//! Database access for `eth_` transaction RPC methods. Loads transaction and receipt data w.r.t.
//! network.

use super::{EthApiSpec, EthSigner, LoadBlock, LoadFee, LoadReceipt, LoadState, SpawnBlocking};
use crate::{
    helpers::{estimate::EstimateCall, spec::SignersForRpc},
    FromEthApiError, FullEthApiTypes, IntoEthApiError, RpcNodeCore, RpcNodeCoreExt, RpcReceipt,
    RpcTransaction,
};
use alloy_consensus::{
    transaction::{SignerRecoverable, TransactionMeta, TxHashRef},
    BlockHeader, Transaction, TxEnvelope,
};
use alloy_dyn_abi::TypedData;
use alloy_eips::{eip2718::Encodable2718, BlockId};
use alloy_network::{Ethereum, EthereumWallet, TransactionBuilder, TransactionBuilder4844};
use alloy_primitives::{hex, Address, Bytes, TxHash, TxKind, B256, U256};
use alloy_rpc_types_eth::{
    BlockNumberOrTag, TransactionInfo, TransactionInput, TransactionRequest,
};
use futures::{Future, StreamExt};
use jsonrpsee::core::Serialize;
use reth_chain_state::CanonStateSubscriptions;
use reth_node_api::BlockBody;
use reth_primitives_traits::{
    NodePrimitives, Recovered, RecoveredBlock, SignedTransaction, TxTy, WithEncoded,
};
use reth_rpc_convert::{transaction::RpcConvert, RpcTxReq, TransactionConversionError};
use reth_rpc_eth_types::{
    utils::{binary_search, recover_raw_transaction},
    EthApiError::{self, TransactionConfirmationTimeout},
    FillTransaction, SignError, TransactionSource,
};
use reth_storage_api::{
    BlockNumReader, BlockReaderIdExt, ProviderBlock, ProviderReceipt, ProviderTx, ReceiptProvider,
    TransactionsProvider,
};
use reth_transaction_pool::{
    AddedTransactionOutcome, EthPooledTransaction, PoolPooledTx, PoolTransaction,
    TransactionOrigin, TransactionPool,
};
use serde::Deserialize;
use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::str::FromStr;
use std::{sync::Arc, time::Duration};
use tracing::{info, warn};
use aml_engine::aml::{AML_EVALUATOR};

/// Transaction related functions for the [`EthApiServer`](crate::EthApiServer) trait in
/// the `eth_` namespace.
///
/// This includes utilities for transaction tracing, transacting and inspection.
///
/// Async functions that are spawned onto the
/// [`BlockingTaskPool`](reth_tasks::pool::BlockingTaskPool) begin with `spawn_`
///
/// ## Calls
///
/// There are subtle differences between when transacting [`RpcTxReq`]:
///
/// The endpoints `eth_call` and `eth_estimateGas` and `eth_createAccessList` should always
/// __disable__ the base fee check in the [`CfgEnv`](revm::context::CfgEnv).
///
/// The behaviour for tracing endpoints is not consistent across clients.
/// Geth also disables the basefee check for tracing: <https://github.com/ethereum/go-ethereum/blob/bc0b87ca196f92e5af49bd33cc190ef0ec32b197/eth/tracers/api.go#L955-L955>
/// Erigon does not: <https://github.com/ledgerwatch/erigon/blob/aefb97b07d1c4fd32a66097a24eddd8f6ccacae0/turbo/transactions/tracing.go#L209-L209>
///
/// See also <https://github.com/paradigmxyz/reth/issues/6240>
///
/// This implementation follows the behaviour of Geth and disables the basefee check for tracing.
///
///

#[derive(Debug, Deserialize)]
struct CsvRecord {
    block_number: u64,
    raw_tx: String, // Hex-encoded signed transaction (with or without 0x prefix)
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct LoadTestResult {
    pub total_transactions: usize,
    pub blocks_processed: usize,
    pub transaction_hashes: Vec<B256>,
}

#[cfg(feature = "sol-types")]
alloy_sol_types::sol! {
    function transfer(address to, uint256 amount) external returns (bool);
}

// ============================================================================
// Helper Functions (OUTSIDE the trait impl)
// ============================================================================

fn parse_hex_bytes(s: &str) -> Result<Bytes, String> {
    let s = s.trim().strip_prefix("0x").unwrap_or(s);
    hex::decode(s).map(|v| v.into()).map_err(|e| format!("invalid hex: {}", e))
}

pub trait EthTransactions: LoadTransaction<Provider: BlockReaderIdExt> {
    /// Returns a handle for signing data.
    ///
    /// Signer access in default (L1) trait method implementations.
    fn signers(&self) -> &SignersForRpc<Self::Provider, Self::NetworkTypes>;

    /// Returns a list of addresses owned by provider.
    fn accounts(&self) -> Vec<Address> {
        self.signers().read().iter().flat_map(|s| s.accounts()).collect()
    }

    /// Returns the timeout duration for `send_raw_transaction_sync` RPC method.
    fn send_raw_transaction_sync_timeout(&self) -> Duration;

    /// Decodes and recovers the transaction and submits it to the pool.
    ///
    /// Returns the hash of the transaction.
    fn send_raw_transaction(
        &self,
        tx: Bytes,
    ) -> impl Future<Output = Result<B256, Self::Error>> + Send {
        async move {
            let recovered = recover_raw_transaction::<PoolPooledTx<Self::Pool>>(&tx)?;
            self.send_transaction(WithEncoded::new(tx, recovered)).await
        }
    }

    /// Submits the transaction to the pool.
    fn send_transaction(
        &self,
        tx: WithEncoded<Recovered<PoolPooledTx<Self::Pool>>>,
    ) -> impl Future<Output = Result<B256, Self::Error>> + Send;

    /// Decodes and recovers the transaction and submits it to the pool.
    ///
    /// And awaits the receipt.
    fn send_raw_transaction_sync(
        &self,
        tx: Bytes,
    ) -> impl Future<Output = Result<RpcReceipt<Self::NetworkTypes>, Self::Error>> + Send
    where
        Self: LoadReceipt + 'static,
    {
        let this = self.clone();
        let timeout_duration = self.send_raw_transaction_sync_timeout();
        async move {
            let mut stream = this.provider().canonical_state_stream();
            let hash = EthTransactions::send_raw_transaction(&this, tx).await?;
            tokio::time::timeout(timeout_duration, async {
                while let Some(notification) = stream.next().await {
                    let chain = notification.committed();
                    for block in chain.blocks_iter() {
                        if block.body().contains_transaction(&hash)
                            && let Some(receipt) = this.transaction_receipt(hash).await?
                        {
                            return Ok(receipt);
                        }
                    }
                }
                Err(Self::Error::from_eth_err(TransactionConfirmationTimeout {
                    hash,
                    duration: timeout_duration,
                }))
            })
            .await
            .unwrap_or_else(|_elapsed| {
                Err(Self::Error::from_eth_err(TransactionConfirmationTimeout {
                    hash,
                    duration: timeout_duration,
                }))
            })
        }
    }

    /// Returns the transaction by hash.
    ///
    /// Checks the pool and state.
    ///
    /// Returns `Ok(None)` if no matching transaction was found.
    #[expect(clippy::complexity)]
    fn transaction_by_hash(
        &self,
        hash: B256,
    ) -> impl Future<
        Output = Result<Option<TransactionSource<ProviderTx<Self::Provider>>>, Self::Error>,
    > + Send {
        LoadTransaction::transaction_by_hash(self, hash)
    }

    /// Get all transactions in the block with the given hash.
    ///
    /// Returns `None` if block does not exist.
    #[expect(clippy::type_complexity)]
    fn transactions_by_block(
        &self,
        block: B256,
    ) -> impl Future<Output = Result<Option<Vec<ProviderTx<Self::Provider>>>, Self::Error>> + Send
    {
        async move {
            self.cache()
                .get_recovered_block(block)
                .await
                .map(|b| b.map(|b| b.body().transactions().to_vec()))
                .map_err(Self::Error::from_eth_err)
        }
    }

    /// Returns the EIP-2718 encoded transaction by hash.
    ///
    /// If this is a pooled EIP-4844 transaction, the blob sidecar is included.
    ///
    /// Checks the pool and state.
    ///
    /// Returns `Ok(None)` if no matching transaction was found.
    fn raw_transaction_by_hash(
        &self,
        hash: B256,
    ) -> impl Future<Output = Result<Option<Bytes>, Self::Error>> + Send {
        async move {
            // Note: this is mostly used to fetch pooled transactions so we check the pool first
            if let Some(tx) =
                self.pool().get_pooled_transaction_element(hash).map(|tx| tx.encoded_2718().into())
            {
                return Ok(Some(tx));
            }

            self.spawn_blocking_io(move |ref this| {
                Ok(this
                    .provider()
                    .transaction_by_hash(hash)
                    .map_err(Self::Error::from_eth_err)?
                    .map(|tx| tx.encoded_2718().into()))
            })
            .await
        }
    }

    /// Returns the _historical_ transaction and the block it was mined in
    #[expect(clippy::type_complexity)]
    fn historical_transaction_by_hash_at(
        &self,
        hash: B256,
    ) -> impl Future<
        Output = Result<Option<(TransactionSource<ProviderTx<Self::Provider>>, B256)>, Self::Error>,
    > + Send {
        async move {
            match self.transaction_by_hash_at(hash).await? {
                None => Ok(None),
                Some((tx, at)) => Ok(at.as_block_hash().map(|hash| (tx, hash))),
            }
        }
    }

    /// Returns the transaction receipt for the given hash.
    ///
    /// Returns None if the transaction does not exist or is pending
    /// Note: The tx receipt is not available for pending transactions.
    fn transaction_receipt(
        &self,
        hash: B256,
    ) -> impl Future<Output = Result<Option<RpcReceipt<Self::NetworkTypes>>, Self::Error>> + Send
    where
        Self: LoadReceipt + 'static,
    {
        async move {
            match self.load_transaction_and_receipt(hash).await? {
                Some((tx, meta, receipt)) => {
                    self.build_transaction_receipt(tx, meta, receipt).await.map(Some)
                }
                None => Ok(None),
            }
        }
    }

    /// Helper method that loads a transaction and its receipt.
    #[expect(clippy::complexity)]
    fn load_transaction_and_receipt(
        &self,
        hash: TxHash,
    ) -> impl Future<
        Output = Result<
            Option<(ProviderTx<Self::Provider>, TransactionMeta, ProviderReceipt<Self::Provider>)>,
            Self::Error,
        >,
    > + Send
    where
        Self: 'static,
    {
        self.spawn_blocking_io(move |this| {
            let provider = this.provider();
            let (tx, meta) = match provider
                .transaction_by_hash_with_meta(hash)
                .map_err(Self::Error::from_eth_err)?
            {
                Some((tx, meta)) => (tx, meta),
                None => return Ok(None),
            };

            let receipt = match provider.receipt_by_hash(hash).map_err(Self::Error::from_eth_err)? {
                Some(recpt) => recpt,
                None => return Ok(None),
            };

            Ok(Some((tx, meta, receipt)))
        })
    }

    /// Get transaction by [`BlockId`] and index of transaction within that block.
    ///
    /// Returns `Ok(None)` if the block does not exist, or index is out of range.
    fn transaction_by_block_and_tx_index(
        &self,
        block_id: BlockId,
        index: usize,
    ) -> impl Future<Output = Result<Option<RpcTransaction<Self::NetworkTypes>>, Self::Error>> + Send
    where
        Self: LoadBlock,
    {
        async move {
            if let Some(block) = self.recovered_block(block_id).await? {
                let block_hash = block.hash();
                let block_number = block.number();
                let base_fee_per_gas = block.base_fee_per_gas();
                if let Some((signer, tx)) = block.transactions_with_sender().nth(index) {
                    let tx_info = TransactionInfo {
                        hash: Some(*tx.tx_hash()),
                        block_hash: Some(block_hash),
                        block_number: Some(block_number),
                        base_fee: base_fee_per_gas,
                        index: Some(index as u64),
                    };

                    return Ok(Some(
                        self.converter().fill(tx.clone().with_signer(*signer), tx_info)?,
                    ));
                }
            }

            Ok(None)
        }
    }

    /// Find a transaction by sender's address and nonce.
    fn get_transaction_by_sender_and_nonce(
        &self,
        sender: Address,
        nonce: u64,
        include_pending: bool,
    ) -> impl Future<Output = Result<Option<RpcTransaction<Self::NetworkTypes>>, Self::Error>> + Send
    where
        Self: LoadBlock + LoadState,
    {
        async move {
            // Check the pool first
            if include_pending
                && let Some(tx) =
                    RpcNodeCore::pool(self).get_transaction_by_sender_and_nonce(sender, nonce)
            {
                let transaction = tx.transaction.clone_into_consensus();
                return Ok(Some(self.converter().fill_pending(transaction)?));
            }

            // Note: we can't optimize for contracts (account with code) and cannot shortcircuit if
            // the address has code, because with 7702 EOAs can also have code

            let highest = self.transaction_count(sender, None).await?.saturating_to::<u64>();

            // If the nonce is higher or equal to the highest nonce, the transaction is pending or
            // not exists.
            if nonce >= highest {
                return Ok(None);
            }

            let Ok(high) = self.provider().best_block_number() else {
                return Err(EthApiError::HeaderNotFound(BlockNumberOrTag::Latest.into()).into());
            };

            // Perform a binary search over the block range to find the block in which the sender's
            // nonce reached the requested nonce.
            let num = binary_search::<_, _, Self::Error>(1, high, |mid| async move {
                let mid_nonce =
                    self.transaction_count(sender, Some(mid.into())).await?.saturating_to::<u64>();

                Ok(mid_nonce > nonce)
            })
            .await?;

            let block_id = num.into();
            self.recovered_block(block_id)
                .await?
                .and_then(|block| {
                    let block_hash = block.hash();
                    let block_number = block.number();
                    let base_fee_per_gas = block.base_fee_per_gas();

                    block
                        .transactions_with_sender()
                        .enumerate()
                        .find(|(_, (signer, tx))| **signer == sender && (*tx).nonce() == nonce)
                        .map(|(index, (signer, tx))| {
                            let tx_info = TransactionInfo {
                                hash: Some(*tx.tx_hash()),
                                block_hash: Some(block_hash),
                                block_number: Some(block_number),
                                base_fee: base_fee_per_gas,
                                index: Some(index as u64),
                            };
                            Ok(self.converter().fill(tx.clone().with_signer(*signer), tx_info)?)
                        })
                })
                .ok_or(EthApiError::HeaderNotFound(block_id))?
                .map(Some)
        }
    }

    /// Get transaction, as raw bytes, by [`BlockId`] and index of transaction within that block.
    ///
    /// Returns `Ok(None)` if the block does not exist, or index is out of range.
    fn raw_transaction_by_block_and_tx_index(
        &self,
        block_id: BlockId,
        index: usize,
    ) -> impl Future<Output = Result<Option<Bytes>, Self::Error>> + Send
    where
        Self: LoadBlock,
    {
        async move {
            if let Some(block) = self.recovered_block(block_id).await?
                && let Some(tx) = block.body().transactions().get(index)
            {
                return Ok(Some(tx.encoded_2718().into()));
            }

            Ok(None)
        }
    }

    /// Signs transaction with a matching signer, if any and submits the transaction to the pool.
    /// Returns the hash of the signed transaction.
    fn send_transaction_request(
        &self,
        mut request: RpcTxReq<Self::NetworkTypes>,
    ) -> impl Future<Output = Result<B256, Self::Error>> + Send
    where
        Self: EthApiSpec + LoadBlock + EstimateCall,
    {
        async move {
            let from = match request.as_ref().from() {
                Some(from) => from,
                None => return Err(SignError::NoAccount.into_eth_err()),
            };

            if self.find_signer(&from).is_err() {
                return Err(SignError::NoAccount.into_eth_err());
            }

            // set nonce if not already set before
            if request.as_ref().nonce().is_none() {
                let nonce = self.next_available_nonce(from).await?;
                request.as_mut().set_nonce(nonce);
            }

            let chain_id = self.chain_id();
            request.as_mut().set_chain_id(chain_id.to());

            let estimated_gas =
                self.estimate_gas_at(request.clone(), BlockId::pending(), None).await?;
            let gas_limit = estimated_gas;
            request.as_mut().set_gas_limit(gas_limit.to());

            let transaction = self.sign_request(&from, request).await?.with_signer(from);

            let pool_transaction =
                <<Self as RpcNodeCore>::Pool as TransactionPool>::Transaction::try_from_consensus(
                    transaction,
                )
                .map_err(|e| {
                    Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
                })?;

            // submit the transaction to the pool with a `Local` origin
            let AddedTransactionOutcome { hash, .. } = self
                .pool()
                .add_transaction(TransactionOrigin::Local, pool_transaction)
                .await
                .map_err(Self::Error::from_eth_err)?;

            Ok(hash)
        }
    }

    /// Signs transaction with a matching signer, if any and submits the transaction to the pool.
    /// Returns the hash of the signed transaction.
    fn send_transactions_batch(
        &self,
        requests: Vec<Bytes>,
    ) -> impl Future<Output = Result<Vec<B256>, Self::Error>> + Send
    where
        Self: EthApiSpec + LoadBlock + EstimateCall,
    {
        async move {
            let mut pool_transactions = Vec::with_capacity(requests.len());
            let mut hashes = Vec::with_capacity(requests.len());

            for raw_tx_bytes in requests {
                // 1. Decode the RLP bytes into a Signed Transaction
                // Assuming raw_tx_bytes is the `Bytes` from the JSON-RPC call
                type SignedTx<T> = <<T as RpcNodeCore>::Primitives as NodePrimitives>::SignedTx;

                // 2. Recover specifically into the Node's SignedTx type
                // This performs RLP decoding AND ecrecover
                let recovered = recover_raw_transaction::<SignedTx<Self>>(&raw_tx_bytes)?;

                // 3. Convert the Consensus type (SignedTx) into the Pooled type
                // This is where the decoupled types are mapped together
                let pool_transaction = <<Self as RpcNodeCore>::Pool as TransactionPool>::Transaction::try_from_consensus(
                    recovered,
                ).map_err(|e| {
                    Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
                })?;

                pool_transactions.push(pool_transaction);
            }

            // 4. Submit to the pool as 'External' or 'Local'
            // Since these come via RPC, 'Local' is appropriate for immediate priority
            let outcomes =
                self.pool().add_transactions(TransactionOrigin::Local, pool_transactions).await;

            for outcome in outcomes {
                match outcome {
                    Ok(added) => hashes.push(added.hash),
                    Err(e) => eprintln!("Failed to add transaction: {:?}", e),
                }
            }

            Ok(hashes)
        }
    }

    fn load_test_from_csv(
        &self,
        csv_path: String,
    ) -> impl Future<Output = Result<LoadTestResult, Self::Error>> + Send
    where
        Self: EthApiSpec + LoadBlock + EstimateCall,
    {
        async move {
            // 1. Read and parse CSV
            let transactions_by_block = self.read_csv_file(&csv_path)?;
            info!("Loaded {} target blocks from CSV", transactions_by_block.len());
            let blocks_processed = transactions_by_block.len();
            let mut total_txs = 0;
            let mut all_hashes = Vec::new();
            let mut current_chain_height = self.provider().last_block_number().unwrap_or(0);

            info!("Pre-decoding all transactions...");
            let mut batches_prepared = Vec::new();

            for (csv_block_num, records) in transactions_by_block {
                let (pool_transactions, batch_hashes) = self.decode_transactions(records)?;
                batches_prepared.push((csv_block_num, pool_transactions, batch_hashes));
            }

            info!("All {} batches pre-decoded and ready", batches_prepared.len());

            // 2. Process each block batch
            for (csv_block_num, pool_transactions, batch_hashes) in batches_prepared {
                info!("CSV Block {}: Submitting {} transactions", csv_block_num, pool_transactions.len());

                // Submit to pool IMMEDIATELY
                let outcomes = self.pool()
                    .add_transactions(TransactionOrigin::Local, pool_transactions)
                    .await;

                let success_count = outcomes.iter().filter(|o| o.is_ok()).count();
                total_txs += success_count;

                // Track successful transaction hashes
                for (idx, outcome) in outcomes.iter().enumerate() {
                    if outcome.is_ok() {
                        all_hashes.push(batch_hashes[idx]);
                    }
                }

                info!("Batch submitted: {}/{} transactions accepted", success_count, outcomes.len());

                // Wait for block production (transactions are already in pool, waiting for next block to mine them)
                current_chain_height = self.wait_for_next_block(current_chain_height).await?;

                // Small delay before next batch
                tokio::time::sleep(Duration::from_millis(1)).await;
            }

            Ok(LoadTestResult {
                total_transactions: total_txs,
                blocks_processed,
                transaction_hashes: all_hashes,
            })
        }
    }

    async fn load_test_from_csv_bulk(
        &self,
        csv_path: String,
    ) -> Result<LoadTestResult, Self::Error> {
        // Read all transactions
        let transactions_by_block = self.read_csv_file(&csv_path)?;

        // Flatten all transactions into one big batch
        let all_records: Vec<CsvRecord> =
            transactions_by_block.into_iter().flat_map(|(_, records)| records).collect();

        info!("Loading {} transactions in bulk", all_records.len());

        let (pool_transactions, batch_hashes) = self.decode_transactions(all_records)?;

        // Submit everything at once
        let outcomes =
            self.pool().add_transactions(TransactionOrigin::Local, pool_transactions).await;

        let success_count = outcomes.iter().filter(|o| o.is_ok()).count();

        // Track successful transaction hashes
        let mut successful_hashes = Vec::new();
        for (idx, outcome) in outcomes.iter().enumerate() {
            if outcome.is_ok() {
                successful_hashes.push(batch_hashes[idx]);
            }
        }

        info!(
            "Bulk injection complete: {}/{} transactions accepted",
            success_count,
            outcomes.len()
        );

        Ok(LoadTestResult {
            total_transactions: success_count,
            blocks_processed: 1, // All in one go
            transaction_hashes: successful_hashes,
        })
    }

    /// Build a batch of signed transactions from CSV records
    fn read_csv_file(&self, csv_path: &str) -> Result<BTreeMap<u64, Vec<CsvRecord>>, Self::Error> {
        let mut reader = csv::Reader::from_path(csv_path).map_err(|e| {
            Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
        })?;

        let mut transactions_by_block: BTreeMap<u64, Vec<CsvRecord>> = BTreeMap::new();

        for result in reader.deserialize() {
            let record: CsvRecord = result.map_err(|e| {
                Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
            })?;

            transactions_by_block.entry(record.block_number).or_default().push(record);
        }

        Ok(transactions_by_block)
    }

    fn decode_transactions(
        &self,
        records: Vec<CsvRecord>,
    ) -> Result<(Vec<<Self::Pool as TransactionPool>::Transaction>, Vec<B256>), Self::Error> {
        let mut pool_transactions = Vec::with_capacity(records.len());
        let mut hashes = Vec::with_capacity(records.len());

        for record in records {
            // Parse hex bytes
            let raw_tx_bytes = parse_hex_bytes(&record.raw_tx).map_err(|e| {
                Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
            })?;

            // Decode and recover the transaction
            type SignedTx<T> = <<T as RpcNodeCore>::Primitives as NodePrimitives>::SignedTx;
            let recovered = recover_raw_transaction::<SignedTx<Self>>(&raw_tx_bytes)?;

            // Get the hash before converting
            let tx_hash = *recovered.tx_hash();

            // Convert to pool transaction
            let pool_transaction =
                <<Self as RpcNodeCore>::Pool as TransactionPool>::Transaction::try_from_consensus(
                    recovered,
                )
                .map_err(|e| {
                    Self::Error::from_eth_err(TransactionConversionError::Other(e.to_string()))
                })?;

            pool_transactions.push(pool_transaction);
            hashes.push(tx_hash);
        }

        Ok((pool_transactions, hashes))
    }

    fn wait_for_next_block(
        &self,
        current_height: u64,
    ) -> impl Future<Output = Result<u64, Self::Error>> + Send {
        async move {
            let target_height = current_height + 1;

            let timeout_duration = Duration::from_secs(10);
            let start_wait = std::time::Instant::now();

            loop {
                let best = {
                    let aml_evaluator = AML_EVALUATOR
                        .get()
                        .expect("AML_EVALUATOR not initialized")
                        .read()
                        .expect("poisoned lock");

                    aml_evaluator.block_number
                }; // Guard dropped here

                if best >= target_height {
                    return Ok(best);
                }

                if start_wait.elapsed() > timeout_duration {
                    warn!(
                        "Timeout waiting for block {} - Ghost block likely occurred or pool rejected txs",
                        target_height
                    );
                    return Ok(current_height); // Return current height on timeout
                }

                tokio::time::sleep(Duration::from_millis(5)).await;
            }
        }
    }

    /// Fills the defaults on a given unsigned transaction.
    fn fill_transaction(
        &self,
        mut request: RpcTxReq<Self::NetworkTypes>,
    ) -> impl Future<Output = Result<FillTransaction<TxTy<Self::Primitives>>, Self::Error>> + Send
    where
        Self: EthApiSpec + LoadBlock + EstimateCall + LoadFee,
    {
        async move {
            let from = match request.as_ref().from() {
                Some(from) => from,
                None => return Err(SignError::NoAccount.into_eth_err()),
            };

            if request.as_ref().value().is_none() {
                request.as_mut().set_value(U256::ZERO);
            }

            if request.as_ref().nonce().is_none() {
                let nonce = self.next_available_nonce(from).await?;
                request.as_mut().set_nonce(nonce);
            }

            let chain_id = self.chain_id();
            request.as_mut().set_chain_id(chain_id.to());

            if request.as_ref().has_eip4844_fields()
                && request.as_ref().max_fee_per_blob_gas().is_none()
            {
                let blob_fee = self.blob_base_fee().await?;
                request.as_mut().set_max_fee_per_blob_gas(blob_fee.to());
            }

            if request.as_ref().blob_sidecar().is_some()
                && request.as_ref().blob_versioned_hashes.is_none()
            {
                request.as_mut().populate_blob_hashes();
            }

            if request.as_ref().gas_limit().is_none() {
                let estimated_gas =
                    self.estimate_gas_at(request.clone(), BlockId::pending(), None).await?;
                request.as_mut().set_gas_limit(estimated_gas.to());
            }

            if request.as_ref().gas_price().is_none() {
                let tip = if let Some(tip) = request.as_ref().max_priority_fee_per_gas() {
                    tip
                } else {
                    let tip = self.suggested_priority_fee().await?.to::<u128>();
                    request.as_mut().set_max_priority_fee_per_gas(tip);
                    tip
                };
                if request.as_ref().max_fee_per_gas().is_none() {
                    let header =
                        self.provider().latest_header().map_err(Self::Error::from_eth_err)?;
                    let base_fee = header.and_then(|h| h.base_fee_per_gas()).unwrap_or_default();
                    request.as_mut().set_max_fee_per_gas(base_fee as u128 + tip);
                }
            }

            let tx = self.converter().build_simulate_v1_transaction(request)?;

            let raw = tx.encoded_2718().into();

            Ok(FillTransaction { raw, tx })
        }
    }

    /// Signs a transaction, with configured signers.
    fn sign_request(
        &self,
        from: &Address,
        txn: RpcTxReq<Self::NetworkTypes>,
    ) -> impl Future<Output = Result<ProviderTx<Self::Provider>, Self::Error>> + Send {
        async move {
            self.find_signer(from)?
                .sign_transaction(txn, from)
                .await
                .map_err(Self::Error::from_eth_err)
        }
    }

    /// Signs given message. Returns the signature.
    fn sign(
        &self,
        account: Address,
        message: Bytes,
    ) -> impl Future<Output = Result<Bytes, Self::Error>> + Send {
        async move {
            Ok(self
                .find_signer(&account)?
                .sign(account, &message)
                .await
                .map_err(Self::Error::from_eth_err)?
                .as_bytes()
                .into())
        }
    }

    /// Signs a transaction request using the given account in request
    /// Returns the EIP-2718 encoded signed transaction.
    fn sign_transaction(
        &self,
        request: RpcTxReq<Self::NetworkTypes>,
    ) -> impl Future<Output = Result<Bytes, Self::Error>> + Send {
        async move {
            let from = match request.as_ref().from() {
                Some(from) => from,
                None => return Err(SignError::NoAccount.into_eth_err()),
            };

            Ok(self.sign_request(&from, request).await?.encoded_2718().into())
        }
    }

    /// Encodes and signs the typed data according EIP-712. Payload must implement Eip712 trait.
    fn sign_typed_data(&self, data: &TypedData, account: Address) -> Result<Bytes, Self::Error> {
        Ok(self
            .find_signer(&account)?
            .sign_typed_data(account, data)
            .map_err(Self::Error::from_eth_err)?
            .as_bytes()
            .into())
    }

    /// Returns the signer for the given account, if found in configured signers.
    #[expect(clippy::type_complexity)]
    fn find_signer(
        &self,
        account: &Address,
    ) -> Result<
        Box<dyn EthSigner<ProviderTx<Self::Provider>, RpcTxReq<Self::NetworkTypes>> + 'static>,
        Self::Error,
    > {
        self.signers()
            .read()
            .iter()
            .find(|signer| signer.is_signer_for(account))
            .map(|signer| dyn_clone::clone_box(&**signer))
            .ok_or_else(|| SignError::NoAccount.into_eth_err())
    }
}

/// Loads a transaction from database.
///
/// Behaviour shared by several `eth_` RPC methods, not exclusive to `eth_` transactions RPC
/// methods.
pub trait LoadTransaction: SpawnBlocking + FullEthApiTypes + RpcNodeCoreExt {
    /// Returns the transaction by hash.
    ///
    /// Checks the pool and state.
    ///
    /// Returns `Ok(None)` if no matching transaction was found.
    #[expect(clippy::complexity)]
    fn transaction_by_hash(
        &self,
        hash: B256,
    ) -> impl Future<
        Output = Result<Option<TransactionSource<ProviderTx<Self::Provider>>>, Self::Error>,
    > + Send {
        async move {
            // Try to find the transaction on disk
            if let Some((tx, meta)) = self
                .spawn_blocking_io(move |this| {
                    this.provider()
                        .transaction_by_hash_with_meta(hash)
                        .map_err(Self::Error::from_eth_err)
                })
                .await?
            {
                // Note: we assume this transaction is valid, because it's mined (or
                // part of pending block) and already. We don't need to
                // check for pre EIP-2 because this transaction could be pre-EIP-2.
                let transaction = tx
                    .try_into_recovered_unchecked()
                    .map_err(|_| EthApiError::InvalidTransactionSignature)?;

                return Ok(Some(TransactionSource::Block {
                    transaction,
                    index: meta.index,
                    block_hash: meta.block_hash,
                    block_number: meta.block_number,
                    base_fee: meta.base_fee,
                }));
            }

            // tx not found on disk, check pool
            if let Some(tx) = self.pool().get(&hash).map(|tx| tx.transaction.clone_into_consensus())
            {
                return Ok(Some(TransactionSource::Pool(tx.into())));
            }

            Ok(None)
        }
    }

    /// Returns the transaction by including its corresponding [`BlockId`].
    ///
    /// Note: this supports pending transactions
    #[expect(clippy::type_complexity)]
    fn transaction_by_hash_at(
        &self,
        transaction_hash: B256,
    ) -> impl Future<
        Output = Result<
            Option<(TransactionSource<ProviderTx<Self::Provider>>, BlockId)>,
            Self::Error,
        >,
    > + Send {
        async move {
            Ok(self.transaction_by_hash(transaction_hash).await?.map(|tx| match tx {
                tx @ TransactionSource::Pool(_) => (tx, BlockId::pending()),
                tx @ TransactionSource::Block { block_hash, .. } => {
                    (tx, BlockId::Hash(block_hash.into()))
                }
            }))
        }
    }

    /// Fetches the transaction and the transaction's block
    #[expect(clippy::type_complexity)]
    fn transaction_and_block(
        &self,
        hash: B256,
    ) -> impl Future<
        Output = Result<
            Option<(
                TransactionSource<ProviderTx<Self::Provider>>,
                Arc<RecoveredBlock<ProviderBlock<Self::Provider>>>,
            )>,
            Self::Error,
        >,
    > + Send {
        async move {
            let (transaction, at) = match self.transaction_by_hash_at(hash).await? {
                None => return Ok(None),
                Some(res) => res,
            };

            // Note: this is always either hash or pending
            let block_hash = match at {
                BlockId::Hash(hash) => hash.block_hash,
                _ => return Ok(None),
            };
            let block = self
                .cache()
                .get_recovered_block(block_hash)
                .await
                .map_err(Self::Error::from_eth_err)?;
            Ok(block.map(|block| (transaction, block)))
        }
    }
}
