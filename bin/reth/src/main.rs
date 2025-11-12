#![allow(missing_docs)]

#[global_allocator]
static ALLOC: reth_cli_util::allocator::Allocator = reth_cli_util::allocator::new_allocator();

use std::sync::RwLock;
use clap::Parser;
use tempfile::tempdir;
use reth::{args::RessArgs, cli::Cli, ress::install_ress_subprotocol};
use reth_ethereum_cli::chainspec::EthereumChainSpecParser;
use reth_node_builder::NodeHandle;
use reth_node_ethereum::EthereumNode;
use tracing::info;
use aml_engine::aml::{AmlEvaluator, AML_EVALUATOR};
use aml_engine::aml_db::AmlDb;

fn main() {
    reth_cli_util::sigsegv_handler::install();

    // Enable backtraces unless a RUST_BACKTRACE value has already been explicitly provided.
    if std::env::var_os("RUST_BACKTRACE").is_none() {
        unsafe { std::env::set_var("RUST_BACKTRACE", "1") };
    }

    if let Err(err) =
        Cli::<EthereumChainSpecParser, RessArgs>::parse().run(async move |builder, ress_args| {
            // TODO: (ms) move initialization to properly handle block history (initialize from block X onwards)
            
            info!("launching aml evaluator");
            match AML_EVALUATOR.set(RwLock::new(AmlEvaluator::new())) {
                Ok(()) => {
                    // Successfully initialized
                    info!("AML_EVALUATOR initialized");
                }
                Err(_existing) => {
                    // Already initialized — handle as needed
                    info!("AML_EVALUATOR was already initialized");
                }
            }
            

            info!(target: "reth::cli", "Launching node");
            let NodeHandle { node, node_exit_future } =
                builder.node(EthereumNode::default()).launch_with_debug_capabilities().await?;

            // Install ress subprotocol.
            if ress_args.enabled {
                info!("ress is enabled");
                install_ress_subprotocol(
                    ress_args,
                    node.provider,
                    node.evm_config,
                    node.network,
                    node.task_executor,
                    node.add_ons_handle.engine_events.new_listener(),
                )?;
            }

            node_exit_future.await
        })
    {
        eprintln!("Error: {err:?}");
        std::process::exit(1);
    }
}
