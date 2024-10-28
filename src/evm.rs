use crate::codegen::util::{fr_to_u256, to_u256_be_bytes};
use halo2_proofs::halo2curves::bn256;
use itertools::chain;
use ruint::aliases::U256;

/// Function signature of `verifyProof(bytes,uint256[])`.
pub const FN_SIG_VERIFY_PROOF: [u8; 4] = [0x1e, 0x8e, 0x1e, 0x13];

/// Function signature of `verifyProof(address,bytes,uint256[])`.
pub const FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS: [u8; 4] = [0xaf, 0x83, 0xa1, 0x8d];

/// Encode proof into calldata to invoke `Halo2Verifier.verifyProof`.
///
/// For `vk_address`:
/// - Pass `None` if verifying key is embedded in `Halo2Verifier`
/// - Pass `Some(vk_address)` if verifying key is separated and deployed at `vk_address`
pub fn encode_calldata(
    vk_address: Option<[u8; 20]>,
    proof: &[u8],
    instances: &[bn256::Fr],
) -> Vec<u8> {
    let (fn_sig, offset) = if vk_address.is_some() {
        (FN_SIG_VERIFY_PROOF_WITH_VK_ADDRESS, 0x60)
    } else {
        (FN_SIG_VERIFY_PROOF, 0x40)
    };
    let vk_address = if let Some(vk_address) = vk_address {
        U256::try_from_be_slice(&vk_address)
            .unwrap()
            .to_be_bytes::<0x20>()
            .to_vec()
    } else {
        Vec::new()
    };
    let num_instances = instances.len();
    chain![
        fn_sig,                                                      // function signature
        vk_address,                                                  // verifying key address
        to_u256_be_bytes(offset),                                    // offset of proof
        to_u256_be_bytes(offset + 0x20 + proof.len()),               // offset of instances
        to_u256_be_bytes(proof.len()),                               // length of proof
        proof.iter().cloned(),                                       // proof
        to_u256_be_bytes(num_instances),                             // length of instances
        instances.iter().map(fr_to_u256).flat_map(to_u256_be_bytes), // instances
    ]
    .collect()
}

/// Encode VKA deployment calldata to invoke `Halo2Reusable.deployVKA`.
pub fn encode_deploy(vk_creation_code: &[u8]) -> Vec<u8> {
    chain![
        [0xde, 0x8f, 0x56, 0x58], // function signature "deployVKA(bytes)"
        to_u256_be_bytes(0x20),   // offset of vka bytecode
        to_u256_be_bytes(vk_creation_code.len()), // length of vka bytecode
        vk_creation_code.iter().cloned()
    ]
    .collect()
}

#[cfg(any(test, feature = "evm"))]
pub(crate) mod test {
    pub use revm;
    use revm::{
        primitives::{
            Address, Bytes, CfgEnv, CfgEnvWithHandlerCfg, ExecutionResult, HaltReason, Output,
            TransactTo, TxEnv,
        },
        Evm as EVM, InMemoryDB,
    };
    use std::{
        fmt::{self, Debug, Formatter},
        io::{self, Write},
        process::{Command, Stdio},
        str,
    };

    /// Compile solidity with `--via-ir` flag, then return creation bytecode.
    ///
    /// # Panics
    /// Panics if executable `solc` can not be found, or compilation fails.
    pub fn compile_solidity(solidity: impl AsRef<[u8]>) -> Vec<u8> {
        let mut process = match Command::new("solc")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .arg("--bin")
            .arg("--optimize")
            .arg("--model-checker-targets")
            .arg("underflow,overflow")
            .arg("-")
            .spawn()
        {
            Ok(process) => process,
            Err(err) if err.kind() == io::ErrorKind::NotFound => {
                panic!("Command 'solc' not found");
            }
            Err(err) => {
                panic!("Failed to spawn process with command 'solc':\n{err}");
            }
        };
        process
            .stdin
            .take()
            .unwrap()
            .write_all(solidity.as_ref())
            .unwrap();
        let output = process.wait_with_output().unwrap();
        let stdout = str::from_utf8(&output.stdout).unwrap();
        if let Some(binary) = find_binary(stdout) {
            binary
        } else {
            panic!(
                "Compilation fails:\n{}",
                str::from_utf8(&output.stderr).unwrap()
            )
        }
    }

    fn find_binary(stdout: &str) -> Option<Vec<u8>> {
        let start = stdout.find("Binary:")? + 8;
        Some(hex::decode(&stdout[start..stdout.len() - 1]).unwrap())
    }

    /// Evm runner.
    pub struct Evm<'a> {
        evm: EVM<'a, (), InMemoryDB>,
    }

    impl Debug for Evm<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            self.evm.fmt(f)
        }
    }

    impl Default for Evm<'_> {
        fn default() -> Self {
            let evm = EVM::builder().with_db(InMemoryDB::default()).build();
            Self { evm }
        }
    }

    impl Evm<'_> {
        /// Return code_size of given address.
        ///
        /// # Panics
        /// Panics if given address doesn't have bytecode.
        pub fn code_size(&mut self, address: Address) -> usize {
            self.evm.db().accounts[&address]
                .info
                .code
                .as_ref()
                .unwrap()
                .len()
        }

        /// Return a version of the evm that allows for unlimited deployments sizes.
        pub fn unlimited() -> Self {
            let mut cfg_env: CfgEnv = Default::default();
            cfg_env.limit_contract_code_size = Some(usize::MAX);
            let evm = EVM::builder()
                .with_db(InMemoryDB::default())
                .with_cfg_env_with_handler_cfg(CfgEnvWithHandlerCfg {
                    cfg_env,
                    handler_cfg: Default::default(),
                })
                .build();
            Self { evm }
        }

        /// Apply create transaction with given `bytecode` as creation bytecode.
        /// Return created `address`.
        ///
        /// # Panics
        /// Panics if execution reverts or halts unexpectedly.
        pub fn create(&mut self, bytecode: Vec<u8>) -> (Address, u64) {
            let (gas_used, output) = self.transact_success_or_panic(TxEnv {
                gas_limit: u64::MAX,
                transact_to: TransactTo::Create,
                data: bytecode.into(),
                ..Default::default()
            });
            match output {
                Output::Create(_, Some(address)) => (address, gas_used),
                _ => unreachable!(),
            }
        }

        /// Apply call transaction to given `address` with `calldata`.
        /// Returns `gas_used` and `return_data`.
        ///
        /// # Panics
        /// Panics if execution reverts or halts unexpectedly.
        pub fn call(&mut self, address: Address, calldata: Vec<u8>) -> (u64, Vec<u8>) {
            let (gas_used, output) = self.transact_success_or_panic(TxEnv {
                gas_limit: u64::MAX,
                transact_to: TransactTo::Call(address),
                data: calldata.into(),
                ..Default::default()
            });
            match output {
                Output::Call(output) => (gas_used, output.into()),
                _ => unreachable!(),
            }
        }

        /// Apply call transaction to given `address` with `calldata` with the expectation of failure.
        /// Returns `gas_used` and `return_data`.
        ///
        /// # Panics
        /// Panics if execution succeeds.
        pub fn call_fail(&mut self, address: Address, calldata: Vec<u8>) {
            let (_, _) = self.transact_failure_or_panic(TxEnv {
                gas_limit: u64::MAX,
                transact_to: TransactTo::Call(address),
                data: calldata.into(),
                ..Default::default()
            });
        }

        fn transact_success_or_panic(&mut self, tx: TxEnv) -> (u64, Output) {
            self.evm.context.evm.env.tx = tx;
            let result = self.evm.transact_commit().unwrap();
            self.evm.context.evm.env.tx = Default::default();
            match result {
                ExecutionResult::Success {
                    gas_used,
                    output,
                    logs,
                    ..
                } => {
                    if !logs.is_empty() {
                        println!("--- logs from {} ---", logs[0].address);
                        for (log_idx, log) in logs.iter().enumerate() {
                            println!("log#{log_idx}");
                            for (topic_idx, topic) in log.topics().iter().enumerate() {
                                println!("  topic{topic_idx}: {topic:?}");
                            }
                        }
                        println!("--- end ---");
                    }
                    (gas_used, output)
                }
                ExecutionResult::Revert { gas_used, output } => {
                    panic!("Transaction reverts with gas_used {gas_used} and output {output:#x}")
                }
                ExecutionResult::Halt { reason, gas_used } => panic!(
                    "Transaction halts unexpectedly with gas_used {gas_used} and reason {reason:?}"
                ),
            }
        }

        fn transact_failure_or_panic(&mut self, tx: TxEnv) -> (u64, Result<Bytes, HaltReason>) {
            self.evm.context.evm.env.tx = tx;
            let result = self.evm.transact_commit().unwrap();
            self.evm.context.evm.env.tx = Default::default();
            match result {
                ExecutionResult::Success {
                    gas_used,
                    output,
                    logs,
                    ..
                } => {
                    if !logs.is_empty() {
                        println!("--- logs from {} ---", logs[0].address);
                        for (log_idx, log) in logs.iter().enumerate() {
                            println!("log#{log_idx}");
                            for (topic_idx, topic) in log.topics().iter().enumerate() {
                                println!("  topic{topic_idx}: {topic:?}");
                            }
                        }
                        println!("--- end ---");
                    }
                    panic!("Transaction succeeds unexpectedly with gas_used {gas_used} and output {output:?}")
                }
                ExecutionResult::Revert { gas_used, output } => {
                    println!("Transaction reverts with gas_used {gas_used} and output {output:#x}");
                    (gas_used, Ok(output))
                }
                ExecutionResult::Halt { reason, gas_used } => {
                    println!(
                        "Transaction halts unexpectedly with gas_used {gas_used} and reason {reason:?}"
                    );
                    (gas_used, Err(reason))
                }
            }
        }
    }
}
