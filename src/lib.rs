//! Solidity verifier generator for [`halo2`] proof with KZG polynomial commitment scheme on BN254.
//!
//! [`halo2`]: http://github.com/privacy-scaling-explorations/halo2

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![deny(rustdoc::broken_intra_doc_links)]

mod codegen;
mod evm;
mod transcript;

#[cfg(test)]
mod test;

pub use codegen::{AccumulatorEncoding, BatchOpenScheme, SolidityGenerator};
pub use evm::{
    encode_calldata, encode_calldata_malicious, encode_calldata_malicious_wrapper,
    encode_register_vk_calldata, FN_SIG_VERIFY_PROOF, FN_SIG_VERIFY_PROOF_WITH_VKA,
};
pub use transcript::Keccak256Transcript;

#[cfg(feature = "evm")]
pub use evm::test::{compile_solidity, revm, Evm};
