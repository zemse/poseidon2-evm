//! The poseidon2-evm code generators: the Poseidon2 BN254 parameters, the
//! reference permutation, and the Huff and Yul generators. They port the
//! TypeScript generators (`generator/`, removed after 8067f7a) with
//! byte-identical output; "the TS" in comments means those.

pub mod assert_known;
pub mod eip8024;
pub mod error;
pub mod fdlibm;
pub mod field;
pub mod huff;
pub mod lean_export;
pub mod reference;
pub mod round_constants;
pub mod value;
pub mod vectors;
pub mod yul;
