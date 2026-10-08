// Hardfork table (huff/fork.ts): the EVM features the emitted code may use
// and the limits it must respect, per fork. PUSH0 (EIP-3855) and the
// initcode limit (EIP-3860) arrive with Shanghai, DUPN / SWAPN (EIP-8024)
// and the larger code size (EIP-7954) with Amsterdam. Nothing emitted
// depends on Cancun, Prague or Osaka, so their output equals Shanghai's.

use crate::bail;
use crate::error::Result;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fork {
    pub name: &'static str,
    /// a zero is PUSH0 (2 gas, 1 byte) instead of PUSH1 0x00 (3 gas, 2 bytes)
    pub push0: bool,
    /// deepest DUP / SWAP slot: 16, or 235 with DUPN / SWAPN (3 gas, 2 bytes)
    pub reach: usize,
    /// runtime code size limit of one contract
    pub code_size: usize,
    /// initcode size limit (none before Shanghai)
    pub initcode_size: usize,
    /// STATICCALL account access, cold (first touch in the transaction) / warm
    pub cold_account: u64,
    pub warm_account: u64,
}

const LEGACY: Fork = Fork {
    name: "",
    push0: true,
    reach: 16,
    code_size: 24576,
    initcode_size: 49152,
    cold_account: 2600,
    warm_account: 100,
};

pub const FORKS: [Fork; 6] = [
    Fork {
        name: "paris",
        push0: false,
        initcode_size: usize::MAX,
        ..LEGACY
    },
    Fork {
        name: "shanghai",
        ..LEGACY
    },
    Fork {
        name: "cancun",
        ..LEGACY
    },
    Fork {
        name: "prague",
        ..LEGACY
    },
    Fork {
        name: "osaka",
        ..LEGACY
    },
    Fork {
        name: "amsterdam",
        reach: 235,
        code_size: 65536,
        initcode_size: 131072,
        ..LEGACY
    },
];

pub const SHANGHAI: Fork = FORKS[1];

/// the fork the output in src/bn254/huff/ targets
pub const DEFAULT_HARDFORK: &str = "amsterdam";

pub fn fork(name: &str) -> Result<Fork> {
    match FORKS.iter().find(|f| f.name == name) {
        Some(f) => Ok(*f),
        None => {
            let names: Vec<&str> = FORKS.iter().map(|f| f.name).collect();
            bail!("unknown hardfork: {name} (one of {})", names.join(", "))
        }
    }
}
