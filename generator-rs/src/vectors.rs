// Test inputs shared by both generators (shared/vectors.ts): the externally
// confirmed [0, 1, ..., t-1], all zeros, all p - 1, descending from p - 1 and
// four pseudo-random states.

use crate::field::{PRIME, U256, reduce, u256};

/// Deterministic 256-bit values from a splitmix64 stream.
pub struct Prng {
    s: u64,
}

impl Prng {
    pub fn new(seed: u64) -> Prng {
        Prng { s: seed }
    }

    fn next64(&mut self) -> u64 {
        self.s = self.s.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.s;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    pub fn next_word(&mut self) -> U256 {
        reduce(self.next_u256())
    }

    /// a full 256-bit word, not reduced
    pub fn next_u256(&mut self) -> U256 {
        // the first word drawn is the most significant
        let a = self.next64();
        let b = self.next64();
        let c = self.next64();
        let d = self.next64();
        U256::from_limbs([d, c, b, a])
    }
}

pub fn test_inputs(t: usize) -> Vec<Vec<U256>> {
    let mut rand = Prng::new(t as u64);
    let p1 = PRIME - u256(1);
    let mut inputs = vec![
        (0..t).map(|i| u256(i as u64)).collect(),
        vec![U256::ZERO; t],
        vec![p1; t],
        (0..t).map(|i| p1 - u256(i as u64)).collect(),
    ];
    for _ in 0..4 {
        inputs.push((0..t).map(|_| rand.next_word()).collect());
    }
    inputs
}
