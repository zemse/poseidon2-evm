// BN254 scalar field arithmetic on 256-bit integers (shared/field.ts).

pub use ruint::aliases::{U256, U512};
use ruint::uint;

pub const PRIME: U256 =
    uint!(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001_U256);

pub const UINT256_MAX: U256 = U256::MAX;

/// a mod PRIME for any a: 2^256 < 6 PRIME, so at most five subtractions.
pub fn reduce(mut a: U256) -> U256 {
    while a >= PRIME {
        a -= PRIME;
    }
    a
}

/// (a + b) mod PRIME for any a, b.
pub fn add(a: U256, b: U256) -> U256 {
    // two reduced values sum below 2 PRIME < 2^255
    let s = reduce(a) + reduce(b);
    if s >= PRIME { s - PRIME } else { s }
}

/// (a * b) mod PRIME for any a, b, by Montgomery multiplication.
pub fn mul(a: U256, b: U256) -> U256 {
    let ab = mont_mul(reduce(a).as_limbs(), reduce(b).as_limbs());
    U256::from_limbs(mont_mul(&ab, &R2))
}

const P_LIMBS: [u64; 4] = [
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

/// -PRIME^-1 mod 2^64
const P_INV: u64 = {
    let mut inv: u64 = 1;
    let mut i = 0;
    while i < 6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(P_LIMBS[0].wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
};

/// 2^512 mod PRIME
const R2: [u64; 4] = [
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
];

fn mac(acc: u64, a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = u128::from(acc) + u128::from(a) * u128::from(b) + u128::from(carry);
    (t as u64, (t >> 64) as u64)
}

/// a b 2^-256 mod PRIME for a, b < PRIME (CIOS).
fn mont_mul(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut t = [0u64; 6];
    for &bi in b {
        let mut carry = 0;
        for j in 0..4 {
            (t[j], carry) = mac(t[j], a[j], bi, carry);
        }
        let s = u128::from(t[4]) + u128::from(carry);
        t[4] = s as u64;
        t[5] = (s >> 64) as u64;
        let m = t[0].wrapping_mul(P_INV);
        let (_, mut carry) = mac(t[0], m, P_LIMBS[0], 0);
        for j in 1..4 {
            (t[j - 1], carry) = mac(t[j], m, P_LIMBS[j], carry);
        }
        let s = u128::from(t[4]) + u128::from(carry);
        t[3] = s as u64;
        t[4] = t[5] + (s >> 64) as u64;
    }
    // below 2 PRIME < 2^256, so t[4] is zero
    let r = U256::from_limbs([t[0], t[1], t[2], t[3]]);
    let r = if r >= PRIME { r - PRIME } else { r };
    r.into_limbs()
}

/// (a - b) mod PRIME for any a, b.
pub fn sub(a: U256, b: U256) -> U256 {
    let (a, b) = (reduce(a), reduce(b));
    if a >= b { a - b } else { a + (PRIME - b) }
}

pub fn neg(a: U256) -> U256 {
    sub(U256::ZERO, a)
}

pub fn pow(base: U256, exp: U256) -> U256 {
    let mut result = U256::from(1u64);
    let mut b = reduce(base);
    let mut e = exp;
    while !e.is_zero() {
        if e.bit(0) {
            result = mul(result, b);
        }
        b = mul(b, b);
        e >>= 1;
    }
    result
}

pub fn inv(a: U256) -> U256 {
    reduce(a).inv_mod(PRIME).expect("inverse of zero")
}

/// Lowercase hex without leading zeros, like BigInt `toString(16)`.
pub fn hex_digits(value: U256) -> String {
    format!("{value:x}")
}

/// "0x" and 64 hex digits.
pub fn hex(value: U256) -> String {
    format!("0x{:0>64}", hex_digits(value))
}

/// The double nearest to the integer, like `Number(bigint)`.
pub fn to_f64(value: U256) -> f64 {
    // the decimal string parses with correct rounding
    value.to_string().parse().expect("decimal digits")
}

pub fn u256(n: u64) -> U256 {
    U256::from(n)
}

pub fn wide(a: U256) -> U512 {
    U512::from(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_formats() {
        assert_eq!(hex_digits(U256::ZERO), "0");
        assert_eq!(hex_digits(u256(255)), "ff");
        assert_eq!(
            hex(u256(1)),
            "0x0000000000000000000000000000000000000000000000000000000000000001"
        );
        assert_eq!(
            hex(PRIME),
            "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
        );
    }

    #[test]
    fn montgomery_matches_ruint() {
        let mut rand = crate::vectors::Prng::new(7);
        let mut words = vec![
            U256::ZERO,
            u256(1),
            PRIME - u256(1),
            PRIME,
            PRIME + u256(1),
            U256::MAX,
        ];
        for _ in 0..200 {
            // full 256-bit words, not reduced
            words.push(rand.next_word() << 3 | u256(rand.next_word().as_limbs()[0] & 7));
        }
        for &a in &words {
            for &b in &words[..40] {
                assert_eq!(mul(a, b), a.mul_mod(b, PRIME));
                assert_eq!(add(a, b), a.add_mod(b, PRIME));
            }
            assert_eq!(reduce(a), a.reduce_mod(PRIME));
        }
    }

    #[test]
    fn arithmetic() {
        assert_eq!(mul(inv(u256(7)), u256(7)), u256(1));
        assert_eq!(sub(u256(1), u256(2)), PRIME - u256(1));
        assert_eq!(to_f64(u256(1) << 60), 2f64.powi(60));
    }
}
