// BN254 scalar field arithmetic on 256-bit integers (shared/field.ts).

pub use ruint::aliases::{U256, U512};
use ruint::uint;

pub const PRIME: U256 =
    uint!(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001_U256);

pub const UINT256_MAX: U256 = U256::MAX;

pub fn reduce(a: U256) -> U256 {
    a.reduce_mod(PRIME)
}

pub fn add(a: U256, b: U256) -> U256 {
    a.add_mod(b, PRIME)
}

pub fn mul(a: U256, b: U256) -> U256 {
    a.mul_mod(b, PRIME)
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
    assert!(!reduce(a).is_zero(), "inverse of zero");
    pow(a, PRIME - U256::from(2u64))
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
    fn arithmetic() {
        assert_eq!(mul(inv(u256(7)), u256(7)), u256(1));
        assert_eq!(sub(u256(1), u256(2)), PRIME - u256(1));
        assert_eq!(to_f64(u256(1) << 60), 2f64.powi(60));
    }
}
