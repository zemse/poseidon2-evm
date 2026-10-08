// Bound-tracked field values shared by the Huff and Yul generators
// (shared/value.ts).
//
// A Value carries an exact upper bound (inclusive) and one concrete
// evaluation per test vector. apply_op is the single place that decides what
// an EVM arithmetic opcode does to a bound: ADD and MUL are only allowed when
// the result provably fits in uint256, ADDMOD / MULMOD / MOD reduce to
// PRIME - 1.

use crate::bail;
use crate::error::Result;
use crate::field::{PRIME, U256};

#[derive(Debug, Clone)]
pub struct Value {
    pub name: String,
    pub bound: U256,
    pub vals: Vec<U256>,
    pub constant: Option<U256>,
}

impl Value {
    pub fn new(
        name: String,
        bound: U256,
        vals: Vec<U256>,
        constant: Option<U256>,
    ) -> Result<Value> {
        if vals.iter().any(|v| *v > bound) {
            bail!("concrete value exceeds bound for {name}");
        }
        Ok(Value {
            name,
            bound,
            vals,
            constant,
        })
    }

    pub fn is_prime(&self) -> bool {
        self.constant == Some(PRIME)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add,
    Mul,
    Shl,
    Addmod,
    Mulmod,
    Mod,
}

impl Op {
    pub fn arity(self) -> usize {
        match self {
            Op::Add | Op::Mul | Op::Shl | Op::Mod => 2,
            Op::Addmod | Op::Mulmod => 3,
        }
    }

    pub fn text(self) -> &'static str {
        match self {
            Op::Add => "add",
            Op::Mul => "mul",
            Op::Shl => "shl",
            Op::Addmod => "addmod",
            Op::Mulmod => "mulmod",
            Op::Mod => "mod",
        }
    }
}

/// Result of op on args (first operand first, so shl takes the constant
/// shift first like the opcode), with the bound of the result and its
/// concrete value for each of the `vectors` test inputs.
pub fn apply_op(op: Op, args: &[&Value], name: String, vectors: usize) -> Result<Value> {
    let a = args[0];
    let b = args[1];
    let each = |f: &dyn Fn(usize) -> U256| (0..vectors).map(f).collect::<Vec<_>>();
    match op {
        Op::Add => {
            let Some(bound) = a.bound.checked_add(b.bound) else {
                bail!("add overflow: {} + {}", a.name, b.name);
            };
            Value::new(name, bound, each(&|i| a.vals[i] + b.vals[i]), None)
        }
        Op::Mul => {
            let Some(bound) = a.bound.checked_mul(b.bound) else {
                bail!("mul overflow: {} * {}", a.name, b.name);
            };
            Value::new(name, bound, each(&|i| a.vals[i] * b.vals[i]), None)
        }
        Op::Shl => {
            let Some(shift) = a.constant else {
                bail!("shl needs a constant shift");
            };
            let fits = b.bound.is_zero()
                || (shift < U256::from(256u64) && b.bound.leading_zeros() >= shift.to::<usize>());
            if !fits {
                bail!("shl overflow: {} << {}", b.name, a.name);
            }
            let shift = if b.bound.is_zero() {
                0
            } else {
                shift.to::<usize>()
            };
            Value::new(name, b.bound << shift, each(&|i| b.vals[i] << shift), None)
        }
        Op::Addmod => {
            if !args[2].is_prime() {
                bail!("addmod modulus must be PRIME");
            }
            Value::new(
                name,
                PRIME - U256::from(1u64),
                each(&|i| a.vals[i].add_mod(b.vals[i], PRIME)),
                None,
            )
        }
        Op::Mulmod => {
            if !args[2].is_prime() {
                bail!("mulmod modulus must be PRIME");
            }
            Value::new(
                name,
                PRIME - U256::from(1u64),
                each(&|i| a.vals[i].mul_mod(b.vals[i], PRIME)),
                None,
            )
        }
        Op::Mod => {
            if !b.is_prime() {
                bail!("mod modulus must be PRIME");
            }
            Value::new(
                name,
                PRIME - U256::from(1u64),
                each(&|i| a.vals[i].reduce_mod(PRIME)),
                None,
            )
        }
    }
}
