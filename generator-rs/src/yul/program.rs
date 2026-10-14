// Straight-line Yul emitter backed by the shared bound tracker
// (yul/program.ts).
//
// Every operand is a Value whose name is the Yul text that produces it: a
// variable, a literal, an mload or a nested expression. expr() builds a
// nested expression and runs apply_op on it, so an ADD or MUL that could
// overflow uint256 fails before any text is written. let_(), assign() and
// mstore() are the only calls that emit statements.

use std::collections::HashMap;

use crate::bail;
use crate::error::Result;
use crate::field::{PRIME, U256, UINT256_MAX, hex};
use crate::value::{Op, Value, apply_op};

pub fn literal(c: U256) -> String {
    if c < U256::from(256u64) {
        c.to_string()
    } else {
        hex(c)
    }
}

fn rename(v: &Value, name: String) -> Result<Value> {
    Value::new(name, v.bound, v.vals.clone(), v.constant)
}

pub struct Program {
    pub lines: Vec<String>,
    /// every `let` is a stack slot until its block ends: the count per open
    /// block
    frames: Vec<usize>,
    vectors: usize,
    pub p: Value,
    level: usize,
    memory: HashMap<String, Value>,
}

impl Program {
    pub fn new(vectors: usize, level: usize) -> Program {
        Program {
            lines: Vec::new(),
            frames: vec![0],
            vectors,
            p: Value {
                name: "PRIME".to_string(),
                bound: PRIME,
                vals: vec![PRIME; vectors],
                constant: Some(PRIME),
            },
            level,
            memory: HashMap::new(),
        }
    }

    // ---- text --------------------------------------------------------------

    pub fn line(&mut self, text: &str) {
        self.lines
            .push(format!("{}{text}", "    ".repeat(self.level)));
    }

    pub fn comment(&mut self, text: &str) {
        self.line(&format!("// {text}"));
    }

    pub fn blank(&mut self) {
        self.lines.push(String::new());
    }

    pub fn open(&mut self) {
        self.line("{");
        self.level += 1;
        self.frames.push(0);
    }

    pub fn close(&mut self) {
        self.frames.pop();
        self.level -= 1;
        self.line("}");
    }

    /// slots currently held by `let`s of the open blocks
    pub fn live(&self) -> usize {
        self.frames.iter().sum()
    }

    // ---- values ------------------------------------------------------------

    pub fn constant(&self, c: U256) -> Value {
        Value {
            name: literal(c),
            bound: c,
            vals: vec![c; self.vectors],
            constant: Some(c),
        }
    }

    /// A caller-supplied word (function argument or calldata): any uint256.
    pub fn input(&self, name: &str, vals: Vec<U256>) -> Value {
        Value {
            name: name.to_string(),
            bound: UINT256_MAX,
            vals,
            constant: None,
        }
    }

    /// Nested expression; nothing is emitted. A result used more than once
    /// must be bound with let_() or the text would be evaluated twice.
    pub fn expr(&self, op: Op, args: &[&Value]) -> Result<Value> {
        let names: Vec<&str> = args.iter().map(|a| a.name.as_str()).collect();
        let name = format!("{}({})", op.text(), names.join(", "));
        apply_op(op, args, name, self.vectors)
    }

    pub fn let_(&mut self, name: &str, v: &Value) -> Result<Value> {
        *self.frames.last_mut().expect("open frame") += 1;
        self.line(&format!("let {name} := {}", v.name));
        rename(v, name.to_string())
    }

    pub fn assign(&mut self, name: &str, v: &Value) -> Result<Value> {
        self.line(&format!("{name} := {}", v.name));
        rename(v, name.to_string())
    }

    /// Store v at the address expression and return the value an mload of
    /// the same address yields from now on.
    pub fn mstore(&mut self, addr: &str, v: &Value) -> Result<Value> {
        self.line(&format!("mstore({addr}, {})", v.name));
        let loaded = rename(v, format!("mload({addr})"))?;
        self.memory.insert(addr.to_string(), loaded.clone());
        Ok(loaded)
    }

    pub fn mload(&self, addr: &str) -> Result<Value> {
        match self.memory.get(addr) {
            Some(v) => Ok(v.clone()),
            None => bail!("mload of {addr} before any mstore"),
        }
    }
}
