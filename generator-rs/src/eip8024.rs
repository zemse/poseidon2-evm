// A corpus of small programs around EIP-8024 (DUPN, SWAPN, EXCHANGE) and what
// revm's Amsterdam interpreter does with each: every immediate byte, stack
// depths at the underflow and overflow boundaries, the immediate cut by the
// end of the code, the gas boundary, the EIP's own execution tests, jumps
// into immediates and a few sequences. formal-verification/scripts/
// Eip8024Diff.lean runs the same programs through the Lean overlay
// (Evm/Eip8024.lean) and compares; scripts/eip8024-diff.sh runs both.
//
// One line per program: `<family> <code hex> <depth> <gas> <result>`. The
// program starts with `depth` stack items 1, 2, .., depth (1 on top), `gas`
// gas and pc 0, and runs to its end. The result is `stop <gas left> <stack>`
// (the stack top first, runs of consecutive numbers as `a..b`) or
// `halt <reason>` for an exceptional halt.

use revm::bytecode::Bytecode;
use revm::interpreter::host::DummyHost;
use revm::interpreter::interpreter::{EthInterpreter, ExtBytecode};
use revm::interpreter::{
    InputsImpl, InstructionResult, Interpreter, InterpreterAction, SharedMemory, gas_table,
    instruction_table,
};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Bytes, U256, hex};

pub const DUPN: u8 = 0xe6;
pub const SWAPN: u8 = 0xe7;
pub const EXCHANGE: u8 = 0xe8;

/// One program of the corpus.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub family: &'static str,
    pub code: Vec<u8>,
    pub depth: usize,
    pub gas: u64,
}

/// EIP-8024 `decode_single`.
pub fn decode_single(x: u8) -> Option<usize> {
    (x <= 90 || x >= 128).then(|| (x as usize + 145) % 256)
}

/// EIP-8024 `decode_pair`.
pub fn decode_pair(x: u8) -> Option<(usize, usize)> {
    if x > 81 && x < 128 {
        return None;
    }
    let k = (x ^ 143) as usize;
    let (q, r) = (k / 16, k % 16);
    Some(if q < r {
        (q + 1, r + 1)
    } else {
        (r + 1, 29 - q)
    })
}

/// The stack items the opcode needs with immediate `x`, `None` for an
/// invalid immediate.
fn needs(op: u8, x: u8) -> Option<usize> {
    match op {
        DUPN => decode_single(x),
        SWAPN => decode_single(x).map(|n| n + 1),
        _ => decode_pair(x).map(|(_, m)| m + 1),
    }
}

/// The EIP's execution tests (stack from the code alone).
pub const EIP_TESTS: [&str; 10] = [
    "60016000808080808080808080808080808080e680",
    "600160008080808080808080808080808080806002e780",
    "600260008080808080600160008080808080808080e8",
    "600060016002e88e",
    "600080808080808080808080808080808080808080808080808080808060016002e88f",
    "e75b",
    "600456e65b",
    "60008080e88e15",
    "e852",
    "6000808080808080808080808080808080e680",
];

/// The corpus, in a fixed order.
pub fn corpus() -> Vec<Program> {
    let mut out = Vec::new();
    let mut add = |family, code: Vec<u8>, depth, gas| {
        out.push(Program {
            family,
            code,
            depth,
            gas,
        })
    };
    for op in [DUPN, SWAPN, EXCHANGE] {
        // every immediate, at the stack depths around the boundaries
        for x in 0..=255u8 {
            let depths = match needs(op, x) {
                Some(n) => vec![0, n - 1, n, 1023, 1024],
                None => vec![0, 300],
            };
            for d in depths {
                add("imm", vec![op, x], d, 100);
            }
        }
        // the immediate past the end of the code reads 0
        let n = needs(op, 0).expect("0 is a valid immediate");
        for d in [n - 1, n, 1024] {
            add("trunc", vec![op], d, 100);
        }
        // the gas boundary, and an invalid immediate or a short stack with too
        // little gas (the order of the checks differs, the halt does not)
        let x = if op == EXCHANGE { 0x8e } else { 0x80 };
        for g in [0, 2, 3, 4] {
            add("gas", vec![op, x], 40, g);
        }
        add("gas", vec![op, 0x5b], 40, 2);
        add("gas", vec![op, x], 0, 2);
        // jumps to the opcode, its immediate and the byte after
        for imm in [0x5b, 0x80, 0x60, 0x5f, 0x00, 0x8e] {
            for t in [3u8, 4, 5] {
                add("jump", vec![0x60, t, 0x56, op, imm, 0x5b, 0x00], 300, 1000);
            }
        }
    }
    for code in EIP_TESTS {
        add("eip", hex::decode(code).expect("hex"), 0, 1000);
    }
    // sequences: pc advances by 2 each time
    for code in [
        "e680e680e680",
        "e680e7808ee88e",
        "e6ffe7ffe8ff5f",
        "e65ae75a",
        "e88e5be88e",
        "e6805b600656e65b5b",
    ] {
        add("seq", hex::decode(code).expect("hex"), 240, 1000);
    }
    // a PUSH cut by the end of the code: the EVM pads it with zeros on the
    // right, EVMLean reads only the bytes there are (a known deviation, the
    // checker never runs such a PUSH)
    for code in ["61ab", "62abcd", "7fab", "6001"] {
        add("pushtrunc", hex::decode(code).expect("hex"), 0, 100);
    }
    out
}

/// A stack, top first, with runs of consecutive numbers as `a..b`.
pub fn render_stack(top_first: &[U256]) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut i = 0;
    while i < top_first.len() {
        let mut j = i;
        while j + 1 < top_first.len() && top_first[j + 1] == top_first[j] + U256::from(1) {
            j += 1;
        }
        if j > i {
            parts.push(format!("{}..{}", top_first[i], top_first[j]));
        } else {
            parts.push(top_first[i].to_string());
        }
        i = j + 1;
    }
    format!("[{}]", parts.join(","))
}

/// The reason of an exceptional halt, in the words the Lean side uses.
fn reason(r: InstructionResult) -> String {
    match r {
        InstructionResult::OutOfGas => "oog".into(),
        InstructionResult::StackUnderflow => "underflow".into(),
        InstructionResult::StackOverflow => "overflow".into(),
        InstructionResult::InvalidImmediateEncoding
        | InstructionResult::InvalidFEOpcode
        | InstructionResult::OpcodeNotFound => "invalid".into(),
        InstructionResult::InvalidJump => "badjump".into(),
        other => format!("{other:?}"),
    }
}

/// Runs a program on revm's interpreter at Amsterdam.
pub fn run(p: &Program) -> String {
    let bytecode = Bytecode::new_raw(Bytes::copy_from_slice(&p.code));
    let mut interp = Interpreter::<EthInterpreter>::new(
        SharedMemory::new(),
        ExtBytecode::new(bytecode),
        InputsImpl::default(),
        false,
        SpecId::AMSTERDAM,
        p.gas,
    );
    for v in (1..=p.depth).rev() {
        assert!(interp.stack.push(U256::from(v)), "stack limit");
    }
    let table = instruction_table::<EthInterpreter, DummyHost>();
    let mut host = DummyHost::new(SpecId::AMSTERDAM);
    let action = interp.run_plain(&table, &gas_table(), &mut host);
    let InterpreterAction::Return(res) = action else {
        return "halt newframe".into();
    };
    match res.result {
        InstructionResult::Stop | InstructionResult::Return => {
            let mut stack: Vec<U256> = interp.stack.data().to_vec();
            stack.reverse();
            format!("stop {} {}", res.gas.remaining(), render_stack(&stack))
        }
        InstructionResult::Revert => format!("revert {}", res.gas.remaining()),
        r => format!("halt {}", reason(r)),
    }
}

/// The corpus with revm's results, one line per program.
pub fn lines() -> Vec<String> {
    corpus()
        .iter()
        .map(|p| {
            format!(
                "{} {} {} {} {}",
                p.family,
                hex::encode(&p.code),
                p.depth,
                p.gas,
                run(p)
            )
        })
        .collect()
}
