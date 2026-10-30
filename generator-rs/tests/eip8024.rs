// The EIP-8024 corpus (eip8024.rs): revm on the EIP's own test cases, the
// immediate decoding against the EIP's encoders, and the shape of the corpus
// that formal-verification/scripts/Eip8024Diff.lean compares with the Lean
// overlay.

use poseidon2_gen::eip8024::{
    EIP_TESTS, Program, corpus, decode_pair, decode_single, lines, render_stack, run,
};
use revm::primitives::{U256, hex};

fn eip(code: &str) -> String {
    run(&Program {
        family: "eip",
        code: hex::decode(code).unwrap(),
        depth: 0,
        gas: 1000,
    })
}

fn stack(top_first: &[u64]) -> String {
    render_stack(&top_first.iter().map(|&v| U256::from(v)).collect::<Vec<_>>())
}

/// `stop <gas left> <stack>` with the stack as given
fn stopped(result: &str, top_first: &[u64]) {
    let mut words = result.splitn(3, ' ');
    assert_eq!(words.next(), Some("stop"), "{result}");
    words.next();
    assert_eq!(words.next(), Some(stack(top_first).as_str()), "{result}");
}

#[test]
fn eip_execution_tests() {
    // 18 items, top and bottom 1, the rest 0
    let mut s = vec![1];
    s.extend([0; 16]);
    s.push(1);
    stopped(&eip(EIP_TESTS[0]), &s);
    // 18 items, top 1, bottom 2, the rest 0
    let mut s = vec![1];
    s.extend([0; 16]);
    s.push(2);
    stopped(&eip(EIP_TESTS[1]), &s);
    // EXCHANGE at the end of the code: 17 items, bottom 1, the 10th from the
    // top 2, the rest 0
    let mut s = vec![0; 17];
    s[16] = 1;
    s[9] = 2;
    stopped(&eip(EIP_TESTS[2]), &s);
    stopped(&eip(EIP_TESTS[3]), &[2, 0, 1]);
    // 30 items, top 2, bottom 1, the rest 0
    let mut s = vec![0; 30];
    s[0] = 2;
    s[29] = 1;
    stopped(&eip(EIP_TESTS[4]), &s);
    assert_eq!(eip(EIP_TESTS[5]), "halt invalid");
    stopped(&eip(EIP_TESTS[6]), &[]);
    stopped(&eip(EIP_TESTS[7]), &[1, 0, 0]);
    assert_eq!(eip(EIP_TESTS[8]), "halt invalid");
    // 17 items and DUPN 17 on 16 of them: revm says StackOverflow (its `dup`
    // fails both ways), the EIP an exceptional halt
    assert!(eip(EIP_TESTS[9]).starts_with("halt "));
}

/// The EIP's `encode_single` and `encode_pair`.
fn encode_single(n: usize) -> u8 {
    ((n + 111) % 256) as u8
}

fn encode_pair(n: usize, m: usize) -> u8 {
    let (q, r) = if m <= 16 {
        (n - 1, m - 1)
    } else {
        (29 - m, n - 1)
    };
    ((16 * q + r) ^ 143) as u8
}

#[test]
fn decoding_inverts_encoding() {
    for n in 17..=235 {
        assert_eq!(decode_single(encode_single(n)), Some(n));
    }
    let mut pairs = 0;
    for n in 1..=14 {
        for m in n + 1..=30 - n {
            assert_eq!(decode_pair(encode_pair(n, m)), Some((n, m)));
            pairs += 1;
        }
    }
    // every valid immediate is some pair
    let valid = (0..=255u8).filter(|&x| decode_pair(x).is_some()).count();
    assert_eq!(valid, pairs);
}

#[test]
fn corpus_shape() {
    let c = corpus();
    for family in ["imm", "trunc", "gas", "jump", "eip", "seq", "pushtrunc"] {
        assert!(c.iter().any(|p| p.family == family), "{family}");
    }
    let l = lines();
    assert_eq!(l.len(), c.len());
    // every immediate of every opcode, valid ones at five depths
    assert!(c.iter().filter(|p| p.family == "imm").count() > 3 * 256 * 2);
    // a few results pinned: DUPN 17 on 17 items, SWAPN 17 on 17 items
    assert!(l.contains(&"imm e680 17 100 stop 97 [17,1..17]".to_string()));
    assert!(l.contains(&"imm e780 17 100 halt underflow".to_string()));
}
