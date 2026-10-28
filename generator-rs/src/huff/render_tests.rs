use super::*;
use crate::huff::fork::fork;

fn ops(code: &Code) -> String {
    code.lines
        .iter()
        .map(|line| line.split("//").next().unwrap().trim())
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn compact_loads_count_only_present_slots() {
    let slots = [None, Some(RAW_INPUT), Some(COMPACT_INPUT), None];
    for name in ["paris", "osaka", "amsterdam"] {
        let mut code = Code::new(fork(name).unwrap());
        loads(&mut code, 4, &slots, 0, true);
        assert_eq!(
            ops(&code),
            "SETUP() dup1 0x60 calldataload mod 0x0 dup3 0x0 calldataload mod"
        );
        assert_eq!(code.gas, if name == "paris" { 34 } else { 32 });
        assert_eq!(code.bytes, if name == "paris" { 45 } else { 43 });
        assert_eq!(
            code.lines.last().unwrap().split("// ").nth(1).unwrap(),
            "[s0, 0, s3, PRIME]"
        );
    }
}

#[test]
fn compact_loads_preserve_prime_reach_and_lazy_entries() {
    let mut slots = vec![None; 20];
    slots[16..].fill(Some(COMPACT_INPUT));
    let fork = fork("osaka").unwrap();
    let mut code = Code::new(fork);
    loads(&mut code, 20, &slots, 0, true);
    let text = ops(&code);
    assert!(!text.contains("[PRIME]"));
    assert!(text.contains("dup16 0x0 calldataload mod"));
    assert_eq!(text.matches("calldataload").count(), 16);
    assert!(!text.contains("mstore"));
    let mut lazy = Code::new(fork);
    loads(&mut lazy, 20, &slots, 0, false);
    let text = ops(&lazy);
    assert!(!text.contains("dup"));
    assert!(!text.contains("mod"));
    assert_eq!(text.matches("calldataload").count(), 16);
    assert_eq!(lazy.gas, 98);
}
