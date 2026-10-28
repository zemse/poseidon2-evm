use super::*;
use crate::error::Error;
use crate::huff::fork::fork;
use crate::huff::schedule::{Best, DEFAULT_OPTIONS};
use std::collections::VecDeque;

// Synthetic results test selection, not executable bytecode.
fn result(tag: &str, bytes: usize, gas: u64) -> Best {
    Best {
        opts: BuildOptions {
            shared_body: true,
            ..DEFAULT_OPTIONS
        },
        result: BuildResult {
            lines: vec![tag.to_string()],
            gas,
            bytes,
            max_depth: 3,
            max_dup: 2,
            swaps: 0,
            pops: 0,
            stores: 0,
            loads: 0,
            range: Range { from: 0, to: 65 },
            state_in_memory: true,
            input_slots: vec![None; 2],
            step_bytes: Vec::new(),
            memory: 64,
            tables: Vec::new(),
        },
    }
}

fn small_fork() -> Fork {
    let mut f = fork("osaka").unwrap();
    f.code_size = 500;
    f
}

fn choose(results: Vec<Result<Option<Best>>>) -> (Option<Best>, Vec<usize>) {
    let mut results: VecDeque<_> = results.into();
    let mut budgets = Vec::new();
    let chosen = entry_with_retry(2, small_fork(), |budget| {
        budgets.push(budget);
        results.pop_front().expect("no extra retry")
    })
    .unwrap();
    assert!(results.is_empty());
    (chosen, budgets)
}

#[test]
fn actual_wrapper_frees_a_bounded_retry_budget() {
    let prior = result("prior", 400, 500);
    let f = small_fork();
    let reserved = entry_bytes(f, 2, &[], false, MEMORY_UNKNOWN);
    let actual = entry_bytes(f, 2, &prior.result.input_slots, true, 64);
    assert!(actual < reserved);
    let retry = result("retry", f.code_size - actual, 499);
    let (chosen, budgets) = choose(vec![Ok(Some(prior)), Ok(Some(retry))]);
    assert_eq!(budgets, vec![f.code_size - reserved, f.code_size - actual]);
    let chosen = chosen.unwrap();
    assert_eq!(chosen.result.lines, ["retry"]);
    assert_eq!(chosen.result.bytes + actual, f.code_size);
}

#[test]
fn failed_missing_tied_and_slower_retries_keep_prior() {
    for retry in [
        Err(Error("failed candidate".to_string())),
        Ok(None),
        Ok(Some(result("tie", 410, 500))),
        Ok(Some(result("slower", 410, 501))),
    ] {
        let (chosen, budgets) = choose(vec![Ok(Some(result("prior", 400, 500))), retry]);
        assert_eq!(budgets.len(), 2);
        assert_eq!(chosen.unwrap().result.lines, ["prior"]);
    }
}

#[test]
fn retry_checks_its_own_wrapper_and_full_frame_cost() {
    let f = small_fork();
    let prior = result("prior", 400, 500);
    let actual = entry_bytes(f, 2, &prior.result.input_slots, true, 64);
    let mut oversized = result("oversized", f.code_size - actual, 0);
    oversized.result.state_in_memory = false;
    oversized.result.memory = 0;
    assert!(
        oversized.result.bytes + entry_bytes(f, 2, &oversized.result.input_slots, false, 0)
            > f.code_size
    );
    let mut dearer_wrapper = oversized.clone();
    dearer_wrapper.result.bytes = 400;
    dearer_wrapper.result.gas = 499;
    assert!(entry_gas(&f, 2, &dearer_wrapper.result) > entry_gas(&f, 2, &prior.result));
    for retry in [oversized, dearer_wrapper, result("overflow", usize::MAX, 0)] {
        let (chosen, _) = choose(vec![Ok(Some(prior.clone())), Ok(Some(retry))]);
        assert_eq!(chosen.unwrap().result.lines, ["prior"]);
    }
}

#[test]
fn retry_is_not_needed_without_binding_or_freed_bytes() {
    let mut unbound = result("unbound", 400, 500);
    unbound.opts.shared_body = false;
    let mut unchanged = result("same wrapper", 400, 500);
    unchanged.result.state_in_memory = false;
    unchanged.result.memory = 128;
    assert_eq!(
        entry_bytes(small_fork(), 2, &unchanged.result.input_slots, false, 128),
        entry_bytes(small_fork(), 2, &[], false, MEMORY_UNKNOWN)
    );
    for prior in [unbound, unchanged] {
        let (chosen, budgets) = choose(vec![Ok(Some(prior))]);
        assert!(chosen.is_some());
        assert_eq!(budgets.len(), 1);
    }
}

#[test]
fn impossible_initial_budgets_do_not_wrap_or_retry() {
    let mut f = small_fork();
    f.code_size = 0;
    assert!(
        entry_with_retry(2, f, |_| panic!("wrapper exceeds limit"))
            .unwrap()
            .is_none()
    );
    f.code_size = entry_bytes(f, 2, &[], false, MEMORY_UNKNOWN);
    assert!(
        entry_with_retry(2, f, |budget| {
            assert_eq!(budget, 0);
            Ok(None)
        })
        .unwrap()
        .is_none()
    );
    let (missing, calls) = choose(vec![Ok(None)]);
    assert!(missing.is_none());
    assert_eq!(calls.len(), 1);
    let (oversized, calls) = choose(vec![Ok(Some(result("invalid", usize::MAX, 0)))]);
    assert!(oversized.is_none());
    assert_eq!(calls.len(), 1);
    assert!(
        entry_with_retry(2, small_fork(), |_| Err(Error(
            "initial failure".to_string()
        )))
        .is_err()
    );
}
