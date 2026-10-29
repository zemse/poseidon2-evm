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
fn alternatives_keep_the_completed_serial_retry_on_failure_or_regression() {
    let f = small_fork();
    let initial = result("initial", 400, 600);
    let prior = result(
        "serial retry",
        f.code_size - entry_wrapper(2, f, &initial.result),
        500,
    );
    let (serial, _) = choose(vec![Ok(Some(initial)), Ok(Some(prior.clone()))]);
    let mut oversized = result("larger wrapper", prior.result.bytes, 0);
    oversized.result.state_in_memory = false;
    oversized.result.memory = 0;
    let mut deep = result("too deep", 400, 0);
    deep.result.max_depth = 1001;
    let mut dearer = result("cheaper core", 400, 499);
    dearer.result.state_in_memory = false;
    dearer.result.memory = 0;
    assert!(entry_gas(&f, 2, &dearer.result) > entry_gas(&f, 2, &prior.result));
    for alternative in [
        Err(Error("failed alternative".to_string())),
        Ok(None),
        Ok(Some(result("tie", 400, 500))),
        Ok(Some(result("slower", 400, 501))),
        Ok(Some(oversized)),
        Ok(Some(deep)),
        Ok(Some(dearer)),
        Ok(Some(result("overflow", usize::MAX, 0))),
    ] {
        let mut alternative = Some(alternative);
        let chosen = improve_entry(2, f, serial.clone(), |budget, seed| {
            assert_eq!(seed.result.lines, ["serial retry"]);
            assert_eq!(budget, f.code_size - entry_wrapper(2, f, &seed.result));
            alternative.take().expect("one attempt")
        })
        .unwrap();
        assert_eq!(chosen.result.lines, ["serial retry"]);
        assert!(alternative.is_none());
    }
    assert!(improve_entry(2, f, None, |_, _| panic!("no serial seed")).is_none());
}

#[test]
fn alternative_retry_uses_its_own_wrapper_and_keeps_a_valid_improvement() {
    let f = small_fork();
    let mut prior = result("serial", 350, 600);
    prior.result.state_in_memory = false;
    prior.result.memory = 0;
    let candidate = result("fused", 400, 500);
    let actual = entry_wrapper(2, f, &candidate.result);
    let mut oversized = result("bad retry", f.code_size - actual, 0);
    oversized.result.state_in_memory = false;
    oversized.result.memory = 0;
    let mut results = VecDeque::from([Ok(Some(candidate)), Ok(Some(oversized))]);
    let mut budgets = Vec::new();
    let reserved = entry_wrapper(2, f, &prior.result);
    let chosen = improve_entry(2, f, Some(prior), |budget, _| {
        budgets.push(budget);
        results.pop_front().expect("no extra retry")
    })
    .unwrap();
    assert_eq!(budgets, [f.code_size - reserved, f.code_size - actual]);
    assert!(results.is_empty());
    assert_eq!(chosen.result.lines, ["fused"]);
}

#[test]
fn seeded_alternatives_keep_the_completed_fused_retry() {
    let f = small_fork();
    let mut serial = result("serial", 350, 600);
    serial.result.state_in_memory = false;
    serial.result.memory = 0;
    let initial = result("fused initial", 400, 500);
    let mut retry = result(
        "fused retry",
        f.code_size - entry_wrapper(2, f, &initial.result),
        490,
    );
    retry.opts.fused_tree = schedule::FusedTree::PreplacedBounded;
    let mut results = VecDeque::from([Ok(Some(initial)), Ok(Some(retry.clone()))]);
    let completed = improve_entry(2, f, Some(serial), |_, _| {
        results.pop_front().expect("no extra retry")
    });
    assert!(results.is_empty());
    assert_eq!(completed.as_ref().unwrap().result.lines, ["fused retry"]);
    let mut oversized = result("larger wrapper", retry.result.bytes, 0);
    oversized.result.state_in_memory = false;
    oversized.result.memory = 0;
    let mut deep = result("too deep", 400, 0);
    deep.result.max_depth = 1001;
    let mut dearer = result("cheaper core", 400, 489);
    dearer.result.state_in_memory = false;
    dearer.result.memory = 0;
    assert!(entry_gas(&f, 2, &dearer.result) > entry_gas(&f, 2, &retry.result));
    for alternative in [
        Err(Error("failed seed".to_string())),
        Ok(None),
        Ok(Some(result("tie", 400, 490))),
        Ok(Some(result("slower", 400, 491))),
        Ok(Some(oversized)),
        Ok(Some(deep)),
        Ok(Some(dearer)),
        Ok(Some(result("overflow", usize::MAX, 0))),
    ] {
        let mut alternative = Some(alternative);
        let chosen = improve_entry(2, f, completed.clone(), |budget, prior| {
            assert_eq!(prior.result.lines, ["fused retry"]);
            assert_eq!(prior.opts, retry.opts);
            assert_eq!(budget, f.code_size - entry_wrapper(2, f, &prior.result));
            alternative.take().expect("one attempt")
        })
        .unwrap();
        assert_eq!(chosen.result.lines, ["fused retry"]);
        assert!(alternative.is_none());
    }
    let chosen =
        improve_entry(2, f, completed, |_, _| Ok(Some(result("seeded", 400, 489)))).unwrap();
    assert_eq!(chosen.result.lines, ["seeded"]);
}

#[test]
fn slot_alternatives_keep_the_completed_seeded_retry() {
    let f = small_fork();
    let mut fused = result("fused", 350, 600);
    fused.result.state_in_memory = false;
    fused.result.memory = 0;
    let initial = result("seeded initial", 400, 500);
    let mut retry = result(
        "seeded retry",
        f.code_size - entry_wrapper(2, f, &initial.result),
        490,
    );
    retry.opts.fused_tree = schedule::FusedTree::PreplacedSeeded;
    retry.opts.consume_slots = 14;
    let mut results = VecDeque::from([Ok(Some(initial)), Ok(Some(retry.clone()))]);
    let completed = improve_entry(2, f, Some(fused), |_, _| {
        results.pop_front().expect("no extra retry")
    });
    assert!(results.is_empty());
    assert_eq!(completed.as_ref().unwrap().result.lines, ["seeded retry"]);
    let mut oversized = result("larger wrapper", retry.result.bytes, 0);
    oversized.result.state_in_memory = false;
    oversized.result.memory = 0;
    let mut deep = result("too deep", 400, 0);
    deep.result.max_depth = 1001;
    let mut dearer = result("cheaper core", 400, 489);
    dearer.result.state_in_memory = false;
    dearer.result.memory = 0;
    assert!(entry_gas(&f, 2, &dearer.result) > entry_gas(&f, 2, &retry.result));
    for alternative in [
        Err(Error("invalid layout bounds".to_string())),
        Ok(None),
        Ok(Some(result("tie", 400, 490))),
        Ok(Some(result("slower", 400, 491))),
        Ok(Some(oversized)),
        Ok(Some(deep)),
        Ok(Some(dearer)),
        Ok(Some(result("overflow", usize::MAX, 0))),
    ] {
        let mut alternative = Some(alternative);
        let chosen = improve_entry(2, f, completed.clone(), |budget, prior| {
            assert_eq!(prior.result.lines, ["seeded retry"]);
            assert_eq!(prior.opts, retry.opts);
            assert_eq!(budget, f.code_size - entry_wrapper(2, f, &prior.result));
            alternative.take().expect("one attempt")
        })
        .unwrap();
        assert_eq!(chosen.result.lines, ["seeded retry"]);
        assert!(alternative.is_none());
    }
    let chosen = improve_entry(2, f, completed, |_, _| {
        Ok(Some(result("neighbour", 400, 489)))
    })
    .unwrap();
    assert_eq!(chosen.result.lines, ["neighbour"]);
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
