// Cuts a permutation that does not fit the fork's code size into parts at
// step boundaries (huff/split.ts). Every hop costs the same whatever the
// cut, so the fewest parts cost the least gas unless a part only fits
// through the dearest schedules: a greedy pass finds that number by
// extending each part as far as the size allows (with the shared body of
// the internal rounds, at its shortest period, where that holds more), then
// the cuts are moved to balance the bytes so every part keeps the same
// slack, and fewer parts are kept while they build and cost less. Each part
// is built like a whole permutation (option search, bound tracker, reference
// check of its own steps); a part after the first takes its inputs as the
// part before leaves them, lazy below the hand-over bound (part_boundary),
// so its entry neither reduces nor stores them.

use rayon::prelude::*;

use super::fork::Fork;
use super::render::{Overhead, overhead};
use super::schedule::{
    Best, BuildOptions, DEFAULT_OPTIONS, Range, build_best, build_best_with,
    build_permutation_with, group_candidates, largest, part_boundary, step_count,
};
use crate::bail;
use crate::error::Result;
use crate::field::U256;
use crate::round_constants::Params;

#[derive(Debug, Clone)]
pub struct Part {
    pub best: Best,
    pub overhead: Overhead,
}

/// the initcode is CONSTRUCTOR (11 bytes), the runtime and the address word
const CONSTRUCTOR_BYTES: usize = 11;

pub fn split_permutation(params: &Params, inputs: &[Vec<U256>], fork: Fork) -> Result<Vec<Part>> {
    let t = params.t;
    let steps = step_count(params);
    // entry and tail at their largest (every input shadowed, PUSH2 offsets),
    // and the address word a part that hands over keeps behind its code
    let all_slots = vec![Some(0xffff); t];
    let word = |to: usize| if to < steps { 32 } else { 0 };
    // a part after the first takes its inputs lazy from calldata (no
    // reduction, no slots)
    let budget = |range: Range| {
        let Range { from, to } = range;
        let slots: &[Option<usize>] = if from == 0 { &all_slots } else { &[] };
        fork.code_size - overhead(fork, t, slots, true, to < steps, from > 0).bytes - word(to)
    };
    let boundary = |range: Range| part_boundary(t, range.from);

    // options for the size probes: the cheapest schedule of a short range,
    // which also decides whether the state needs shadowing
    let probe = build_best(
        params,
        inputs,
        usize::MAX,
        fork,
        Range {
            from: 0,
            to: steps.min(6),
        },
    )?;
    let Some(probe) = probe else {
        bail!("the first steps do not build");
    };
    let probe_opts = BuildOptions {
        shadow: probe.opts.shadow,
        diag_in_memory: probe.opts.diag_in_memory,
        ..DEFAULT_OPTIONS
    };
    // the shared body of the steady internal rounds lets a part hold far
    // more of them: the probe also tries that schedule (as the option
    // search will), with the steady rounds it needs inline, as one chain
    // and in the sub-chains of the shortest period
    let body_opts = BuildOptions {
        internal_consume: true,
        prime_stack: true,
        shared_body: true,
        ..probe_opts
    };
    let mut groups = vec![0];
    groups.extend(group_candidates(params, &fork).first());
    let fits = |opts: &BuildOptions, range: Range| -> bool {
        match build_permutation_with(params, inputs, opts, fork, range, false, &boundary(range)) {
            Ok(r) => r.max_depth <= 1000 && r.bytes <= budget(range),
            Err(_) => false,
        }
    };
    let builds = |range: Range| -> bool {
        fits(&probe_opts, range)
            || (t >= 8
                && groups.iter().any(|&consume_group| {
                    (0..3).any(|body_inline| {
                        fits(
                            &BuildOptions {
                                body_inline,
                                consume_group,
                                ..body_opts
                            },
                            range,
                        )
                    })
                }))
    };

    // fewest parts: extend each as far as it fits
    let mut greedy: Vec<Range> = Vec::new();
    let mut step_bytes: Vec<usize> = Vec::new();
    let mut from = 0;
    while from < steps {
        let len = largest(steps - from, |n| {
            n == 0 || builds(Range { from, to: from + n })
        });
        if len == 0 {
            bail!("step {from} alone exceeds the code size on {}", fork.name);
        }
        let range = Range {
            from,
            to: from + len,
        };
        let r = build_permutation_with(
            params,
            inputs,
            &probe_opts,
            fork,
            range,
            false,
            &boundary(range),
        )?;
        let mut prev = 0;
        for b in r.step_bytes {
            step_bytes.push(b - prev);
            prev = b;
        }
        greedy.push(range);
        from += len;
    }

    // cuts that balance the bytes of the steps over `count` parts
    let balance = |count: usize, weights: &[usize]| -> Vec<Range> {
        let total: usize = weights.iter().sum();
        let mut ranges = Vec::new();
        let mut from = 0;
        let mut sum = 0;
        for (step, w) in weights.iter().enumerate().take(steps) {
            sum += w;
            let j = ranges.len() + 1;
            // the TS divides in doubles
            if j < count && sum as f64 >= (j * total) as f64 / count as f64 {
                ranges.push(Range { from, to: step + 1 });
                from = step + 1;
            }
        }
        ranges.push(Range { from, to: steps });
        ranges
    };

    // the bytes of each step as built parts had them
    let measured = |parts: &[Part]| -> Vec<usize> {
        let mut weights = Vec::new();
        for part in parts {
            let mut prev = 0;
            for &b in &part.best.result.step_bytes {
                weights.push(b - prev);
                prev = b;
            }
        }
        weights
    };

    // every part is searched in parallel; the first missing part (in order)
    // makes the split fail, the first oversized one is an error, as in the
    // sequential TS
    let build = |ranges: Vec<Range>| -> Result<Option<Vec<Part>>> {
        let bests: Vec<Result<Option<Best>>> = ranges
            .par_iter()
            .map(|&range| {
                build_best_with(params, inputs, budget(range), fork, range, &boundary(range))
            })
            .collect();
        let mut parts = Vec::new();
        for (range, best) in ranges.iter().zip(bests) {
            let Some(best) = best? else {
                return Ok(None);
            };
            let result = &best.result;
            let o = overhead(
                fork,
                t,
                &result.input_slots,
                result.state_in_memory,
                range.to < steps,
                range.from > 0,
            );
            let runtime = result.bytes + o.bytes;
            if runtime + word(range.to) > fork.code_size {
                bail!("part {}..{}: {runtime} bytes", range.from, range.to);
            }
            if CONSTRUCTOR_BYTES + runtime + 32 > fork.initcode_size {
                bail!("part {}..{}: initcode too large", range.from, range.to);
            }
            parts.push(Part { best, overhead: o });
        }
        Ok(Some(parts))
    };
    let gas = |parts: &[Part]| -> u64 {
        parts
            .iter()
            .map(|p| p.overhead.entry_gas + p.best.result.gas + p.overhead.tail_gas)
            .sum()
    };
    let cheaper = |a: Option<Vec<Part>>, b: Option<Vec<Part>>| match (a, b) {
        (Some(a), Some(b)) => Some(if gas(&b) < gas(&a) { b } else { a }),
        (a, b) => a.or(b),
    };
    // both candidates of a comparison are built at once; the first error in
    // the TS evaluation order wins
    let both = |a: Vec<Range>, b: Vec<Range>| -> Result<Option<Vec<Part>>> {
        let (a, b) = rayon::join(|| build(a), || build(b));
        Ok(cheaper(a?, b?))
    };

    let Some(mut parts) = both(balance(greedy.len(), &step_bytes), greedy.clone())? else {
        bail!("no split fits on {}", fork.name);
    };
    // the option search per part may find smaller code than the probe: try
    // fewer parts while they fit and cost less (a part may only fit through
    // the dearest schedules), cut by the probe bytes and by the bytes the
    // parts actually had
    for count in (1..greedy.len()).rev() {
        let fewer = both(
            balance(count, &step_bytes),
            balance(count, &measured(&parts)),
        )?;
        let Some(fewer) = fewer else { break };
        if gas(&fewer) >= gas(&parts) {
            break;
        }
        parts = fewer;
    }
    Ok(parts)
}
