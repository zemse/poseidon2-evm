// Private small-state entries consume their final outputs into empty memory.
// Public permutations and split boundaries keep their existing contracts.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Terminal {
    T2,
    T3,
}

const OPTIONS: BuildOptions = BuildOptions {
    prime_under_external: false,
    internal_reduce_outputs: true,
    external_template: true,
    internal_mul3: true,
    ..DEFAULT_OPTIONS
};

const T3_OPTIONS: BuildOptions = BuildOptions {
    prime_under_external: false,
    external_template: true,
    internal_template: true,
    external_seam: true,
    ..DEFAULT_OPTIONS
};

fn whole_stack(params: &Params, range: Range, boundary: &Boundary) -> bool {
    range
        == (Range {
            from: 0,
            to: step_count(params),
        })
        && boundary.bounds.is_none()
        && !boundary.calldata
        && boundary.live.is_none()
        && !boundary.prime_second
        && boundary.prime_below.is_none()
        && !boundary.store_inputs
}

fn eligible(params: &Params, opts: BuildOptions, range: Range, boundary: &Boundary) -> bool {
    (params.t, params.rounds_f, params.rounds_p) == (2, 8, 56)
        && opts == OPTIONS
        && whole_stack(params, range, boundary)
}

fn eligible3(params: &Params, opts: BuildOptions, range: Range, boundary: &Boundary) -> bool {
    (params.t, params.rounds_f, params.rounds_p) == (3, 8, 56)
        && opts == T3_OPTIONS
        && whole_stack(params, range, boundary)
}

// Memory counters alone do not cover MLOAD. Only a recorded straight-line
// stack prefix can establish the empty-memory precondition of this entry.
pub(super) fn stack_only(lines: &[String], fork: Fork) -> bool {
    let mut tokens = lines
        .iter()
        .flat_map(|line| line.split("//").next().unwrap_or("").split_whitespace());
    while let Some(token) = tokens.next() {
        if matches!(token, "[PRIME]" | "add" | "mul" | "addmod" | "mulmod")
            || token.strip_prefix("0x").is_some_and(|hex| {
                !hex.is_empty() && hex.len() <= 64 && hex.bytes().all(|c| c.is_ascii_hexdigit())
            })
        {
            continue;
        }
        if matches!(token, "dupn" | "swapn") {
            if fork.reach <= 16
                || !tokens.next().is_some_and(|n| {
                    n.parse::<usize>()
                        .is_ok_and(|n| (17..=fork.reach).contains(&n))
                })
            {
                return false;
            }
        } else if !token
            .strip_prefix("dup")
            .or_else(|| token.strip_prefix("swap"))
            .is_some_and(|n| n.parse::<usize>().is_ok_and(|n| (1..=16).contains(&n)))
        {
            return false;
        }
    }
    !lines.is_empty()
}

pub(crate) fn build(
    params: &Params,
    inputs: &[Vec<U256>],
    fork: Fork,
    prior: &Best,
) -> Result<Option<BuildResult>> {
    let boundary = Boundary::default();
    let result = &prior.result;
    let kind = if eligible(params, prior.opts, result.range, &boundary) {
        Terminal::T2
    } else if eligible3(params, prior.opts, result.range, &boundary) {
        Terminal::T3
    } else {
        return Ok(None);
    };
    if result.state_in_memory
        || result.memory != 0
        || result.stores != 0
        || result.loads != 0
        || result.input_slots != vec![None; params.t]
        || !result.tables.is_empty()
        || !stack_only(&result.lines, fork)
    {
        return Ok(None);
    }
    let mut b = Builder::new(
        params,
        inputs,
        prior.opts,
        fork,
        result.range,
        HashSet::new(),
        false,
        true,
        &boundary,
    )?;
    b.terminal = Some(kind);
    let outputs = b.build()?;
    let expected = expected_outputs(params, inputs, result.range);
    finish_checked(b, &outputs, &expected, &boundary).map(Some)
}

impl Builder<'_> {
    pub(super) fn terminal_round2(&mut self, round: usize) -> Result<()> {
        if !eligible(self.params, self.opts, self.range, &Boundary::default())
            || round + 2 != self.range.to
            || self.live.is_some()
            || self.state_in_memory
            || self.stored
            || self.lane_constants.is_some()
            || self.input_slots != [None; 2]
            || self.e.memory != 0
            || self.e.prime_slot.is_some()
            || self.e.stores != 0
            || self.e.loads != 0
            || !self.e.tables.is_empty()
        {
            bail!("t2 terminal entry needs a whole stack-only permutation");
        }
        self.e.end_line();
        if !stack_only(&self.e.lines, self.e.fork) {
            bail!("t2 terminal entry needs an untouched-memory prefix");
        }
        let inputs = self.state.clone();
        let x = self.template_lane(&inputs, 0, round, true)?;
        self.e.end_line();
        for _ in 0..3 {
            self.e.push_prime()?;
        }
        self.e.swap(4)?;
        let y = self.template_lane(&inputs, 1, round, true)?;
        self.e.end_line();
        let e = &mut self.e;
        if !e.from_top().starts_with(&[y, e.p, x, e.p])
            || e.bound(x) >= PRIME
            || e.bound(y) >= PRIME
            || !stack_only(&e.lines, e.fork)
        {
            bail!("t2 terminal entry needs clean [y, PRIME, x, PRIME]");
        }
        let tail = e.from_top()[4..].to_vec();
        e.dup(y)?;
        e.dup(x)?;
        let sum = e.compute(Op::Add, &[inplace(x), inplace(y)], "sum")?;
        e.dup(e.p)?;
        e.dup(sum)?;
        e.dup(x)?;
        let z0 = e.compute(Op::Addmod, &[inplace(x), inplace(sum), inplace(e.p)], "s0'")?;
        e.end_line();
        if e.mstore_next(0)? != z0 {
            bail!("t2 terminal entry did not store s0'");
        }
        e.end_line();
        let z1 = e.compute(Op::Addmod, &[inplace(sum), inplace(y), inplace(e.p)], "s1'")?;
        e.end_line();
        if e.mstore_next(32)? != z1 {
            bail!("t2 terminal entry did not store s1'");
        }
        e.end_line();
        let stack = e.from_top();
        if !stack.starts_with(&[x, e.p]) || stack[2..] != tail || e.memory != 64 {
            bail!("t2 terminal entry changed its retained stack or memory extent");
        }
        self.state = vec![z0, z1];
        self.state_in_memory = true;
        self.stored = true;
        Ok(())
    }
}

impl Builder<'_> {
    pub(super) fn terminal_round3(&mut self, round: usize) -> Result<()> {
        if !eligible3(self.params, self.opts, self.range, &Boundary::default())
            || self.terminal != Some(Terminal::T3)
            || round.checked_add(2) != Some(self.range.to)
            || self.live.is_some()
            || self.state_in_memory
            || self.stored
            || self.lane_constants.is_some()
            || self.input_slots != [None; 3]
            || self.e.memory != 0
            || self.e.prime_slot.is_some()
            || self.e.stores != 0
            || self.e.loads != 0
            || !self.e.tables.is_empty()
        {
            bail!("t3 terminal entry needs a whole stack-only permutation");
        }
        let inputs = self.state.clone();
        if inputs.len() != 3
            || !self
                .e
                .from_top()
                .starts_with(&[inputs[0], self.e.p, inputs[2], inputs[1]])
            || inputs.iter().enumerate().any(|(i, &id)| {
                self.e.bound(id) > p1() * u256(4)
                    || !self
                        .e
                        .fits_add(self.e.bound(id), self.params.round_constants[round][i])
            })
        {
            bail!("t3 terminal entry needs the final template layout and bounds");
        }
        self.e.end_line();
        if !stack_only(&self.e.lines, self.e.fork) {
            bail!("t3 terminal entry needs an untouched-memory prefix");
        }
        let x = self.template_lane(&inputs, 0, round, true)?;
        self.e.end_line();
        self.e.push_prime()?;
        self.e.push_prime()?;
        self.e.dup(inputs[1])?;
        let y = self.template_lane(&inputs, 1, round, true)?;
        self.e.end_line();
        self.e.swap(3)?;
        let z = self.template_lane(&inputs, 2, round, true)?;
        self.e.end_line();
        if !self.e.from_top().starts_with(&[z, x, y, inputs[1]])
            || !stack_only(&self.e.lines, self.e.fork)
        {
            bail!("t3 terminal entry needs clean [z, x, y, s1]");
        }
        self.state = terminal3(&mut self.e)?;
        self.state_in_memory = true;
        self.stored = true;
        Ok(())
    }
}

// [z, x, y, U] -> memory [s0', s1', s2'], stack [x, y, U].
fn terminal3(e: &mut Emitter) -> Result<Vec<Id>> {
    if e.memory != 0 || e.prime_slot.is_some() {
        bail!("t3 terminal entry needs untouched memory");
    }
    let z = e.top(0)?;
    let x = e.top(1)?;
    let y = e.top(2)?;
    if [x, y, z].iter().any(|&id| e.bound(id) >= PRIME) {
        bail!("t3 terminal entry needs clean S-box outputs");
    }
    let tail = e.from_top()[3..].to_vec();
    e.dup(z)?;
    e.dup(y)?;
    e.dup(x)?;
    let pair = e.compute(Op::Add, &[inplace(x), inplace(y)], "pair")?;
    let sum = e.compute(Op::Add, &[inplace(pair), inplace(z)], "sum")?;
    e.push(PRIME, None)?;
    e.dup(e.p)?;
    e.dup(sum)?;
    e.dup(x)?;
    let o0 = e.compute(Op::Addmod, &[inplace(x), inplace(sum), inplace(e.p)], "s0'")?;
    e.end_line();
    if e.mstore_next(0)? != o0 || e.top(0)? != e.p {
        bail!("t3 terminal entry did not store s0' and retain PRIME");
    }
    e.end_line();
    e.dup(e.p)?;
    e.dup(sum)?;
    e.dup(y)?;
    let o1 = e.compute(Op::Addmod, &[inplace(y), inplace(sum), inplace(e.p)], "s1'")?;
    e.end_line();
    if e.mstore_next(32)? != o1 || e.top(0)? != e.p {
        bail!("t3 terminal entry did not store s1' and retain PRIME");
    }
    e.end_line();
    e.swap(2)?;
    let o2 = e.compute(Op::Addmod, &[inplace(z), inplace(sum), inplace(e.p)], "s2'")?;
    e.end_line();
    if e.mstore_next(64)? != o2 {
        bail!("t3 terminal entry did not store s2'");
    }
    e.end_line();
    let stack = e.from_top();
    if !stack.starts_with(&[x, y]) || stack[2..] != tail || e.memory != 96 {
        bail!("t3 terminal entry changed its retained stack or memory extent");
    }
    Ok(vec![o0, o1, o2])
}

#[cfg(test)]
#[path = "t3_entry_tests.rs"]
mod t3_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::huff::fork::fork;
    use crate::round_constants::generate_params;

    #[test]
    fn t2_terminal_range_boundary_and_prefix_guards() {
        let params = generate_params(2);
        let range = Range {
            from: 0,
            to: step_count(&params),
        };
        assert!(eligible(&params, OPTIONS, range, &Boundary::default()));
        for range in [
            Range { from: 1, ..range },
            Range {
                to: range.to - 1,
                ..range
            },
        ] {
            assert!(!eligible(&params, OPTIONS, range, &Boundary::default()));
        }
        for boundary in [
            Boundary {
                bounds: Some(vec![p1(); 2]),
                ..Boundary::default()
            },
            Boundary {
                calldata: true,
                ..Boundary::default()
            },
            Boundary {
                live: Some(vec![0]),
                ..Boundary::default()
            },
            Boundary {
                prime_second: true,
                ..Boundary::default()
            },
            Boundary {
                prime_below: Some(0),
                ..Boundary::default()
            },
            Boundary {
                store_inputs: true,
                ..Boundary::default()
            },
        ] {
            assert!(!eligible(&params, OPTIONS, range, &boundary));
        }
        assert!(!eligible(
            &generate_params(3),
            OPTIONS,
            range,
            &Boundary::default()
        ));
        assert!(!eligible(
            &params,
            DEFAULT_OPTIONS,
            range,
            &Boundary::default()
        ));
        for name in ["amsterdam", "osaka", "paris"] {
            let fork = fork(name).unwrap();
            assert!(stack_only(&["dup1 [PRIME] 0x01 add mulmod".into()], fork));
            for op in [
                "mload",
                "mstore",
                "msize",
                "codecopy",
                "calldatacopy",
                "jump",
                "UNKNOWN()",
                "dup17",
                "dupn",
                "dupn 0",
                "dupn 236",
            ] {
                assert!(!stack_only(&[op.into()], fork), "{name}: {op}");
            }
            assert_eq!(stack_only(&["dupn 124".into()], fork), name == "amsterdam");
        }
    }

    #[test]
    fn t2_terminal_production_selection_guards() {
        use crate::huff::render::{render_entry, render_entry_plan};
        use crate::huff::{entry_wrapper, select_terminal};
        let params = generate_params(2);
        let inputs = crate::vectors::test_inputs(2);
        for name in ["amsterdam", "osaka", "paris"] {
            let fork = fork(name).unwrap();
            let prior = crate::huff::build_entry(&params, &inputs, fork)
                .unwrap()
                .unwrap();
            let candidate = build(&params, &inputs, fork, &prior).unwrap().unwrap();
            let bytes = candidate.bytes + entry_wrapper(2, fork, &candidate);
            // Metadata mutations test selection, not executable bytecode.
            for delta in [0, 1] {
                let mut limited = fork;
                limited.code_size = bytes - delta;
                let chosen =
                    select_terminal(2, limited, prior.clone(), Ok(Some(candidate.clone())));
                assert_eq!(chosen.terminal_result().is_some(), delta == 0);
            }
            let mut deep = candidate.clone();
            deep.max_depth = 1000;
            assert!(
                select_terminal(2, fork, prior.clone(), Ok(Some(deep)))
                    .terminal_result()
                    .is_some()
            );
            for change in 0..6 {
                let mut bad = candidate.clone();
                match change {
                    0 => bad.bytes = usize::MAX,
                    1 => bad.max_depth = 1001,
                    2 => bad.max_dup = fork.reach + 1,
                    3 => bad.gas += 3,
                    4 => bad.gas += 4,
                    _ => bad.bytes = fork.code_size,
                }
                let chosen = select_terminal(2, fork, prior.clone(), Ok(Some(bad)));
                assert!(chosen.terminal_result().is_none());
                assert_eq!(chosen.entry_result().lines, prior.result.lines);
                assert_eq!(
                    render_entry_plan(&params, &fork, &chosen),
                    render_entry(&params, &fork, &prior.result)
                );
            }
            for missing in [Ok(None), Err(Error("failed terminal build".into()))] {
                let chosen = select_terminal(2, fork, prior.clone(), missing);
                assert!(chosen.terminal_result().is_none());
                assert_eq!(chosen.entry_result().lines, prior.result.lines);
            }
        }
    }

    #[test]
    fn t2_terminal_production_split_stays_on_the_existing_boundary() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let mut fork = fork("osaka").unwrap();
        fork.code_size = 1500;
        let width = crate::huff::generate(2, &fork).unwrap();
        assert!(
            matches!(&width.target, crate::huff::Target::Parts { paths, .. } if paths.len() > 1)
        );
        for (_, source) in width.files().filter(|(path, _)| path.ends_with(".huff")) {
            assert!(!source.contains("Private terminal body"));
        }
        let reports = crate::huff::verify::verify(&root, &fork, &[width]).unwrap();
        assert_eq!(reports[0].gas.diff(), 0);
        assert_eq!(reports[0].warm.unwrap().diff(), 0);
    }

    #[test]
    fn t2_terminal_production_builder_matches_checked_fixture() {
        let params = generate_params(2);
        let inputs = crate::vectors::test_inputs(2);
        for name in ["amsterdam", "osaka", "paris"] {
            let fork = fork(name).unwrap();
            let prior = crate::huff::build_entry(&params, &inputs, fork)
                .unwrap()
                .unwrap();
            let candidate = build(&params, &inputs, fork, &prior).unwrap().unwrap();
            let (fixture, _) =
                super::super::t2_terminal_tests::build_fixture(&params, &inputs, fork, true, 0)
                    .unwrap();
            let tokens = |lines: &[String]| {
                lines
                    .iter()
                    .flat_map(|l| l.split("//").next().unwrap().split_whitespace())
                    .map(str::to_string)
                    .collect::<Vec<_>>()
            };
            assert_eq!(tokens(&candidate.lines), tokens(&fixture.lines));
            assert_eq!(
                (
                    candidate.gas,
                    candidate.bytes,
                    candidate.memory,
                    candidate.max_depth,
                    candidate.max_dup
                ),
                (
                    fixture.gas,
                    fixture.bytes,
                    64,
                    fixture.max_depth,
                    fixture.max_dup
                )
            );
            assert_eq!(candidate.step_bytes, fixture.step_bytes);
            assert!(candidate.state_in_memory);
            for change in 0..7 {
                let mut bad = prior.clone();
                match change {
                    0 => bad.result.memory = 32,
                    1 => bad.result.state_in_memory = true,
                    2 => bad.result.input_slots[0] = Some(RAW_INPUT),
                    3 => bad.result.range.from = 1,
                    4 => bad.opts.shadow = true,
                    5 => bad.result.lines.push("mload".into()),
                    _ => bad.result.input_slots[0] = Some(COMPACT_INPUT),
                }
                assert!(build(&params, &inputs, fork, &bad).unwrap().is_none());
            }
        }
    }
}
