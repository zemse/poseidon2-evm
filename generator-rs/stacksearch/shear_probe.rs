// Full-chain checks of the fixed-DAG schedules in results/astra-shear.program.
// Test-only candidate, not a production coordinate representation.
use super::*;
use crate::field::{self, PRIME, u256};
use crate::huff::fork::fork;

const ENTRY: &str = "P dup4 dup6 addmod=u swap4 pop";
const EXIT: &str = "P dup4 4P sub dup6 addmod=b swap4 pop";
const SBOX: &str = "add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod";

struct Phase {
    mask: u32,
    u: u64,
    v: u64,
    gas: u64,
    dsl: &'static str,
}

fn phases() -> Vec<Phase> {
    include_str!("results/astra-shear.program")
        .lines()
        .map(|line| {
            let fields: Vec<_> = line.splitn(5, '\t').collect();
            assert_eq!(fields.len(), 5);
            Phase {
                mask: fields[0].parse().unwrap(),
                u: fields[1].parse().unwrap(),
                v: fields[2].parse().unwrap(),
                gas: fields[3].parse().unwrap(),
                dsl: fields[4],
            }
        })
        .collect()
}

fn policy(round: usize) -> usize {
    assert!(round < 56);
    match round {
        53 | 54 => 6,
        55 => 5,
        _ => round % 6,
    }
}

fn render(dsl: &str) -> String {
    dsl.split_whitespace()
        .map(|token| match token {
            "P" => format!("{PRIME:#x}"),
            "4P" => format!("{:#x}", PRIME * u256(4)),
            _ => token.split('=').next().unwrap().to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Word {
    value: U256,
    low: U256,
    high: U256,
}

impl Word {
    fn literal(value: U256) -> Self {
        Self {
            value,
            low: value,
            high: value,
        }
    }

    fn variable(value: U256, high: U256) -> Self {
        assert!(value <= high);
        Self {
            value,
            low: U256::ZERO,
            high,
        }
    }
}

fn replay(stack: &mut Vec<Word>, dsl: &str) -> std::result::Result<u64, String> {
    let mut gas = 0;
    for token in render(dsl).split_whitespace() {
        if let Some(hex) = token.strip_prefix("0x") {
            let v = U256::from_str_radix(hex, 16).map_err(|e| e.to_string())?;
            if v == U256::ZERO {
                return Err("zero literal outside this PUSH gas model".into());
            }
            stack.insert(0, Word::literal(v));
            gas += 3;
        } else if let Some(n) = token.strip_prefix("dup") {
            let n: usize = n.parse().map_err(|_| "DUP index")?;
            if !(1..=16).contains(&n) || n > stack.len() {
                return Err("DUP reach".into());
            }
            stack.insert(0, stack[n - 1]);
            gas += 3;
        } else if let Some(n) = token.strip_prefix("swap") {
            let n: usize = n.parse().map_err(|_| "SWAP index")?;
            if !(1..=16).contains(&n) || n >= stack.len() {
                return Err("SWAP reach".into());
            }
            stack.swap(0, n);
            gas += 3;
        } else if token == "pop" {
            if stack.is_empty() {
                return Err("POP underflow".into());
            }
            stack.remove(0);
            gas += 2;
        } else {
            let modular = matches!(token, "addmod" | "mulmod");
            let take = if modular { 3 } else { 2 };
            if stack.len() < take {
                return Err("arithmetic underflow".into());
            }
            let (a, b) = (stack[0], stack[1]);
            let out = match token {
                "add" => Word {
                    value: a.value.checked_add(b.value).ok_or("ADD overflow")?,
                    low: a.low.checked_add(b.low).ok_or("ADD lower bound")?,
                    high: a.high.checked_add(b.high).ok_or("ADD upper bound")?,
                },
                "sub" => Word {
                    value: a.value.checked_sub(b.value).ok_or("SUB underflow")?,
                    low: a.low.checked_sub(b.high).ok_or("SUB lower bound")?,
                    high: a.high.checked_sub(b.low).ok_or("SUB upper bound")?,
                },
                "addmod" | "mulmod" => {
                    if stack[2] != Word::literal(PRIME) {
                        return Err("wrong modulus".into());
                    }
                    Word::variable(
                        if token == "addmod" {
                            a.value.add_mod(b.value, PRIME)
                        } else {
                            a.value.mul_mod(b.value, PRIME)
                        },
                        PRIME - u256(1),
                    )
                }
                _ => return Err(format!("unknown opcode {token}")),
            };
            assert!(out.low <= out.value && out.value <= out.high);
            stack.drain(..take);
            stack.insert(0, out);
            gas += if modular { 8 } else { 3 };
        }
        if stack.len() > 1024 {
            return Err("stack limit".into());
        }
    }
    Ok(gas)
}

#[test]
fn shear_chain_bounds_costs_and_reference() {
    let phases = phases();
    let l = PRIME - u256(1);
    assert!(l.checked_mul(u256(5)).is_some());
    assert!(l.checked_mul(u256(6)).is_none());
    let mut random = Prng::new(0x0073_6865_6172);
    for trial in 0..64 {
        let mut state: Vec<_> = (0..3)
            .map(|_| match trial {
                0 => U256::ZERO,
                1 => l * u256(4),
                2 => l * u256(2),
                _ => random.next_u256() % (l * u256(4) + u256(1)),
            })
            .collect();
        let tail = Word::literal(u256(17));
        let mut stack = vec![
            Word::variable(state[0], l * u256(4)),
            Word::literal(PRIME),
            Word::variable(state[2], l * u256(4)),
            Word::variable(state[1], l * u256(4)),
            tail,
        ];
        let entry = replay(&mut stack, ENTRY).unwrap();
        assert_eq!(entry, 22);
        assert_eq!(stack[3].value, field::add(state[1], state[2]));
        let (mut rounds, mut reductions, mut funded) = (0, 0, 0);
        for round in 0..56 {
            let phase = &phases[policy(round)];
            assert_eq!(
                [stack[3].high, stack[2].high],
                [l * u256(phase.u), l * u256(phase.v)]
            );
            let c = match trial {
                0 => u256(1),
                1 => l,
                _ => field::reduce(random.next_u256()).max(u256(1)),
            };
            let sbox = replay(&mut stack, &format!("{c:#x} {SBOX}")).unwrap();
            assert_eq!(sbox, 45);
            let post = replay(&mut stack, phase.dsl).unwrap();
            assert_eq!(post, phase.gas);
            rounds += sbox + post;
            reductions += phase.mask.count_ones();
            funded += 39 + 8 * phase.mask.count_ones();
            let x = field::pow(field::add(state[0], c), u256(5));
            let sum = field::add(field::add(x, state[1]), state[2]);
            state = vec![
                field::add(sum, x),
                field::add(sum, state[1]),
                field::add(sum, field::add(state[2], state[2])),
            ];
            assert_eq!(field::reduce(stack[0].value), state[0]);
            assert_eq!(
                field::reduce(stack[3].value),
                field::add(state[1], state[2])
            );
            assert_eq!(field::reduce(stack[2].value), state[2]);
            assert_eq!(stack[1], Word::literal(PRIME));
            assert!(stack[0].high <= l * u256(4));
            assert_eq!(stack.len(), 6 + round);
            assert_eq!(stack.last(), Some(&tail));
        }
        let exit = replay(&mut stack, EXIT).unwrap();
        assert_eq!(exit, 28);
        assert_eq!(
            [rounds, u64::from(reductions), u64::from(funded)],
            [6032, 103, 3008]
        );
        assert_eq!(funded - 3 * 56, 2840);
        assert_eq!(u64::from(funded) + 45 * 56, 5528);
        assert_eq!(entry + rounds + exit, 6082);
        for (i, word) in [stack[0], stack[3], stack[2]].into_iter().enumerate() {
            assert_eq!(field::reduce(word.value), state[i]);
            assert!(word.high <= l * u256(4));
        }
        assert_eq!(stack.len(), 61);
        assert_eq!(stack.last(), Some(&tail));
    }
}

#[test]
fn shear_replay_rejects_unsafe_arithmetic_and_boundaries() {
    let l = PRIME - u256(1);
    let start = vec![
        Word::variable(l * u256(4), l * u256(4)),
        Word::literal(PRIME),
        Word::variable(l * u256(4), l * u256(4)),
        Word::variable(l * u256(4), l * u256(4)),
    ];
    assert!(replay(&mut start.clone(), &ENTRY.replace("addmod", "add")).is_err());
    assert!(replay(&mut start.clone(), &ENTRY.replace("P ", "4P ")).is_err());
    assert!(replay(&mut start.clone(), &EXIT.replace("4P sub", "4P swap1 sub")).is_err());
    assert!(replay(&mut start.clone(), "swap16").is_err());
    assert!(replay(&mut start.clone(), "dup17").is_err());
    assert!(replay(&mut start.clone(), "swap1 0x1 add dup2 mulmod").is_err());
}

#[test]
fn shear_compiled_whole_call_regression() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let params = generate_params(3);
    assert_eq!(params.rounds_p, 56);
    let phases = phases();
    let mut body = render(ENTRY);
    for round in 0..56 {
        body.push_str(&format!(
            "\n{:#x} {SBOX} {}",
            params.round_constants[4 + round][0],
            render(phases[policy(round)].dsl)
        ));
    }
    body.push_str(&format!("\n{}\n", render(EXIT)));
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let width = super::super::generate(3, &fork).unwrap();
        let Target::Entry { path: entry, .. } = &width.target else {
            panic!("expected whole t3 target");
        };
        let files: HashMap<String, String> = width
            .files()
            .map(|(path, text)| (path.to_string(), text.to_string()))
            .collect();
        let path = files
            .keys()
            .find(|path| path.ends_with("/Permutation.huff"))
            .unwrap()
            .clone();
        let original = &files[&path];
        let (prefix, rest) = original.split_once("// Round 4 (internal)").unwrap();
        let (_, suffix) = rest.split_once("// Round 60 (external)").unwrap();
        let candidate = format!("{prefix}{body}// Round 60 (external){suffix}");
        let mut measured = Vec::new();
        for text in [original, &candidate] {
            let mut files = files.clone();
            files.insert(path.clone(), text.clone());
            let sources = Arc::new(Sources {
                root: root.clone(),
                files,
            });
            let compiled = compile(&sources, entry, &fork).unwrap();
            let mut chain = Chain::new(&fork);
            let to = chain.deploy(compiled.initcode).unwrap();
            let calls = check_permutation(&mut chain, to, &[], 3, "shear").unwrap();
            measured.push(same_gas(&calls, "shear").unwrap());
            assert_eq!(calls.len(), 24);
        }
        assert_eq!(measured[1], measured[0] - 6000 + 6082);
        println!(
            "{name} t3: baseline {}, shear {}, 48 reference-checked calls, 6082 chain gas",
            measured[0], measured[1]
        );
    }
}
