// Stack programs for the external rounds of t <= 4 and for the M4 of a
// block of the external_d layer (huff/templates.ts), searched with A* and
// replayed by the schedule with the external_template option. Full t = 4
// rounds fix the first S-boxes (two for a round, three for the last) and
// search the others together with the linear layer; they are not globally
// optimal. A program is a list of moves, space separated:
// dupN, swapN, P (a PRIME copy on top), 4 (PUSH1 4), pop, add=NAME,
// addmod=NAME, mulmod=NAME (the op on the top of the stack, its result named
// NAME; addmod and mulmod take the PRIME copy at slot 3), sboxI (lane I: s_I
// + c on top of a PRIME copy, both consumed by the S-box), sboxIn (lane I
// without the PRIME copy under it) and dI (the internal diag constant I).
// `init` is the layout the program expects on top: the elements of the state
// by index and PRIME copies; the programs of a kind are tried in order, the
// first whose layout matches is replayed.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateKind {
    /// the initial linear layer, from the inputs in state order over a
    /// PRIME copy
    Entry,
    /// an external round from the layout it leaves
    Round,
    /// the last external round before the internal rounds, leaving [s0',
    /// PRIME, ...]
    Exit,
    /// the last round: clean outputs in state order over a PRIME copy
    Final,
}

/// The M4 of a block of t >= 8 with external_d, from its four lazy inputs
/// on top in order: Block leaves the outputs in order, Exit with a PRIME
/// copy under the first (the last external round before the internal
/// rounds), Final reduced (the last round); none leaves anything else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Block,
    Exit,
    Final,
}

pub struct Template {
    pub init: &'static str,
    pub ops: &'static str,
}

const ROUND4: &[Template] = &[
    Template {
        init: "s0,P,s1,s2,s3",
        ops: "sbox0 P dup3 sbox1 dup1 dup1 add=2s1 swap2 add=t0 P P dup7 sbox3 P P dup5 dup4 dup1 add=2s3 addmod=t3 swap7 sbox2 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
    },
    Template {
        init: "s0,s1,s2,s3",
        ops: "P swap1 sbox0 P dup3 sbox1 dup1 dup1 add=2s1 swap2 add=t0 P P dup7 sbox3 P P dup5 dup4 dup1 add=2s3 addmod=t3 swap7 sbox2 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
    },
];

pub fn templates(t: usize, kind: TemplateKind) -> &'static [Template] {
    match (t, kind) {
        (2, TemplateKind::Entry) => &[Template {
            init: "s0,s1,P",
            ops: "dup2 dup2 add=sum P swap2 dup2 add=s0' swap3 add=s1'",
        }],
        (2, TemplateKind::Round) => &[
            Template {
                init: "s1,P,s0",
                ops: "sbox1 P dup3 sbox0 dup2 dup2 add=sum P swap2 dup2 add=s0' swap3 add=s1'",
            },
            Template {
                init: "s0,P,s1",
                ops: "sbox0 P dup3 sbox1 dup1 dup3 add=sum P swap2 dup2 add=s1' swap3 add=s0'",
            },
            Template {
                init: "s0,s1",
                ops: "P P swap2 sbox0 swap2 sbox1 dup1 dup3 add=sum P swap2 dup2 add=s1' swap3 add=s0'",
            },
        ],
        (2, TemplateKind::Exit) => &[Template {
            init: "s1,P,s0",
            ops: "sbox1 P P dup4 sbox0 dup3 dup2 add=sum swap3 dup4 add=s1' swap3 add=s0'",
        }],
        (2, TemplateKind::Final) => &[Template {
            init: "s0,P,s1",
            ops: "sbox0 P P P swap4 sbox1 P dup2 dup5 add=sum swap2 dup3 addmod=s1' swap3 addmod=s0'",
        }],
        (3, TemplateKind::Entry) => &[Template {
            init: "s0,s1,s2,P",
            ops: "dup3 dup3 dup3 add=s0+s1 add=sum swap1 dup2 add=s0' swap4 swap2 dup2 add=s1' swap3 add=s2'",
        }],
        (3, TemplateKind::Round) => &[
            Template {
                init: "s2,P,s1,s0",
                ops: "sbox2 P P P dup6 sbox0 swap4 sbox1 dup4 dup4 dup3 add=s1+s2 add=sum swap3 dup4 add=s2' swap4 dup4 add=s0' swap3 add=s1'",
            },
            Template {
                init: "s1,P,s0,s2",
                ops: "sbox1 P P P dup6 sbox2 swap4 sbox0 dup1 dup5 dup5 add=s1+s2 add=sum swap4 dup5 add=s2' swap3 dup5 add=s1' swap4 add=s0'",
            },
            Template {
                init: "s0,P,s2,s1",
                ops: "sbox0 P P P dup6 sbox1 swap4 sbox2 dup3 dup2 dup6 add=s1+s2 add=sum swap4 dup5 add=s1' swap3 dup5 add=s0' swap4 add=s2'",
            },
            // the internal boundary re-enters the cycle at s1,P,s0,s2
            Template {
                init: "s0,P,s1,s2",
                ops: "sbox0 P dup3 sbox1 P P dup6 sbox2 dup3 dup5 add=s0+s1 dup2 add=sum swap1 dup2 add=s2' swap4 dup2 add=s0' swap3 add=s1'",
            },
        ],
        (3, TemplateKind::Exit) => &[Template {
            init: "s2,P,s1,s0",
            ops: "sbox2 P P dup4 sbox1 swap4 sbox0 P dup2 dup4 dup7 add=s1+s2 add=sum dup1 dup7 add=s1' swap4 dup2 add=s2' swap3 add=s0'",
        }],
        (3, TemplateKind::Final) => &[
            Template {
                init: "s0,P,s2,s1",
                ops: "sbox0 P P dup5 sbox1 swap3 sbox2 dup1 dup4 dup4 add=s0+s1 add=sum P P P swap4 dup4 addmod=s2' swap4 dup3 addmod=s0' swap4 addmod=s1' P swap3",
            },
            Template {
                init: "s2,P,s1,s0",
                ops: "sbox2 P dup3 sbox1 P dup5 sbox0 dup3 dup3 dup3 add=s0+s1 add=sum P P P swap4 dup4 addmod=s0' swap5 dup3 addmod=s2' swap3 addmod=s1' P swap3",
            },
        ],
        // the initial linear layer leaves the layout the rounds take
        (4, TemplateKind::Entry) => &[Template {
            init: "s0,s1,s2,s3,P",
            ops: "dup2 add=t0 P P dup3 dup7 dup1 add=2s3 addmod=t3 swap5 dup5 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 dup1 add=2s1 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
        }],
        (4, TemplateKind::Round | TemplateKind::Exit) => ROUND4,
        (4, TemplateKind::Final) => &[Template {
            init: "s0,P,s1,s2,s3",
            ops: "sbox0 P dup3 sbox1 P dup6 sbox3 swap2 dup2 add=t0 P P P P dup5 dup8 dup1 add=2s3 addmod=t3 swap8 sbox2 P swap6 add=t1 P dup9 P dup4 4 mulmod=4t1 addmod=s3' swap5 dup1 add=2s1 addmod=t2 P P dup6 dup4 addmod=s2' swap4 4 mulmod=4t0 addmod=s1' P dup2 dup8 addmod=s0'",
        }],
        _ => &[],
    }
}

/// The forms of round 0 of the t = 4 hash entry for n inputs. It runs from
/// the PRIME copy SETUP pushed, which it leaves under everything for the
/// rounds after to copy, and loads the inputs itself: rI is calldata word I
/// as it is (PUSH 4 + 32 I, CALLDATALOAD), which only ADDMOD, MULMOD and
/// mod=NAME (MOD by the PRIME copy under it) take. It leaves p_i = sum_j
/// M4[i][j] in_j, named p0..p3, as [p0, P, p1, p2, p3], the cheapest
/// schedule of its DAG stacksearch's hashdag finds; ROUND4 then adds the
/// folded constants K_i in its S-boxes.
pub fn hash_forms(n: usize) -> Option<&'static str> {
    match n {
        1 => Some("P r0 mod=p2 dup1 P 4 dup3 mulmod=p1 P dup3 dup3 add=p0"),
        2 => Some(
            "P r0 r1 addmod=p3 P 4 dup3 mulmod=4p3 P r1 dup1 addmod=w dup3 dup2 add=p2 swap2 add=p1 P dup4 dup3 add=p0",
        ),
        3 => Some(
            "P r1 mod=b P r0 dup3 addmod=t0 P r2 dup4 P 4 dup4 mulmod=4c dup5 add=p3 swap5 add=2b addmod=w P dup2 P 4 dup6 mulmod=4t0 add=p1 swap2 dup5 add=p2 swap3 dup3 add=p0",
        ),
        _ => None,
    }
}

pub fn round4() -> &'static [Template] {
    std::slice::from_ref(&ROUND4[0])
}

/// The t = 4 internal round with the internal_template option: the program
/// stacksearch's `internal` finds for three lanes, extended to four (166 gas
/// against 169). The sum lands on a PRIME copy, its copies and the operands
/// of three lanes are pre-placed in the order the lanes come, s3 is taken by
/// a copy and every other output is swapped into the slot of the next lane,
/// which comes up onto its operands. It leaves s3 dead under the outputs and
/// a PRIME copy under s0'.
pub fn internal4() -> &'static [Template] {
    &[Template {
        init: "s0,P,s1,s2,s3",
        ops: "sbox0 P P dup5 dup4 dup6 add=x+s1 dup8 add=x+s1+s3 addmod=sum dup2 d0 dup3 dup3 dup2 dup2 dup1 d3 dup14 mulmod=m3 dup3 add=s3' swap11 d2 mulmod=m2 add=s2' swap8 d1 mulmod=m1 add=s1' swap5 mulmod=m0 add=s0'",
    }]
}

/// The t = 3 internal round with the internal_template option (stacksearch's
/// t3int): s1' and s2' are reduced on pre-placed PRIME copies and s1' is
/// swapped into the slot of s2, which comes up for 2 s2. The first program
/// takes reduced s1 and s2 and keeps the sum lazy (64 gas after the S-box),
/// the second lazy ones as the external round leaves them and reduces the
/// sum (72). Both leave s1 dead under the outputs and a PRIME copy under s0'.
pub fn internal3() -> &'static [Template] {
    &[
        Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P dup4 dup4 dup4 add=x+s2 add=sum P P dup3 dup8 addmod=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
        },
        Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P P dup5 dup5 dup5 add=x+s2 addmod=sum P P dup3 dup8 addmod=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
        },
    ]
}

#[derive(Debug, Clone, Copy)]
pub enum Internal3Kind {
    Low,
    High,
    Reset,
    Final,
}

/// The t = 3 periodic reduction policy: sum is reduced, s1' is reset above
/// 3(P-1), and 2 s2 is reduced above 2(P-1). The final program reduces s2'
/// before external re-entry. All leave s1 dead under [s0',P,s2',s1'].
pub fn internal3_periodic(kind: Internal3Kind) -> &'static [Template] {
    match kind {
        Internal3Kind::Low => &[Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum dup1 dup6 add=s1' swap4 dup1 add=2s2 dup2 add=s2' swap3 add=s0'",
        }],
        Internal3Kind::High => &[Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P dup2 dup7 add=s1' swap5 dup1 addmod=2s2 dup2 add=s2' swap3 add=s0'",
        }],
        Internal3Kind::Reset => &[Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P P dup3 dup8 addmod=s1' swap5 dup1 addmod=2s2 dup2 add=s2' swap3 add=s0'",
        }],
        Internal3Kind::Final => &[Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P dup2 dup7 add=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
        }],
    }
}

/// The linear-only final M4 of t = 4 leaves a PRIME copy under its outputs.
pub fn linear_final4() -> &'static [Template] {
    &[Template {
        init: "s0,s1,s2,s3",
        ops: "dup2 add=t0 P P swap4 P dup4 dup8 dup1 add=2s3 addmod=t3 swap6 add=t1 P dup7 P dup4 4 mulmod=4t1 addmod=s3' swap4 dup1 add=2s1 addmod=t2 P P dup5 dup4 addmod=s2' swap3 4 mulmod=4t0 P swap2 addmod=s1' P P swap1 swap6 dup3 addmod=s0'",
    }]
}

/// One block of an Osaka streamed layer (stacksearch `sblock`), from the
/// column sums and a PRIME copy on top, [S0, S1, S2, S3, P]: `u<i>` is u_i
/// = x_i + S_i on top, `q=<n>` PUSH1 4 MULMOD over a PRIME copy, `lane=z<i>`
/// s_i' + c_i and its S-box over the PRIME copy under s_i', stored unless
/// the block is kept; o<i> is s_i'. The first program whose DUPs reach the
/// layout runs, else the block template.
pub fn stream_blocks(kept: bool, on_stack: bool) -> &'static [&'static str] {
    match (kept, on_stack) {
        (false, _) => &[
            "u1 u3 u2 dup2 add=t1 P dup2 dup5 dup1 add=d1 addmod=t2 P u0 P swap6 add=t0 P dup2 q=q0 dup4 add=o1 swap5 dup1 add=d3 addmod=t3 P dup5 dup3 add=o0 lane=z0 P P swap4 q=q1 add=o3 P dup2 lane=z3 add=o2 lane=z2 lane=z1",
            "u3 u1 u0 dup2 add=t0 P dup2 dup5 dup1 add=d3 addmod=t3 P u2 P swap6 add=t1 P dup2 q=q1 dup4 add=o3 swap5 dup1 add=d1 addmod=t2 P dup2 dup6 add=o2 lane=z2 P P swap4 q=q0 add=o1 P dup2 lane=z1 add=o0 lane=z0 lane=z3",
        ],
        (true, false) => &[
            "u1 u0 dup2 add=t0 u2 P P u3 P dup2 dup1 add=d3 dup7 addmod=t3 swap4 add=t1 dup6 P dup3 q=q1 dup6 add=o3 swap7 add=d1 addmod=t2 P P P dup8 lane=z3 swap7 dup4 add=o2 lane=z2 swap5 q=q0 add=o1 P dup2 lane=z1 swap3 add=o0 lane=z0",
        ],
        (true, true) => &[
            "u0 u3 u2 dup2 add=t1 P P u1 P dup2 dup1 add=d1 dup6 addmod=t2 swap6 add=t0 dup5 P dup3 q=q0 dup8 add=o1 swap6 add=d3 addmod=t3 P P P dup7 lane=z1 swap5 q=q1 dup3 add=o3 P dup2 lane=z3 swap7 add=o2 lane=z2 swap4 add=o0 lane=z0",
        ],
    }
}

pub fn blocks(kind: BlockKind) -> &'static [Template] {
    match kind {
        BlockKind::Block => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P P dup3 4 mulmod=4t0 swap4 dup6 add=t1 swap5 dup1 add=2s3 P swap3 addmod=t3 swap2 dup1 add=2s1 dup3 P dup7 4 mulmod=4t1 add=s3' swap5 addmod=t2 dup4 dup2 add=s2' swap3 add=s1' swap1 dup2 add=s0'",
        }],
        BlockKind::Exit => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P P P dup4 4 mulmod=4t0 swap5 dup7 add=t1 swap6 dup1 add=2s3 P swap4 addmod=t3 swap3 dup1 add=2s1 dup4 P dup8 4 mulmod=4t1 add=s3' swap6 addmod=t2 dup5 dup2 add=s2' swap4 add=s1' swap2 dup3 add=s0'",
        }],
        BlockKind::Final => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 swap2 P dup4 dup6 dup1 add=2s3 addmod=t3 swap2 dup1 add=2s1 swap4 add=t1 P P P swap3 P dup6 P dup4 4 mulmod=4t1 addmod=s3' swap7 addmod=t2 P P dup8 dup4 addmod=s2' swap6 4 mulmod=4t0 addmod=s1' swap2 dup3 addmod=s0'",
        }],
    }
}
