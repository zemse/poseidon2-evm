// Stack programs for the external rounds of t <= 4 and for the M4 of a
// block of the external_d layer (huff/templates.ts), found by an
// exhaustive search and replayed by the schedule with the
// external_template option. A program is a list of moves, space separated:
// dupN, swapN, P (a PRIME copy on top), 4 (PUSH1 4), pop, add=NAME,
// addmod=NAME, mulmod=NAME (the op on the top of the stack, its result named
// NAME; addmod and mulmod take the PRIME copy at slot 3), sboxI (lane I: s_I
// + c on top of a PRIME copy, both consumed by the S-box) and sboxIn (lane I
// without the PRIME copy under it). `init` is the layout the program expects
// on top: the elements of the state by index and PRIME copies; the programs
// of a kind are tried in order, the first whose layout matches is replayed.

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
            // the re-entry after the internal rounds: two swaps into the
            // cycle of the three above, which the search did not finish for
            // the layout itself
            Template {
                init: "s0,P,s1,s2",
                ops: "swap2 swap3 swap2 sbox0 P P P dup6 sbox1 swap4 sbox2 dup3 dup2 dup6 add=s1+s2 add=sum swap4 dup5 add=s1' swap3 dup5 add=s0' swap4 add=s2'",
            },
        ],
        (3, TemplateKind::Exit) => &[Template {
            init: "s2,P,s1,s0",
            ops: "sbox2 P P dup4 sbox1 swap4 sbox0 P dup2 dup4 dup7 add=s1+s2 add=sum dup1 dup7 add=s1' swap4 dup2 add=s2' swap3 add=s0'",
        }],
        // written by hand (the search did not finish): the lanes as the exit
        // program takes them, then the three reduced outputs over a PRIME
        // copy
        (3, TemplateKind::Final) => &[Template {
            init: "s0,P,s2,s1",
            ops: "sbox0 P dup3 sbox2 P dup5 sbox1 dup3 dup2 add=s0+s1 dup3 add=sum P P dup3 dup6 addmod=s2' P dup4 dup6 addmod=s1' P dup5 dup9 addmod=s0'",
        }],
        // the last M4 of t = 4 on the S-box outputs, reduced, over a PRIME
        // copy (the blocks leave none, as t >= 8 stacks them)
        (4, TemplateKind::Final) => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P P swap4 P dup4 dup8 dup1 add=2s3 addmod=t3 swap6 add=t1 P dup7 P dup4 4 mulmod=4t1 addmod=s3' swap4 dup1 add=2s1 addmod=t2 P P dup5 dup4 addmod=s2' swap3 4 mulmod=4t0 P swap2 addmod=s1' P P swap1 swap6 dup3 addmod=s0'",
        }],
        _ => &[],
    }
}

pub fn blocks(kind: BlockKind) -> &'static [Template] {
    match kind {
        BlockKind::Block => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P dup2 4 mulmod=4t0 swap3 dup5 add=t1 swap4 dup1 add=2s3 P swap2 addmod=t3 swap1 dup1 add=2s1 dup2 P dup6 4 mulmod=4t1 add=s3' swap4 P swap2 addmod=t2 dup4 dup2 add=s2' swap3 add=s1' swap1 dup2 add=s0'",
        }],
        BlockKind::Exit => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P dup2 4 mulmod=4t0 swap3 P dup6 dup1 add=2s3 P swap4 addmod=t3 swap3 dup1 add=2s1 swap5 add=t1 dup3 P dup3 4 mulmod=4t1 add=s3' swap5 addmod=t2 dup4 dup2 add=s2' swap3 add=s1' P swap1 swap2 dup3 add=s0'",
        }],
        BlockKind::Final => &[Template {
            init: "s0,s1,s2,s3",
            ops: "dup2 add=t0 P dup2 4 mulmod=4t0 swap3 dup5 add=t1 swap4 dup1 add=2s3 P swap2 addmod=t3 swap1 dup1 add=2s1 P dup5 4 mulmod=4t1 P swap1 dup4 addmod=s3' swap4 P swap2 addmod=t2 P dup5 dup3 addmod=s2' swap3 P swap2 addmod=s1' P swap1 swap2 dup3 addmod=s0'",
        }],
    }
}
