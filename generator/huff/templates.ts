// Stack programs for the external rounds of t <= 4 and for the M4 of a
// block of the externalD layer (t >= 8), searched with A* and replayed by
// the schedule (Builder.runTemplate) with the externalTemplate option.
// A lane's S-box is one search move. The full t = 4 rounds fix the first
// S-boxes (two for a round, three for the last) and search the others
// together with the linear layer, so they are not globally optimal. Rounds may leave dead values below the outputs; blocks leave
// nothing else.
//
// A program is a list of moves, space separated:
//   dupN, swapN    DUP / SWAP of slot N (1-based from the top)
//   P              a PRIME copy on top (DUPed from the nearest, else pushed)
//   4              PUSH1 4
//   pop
//   add=NAME, addmod=NAME, mulmod=NAME
//                  the op on the top of the stack, its result named NAME
//                  (addmod and mulmod take the PRIME copy at slot 3)
//   sboxI          lane I: s_I + c on top of a PRIME copy, both consumed by
//                  the S-box, x_I on top
//   sboxIn         lane I without the PRIME copy under it
//   dI             the internal diag constant I
// `init` is the layout the program expects on top: the elements of the
// state by index and PRIME copies. The programs of a kind are tried in
// order, the first whose layout matches is replayed.
//
// The kinds: `entry` is the initial linear layer (the inputs in state order
// over a PRIME copy), `round` an external round from the layout it leaves,
// `exit` the last external round before the internal rounds (leaves [s0',
// PRIME, ...] as they expect) and `final` the last round (clean outputs in
// state order over a PRIME copy).

export type TemplateKind = "entry" | "round" | "exit" | "final";

// The M4 of a block of t >= 8 with externalD, from its four lazy inputs on
// top in order: `block` leaves the outputs in order, `exit` with a PRIME
// copy under the first (the last external round before the internal
// rounds), `final` reduced (the last round); none leaves anything else.
export type BlockKind = "block" | "exit" | "final";

export type Template = { init: string[]; ops: string };

const layout = (s: string) => s.split(",");

const ROUND4: Template[] = [
  {
    init: layout("s0,P,s1,s2,s3"),
    ops: "sbox0 P dup3 sbox1 dup1 dup1 add=2s1 swap2 add=t0 P P dup7 sbox3 P P dup5 dup4 dup1 add=2s3 addmod=t3 swap7 sbox2 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
  },
  {
    init: layout("s0,s1,s2,s3"),
    ops: "P swap1 sbox0 P dup3 sbox1 dup1 dup1 add=2s1 swap2 add=t0 P P dup7 sbox3 P P dup5 dup4 dup1 add=2s3 addmod=t3 swap7 sbox2 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
  },
];

// The forms of round 0 of the t = 4 hash entry for n inputs. It runs from
// the PRIME copy SETUP pushed, which it leaves under everything for the
// rounds after to copy, and loads the inputs itself: rI is calldata word I
// as it is (PUSH 4 + 32 I, CALLDATALOAD), which only ADDMOD, MULMOD and
// mod=NAME (MOD by the PRIME copy under it) take. It leaves p_i = sum_j
// M4[i][j] in_j, named p0..p3, as [p0, P, p1, p2, p3], the cheapest
// schedule of its DAG stacksearch's hashdag finds; ROUND4 then adds the
// folded constants K_i in its S-boxes.
export const HASH_FORMS: Record<number, string> = {
  1: "P r0 mod=p2 dup1 P 4 dup3 mulmod=p1 P dup3 dup3 add=p0",
  2: "P r0 r1 addmod=p3 P 4 dup3 mulmod=4p3 P r1 dup1 addmod=w dup3 dup2 add=p2 swap2 add=p1 P dup4 dup3 add=p0",
  3: "P r1 mod=b P r0 dup3 addmod=t0 P r2 dup4 P 4 dup4 mulmod=4c dup5 add=p3 swap5 add=2b addmod=w P dup2 P 4 dup6 mulmod=4t0 add=p1 swap2 dup5 add=p2 swap3 dup3 add=p0",
};

export const ROUND4_FIRST: Template[] = [ROUND4[0]];

export const TEMPLATES: Record<number, Record<TemplateKind, Template[]>> = {
  2: {
    entry: [
      {
        init: layout("s0,s1,P"),
        ops: "dup2 dup2 add=sum P swap2 dup2 add=s0' swap3 add=s1'",
      },
    ],
    round: [
      {
        init: layout("s1,P,s0"),
        ops: "sbox1 P dup3 sbox0 dup2 dup2 add=sum P swap2 dup2 add=s0' swap3 add=s1'",
      },
      {
        init: layout("s0,P,s1"),
        ops: "sbox0 P dup3 sbox1 dup1 dup3 add=sum P swap2 dup2 add=s1' swap3 add=s0'",
      },
      {
        init: layout("s0,s1"),
        ops: "P P swap2 sbox0 swap2 sbox1 dup1 dup3 add=sum P swap2 dup2 add=s1' swap3 add=s0'",
      },
    ],
    exit: [
      {
        init: layout("s1,P,s0"),
        ops: "sbox1 P P dup4 sbox0 dup3 dup2 add=sum swap3 dup4 add=s1' swap3 add=s0'",
      },
    ],
    final: [
      {
        init: layout("s0,P,s1"),
        ops: "sbox0 P P P swap4 sbox1 P dup2 dup5 add=sum swap2 dup3 addmod=s1' swap3 addmod=s0'",
      },
    ],
  },
  3: {
    entry: [
      {
        init: layout("s0,s1,s2,P"),
        ops: "dup3 dup3 dup3 add=s0+s1 add=sum swap1 dup2 add=s0' swap4 swap2 dup2 add=s1' swap3 add=s2'",
      },
    ],
    round: [
      {
        init: layout("s2,P,s1,s0"),
        ops: "sbox2 P P P dup6 sbox0 swap4 sbox1 dup4 dup4 dup3 add=s1+s2 add=sum swap3 dup4 add=s2' swap4 dup4 add=s0' swap3 add=s1'",
      },
      {
        init: layout("s1,P,s0,s2"),
        ops: "sbox1 P P P dup6 sbox2 swap4 sbox0 dup1 dup5 dup5 add=s1+s2 add=sum swap4 dup5 add=s2' swap3 dup5 add=s1' swap4 add=s0'",
      },
      {
        init: layout("s0,P,s2,s1"),
        ops: "sbox0 P P P dup6 sbox1 swap4 sbox2 dup3 dup2 dup6 add=s1+s2 add=sum swap4 dup5 add=s1' swap3 dup5 add=s0' swap4 add=s2'",
      },
      // the internal boundary re-enters the cycle at s1,P,s0,s2
      {
        init: layout("s0,P,s1,s2"),
        ops: "sbox0 P dup3 sbox1 P P dup6 sbox2 dup3 dup5 add=s0+s1 dup2 add=sum swap1 dup2 add=s2' swap4 dup2 add=s0' swap3 add=s1'",
      },
    ],
    exit: [
      {
        init: layout("s2,P,s1,s0"),
        ops: "sbox2 P P dup4 sbox1 swap4 sbox0 P dup2 dup4 dup7 add=s1+s2 add=sum dup1 dup7 add=s1' swap4 dup2 add=s2' swap3 add=s0'",
      },
    ],
    final: [
      {
        init: layout("s0,P,s2,s1"),
        ops: "sbox0 P P dup5 sbox1 swap3 sbox2 dup1 dup4 dup4 add=s0+s1 add=sum P P P swap4 dup4 addmod=s2' swap4 dup3 addmod=s0' swap4 addmod=s1' P swap3",
      },
      {
        init: layout("s2,P,s1,s0"),
        ops: "sbox2 P dup3 sbox1 P dup5 sbox0 dup3 dup3 dup3 add=s0+s1 add=sum P P P swap4 dup4 addmod=s0' swap5 dup3 addmod=s2' swap3 addmod=s1' P swap3",
      },
    ],
  },
  4: {
    // the initial linear layer leaves the layout the rounds take
    entry: [
      {
        init: layout("s0,s1,s2,s3,P"),
        ops: "dup2 add=t0 P P dup3 dup7 dup1 add=2s3 addmod=t3 swap5 dup5 add=t1 dup6 P dup3 4 mulmod=4t1 add=s3' swap4 dup1 add=2s1 addmod=t2 P dup4 dup3 add=s2' swap3 4 mulmod=4t0 add=s1' P dup2 dup7 add=s0'",
      },
    ],
    round: ROUND4,
    exit: ROUND4,
    final: [
      {
        init: layout("s0,P,s1,s2,s3"),
        ops: "sbox0 P dup3 sbox1 P dup6 sbox3 swap2 dup2 add=t0 P P P P dup5 dup8 dup1 add=2s3 addmod=t3 swap8 sbox2 P swap6 add=t1 P dup9 P dup4 4 mulmod=4t1 addmod=s3' swap5 dup1 add=2s1 addmod=t2 P P dup6 dup4 addmod=s2' swap4 4 mulmod=4t0 addmod=s1' P dup2 dup8 addmod=s0'",
      },
    ],
  },
};

// The t = 4 internal round with the internalTemplate option: the program
// stacksearch's `internal` finds for three lanes, extended to four (166 gas
// against 169). The sum lands on a PRIME copy, its copies and the operands
// of three lanes are pre-placed in the order the lanes come, s3 is taken by
// a copy and every other output is swapped into the slot of the next lane,
// which comes up onto its operands. It leaves s3 dead under the outputs and
// a PRIME copy under s0'.
export const INTERNAL4: Template[] = [
  {
    init: layout("s0,P,s1,s2,s3"),
    ops: "sbox0 P P dup5 dup4 dup6 add=x+s1 dup8 add=x+s1+s3 addmod=sum dup2 d0 dup3 dup3 dup2 dup2 dup1 d3 dup14 mulmod=m3 dup3 add=s3' swap11 d2 mulmod=m2 add=s2' swap8 d1 mulmod=m1 add=s1' swap5 mulmod=m0 add=s0'",
  },
];

// The t = 3 internal round with the internalTemplate option (stacksearch's
// t3int): s1' and s2' are reduced on pre-placed PRIME copies and s1' is
// swapped into the slot of s2, which comes up for 2 s2. The first program
// takes reduced s1 and s2 and keeps the sum lazy (64 gas after the S-box),
// the second lazy ones as the external round leaves them and reduces the
// sum (72). Both leave s1 dead under the outputs and a PRIME copy under s0'.
export const INTERNAL3: Template[] = [
  {
    init: layout("s0,P,s2,s1"),
    ops: "sbox0 P dup4 dup4 dup4 add=x+s2 add=sum P P dup3 dup8 addmod=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
  },
  {
    init: layout("s0,P,s2,s1"),
    ops: "sbox0 P P dup5 dup5 dup5 add=x+s2 addmod=sum P P dup3 dup8 addmod=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
  },
];

// The t = 3 periodic reduction policy: sum is reduced, s1' is reset above
// 3(P-1), and 2 s2 is reduced above 2(P-1). The final program reduces s2'
// before external re-entry. All leave s1 dead under [s0',P,s2',s1'].
export const INTERNAL3_PERIODIC: Record<
  "low" | "high" | "reset" | "final",
  Template[]
> = {
  low: [
    {
      init: layout("s0,P,s2,s1"),
      ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum dup1 dup6 add=s1' swap4 dup1 add=2s2 dup2 add=s2' swap3 add=s0'",
    },
  ],
  high: [
    {
      init: layout("s0,P,s2,s1"),
      ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P dup2 dup7 add=s1' swap5 dup1 addmod=2s2 dup2 add=s2' swap3 add=s0'",
    },
  ],
  reset: [
    {
      init: layout("s0,P,s2,s1"),
      ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P P dup3 dup8 addmod=s1' swap5 dup1 addmod=2s2 dup2 add=s2' swap3 add=s0'",
    },
  ],
  final: [
    {
      init: layout("s0,P,s2,s1"),
      ops: "sbox0 P P dup4 dup6 dup5 add=x+s1 addmod=sum P dup2 dup7 add=s1' swap5 dup1 dup4 add=sum+s2 addmod=s2' swap3 add=s0'",
    },
  ],
};

// The linear-only final M4 of t = 4 leaves a PRIME copy under its outputs.
export const LINEAR_FINAL4: Template[] = [
  {
    init: layout("s0,s1,s2,s3"),
    ops: "dup2 add=t0 P P swap4 P dup4 dup8 dup1 add=2s3 addmod=t3 swap6 add=t1 P dup7 P dup4 4 mulmod=4t1 addmod=s3' swap4 dup1 add=2s1 addmod=t2 P P dup5 dup4 addmod=s2' swap3 4 mulmod=4t0 P swap2 addmod=s1' P P swap1 swap6 dup3 addmod=s0'",
  },
];

// One block of an Osaka streamed layer (stacksearch `sblock`), from the
// column sums and a PRIME copy on top, [S0, S1, S2, S3, P]: `u<i>` is u_i =
// x_i + S_i on top, `q=<n>` PUSH1 4 MULMOD over a PRIME copy, `lane=z<i>`
// s_i' + c_i and its S-box over the PRIME copy under s_i', stored unless the
// block is kept; o<i> is s_i'. The first program whose DUPs reach the layout
// runs, else the block template.
export function streamBlocks(kept: boolean, onStack: boolean): string[] {
  if (!kept) {
    return [
      "u1 u3 u2 dup2 add=t1 P dup2 dup5 dup1 add=d1 addmod=t2 P u0 P swap6 add=t0 P dup2 q=q0 dup4 add=o1 swap5 dup1 add=d3 addmod=t3 P dup5 dup3 add=o0 lane=z0 P P swap4 q=q1 add=o3 P dup2 lane=z3 add=o2 lane=z2 lane=z1",
      "u3 u1 u0 dup2 add=t0 P dup2 dup5 dup1 add=d3 addmod=t3 P u2 P swap6 add=t1 P dup2 q=q1 dup4 add=o3 swap5 dup1 add=d1 addmod=t2 P dup2 dup6 add=o2 lane=z2 P P swap4 q=q0 add=o1 P dup2 lane=z1 add=o0 lane=z0 lane=z3",
    ];
  }
  if (!onStack) {
    return [
      "u1 u0 dup2 add=t0 u2 P P u3 P dup2 dup1 add=d3 dup7 addmod=t3 swap4 add=t1 dup6 P dup3 q=q1 dup6 add=o3 swap7 add=d1 addmod=t2 P P P dup8 lane=z3 swap7 dup4 add=o2 lane=z2 swap5 q=q0 add=o1 P dup2 lane=z1 swap3 add=o0 lane=z0",
    ];
  }
  return [
    "u0 u3 u2 dup2 add=t1 P P u1 P dup2 dup1 add=d1 dup6 addmod=t2 swap6 add=t0 dup5 P dup3 q=q0 dup8 add=o1 swap6 add=d3 addmod=t3 P P P dup7 lane=z1 swap5 q=q1 dup3 add=o3 P dup2 lane=z3 swap7 add=o2 lane=z2 swap4 add=o0 lane=z0",
  ];
}

// One block of an external layer with its outputs on top in order,
// [s0', s1', s2', s3'] ([s0', P, s1', s2', s3'] for exit), from the column
// sums (stacksearch `sblock` exit / exit0 / final): the moves of streamBlocks
// without lanes. The first program whose DUPs reach the layout runs, else the
// block template.
export const ORDERED_BLOCKS: Record<BlockKind, string[]> = {
  block: [
    "u1 u0 dup2 add=t0 u3 P P dup3 dup1 add=d3 dup5 addmod=t3 swap2 u2 add=t1 P dup2 q=q1 dup4 add=o3 swap5 dup1 add=d1 addmod=t2 P dup2 dup6 add=o2 swap4 q=q0 add=o1 dup1 swap2 add=o0",
  ],
  exit: [
    "u1 u0 dup2 add=t0 u3 P P P dup4 dup1 add=d3 dup6 addmod=t3 swap3 u2 add=t1 P dup2 q=q1 dup5 add=o3 swap6 dup1 add=d1 addmod=t2 P dup2 dup7 add=o2 swap5 q=q0 add=o1 dup1 swap3 add=o0",
  ],
  final: [
    "u1 u0 dup2 add=t0 u2 P P P u3 P dup2 dup1 add=d3 dup8 addmod=t3 swap5 add=t1 P P dup3 q=q1 dup7 addmod=o3 swap7 dup1 add=d1 addmod=t2 P P dup3 dup9 addmod=o2 swap6 q=q0 addmod=o1 dup1 swap3 addmod=o0",
  ],
};

export const BLOCKS: Record<BlockKind, Template[]> = {
  block: [
    {
      init: layout("s0,s1,s2,s3"),
      ops: "dup2 add=t0 P P dup3 4 mulmod=4t0 swap4 dup6 add=t1 swap5 dup1 add=2s3 P swap3 addmod=t3 swap2 dup1 add=2s1 dup3 P dup7 4 mulmod=4t1 add=s3' swap5 addmod=t2 dup4 dup2 add=s2' swap3 add=s1' swap1 dup2 add=s0'",
    },
  ],
  exit: [
    {
      init: layout("s0,s1,s2,s3"),
      ops: "dup2 add=t0 P P P dup4 4 mulmod=4t0 swap5 dup7 add=t1 swap6 dup1 add=2s3 P swap4 addmod=t3 swap3 dup1 add=2s1 dup4 P dup8 4 mulmod=4t1 add=s3' swap6 addmod=t2 dup5 dup2 add=s2' swap4 add=s1' swap2 dup3 add=s0'",
    },
  ],
  final: [
    {
      init: layout("s0,s1,s2,s3"),
      ops: "dup2 add=t0 swap2 P dup4 dup6 dup1 add=2s3 addmod=t3 swap2 dup1 add=2s1 swap4 add=t1 P P P swap3 P dup6 P dup4 4 mulmod=4t1 addmod=s3' swap7 addmod=t2 P P dup8 dup4 addmod=s2' swap6 4 mulmod=4t0 addmod=s1' swap2 dup3 addmod=s0'",
    },
  ],
};
