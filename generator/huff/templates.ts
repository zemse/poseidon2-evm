// Stack programs for the external rounds of t <= 4 and for the M4 of a
// block of the externalD layer (t >= 8), searched with A* and replayed by
// the schedule (Builder.runTemplate) with the externalTemplate option.
// A lane's S-box is one search move. The full t = 4 rounds fix an S-box
// prefix and search the linear layer separately, so they are not globally
// optimal. Rounds may leave dead values below the outputs; blocks leave
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
    ops: "sbox0 P dup3 sbox1 P dup6 sbox3 P dup6 sbox2 dup2 add=t1 P P dup3 4 mulmod=4t1 swap4 P P swap4 dup3 dup1 add=2s1 addmod=t2 swap6 add=t0 dup6 P dup3 4 mulmod=4t0 add=s1' swap4 dup1 add=2s3 addmod=t3 dup3 dup2 add=s0' swap4 add=s3' swap4 dup5 add=s2' swap3",
  },
  {
    init: layout("s0,s1,s2,s3"),
    ops: "P swap1 sbox0 P dup3 sbox1 P dup6 sbox3 P dup6 sbox2 dup2 add=t1 P P dup3 4 mulmod=4t1 swap4 P P swap4 dup3 dup1 add=2s1 addmod=t2 swap6 add=t0 dup6 P dup3 4 mulmod=4t0 add=s1' swap4 dup1 add=2s3 addmod=t3 dup3 dup2 add=s0' swap4 add=s3' swap4 dup5 add=s2' swap3",
  },
];

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
    entry: [],
    round: ROUND4,
    exit: ROUND4,
    final: [
      {
        init: layout("s0,P,s1,s2,s3"),
        ops: "sbox0 P dup3 sbox1 P dup5 sbox2 P dup7 sbox3 P P P swap6 dup6 add=t0 swap4 P dup6 dup6 dup1 add=2s3 addmod=t3 swap4 add=t1 P dup5 P dup4 4 mulmod=4t1 addmod=s3' swap6 dup1 add=2s1 addmod=t2 P P dup7 dup4 addmod=s2' swap5 4 mulmod=4t0 addmod=s1' swap1 P swap1 dup3 addmod=s0'",
      },
    ],
  },
};

// The linear-only final M4 of t = 4 leaves a PRIME copy under its outputs.
export const LINEAR_FINAL4: Template[] = [
  {
    init: layout("s0,s1,s2,s3"),
    ops: "dup2 add=t0 P P swap4 P dup4 dup8 dup1 add=2s3 addmod=t3 swap6 add=t1 P dup7 P dup4 4 mulmod=4t1 addmod=s3' swap4 dup1 add=2s1 addmod=t2 P P dup5 dup4 addmod=s2' swap3 4 mulmod=4t0 P swap2 addmod=s1' P P swap1 swap6 dup3 addmod=s0'",
  },
];

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
