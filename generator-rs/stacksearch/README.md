# stacksearch

The offline search behind the stack programs of `generator-rs/src/huff/templates.rs`: an A\* over the EVM stack programs that compute one Poseidon2 external round (or the M4 of a block of the `externalD` layer) from a given stack layout to a given layout, with the S-box of a lane as one move. Values are linear forms over the S-box outputs with a bound in units of P, so an `ADD` is allowed only while the bound stays below 2^256 and the result otherwise takes an `ADDMOD`; only the forms the linear layer needs are allowed (`build` in `src/bin/macro.rs`).

The binaries, run from this directory after `cargo build --release`:

- `target/release/macro` (`src/bin/macro.rs`) searches over macro moves: the next arithmetic op together with which of its operands are consumed in place (brought to the top by a swap sequence from a precomputed table, at most 3 swaps) and which are DUPed, a chain pre-placing the operands of the op that consumes the result, the S-box of a lane as one move, standalone `PUSH P` / `POP` / `SWAP1..4` for the goal layout. This is the one that found the programs in the repository.

  ```
  macro <t> <init> <goal> [reach=16] [max_garbage=2] [extra_depth=8] [final|x] [chain=2] [lazy,strict]
  ```

  `UB=<cost>` drops every node whose f reaches cost, so the search returns only a program cheaper than cost, or `no solution` once everything below it is exhausted.

- `target/release/stacksearch` (`src/main.rs`) is the earlier single-opcode search with the same value model; slower, kept for reference.

- `target/release/internal` (`src/bin/internal.rs`) searches the t = 4 internal round over single opcodes (the S-box of lane 0 one move), with the products `d_i * s_i` and the outputs `m_i + sum` as classes. Its conservative bound charges missing output ADDs and product MULMODs, with the greater of net stack supply and mandatory diagonal/PRIME supply; only the raw t = 4 five-slot boundary with bounds 2 also uses the 154-gas fixed-arithmetic relaxation. Copy, garbage and placement charges were removed after allowed-state completion counterexamples. The strict DUP filter remains a generation restriction, not a proved-complete rule. `O` accepts any unplaced output; `UNORDERED=1` accepts any permutation of the goal's outputs and PRIME copies. Goals require every output exactly once, with its lane-specific bound. `UB=<gas>` prunes f >= gas before inserting a node. `REPLAY="<program>"` scores a program in the template DSL instead and emits the same cost/layout/DSL records for independent replay.

  ```
  internal <lanes> <init> <goal> [max_garbage=0] [max_depth=16] [s=<bounds>;o=<bounds>]
  ```

- `target/release/t3int` (`src/bin/t3int.rs`) searches the t = 3 internal round after its S-box over single opcodes, from `[x, s2, s1]` to `[s0', P, s2', s1']`: values are linear forms over x, s1, s2 with a bound in units of P (ADD while the bound stays at most 5), so diag 1, 1, 2 needs no products. Its bound counts the final op of every missing output (an ADDMOD with its PRIME copy for an output reduced below P), mandatory PRIME supply and the largest leaf-copy deficit. It omits cleanup charges. `EXCHANGE=1` enables EIP-8024 exchanges within the working window; `REPLAY="<program>"` checks a printed DSL program, its goal and every suffix's bound. Bounds must be in 1..5 and the window in 4..16. The whitelist, live-only DUP filter and window remain restrictions, not an unrestricted optimality proof.

  ```
  t3int <s1 bound> <s2 bound> <s1' bound> <s2' bound> [max_garbage=2] [max_len=10] [s0' bound=4] [ub]
  ```

- `target/release/t3dag` (`src/bin/t3dag.rs`) schedules the fixed t3 low-phase DAG after its S-box: q = x + b, sum = ADDMOD(q,c), a' = sum + x, b' = sum + b, d = c + c, c' = sum + d. Input bounds are (1,3,2) times P-1, output bounds (2,4,5), with goal `[a',P,c',b']` and at most one trailing garbage slot. Each node runs once. Live-value copies and PRIME supply are limited only by the window. The heuristic funds remaining operations and copies (47 gas initially). `EXCHANGE=1` and `REPLAY="..."` work as in t3int; the fixed DAG, once-only nodes and window restrict the result.

  ```
  t3dag [window=8] [upper_bound=56]
  ```

- `target/release/sheardag` (`src/bin/sheardag.rs`) uses the same fixed-DAG engine for the inactive shear u = b + c, v = c: q = x + u, s = q + v, a' = q + x, v' = s + v, h = s + q, u' = h + u. Bit i of the mask selects ADDMOD at node i. Inclusive bounds in units of P-1 must fit uint256 and leave room for the next active constant. The boundary is `[x,v,u]` to `[a',P,v',u']`, with at most one trailing garbage slot. `EXCHANGE` and `REPLAY` work as above. These are post-S-box model costs, not full-call gas. Portable programs and the compiled whole-chain rejection are in `results/astra-shear.program`, `shear_probe.rs` and ASTRA-OPTIMISATION.md.

  ```
  sheardag <mask> <u_bound> <v_bound> [window=12] [upper_bound=funded+10]
  ```

- `target/release/t3variants` (`src/bin/t3variants.rs`) varies the low-phase original-basis DAG: the first sum pair is x+b, x+c or b+c, and the c' path is `(c+c)+sum` or `(sum+c)+c`. All have the t3dag input/output bounds and funded root. `LAYOUT=cb-cb` (default), `cb-bc`, `bc-cb` or `bc-bc` sets the inactive input/output order under the active lane and PRIME. `EXCHANGE` and `REPLAY` use the shared engine. ASTRA-OPTIMISATION.md records the scoped sub-56 exhaustion for these graphs and boundaries at window 11.

  ```
  t3variants <xb|xc|bc> <cc|sc> [window=11] [upper_bound=56]
  ```

- `target/release/cycle` (`src/bin/cycle.rs`) bounds the steady internal rounds of t = 3 and t = 4 with no layout fixed between rounds: the least mean cost per round over every cycle of rounds, the next round allowed to start before this one ends. It counts only the copies, SWAPs and POPs of the values of the linear layer; PRIME copies and constants are left out, so a SWAP that moved one becomes a move of a value to or from the top, 3 gas. Every layout a round can end in starts at 0, and value iteration over k rounds brackets the cycle mean between the least and largest change of D_k. Layers 0 prints one round from `s0,s1,...` back to it instead. Environment variables relax the model: `SBOX` (the S-box as three MULMODs on values of its own, linear-layer moves allowed between them), `SPLIT` (the S-box input consumed and x made later, intermediates left out), `SHL` (t = 3: 2 s2 as PUSH1 1 SHL), `COMP` (t = 4: s_i' = mu_i s_i + the sum of the other lanes).

  ```
  cycle <t> [max_window=12] [layers=4]
  ```

- `target/release/hashdag` (`src/bin/hashdag.rs`) schedules the forms of the t = 4 hash entry's round 0 (`hash_forms` in templates.rs) over single opcodes: a fixed DAG of `add`, `addmod`, `mulmod` (by a node or 4) and `mod` nodes over the calldata words r0..r2 as CALLDATALOAD leaves them (6 gas a load, any number of times), from the PRIME copy SETUP pushes to p0 on top of a PRIME copy and p1..p3 anywhere. A* with the ops still to run, a DUP or load per use beyond the entries on the stack and a PRIME copy or 4 per op that needs one. `KEEP=1` leaves SETUP's PRIME copy where it is; `WEIGHT=w` orders by g + w h / 10 (not optimal).

  ```
  hashdag <n> '<name>=<op>(<a>,<b>);...' [max_depth=12] [ub]
  ```

- `target/release/ecycle` (`src/bin/ecycle.rs`) is `cycle` for the steady t = 4 external rounds: the least mean cost per round of the copies, SWAPs, moves and POPs of the round's values over every cycle of rounds, the linear layer as ROUND4 builds it or through t23, PRIME copies and constants left out (`PRIME=1` keeps the PRIME copies as tokens, each pushed for 3).

  ```
  ecycle [max_window=8] [layers=4]
  ```

- `target/release/sblock` (`src/bin/sblock.rs`) searches one block of an Osaka streamed external layer (`stream_blocks` in templates.rs): `u = x + S`, the M4 DAG of the `block` program and each output's round constant and S-box, stored or kept on the stack, from an empty working stack over a fixed floor (the column sums, a PRIME copy, the inputs where they sit) back to it, or to the kept S-box outputs. Single opcodes plus three fixed macros (`u<i>`, `q` = `PUSH1 4 MULMOD`, `lane` = constant, S-box and store); `P` DUPs the nearest PRIME copy. The heuristic counts the ops, macros, copies, PRIME copies and POPs left; `trace <program>` replays a program.

  ```
  sblock <floor> [stored|kept] [max_working=8] [ub | trace <program>]
  ```

- `target/release/seam` (`src/bin/seam.rs`) searches the seams of t = 2 and 3 over single opcodes: values are linear forms over the S-box outputs (coefficients 0..2, bound in units of P-1), with PRIME copies, DUP, SWAP, EXCHANGE (`EXCHANGE=1`), POP, ADD, ADDMOD, the S-box of a lane on a PRIME copy (45) and `msize mstore` of the next output. The goal is `store` (the terminal round of the private entries) or a layout prefix. `LOADS=0,1,...` takes lanes from calldata reduced (14) for the entries; `ROUNDS=2` (t = 2) searches two external rounds at once. It found the terminal rounds of t = 2 (143) and t = 3 (219); LANE3-SMALL.md records the runs.

  ```
  seam <t> <init> <goal> [window=10] [ub]
  ```

`cycle` and `ecycle` take `EXCHANGE=1` too: a transposition of two values below the top, or a move of one between two depths (an EXCHANGE with a PRIME copy or constant), 3 gas.

Layouts are comma separated class names, top first. `s<i>` is lane i of the state before its S-box, `x<i>` the S-box output, `P` a PRIME copy, `o<i>` (t = 2, 3) or `t4..t7` (t = 4: s3', s1', s0', s2') an output. In the goal `_` is a wildcard and `O` any output not yet placed. `final` reduces the outputs (the last round), `lazy` (t = 4) takes the inputs below 2P as the blocks of t >= 8 see them, `strict` counts leftover PRIME copies as garbage too. `max_garbage` is the number of dead values the program may leave on the stack.

Examples:

```
# one t = 2 external round from the layout the previous round leaves
target/release/macro 2 s1,P,s0 O,P,O 16 1 8 x 1
# the M4 of a block of t >= 8 (the `block` program of BLOCKS)
target/release/macro 4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 x 2 lazy
```

The output is the cost in gas, the layout the program leaves and one move per line with the stack after it, which the template DSL transcribes. `run23.sh`, `run_entry.sh`, `run_block.sh` and `run_block2.sh` are the runs that produced the programs of t = 2, t = 3 and the blocks.

A template is the `init` layout (the state elements by index and PRIME copies as the program expects them on top) and the DSL string; the schedule replays the first program of a kind whose layout matches. The t = 3 re-entry layout `s0,P,s1,s2` finishes at 189. Both t = 3 final-cycle layouts now finish at 216. Earlier searches did not finish the full t = 4 external round (over 19 GB in hours) or the t = 3 final round (2 h limit).

## Bounds and scope

The heuristic counts mandatory arithmetic, consumed constants and retained goal constants. Binary arithmetic consumes a value slot, whereas S-boxes and multiplication by four preserve it: if B binary operations remain, G output slots are required and V live value/input slots are present, at least max(0, B + G - V) DUPs remain. This is combined with the per-class copy bound by taking their maximum, not their sum. An input counts as one slot however many copies are on the stack: its only consumer is its S-box. On top, each S-box left but the one whose input is already on top costs at least 2: only a DUP or SWAP of that input or a POP right above it brings the input to the top (an op leaves its result there), and none of these is counted elsewhere.

For t = 3, a degree-four output needs a degree-three form or two distinct degree-two forms. The second intermediate group is satisfied by either route. Charging a degree-three form unconditionally overestimates a completion using two degree-two forms.

The bound requires complete computation history and every output. The CLI therefore accepts only raw inputs, S-box outputs and constants initially, and requires every output exactly once in the goal (fixed or `O`). `lazy` is supported only for t = 4. Goals normally constrain a prefix; `--clean-goal` also forbids trailing values and constants, without restricting temporary PRIME copies during expansion. Use it for production M4 blocks. Equal-f nodes are ordered by larger g, then LIFO. Optimality is within the macro graph, useful-form whitelist, garbage, depth and reach limits, not over arbitrary EVM programs. A positive `chain` enables one continuation; deeper recursion returned results the outer macro could not consume and is skipped.

## Composed rounds

The first full t = 4 round candidates came from a restricted search that fixed all S-boxes before the linear layer, trying each order with the initial top lane first, with conservative lazy bounds. These restrictions give up global optimality, and `peak_depth` can exceed the default full-round search's depth.

A second restricted search fixed only the first k S-boxes of a t = 4 round from `s0,P,s1,s2,s3` and searched the others together with the linear layer, with lazy bounds and a garbage limit of the prefix's dead inputs. The integrated t = 4 round fixes two S-boxes (k = 1 and the unrestricted search find nothing cheaper), the final round three (k = 2 and k = 1 find nothing cheaper). The Python drivers of both searches were removed; the programs they found are the generator's templates.

## Profiling

Run a search under `/usr/bin/time -l` with a time and RSS limit. The programs a search finds are checked where they land: the generator's compiled `verify` replays every template in revm against the reference permutation.

[OSAKA-OPTIMISATION.md](OSAKA-OPTIMISATION.md) records the lane's bounded searches and exact scope.

Build the profiling features separately:

```
cargo build --profile profiling --features dhat-heap
cargo build --profile profiling --features profile --target-dir target/hotpath
cargo build --profile profiling --features profile-alloc --target-dir target/hotpath-alloc
```

Dhat writes `dhat-heap.json` in the run directory. Sum the allocation sites' `gb` fields for the live bytes at the global heap peak, not their individual `mb` maxima. `HOTPATH_REPORT=functions-timing` selects timings; `HOTPATH_REPORT=functions-alloc` selects exclusive allocation bytes, or counts with `HOTPATH_ALLOC_METRIC=count`. Nested timing totals are inclusive and must not be summed. Start hotpath with the small t = 2 case: its event storage can dominate memory on a full search. The M4 timing profile hit the RSS guard even though the uninstrumented search used about 102 MB.

Use `footprint <pid>` and `vmmap --summary <pid>` during a native run. The node arena contains distinct open and closed states; the queue count also contains stale entries and must not be added to it. Peak-heap/final-state ratios include capacity slack and transient table growth, not just the 24-byte node payload. `target/release/intrinsics` measures single-threaded hash/copy latency, streaming reads and dependent random reads at 128 and 768 MiB (15 warm samples).

[RESULTS.md](RESULTS.md) records the measured comparisons, limits and verified call gas. The integrated programs and earlier candidates are archived in `results/`; `results/programs.json` gives each program's replay arguments, cost and search scope.
