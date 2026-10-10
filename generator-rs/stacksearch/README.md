# stacksearch

The offline search behind the stack programs of `generator/huff/templates.ts` and `generator-rs/src/huff/templates.rs`: an A\* over the EVM stack programs that compute one Poseidon2 external round (or the M4 of a block of the `externalD` layer) from a given stack layout to a given layout, with the S-box of a lane as one move. Values are linear forms over the S-box outputs with a bound in units of P, so an `ADD` is allowed only while the bound stays below 2^256 and the result otherwise takes an `ADDMOD`; only the forms the linear layer needs are allowed (`build` in `src/bin/macro.rs`).

Two binaries, run from this directory after `cargo build --release`:

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

- `target/release/t3int` (`src/bin/t3int.rs`) searches the t = 3 internal round after its S-box over single opcodes, from `[x, s2, s1]` to `[s0', P, s2', s1']`: values are linear forms over x, s1, s2 with a bound in units of P (ADD while the bound stays at most 5), so diag 1, 1, 2 needs no products. Its bound counts the final op of every missing output (an ADDMOD with its PRIME copy for an output reduced below P), the PRIME copies, one DUP per output a leaf must still reach beyond its entries, and a POP per dead value beyond the garbage limit.

  ```
  t3int <s1 bound> <s2 bound> <s1' bound> <s2' bound> [max_garbage=2] [max_len=10] [s0' bound=4] [ub]
  ```

Layouts are comma separated class names, top first. `s<i>` is lane i of the state before its S-box, `x<i>` the S-box output, `P` a PRIME copy, `o<i>` (t = 2, 3) or `t4..t7` (t = 4: s3', s1', s0', s2') an output. In the goal `_` is a wildcard and `O` any output not yet placed. `final` reduces the outputs (the last round), `lazy` (t = 4) takes the inputs below 2P as the blocks of t >= 8 see them, `strict` counts leftover PRIME copies as garbage too. `max_garbage` is the number of dead values the program may leave on the stack.

Examples:

```
# one t = 2 external round from the layout the previous round leaves
target/release/macro 2 s1,P,s0 O,P,O 16 1 8 x 1
# the M4 of a block of t >= 8 (the `block` program of BLOCKS)
target/release/macro 4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 x 2 lazy
```

The output is the cost in gas, the layout the program leaves and one move per line with the stack after it; `todsl.py` turns it into the template DSL (`python3 todsl.py result.txt`) and `drive.py <t>` chases the layouts of a width: the entry, rounds until a layout repeats, the exit, the re-entry after the internal rounds and the final round, appending the DSL of every result to `t<t>.dsl.txt` (`CHAIN=<n>` sets the chain depth, default 1). `run23.sh`, `run_entry.sh`, `run_block.sh` and `run_block2.sh` are the runs that produced the programs of t = 2, t = 3 and the blocks.

A template is the `init` layout (the state elements by index and PRIME copies as the program expects them on top) and the DSL string; the schedule replays the first program of a kind whose layout matches. The t = 3 re-entry layout `s0,P,s1,s2` finishes at 189. Both t = 3 final-cycle layouts now finish at 216. Earlier searches did not finish the full t = 4 external round (over 19 GB in hours) or the t = 3 final round (2 h limit).

## Bounds and scope

The heuristic counts mandatory arithmetic, consumed constants and retained goal constants. Binary arithmetic consumes a value slot, whereas S-boxes and multiplication by four preserve it: if B binary operations remain, G output slots are required and V live value/input slots are present, at least max(0, B + G - V) DUPs remain. This is combined with the per-class copy bound by taking their maximum, not their sum. An input counts as one slot however many copies are on the stack: its only consumer is its S-box. On top, each S-box left but the one whose input is already on top costs at least 2: only a DUP or SWAP of that input or a POP right above it brings the input to the top (an op leaves its result there), and none of these is counted elsewhere.

For t = 3, a degree-four output needs a degree-three form or two distinct degree-two forms. The second intermediate group is satisfied by either route. Charging a degree-three form unconditionally overestimates a completion using two degree-two forms.

The bound requires complete computation history and every output. The CLI therefore accepts only raw inputs, S-box outputs and constants initially, and requires every output exactly once in the goal (fixed or `O`). `lazy` is supported only for t = 4. Goals normally constrain a prefix; `--clean-goal` also forbids trailing values and constants, without restricting temporary PRIME copies during expansion. Use it for production M4 blocks. Equal-f nodes are ordered by larger g, then LIFO. Optimality is within the macro graph, useful-form whitelist, garbage, depth and reach limits, not over arbitrary EVM programs. A positive `chain` enables one continuation; deeper recursion returned results the outer macro could not consume and is skipped.

## Composed rounds

`compose.py <t> <init> <goal> <round|final> <output-directory> [seconds-per-order]` fixes all S-boxes before the linear layer, trying each order with the initial top lane first. Each linear search has a 2 GiB RSS guard and a default 180 s limit. Its cache key includes the binary, arguments and time limit; cached and composed programs are independently replayed. The t = 4 linear search uses conservative lazy bounds. These restrictions give up global optimality, and `peak_depth` can exceed the default full-round search's depth. This was the restricted search for the first full t = 4 round candidates.

`interleave.py <k> <round|final> <extra-garbage> <output-directory> [seconds] [ub] [orders...]` fixes only the first k S-boxes of a t = 4 round from `s0,P,s1,s2,s3` (placed as `compose.py` places them) and searches the others together with the linear layer under `bench.py`, with lazy bounds and a garbage limit of the prefix's dead inputs plus `extra-garbage`. With `ub` it asks only for programs cheaper than ub in total. The full program is replayed and written to `full.txt` and `best.json`. The integrated t = 4 round fixes two S-boxes (k = 1 and the unrestricted search find nothing cheaper), the final round three (k = 2 and k = 1 find nothing cheaper).

## Profiling

`bench.py <output-directory> <seconds> <binary> <arguments...>` runs one search under `/usr/bin/time -l`, samples process-group RSS, and stops at the time limit or 48 GiB RSS (`RSS_GIB` overrides this up to 56). It writes a live `snapshot.json`, stdout, stderr and a result record, including the search environment. Successful programs are independently replayed on 64 deterministic BN254 inputs, including boundaries, with checks for ADD overflow, operands, output order, reduction and gas. `check.py <result-file> <arguments...>` runs the macro replay separately. The `internal` binary uses `internal_check.py` instead, also runnable with the same result-file/arguments convention (`UNORDERED=1` matches the search). Its numeric replay is not a symbolic proof over all inputs.

`python3 internal_layouts.py` evaluates the six inactive-lane renamings of the current t = 4 internal template with shortest SWAP-only adapters, including both boundaries of two and 56 rounds. `python3 -m unittest discover -s . -p internal_test.py` tests the numeric replay, adapters and runner. [OSAKA-OPTIMISATION.md](OSAKA-OPTIMISATION.md) records the lane's bounded searches and exact scope.

Build the profiling features separately:

```
cargo build --profile profiling --features dhat-heap
cargo build --profile profiling --features profile --target-dir target/hotpath
cargo build --profile profiling --features profile-alloc --target-dir target/hotpath-alloc
```

Dhat writes `dhat-heap.json` in the run directory. Sum the allocation sites' `gb` fields for the live bytes at the global heap peak, not their individual `mb` maxima. `HOTPATH_REPORT=functions-timing` selects timings; `HOTPATH_REPORT=functions-alloc` selects exclusive allocation bytes, or counts with `HOTPATH_ALLOC_METRIC=count`. Nested timing totals are inclusive and must not be summed. Start hotpath with the small t = 2 case: its event storage can dominate memory on a full search. The M4 timing profile hit the RSS guard even though the uninstrumented search used about 102 MB.

Use `footprint <pid>` and `vmmap --summary <pid>` during a native run. The node arena contains distinct open and closed states; the queue count also contains stale entries and must not be added to it. Peak-heap/final-state ratios include capacity slack and transient table growth, not just the 24-byte node payload. `target/release/intrinsics` measures single-threaded hash/copy latency, streaming reads and dependent random reads at 128 and 768 MiB (15 warm samples).

[RESULTS.md](RESULTS.md) records the measured comparisons, limits and verified call gas. The integrated programs and earlier candidates are archived in `results/`; `results/programs.json` gives each program's replay arguments, cost and search scope.
