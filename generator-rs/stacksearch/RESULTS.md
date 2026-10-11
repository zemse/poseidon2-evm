# Stacksearch measurements

## Method

Apple Mac14,6, 96 GiB RAM, eight performance cores and four efficiency cores. The comparison suites run searches serially. Release builds use the existing lockfile and no new dependencies. Native RSS comes from `/usr/bin/time -l`; heap numbers come from separate `dhat-heap` builds with line information. Profiling overhead is not presented as native search time. This report reads the saved artifacts, without rerunning benchmarks.

Sources are under `target/measurements/`: `summary.jsonl`, `t2-warm.json`, `intrinsics.jsonl`, each run's `result.json`, `stdout.txt`, `stderr.txt` and `dhat-heap.json`, and `composed-*/best.json`. The standalone `baseline-m4.txt` supplies baseline M4 native measurements, which are absent from the summary's native rows. The similarly named `baseline-m4-time` is a failed hotpath profile, not that native run. Later completed result records take precedence over the older summary, notably for the t4 timeouts.

Fixed comparison inputs:

- t2: `2 s1,P,s0 O,P,O 16 1 8 x 1`.
- M4: `4 x0,x1,x2,x3 t6,t5,t7,t4 16 0 8 x 2 lazy`.
- t3 re-entry: `3 s0,P,s1,s2 O,P,O,O 16 2 8 x 1`.

The M4 comparison goal is a prefix, as in the original benchmark. Production block searches additionally require `--clean-goal`, because leftover PRIME copies would otherwise change the caller's stack. Reported successful search records have independent numeric replay via `check.py` on 64 deterministic BN254 inputs, including boundaries, checking overflow, operands, output order, reduction and program cost. This is not a proof over all field inputs or validation of the generated caller's gas.

For t2, wall time is the median of 15 warm subprocess runs, including process startup. The coarse single-run times in `summary.jsonl` are not used for t2 timing comparisons. RSS still comes from the individual native run, not a median of those 15 runs. M4 and t3 wall times are individual native `/usr/bin/time -l` results, not repeated medians. Small differences should not be treated as statistically established improvements. The comparison RSS and heap columns are exact bytes; per-state ratios are rounded. Descriptive MB uses decimal units, and MiB/GiB uses powers of two. Profiler and snapshot units are preserved as printed where noted.

`expanded` counts partial expansions, including repeated visits to a retained state. The arena counts distinct retained states, both open and closed. Queue entries are not additional states: they may be stale or refer to partially expanded nodes. Dhat's global peak is the sum of `gb`, not the sum of the individual allocation-site maxima. Heap/RSS are different quantities measured in different runs and need not agree.

## Cumulative performance comparison

Each row includes the preceding changes, rather than measuring an isolated patch:

| Variant | Revision | Change |
| :--- | :--- | :--- |
| baseline | `2fb3452` | Partial-expansion A*, 24-byte nodes, exact-key index table and bucket queue |
| buckets | `6e1bfb4` | Release exhausted f-bucket capacity |
| chain | `088ea3f` | Skip nested continuations whose result cannot feed the outer macro |
| resource | `c9e2d74` | Correct the t3 intermediate bound; account for value-slot copies and retained goal constants |
| tiebreak | `c40dbd7` | Larger g first at equal f, then LIFO; add clean goals |
| live | `9f9f16a` | Exclude dead values from the copy-bound supply |

All completed fixed-input comparison runs return the same program cost: t2 123, M4 125, t3 189. The resource change also corrects an overestimate in the old t3 heuristic; unchanged measured costs are not a general proof of the old heuristic's admissibility.

### t2

| Variant | Warm wall median | Native peak RSS (B) | Dhat peak heap (B) | Heap/final state (B) | Expanded | Final retained |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline | 25.045 ms | 3,047,424 | 587,317 | 90.44 | 11,940 | 6,494 |
| buckets | 25.188 ms | 2,998,272 | 565,455 | 87.07 | 11,940 | 6,494 |
| chain | 25.223 ms | 2,998,272 | 565,453 | 87.07 | 11,940 | 6,494 |
| resource | 14.268 ms | 2,916,352 | 552,083 | 130.76 | 5,965 | 4,222 |
| tiebreak | 9.695 ms | 2,883,584 | 449,505 | 170.20 | 3,713 | 2,641 |
| live | 6.506 ms | 2,834,432 | 396,781 | 266.65 | 1,964 | 1,488 |

Baseline samples span 24.804 to 25.429 ms; live spans 6.210 to 6.707 ms. The warm median improves 3.85x, native RSS falls 7.0%, and peak heap falls 32.4%. Buckets and chain do not improve this input's warm time. The increasing heap/final-state ratio is not an increasing node size: the fixed 256 KiB initial index table alone is 262,144 bytes even when only 1,488 states remain.

### M4

| Variant | Native wall | Native peak RSS (B) | Dhat peak heap (B) | Heap/final state (B) | Expanded | Final retained |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline | 20.42 s | 101,761,024 | 95,693,915 | 47.35 | 6,198,080 | 2,020,923 |
| buckets | 18.71 s | 94,994,432 | 82,404,089 | 40.78 | 6,198,080 | 2,020,923 |
| chain | 9.61 s | 97,107,968 | 82,402,871 | 40.77 | 6,198,080 | 2,020,923 |
| resource | 4.82 s | 83,427,328 | 85,540,782 | 57.68 | 3,232,754 | 1,483,005 |
| tiebreak | 4.20 s | 76,103,680 | 81,624,178 | 59.74 | 2,986,211 | 1,366,327 |
| live | 4.22 s | 74,350,592 | 81,624,174 | 59.74 | 2,986,211 | 1,366,327 |

Baseline to live is 4.84x faster, with 26.9% lower native RSS and 14.7% lower peak heap. Chain halves the remaining runtime without changing expanded or retained states, but native RSS rises relative to buckets. Resource reduces states yet increases heap from 82.40 to 85.54 MB: the queue at the global peak grows from 6,823,936 to 9,961,472 bytes while arena and overlapping table capacities stay unchanged. Live does not reduce M4's state counts relative to tiebreak; 4.20 versus 4.22 s and four bytes of heap difference are not evidence of a speed or heap improvement.

### t3 re-entry

| Variant | Native wall | Native peak RSS (B) | Dhat peak heap (B) | Heap/final state (B) | Expanded | Final retained |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline | 338.41 s | 684,523,520 | 711,356,994 | 48.95 | 23,411,641 | 14,533,275 |
| buckets | 328.38 s | 651,624,448 | 674,526,268 | 46.41 | 23,411,641 | 14,533,275 |
| chain | Not rerun | Not rerun | Not rerun | Not rerun | Not rerun | Not rerun |
| resource | 257.62 s | 535,085,056 | 670,271,560 | 58.52 | 16,600,747 | 11,454,239 |
| tiebreak | 146.69 s | 325,009,408 | 339,900,869 | 51.69 | 9,866,596 | 6,576,352 |
| live | 30.27 s | 88,915,968 | 87,663,641 | 55.78 | 2,076,175 | 1,571,668 |

Chain t3 was deliberately not rerun because this input already uses `chain=1`; the skipped deeper recursion does not change it. The buckets row is the preceding measurement, not a new chain measurement. Baseline to live is 11.18x faster, with 87.0% lower native RSS and 87.7% lower peak heap. Excluding dead values from the resource supply makes the largest final reduction: 9,866,596 to 2,076,175 expansions and 6,576,352 to 1,571,668 retained states.

## What the heap peak means

Heap/final state above is a normalization by the final retained count, not the bytes per state present at the instant of peak heap. `summarize.py` infers a table-growth peak from simultaneous old N-slot and new 2N-slot u32 tables: table bytes are 12N, and the triggering retained count is `floor(0.6N) + 1`. The raw dhat `gb` sums match the reported peaks. Where this capacity signature exists:

| Case / variant | Old + new table bytes | Inferred states at peak | Peak heap / states at peak (B) |
| :--- | ---: | ---: | ---: |
| M4 buckets | 25,165,824 | 1,258,292 | 65.49 |
| M4 chain | 25,165,824 | 1,258,292 | 65.49 |
| M4 resource | 25,165,824 | 1,258,292 | 67.98 |
| M4 tiebreak | 25,165,824 | 1,258,292 | 64.87 |
| M4 live | 25,165,824 | 1,258,292 | 64.87 |
| t3 baseline | 201,326,592 | 10,066,330 | 70.67 |
| t3 buckets | 201,326,592 | 10,066,330 | 67.01 |
| t3 resource | 201,326,592 | 10,066,330 | 66.59 |
| t3 tiebreak | 100,663,296 | 5,033,165 | 67.53 |
| t3 live | 25,165,824 | 1,258,292 | 69.67 |

There is no corresponding inferred peak count for baseline M4 or the t2 profiles. Do not substitute their final counts as measured instantaneous counts. Capacity slack, temporary old/new tables, queues and cached information all sit above the 24-byte node payload.

Baseline M4 holds 95,693,915 bytes at its global peak: 50,331,648 in the node arena, 28,498,752 in queue buckets and 16,777,216 in the index table, plus smaller allocations. Live M4's peak instead includes 50,331,648 arena bytes, 25,165,824 overlapping table bytes and 6,025,920 queue-entry bytes. Live t3 also has 50,331,648 arena and 25,165,824 table bytes, with 6,960,848 queue-entry bytes and 4,456,456 bytes at the validity-cache allocation site, plus smaller allocations.

Optimized stack frames can be aliased or misleading, including frames labelled `build`, `main` or the end of `search`. They do not establish that the global peak occurred during path reconstruction. The table-capacity inference above is separate from frame-based attribution; no reconstruction instant is inferred here.

A running baseline M4 snapshot reported 58 MB footprint: 43 MB Malloc Large, 14 MB Malloc Small and 656 KB malloc metadata. The corresponding vmmap summary reported 57.4 MiB resident malloc pages and 73.1 MiB allocated. These are mid-run snapshots, not whole-run peaks (`baseline-m4.footprint.txt`, `baseline-m4.vmmap.txt`). The recorded `xcrun --find xctrace` check was unavailable, so Allocations was not installed or used.

## Computation trace and profiling

1. Build the small class/production graph and swap table.
2. Pop an index, read its 24-byte node and decode the packed stack.
3. Enumerate productions, operand placements and one continuation; reject dead or unreachable layouts.
4. Evaluate each child's stack-dependent heuristic from cached mask information.
5. Probe the exact-key index table for admitted children, insert/improve labels, and queue the next partial-expansion threshold.
6. Re-expand the winning parents and independently replay the primitive program.

### t2 hotpath before and after

Sources: `baseline-t2-time/stdout.txt` and `live-t2-time/stdout.txt`. These are instrumented timings, not the native warm subprocess medians.

| Function | Baseline calls | Live calls | Baseline total | Live total |
| :--- | ---: | ---: | ---: | ---: |
| main | 1 | 1 | 61.56 ms | 7.10 ms |
| search | 1 | 1 | 60.21 ms | 6.62 ms |
| expand | 11,946 | 1,971 | 49.07 ms | 5.33 ms |
| chain | 71,086 | 10,350 | 69.51 ms | 7.56 ms |
| realize | 316,287 | 48,148 | 6.91 ms | 0.72360 ms |
| valid | 310,918 | 48,319 | 13.06 ms | 1.48 ms |
| heuristic | 135,083 | 20,670 | 2.00 ms | 0.28620 ms |
| closed_lookup | 25,382 | 3,037 | 0.87445 ms | 0.06369 ms |
| closed_insert | 6,493 | 1,487 | 0.10938 ms | 0.03335 ms |
| open_pop | 11,941 | 1,965 | 0.14634 ms | 0.03295 ms |
| comp_info | 30 | 26 | 0.02795 ms | 0.00824 ms |

Timings are inclusive and overlap. Recursive chain totals exceed the enclosing search time; they must not be added to expand or treated as an independent segment. Expand includes reconstruction calls, so its counts exceed the native expanded-state counters by six and seven respectively. The trace supports prioritizing successor generation over closed lookup, but not summing every row into a runtime model.

Allocation sources: `baseline-t2-alloc-count/stdout.txt`, `live-t2-alloc-count/stdout.txt` and the corresponding `*-alloc/stdout.txt`. Counts and bytes are separate profiles and exclusive of nested functions. Byte units and rounding in this table are as printed by hotpath, not exact-byte dhat peaks or retained memory.

| Function | Baseline allocations | Live allocations | Baseline allocated bytes | Live allocated bytes |
| :--- | ---: | ---: | ---: | ---: |
| Total | 6,002 | 6,847 | 1.0 MB | 723.6 KB |
| main / setup | 5,750 | 5,751 | 235.1 KB | 235.1 KB |
| search | 153 | 254 | 392.5 KB | 326.2 KB |
| closed_insert | 13 | 766 | 383.9 KB | 126.4 KB |
| comp_info | 60 | 52 | 660 B | 572 B |
| chain | 15 | 14 | 18.2 KB | 17.8 KB |
| valid | 9 | 8 | 34.0 KB | 17.0 KB |
| expand | 2 | 2 | 608 B | 608 B |
| realize, heuristic, closed_lookup, open_pop | 0 | 0 | 0 B | 0 B |

Total allocation count rises by 845 despite lower allocated bytes and lower peak heap. In particular, the counts attributed to closed_insert and search increase; the smaller state set does not imply fewer allocations. Zero-allocation realize, heuristic and lookup paths remain zero-allocation.

The full baseline M4 hotpath timing attempt was stopped at the RSS guard, with a sampled 64,150,650,880 bytes for the process group. Its event storage dwarfed the search heap; no timing profile was completed, and its wall time is not used. Although its stdout contains cost 125, its result is stopped and unverified. The guard was subsequently tightened to 48 GiB with 250 ms sampling. The small complete hotpath traces are used instead. This is a profiler limitation worth investigating separately, not a search-memory result.

### Measured intrinsic references and headroom

`intrinsics.jsonl` records single-threaded medians of 15 samples after a warmup (`src/bin/intrinsics.rs`):

| Primitive | Measured reference |
| :--- | ---: |
| Dependent two-multiply/rotate hash chain | 3.040 ns/hash |
| 19-byte stack copy and byte update | 5.373 ns/copy |
| Sequential read, 128 MiB working set | 59.73 GB/s |
| Sequential read, 768 MiB working set | 58.62 GB/s |
| Dependent random lookup, 128 MiB working set | 88.53 ns/lookup |
| Dependent random lookup, 768 MiB working set | 117.02 ns/lookup |

These are primitive reference costs, not a complete search floor. A hash reference omits table probes, key comparisons, node reads and collisions. A copy reference omits operand placement, arithmetic, reachability and rejection. Large-working-set dependent reads are not a model for cache-resident t2: its measured closed-lookup averages are only 34 ns baseline and 20 ns live. Streaming bandwidth is not random-table throughput, and heap capacity is not a measurement of bytes actually read.

For scale, one reference hash per recorded closed lookup would cost 0.07716 ms baseline and 0.00923 ms live. One reference copy per realize call would cost 1.69925 ms and 0.25868 ms. Those are incomplete primitive-floor proxies, conditional on that work count, not rigorous lower bounds for the optimized functions. Compiler fusion, early rejection and different cache behavior can change the correspondence. Subtracting them from hotpath totals does not predict an achievable saving or speedup.

Successor generation dominates the complete t2 trace: 49.07 ms inclusive in the baseline versus 0.87445 ms for exact closed lookup. In the live version these are 5.33 and 0.06369 ms. The incomplete primitive counts and instrumentation overhead do not establish a complete runtime floor or a numerical speedup prediction. Setup and reconstruction have no independent segment profile, and the large-M4 hotpath trace did not complete. The measured priority is reducing generation work and unnecessary states, not replacing exact keys based on a hash or bandwidth ratio.

## Search outcomes and scope

The following costs are primitive-program search costs, not final permutation or public hash gas tables. Optimality is only within the configured macro graph, useful-form whitelist, garbage, depth and reach limits. Numeric replay establishes the recorded candidates' tested behavior, not unrestricted EVM optimality. Caller cleanup, layout transitions and retained constants still matter.

### t2 and clean M4

- t2 entry costs 27 (`t2-entry`); round and exit cost 123 (`live-t2`, `t2-round-other`, `t2-exit`); re-entry costs 129 (`t2-reentry`); final costs 139 (`t2-final`). All records are verified.
- Clean M4 block, exit and final cost 125, 128 and 157 respectively (`m4-clean`, `m4-exit`, `m4-final`), versus the existing template costs 128, 131 and 169. These are clean goals, unlike the fixed prefix benchmark. Their native walls are 4.20, 5.24 and 3.99 s. They leave exactly `t6,t5,t7,t4`, `t6,P,t5,t7,t4`, and `t6,t5,t7,t4` respectively.
- t3 re-entry from `s0,P,s1,s2` costs 189 versus the previous template's 198. Cost 189 was already found at baseline; the cumulative changes reduce the resources needed to find it, not this result's cost.

### Full t3 finals

Both final-cycle inputs reach the fixed reduced goal `o0,o1,o2,P` at cost 216, matching the current hand-written final's cost rather than improving it:

| Artifact | Initial layout | Garbage limit | Cost | Native wall | Expanded | Final retained | Native peak RSS (B) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `t3-final-old-live` | `s0,P,s2,s1` | 2 | 216 | 976.70 s | 48,348,912 | 36,267,384 | 1,264,123,904 |
| `t3-final-new` | `s2,P,s1,s0` | 2 | 216 | 986.51 s | 48,348,882 | 36,267,359 | 1,253,163,008 |
| `t3-final-C-g6` | `s0,P,s2,s1` | 6 | 216 | 1,142.82 s | 54,586,949 | 41,567,292 | 1,942,634,496 |

The earlier `t3-final-old` stopped at 600.04 s without a result, at sampled peak RSS 994,934,784 bytes. It is not evidence that the later completed search failed. Widening garbage from two to six finds no cheaper program in the recorded run and costs more time and memory.

A garbage-two full search cannot reproduce the exact old hand program because that program leaves six dead values. It nevertheless finds equivalent cost-216 programs leaving only one dead value (`s1`) or two (`s1,s0`) after the goal prefix. The garbage-six result also leaves only `s1`. Equal cost and equivalent required outputs do not mean an identical opcode sequence or identical trailing stack.

Auxiliary linear-only final searches are separate from these full results: `t3-linear-final-012` returns 69 in 27.87 s; `-102` returns 72 in 112.53 s; `-210` returns 72 in 111.30 s; `-120` times out. Those costs omit the S-box prefix. The saved `t3-final-A-fallback.txt` is a cost-222 fallback, not the best completed full final.

### t4 full-search limits and restricted composition

At this report's readback, `t4-round-0`, `t4-exit` and `t4-final` have completed `result.json` records, superseding their earlier running status. Each stopped at its 600 s time limit without a cost. None establishes an unfinished search's eventual outcome or an impossibility result.

| Artifact | Recorded outcome | Elapsed runner time | Sampled peak process-group RSS (B) |
| :--- | :--- | ---: | ---: |
| `t4-entry` | 2 GiB RSS guard, no result | 197.38 s | 2,149,138,432 |
| `t4-round-0` | Time limit, no result | 600.01 s | 4,068,278,272 |
| `t4-exit` | Time limit, no result | 600.01 s | 3,999,367,168 |
| `t4-final` | Time limit, no result | 600.19 s | 4,193,304,576 |

These stopped-run RSS values are sampled group maxima, not completed `/usr/bin/time -l` native peaks. The full round, exit and final use garbage limit three, extra depth eight and chain one. Entry starts with S-box outputs and is linear-only. With the conservative lazy M4 model, `t4-entry-lazy` completes at cost 125 in 4.04 s native wall, with 77,774,848-byte native peak RSS. `t4-linear-final` returns linear-only cost 163 in 5.11 s; it is not a full cost-163 final round.

Completed `composed-*/best.json` files give the following restricted candidates, all marked verified:

| Artifact | Initial layout | Best cost | S-box order | Peak composed stack |
| :--- | :--- | ---: | :--- | ---: |
| `composed-t4-round-prime` | `s0,P,s1,s2,s3` | 326 | 0,1,3,2 | 13 |
| `composed-t4-round-raw` | `s0,s1,s2,s3` | 332 | 0,1,3,2 | 13 |
| `composed-t4-round-canonical` | `s0,s1,s2,s3,P` | 332 | 0,1,3,2 | 14 |
| `composed-t4-final-prime` | `s0,P,s1,s2,s3` | 358 | 0,1,2,3 | 15 |

The round goal is `t6,P,t5,t7,t4`; the final goal is `t6,t5,t7,t4,P`. Each candidate leaves `s1,s2,s3` beyond that prefix; the canonical round additionally leaves its original trailing P. Prime-under-first is cheaper than raw/canonical here, but changing the caller to supply that layout has a cost of its own.

Composition fixes all S-boxes before the linear layer, tries orders with the initial top lane first, and uses the conservative lazy M4 model for the separate linear search. It does not search arbitrary interleavings. Its replay arguments permit garbage eight and extra depth thirteen; the measured peak stack is 13 to 15. Per-order time and RSS limits further restrict the exploration. These are best recorded composed candidates, not globally optimal t4 programs, and not results of the unrestricted full-round searches.

### t4 interleaved rounds

The heuristic now counts an input once however many copies are on the stack and charges at least 2 for every S-box whose input is not on top (only a DUP or SWAP of the input or a POP right above it brings it there). From `s0,P,s1,s2,s3` the round bound rises from 296 to 302 and the final bound to 334; the entry (`x0,x1,x2,x3,P`, linear only) is 104. Earlier programs and costs reproduce: t2 123, t3 re-entry 189 (30 s), the clean M4 exit 128, the t3 final 216. `UB=<cost>` drops every node whose f reaches cost, so a search either returns a cheaper program or proves within its graph that there is none.

Three restrictions of the composed programs cost gas. The linear search ran with garbage zero and a clean goal; with garbage two, lazy, the M4 from the composed S-box order costs 125 instead of 128 (`x2,x3,x1,x0` and `x3,x2,x1,x0`; `x1,x3,x2,x0` and `x1,x2,x3,x0` stay 128; the final M4 stays 160). The entry was the clean block (125) followed by `DUP5 SWAP1` (6) in round 0; searched to the round layout directly it costs 122. And the S-boxes need not all come first. `interleave.py` fixes the first k S-boxes and searches the others with the linear layer (lazy, the prefix's dead inputs plus two more as garbage):

| Kind | Bound | Composed | k = 3 | k = 2 | k = 1 | k = 0 |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| round (`t6,P,t5,t7,t4`) | 302 | 326 | 320 | 317 | none < 317 | none < 317 |
| final (`t6,t5,t7,t4,P`) | 334 | 358 | 352 | none < 352 | none < 352 | stopped |
| entry (linear) | 104 | 125 + 6 | | | | 122 |

Every round kind (entry exit, steady, pre-internal exit, re-entry after the internal rounds) starts from `s0,P,s1,s2,s3`: the internal template leaves its outputs in that layout over one dead s3, so one round program serves all of them. The k = 3 round prefixes 0,1,2 and 0,1,3 give 320 (63 s and 138 s), 0,2,1 / 0,2,3 / 0,3,2 give 323, 0,3,1 stops at its 600 s limit. The k = 2 round prefix 0,1 gives 317 in 72 s (948 MiB); 0,2 and 0,3 exhaust everything below 317 in 21 s and 39 s. With S-box 0 fixed (garbage two and four) nothing below 317 exists (141 s, 1.1 GiB; 277 s, 2.1 GiB). The unrestricted round search (`s0,P,s1,s2,s3`, garbage four, `UB=317`) exhausts f below 317 in 881 s at 7.6 GB sampled RSS, 181M states: 317 is optimal within the macro graph, reach, depth, garbage and the lazy bounds. The final k = 3 prefix 0,1,3 gives 352 (130 s); 0,1,2 and 0,2,1 give 355; with two S-boxes fixed nothing below 352 exists (every prefix within 443 s), nor with S-box 0 fixed (garbage four, 1,582 s, 14.6 GB peak RSS). The unrestricted final search (`UB=352`) was stopped by hand after 53 minutes at f = 349 with 722M states and 25 GB sampled RSS, two f levels short.

## Verified call gas

Before is `2fb3452`; after is the paired TS/Rust template update. Except for the explicitly labelled t4 hashes, these are raw permutation entry calls, not hypothetical public hash wrappers. The README uses the same raw entries for widths other than t4. Gas excludes transaction intrinsic cost. Osaka split entries include cold hops.

| Entry | Osaka before | Osaka after | Amsterdam before | Amsterdam after |
|---|---:|---:|---:|---:|
| t2 | 6,066 | 6,066 | 6,027 | 6,027 |
| t3 | 7,992 | 7,992 | 7,914 | 7,914 |
| t4 hash_1 | 12,263 | 12,227 | 12,176 | 12,149 |
| t4 hash_2 | 12,285 | 12,249 | 12,198 | 12,171 |
| t4 hash_3 | 12,358 | 12,322 | 12,271 | 12,244 |
| t4 permutation | 12,482 | 12,428 | 12,395 | 12,350 |
| t8 | 24,759 | 24,507 | 24,280 | 24,208 |
| t12 | 35,826 | 35,718 | 34,884 | 34,776 |
| t16 | 54,194 | 53,927 | 45,684 | 45,540 |
| t20 | 72,368 | 69,398 | 56,665 | 56,485 |
| t24 | 87,534 | 87,333 | 67,559 | 67,343 |
| t28 | 106,606 | 105,773 | 80,301 | 80,049 |

No call-gas regressions. The lower t3 re-entry program cost does not reduce the selected complete call's gas. The generator re-enters from `s0,P,s2,s1`, whose template already costs 189 like the searched `s0,P,s1,s2` program, so the layout has nothing to gain; the loss was the lazy outputs of the last internal round, whose s1 + c and s2 + c took an ADDMOD and the S-box without its PRIME copy (14 gas a lane). Reducing them in that round instead (8 a lane) gives t3 7,914 to 7,902 (Amsterdam) and 7,992 to 7,980 (Osaka). The t = 3 internal rounds averaged 111.5 gas (S-box 42 plus 59 to 83, four dead values a round, all DUPs). `t3int 1 1 1 1 2 9` finds 64 after the S-box from reduced s1, s2 back to reduced outputs (lazy sum, two ADDMODs, one dead value, two SWAPs; 221 s, 27 GB, nothing cheaper within garbage 2 and 9 entries), `t3int 4 4 1 1 2 9` 72 from the lazy outputs of the external round (306 s). With them t3 is 7,768 on Amsterdam and Osaka (7,902 and 7,980 before); the rounds consume their PRIME copies, so the later ones are PUSH32 (Amsterdam 5,031 to 6,733 bytes, same gas). Garbage 3 with 10 entries ran out of memory past 21 GB; the relaxed floor is about 55 (six DUPs, three PRIME copies, four ADDs, two ADDMODs). Osaka t20 now uses one 23,910-byte contract rather than two parts. t24/t28 still use two parts; their warm-hop gas is 84,833/103,273. Amsterdam t8 is 24,090 to 24,018 core gas plus the unchanged 190-gas raw wrapper, so its comparable call saving is 72 gas.

Verification completed:

- `npm run generate:huff:rs` passed.
- `./generator-rs/parity.sh amsterdam osaka` found 27 Amsterdam and 29 Osaka files byte-identical. TS/Rust times were 505.047/35.701 seconds for Amsterdam and 1,005.720/104.034 for Osaka.
- `poseidon2-gen verify --hardfork` passed widths 2, 3, 4, 8, 12, 16, 20, 24, 28 on each fork; every measured gas value matched the model exactly.
- Forge passed 123 tests across 13 suites, with zero failures or skips. Three t4 fuzz tests retained 10,000 cases each; four Yul comparison tests retained their existing 1,000-case overrides.
- `./gas-report.sh` passed and confirmed the three Amsterdam t4 hash values above.
- Independent review found all 21 TS/Rust template `init`/`ops` pairs identical and no actionable dispatch, layout or round-index issue. Full t4 templates run before separate S-boxes; unmatched layouts retain a linear or generic fallback. Folded hash round zero and the s0-only hash final path remain separate.

## Internal rounds

The t = 4 internal round the scheduler built costs 169 gas (S-box 45, sum 29, lanes 95) and leaves five dead values: the sum, s0^5 and the three old lanes. With every value used as often as the round needs and nothing left behind, its floor is 154. Without SWAP five dead values are the minimum: the sum is created on top and never consumed (the first output that consumes it leaves no copy for the others), so every value under it at that moment stays, and each lane is still needed there for its product. The audit's estimate of two recoverable values (336 gas) does not hold without SWAP.

`internal` searches the round over single opcodes. For four lanes it does not finish: with the DUP rule, garbage at most 1 and depth 15 the f = 157 level was still open after 18M expansions and 133M states. The three-lane analogue (lanes scaled by their own d_i, not the t = 3 round) finishes: `internal 3 s0,P,s1,s2 s0,P,s1,s2 4 12` with `NO_POP=1` returns 137 in 18.9M expansions and 81M states (`internal3.program`), against 140 for the four dead values a round without SWAP leaves there. It leaves one dead value and takes two SWAPs: the sum lands on a PRIME copy, its copies and the operands of the lanes are pre-placed in the order the lanes come, the last lane is taken by a copy, and every other output is swapped into the slot of the next lane, which comes up onto its operands.

Extended by hand to four lanes (`internal4.replay`, replayed at 166 from the bounds of the first internal round, s = 3,2,3,2) the round costs 166: one dead value and three SWAPs. With it the t = 4 permutation is 12,252 to 12,067 gas and hash_1/2/3 12,149/12,171/12,244 to 11,964/11,986/12,059 on Amsterdam; on Osaka, whose rounds had to leave a PRIME copy within DUP16 reach above the growing garbage, hash_2 is 12,249 to 11,986. The stack depth falls from 319 to 93.

`cycle` bounds the internal rounds with no layout fixed between them (any sequence of rounds, the next one free to start early). Its relaxation drops PRIME copies, constants and the S-box's own copies (each a fixed cost) and counts the copies, SWAPs and POPs of the linear layer's values, with the DAG fixed (the sum as merges of partial sums; t = 4 d_i * s_i + sum; t = 3 x + sum, s1 + sum, (sum + s2) + s2 or 2 s2 + sum). Over every layout a round can end in, value iteration gives the least cycle mean exactly (the least and largest change of D_k agree from k = 2):

| Width | Window | End layouts | States a round | Cycle mean | Round (fixed part + mean) |                Wall |
| :---- | -----: | ----------: | -------------: | ---------: | ------------------------: | ------------------: |
| t=4   |      7 |      27,530 |      1,842,225 |         33 |            133 + 33 = 166 |                83 s |
| t=4   |      8 |     176,610 |     18,334,540 |         33 |            133 + 33 = 166 |             1,160 s |
| t=3   |      8 |      16,590 |      4,989,712 |         27 |             82 + 27 = 109 |               235 s |
| t=3   |      9 |      39,172 |     25,042,752 |         27 |             82 + 27 = 109 | stopped after k = 2 |

The window counts values above the deepest live one (PRIME copies and constants not included); the 166 program needs 8. t = 4 with window 9 did not finish its first round in 43 minutes (10 GB) and was stopped. The relaxation does not see which ADD reduces, so the t = 3 mean holds for any reduction policy: the four periodic templates (low 101, high 109, reset 117, final 109) take 27 like the earlier 109 one (nine value DUPs and SWAPs), only their fixed part differs (74, 82, 90, 82). The rounds in the repository are therefore optimal over every multi-round schedule in this model: a cyclic search has nothing to find. One round alone from a free layout to a free one costs 27 (t = 4) and 21 (t = 3), so a free start and end save at most 6 gas a hash. Outside the model are other DAGs (outputs not built as product plus sum, more additions) and S-boxes interleaved with other values.

Those departures were tested next, and none makes the internal rounds cheaper:

- S-box interleaved with the linear layer. `SBOX=1` makes the S-box three MULMODs on stack values of its own (v = s0 + c used three times, v^2 twice, v^4 once), their copies counted and every linear-layer move allowed between them; the fixed part drops the 9 gas of S-box copies it held (t = 4 124, t = 3 73). The mean is the old one plus exactly those 9: t = 3 window 8 36 (73 + 36 = 109; 56,084 end layouts, 11.0M states, 585 s, 1.4 GB), t = 4 window 7 with `COMP` 42 (124 + 42 = 166; 40,010 end layouts, 6.2M states, 238 s, 0.8 GB). `SPLIT=1`, which leaves the intermediates out and lets x appear on top any time after s0 is consumed, gives t = 3 24, but a real program cannot do that: an intermediate left under other values costs a copy or a SWAP, and `SBOX` charges them. The window counts the S-box's values, so these cover fewer linear-layer layouts than the base runs; t = 4 window 8 would take about 3,500 s and was not run, t = 3 one round from `s0,s1,s2` at window 9 did not finish in 900 s (2.9 GB).
- Other DAGs. In any straight-line program whose outputs are used once and every other value at least once, copies = uses - values = the number of binary ops with two non-constant operands (ADD of two values, MULMOD of two values; a PUSHed constant is a value used once). Floor B therefore depends only on the op count: the same ops in another tree cost the same, and only fewer value-value ops can lower it. t = 4 needs four MULMODs by its constants per round: d_0..d_3 are 247 to 254 bits, no d_i or d_i + 1 is a small rational (numerator times denominator below 2^80), no two satisfy a + k b small for |k| <= 8, none is a power of another up to degree 8, so no MULMOD becomes an ADD or SHL (`diag_relations.py`). Rescaling the lanes (s_i stored as lambda_i s_i, lane 0 through the fifth root, which exists since 5 does not divide p - 1) moves mu_0 but keeps it: the ratio of x to the other lanes in s0' against the other outputs is mu_0 under every scaling. `COMP=1` lets t = 4 build s_i' as mu_i s_i + (the sum of the other lanes) when that partial sum is in the tree (MULMOD(s_i, diag + 1) folding the self term): window 7 33, unchanged (29,450 end layouts, 4.7M states, 178 s, 0.8 GB). For t = 3, `SHL=1` (2 s2 as PUSH1 1 SHL: one value-value op less, 3 gas more of arithmetic) gives 27 at window 8, unchanged, and 36 with `SBOX`.
- The round constant. It enters lane 0 only, right before the S-box, and the EVM has no a b + c op, so it takes its own PUSH32 and ADD: fusing it into the sum adds it to every lane, into d_0 x needs a second constant. The sum's one reduction stays too: lazy s_i' < 2P give x + s1 + s2 + s3 < 7P, over 2^256 (5.29P), and ADDMOD, MOD + ADD, or reducing the outputs cost at least the same 8 gas more than an ADD.

## Hash round 0 (t = 4)

The hash entry's round 0 folds the initial linear layer and the sponge constants into y_i = p_i + K_i, p_i = sum_j M4[i][j] in_j. It loaded each word reduced (DUP of PRIME, PUSH, CALLDATALOAD, MOD: 14), built y_i lane by lane with its S-box, ran the generic M4 (131) to `[s0', s1', s2', s3', PRIME]`, and the rounds after began with `DUP5 SWAP1` to reach ROUND4's `s0,P,s1,s2,s3`. Loads, round 0 and that adapter cost hash_1 / hash_2 / hash_3 14 + 357 + 6 = 377, 28 + 399 + 6 = 433 and 42 + 425 + 6 = 473 (the 399 of hash_2 against a floor of 354).

Now round 0 is the forms p_i, left as `[p0, P, p1, p2, p3]`, then ROUND4 itself (317) with K_i in place of its round constants (`hash_forms` in templates.rs). The forms take the words from calldata as CALLDATALOAD leaves them (PUSH, CALLDATALOAD: 6) as often as they like: ADDMOD, MULMOD and MOD reduce them as they use them, so a word used only by those needs neither its MOD nor a copy. `hashdag` (`src/bin/hashdag.rs`) schedules a fixed DAG over single opcodes from the PRIME copy SETUP pushes, A* with the ops still to run, a DUP or load per use beyond the entries on the stack and a PRIME copy or 4 per op that needs one as the heuristic:

| Arity | DAG | Forms gas | Scope | States | Wall | Peak RSS |
| :--- | :--- | ---: | :--- | ---: | ---: | ---: |
| hash_1 | p2 = in0 mod P, p1 = 4 p2 (MULMOD), p0 = p1 + p2 | 40 | depth 9 | 240 | 0.7 s | 2 MB |
| hash_2 | p3 = ADDMOD(in0, in1), w = ADDMOD(in1, in1), p2 = p3 + w, p1 = 4 p3 + w, p0 = p1 + p3 | 84 | depth 10 | 4.9M | 4.8 s | 0.9 GB |
| hash_3 | b = in1 mod P, t0 = ADDMOD(in0, b), w = ADDMOD(b + b, in2), p3 = t0 + 4 in2, p2 = p3 + w, p1 = 4 t0 + w, p0 = p1 + t0 | 124 | depth 8 | 37.9M | 75 s | 6.7 GB |

Nothing cheaper exists for these DAGs within those depths. hash_2 with p0 = p2 + 4 p3, or with in1 reduced and w = b + b, has nothing below 84; hash_3 with all three words raw (t0, 2 in1 and w by ADDMOD), or with in0 and in1 reduced and t0 = a + b, has nothing below 124 at depth 8; hash_3 at depth 10 was stopped by the 30 GiB guard at f = 121. These are the cheapest found, not a proof over every DAG.

Each program above consumes the PRIME copy SETUP pushes. The rounds after then hold no PRIME copy to DUP and push PRIME 103 times (PUSH32, the same 3 gas): hash_1 / hash_2 / hash_3 would be 11,890 / 11,900 / 11,973 gas at 16,739 runtime bytes on Amsterdam (13,629 before). Pushing one PRIME copy first and leaving SETUP's under everything costs 3 more a call (`hashdag` with `KEEP=1` finds 43 / 87 / 127, the same programs after a PRIME copy), and hash_1 copies its word once more (46) so that every arity leaves `[s0', P, s1', s2', s3', 3 dead, P]`, the layout the shared rounds take. That is the committed version: 46 + 317 = 363, 87 + 317 = 404 and 127 + 317 = 444 against 377, 433 and 473, so hash_1 / hash_2 / hash_3 11,910 / 11,932 / 12,005 to 11,896 / 11,903 / 11,976 gas on both forks, 13,611 runtime bytes on Amsterdam and 15,719 on Osaka.

ROUND4 copies p1 and p3 and leaves the originals dead. A program that fused the forms with the round could consume them in place, at most 6 gas an arity by the copy count; it was not searched (the round alone takes 881 s and 7.6 GB under `UB=317`).

## External rounds without fixed layouts (t = 4)

The steady external round costs 317 (ROUND4), optimal in the macro graph only from `s0,P,s1,s2,s3` to `t6,P,t5,t7,t4`; floor B is 296. `ecycle` (`src/bin/ecycle.rs`) asks whether freeing the layouts between rounds helps, the way `cycle` did for the internal rounds. It keeps the round's values as tokens (s_i, x_i, t0, t1, 2x1, 2x3, t2, t3, 4t0, 4t1 and t23), leaves out PRIME copies and constants (a fixed part of 266: S-boxes 180, the linear layer's ops 62, its 8 PRIME copies 24), so the S-box and MULMOD by 4 are unary moves on the top token, and counts DUPs (3), SWAPs and moves of one token to or from any depth (3) and POPs (2). The linear layer allows every production of the macro graph for these classes: s0' = s1' + t3 and s2' = s3' + t2, or through t23 = t2 + t3 (its ADD charged). The next round may start before this one ends. Value iteration over every end layout (closure from the inputs in every order) brackets the least cycle mean. ROUND4 costs 51 in this model (13 DUPs, 4 SWAPs) and needs window 9.

| Window | End layouts | States a round | One round from the inputs | Cycle mean bracket | Bound | Wall | Peak RSS |
| -----: | ----------: | -------------: | ------------------------: | :----------------- | :---- | ---: | -------: |
| 6 | none | | | | (no round fits) | 0.2 s | |
| 7 | 3,632 | 1.4M | 57 | 54 (k = 3) | 266 + 54 = 320 | 17 s | 0.2 GB |
| 8 | 21,240 | 12.8M | 57 | [51, 54] (k = 2, 3) | 266 + 51 = 317 | 381 s | 1.4 GB |
| 9 | 112,590 | 114M | 57 | stopped in k = 2 at the 30 min limit (D_1 done: 30) | | 1,800 s | 7.0 GB |

So no schedule of any number of rounds that stays within window 8 beats 317 a round, even with the PRIME copies placed for free; window 9, the first that holds ROUND4 itself, did not finish its second layer in 30 minutes (one layer takes about 13 minutes at 114M states). `PRIME=1` keeps the PRIME copies as tokens (the S-box and MULMOD by 4 take one under their operand, ADDMOD one under its two, each pushed for 3, a SWAP with a copy below everything moving the top to the bottom), which only raises the costs: window 7 gives 81, 242 + 81 = 323 (6,140 end layouts, 2.4M states, 59 s, 0.4 GB). The bound is within the window and over these productions; up to (317 - 296) x 6 = 126 gas a permutation stays unclaimed above window 8 only.

## Changes and rejected approaches

- Release an exhausted f bucket instead of retaining every historical frontier's capacity.
- Skip nested chain continuations: they return a different top value than the outer continuation requires, so the outer expansion already discarded them. This preserves the successor set.
- Correct the t3 intermediate-group bound and add aggregate value-slot accounting and retained goal constants. The CLI now enforces the full-output, raw-input domain required by the bound. Regression tests cover the former 11-gas estimate for an 8-gas two-plus-two completion and reject unsupported composite starts/partial goals.
- Prefer larger g at equal f, with LIFO within equal f/g. This changes tie-breaking, not the heuristic or optimality within the configured macro graph.
- Count only live needed values as the supply for mandatory copies. Dead inputs cannot supply a remaining operand or output, so they cannot reduce the copy deficit.
- Keep exact keys. No fingerprint collisions, beam pruning, weighted heuristic or memory-bounded deletion has been introduced. Resource guards stop runs; they do not silently discard search states and declare success.
- Fixed-prefix composition is an explicitly restricted alternative, not a replacement proof of full-search optimality.

Prior art: [Enhanced Partial Expansion A*](https://www.jair.org/index.php/jair/article/view/10882) distinguishes storing surplus successors from generating them; [Tiebreaking Strategies for A* Search: How to Explore the Final Frontier](https://cdn.aaai.org/ojs/10071/10071-13-13599-1-2-20201228.pdf) studies ordering within equal-f plateaus. The resource bound used here is derived directly from value-slot conservation, not an imported pattern database.
