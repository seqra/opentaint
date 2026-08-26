# TIFA without unrolling — implementation and measurement

`saloed/31-any-unroll-manager-design`, 2026-08-26. Implements
`2026-08-26-tifa-never-unroll-design.md` in
`core/.../ap/ifds/access/tree/TreeInitialFactAbstraction.kt`.

Frontier analyzer throughout: `anyUnrollLimit=100`, `anyUnrollKindPolicy=rescore`,
`anyUnrollRescoreStrategy=bfs`, conductor, one Spring handler (`WorkflowResource#rerun`), one taint
rule, 8 GB, 300 s IFDS budget. Harness `scoped-harness/scoped-run.sh`, jars
`tifabase-75d028a7aa0b4a67` (HEAD before the change, i.e. the memo build) and
`tifanew-597677812a956476`. `tifafinal-e10d579baf6f1dc1` is the same code with two comment blocks
and one dead private method different, rebuilt from the committed tree and re-gated; §4 carries its
confirmation run.

**Gate: 3,485 tests, 3,452 passed, 2 failures**, both the pre-existing
`JIRFactTypeCheckerUnrollFilterTest` ones (`gate-review.log` and `gate-inv.log` from earlier sessions
carry the same two).

---

## 1. What shipped

The walk is now five rules over a state `(T, N, p)` with `E = T.exclusions()`, and no round of
materialisation anywhere:

| rule | condition | action |
|---|---|---|
| R0 | `E == null` | emit `p` |
| R1 | — | nothing is ever written into `added` from an `[any]` |
| R2 | `a` held literally | descend if `T.child(a)`, else emit `p.a` if `a ∈ E` |
| R3a | `N` owns `[any]`, `E ≠ ∅`, no `[any]` trie child | emit `p.[any]` — **off by default**, §3 |
| R3b | `u ∈ U` in the `[any]` subtree | run the per-accessor helper at **this** prefix |
| R3c | `a ∈ E`, covered, absent, type-accepted | emit `p.a` |
| R4 | trie child `a`, not held literally, covered | descend into `N.getChild(a)` |

Deleted: `unrollAnyAccessors`, `UnrollResult`, `AnyAccessorUnrollRequest`, `addReversedApParents`,
the unroll round loop, `AccessPathTrieNode.unrolled` / `unrollAccessors`,
`enumerateAnyFrontier` / `enumerateHere`, the hoist state and `AbstractionState.hoistedAny`, and the
whole A-unroll block of `ApOpDiagnostics`. `readChildPaidOnly` and `budgetExhausted` survive on
`AnyUnrollManager` with no engine caller.

Kept, and it is the only loop left: re-walk while the last round registered a premise the trie did
not already hold. It terminates because every emission registers with an **empty** exclusion set, so
a trie node the walk itself created can never satisfy R3a, R3c or R2's emit arm — only nodes
registered from outside carry demand, and the rounds are bounded by the depth of that externally
registered trie, not by the shape of the fact.

## 2. What the design got wrong, and how it was found

Two of the design's rules had to be cut, and both cuts came from the same failure — the only new one
the gate produced.

`TreeCleanerFieldSensitivityAnalysisTest.concrete two-level clean over an abstract source — the
sanitized field is silent` went red: **one false positive**, a cleaned field resurrected. The test's
own comment says what it depends on:

> The source is any-field, so the cleaner's path does not exist as a fact until the demand-driven
> refinement produces it. Once it does, the clean is a node deletion again and field sensitivity
> survives the summary.

"the demand-driven refinement produces it" was the unroll.

The mechanism is not the missing materialisation, though. It is the premise **shape**: an entry fact
`R.[any].*` cannot express a node deletion inside the `[any]`, so a cleaner that bites on a concrete
path stops biting under it, and any `[any]`-carrying premise is a false-positive generator while
concrete premises are still being handed out.

That was **identified, not guessed**, and the ablation controls are how. The failure survived R3a
off, R3c off, R4 off, and single-round; it died only when the `[any]`-carrying premise disappeared
from both of its producers:

| arm | `sanitized field is silent` | `unsanitized field reports` |
|---|---|---|
| R3a on, speculative `p.[any].u` on | **FAIL** | pass |
| R3a **off**, speculative `p.[any].u` on | **FAIL** | pass |
| R3a on, speculative `p.[any].u` removed | **FAIL** | pass |
| R3a off, R3b off entirely | pass | **FAIL ×2** |
| **R3a off, R3b at this prefix only** | **pass** | **pass** |

The last row is what shipped. Two consequences:

**R3a ships off**, overturning design §7 R5's "always". The old code had exactly this guard, spelled
`!enumerateAnyFrontier` — emit the coarse edge only once the base has stopped enumerating. R1 does
not remove that argument, it makes it *unconditional*: there is no cap any more, so the enumeration
never stops, so the guard is never satisfied. R3c answers every covered demand precisely and R3b
answers the uncovered frontier; the coarse edge has nothing left to answer that they do not. It is
kept behind `TreeApManager.anyFrontierPremise` because the premise shape is still load-bearing
elsewhere (summaries keyed on an `[any]` premise, `splitDelta` stepping over one,
`AccessBasedStorage`'s `[any]`-keyed lookup) and because it is the arm to reach for if a workload
ever shows that the *enumeration*, rather than the materialisation, is what has to be bounded.

**R3b emits one edge, not two.** The design asked for both `p.u` and `p.[any].u`. The
`[any]`-carrying half is speculative — it names a mark one link below the `[any]` off demand
registered at `p` — and it is the same false-positive generator. It is still reachable, but only
where the engine has actually refined `p.[any]` itself, which lands demand on the `[any]` trie child
and is answered by the ordinary descent. Demand-driven, not speculative.

Row 4 of that table is also design §9.2's positive control, at unit scale: with R3b off, the suite
loses two `the unsanitized field reports` cases outright. A suite that cannot detect the known
failure is not validating anything, and this one can.

## 3. The result the design did not predict

`AnyUnrollGrowthPatternTest` passes **unchanged** — all five tests, including `the fixed point is
every non-repeating sequence over the demand set` (4 / 15 / 64 premises for demand sets of 2, 3, 4)
and `growth is superexponential in the size of the demand set`. The design listed both as tests that
"must be deliberately rewritten", on the reasoning that they pin the explosion and R1 exists to
invalidate them.

They did not need rewriting, and that is the single most important thing this change measured:

> **R1 removes the fact materialisation, not the premise enumeration.**

R3c hands out `p.a` for every demanded `a`, R4 descends into it, the caller refines `p.a`, R3c hands
out `p.a.b` — the same `Σ n!/(n−k)!` family the unroll produced, arrived at by reading instead of
copying. `AccessPath.limitFieldAccess` still collapses a repeated field, so `a.a` is still not
enumerated and the bound is still `N!` rather than infinity.

What is gone is the copy: `carrierPerRequest = 10.72` nodes per request, `nodesPerMaterialised =
5.91`, and 99.4% of those copies still owning an `[any]` of their own.

## 4. Conductor

Two replicates per arm. Volume counters span up to 5x across replicates of the same jar on this
workload (the interner race), so everything below is a range, and the structural ratios are what the
argument rests on.

| arm | rc | stopped by | fwd scan | events | events/s | `Total vulns` | SARIF |
|---|---|---|---|---|---|---|---|
| base-1 | 253 | low memory | 134.1 s | 906,715 | 6,761 | **2** | 2 |
| base-2 | 253 | low memory | 144.6 s | 900,096 | 6,225 | **2** | 2 |
| **new-1** | 253 | low memory | 190.2 s | **2,284,701** | **12,012** | **2** | 2 |
| **new-2** | 254 | the clock | 233.1 s | **2,334,753** | **10,016** | **2** | 2 |
| new + R3a on | 254 | the clock | 233.2 s | 2,276,357 | 9,761 | **2** | 2 |
| new-3 | 253 | low memory | 196.8 s | **2,343,977** | **11,910** | **2** | 2 |
| new + R3a on | 254 | the clock | 233.2 s | 2,276,357 | 9,761 | **2** | 2 |
| new, R3b off | 254 | the clock | 233.1 s | 2,313,405 | 9,925 | **0** | 0 |
| base @ 16 GB | 254 | the clock | 233.9 s | 980,043 | 4,190 | **2** | 2 |
| **new @ 16 GB** | 254 | the clock | 233.7 s | **2,775,222** | **11,875** | **2** | 2 |
| final jar, committed tree | 254 | the clock | 233.2 s | 2,337,936 | 10,025 | **2** | 2 |

- **Events to the stop: 2.5-2.6x at 8 GB, 2.8x at 16 GB.** 900k-907k -> 2.28M-2.34M; 980k -> 2.78M.
- **Throughput: 1.5-1.9x at 8 GB, 2.8x at 16 GB.** 6,225-6,761 -> 10,016-12,012 events/s; 4,190 ->
  11,875.
- **Findings unchanged.** `Total vulnerabilities: 2` in every arm that has R3b, baseline and new
  alike, and the SARIF count agrees because the trace phase still had time.
- **The failure mode moved.** Both baselines die of the low-memory stop at ~135-145 s. One new
  replicate does too, at 190 s; the other survives to the full 233 s forward-scan budget and dies of
  the clock. Memory is no longer reliably the binding constraint.
- Peak RSS is flat at 9.2-9.4 GB against `-Xmx8g`, which is what "the low-memory stop" means here --
  it is a soft-reference cliff, not a heap ceiling.
- **More heap now helps, which it did not before.** The baseline at 16 GB is *slower per event* than
  the same jar at 8 GB (4,190 vs 6,225-6,761 events/s) -- the throughput collapse
  ([[conductor-throughput-collapse]]: per-event cost grows, so more clock buys 12.5%). The new arm at
  16 GB holds its 8 GB throughput (11,875 vs 10,016-12,012) and converts the extra headroom into 19%
  more events. So the change does not only move the wall further out; it changes whether buying more
  memory is worth anything.

**The positive control fires.** `-Dopentaint.tifaNoUncoveredFrontier=true` -- R3b off -- reports
`Total vulnerabilities: 0`, losing both findings while running at the same speed. Design §9.2 asked
for exactly this: a suite that cannot detect the known failure is not validating anything, and this
one detects it at both scales (two red `unsanitized field reports` cases in the unit gate, both
conductor findings here).

**R3a costs nothing here and buys nothing here.** With the coarse edge on, conductor is within noise
on every volume counter and still reports 2 findings; the only measured difference is the cleaner
false positive in the gate. So the conductor numbers do not argue against shipping it off, and the
gate argues for it.

**Byte identity on the converging arm.** `rulesets/single-rule-nostar` finishes in 37.9 s with `rc 0`
on both jars, and `results.sarif` has the same sha256 `d14667c3c33b015f...` -- the one conductor
control that converges produces an identical report.

### The counters, and which way each moved

| counter | base (2 reps) | new (2 reps) | ratio |
|---|---|---|---|
| `J-trimMemo` calls, the `[any]` subsumption walk | 123.3M / 128.0M | **567k / 202k** | **217-634x fewer** |
| `B-getChildAny` calls, R4's synthesis | 140k / 148k | **25.1M / 34.1M** | 170-244x more |
| `C-concat` calls | 1.97M / 1.96M | 5.48M / 5.47M | 2.8x more (tracks events) |
| `C-concat` `growthPerCall` | 65.90 / 60.94 | **23.51 / 27.66** | **2.3-2.8x cheaper** |
| `C-concat` `resultNodes` | 185.8M / 172.9M | 157.8M / 177.9M | flat, on 2.5x the events |
| `E-delta` `remainderPerFact` | 0.42 / 0.41 | 0.52 / 0.51 | +24% |
| TIFA `[any]`-carrying arrivals | 6,207 / 5,833 | **409 / ~400** | 15x fewer |
| TIFA `[any]`-carrying incoming nodes | 20.5M / 14.0M | **11.5k / ~10k** | **~1,400-1,800x fewer** |
| `anyunroll tifaFacts` (facts the unroll materialised) | 322 / - | **0** | gone by construction |
| premises carrying an `[any]` (`emitsWithAnyInChain`) | 1,923 / 1,939 | **0** | R3a off |

### The premise census

`-Dopentaint.summaryPremiseDiag=true` on both jars, same everything else. This diagnostic costs
enough to change the run, so these two are a matched pair and are not comparable with the table
above.

| | base | new |
|---|---|---|
| summary premises | 48,799 | 112,621 |
| over methods | 14,696 | 14,696 |
| events reached | 735,536 | 2,284,397 |
| **premises per event** | **0.0663** | **0.0493** (-26%) |
| worst method | `WorkflowExecutorOps#decide`, 4,273 | `WorkflowExecutorOps#rerunWF`, 11,807 |
| of those, carrying an `[any]` | 36 | **0** |
| longest premise chain | 10 links | **7 links** |

Read the raw totals and you conclude the premise population **more than doubled**. Read them per unit
of work done and it fell by a quarter. Both are true and neither is the interesting number: premises
accumulate with work, the new arm did 3.1x the work in the same wall clock, and a premise store that
grows sublinearly in events is still a store that grows.

The two shape numbers are firmer than either total. The longest chain fell from 10 links to 7, and
the `[any]`-carrying premises went to zero -- so what replaced the unroll's output is a strictly
concrete, strictly shallower premise family.

Two predictions from the design's open list, settled:

- **§8.4 was right.** A coarser premise lands shallower and leaves a bigger remainder:
  `remainderPerFact` rose from 0.41-0.42 to 0.51-0.52. It cost less than feared -- `concat`'s
  `resultNodes` is flat on 2.5x the events, because the graft got cheaper per call faster than the
  remainder grew.
- **§8.5 was right about where to look, and the direction is the good one.** See §5.

## 5. Where the time went instead

The design's §8.5 named the thing to watch: *"Every emitted pair feeds the engine's hottest function.
`AccessTreeAnySuffixMatcher.getNonMatchingNode` runs on every merge of an `[any]`-carrying tree and
was 73.6% of analyser CPU before the memo landed. Watch it, not the premise store, for the
performance outcome."*

That is exactly where the win is, and it is not because the function got faster. It is because it
stops being called.

`getNonMatchingNode` is the `[any]` subsumption walk, and it runs on a merge only when the receiver
owns an `[any]`. The accumulator that owned them was `added`, and it owned them because the unroll
kept re-rooting an `[any]`-carrying carrier into it. With R1 that accumulator is almost `[any]`-free,
so the merge takes the cheap arm.

Two counters move in opposite directions, and the trade is the whole change:

| counter | what it is | direction |
|---|---|---|
| `J-trimMemo` calls (hits+misses) | the `[any]` subsumption walk | **collapses** |
| `B-getChildAny` calls | R4's synthesis, `peekChild`, nothing stored | **explodes** |

The second is the price of the first. Every R4 descent is a `getChild` on a node that holds nothing
literally under the accessor (`fromNothing` = 100% of calls), assembling a result from subtrees of
the receiver. It allocates and it is not free — but it is a read, it moves no budget, and it does not
feed the accumulator that made the merge expensive.


## 6. What this leaves

1. **The premise enumeration is untouched, and it is now the only thing left.** §3. `limitFieldAccess`
   still bounds a concrete chain at `N!` rather than at infinity, and with R3a off almost no premise
   carries an `[any]`, so the design's §8.1 worry -- that putting `[any]` into a majority of premises
   would remove the bound from a majority of chains -- did not materialise. It comes back the moment
   `anyFrontierPremise` is turned on, and there is still no replacement bound.
2. **Memory is still the binding constraint, but no longer reliably.** One new replicate dies of the
   low-memory stop at 190 s and the other reaches the full budget. Whether the remaining pressure is
   the premise population or the fact store is the next thing to separate; the 16 GB pair in §4 is
   the first cut at it.
3. **`anyUnrollLimit` no longer caps anything.** Its only engine caller was the unroll.
   `readChildPaidOnly` and `budgetExhausted` survive on `AnyUnrollManager` with their tests and no
   callers, and the property now decides only whether a `readChild` mint is `PAID` or `CREDIT`, i.e.
   whether the absorbing prepend may fire. The whole L-sweep of the previous investigations is a
   sweep over that, not over the abstraction.
4. **The two consumers keyed on premise shape, design §8.3, were not touched** --
   `MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:55` and `taint/Source.kt:44-58`. With
   R3a off, TIFA produces no `[any]` premises at all, so neither is reachable from this file any
   more; both become live again if `anyFrontierPremise` is turned on.
5. **The design's §9.1 order was not followed.** R3b's test was written after the change, not before.
   The failure it would have caught was caught anyway, by the gate rather than by the unit test.

## 7. Reproducing

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint-w3-benchmark-results/scoped-harness
./buildjar.sh tifanew                       # -> jars/tifanew-<sha16>.jar
FLAGS="-Dopentaint.anyUnrollLimit=100 -Dopentaint.anyUnrollKindPolicy=rescore \
       -Dopentaint.anyUnrollRescoreStrategy=bfs -Dopentaint.anyManagerDiag=true \
       -Dopentaint.apOpDiag=true -Dopentaint.tifaDiag=true"

./scoped-run.sh new-1 jars/tifanew-<sha>.jar $FLAGS                              # the arm
./scoped-run.sh ctl-1 jars/tifanew-<sha>.jar $FLAGS \
    -Dopentaint.tifaNoUncoveredFrontier=true                                     # must report 0
RULES=$PWD/rulesets/single-rule-nostar ./scoped-run.sh id-1 jars/... $FLAGS      # byte identity
./gate.sh tifa                                                                   # 3,485 tests
```

Read `Total vulnerabilities` in `analyzer.log` before the SARIF count: every non-converging arm can
lose traces to the clock, and a SARIF count read as a soundness signal has produced a false alarm on
this workload before.

Ablation controls, all default off and all unsound alone: `-Dopentaint.tifaAnyFrontierPremise`
(R3a on), `-Dopentaint.tifaNoUncoveredFrontier` (R3b off), `-Dopentaint.tifaNoSynthesised` (R3c off),
`-Dopentaint.tifaNoVirtualDescent` (R4 off), `-Dopentaint.tifaSingleRound` (one walk per call).
