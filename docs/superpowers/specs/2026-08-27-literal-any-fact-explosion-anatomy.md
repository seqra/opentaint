# Why there are still so many facts, under literal `[any]` matching

> **The answer in one paragraph.** Premises fell 7.3x, to 42,267. Facts did not: a fact is a set of
> accessor paths and its size is a **product along the path**, over an alphabet that includes the
> collection model's `Element` / `MapKey` / `MapValue` / `Key` / `Value` / `entries` as well as the
> object's fields. Nothing bounds that product. Breadth has no bound anywhere in the backend;
> `Element` is not a field so the no-repeated-field rule does not touch it and the element cap only
> forbids *consecutive* runs; the one contracting operator refuses any branch containing an abstract
> node, which is exactly the dominant `[any].*` leaf shape; the graft bypasses that operator
> entirely; and the edge store re-propagates the **whole merged tree** on every growth. The only
> bound that ever binds is the fact-depth gate — and it is a scheduling artefact that raises itself
> whenever a unit goes idle. `[any]` is charged **10** depth units against a budget that starts at
> **3**, so under literal matching every `[any]` fact is parked, the unit starves, and the gate
> ratchets to **76**, admitting a generation of far larger facts each time. Correcting that charge
> and capping the ratchet converges conductor in **~49 s with both findings**, in 5 of 6 replicates.

Type vacuity is not in this list on purpose. The type filter can *reject* a step in the product; it
cannot create one. It is a mitigation, and `2026-08-26-frontier-fact-explosion-anatomy.md` measured
how much it mitigates. This document is about what manufactures the product.

---

## 1. What was measured

Conductor, single entry point (`WorkflowResource#rerun`), single rule, 8 GB, 300 s IFDS budget,
frontier flags (`anyUnrollLimit=100`, `rescore`, `bfs`), `foreign_overlap 0%` on every run. One jar
per arm-set; the arms differ only by `-D` flags. Instrumentation: `EdgeStoreDiagnostics`
(`edgeCensus`), `TifaDiagnostics` (`tifaDiag`), `ApOpDiagnostics` (`apOpDiag`), plus two counters and
two flags added for this investigation (§7).

---

## 2. Premises: 309,324 → 42,267

| | old reader | literal |
|---|---:|---:|
| **premises emitted (TIFA `emits`)** | **309,324** | **42,267** |
| TIFA `walkStates` | 48,365,169 | 564,608 |
| R4 virtual descents | 24,984,408 | 7,990 |
| R3c premises (counted at the suppression point) | 26,210 | 215,078 |

**7.3x fewer premises and 86x less TIFA work.** The design did what it claimed. R3c's suppressed
count is the ladder that no longer runs: 215,078 concrete premises that would have been handed out.

---

## 3. Facts: fewer, much bigger, and re-propagated whole

| | old reader | literal | literal + §6 fix |
|---|---:|---:|---:|
| slots opened | 1,957,570 | 419,497 | 296,312 |
| store mass (path-multiplicity) | 72,933,777 | 43,079,259 | 3,865,218 |
| **mass per slot** | **37.3** | **102.7** | **13.0** |
| largest single slot | 2,897 | **17,377** | 1,736 |
| propagated mass | 202,886,555 | **435,366,412** | 16,382,046 |
| **propagated per growth** | **49.67** | **330.54** | **19.57** |
| root breadth mean / max | 1.57 / 27 | 2.22 / 55 | 1.47 / 44 |
| depth-gate max | 9 | **76** | 9 |
| gate raises | 571 | **9,198** | 800 |
| edges still parked at the stop | 82,891 | **0** | 10 |

**The population inverted.** The old reader holds ~2M small slots; literal matching holds 4.7x fewer
slots that are 2.8x larger, with the largest 6x larger — and it propagates **2.1x more total mass in
3.3x fewer operations**. `propagatedPerGrowth` 49.67 → 330.54 is the single number that explains the
memory death.

---

## 4. Where the nodes are manufactured

`concat` — the summary graft — is where nodes physically land.

| | old reader | literal |
|---|---:|---:|
| concat calls | 5,705,141 | 999,854 |
| **graft points per call** | 2.49 | **11.02** |
| most graft points in one call | 245 | **1,765** |
| graft points that re-visit a node already grafted this call | 47.05% | **81.40%** |
| delta nodes offered per call | 21.1 | **68.9** |
| **nodes created per call** | **21.65** | **88.59** |
| `filterStartsWith` in → out | 16.7M → 7.1M, grew 16,258 | 82.8M → 1.29M, **grew 0** |

Two things to read here. First, `filterStartsWith` **can no longer grow** (`grew=0`, against 16,258
before) — the literal rule closed that channel exactly as designed. Second, everything moved into
`concat`: each call now offers a **3.3x bigger delta** and grafts it at **4.4x more points**, 81% of
which are re-visits. That is because the coarsest available premise is now `p.[any]`, and
`delta(F, p.[any])` hands back *the entire subtree under the `[any]` edge* as the remainder.

**Caveat, load-bearing.** `AccessNode.size` counts paths, not distinct nodes — a shared subtree is
counted once per path. The sampler gives both: `distinctGrowthPerSample = 20.46` against
`sizeGrowthPerSample = 89.69`, a factor of **4.4**. So the honest manufacturing rate is ~20 distinct
nodes per concat call, ~20M distinct nodes over the run. Every "mass" figure above is a path mass and
should be divided by roughly this factor to get object counts.

---

## 5. The product, read off a real delta

A sampled graft, verbatim — a 466-node delta onto a 116-node receiver, producing **8,149** nodes:

```
.Element.MapKey.[any]                            .Element.inputData.[any]
.Element.MapKey.Element.[any]                    .Element.inputData.MapKey.[any]
.Element.Element.Value.[any]                     .Element.inputData.MapKey.Element.[any]
.Element.Element.Value.name.[any]                .Element.inputData.entries.[any]
.Element.Element.Key.[any]                       .Element.outputData.entries.Element.Value.[any]
.Element.outputData.entries.Value.[any]          .Element.outputData.entries.Element.Key.[any]
.Element.outputData.entries.Key.[any]            .Element.outputData.entries.name.[any]
```

Accessor frequency across the samples: `Element` 44, `[any]` 28, `entries` 12, `outputData` 10,
`Value` 8, `MapKey` 8, `inputData` 8, `Key` 6, `name` 4.

This is a **free product** over the collection model applied to conductor's `TaskModel.inputData` /
`outputData`, which are `Map<String, Object>`. Every branch terminates in `.[any].*`.

**Why nothing stops it:**

- `ElementAccessor` is a `data object` (`Accessors.kt:125`), **not** a `FieldAccessor`. So
  `limitFieldAccess` — the no-repeated-field-on-a-path rule, and the only reason the premise space
  was ever `Σ N!/(N−k)!` rather than infinite — **does not apply to it**. `Element` recurs freely:
  `.Element.MapKey.Element`, `.Element.inputData.MapKey.Element`.
- `limitElementAccess` caps only **consecutive** element runs, at 2
  (`SUBSEQUENT_ARRAY_ELEMENTS_LIMIT`). `.Element.X.Element` is not consecutive and is not capped.
- The field-like model accessors (`MapKey`, `Value`, `entries`, `inputData`, …) each appear at most
  once per path, which is `limitFieldAccess` working correctly — and it is the *only* thing working.

So the path language is roughly `Element^{≤2} ( f_i Element^{≤2} )*` over distinct field-like
accessors `f_i`, and the fact is its prefix-closure. Root breadth of 2.2 compounded over ~12
effective levels is the 17,377-node slot.

---

## 6. The one bound that binds, and why it stopped binding

`MethodAnalyzer.factDepthLimit` starts at `INITIAL_ALLOWED_FACT_DEPTH = 3`. `edgeExceedLimit` parks
an entry edge above it — it never shrinks anything — and `TaintAnalysisUnitRunner.resumeDelayedAnalyzers`
does `++factLimit` **with no ceiling**, fired when the unit would otherwise go idle.

And `ANY_ACCESSOR_DEPTH_CHARGE = 10` (`AccessTree.kt`): a node owning an `[any]` edge adds **10** to
`maxDepth`. It was calibrated when `[any]` was rare and got unrolled away.

Under literal matching `[any]` is the dominant fact shape, so:

1. every `[any]`-carrying fact exceeds the depth gate immediately (11 > 3 + 2) and is parked;
2. the unit starves, `DelayedAnalysisResume` fires, the limit goes up by one;
3. each raise admits facts with one more tenth of an `[any]` level; the gate has become an
   `[any]`-nesting counter;
4. 9,198 raises later the limit is 76 — about seven nested `[any]` levels — and the product in §5 has
   room to run over all of them.

**Measured, one variable at a time** (`-Dopentaint.factDepthCeiling`, `-Dopentaint.anyDepthCharge`):

| arm | rc | wall | events | vulns | SARIF |
|---|---|---:|---:|---:|---:|
| literal, as shipped | 253 low-memory | 138.0 s | 670,745 | 2 | 1 |
| literal + ceiling 9 | **0 converged** | 35.7 s | 161,317 | **0** | 0 |
| literal + charge 1 | 253 low-memory | 151.9 s | 698,425 | 2 | 1 |
| **literal + charge 1 + ceiling 9** | **0 converged** | **49.6 s** | 368,239 | **2** | **2** |
| literal + charge 1 + ceiling 5 | 0 converged | 36.9 s | 206,429 | 0 | 0 |
| old reader + charge 1 + ceiling 9 | 253 low-memory | 93.4 s | 1,073,889 | 0 | 0 |
| old reader, as shipped | 254 timeout | 269.2 s | 2,332,148 | 2 | 2 |
| old reader + ceiling 9 | 254 timeout | 269.8 s | 2,365,112 | 2 | 2 |

Both knobs are necessary and neither is sufficient. The ceiling alone loses the findings, because at
charge 10 a depth of 9 admits **one** `[any]` edge and the witness needs more. The charge alone still
dies, because nothing stops the ratchet. Together the gate measures actual structure again, 9 is
enough to express the witness, and the run converges. The last row is the control that the ceiling
flag is inert when it does not bind: the old reader never exceeded 9 anyway, and is unchanged.

**Replication, and an honest caveat.** Six runs of `charge 1 + ceiling 9`: converged every time
(rc=0, 44–79 s, 368k–536k events), **2 vulnerabilities and 2 SARIF traces in 5 of 6**; one run
derived 0. `Filter out … without traces` never fired, so the outlier genuinely failed to derive them
rather than losing a trace. This is the signature of the pre-existing interner data race
(`interner-data-race.md`, fixed on `saloed/8-interner-race`, present here). **Do not treat this
configuration as a result until that race is excluded** — but it is the first time this workload has
converged *with* its findings in this entire line of work.

---

## 7. The complete list of reasons a fact can grow, and what bounds each

| mechanism | bound |
|---|---|
| breadth (children per node) | **none.** `accessorCount()` is compared against no threshold anywhere; `TifaDiagnostics.kt:73` says so in the source |
| repeated field on a path | `limitFieldAccess` — real, but hoists occurrences **to the root**, increasing root breadth |
| repeated `Element` | only if **consecutive**, cap 2. Non-consecutive recurrence is unbounded |
| `[any]` subsumption (`f.* ⊆ [any].*`) | `AccessTreeAnySuffixMatcher` — refuses any branch containing an abstract node (`TRIM_ABSTRACT` default false), i.e. exactly the dominant shape. `J-abstractHole keptForAbstract = 160,661` |
| the same, at TIFA's accumulator | switched off: `foldToAny = false`, deliberately, because R2/R3b need the concrete *names* |
| the same, at the graft | **bypassed**: `bulkMergeAddAccessors` writes new accessors verbatim with no suffix-matcher pass |
| whole-tree re-propagation | none. The edge store returns the merged whole; summaries and subscriptions return deltas |
| premise-trie subsumption | **none.** `p.[any]` does not retire `p.a.b`; lookup activates every prefix, so one fact fires several slots, each re-propagating its own tree |
| depth | `factDepthLimit`, raised without ceiling whenever a unit idles — §6 |
| type feasibility | the type filter. A **mitigation**, vacuous past `java.lang.Object`; see the 2026-08-26 anatomy |

Turning the one dead contraction on (`-Dopentaint.anyTrimAbstract=true`) converges in 43.7 s and
reports **0 findings**: folding `f.![m]` into `[any].*` preserves the denotation and destroys the
*naming* R3b exists for. Same shape as the type ablation — the steps carrying the volume carry the
signal.

---

## 8. Instrumentation added here

- `EdgeStoreDiagnostics.recordRootBreadth` — O(1) at slot-open and merge; `rootBreadth mean/max/buckets`.
  The root is the right place to watch width because `limitFieldAccess` hoists there.
- `-Dopentaint.factDepthCeiling=N` — caps the idle-driven ratchet. Diagnostic.
- `-Dopentaint.anyDepthCharge=N` — makes `ANY_ACCESSOR_DEPTH_CHARGE` tunable (default 10, unchanged).

Known blind spots in the existing census, found while doing this and worth fixing before the numbers
are used again: `storeMass` omits the ND lane entirely, so `propagatedPerStored` is an upper bound;
an exclusion-only re-propagation is booked as a `growth` although the store did not grow;
`SIDE_EFFECT_REQ` can never be observed because `handleInputFactChange` re-tags to `INPUT_REFINE`
first; and zero-to-zero summary application is untagged and lands in `OTHER`.

---

## 9. What this closes and opens

**Closes.** "How many premises now" — 42,267, down 7.3x. "Is the premise set still the problem" —
no; TIFA is 86x cheaper and `filterStartsWith` can no longer grow at all. The remaining explosion is
entirely on the fact side.

**Opens, in the order the evidence ranks them.**

1. **The depth gate is the whole throttle, and it is an accident.** Give it a real ceiling and charge
   `[any]` honestly (§6). This is the only lever measured to converge conductor with findings intact.
2. **Bound breadth.** There is no bound at all today. The product in §5 is the population.
3. **Stop re-propagating the merged whole.** The edge store is the only family that does; the
   summary and subscription storages already hand out deltas. `propagatedPerGrowth` is 330.
4. **`Element` escapes every path rule.** Either make the element cap non-consecutive, or give the
   collection model a repeat rule of its own.
5. **The interner race** makes every one of these numbers non-deterministic, and made one replicate
   of the converged configuration report zero findings. Land `saloed/8-interner-race` first.
