# Sibling subsumption and the absorbing prepend: two answers

Two questions, both measured on the conductor single-entry-point / single-rule arm, frontier flags
(`anyUnrollLimit=100`, `rescore`, `bfs`), 8 GB, literal `[any]` matching.

---

## 1. Are there sibling paths an `[any]` can absorb?

**Yes — and not a few. Essentially all of them.**

Census over stored facts (`-Dopentaint.edgeCensus=true`, sampled 1 in 512, min size 50, identity-memoised,
visit-budgeted; matcher built with `forceCancelAbstract = true` so the number is the full residue
while the engine keeps its shipped semantics):

| | literal | literal + depth fix | old reader |
|---|---:|---:|---:|
| facts sampled | 723 | 111 | 2,714 |
| nodes owning an `[any]` | 39,944 | 1,770 | **0** |
| sibling branches at those nodes | 214,991 | 7,680 | 0 |
| sibling mass | 2,522,467 | 44,669 | 0 |
| **fully subsumed by the fact's own `[any]`** | **214,991 (100%)** | **7,680 (100%)** | – |
| … of which name-critical | **0** | **0** | – |
| partially subsumed / not subsumed | 0 / 0 | 0 / 0 | – |

The old-reader column is the control: it holds no `[any]`-owning nodes at all, matching its measured
402-of-1.51M `[any]` arrivals. The census is regime-dependent, not an artefact.

**Why it is 100%, and why that is not a bug.** Production facts carry `[any].*` — an **abstract**
subtree under the `[any]` — and `*` denotes every path at that position. So every sibling of such an
`[any]` is denotationally redundant, whatever it is. The concrete siblings add **no denotation at
all**; they exist only to carry NAMES.

Pinned by `SelfSubsumptionClassifierTest`, which also shows the classifier can say no:

- `[any].*` subsumes siblings `f.g.*` and `h.*` → nothing survives;
- `[any].g.*` does **not** subsume `h.*` → `h` survives;
- `[any].g.*` **does** subsume `f.g.*` → nothing survives. *This is the case from the question:
  `a.b.c` beside `a.[any].c`.*

Two semantics worth writing down, because both cost me a wrong test first: an "empty" result is
`manager.emptyNode`, whose `size` is **1**, not 0; and `*` (abstract, "any continuation") does **not**
imply `$` (final, "the path ends here"), so `[any].*` does not subsume a sibling ending in `$`.

### Why the engine never removes it

`trimAnyCoveredAndPushChildren` (`AccessTree.kt:2019`) is a **cross-trim between two merge
OPERANDS** — it matches one operand's `[any]` against the *other* operand's branches:

```kotlin
val aAnyIdx = aAccessorsUntrimmed.indexOf(ANY_ACCESSOR_IDX)
val bTrimmed = if (aAnyIdx >= 0) aNodesUntrimmed[aAnyIdx].suffixMatcher().getNonMatchingNode(b) else b
```

**Nothing in the engine ever trims a node's own sibling against its own `[any]`.** A node holding
`f.c` and `[any].c` at once is cleaned up only by accident, if some later merge partner happens to
carry an `[any]` at exactly that position. `bulkMergeAddAccessors` — the graft's assembly path — only
merges *same-accessor* pairs, so it cannot subsume either. Self-subsumption is not a heuristic that
is tuned too conservatively; it is an operator that does not exist.

### Can we improve the heuristic? Measured, and the answer is "not by folding alone"

`AccessTreeAnySuffixMatcher` already declines every branch containing an abstract node
(`TRIM_ABSTRACT`, default off). Turning that on, and a new `safe` variant restricted to branches
holding nothing an `[any]` can never denote (no mark, static, `[value]`, type-info — the O(1)
`containsNameCriticalInThisOrDeepNodes` bit added here and pinned by `NameCriticalFlagTest`):

| arm | rc | wall | events | vulns |
|---|---|---:|---:|---:|
| baseline (charge 1 + ceiling 9) | 0 | 48.7 s | 369,983 | **2** |
| `anyTrimAbstract=safe` | 0 | 43.6 s | 331,306 | 0 |
| `anyTrimAbstract=true` | 0 | 42.8 s | 346,670 | 0 |
| **`anyTrimAbstract=safe`, no depth fix** | **0 converged** | 42.6 s | 349,836 | 0 |

The last row is the striking one: **sibling subsumption alone converges the arm that otherwise dies
of memory at 138 s.** The redundancy is real and it is most of the cost. `J-trimCF keptFraction`
falls 1.00 → **0.29** and `wouldDropAll` 11 → 25,741; concat's `growthPerCall` falls 35.8 → 11.2.

And it still costs every finding — even restricted to branches with no name in them. `R3b` emissions
fall 2,828 → 850 and `walkStates` 578,498 → 324,350: the whole analysis shrinks, and the concrete
paths that carried the witness shrink with it.

**The reason is the one that governs everything here: premise emission is SYNTACTIC.** TIFA emits
premises by walking the fact's literal edges — R2 over literal children, R3b over the uncovered
accessors one level below an `[any]`. A denotationally exact fold removes edges, and an edge that
is not there cannot be named. The redundant siblings are redundant *as denotation* and load-bearing
*as syntax*. `AccessTreeAnySuffixMatcher`'s own KDoc names the second half of the cost: the fold
"removes the abstract nodes that are the graft points" `concatToLeafAbstractNodes` attaches to.

So the heuristic to improve is not the fold. **A fold can only be safe if the premise machinery
stops depending on the fact's shape** — i.e. if the names it needs are recorded somewhere the fold
does not touch. That is the design question this measurement opens.

---

## 2. The any-manager is on. Why doesn't the absorbing prepend help?

**Because it fires 9 times in 6,593,929.**

`-Dopentaint.anyManagerDiag=true`, literal arm, `L=100`:

```
prepend=[absorbExact:9, absorbStay:0, writtenPaid:6593920, writtenMismatch:57,
         guardBlocked:0, uncovered:0, element:0, graft:0, chainFold:0]
```

`writesAbove` (`AnyUnroll.kt:1464`) returns **true — meaning WRITE, do not absorb — for `ORIGIN` and
`PAID` states**. Only a `CREDIT` state absorbs, and `readChild` stamps `CREDIT` only once the pot has
crossed `L`. At `L=100` it essentially never does: `refused=0`, `maxPotRefusals=0`, and the DAG
census shows `crossedLimit=1` of 298 live pots, with 278 of them below a total of 2. The absorbing
prepend is a **budget-exhaustion fallback**, not a normalisation rule, and the budget is never
exhausted.

### Forcing it does not help either

`L=0` starts every pot spent, so absorption always fires:

| arm | absorbStay | writtenMismatch | graft | rc | wall | events | vulns |
|---|---:|---:|---:|---|---:|---:|---:|
| `L=100`, literal | 0 | 57 | 0 | 253 low-mem | 135 s | 680k | 2 |
| `L=0`, literal | **2,644,423** | 4,529,154 | 2,526,886 | 253 low-mem | 124 s | 668k | **0** |
| `L=0`, + depth fix | 132,998 | 151,158 | 78,523 | 0 | 47 s | 384k | **0** |

2.64M absorptions, and the run still dies at 124 s having done *fewer* events. **Absorption is not
the size lever**, and it costs every finding. Even with the budget forced open, 63% of prepends still
cannot absorb: `writtenMismatch` is the automaton refusing an accessor the `[any]` never sold, and
`graft` is the graft context declining. The independently measured ceiling on opening the kind gate
is **+14.5%**, because 78.5% of declines would absorb into a self-loop and rewrite nothing.

### And it is structurally the wrong shape for this problem

- **It is adjacency-only.** `absorbTargetFor` (`AccessTree.kt:1769`) begins `node.anyId ?: return null`,
  and the node invariant makes that "the `[any]` edge is *directly* below the accessor being written".
  Given `a.b.[any].X`, writing `a` above `b.[any].X` sees no `anyId` and returns null — **with no
  counter**, so it is invisible in the dump. This is the dominant structural exclusion.
- **No rule absorbs a concrete PREFIX of an existing fact.** There is no rewrite of `a.b.[any].X` into
  `[any].X` anywhere; the complete inventory is `absorbCoveredByAnyPrefix`, `absorbBeyondAnyEntries`,
  `absorbTargetFor`. The prepend rule can only eat an accessor *at the instant it is written onto* an
  `[any]`-rooted node. Once the fact exists, nothing walks it and hoists the prefix.
- **The suffix direction is free and unconditional.** `absorbCoveredByAnyPrefix` does
  `[any].x.y.![m] → [any].![m]` with no manager, no budget, no counter — but only at the graft point,
  and only to the delta, never to the receiver's own stored structure. It fires 60 times in 29M graft
  points.

So the asymmetry is: `[any].a.b → [any]` is free; `a.b.[any] → [any]` needs adjacency plus a manager
transition and is refused ~82% of the time; and **the redundancy that actually dominates is neither
of those — it is sibling breadth**, which no absorption rule addresses at all.

### One more thing the counters hide

`anyUnrollLimit` no longer caps anything. Since the never-unroll commit removed the only callers of
`readChildPaidOnly` and `budgetExhausted`, `L` survives purely as a stamp threshold deciding `PAID`
vs `CREDIT` for this prepend. Counters that now read zero for structural rather than empirical
reasons: `readsRefused`, `maxPotRefusals`, `paidMintsFromUnroll`, `tifaUnrolledFacts`,
`tifaAbsorbSuppressed`.

---

## 3. What this adds up to

The fact is a product over collection-model accessors (`2026-08-27-literal-any-fact-explosion-anatomy.md`).
Under literal matching almost every node in that product also owns an `[any].*`, which denotes the
entire product beneath it. **The engine is therefore storing, merging, grafting and re-propagating a
structure that is 100% denotationally redundant against a sibling it already holds** — and it does so
because its premise emission reads syntax, not denotation.

That is why every fold measured here converges the run and loses the findings, and why the absorbing
prepend — which addresses prefixes, adjacently, on a budget that never runs out — cannot touch it.

**The open design question, stated precisely:** can the names R2/R3b need be recorded independently of
the fact's edges? If yes, sibling subsumption becomes available and it is worth roughly the whole
explosion (138 s memory death → 42.6 s convergence). If no, the redundancy is structural and the only
levers left are the depth gate (measured, converges with findings) and bounding breadth directly.

---

## 4. Instrumentation added

- `EdgeStoreDiagnostics.runSelfSubsumptionCensus` — sampled 1/512, `size ≥ 50`, identity-memoised,
  20k visit budget with an explicit `truncated` count. Reports `edgeStore selfSubsume …`.
  Builds a **fresh local matcher** per point rather than the cached `anySuffixMatcher`, whose
  unsynchronised identity memos are shared across worker threads.
- `AccessTreeAnySuffixMatcher(suffixNode, forceCancelAbstract)` — census-only; lets a diagnostic
  measure the full residue while the engine runs its shipped semantics. Never set by engine code.
- `AccessNode.containsNameCriticalInThisOrDeepNodes` — O(1) flag bit, "this subtree holds a mark,
  static, `[value]` or type-info". Pinned by `NameCriticalFlagTest`.
- `-Dopentaint.anyTrimAbstract=safe` — the abstract cancellation restricted to non-name-critical
  branches. Measured above; ships off.

Gate 3497/2, both pre-existing.
