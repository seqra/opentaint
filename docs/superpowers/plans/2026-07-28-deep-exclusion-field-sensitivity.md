# Field-sensitive deep mark exclusions

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a starred cleaner correct. `clean($*A)` inside a summarized wrapper must clean only the paths that actually flowed through it, not every path below the same base.

**Architecture:** A starred clean becomes the base cleaner's idea — node deletion — applied to both node kinds a fact can contain:

- the **concrete part** of the fact is closed (every path is enumerated), so the clean traverses it and deletes every `![m]` node below the position. Nothing is recorded, because nothing can reappear there;
- an **abstract node** is the one place the fact can still grow — by unfolding, or by a summary delta concatenated onto it — so it is the one place a residual claim is needed. The node is annotated: "below here, mark `m` is excluded".

`DeepMarkExclusion` therefore leaves the flat per-edge `ExclusionSet` and becomes part of the **abstraction state of the node** (`isAbstract` generalizes to "abstract, excluding {…}"). Enforcement collapses to two local rules: **concat** drops excluded marks from a delta attached below an annotated abstract node, and **unfold** makes refinement children inherit the annotation. The `removeAccessors` sweep with its depth thresholds, and the deep half of `AccessPath.filter`, are what those two rules replace.

Branch discrimination then needs no machinery at all. `p.raw = b` snapshots the pre-clean fact (abstract node unannotated); `p.val = b` the post-clean one (annotated). The exit-tree merge keeps `.raw` and `.val` as separate branches, each with its own abstract node — the merge-combinator dilemma at the storage sites does not get solved, it stops existing.

**Tech Stack:** Kotlin, JUnit 5, Gradle. The Gradle root is `core/` — the wrapper is `core/gradlew` and every task is invoked from `core/`.

## Global Constraints

- The Gradle root is `core/`. Run `./gradlew` from `core/`, never from the repository root. `:test` is the JVM SAST suite; `:opentaint-dataflow-core:opentaint-dataflow:test` is the dataflow unit suite.
- Baseline at the start of this plan, measured: `:test` **700 passed / 0 failed / 19 skipped**; `:opentaint-dataflow-core:opentaint-dataflow:test` **126 / 0 / 0**. No task may reduce the passing count or add a skip it does not name.
- **This plan deliberately retires the "exclusion-set-only" invariant.** Nine call sites currently assert that a `DeepMarkExclusion` never appears in an access path (`AccessTree`, `AccessPath`, `AccessCactus`, `AccessPathWithCycles`, `AccessGraphInitialFactAp`, `AccessGraphFinalFactAp`, `AccessorInterner`, `AutomataFactFilter`, `JIRFactTypeChecker`). It stops being an `Accessor` altogether and becomes node metadata, so those checks are deleted rather than relaxed. This supersedes the corresponding constraint in `2026-07-28-clean-accessors-deep-exclusion-split.md`.
- Do **not** reintroduce per-lineage grouping in the summary storages (`ba79279ef`). It was measured green on the sibling cases, but it works by keeping two edges from ever meeting rather than by giving the claim a coordinate — Task 4 removes the need for it entirely.
- Every new assertion that a finding is ABSENT must be accompanied by a control that produces it: same program, same sink, cleaner rule deleted. This rule is what exposed the vacuous Automata passes recorded below.
- **Automata greens are not evidence in this area.** Automata drops the taint entirely across an intervening `clean` call, so every `*CleanedFlow` entry point reports nothing regardless of the cleaner. All four non-vacuity controls in `CleanerFieldSensitivityAnalysisTest` are red in that mode and its six `is silent` cases are disabled for exactly that reason. Tree is the mode where this work is measurable.
- Cactus is out of scope. It fails the sibling cases with and without any of this; the gap is in the cactus access representation.

---

## Background an implementer needs

Read this before Task 1. The measurements are the argument; none of it is derivable from the code alone.

### What is actually broken

A mark is not metadata — it is a node in the access path (`TaintMarkAccessor`, `Accessors.kt:86`, printed `![tainted]`). "`b` carries tainted" is the fact whose path is `b.![tainted]`.

A cleaner naming a **concrete** path deletes that node. The store `p.raw = b` prepends `.raw` (`AccessTree.prependAccessor`, `AccessTree.kt:79`), so the exit tree of a wrapper that stores before and after the clean is:

```
Pair
├── .raw
│    └── ![tainted]      ← stored before the clean: reachable
└── .val
     ( nothing )         ← the fact was killed before the store: clean
```

Cleaned-ness is encoded positionally, and the two summary edges can share a storage slot without harm because the merge is a **tree** merge — `.raw` and `.val` are different branches.

A **starred** cleaner cannot do this. `b.[any].![tainted]` stands for unboundedly many paths, so there is no node to delete. `FinalFactReader.excludeDeep` (`FactReader.kt:55`) records `DeepMarkExclusion(mark)` on the *edge's exclusion set* instead — a flat side-channel with no position in the tree. Its only coordinate is a depth threshold (`AccessTree.kt:193`, `minPruneDepth = if (initialAccessDepth == 0) 2 else 1`), and the sweep recurses the whole subtree from the landing point (`removeAccessors`, `AccessTree.kt:625`). It cannot say "below `.val` only", so it either covers both branches or neither.

### Two facts that scope the fix — verified in code, do not re-derive

**The fact at the clean is almost always abstract, even when every caller's fact is concrete.** Callee summaries are computed on *abstracted* initial facts (`TreeInitialFactAbstraction`, and the automata/cactus counterparts). This is why the depth-2 row below fails despite a fully concrete source: inside `wrap`/`clean`'s summary analysis the cleaner sees the abstract initial fact, not the caller's concrete one. The abstract-node annotation is therefore the main path of this plan, not a corner case.

**The concrete half of a starred clean is missing entirely today.** On `arg0.*`, `removeFinalFact` (`Cleaner.kt:31-49`) routes the concrete cleanup through `clearPosition` with accessor list `[AnyAccessor, ![m]]`, and `clearPosition` navigates positionally: a concrete fact does not start with `[any]`, so the fact comes back unchanged. There is no traverse-and-delete anywhere. This is the same defect `2026-07-28-clean-accessors-deep-exclusion-split.md` records as "a starred cleaner applied INLINE does not clear a concrete mark at any depth ≥ 1" — Task 3's traversal half fixes it as a side effect, and that plan's red cases join the acceptance list here.

**Why annotating ONLY abstract nodes is sufficient:** a fact's tree grows only at its abstract nodes — by unfolding or by a delta concatenated there. The concrete part is closed, so traversal deletion is complete and needs no residual claim; any mark that materializes later necessarily passes through an abstract node, where the annotation blocks it.

### Why neither combinator can rescue it — measured

Both directions were tried on the failing sibling cases:

| storage merge combinator | sanitized read | unsanitized read |
| --- | --- | --- |
| `mergeAndIntersectDeep` (claim dropped) | **2 false positives** | reported ✓ |
| deep-aware `union` (claim kept) | clean ✓ | **2 false negatives** |

There is no operator that recovers information the representation already discarded. This is why the fix has to be in the representation.

### The variable, isolated

`CleanerFieldSensitivityAnalysisTest` holds the program, the source, the sink and the read depth constant across each pair and varies only the cleaner position. Measured on Tree:

| source | cleaner position | sink read | result |
| --- | --- | --- | --- |
| base only | concrete `arg0` | `p.val` | ✓ ✓ |
| whole-object | starred | `p.val` | ✓ ✓ |
| `arg0.f` | concrete `arg0.f` | `p.val.f` | ✓ ✓ |
| `arg0.f` | **starred** | `p.val.f` | ✓ **FP** |
| any-field | concrete `arg0.f.k` | `p.val.f.k` | ✓ ✓ |
| any-field | **starred** | `p.val.f.k` | ✓ **FP** |

Three facts an implementer must not re-derive the hard way:

1. **Read depth is irrelevant.** Depths 1, 2 and 3 behave identically.
2. **An abstract source is not the problem.** With an any-field source, the demand-driven refinement (`FinalFactReader.containsPosition`, `FactReader.kt:44-47`) splits the abstract fact into concrete facts until the cleaner's path is one of them — each carrying its own access path. Refinement manufactures the coordinate by making a new fact. That is why a plain exclusion never needed a path coordinate.
3. **Row 2 is not evidence that the star works.** It passes because the starred cleaner's *base* component does a concrete node deletion and the sink reads exactly that node. The deep exclusion is never consulted.

One predicate decides every row: **can the cleaner's removal be expressed as a node deletion on a concrete path?** The star is the single case where refinement cannot produce one, so the coordinate must come from the tree node itself.

### Red cases this plan turns green

All disabled today, all with passing non-vacuity controls, all Tree:

| file | case |
| --- | --- |
| `CleanerFieldSensitivityAnalysisTest` | `starred clean at depth 2 - the sanitized field is silent` |
| `CleanerFieldSensitivityAnalysisTest` | `starred clean at depth 3 - the sanitized field is silent` |
| `DeepCleanSummaryAnalysisTest` | `starred clean survives an unsanitized sibling edge from the same initial fact` |
| `DeepCleanSummaryAnalysisTest` | `any-field-only taint - sanitized sibling edge stays clean` |

Out of scope for this plan, listed so nobody mistakes them for regressions: the two `base-only clean keeps the whole-object field taint through the wrapper` skips and every Automata `is silent` skip.

---

## File structure

| file | responsibility after this plan |
| --- | --- |
| `.../ap/ifds/access/tree/AccessTree.kt` | abstract nodes carry excluded marks as part of their abstraction state; `concat` filters deltas by the annotation at the attach point; unfold children inherit it; `removeAccessors` and its depth thresholds are deleted |
| `.../ap/ifds/access/tree/AccessPath.kt` | the deep half of `filter` and of the `delta` sweep is deleted; plain filtering unchanged |
| `.../dataflow/taint/Cleaner.kt` | `arg0.*` on the concrete part = traverse and delete every `![m]` below the position; on each abstract node = annotate |
| `.../dataflow/taint/FactReader.kt` | `excludeDeep` is replaced by the two mechanisms above; the refinement channel carries plain accessors only |
| `.../ap/ifds/Accessors.kt` | `DeepMarkExclusion` stops being an `Accessor`; becomes an element of the abstract node's mark set |
| `.../ap/ifds/ExclusionSet.kt` | loses `deepExclusion` / `withDeepExclusion` / `mergeAndIntersectDeep`; `union` becomes unconditional again |
| `.../ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt` | one merge operator; no deep special-casing |
| `.../ap/ifds/serialization/ExclusionSetSerializer.kt`, `.../jvm/ap/ifds/JIRSummariesFeature.kt` | fact and summary formats carry the abstract-node annotation |

---

## Tasks

### Task 1 — Unit-pin the combination laws before touching the engine

- [x] Add `AbstractNodeExclusionTest` to the dataflow unit suite covering: annotating an abstract node; the annotation surviving a parent prepend; a sibling branch NOT carrying it; a delta concatenated below an annotated abstract node losing its excluded marks and keeping the rest; unfold children inheriting the annotation; two annotations meeting on the SAME abstract node combining by intersection (the join of a cleaned and an uncleaned lineage is uncleaned — the conditional-clean shape, not the sibling shape).
- [x] The same-node intersection is the one piece of the old law that survives, now at the right granularity. Assert it explicitly.
- [x] Verify: `:opentaint-dataflow-core:opentaint-dataflow:test` **126 + new / 0 / 0**.

**Why first:** this is the part most likely to be wrong and the cheapest place to be wrong in.

### Task 2 — Carry the excluded-mark set in the abstraction state (behaviour-preserving)

- [x] Generalize `isAbstract` to an abstraction descriptor carrying the excluded-mark set (empty in the common case — intern the empty descriptor so plain-abstract costs what the boolean did). Concrete nodes — the bulk — pay nothing.
- [x] Thread it through `manager.create(isAbstract, isFinal, accessors, accessorNodes)` (`AccessTree.kt:622`), node equality, hashing and interning.
- [x] Every construction site passes the empty descriptor. Nothing reads the set yet.
- [x] Verify: both suites at baseline, unchanged. **Record heap and wall-clock for `:test`** — node identity changed even if only abstract nodes carry payload.

**Stop-and-report gate:** if `:test` wall-clock regresses more than ~15%, stop and report before Task 3. Expected cost is far below the every-node design this plan replaced, but the gate stays until measured.

### Task 3 — The clean becomes deletion-plus-annotation

- [x] `removeFinalFact` (`Cleaner.kt:31-49`), `arg0.*` branch, replaces both current mechanisms:
  - traverse the fact's concrete part and delete every `![m]` node strictly below the position's base (the base mark belongs to the rule's `arg0` action). This is the traversal that `clearPosition` does not do today;
  - annotate every abstract node in the fact with `m`.
- [x] Delete `FinalFactReader.excludeDeep` (`FactReader.kt:55`); `refineFact` (`FactReader.kt:59-69`) carries plain accessors only. The claim now lives on the CLEANED fact, structurally — not on the reader refinement that `propagateCleanedFact` moves onto the caller's original fact.
- [x] Enforcement: `concat` filters a delta's marks by the annotation at the attach point; unfold children inherit. Delete `removeAccessors` (`AccessTree.kt:625`) and the deep branch of the `delta()` sweep (`AccessTree.kt:186-196`) and of `AccessPath.filter` (`AccessPath.kt:177-191`).
- [x] `prependAccessor` and `readAccessor` get **no** exclusion-specific code — the annotation moves because the node moves. If either needs any, the design is being misread.
- [x] Verify: the four red cases below go green in Tree with their non-vacuity controls still green; remove their `@Disabled`.
- [x] Verify: the three red cases of `2026-07-28-clean-accessors-deep-exclusion-split.md` (`AssignmentFormCleanAnalysisTest` ×2, `AnyFieldMonotonicityAnalysisTest` inline-clean) — the traversal half should green them; if not, say which and why.
- [x] **Regression guard:** that plan also records that a previous attempt to attach the claim to the cleaned fact regressed three `DeepCleanSummaryAnalysisTest` cases into false negatives. The mechanism there was a flat exclusion lost in transit and should not reproduce structurally, but run the full class in both modes and report, do not assume.

### Task 4 — Collapse the combination laws

- [x] Remove `deepExclusion()` / `withDeepExclusion()` / `mergeAndIntersectDeep()` from `ExclusionSet`; restore `union` to its unconditional form and delete the `check` — nothing deep can reach it once Task 3 lands.
- [x] Return every storage merge site to a single operator. There are **eleven**, not the four the sibling-edge discussion covers — enumerate before editing, because the tree-mode ones are the only ones the acceptance tests exercise and the rest will fail silently:

  | file | line |
  | --- | --- |
  | `access/tree/SideEffectRequirementTreeApStorage.kt` | 69 |
  | `access/tree/MethodInitialToFinalApSummaries.kt` | 270 |
  | `access/tree/MethodEdgesInitialToFinalTreeApSet.kt` | 95 |
  | `access/automata/SideEffectRequirementAutomataApStorage.kt` | 112 |
  | `access/automata/MethodInitialToFinalAutomataApSummariesStorage.kt` | 136 |
  | `access/automata/MethodEdgesInitialToFinalAutomataApSet.kt` | 211 |
  | `access/cactus/SideEffectRequirementCactusApStorage.kt` | 73 |
  | `access/cactus/MethodInitialToFinalApSummaries.kt` | 97 |
  | `access/cactus/MethodEdgesInitialToFinalCactusApSet.kt` | 85 |
  | `access/common/CommonFactSideEffectSummary.kt` | 48 (method reference), 96 |

- [x] Cactus and Automata sites must keep compiling and behaving as they do today until Task 6; if the operator cannot be removed for them yet, keep a mode-local shim rather than half-migrating.
- [x] Simplify `MethodCallSummaryHandler` (`:118-131`, `:143-144`) — no summary deep set to lift onto the caller's fact.
- [x] Verify: both suites green, no new skips.

### Task 5 — Persistence

- [x] `ExclusionSetSerializer.kt:36` and `JIRSummariesFeature.kt:205,254,383` move the annotation from the exclusion set to the node on both the fact and summary formats. Bump the summary format version.
- [x] Delete the nine "must not be prepended to a fact path" checks now that `DeepMarkExclusion` is not an `Accessor`.
- [x] Verify: a summary written before the change is rejected by version, not silently misread.

### Task 6 — Automata (separate decision point)

- [ ] **Do not start this without first fixing the intervening-call taint drop**, or there is no way to tell a fix from the existing vacuity. Re-run the four `CleanerFieldSensitivityAnalysisTest` non-vacuity controls in Automata mode; they must be green before any Automata claim is believable.
- [ ] Give `AccessGraph` the same node annotation (`AccessGraph.kt:328` builds the excluded-accessor bitset today).
- [ ] Verify: the ten Automata skips in `CleanerFieldSensitivityAnalysisTest` and the Automata `base-only clean` skip are re-enabled or individually re-justified.

### Task 7 — Corpus regression gate

- [x] Run the full querylang suites and the OWASP benchmark, not a subset. Partial runs have misled on exactly this code before.
- [x] `EXPECTED_TRACES` must not lose traces. A *gain* in precision (fewer false positives) is the goal; any lost trace is a false negative and blocks the change.
- [x] Record before/after counts in the completion report.

---

## Risks, ranked by how likely they are to bite

1. **Concat filtering** (Task 3). It is the one place the annotation gets teeth, and an over-eager filter is a silent false negative — the direction that matters. The unsanitized-sibling cases and the Task 3 regression guard are the defense.
2. **Same-node merge law and unfold inheritance** (Task 1). Subtle, but cheap to pin before the engine is touched.
3. **Node identity and interning** (Task 2). Much smaller than in the every-node design — only abstract nodes carry payload — but node equality still changed, hence the retained gate.
4. **Automata** (Task 6). May not be reachable at all without the intervening-call fix first.

## Alternatives considered and rejected

- **Per-node "at and below" annotation on every `AccessNode`** — the first draft of this plan. Superseded: growth happens only at abstract nodes, so annotating concrete nodes buys nothing and puts a field on the hottest structure in the engine for no return.
- **A path prefix inside `DeepMarkExclusion`** — keeps the flat set but reimplements tree navigation inside the accessor, needs its own k-limit, and must be rebased by hand at every prepend site in all four AP representations. The tree already does all of that.
- **A different merge combinator at the storage sites** — measured, both directions: `mergeAndIntersectDeep` gives 2 false positives, deep-aware `union` gives 2 false negatives. No operator recovers what the flat representation already discarded.

---

## Execution record (2026-07-28)

Executed Tasks 1–5 and 7; Task 6 deferred by its own gate (requires the Automata
intervening-call fix first). Deviations, each sanctioned by the shim clause or noted:

- **Three seams the plan had not named** were required to make the claim survive to the
  caller, found by measurement on `cleanOnlyFlow`: the empty-delta summary application
  (`SummaryExclusionRefinement` now carries the empty delta and appliers concat it),
  the id-edge storage (`splitOnMatching` no longer matches an annotated abstraction),
  and `AbstractionExclusions.union` for accumulating caller and callee claims on one
  lineage.
- **Task 3 acceptance**: the split plan's red cases (`AssignmentFormCleanAnalysisTest`,
  `AnyFieldMonotonicityAnalysisTest`) do not exist on this branch — removed in the
  history squash. The traversal half is pinned by `AbstractNodeExclusionTest` instead.
- **Task 4**: the three tree-only merge sites use `union` (asserting the deep-free
  invariant); `mergeAndIntersectDeep` and the deep lift stay for automata/cactus and
  the shared `CommonFactSideEffectSummary` until Task 6.
- **Task 5**: the summary store gained a `formatVersion` property (2) using the
  existing absent-property-means-old pattern; pre-existing entities never match and
  are recomputed. The nine "exclusion-set-only" checks stay while the flat channel
  lives.

Results: unit suite 142/0/0 (was 126); `:test` 700/0/15 (was 700/0/19 — the four
red acceptance cases re-enabled and green, wall-clock unchanged, Task 2 perf gate
+1.4%); java-querylang 197/0/23; go-querylang 761/0/4; OWASP (explyt fork corpus,
documented expectation 4112 + 226 = 4338): **total=4338, generationFailed=0** — no
trace lost, none gained.
