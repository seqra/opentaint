# Field-sensitive deep mark exclusions

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a starred cleaner correct. `clean($*A)` inside a summarized wrapper must clean only the paths that actually flowed through it, not every path below the same base.

**Architecture:** A `DeepMarkExclusion` moves out of the flat per-edge `ExclusionSet` and becomes a **per-node annotation on the access tree** — "at this node and below, mark `m` is removed". The node position replaces the depth threshold that is the claim's only coordinate today. Because the annotation lives on the node, `prependAccessor` carries it down with the path for free and `readAccessor` either descends past it or never meets it, which is exactly the branch discrimination the flat set cannot express.

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
| `.../ap/ifds/access/tree/AccessTree.kt` | `AccessNode` carries excluded marks; `removeAccessors` becomes a local descent; `prependAccessor`/`readAccessor` need no exclusion handling |
| `.../ap/ifds/access/tree/AccessPath.kt` | initial-side filter reads the node annotation instead of the flat deep set |
| `.../ap/ifds/Accessors.kt` | `DeepMarkExclusion` stops being an `Accessor`; becomes a mark-set element |
| `.../ap/ifds/ExclusionSet.kt` | loses `deepExclusion` / `withDeepExclusion` / `mergeAndIntersectDeep`; `union` becomes unconditional again |
| `.../dataflow/taint/FactReader.kt` | `excludeDeep` annotates the node at the fact's position instead of writing the refinement channel |
| `.../ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt` | one merge operator; no deep special-casing |
| `.../ap/ifds/serialization/ExclusionSetSerializer.kt`, `.../jvm/ap/ifds/JIRSummariesFeature.kt` | fact and summary formats carry the annotation |

---

## Tasks

### Task 1 — Unit-pin the combination laws before touching the engine

- [ ] Add `AccessNodeExclusionTest` to the dataflow unit suite covering: annotating a node; the annotation surviving a parent prepend; a sibling branch NOT inheriting it; two annotations on the same node combining by intersection (the join of a cleaned and an uncleaned lineage is uncleaned); annotations on different nodes coexisting.
- [ ] The same-node intersection is the one piece of the old law that survives, now at the right granularity. Assert it explicitly.
- [ ] Verify: `:opentaint-dataflow-core:opentaint-dataflow:test` **126 + new / 0 / 0**.

**Why first:** this is the part most likely to be wrong and the cheapest place to be wrong in.

### Task 2 — Carry an excluded-mark set on `AccessNode` (behaviour-preserving)

- [ ] Add the set to `AccessNode` and thread it through `manager.create(isAbstract, isFinal, accessors, accessorNodes)` (`AccessTree.kt:622`), node equality, hashing and interning.
- [ ] Every construction site passes an empty set. Nothing reads it yet.
- [ ] Verify: both suites at baseline, unchanged. **Also record heap and wall-clock for `:test`** — every node in the engine just grew a field, and this is the task where that cost lands.

**Stop-and-report gate:** if `:test` wall-clock regresses more than ~15%, stop and report before Task 3. The alternative design (a path prefix inside `DeepMarkExclusion`) trades this cost for reimplementing tree navigation, and that trade should be made on measured numbers, not guessed.

### Task 3 — Attach the claim to the node

- [ ] `FinalFactReader.excludeDeep` (`FactReader.kt:55`) annotates the node at the fact's current position instead of adding to `refinement`.
- [ ] `refineFact` (`FactReader.kt:59-69`) no longer carries deep entries; the refinement channel goes back to plain accessors only.
- [ ] `removeAccessors` (`AccessTree.kt:625`) becomes a local descent: union the node's annotation into an active set on the way down, drop children in that set. Delete the `minPruneDepth` threshold — the node position is the anchor.
- [ ] `prependAccessor` and `readAccessor` get **no** exclusion-specific code. If either needs any, the annotation is in the wrong place.
- [ ] Verify: the four red cases above go green in Tree with their non-vacuity controls still green; remove their `@Disabled`.

### Task 4 — Collapse the combination laws

- [ ] Remove `deepExclusion()` / `withDeepExclusion()` / `mergeAndIntersectDeep()` from `ExclusionSet`; restore `union` to its unconditional form and delete the `check` — nothing deep can reach it once Task 3 lands.
- [ ] Return every storage merge site to a single operator. There are **eleven**, not the four the sibling-edge discussion covers — enumerate before editing, because the tree-mode ones are the only ones the acceptance tests exercise and the rest will fail silently:

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

- [ ] Cactus and Automata sites must keep compiling and behaving as they do today until Task 6; if the operator cannot be removed for them yet, keep a mode-local shim rather than half-migrating.
- [ ] Simplify `MethodCallSummaryHandler` (`:118-131`, `:143-144`) — no summary deep set to lift onto the caller's fact.
- [ ] Verify: both suites green, no new skips.

### Task 5 — Persistence

- [ ] `ExclusionSetSerializer.kt:36` and `JIRSummariesFeature.kt:205,254,383` move the annotation from the exclusion set to the node on both the fact and summary formats. Bump the summary format version.
- [ ] Delete the nine "must not be prepended to a fact path" checks now that `DeepMarkExclusion` is not an `Accessor`.
- [ ] Verify: a summary written before the change is rejected by version, not silently misread.

### Task 6 — Automata (separate decision point)

- [ ] **Do not start this without first fixing the intervening-call taint drop**, or there is no way to tell a fix from the existing vacuity. Re-run the four `CleanerFieldSensitivityAnalysisTest` non-vacuity controls in Automata mode; they must be green before any Automata claim is believable.
- [ ] Give `AccessGraph` the same node annotation (`AccessGraph.kt:328` builds the excluded-accessor bitset today).
- [ ] Verify: the ten Automata skips in `CleanerFieldSensitivityAnalysisTest` and the Automata `base-only clean` skip are re-enabled or individually re-justified.

### Task 7 — Corpus regression gate

- [ ] Run the full querylang suites and the OWASP benchmark, not a subset. Partial runs have misled on exactly this code before.
- [ ] `EXPECTED_TRACES` must not lose traces. A *gain* in precision (fewer false positives) is the goal; any lost trace is a false negative and blocks the change.
- [ ] Record before/after counts in the completion report.

---

## Risks, ranked by how likely they are to bite

1. **`AccessNode` interning and memory** (Task 2). Every node grows a field, and nodes are interned, cached, hashed and merged throughout the engine. This is a footprint change to the hottest structure in the analysis, and it is why Task 2 has an explicit stop-and-report gate.
2. **Same-node merge law** (Task 1). Subtle, but cheap to pin.
3. **Over-eager annotation drop in `readAccessor`** (Task 3). Dropping a claim too readily is a silent false negative — the direction that matters. The unsanitized-sibling cases are the guard.
4. **Automata** (Task 6). May not be reachable at all without the intervening-call fix first.

## A cheaper partial, if the full change is not affordable

At `excludeDeep`, when the fact's path is fully concrete (no abstract node), delete the node positionally instead of recording a claim. That closes the "starred cleaner over a concrete fact" subclass — the depth-2 row of the table above — with no changes to `AccessNode`, `ExclusionSet` or serialization.

It does **not** fix the `DeepCleanSummaryAnalysisTest` cases, where the source itself is any-field and the fact genuinely is abstract. Treat it as a stopgap, and measure first: instrument `excludeDeep` to count concrete versus abstract fact paths across an OWASP run before deciding it is worth landing on its own. **This is an untested hypothesis, not a measured result.**
