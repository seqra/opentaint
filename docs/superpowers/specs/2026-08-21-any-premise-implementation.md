# `[any]` as a first-class premise accessor — implementation log

Implements `2026-08-21-any-premise-design.md` on branch `saloed/14-any-premise-impl`,
branched from `saloed/13-any-premise-design` (= `saloed/5-default-get` @ `4c358d2e1`
plus the design doc). The design's §10 sequencing is followed; each step is one commit
and was independently gated.

## Test gate

`scratchpad/gate-impl.sh <label> [-Dprop=v]` runs every test task and reports a
per-module breakdown.

**The gate as originally written was measuring the wrong thing, and this was found
mid-implementation.** `core/` is a composite build and `opentaint-dataflow-core` — the
module this work changes most — is an *included* build, so a bare `gradlew test` never
ran its tests, while the result glob happily counted whatever stale XML the directory
held. Every included-build test task is now named explicitly. Real coverage went from a
claimed 1790 to 3341.

| | tests | failures | notes |
|---|---:|---:|---|
| pre-feature baseline (`24d553078`) | 3341 | 0 | measured with the corrected gate |
| step 1 — representation invariants | +7 | 0 | |
| step 2 — concat absorption | +7 | 0 | |
| step 3 — `[any]` in `AccessPath` | +12 | 0 | |
| step 4 — premise lookup rule | +11 | 0 | |
| steps 5–6 — producer and cap | +14 | 0 | |
| **merged, cap off (the shipping default)** | **3392** | **0** | 3341 + exactly 51 new tests |
| **merged, cap forced to 1** | **3392** | **1** | see below |

Steps 7–8 (representation-only) moved the gate by nothing at all, in count or content,
which is the bar a change with no semantic content has to clear.

The arithmetic closing exactly — 3341 + 51 = 3392 — is the evidence that no
pre-existing test was lost or silently skipped anywhere along the way.

### The one failure at cap = 1

`TreeCleanerFieldSensitivityAnalysisTest.concrete two-level clean over an abstract
source - the sanitized field is silent` — an `assertNotReachable`, i.e. a **false
positive, not a lost finding**. That is the FN-safe direction §4 S3 predicts:
past the cut the demand is answered by the coarse `[any]` edge, and an entry fact
carrying `[any]` cannot express the cleaner's node deletion inside it, so the cleaned
field is resurrected.

Verified limit-dependent by direct measurement on the merged tree, same class run
freshly at each setting:

| cap | tests | failures |
|---:|---:|---:|
| 1 | 16 | 1 |
| 3 | 16 | 0 |

The flow needs three unrolls (`node`, `f`, `k`). No `assertReachable` fails anywhere at
cap = 1. This is the precision dial of §7 R2, and it is exactly why the cap ships
**off** (`-Dopentaint.anyUnrollLimit=-1`) pending a value chosen from measurements on a
converging workload.

## What the design got wrong, and what it missed

Four things worth recording, because they are the places where implementing the design
changed it.

1. **§5.1 underestimated the `maxDepth` inflation.** The design treats the 10_000 as
   purely a sentinel that makes the cost gate unsatisfiable. It is also load-bearing for
   *soundness*: `filterStartsWith` prunes a match with `maxDepth < accessPath.size`, but
   the walk descends with `getChild`, which synthesises children through an `[any]` edge
   to arbitrary depth. Shrinking the charge alone would have turned that prefilter into a
   lost flow. Both prefilters are now guarded by `containsAnyInThisOrDeepNodes`, so their
   correctness rests on reachability rather than on the size of a number.

2. **§3.4's C0 and C4 pull in opposite directions, and C4 wins.** Absorbing once on
   descent and letting the absorbed delta propagate below the `[any]` — which is what
   makes C0's limiter savings apply to the whole subtree — *is* absorption into
   `[any].f.*`, which C4 forbids because `[any].f.x.![m]` and `[any].f.![m]` are disjoint.
   The local form is implemented: the flag is set for exactly one level and never
   inherited. C0's benefit is correspondingly narrower than the design implies.

3. **Emitting the `[any]` premise unconditionally is a precision loss.** §3.1 reads as
   though the premise should simply fall out of treating `[any]` as an ordinary accessor.
   Measured: emitting it alongside a live enumeration false-positives a cleaner test even
   *uncapped*, because the caller fact matches the coarse premise as well as the concrete
   ones. Emission is therefore gated on the base having stopped enumerating — which is
   the answer §7 R5 leaves open, now settled with evidence.

4. **A trace-resolution path can lose findings, which the design does not mention.**
   `splitDelta` could not match a required fact against a summary exit fact of shape
   `X.[any].*`. That looks cosmetic — trace resolution explains an already-decided
   finding — but `TracePath.kt:37` turns a null trace into
   `TracePathGenerationResult.Failure` and `TaintAnalyzer.fullScan` filters exactly those
   out, so a derived, registered, confirmed finding is discarded whole. A positive
   `StarOperatorTest` case was lost this way. `splitDelta` now steps over one `[any]` per
   accessor and names it on the matched prefix.

   This also corrects a KDoc written earlier in the same work, which asserted that trace
   resolution cannot remove a finding. The decision it justified (keep `splitDelta`
   permissive) was right; the reason given was wrong, and a future reader could have
   tightened `splitDelta` on the strength of it.

## The design's one open question, resolved

§6.7 flagged that `FactSideEffectSummariesTreeApStorage` and
`SideEffectRequirementTreeApStorage` have no `[any]` expansion arm and asked whether that
matters. Traced, not guessed: `filterContains` → `collectSummariesTo` → `filterTaintedTo`
→ `subscribeOnMethodSummary` → `handleFactToFactMethodSideEffectSummary` →
`tryApplySummaryEdge`. A missed activation means the unfold request never reaches the
caller, so neither the cross-unit refinement nor the upward side effect happens. It is
not systematically compensated — the unfiltered `collectAll*` paths are
serialization-only, and the push path via `filterStartsWith` fires only when the callee's
summary happens to land after the caller subscribed.

The lookup rule was therefore hoisted into the class that owns the trie, so all three
storages share one implementation. Net visibility change was negative: hoisting let
`collectNodesContainsAccessor` go from `open` to `private`.

## Performance

See `2026-08-21-any-premise-benchmark.md`.
