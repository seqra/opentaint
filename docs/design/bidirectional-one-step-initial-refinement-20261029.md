# One-step initial refinement

Date: 29 October 2026. Source revision: `f6f544ab5`.
This note records the selected changes and the remaining proof gaps.
It does not change production code.

The earlier scalar intersection matrix is a comparison with current code.
It is not the selected emission policy. The new policy stops after one new
field. It can emit an initial broader than the submitted fact.

## 1. Selected behavior

Check concrete marks before field refinement. A demand for U and a submitted
T emit nothing when U differs from T. Do not rename the submitted mark to
make it satisfy a concrete demand. The tables use FULL marks and empty
exclusions. FLOW denotes an abstract demand mark.

| Demand entry | Submitted fact | Selected initial |
|---|---|---|
| `p.[any]/FLOW` | `p.f.$/T` | `p.f.*/FLOW` |
| `p.[any]/FLOW` | `p.f.g.$/T` | `p.f.*/FLOW` |
| `p.[any]/FLOW` | `p.$/T` | `p.$/FLOW` |
| `p.[any]/FLOW` | `p.[any]/T` | `p.[any]/FLOW` |
| `p.[any]/FLOW` | `p.[any-taint]/T` | `p.[any-taint]/FLOW` |
| `p.[any]/T` | `p.f.$/T` | `p.f.$/T` |
| `p.[any]/T` | `p.f.g.$/T` | `p.f.*/T`, DEMAND |
| `p.[any]/T` | `p.f.g.[any-taint]/T` | `p.f.*/T`, DEMAND |
| `p.[any]/U`, U differs from T | Any submitted fact with T | None |

`.f` resolves the current unknown field. Do not also consume `.g` or the
terminal `$` in that refinement step. The concrete-T exact-input case is
the selected exception: `p.f.$/T` stays exact instead of becoming STAR.
The exception applies only when the exact input ends after that first new
field. If `.g` remains, emit `p.f.*/T` in DEMAND. Do not preserve `.g.$` in
the initial. The earlier whole-path interpretation was incorrect.
Use the submitted fact after the existing field-limit step. A cut to ANY
does not qualify for the exact-input exception.

An unchanged `[any]` intersection remains valid. Strict field progress is
not a general admission requirement. The earlier source and sink examples
therefore need no special exception.

The earlier decision to retain concrete T for `[any-taint]` was revoked.
There is no such mark exception now. Using the demand mark in that case
requires an abstract `[any-taint]/FLOW` shape as well as `$/FLOW`.
The full transfer and application rules for this new shape need proofs.

## 2. Concrete STAR is always DEMAND

```text
selected initial:  p.f.*/T
starting edge:    p.f.*/T -> p.f.*/T, DEMAND
derived summary:  p.f.*/T -> result, DEMAND
caller NORMAL + derived summary DEMAND -> result DEMAND
```

This is never a NORMAL edge. It remains DEMAND when the submitted input
was NORMAL and when the summary uses coverage matching. It cannot become
a NORMAL persistent record.

This layer rule already exists in
[initialFacts](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Demand.kt#L17).
Keep STAR in its starting conclusion. Do not use the older Lean start row
that changed concrete STAR into ANY.

The concrete STAR rule does not set the layer of `p.f.*/FLOW`.
The existing FLOW STAR start is NORMAL. The new abstract EXACT and MUST
shapes need their own complete transfer and application contracts.

## 3. Coverage matching for these STAR initials

Consider this input and demand at run-3, field limit 2:

```text
demand:    p.[any]/T
submitted: p.f.g.[any-taint]/T, NORMAL
initial:   p.f.*/T, DEMAND
```

The initial covers the submitted fact through suffix `.g`. The submitted
fact does not cover the entire initial. Current restricted matching rejects
this direction for a concrete premise. The selected change permits coverage
matching for these STAR initials.

The corresponding candidate lookup must find the STAR premise above the
submitted path. Fix both candidate selection and the final matching test.
Keep the mark test, suffix binding, field exclusions, and DEMAND layer.
Do not add the same fallback to every concrete ANY or MUST premise.

A code family that needs the new matching direction is:

```java
main() {
    b.f.g = sourceT();
    sinkU(convert(b));
}

// convert rule:
// ContainsMark(arg0.[any], T) -> assign U to return
```

The wider T initial can produce a U summary. The caller must receive that
DEMAND result when its actual T input matches the known suffix.

## 4. First-field abstraction keeps the caller suffix

For an identity helper, the abstract initial need not copy the full actual
field chain:

```text
submitted:        p.f.g.$/T
initial:          p.f.*/FLOW
normal summary:   p.f.*/FLOW -> ret.f.*/FLOW
bound suffix:     .g
caller result:    ret.f.g.$/T
```

The abstract analysis stops at `.f`. Ordinary application still uses the
actual suffix `.g` and actual mark T. The Lean model checks this application.
It does not claim that every result under a broader initial is NORMAL.

## 5. Abstract EXACT and MUST are domain extensions

Current typed initials reject `$/FLOW` and `[any-taint]/FLOW`. Current FLOW
trees allow only STAR and ANY. Supporting the new shapes requires more than
removing the factory guards.

Keep the tail in the FLOW tree header. Existing tree groups already include
the tail in their key; a new payload bit in every trie leaf is not required
by these shapes alone. Audit each consumer of that header.

For EXACT, a root fact must not supply a child read:

```text
initial:       p.$/FLOW
operation:     p.f.* -> out.*
correct:       no result
wrong widening to p.*/FLOW: out.[any]/FLOW, DEMAND
```

The wrong result is an extra DEMAND candidate, not a demonstrated NORMAL
soundness failure. It still changes field transfer and must not be hidden
in initial construction.

There is a separate NORMAL application gap. Suppose an identity method has
the new record `p.$/FLOW -> ret.$/FLOW`. A caller has `q.* -> p.*`, NORMAL.
Removing S8 alone allows the current exact-target cell to produce
`q.* -> ret.$`, NORMAL. That incorrectly maps `q.f` to the returned root;
an identity maps it to `ret.f`. The model proves this false NORMAL pair.
The application rule for the new exact shape must close this gap. No repair
is selected by this note.

Abstract MUST also needs a uniform-mark interpretation. Do not infer uniform
taint from an ordinary FLOW STAR input merely because their covered location
sets overlap. Its transfer, matching, layer, and record contracts need proofs.
Do not silently reuse the STAR branch for MUST.

## 6. Affected implementation boundaries

| Boundary | Current restriction or assumption | Required work |
|---|---|---|
| `Premise.kt`, `Demand.kt`, `ApManager.kt` | Exact and must initials need concrete marks | Admit the selected abstract shapes and define their starts |
| `Conclusions.kt` | FLOW tail is STAR or ANY | Represent new tails without coercion |
| `EdgeApplication.kt`, scalar `Reference.kt` | S8 excludes abstract exact source/target; FLOW traversal assumes STAR/ANY | Prove and implement narrowly scoped new transfer/application rows |
| `Summary.kt` | Non-STAR FLOW is treated as ANY in selection and packing | Preserve EXACT and MUST; do not use fallback classification |
| `CalleeSubscriptions.kt`, `Summary.kt`, `Reference.satisfies` | Concrete restricted initials do not use coverage matching | Add the selected STAR matching direction and candidate lookup |
| `DemandStore.Builder` | Abstract exact demand endpoints are rejected | Preserve new endpoints through handoff |
| `RecordStore.kt` | Abstract native initial must have STAR | Extend persistence and read-view application only with soundness proofs |

Keep existing source and sink mark gates. A new abstract shape does not
authorize a concrete mark check. Keep ZERO canonical. Keep field writes,
alias rules, and normal/demand behavior outside the selected changes.
Do not add grounding labels, provenance stores, or a completed-initial cache.

## 7. Formal validation and scope

[OneStepRefinement.lean](../../spec/lean/proposals/initial-emission/OneStepRefinement.lean)
checks the selected cells, the concrete mark mismatch gate, first-field
stopping, and the concrete exact exception. It distinguishes current matching
from the selected coverage direction. It also checks the suffix-preserving
identity example and both abstract-EXACT hazards.

The model is scalar and uses empty exclusions. It is not a proof of the full
new initial grammar or of whole-driver convergence. A complete emission table
still needs all ancestor, equal-prefix, field-exclusion, and mark-mode cells.
The model pins the exception boundary: `p.f.$/T` stays exact, but every exact
path with at least two new fields stops at `p.f.*/T` in DEMAND.

The new file has 35 checked theorem declarations. It proves that the current
concrete STAR start retains STAR and enters DEMAND; its computed transfers
remain DEMAND; and application of a DEMAND summary cannot produce a NORMAL
result. The NORMAL abstract-EXACT counterexample is a different case.

From `spec/lean`, validate with:

```sh
lake build ApSpec.CorrelatedConcreteImplementation
lake env lean proposals/initial-emission/OneStepRefinement.lean
```

All theorem axiom audits use only `propext` and `Quot.sound`. The
[embedded evidence](../reports/data/bidirectional-initial-emission-refinement-20261029.json)
contains the source hash, commands, output, user decisions, and audit results.

No new project measurement was run. The latest saved local cycle completes
**run-9** at its test cap; its control stops at **run-3**. The latest full
OWASP measurement reaches **run-12**, completes **run-11**, and accepts the
run-11 forward report. These measurements predate the proposed changes.
