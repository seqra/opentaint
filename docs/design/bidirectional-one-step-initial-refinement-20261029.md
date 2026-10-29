# One-step initial refinement

Date: 29 October 2026. Source revision: `1a40d9008`.
This note records the selected changes and the remaining proof gaps.
It does not change production code.

Later clarification: the
[implementation proposal](bidirectional-summary-demand-workload-implementation-20261029.md)
adds the selected mode-aware STAR-demand cells and a total scalar policy.
Use explicit output templates and witnesses for the current image test:
run-2 requested STAR is not a self-emission fixed point. The earlier raw
projection theorem describes the historical policy only.
The partial model below remains historical evidence. The
[closed exact-replay trace](bidirectional-exact-flow-replay-trace-20261029.md)
replaces the standalone application example as the reachable gap witness.
Later decision: [FLOW summary normalization](bidirectional-flow-summary-normalization-20261029.md)
keeps EXACT point queries, records field-write E, and stores STAR summaries.
This supersedes the uncovered-EXACT replay choice below. The older model and
counterexample remain historical evidence. RemoveAll now clears the whole
selected position; partial all-mark cleaners are prohibited.

The earlier scalar intersection matrix is a comparison with current code.
It is not the selected emission policy. The new policy stops after one new
field. It can emit an initial broader than the submitted fact.

## 1. Selected behavior

Check concrete marks before field refinement. A demand for U and a submitted
T emit nothing when U differs from T. Do not rename the submitted mark to
make it satisfy a concrete demand. The tables use FULL marks and empty
exclusions. FLOW denotes an abstract demand mark.

The later STAR-demand correction is mode-specific:

```text
run-2:  p.*/M + submitted p.f.... with a compatible mark -> requested p.*/M
later:  no FLOW STAR demand entry is admitted
later:  concrete STAR/T keeps precise EXACT-at-demand answers
```

From run-2, outgoing FLOW DEMAND conclusions are ANY, not STAR. Their next
entry Dc is therefore ANY. A paired exit Dp may still be STAR. Do not ban
NORMAL FLOW STAR or the first-new-field STAR initial from an ANY demand.
For a concrete run-2 STAR initial, the starting layer remains DEMAND.
Keep demand E, check its admitted child, and use the submitted fact after
field limiting. This correction supersedes the earlier descendant-rejection
row; the closed overwrite/source diagnostic is retained as historical
evidence in `RestrictedInitialPolicy.PreciseDemandWriteDiagnostic`.
The current model is `RestrictedInitialPolicy.DemandStarPolicy`.

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

The new file has 41 checked theorem declarations. It proves that the current
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

## 8. Entry intersection must agree with initial emission

Later boundary update: the invariant below describes raw analysis initials.
For a canonical stored FLOW premise J, use the
[normalized-image rule](bidirectional-flow-summary-normalization-20261029.md#4-c5-the-normalized-emitter-image):
there is an emitted raw initial I whose summary normal form is J. A stored
STAR can therefore have a raw EXACT witness. The raw policy and its proofs
below remain unchanged.

Yes: update the demand-entry intersection used to restrict a summary
`A -> B`. Ordinary location overlap or containment is insufficient.

Define the directed condition:

```text
CanEmit(D_c, A) :=
    there is a valid submitted fact a for which Emit(D_c, a) produces A

EntryIntersection(D_c, A) :=
    A      if CanEmit(D_c, A)
    empty  otherwise
```

The supplied witness `a` need not equal A. For example, a supplied
`p.f.[any]/T` can produce initial `p.f.*/T`. Passing the STAR initial back
to the emitter is not the definition of `CanEmit`.

Compare complete initial descriptors: base, field path, tail, field exclusion,
mark, and the distinction between MAY and MUST. Normalize demand annotations
only where the selected policy already requires it. Do not erase the initial's
exclusions or alter its mark to make it pass.

For the selected ANY rules with empty exclusions:

| `D_c` | Existing initial A | Entry intersection |
|---|---|---|
| `p.[any]/T` | `p.f.*/T` | A; witness `p.f.[any]/T` |
| `p.[any]/T` | `p.f.$/T` | A; exact-input exception |
| `p.[any]/T` | `p.f.g.$/T` | Empty; emission stops at `p.f.*/T` |
| `p.[any]/FLOW` | `p.$/FLOW` | A; witness `p.$/T` |
| `p.[any]/FLOW` | `p.f.*/FLOW` | A; witness `p.f.[any]/T` |
| `p.[any]/FLOW` | `p.f.$/FLOW` | Empty; emission stops at `p.f.*/FLOW` |
| `p.[any]/FLOW` | `p.$/T` | Empty; the emitted mark would be FLOW |
| `p.[any]/M` | `p.*/M` | Empty in the selected ANY table |
| `p.[any]/U`, U differs from T | Any initial with T | Empty |

The current `insideDemand` check accepts several empty rows above. It checks
location and mark containment, not whether the new emitter can produce the
initial. The new guard is therefore a semantic tightening of C5.

### 8.1 Restrict the edge without changing its premise

For a paired demand with entry `D_c` and exit `D_p`:

```kotlin
fun restrict(edge: Edge, demand: Demand): Edge? {
    if (!canEmitInitial(demand.entry, edge.initial)) return null
    if (!insideDemand(edge.initial, demand.entry)) return null
    val exit = demand.exit ?: return null
    val result = restrictConclusion(edge.result, exit) ?: return null
    return edge.copy(result = result)
}
```

This is specification pseudocode. It preserves the existing conclusion-side
restriction, including its mark and layer rules. It also keeps the existing
entry-containment condition. The new condition rejects entries outside the
emitter's possible outputs.

Do not project `p.f.g.$/T -> B` into `p.f.*/T -> B`. Those are different
initials. The broader analysis must actually run to produce its own summary.
Entry intersection either keeps A or rejects the edge. It preserves DEMAND;
in particular, an accepted concrete STAR summary never becomes NORMAL.

### 8.2 Implementation scope

Use one canonical emission policy for C2 admission and the C5 entry guard.
Implement the possible-output test directly from its shape rules. Do not
enumerate actual inputs, marks, or initial combinations. The formal model's
executable witness is proof data, not a proposed runtime object or store.

Place the final guard at the entry check in `Reference.restrict`. All ordinary
local, static-carry, primitive-completion, and transitive-completion candidates
already reach that boundary through `DemandStore.intersect`. Rejected rows
must not contribute to its fully-covered test.

Candidate indexes may remain conservative. Do not reject intermediate static
search states using this final edge filter without a separate completeness
proof. A later composition can produce a different demand entry.

Keep generic `overlap`, `covers`, call matching, raw summary storage, normal
record persistence, and native record replay separate from this C5 update.
For an ND summary, apply the guard to the selected complete member and retain
the whole premise set, as the existing restriction does. Run-1 publication
and the current backward-ZERO publication bypass are unchanged; the C5 theorem
applies when ordinary demand intersection is performed.

### 8.3 Required proof contract

The required invariant is:

```text
EntryIntersection(D_c, A) is nonempty
    implies CanEmit(D_c, A)
```

The extended Lean model proves this implication for every successful query
in its scalar model. Each success contains a computed supplied-fact witness
and a proof that the selected emitter produces the unchanged A. Principal
accepted and rejected cells are checked, including the case where A cannot
emit itself.

Before implementation, also prove that the executable possible-output test
accepts every output of the complete emitter. Otherwise, a sound entry guard
could still reject needed work. The current model checks the principal shape
matrix; it does not claim this full generic completeness theorem or support
all nonempty-exclusion and demand-tail cases.

The old C5 coverage theorem assumes only `insideDemand`. It must gain the
`CanEmit` hypothesis. Its conclusion-side no-added-pair and layer properties
can be reused because the new entry guard only removes candidates.
Whole-run no-loss needs the matching C2-to-C5 and witness-routing proofs.
In particular, marked rule observations rejected under a FLOW entry need an
independent compatible concrete-demand or record route. The entry invariant
alone does not prove that route. This update adds no grounding mechanism.
