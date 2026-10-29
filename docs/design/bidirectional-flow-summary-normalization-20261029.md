# FLOW summary normalization

Date: 29 October 2026. Source reviewed: `57092ce82`.
Status: design draft. Normalization, write exclusions, and whole-position
RemoveAll are selected. Production code is unchanged.
Latest modeled iteration of the motivating example: **run-3**.

## 1. Selected behavior

Keep the selected initial emission policy. Do not replace an emitted
EXACT/FLOW query with STAR at method entry. Normalize at the summary boundary:

```text
point-analysis result:  a.x.$/FLOW -> b.y.$/FLOW, NORMAL
stored summary:        a.x.*/FLOW -> b.y.*/FLOW, NORMAL
```

Replace each EXACT tail of a pure FLOW summary with STAR. Preserve both
bases, both paths, marks, layer, and field exclusions. In particular, y
does not become x. Apply this rule on every run and in both directions.
Keep ANY and MUST tails unchanged. Keep concrete TAINT, ND, and ZERO
relations unchanged. Concrete static class markers remain EXACT.

The normalization is a generalization of a relation. It is not equality
between a literal exact-root relation and a STAR relation. Its required
invariant is that each NORMAL FLOW result describes a valid suffix-preserving
template after its exclusions are applied.

| Part | Before | Selected behavior |
|---|---|---|
| EXACT/FLOW point state | Literal root geometry can discard a child-write exclusion | Keep the read barrier and record the write exclusion |
| Method exit | Store the EXACT premise and result | Store STAR in place of each FLOW EXACT endpoint |
| Replay | Exact target can discard a caller suffix | Apply the ordinary correlated STAR summary |
| C5 entry guard | Test the raw emitter image on the stored premise | Test the normalized image of the raw emitter |
| RemoveAll cleaner | A below-only form can leave a root-only result | Permit only whole-position removal, including descendants |

These are explicit changes to the proposed abstract EXACT domain. Existing
concrete EXACT facts and existing field-write policy keep their behavior.

## 2. Field-write exclusion

For a later run, the immediate-child overwrite has this trace:

```java
// Submitted: p.$/T, at the demanded root.
// Previous demand: entry p.[any]/FLOW; exit ret.*/FLOW.
// Emitted initial: p.$/FLOW; start NORMAL, E={}.
static Root helper(Root p) {
    p.f = new Inner();
    // Point result: p.$/FLOW, NORMAL, E={f}.
    // The overwrite affects the eventual suffix template.

    return p;
    // Point result: ret.$/FLOW, NORMAL, E={f}.
}
// Produced point relation:
//   p.$/FLOW -> ret.$/FLOW, NORMAL, output E={f}.
// Normalized summary:
//   p.*/FLOW -> ret.*/FLOW, NORMAL, output E={f}.
// A marked p.f suffix is excluded. A disjoint p.g suffix survives as ret.g.
```

An EXACT/FLOW conclusion can carry E. Its read geometry remains EXACT:
an ordinary read below that point does not become an ancestor MAY read.
E records the suffix effect that the summary boundary must preserve.
Ordinary root moves, bindings, and return transfer keep this E.

Use the existing strong-write residual rules. At the same fact prefix,
union the overwritten field into E. Keep existing kill, sibling, and proper
prefix branches; do not make a write immune because a query is EXACT.
An ancestor mask is not copied onto a deeper fact after an admitted descent.

Run-1 keeps its existing policy:

```text
write updates a FLOW exclusion
    -> move the affected result to DEMAND
    -> clear E
    -> normalize EXACT to STAR only at the summary boundary
```

No weak-write policy is added. On later runs, a NORMAL result can keep
nonempty E and must persist it.

RemoveAll always removes every mark at the selected position and below it.
Below-only and exact-only all-mark cleaners are prohibited. Thus neither
EXACT/FLOW nor MUST/FLOW can retain a root-only survivor at that position.
This is an explicit cleaner semantic change. Selected RemoveMark reach,
mark exclusions, and request behavior keep their existing rules.

```kotlin
// Rule validation: a terminal AnyField requests the prohibited below-only form.
is RemoveAllMarks -> if (position.any) reject("RemoveAll needs a whole position")

// Rule lowering for an admitted whole position, including a named field.
Cleaner(position.base, position.path, CleanReach.AT_AND_BELOW, mark = null)

// Low-level bidi Cleaner guard; also protects manually supplied/generated forms.
require(mark != null || reach == CleanReach.AT_AND_BELOW)
```

Use `RemoveAll(p)` to clear p and its descendants. Reject `RemoveAll(p.AnyField)`;
do not silently reinterpret a below-only rule. Retain the existing diagnostics
and rule-rejection scope. Static and named-field lowering still use their
ordinary whole-position kill or read/clean/write path. Generated Spring
whole-position cleanup remains valid. Structural field overwrites are not
partial all-mark cleaner actions and keep their existing rules.

Named fields are permitted:

```text
RemoveAll(p.f)          legal: kill marks at p.f and below p.f
                       keep the parent p and disjoint siblings such as p.g
RemoveAll(p.f.AnyField) prohibited: below-only removal would keep p.f
```

For an EXACT/FLOW root query, a field cleaner lowered through its ordinary
read/clean/write steps must record the final write exclusion E={f}. The
ordinary field read barrier does not cancel that write effect. Constructor
validation must also cover generated `CallCleaners`, which bypass provider
actions. Update old tests that admitted partial all-mark cleaners; keep
targeted RemoveMark and structural field-write tests unchanged.

## 3. Storage and publication

Normalize a complete pair. Do not normalize only the Facts result inside
`RunSummaryStore.add`: the caller would still publish the old premise.

```kotlin
data class SummaryForm(val premise: PremiseKey, val facts: Facts)

fun normalizeFlowSummary(p: PremiseKey, f: Facts): SummaryForm {
    if (!p.isFlow || f !is FlowTree) return SummaryForm(p, f)
    val i = p as InitialAp // K6: a FLOW relation has a singleton FLOW premise.
    val initial = if (i.tail == Tail.EXACT)
        internInitial(i.toPattern().withTail(Tail.STAR)) else i
    val result = if (f.tail == Tail.EXACT)
        flowTree(f.base, f.layer, f.exclusion, f.markExclusion, f.root, Tail.STAR)
    else f
    return SummaryForm(initial, result)
}

fun retainSummary(rawInitial: PremiseKey, rawFacts: Facts) {
    val s = normalizeFlowSummary(rawInitial, rawFacts)
    // Keep existing filters and static-summary routing, with the canonical pair.
    val delta = summaries.add(s.premise, s.facts) ?: return
    queuePublications(s.premise, delta)
}
```

These are API sketches. Reuse the manager's existing interning methods.
Preserve E and mark exclusions; do not recreate a tree with default headers.
An exact result's new E is not cleared before constructing its STAR form.

Use the same normal form for raw summary storage, static-summary guidance,
publication, selected demand storage, predefined summaries, and native-record
persistence. Conclusion restriction can create an EXACT piece, so normalize
that piece again before publication or `addDemand`. Assert the normal-form
invariant at stores. Do not normalize static write-point facts or ordinary
method-edge storage merely because they use a summary-like payload.

Normalizing is idempotent. Deduplication uses the canonical premise and
result keys. No origin/history store or new fact-protection flag is added.

## 4. C5: the normalized emitter image

Method analysis still runs under the emitted raw initial I. A stored summary
uses J=NormalizeInitial(I). Thus the former raw-image invariant is replaced:

```text
C5 accepts stored J only if:
    there is a submitted fact a and raw initial I such that
    Emit(Dc, a) = I and NormalizeInitial(I) = J.
```

No runtime history is needed. For a canonical STAR initial, the only possible
raw preimages are that initial and its same-geometry EXACT form:

```kotlin
fun canStoreInitial(entry: Pattern, stored: Pattern): Boolean {
    fun fits(raw: Pattern) =
        policy.canEmitInitial(entry, raw) && insideDemand(raw, entry) &&
            normalizeFlowInitial(raw) == stored

    if (fits(stored)) return true
    return stored.isFlow && stored.tail == Tail.STAR &&
        fits(stored.withTail(Tail.EXACT)) // Validate legal raw E and shape.
}
```

Implement these two structural tests without interning hypothetical APs or
enumerating marks. The formal witness is proof data, not a new retained store.

Apply the old containment test to the candidate raw initial. Testing the
canonical STAR against an EXACT demand would reject a legitimate raw EXACT
query. C2 continues to use the raw emission policy. C5 and its early pruning
filter use `canStoreInitial`. The whole correlated result still passes the
existing conclusion restriction before the covered-result check.

## 5. Effect on the three-run example

Run-1 is unchanged. The run-2 point analyses are also unchanged:

```java
// Previous demand: entry ret.[any]/FLOW; exit p.*/FLOW.
// Submitted: ret.$/FLOW, NORMAL. Emitted initial: ret.$/FLOW.
static Inner helper(Root p) {
    return p.f;
    // Backward point result: p.f.$/FLOW, NORMAL, E={}.
}
// Point relation: ret.$/FLOW -> p.f.$/FLOW, NORMAL.
// Stored/published NORMAL: ret.*/FLOW -> p.f.*/FLOW.
// Forward record view: p.f.*/FLOW -> ret.*/FLOW.
```

Wrapper's run-2 A result is similarly stored as
`ret.a.*/FLOW -> q.f.*/FLOW`, NORMAL. Its forward read view now applies to
the real input `q.f.h.[any-taint]/T` and returns `ret.a.h.[any-taint]/T`.
It preserves h and supplies no T at the root of A.

Run-3 wrapper analysis still runs for its B demand. Helper replay now gives
STAR, so the new raw A summary is valid `q.f.* -> ret.a.*`, NORMAL.
C5 still publishes only B in that run; raw persistence keeps a valid A row.
The existing normalized wrapper record can already deliver A.h to main.
Record availability does not suppress initial admission or create an
unselected completed-query cache.

## 6. Implementation and proof boundaries

Update the proposed EXACT/FLOW guards to permit its field-effect E. Keep
concrete EXACT/T exclusions empty. Preserve the new E in scalar
`Reference.below` and `normalize`, typed FLOW transfer, manager conversion,
root moves, bindings and return. Keep EXACT initial admission and its read
barrier separate from canonical summary keys.
Raw EXACT query premises keep Empty E. Only their derived FLOW conclusions
acquire the write-effect exclusion.

Remove the planned native abstract-EXACT record extension and the separate
covered-EXACT replay planner. Stored FLOW records cannot contain EXACT.
Keep abstract MUST representation, its native-view work and the selected
definite-MUST input test. Concrete EXACT records remain unchanged.

Required implementation checks:

| Boundary | Required cases |
|---|---|
| Summary storage/publication | Normalize both endpoints before dedup; publish the canonical premise; normalize selected pieces again; no stored FLOW EXACT |
| Point transfer | Same-prefix write E; root copy/return keeps E; disjoint sibling; nested-write DEMAND residual; run-1 demotion; ordinary child read still blocked |
| Normalized C5 | ANY and EXACT demand entry; executable raw preimage; incompatible mark rejection; no summary rekeying inside the query |
| Cleaner lowering | RemoveAll(p) and RemoveAll(p.f); reject terminal AnyField and low-level partial all-mark reaches; selected RemoveMark unchanged |
| Generated forms | Constructor guard also catches generated CallCleaners; existing Spring AT_AND_BELOW remains valid |
| Native records | The three-run helper preserves h; no exact FLOW record or separate covered-exact planner; field E persists on NORMAL STAR records |

These tests must compare facts and layers, not only row counts. The existing
project campaign remains required after implementation; no new project run
is claimed by this proposal.

The constructive model is
[FlowSummaryNormalization.lean](../../spec/lean/proposals/initial-emission/FlowSummaryNormalization.lean).
It proves idempotence and data preservation, the exact finite C5 preimage
test, suffix-preserving helper replay, and the immediate-child write cell.
For that write cell, the normalized NORMAL relation equals the ordinary
excluded write-keep followed by return. It also checks run-1 demotion.
The old Empty-E widening is retained as a rejected counterexample.

The model also checks whole-position cleaner admission and kills. Historical
partial-cleaner counterexamples remain regression evidence, not admitted
behavior. It has 31 checked theorems. The executable check is true. All-theorem axiom audits use only
`propext` and `Quot.sound`. The model does not prove all nested writes,
cleaners, adapters, alias closure, global observation coverage, or whole-run
termination. Complete those integration obligations before implementation.
The unselected entry-widening alternative is not part of this design.

From `spec/lean`:

```sh
lake env lean proposals/initial-emission/FlowSummaryNormalization.lean
```

Commands, model/source hashes, selected cases and complete axiom-audit output
are in [the embedded evidence](../reports/data/bidirectional-flow-summary-normalization-20261029.json).
