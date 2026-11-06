# First-field MUST admission: behavior decision candidate

Status: **Decision received: keep STAR; repair demand guidance.**
Date: 2026-11-06. Evidence commit: `f40e83b52`.

The user selected the guidance repair on 2026-11-06. Keep `emit`, its C2 image,
and the existing admission-layer rules unchanged. The MUST-replacement code
below records an alternative that was not selected. Additive STAR/MUST
emission was not selected either. The active repair must preserve required
demand coordinates and their paired exits through canonicalization and
handoff. Its storage and propagation design remains to be proved and tested.

This candidate preserves a known uniform forward fact when C2 advances exactly
one field from an ANY demand. Current changes that fact to STAR. The candidate
replaces that STAR with MUST and can change concrete admission from DEMAND to
NORMAL. It is a new semantic policy, not an equivalent form of the selected
canonicalization optimization. It does not establish recovery of Conductor's
final missing findings.

The [proof guide](../../spec/proof-guide.md) requires the intended major behavior
to be selected before implementation. The code below makes that decision
reviewable. Local shape/image arguments and a model plan are prepared; Lean
proofs and the global required-effect argument remain pending.

## Current rule and candidate

`MUST` means `Tail.ANY_TAINT`; `MAY` means `Tail.ANY`. `E` is the exclusion set
owned by a STAR or MUST head. A fact is a native scalar leaf, not a packet header.
Let `d` be the normalized demand, `p = d.fact.path`, `q = actual.fact.path`, and
`end = firstFieldEnd(d.fact.base, p, q)`. The changed branch is strict
`q.startsWith(p)`, after the equal-path branch, with `d.fact.tail == ANY`.

All existing guards remain: valid demand, equal base, mark compatibility, field
budget, suffix admission, legal initial, group binding, and static anchoring.
The new condition is `direction == FORWARD && end == q.size && actual.tail == MUST`.

| Guard/input cell | Current tail / E | Candidate tail / E |
| --- | --- | --- |
| Forward ANY demand, terminal first-field MUST actual | STAR / empty | MUST / actual E |
| Same, but actual head is deeper: `end < q.size` | STAR / empty | Unchanged |
| Backward | Existing result or rejection | Unchanged; no backward MUST |
| Concrete terminal EXACT actual | EXACT / empty | Unchanged |
| Other EXACT actual | STAR / empty | Unchanged |
| MAY or STAR actual | STAR / empty | Unchanged |
| Equal paths or actual ancestor of demand | Existing rule | Unchanged |
| STAR demand, including run-2 special behavior | Existing rule | Unchanged |

The result keeps `q.take(end)` and the existing rendered mark. Copy actual E at
that head. Do not move E to the demand prefix or merge it with demand-prefix E.
The rule applies to every forward run and owner; it has no Conductor selector.

`admissionLayer` stays unchanged. Its result changes because MUST has a different
intrinsic layer from concrete STAR:

| Rendered mark / actual layer | Current STAR layer | Candidate MUST layer |
| --- | --- | --- |
| FLOW / NORMAL | NORMAL | NORMAL |
| FLOW / DEMAND | NORMAL | NORMAL |
| Concrete FULL / NORMAL | DEMAND | **NORMAL** |
| Concrete FULL / DEMAND | DEMAND | DEMAND |

The FLOW support rule is existing behavior. The concrete NORMAL cell is a major
new effect: provisional STAR work becomes normal uniform work. Group guides can
bind to FULL atoms under the existing catalog rule; no group initial is added.
Tail and E already participate in initial identity; layer stays outside it.

## Exact two-function change under consideration

In [RestrictedInitialPolicy.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/RestrictedInitialPolicy.kt),
replace only the strict-descendant demand-ANY branch of `emit`:

```kotlin
Tail.ANY -> {
    val end = firstFieldEnd(d.fact.base, p, q) ?: return null
    if (direction == Direction.FORWARD && end == q.size &&
        actual.fact.tail == Tail.ANY_TAINT) {
        result(q.take(end), Tail.ANY_TAINT, actual.exclusion)
    } else {
        val tail = if (mark is MarkSlot.Concrete &&
            actual.fact.tail == Tail.EXACT && end == q.size)
            Tail.EXACT else Tail.STAR
        result(q.take(end), tail)
    }
}
```

Replace only the final strict-new-field return in `canEmitInitial`:

```kotlin
val end = firstFieldEnd(d.fact.base, p, q) ?: return false
if (end != q.size) return false
return when (initial.fact.tail) {
    Tail.ANY_TAINT -> direction == Direction.FORWARD
    Tail.STAR -> initial.exclusion == ExclusionSet.Empty
    Tail.EXACT -> initial.exclusion == ExclusionSet.Empty &&
        initial.fact.mark is MarkSlot.Concrete
    Tail.ANY -> false
}
```

Earlier image guards, including `legalInitial`, remain. The new MUST image cell
must allow nonempty E. Keep the old STAR image: an actual STAR still supplies an
executable witness for it. `canStoreInitial` needs no direct edit; it delegates
to `canEmitInitial` plus `insideDemand`. Keep its FLOW EXACT-to-stored-STAR raw
preimage exception. Self-emission is not a replacement for the image predicate.
No constructor, API, interner, transfer, or summary-normalization change is proposed.

## Effects that require review

This is **replacement**, not additive emission. A changed leaf/demand cell loses
its old STAR initial. Another cell might still emit STAR, but that is not assured.
Observed control B retains STAR and adds MUST in the main witness below because
its frozen demand view differs. The candidate would not reproduce B's whole set.

The shared policy serves method C2 and scoped block/loop C2. New tails, E, and
layers change executable entry facts, summary keys, and C5 acceptance. Prepared
C5 tickets and direct restriction must use the same image and retain the paired
exit, port, layer, protection, and budget rules. FLOW EXACT normalization stays
unchanged; MUST and its E remain intact.

Existing native MUST summary reads require uniform support. Exact memberships,
STAR memberships, or a MUST packet header alone cannot satisfy a FLOW MUST
premise. Field reads can retain MUST/NORMAL where STAR loses correlation and
becomes MAY/DEMAND. Excluded holes, mark gates, and protected memberships must
survive. Native reverse-read views do not authorize stored backward MUST facts.

Caller, selected-summary, and link layers still join at application. A
`NormalTarget` requires a NORMAL result. A FLOW NORMAL seed must not turn an
actual or link DEMAND fact into a normal report. Concrete MUST/NORMAL may expose
new source, sink, request, and normal-summary effects; these need explicit checks.

Loop observations include adjacent/repeat entries, scoped labeled admissions,
and enclosing C5 results. They can change, so output restriction can retain a raw
fact that Current cuts. Recheck the certified MAY-cut path against the new
baseline observer and compare its fallback. No loop code edit is needed for
these semantic effects. Do not mix policy versions in one run or cache context.

## Negative cases and proof work

| Case | Required limit/check |
| --- | --- |
| `root.ANY` demand, actual `root.f.g.MUST/T` | Keep `root.f.STAR`; `root.f.MUST` would invent sibling support. |
| Actual `root.f.MUST/T`, E `{g}` | Keep the hole below `f`; do not drop E or hoist it to `root`. |
| Mixed packet: exact T, uniform U | Only the U scalar membership can trigger this rule. |
| Backward, MAY, EXACT, same path | Preserve the current rule and support layers. |
| Static anchor or Element | Retain static grammar; count Element; test native uniform meaning. |
| Non-counted suffix after first field | Full endpoint equality is required, not equal counted depth. |
| Group/mark exclusions, ZERO, field limit | Retain all legality and budget guards. |

No local shape counterexample was found under the complete endpoint guard and
legal native leaf grammar. That source argument is not a completed proof.

**Proof/model plan: PREPARED; implementation and Lean proofs: PENDING.** Extend
the scalar initial-emission and demand-relative C2/C5 models with a forward
child-MUST constructor, E, typed field/static/element constraints, and executable
actual witnesses. Prove emitted-to-image and image-to-legal-witness directions,
inside-demand storage, paired C5 parity, and raw-layer preservation. Recheck
native summary geometry and loop query factoring. Use constructive proofs with
no classical axioms or `sorry`. No new Lean theorem is claimed by this document.

**Global required-effect preservation: OPEN.** Prove that each required effect of
the removed STAR is redundant or preserved by a stated refinement route through
the next iteration. Cover one packet, protection, and both arrival orders.
Fact inclusion, a justified MUST seed, and a complete C5 image do not close this
obligation. Native tests must cover E, N/D matrices, NormalTarget, block/loop
observations, certified/fallback parity, and the unchanged negative cells.

## Evidence and intended-contract options

The [upstream Conductor report](../reports/bidirectional-conductor-upstream-admission-20261106.md)
at `f40e83b52` records query `2d4642a06869395d21b1a14a86f54d47f4eeede366566207f111787138675a6e`:
same NORMAL `arg0.<WorkflowModel.workflowDefinition:WorkflowDef>.MUST/Graal` actual
at `WorkflowExecutorOps.createAndEvaluate(WorkflowModel)`, E empty, native uniform
membership verified. Current returns STAR/FLOW N and STAR/Graal D. B also returns
MUST/FLOW N; B later uses its local ID 4784 as the ROOT premise into
`createAndEvaluateWithLock`. The frozen B2 row was not captured; the root-ANY
policy explanation is inferred from source, not an observed row attribution.

Both captures reached/completed/accepted **4/3/3** at native run-4 START. There
are 5,025 matching positive queries and 181 returned-set differences. Current has
12,558 valid events; B has 15,418 before attempted sequence 15,419 hits the total
output cap. B absence is unknown. These are not full-run quality/performance results.

The [uniform reproducer](../reports/bidirectional-uniform-prefix-refinement-reproducer-20261106.md)
matches the operation: STAR/FLOW reads to MAY/D; MUST/FLOW reads to MUST/N.
Current first reports at run 5, B at run 3; both naturally converge at run 5 with
one finding. This proves delay, not permanent loss or final Conductor causality.
The candidate does not cover the original EXACT source or deeper STAR/MAY cases.

| Possible intended contract | Benefit | Cost/open obligation |
| --- | --- | --- |
| Preserve known MUST by replacement | Keeps actual uniform support without a second seed | Removes STAR effects; changes concrete normality, C5, and loop observations. |
| Keep STAR and repair demand guidance | Keeps current C2 first-field contract; can retain a same-head guide | Must design B2 guidance/retention and its scope, cost, C2/C5 image, and progress proof. |
| Emit MUST plus STAR | Retains coarse seed while adding uniform work | Changes scalar emission contract, identity/work counts, image and loop observations; still needs effect/normality proof. |

The selected row is **Keep STAR and repair demand guidance**. Do not implement
either MUST-replacement snippet or an additive admission policy. Preserve this
analysis as the explanation of the alternatives and their semantic effects.
