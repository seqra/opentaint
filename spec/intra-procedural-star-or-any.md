# Intra-procedural STAR_OR_ANY

Date: 7 November 2026. Status: withdrawn design; historical prototype evidence only.
Language: ASD-STE100 Simplified Technical English.

The user rejected new tail kinds and selected a return to the
[pre-implementation subsumption baseline](subsumption-redesign-baseline-20261107.md).
Use the [principal examples](subsumption-principal-examples-20261107.md) for
the new combined design. The STAR_OR_ANY rules below do not authorize a new
implementation. Their former selection, proof and test history remain here
as evidence. Runtime prototype source has not been changed by this reset.

The user selected FULL initial conversion, then selected a special
`star-or-any` tail to close the nested-call gap. This spec defines that tail.
It applies to FLOW and full concrete marks in restricted runs. It does not
change run-1 mark mode, field limits, rule transfer or ordinary STAR admission.

The [initial audit](../docs/design/bidirectional-star-initial-emission-audit-20261107.md)
records the two old MAY emitters. The
[nested-call report](../docs/reports/bidirectional-star-initial-nested-calls-20261107.md)
records the failed plain-STAR conversion: current policy reports four cases;
the plain-STAR copy loses three wrapper cases. Both stop at run-3. The earlier
original loop case passes the plain-STAR copy at run-5; it is not sufficient
coverage for this design.

## 1. Meaning and selected semantic changes

Write `S?` for `Tail.STAR_OR_ANY`. Ordinary `*` is STAR, `[any]` is MAY,
`[any-taint]` is MUST, and `$` is EXACT. `F` is FLOW; `T` is a full mark.
`N` and `D` are NORMAL and DEMAND. E is the field exclusion.

```text
dataTail(S?) = STAR
dataTail(t)  = t, otherwise

storedTail(S?) = STAR
storedTail(t)  = t, otherwise
```

`S?` has STAR's correlated suffix meaning. It does not mean uniform taint.
Its extra capability is in initial admission. A live S? input can use the MAY
admission cells which reject an ordinary STAR input. The marker is semantic
analyzer state, not compiler metadata which can be erased from equality.

| Mechanism | Current | Selected |
| --- | --- | --- |
| Two C2 MAY output cells | Emit MAY initial/start, D | Emit S? initial/start: F is N, T is D |
| Nested admission from that start | Ordinary STAR replacement would be rejected | S? can use MAY-demand admission while ordinary STAR keeps its old rule |
| Intraprocedural transfer | Existing four tails | S? uses STAR geometry, E, mark and layer behavior; preserve the marker on correlated transport |
| Summary interface | No S? kind | Normalize S? to STAR in every premise member and conclusion before C5/storage/publication |
| Point storage | No admission marker | Preserve S? capability, including fresh deltas and both arrival orders |

Keep ordinary source/cleaner/sink rules, complete ND conditions, protection,
pass rules, alias effects, static handling, physical ports, normal Targets,
the field-limit schedule, demand-relative C5 and stopping rules unchanged.
Do not add grounding support, request propagation, an input archive, a new
mark token, a new alias rule or another cache manager.

## 2. Where S? can exist

S? is allowed in live intra-procedural Facts and raw InitialAp keys. These
include method/block point stores, initial commands, caller inputs retained
for summary application, local loop state and scoped normal-rule contributor
inputs. A contributor remains an intra-procedural point input even when the
existing store retains it for a later run; this spec adds no new erasure there.

S? is forbidden in published or stored method/block summaries, public Target
premises, persistent NORMAL records, and every stored demand endpoint.
Source/sink/field micro-edges do not mint it. Rule permissions retain their
compiled edge identity. Run-1 emitters keep their existing tails.

An interner may hold both raw S? and canonical STAR keys. It does not mutate
either key. A raw initial is not itself a published summary premise.

## 3. Initial emission

Keep all current base, mark, counted-field budget, static-anchor, ZERO and
direction checks. Demand E remains normalized as now. An S? actual must
also pass the original STAR/E reachability check: an excluded field cannot
become reachable merely by trying a MAY admission view.

For an ordinary actual, apply the old C2 selection. Replace an emitted MAY
tail with S?. Other old outputs stay unchanged, including ordinary first-new-
field STAR and terminal concrete EXACT. MAY facts themselves remain MAY.

For an S? actual, keep STAR behavior where STAR admission works. For a MAY
demand where that view rejects, try the MAY admission cases, subject to the
original STAR/E reachability guard. This gives STAR behavior plus the selected
MAY-demand capability; it does not admit an ordinary STAR actual.

Preserve S? when that actual drives a STAR/MAY initial output. EXACT or MUST
outputs retain their own tail. This inheritance is needed when a selected
first-field initial is passed through another wrapper.

```text
emit(d, actual):
    check existing base/mark/budget/grammar guards
    if actual.tail != S?:
        raw = oldEmit(d, actual)
        return raw with MAY output changed to S?

    if the demanded descendant is excluded by actual's STAR/E:
        return nothing
    raw = oldEmit(d, actual viewed as STAR)
    if raw is absent and d.tail == MAY:
        raw = oldEmit(d, actual's MAY admission view)
    if raw.tail is STAR or MAY:
        return raw with S? tail
    return raw
```

This is a scalar selection, not two independently propagated initials. The
actual Facts and its E are not mutated to make the virtual MAY view.

| Added fact | Demand | Emitted raw initial/start |
| --- | --- | --- |
| `x.[any]/T, D` | `x.[any]/F` | `x.S?/F, N` |
| `x.[any]/T, D` | `x.[any]/T` | `x.S?/T, D` |
| `x.[any]/T, D` | `x.f.[any]/T` | `x.f.S?/T, D` |
| `x.S?/F, N` | `x.[any]/F` | `x.S?/F, N` |
| `x.S?/T, D` | `x.[any]/T` | `x.S?/T, D` |
| `x.f.g.S?/T, D` | `x.[any]/T` | `x.f.S?/T, D` |
| `x.S?/T, E={f}, D` | `x.f.[any]/T` | nothing |
| `x.[any]/U, D`, U != T | `x.[any]/T` | nothing |
| `x.*/F, N` | `x.[any]/F` | nothing, unchanged |

Every supplied path must fit the current budget. This table does not allow
an over-budget actual. MUST and exact global class markers keep their rules.
S? starts with STAR intrinsic layers: FLOW N, concrete D. Preserve the current
actual support/loss rule on unrelated EXACT outputs.

## 4. Transfer and summary application

Use STAR reachability and E behavior. A move, field prefix operation or STAR
summary which transports the actual suffix transports S? too. A real limit
cut emits MAY/D as now; it does not preserve the marker on the cut result.
An operation whose result is explicitly EXACT, MAY or MUST keeps that result.

```java
// Backward submitted ret.[any]/F; raw initial/start ret.S?/F, N.
Object wrapG(Object p) {
    Object tmp = getG(p);
    // Backward: tmp.S?/F, N -> bound callee ret.S?/F, N.
    // Callee's ret.[any]/F demand now admits ret.S?/F, N.
    return tmp;
}
// Stored backward summary, after normalization: ret.*/F -> p.g.*/F, N.

// Backward raw initial/start ret.S?/F, N.
Object getG(Object p) {
    return p.g;
    // Backward raw result p.g.S?/F, N. Limit 1 fits g.
}
// Stored backward summary: ret.*/F -> p.g.*/F, N.
```

Applying that stored STAR summary to an S? actual preserves the actual S?
tail. Normalizing the summary does not normalize the caller's offered Facts.
Applying it to MAY/D still yields MAY/D. It does not confirm uncertain input.
Current/saved/opposite matching roles remain unchanged; S? uses STAR geometry
for those roles, including the strict-ancestor restriction.

## 5. Normalize the complete public relation

```text
normalize(P -> C):
    P' = map every initial member: S? -> STAR
         rebuild the premise with existing ZERO/dedup/singleton rules
    C' = map S? -> STAR, preserving paths, marks, E, layer and literal H
    apply the existing complete FLOW EXACT -> STAR normalization
    return the same labelled interface with P' -> C'
```

Normalize before native/prepared C5 and publish the same normalized P used by
storage. A rekey inside a result-only store is insufficient. Normalization
applies to NORMAL and DEMAND, singleton and ND, method and block summaries.
Target summaries normalize P before duplicate/acceptance/storage checks;
the Target value and report ID stay unchanged.

The raw emission image and stored image differ. `canEmitInitial` recognizes
actual raw outputs, including S?. `canStoreInitial` recognizes normalized
STAR through a valid raw S? preimage, plus the current raw STAR and normalized
FLOW EXACT cases. It keeps the existing inside-demand and paired-exit tests.
Do not use self-emission as an image classifier.

The shared run-2 static carry is a virtual family of paired same-position,
same-mark rows. C5 must select a row which accepts the normalized premise.
It must not assume that the stored STAR tail was the original C2 demand.
At a one-field budget, a concrete S? initial can come from a MAY carry row,
while the public STAR key has no requested-STAR witness. Use the direct carry
row first. If it rejects a stored STAR key, test the existing same-position
MAY/MAY row with `canStoreInitial`. Select that row only if the check passes.
Keep actual fields, E, marks, layer and literal H unchanged. This is a C5
adapter correction; it does not add a row to storage, change ordinary C2 or
select either open handoff/repeat policy in section 8.

Demand builders normalize every DATA endpoint before ownership/dedup. Frozen
records, static guidance and block handoff validate that S? did not leak.
Raw run-1 static writer bindings are not rewritten; restricted S? minting
does not occur there. Rule-derived seeds keep their existing edge identities.

## 6. Storage and loop observations

Keep raw S? in point and initial identity. Do not let plain STAR or MAY
coverage discard it. For the same coordinate, stored STAR followed by S?
must produce the new capability as a fresh delta; the reverse arrival order
must retain S?. Keep literal protected tail/E coordinates and the selected
guide-position laws. No new protected subsumption is allowed.

Distinct tail headers are the initial representation. Any later cross-header
merge requires proof that all future C2 effects remain. An unsupported packed
S? case uses the existing scalar fallback, preserving tail, E and H.

Loop admission observations retain raw S? answers and their exact labels.
Enclosing C5/Target observations use normalized public forms. Adapt the fast
certificate to the exact new emission/layer, with a constructive earlier-cut
witness proof. Retain the complete trial fallback if no certificate applies.
Do not change the growth test or consumer families.

## 7. Required proofs and native gates

The old 26-law audit and the 12-law joint/certificate supplement concern the
plain-STAR prototype. They do not prove this new kind or whole-program safety.
The [portable new models](lean/proposals/initial-emission/STAR_OR_ANY.md) have
39 checked local laws: the 29-law model includes arbitrary-count wrapper
induction; the 10-law supplement covers geometric ND deduplication, earlier
MAY-cut certificate witnesses and exact SOA capability frontiers in both
arrival orders. These are local algebra and policy results. They do not prove
native ND rebuilding, complete C5, native loop-trial equality, point-backend
freshness, producer arrival or whole-program soundness and progress. The
design must prove, within the stated scope of each result:

1. STAR data geometry, E reachability and suffix correlation are preserved.
2. The new raw emission image has executable input witnesses; normalized
   stored STAR has the correct raw preimages and paired C5 behavior.
3. FLOW/concrete layers and unrelated exact-loss support remain correct.
4. Summary normalization removes the marker from all P/C/ND/Target forms
   without changing their data relation, flags, labels or report IDs.
5. Point admission preserves the marker capability in one packet and both
   arrival orders. Data inclusion alone does not prove this property.
6. STAR summary application preserves a live actual marker and actual support.
7. Any finite chain of plain wrappers retains the required admission ability.
8. Loop observer equality/certification uses the correct raw/public forms.

Use constructive Lean, then native TDD. Keep the original loop/getter program,
the four nested cases and exact/descendant negative controls. Add concrete-
mark wrappers, excluded-field rejection, normalized ND/Targets, contributor
replay, packed/scalar agreement and boundary no-marker assertions. No manually
supplied summary/demand/initial may stand in for full-program recovery.

Global source/sink and progress claims remain unproved until their stated
model and native scope is checked. The known plain-STAR wrapper regression
must become green before a core patch lands. Follow with the four fixed
project experiments and report all reached/complete/accepted run labels.

## 8. Open handoff gap

The first full native gate found a required loop finding which this contract
loses. A backward concrete S? DEMAND relation becomes a public STAR relation.
Its next forward STAR demand rejects a deeper exact actual after run-2.
The marker's local C2 capability therefore does not suffice across handoff.

The [native report](../docs/reports/bidirectional-star-or-any-handoff-gap-20261107.md)
contains the code, facts, physical ports and evidence. The two-loop case ends
at run-3 without its required finding. A separate deep-loop test ends at
run-5 without its required finding.

In that second case, repeat C2 has no DATA answer for `x.f.f.f.$/T, N`, but
the same repeat scope has a saved NORMAL `x.f.*/FLOW -> x.*/FLOW` relation.
The existing growth gate records two empty-observation drops. Its saved
consumer view covers adjacent scopes; it does not observe that repeat row.
The post-run queries and source trace do not prove a complete repair. The
required saved-repeat behavior is a separate pending choice. Do not silently
add a consumer family or change the growth test.

The portable checker also checks eight **counterexample** laws. They model
this next-admission loss; they are separate from the 39 selected local laws.
Neither set proves global analyzer progress. Keep the positive finding tests
strict. A behavior choice must close the handoff gap before this patch lands.
Do not silently change ordinary STAR demand admission or the public
normalization rule to make the gate pass.
