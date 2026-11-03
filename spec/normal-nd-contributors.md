# Keep NORMAL contributors to ND rules

Date: 3 November 2026. Status: selected correction; implemented and native
checks pass. Project quality and performance checks remain pending.

## 1. Scope

An ND rule needs more than one condition fact. A completed run can prove
some of these facts with NORMAL edges. Keep these edges at the condition
point. A later forward run can use them in the same rule join.

This changes the lifetime of NORMAL condition evidence. It does not change
ZERO admission, C2 initial emission, C5 summary restriction, field transfer,
source permissions, or Target composition. Do not implement the separate
`forward-internal-zero-control.md` draft as part of this correction.

The same rule applies to conditional sources, conjunctive transfers, and
sink conditions. Keep an accepted NORMAL leaf even if its full condition
does not complete. Do not keep DEMAND leaves. Do not keep the compiled
predicate, a method actor, a call plan, or a callback.

## 2. Current and new behavior

Current behavior:

```text
run-1, at sink:
    ZERO -> session.$/SESSION    NORMAL
    I    -> param/DATA           DEMAND
    joined result: I -> DemandTarget

freeze:
    discard all local condition supports
    persist NORMAL outputs only at block exits

run-3, at the same sink:
    param.$/DATA                 NORMAL
    no SESSION contributor
    no sink result
```

New behavior:

```text
run-1, at sink:
    keep the accepted NORMAL ZERO -> session.$/SESSION leaf
    emit I -> DemandTarget as before

run-3, when current DATA satisfies a sink leaf:
    restore the saved SESSION leaf in this sink's local join
    join it with current param.$/DATA
    emit param.$/DATA -> NormalTarget(id)
```

The saved SESSION fact is not sent through the CFG. Its source rule does
not run again. There is no new ZERO initial and no new ZERO demand.

## 3. A saved contributor is a conditional edge

Keep the complete original premise. In this example, the saved premise is
ZERO. In general, it can contain one or more nonzero facts.

```text
saved:   P -> x.$/T       NORMAL
current: Q -> y.$/U       NORMAL
rule:    CM(x,T) AND CM(y,U)

result premise: union(P, Q)
```

Do not replace P with ZERO. Do not erase any member of P. The ordinary
caller join must satisfy every member of the resulting ND premise.
No actual-input rebinding is needed to reuse this conditional relation.

```java
void check(Object p, Object q) {
    sinkBoth(p, q); // CM(p,T) AND CM(q,U).
    return;
}
// A saved p/T contributor cannot make a caller with only q/U report.
// The resulting summary still requires both p/T and q/U.
```

## 4. Storage and ownership

The persistent key contains:

```text
analysis owner / configuration
method context
block ID and physical entry port
mark mode
physical instruction and operation stage
boundary/cleaner phase, where applicable
rule occurrence or stable legacy rule shape
predicate leaf index
```

The operation key names a semantic observation point. A call sink is
observed at BOUND. Two outgoing stages from BOUND can have different
array ordinals but still observe the same sink; use one BOUND key for
them. Keep the actual request/resume address unchanged. Other rule stages
keep their distinct identities.

The live FULL condition joins must use this same point ownership. Their
old rule-plus-statement key alone does not separate two source stages.
Use the semantic point to namespace these joins, including run-1 origin
joins. Do not change the separate call-summary E6 join. Keep GROUP's live
join behavior unchanged. Production lowering already gives a source
occurrence one source stage; the explicit key also prevents a reused
manual occurrence from joining across two distinct phases.

The value is a set of accepted inputs:

```kotlin
data class NormalContributor(
    val premise: PremiseKey,
    val facts: Facts, // NORMAL; includes geometry and protection metadata.
)
```

Keep the accepted condition image, not the untested incoming fact. Preserve
its full mark, tail, paths, exclusions, and protection. Merge only with
the existing AP union operations. A source, sink, or transfer at another
location cannot read this evidence. A physical operation's transient
`FormOwner` must not make its address change between runs.

Workers read the snapshot from earlier completed runs. Each method actor
collects its new NORMAL contributors locally. Publish them only at a
successful completed forward-run barrier. Failed and cancelled runs do
not publish partial evidence. Backward runs do not restore or add forward
contributors. Implement this correction for FULL mode. GROUP capture and
restore stay disabled; its previously recorded issues remain outside this
correction. Keep mode in the key and never read GROUP evidence as FULL.

## 5. Processing

Use the current `RulePredicateStore` and `ConjunctionStore`. Do not add a
second condition evaluator.

```kotlin
fun onAcceptedLeaf(rule, site, leaf, input, emit) {
    // This call follows a current MarkCheck.Holds.
    if (firstAcceptedCheck(rule, site)) {
        val ready = mutableListOf<CompleteBinding>()
        for (old in previous.normalContributors(rule, site)) {
            ordinaryJoin.add(old.leaf, old.input) { ready += it }
        }
        // Loading a snapshot alone executes nothing. The current accepted
        // check activates these valid, conditional bindings.
        for (binding in ready) emit(binding)
    }
    if (input.layer == NORMAL) temporary.keep(rule, site, leaf, input)
    ordinaryJoin.add(leaf, input, emit)
}
```

Restore all saved leaves for that rule/site once. Some can complete a
binding before the current input is added. Deliver these ready bindings
at the current accepted check; do not lose them to the ordinary join's
deduplication. A check that matches no leaf cannot activate the cache.

Source-result callbacks keep their current source-permission checks.
Sink callbacks keep complete premise union, layer calculation, existing
NormalTarget suppression, and the existing DEMAND Target rules. Keep
`Triggers.parts` limited to the facts checked from the current input.
Saved leaves are condition evidence, not extra current input packets.

## 6. Required invariants and proofs

1. Every retained input has an accepted NORMAL derivation at the same key.
2. A restored input is the same conditional edge, with all metadata intact.
3. Restoring and adding a current input has the ordinary join outcome for
   that union of accepted inputs, regardless of arrival order.
4. Every output keeps the union of all contributor premises. A mixed cube
   cannot produce an independent ZERO sink arm.
5. A result is NORMAL only when every selected contributor is NORMAL.
6. Restoring one owner, stage, leaf, direction, or mode cannot add evidence
   to another one. Identical facts in two locations do not merge owners.
7. Persistence and restoration create no CFG work, initial, demand row,
   source permission, source hit, or report by themselves.
8. A current accepted rule check can complete the SESSION/DATA example
   without admitting ZERO to the after block.
9. Keeping old conditional nonzero evidence does not remove the caller's
   complete ND-premise check.

The constructive formal model and its audit belong in
`lean/proposals/normal-nd-contributors-20261103/`. Model proofs do not verify
the Kotlin runtime. Native regressions must check the runtime separately.

The [formal audit](lean/proposals/normal-nd-contributors-20261103/checks.json)
passes 55 theorems and 92 audited declarations, with no choice or unproved
axioms. The [native receipt](../docs/reports/data/bidirectional-normal-nd-contributors-validation-20261103.json)
records 2,395 common tests, 453 JVM tests, and 60 harness tests, all passing.
The former SESSION/DATA failure and its controls pass. This establishes
the stated native gate; it is not a four-project quality or speed result.

## 7. Validation

First retain the failing exact-array/unconditional-session native case.
Require it to report under the selected FULL schedule `1,1,2,3,...`.
Keep its no-feedback and conditional-session controls. Add cases for an
incomplete old cube, nonzero conditional premises, DEMAND rejection,
rule/site isolation, source permission checks, and duplicate restoration.

Run the existing common and JVM checks. Then repeat the four selected
projects under task.md. Record the latest reached, completed, and accepted
run iteration. The last native counterexample completed run-3 with no
finding; the last OWASP measurement completed and accepted run-5 with 18
missing identities. These are pre-correction measurements, not validation
of this correction.
