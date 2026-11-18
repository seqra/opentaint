# Run-2 STAR relay after run-1 abstraction

17 November 2026. Synthetic data-flow reachability. FULL marks.
Proposal and proof update. Production is unchanged.
Latest reached iteration in the repaired example: **run-3**, natural completion.
Follow [proof-guide.md](../../spec/proof-guide.md).
This delta is part of the [consolidated approach](bidirectional-demand-termination-approach-20261115.md).

## 1. Cause and selected change

Run-1 does not record field exclusions. A write to `p.f` therefore turns
`p.* / FLOW` preservation into DEMAND. Run-2 must learn the NORMAL relation
with the real exclusion `{f}`. A wrapper can submit exactly the STAR query
that it started from that DEMAND. Rejecting this relay loses the relation.
Increasing the field limit does not fix this same-head rejection.

**Major semantic change:** in run-2, disable the same-head STAR-to-STAR C2
rejection for precise STAR demand. This applies to FLOW and concrete FULL
marks. Use the existing base, directed mark, grammar and field-budget gates.
It is a phase rule for run-1's handoff, not a method- or field-specific rule.
The existing run-2 deeper-actual requested-STAR case also stays active.

| Entry demand, same head | Actual STAR, before | Actual STAR, new run-2 | Run-3 and later |
|---|---|---|---|
| STAR / FLOW | no start | STAR / FLOW, NORMAL hypothesis | old rejection |
| STAR / T | no start | STAR / T, DEMAND, plus STAR / FLOW, NORMAL hypothesis | old rejection |
| EXACT / T | no start | no start | old rejection |
| MAY, NE or MUST | existing table | existing table | existing table |

These starts are identities. A structural FLOW hypothesis proves no actual
concrete mark. Application retains the actual binding and joins its layer;
a DEMAND caller cannot become NORMAL through this rule. Backward MUST
remains invalid. No cleaner, write, read, alias, static, ND, Target, source
permission or summary-application rule changes.

## 2. C2 and C5 must use the same policy

```text
emit(run, direction, demand, actual):
    if run != 2 or direction != BACKWARD
       or demand.tail != STAR or actual.tail != STAR
       or demand.path != actual.path:
        return previousCompleteC2(run, direction, demand, actual)

    if not existingBaseMarkGrammarAndBudgetChecks(demand, actual):
        return {}

    d = existingSelectorNormalization(demand)
    family = { identity(d.path, STAR, d.mark, d.E,
                        layer = NORMAL if d.mark == FLOW else DEMAND) }
    if d.mark is concrete:
        family += sameGeometryFLOWCompanion(layer=NORMAL, mx={})
    return existingUnchangedHeadActualExclusionMap(family, demand, actual)

restrict(rawInitial, conclusion, ownDemandRow):
    require rawInitial in completeRawImage(emit, ownDemandRow.Dc)
    normalize FLOW EXACT to STAR by the existing rule
    result = existingOutputIntersection(conclusion, ownDemandRow.Dp)
    return existingNormalizeAndCut(result,
                 min(globalLimit, FL(ownDemandRow.Dp)+1))
```

The complete image is over legal offers, not only observed caller inputs.
The new STAR offer is its own executable C5 witness. This is needed even
when the demanded head already reaches the field cap: there need not be
room for a deeper offer. Test the raw initial before normalization. A public
STAR key from an EXACT probe is not a raw STAR witness.

Use this common policy in method calls and generated block admission and
restriction. Update prepared plans, image tests and any equivalent cached
predicate together. Do not change only callee `startInitials` while keeping
a stale caller plan or C5 image.

Keep the existing E policy. A FLOW/STAR selector has Empty E. Concrete
selectors retain their demanded E. In a concrete family, the existing map
copies actual E to an empty-E STAR initial at exactly the actual head,
including its FLOW companion. Do not move holes to a shorter path or add a
new FLOW-only E-copy rule. Actual E, mx and H remain on the existing binding
and resume path. Plain and protected memberships remain separate.

## 3. Complete reference trace

`N/D` are layers. `F` is FLOW. `ret` denotes the return position. `f != g`.
Run-1 is unchanged; its exact source and both helper DATA rows are shown in
[the historical counterexample](../reports/bidirectional-nested-star-soundness-gap-20261117.md).

```java
// RUN-1, forward, limit 1. Demand: unrestricted; submitted/initial: ZERO,N.
void main() {
    Box a = new Box();
    markG(a);                   // Assign T at a.g.$, NORMAL.
    Box r = wrap(a);             // Returned r.g.$/T, DEMAND.
    observeG(r);                // DEMAND witness.
}
// Summaries: ZERO -> DemandTarget,D; ZERO -> ZERO,N.

// Submitted: p.g.$/T,N. Initial: p.*/F,N.
Box wrap(Box p) {
    Box r = overwrite(p);       // Submit p.*/F,N.
    return r;
}
// Summaries: p.*/F -> ret.*/F,D; p.*/F -> p.*/F,D; ZERO -> ZERO,N.

// Submitted: p.*/F,N. Initial: p.*/F,N.
Box overwrite(Box p) {
    p.f = new Box();            // E stays empty; preserving edge becomes D.
    return p;
}
// Summaries: p.*/F -> ret.*/F,D; p.*/F -> p.*/F,D; ZERO -> ZERO,N.
```

```java
// RUN-2, backward, limit 1. Summaries above bodies.
// main: ZERO -> DemandTarget,D through the existing source/Target route.
void main() {
    Box a = new Box();
    markG(a);                   // Backward a.g.$/T can now reach this rule.
    Box r = wrap(a);
    observeG(r);                // Seeds r.g.$/T,N.
}
// Demand: (Target; ZERO). Submitted/initial control: ZERO.

// Published: ret.*/F -> p.*/F {f},N; ZERO identity as admitted by control.
Box wrap(Box p) {
    Box r = overwrite(p);       // Submit ret.*/F,N to overwrite.
    return r;
}
// Demand pairs (Dc; Dp): (ret.*/F; p.*/F), (p.*/F; p.*/F).
// Submitted: ret.g.$/T,N. Initial: ret.*/F,N (old deeper-actual case).

// Published: ret.*/F -> p.*/F {f},N; ZERO identity as admitted by control.
Box overwrite(Box p) {
    p.f = new Box();            // Strong backward keep adds real E={f}.
    return p;                  // Backward: ret.*/F,N -> p.*/F,N.
}
// Demand pairs (Dc; Dp): (ret.*/F; p.*/F), (p.*/F; p.*/F).
// Submitted: ret.*/F,N. Initial: ret.*/F,N (NEW same-head relay).
```

The argument-entry pair does not match the return offer. C5 uses the return
pair's own p output selector. It keeps `{f}` and NORMAL. The wrapper applies
the reply and publishes the same exclusion-guarded relation.

```java
// RUN-3, forward, limit 2. Demand: control route; submitted/initial: ZERO.
void main() {
    Box a = new Box();
    markG(a);                   // a.g.$/T,N.
    Box r = wrap(a);             // Saved NORMAL replay: r.g.$/T,N.
    observeG(r);                // NORMAL witness.
}
// Published: ZERO -> NormalTarget(id),N; no outgoing refinement demand.
// Natural completion at run-3. The NORMAL observation stays retained.

// No current DATA demand/initial. Submitted: p.g.$/T,N; saved replay first.
Box wrap(Box p) {
    Box r = overwrite(p);
    return r;
}
// Current DATA summaries: none needed.
// Saved reverse: p.*/F {f} -> ret.*/F,N. Return ret.g.$/T,N to caller.

// No new invocation/current initial needed; wrapper uses its saved record.
Box overwrite(Box p) {
    p.f = new Box();
    return p;
}
// Saved reverse: p.*/F {f} -> ret.*/F,N.
```

The saved record rejects `p.f.$/T`, which was overwritten. It preserves
`p.g.$/T`. A DEMAND g offer produces a DEMAND result. An arbitrary finite
number of transparent wrappers retains the same NORMAL relation; it does
not require a new field limit or a full suffix-evidence product.

## 4. Proof and workload limits

[Constructive package](../../spec/lean/proposals/run2-star-relay-20261117/README.md):

- The only new cell has run=2, backward direction, two STAR tails and the same head.
- All old C2 members and paired C5 results remain. New raw C5 members have executable offer witnesses.
- Wrong base/mark, excluded marks, zero budget, exact demand and backward MUST still reject as specified.
- A new family has at most two starts, with the requested head. Both entry field caps hold, including at the global cap.
- The trace computes the strong-write summary, own-row C5, arbitrary wrapper depth and precise g replay. The f and DEMAND-layer controls prevent unsound confirmation.

This repair can add run-2 work. Deduplicate the ordinary initial and summary
keys. It adds no new tail, field, key label, archive, cross-call evidence,
field-cap exception or unrestricted traversal. Run-1 and run-3 onward are
unchanged functions of their inputs; the additional run-2 summaries can
change later frontiers. Thus, earlier local termination and service proofs
remain valid in their stated scopes. Equal whole-program run counts for
all earlier examples do not follow from this local fact alone.

These are local admission/C5 and prefix-write/wrapper proofs. The native
adapter checks a cold example; it does not install the full consolidated
proposal. General G1–G4 obligations in the
[soundness audit](bidirectional-demand-termination-soundness-audit-20261117.md)
remain open. No whole-analyzer soundness or universal termination claim is made.


Validation: **36 new constructive Lean claims**; **7,160 cumulative audited
claims in 412 hash-checked modules**. **65 targeted native tests pass**.
The repaired nested case has one NORMAL observation at natural **run-3**.
The overwritten-field control has zero NORMAL observations at run-3; the
historical rejection control has zero findings at run-3. The no-write
control completes at run-1. No hard iteration cutoff is used as proof.
