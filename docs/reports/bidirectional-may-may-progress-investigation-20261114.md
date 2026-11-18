# MAY/MAY progress investigation

**Superseded approach:** use
[bounded demand refinement](../design/bidirectional-bounded-demand-refinement-20261114.md).
It keeps both original field bounds and applies a one-field plan in both
directions. The full-guard premise-depth relaxation discussed below is not
part of the replacement. This report preserves the earlier experiment.

14 November 2026. Investigation of the [working goal](../design/bidirectional-may-may-progress-task-20261113.md), under [proof-guide.md](../../spec/proof-guide.md).
Production and the selected [non-empty-MAY specification](../../spec/non-empty-may.md) are unchanged.

**Result:** there is a bounded candidate for the two supplied neutral-FLOW
cycles: partition coarse FLOW queries with guards from retained NORMAL
summaries, and check NORMAL coverage before a relative C5 cut. The reference
reaches a NORMAL finding and an empty frontier after **run-5**. This is a
concept result, not a native engine run or a general termination theorem.

Simply removing the nonempty answer to MAY/MAY is unsafe. The cleaner
example below needs that answer. Increasing only the global field limit
also fails: one cycle has no field cut, and the other has a fixed relative
budget.

## 1. The two causes

The supplied program has no loops, recursion, statics, aliases or ND:

```java
void main(boolean flag) {
    Box a = sourceAtF();        // Assign T at a.f and all descendants.
    Box b = choose(a, flag);
    Box c = choose(b, flag);
    sinkAnywhere(c);           // CM(c.[any], T).
}
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;
    Box q = new Box();
    q.f = p;
    return q;
}
```

Notation: `M` = MAY, `NE` = non-empty MAY, `U` = MUST, `F` = FLOW;
`N` = NORMAL, `D` = DEMAND. A demand pair `[Dc ; Dp]` is in the direction
of the receiving run. Protection and mark exclusions are empty unless
shown. Fields are `f` and `g`; every fact starts with a code variable.

| Owner / operation | Repeated question | Why the limit does not fix it |
| --- | --- | --- |
| Method-only `choose` | `p.M/F` plus actual `p.M/T,D` starts `p.$/F,N` and `p.*/F,N`. The latter reads unknown `f.g` and emits `ret.M/F,D`. Backward `ret.*` through the writer emits `p.M/F,D`. | Neither repeated root MAY result cuts a field. |
| BB version, method boundary | `p.f.U/F,N` through the saved writer gives `ret.f.f.U/F,N`. With paired `Dp=ret.*`, C5 cuts it to `ret.f.NE/F,D`. | `FL(Dp)+1` remains 1. A larger global limit cannot raise it. |
| BB version, next call | That cut submits `p.f.NE/T,D`; C2 starts `p.f.*/F,N`. Saved opposite-direction `p.f.g.* → ret.*` reads unknown `g` and emits `ret.M/F,D`. | A precise saved relation is applied to an unnecessarily coarse query. |

The two losses therefore need different actions. A tail-depth counter does
not eliminate the unknown-read loss. A query partition alone does not stop
the repeated C5 cut of a known NORMAL specialization.

The old MAY/MAY table has no new field to select: its inputs are identical
at every later limit. The proposed additional information is a **retained
NORMAL premise guard**, already available at handoff. It is not the full
suffix that was discarded at an earlier call.

## 2. A failed local fix: answer MAY/MAY with EXACT only

Selected source and cleaner rules:

```text
sourceAtF(): assign T exactly at ret.f.$
cleanRootT(p): remove T exactly at p.$; preserve descendants
sinkAnywhere(x): CM(x.M, T)
```

```java
void main() {
    Box a = sourceAtF();
    Box r = clean(a);
    sinkAnywhere(r);
}
Box clean(Box p) {
    cleanRootT(p);
    return p;
}
```

The run-1 abstraction can publish `p.*/T → ret.M/T,D,protected`.
The FLOW route excludes T. In run-2, the nonexact sink submits `ret.M/T,D`.

```java
// BACKWARD: surviving concrete publication includes
// ret.*/T -> p.M/T,D,protected.
Box clean(Box p) {
    cleanRootT(p);             // ret.$/T branch: killed at p.$.
                              // ret.*/T branch: descendant survivor p.M/T,D.
    return p;
}
// Demand: [ret.M/T ; p.*/T]. Submitted: ret.M/T,D.
// Current initials: ret.$/T,D; ret.*/T,D; ret.*/F,N.
```

The surviving `p.M/T` reaches the real `a.f.$/T` source and gives it
permission for run-3. The next forward admission can start the precise
`p.f.$/T,N`, which the root-only cleaner preserves.

An EXACT-only replacement kills the concrete root query. Its FLOW companion
still excludes T. There is no concrete descendant source hit from these
queries. The Lean check proves this seed/cleaner/source-hit distinction;
it does not claim a newly executed native whole-program regression.

This refutes the proposed removal of the nonempty branch. It does not
authorize changing the selected cleaner semantics or emitting backward
MUST seeds.

## 3. Candidate: partition a coarse FLOW query by known NORMAL guards

Suppose the owner has retained these ordinary NORMAL records:

```text
R: p.f.g.*/F -> ret.*/F, N
W: p.*/F     -> ret.f.*/F, N
```

R is not inferred from repetition. The selected trace supplies a run-3
partial `p.f.* → ret.M,D` row. Its reversal supplies the run-4 pair
`[ret.M/F ; p.f.*/F]`. That pair has output budget 2, which can retain
`ret.* → p.f.g.*,N`. The reference checks this C5 cell directly.

Use the **premises** of retained NORMAL records in the current direction
to build a finite guard trie. For the read record, the guard is `p.f.g`.
Replace the conditional coarse `p.*/F,N` query by:

```text
p.$/F, N
p.*/F {f}, N          # residual: no suffix whose first field is f
p.f.$/F, N
p.f.*/F {g}, N        # residual below f: no next field g
p.f.g.*/F, N          # complete reader guard, not a MUST assertion
```

The braces are **real field exclusions**, using the existing AP meaning.
Here "partition" means an exhaustive finite cover. The point model lets
STAR regions include their head, so the scheduled EXACT queries can
overlap them. No proof depends on disjointness.
There is no separate field-promotion ban. The residuals remain active;
the selected children include their exact root points. A field not in
the guard remains in a residual query and can still produce MAY demand.
For example, an additional unmodeled `return p.h` branch can read `h`
from `p.* {f}` and stays unresolved. Presence of R and W is not treated
as a proof that the method has no other behavior.

For a first query already at `p.f.*`, only its remaining guard is split:

```text
p.f.$/F,N ; p.f.*/F {g},N ; p.f.g.*/F,N
```

The retained NORMAL W covers the writer results of all these queries.
The reader rejects the exact ancestors and excluded residuals. Its last
query produces the correlated NORMAL `p.f.g.* → ret.*` result. Thus no
`p.* → ret.M` projection has to be regenerated by these FLOW queries.

### Explicit semantic changes

| Part | Selected/current reference | Investigated candidate |
| --- | --- | --- |
| Conditional FLOW STAR query from MAY admission | Keep one coarse STAR query, plus existing companions. | Refine it with a complete finite partition derived from retained NORMAL input guards. Empty-E FLOW queries only in this prototype. |
| C2 premise-depth bound | At most one concrete field beyond the incoming demand. | A guarded FLOW query may reach a retained NORMAL guard, still within the global field limit. The model proves that this can exceed the old relative bound. |
| C5 raw entry check | Constructive image of the original C2 producer. | Constructive image of the **same updated prepared C2 plan**. Old C5 cannot reject the deeper queries and still implement this candidate. |
| Publication of a raw NORMAL specialization | C5 may cut it to DEMAND before store subsumption. | If a retained NORMAL provider covers the whole raw transfer and service, omit the duplicate publication before that cut. |

The first three rows are admission changes. This is not a storage-only
optimization. The last row also changes the intermediate demand frontier.
The native provider-service proof is not established by AP geometry alone.

Unchanged: no MAY/NE premises, no new tails, original concrete T admission,
the dedicated forward MUST lane, backward seeds, cleaner/protection rules,
source permission rules, Target rules, call order, and saved NORMAL replay
on the original input. Run-1 is unchanged. No full field evidence is
composed across calls. The candidate does not restore the withdrawn
relational-evidence design.

The BB check includes the MUST-initial case: W applied to `p.f.U/F`
produces `ret.f.f.U/F`. The precoverage implementation must prove this
uniform image as well as ordinary aligned STAR specialization. Checking
only the existing STAR-to-STAR shape rule would leave this BB cut active.

### Algorithm and storage

Use a per-owner trie keyed by scope, ports, direction and NORMAL premise
geometry. It contains references to ordinary retained summaries. The
prototype uses one guard and existing Empty-E conditional FLOW starts.
Concrete queries are left unchanged. Snapshot the retained guard basis
when preparing the plan; do not mutate an already submitted query family.

```text
offer(owner, originalInput):
    applyPersistedNormalSummaries(owner, originalInput)   // existing policy
    if not restrictedForwardRun:
        continueExistingOfferPipeline()
        return
    plan = originalC2(owner.demand, originalInput)
    guards = retainedNormalInputTrie(owner)

    refined = []
    for q in plan:
        if q is an Empty-E conditional FLOW STAR query:
            // Split only guards that fit the global limit. Otherwise keep q.
            // At each trie node: exact point, excluded residual, child cones.
            refined += partitionByGuards(q, guards, globalLimit)
        else:
            refined += q

    prepared = deduplicate(refined)                      // original-input binding
    for q in prepared:                                  // EXACT-first locally
        analyzeOwner(q)

    onRawSummary(q, result):
        // Exit observations have already run. No unrestricted result is stored.
        if eligibleNeutralPrefixScope(owner)             // prototype scope only
           and result is NORMAL and unprotected DATA
           and fitsGlobalLimit(result)
           and retainedNormalProviderCoversWholeTransferAndService(q, result):
            return                                      // provider already replayed
        publish(pairedC5(prepared, q, result, owner.demand))
```

For one guard with `n` fields, the model produces `2n+1` queries and no
query deeper than `n` relative to the original head. A prefix trie shares
common guards; a union of guard prefixes needs storage linear in its
nodes. This bounds the **extra partition** by retained finite AP guards.
It is not a bound on the analyzer's total AP relation count.

Do not cut a deeper guard at the global limit and then exclude its full
branch: leave the unresolved coarse region active. Do not copy the
prototype's Empty-E constructor to nonempty-E queries; their intersections
need a separate proof. Do not treat output-fact equality as proof of native
alias, request or ND delivery equivalence.

## 4. Retrace from the run-4 handoff

Runs 1–4 supply the same relevant facts as the
[method-only trace](bidirectional-non-empty-may-acyclic-nontermination-20261113.md)
and the [BB trace](bidirectional-non-empty-may-basic-block-retrace-20261113.md):

| Run | Method-only owner | BB version |
| --- | --- | --- |
| run-1 forward, limit 1 | Retain W; unknown reader publishes root MAY demand. | Same, with separate read/write owners. |
| run-2 backward, limit 1 | Reverse read cuts `p.f.g.*` to `p.f.NE`; broad `p.M` also exists. | readBB retains its separate `p.f.NE` demand. |
| run-3 forward, limit 2 | Source `p.f.U/T,N` starts partial `p.f.*` and exact FLOW prefix probe; partial read publishes `p.f.* → ret.M,D`. | readBB accepts that partial query and publishes the same loss. |
| run-4 backward, limit 3 | The partial row permits the NORMAL reader R, although the root cycle also remains. | readBB retains R; normal block-summary delivery can make it available to the method. |

The experiment starts from this retained R/W state. It proves retirement
of the supplied repeating witnesses from that state, not a full native
driver derivation of every run-1–4 row.

### Run-5, forward, limit 4: method-only owner

```java
// Demand: [p.M/F ; ret.*/F]. Retained: R and W.
// Call 1 submitted p.f.U/T,N.
// Original C2: p.f.*/F,N; p.$/F,N.
// Updated initials: p.f.$/F,N; p.f.*/F {g},N;
//                   p.f.g.*/F,N; p.$/F,N.
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;    // Only p.f.g.* reaches this return.
                              // Raw NORMAL R is already retained.
    Box q = new Box();
    q.f = p;                  // Raw NORMAL specializations of W.
    return q;                 // W coverage is checked before relative cut.
}
// New NORMAL publications: none needed; retained R/W remain.
// New DEMAND publications: none.
```

The previous abstract call-2 offer `p.M/T,D`, if offered in isolation,
would start `p.$` and the five-query partition listed in §3. The reference
also computes its owner publications: none. In the new actual caller
execution that MAY offer is no longer regenerated.

```java
// Demand: [Target ; ZERO]. Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void main(boolean flag) {
    Box a = sourceAtF();        // a.f.U/T,N, using run-4 source permission.
    Box b = choose(a, flag);    // Saved R: b.U/T,N.
                              // Saved W: b.f.f.U/T,N.
    Box c = choose(b, flag);    // From b.U: c.U/T,N; c.f.U/T,N.
                              // From b.f.f.U: read fails f!=g;
                              //                  writer gives c.f.f.f.U/T,N.
    sinkAnywhere(c);           // NORMAL witnesses only -> NormalTarget(id).
}
// NORMAL: ZERO -> NormalTarget(id).
// DEMAND: none. All actual paths fit limit 4. Natural stop after run-5.
```

### Run-5, forward, limit 4: BB version

```java
// Method demand: [p.f.M/F ; ret.*/F]. Retained: R and W.
// Call 1 submitted p.f.U/T,N. Initial: p.f.U/F,N (unchanged MUST lane).
// A hypothetical old second offer p.f.NE/T,D is also checked by the model:
// its old p.f.* query becomes p.f.$; p.f.* {g}; p.f.g.*.
Box choose(Box p, boolean flag) {
    if (flag) {
        // readBB: no current DATA demand or initial.
        // Submitted from method: p.f.U/F,N.
        // Saved opposite R -> ret.U/F,N.
        readBB: { return p.f.g; }
        // New readBB summaries: none; retained R remains.
    } else {
        // writeBB: no current DATA demand or initial.
        // Submitted from method: p.f.U/F,N.
        // Saved W -> ret.f.f.U/F,N.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // New writeBB summaries: none; retained W remains.
    }
}
// Raw method ret.f.f.U result is covered by retained W BEFORE C5.
// It does not create ret.f.NE. The reader result is covered by R.
// New method DEMAND summaries: none.
```

The actual main replay is the same as above. Its second call receives
NORMAL MUST facts, not the old NE offer. Inner DATA frontiers and the
method DATA frontier are empty; main emits NormalTarget only. This
reference also stops after **run-5**. There is no run-6 forced by the
model, and no iteration cutoff in the test.

### Wrapper guard

The experiment does not delete a MAY result merely because a normal
reader exists. A wrapper that still submits `p.*/T,D` to the saved
opposite-direction R gets `ret.M/T,D`; W also gives `ret.f.*/T,D`.
That coarse result remains available to the enclosing owner and its
demand checks. The reference explicitly checks this replay. The two-call
example stops because its **actual** offers become NORMAL MUST, not because
the prototype discards every coarse call result.

This component check is not the full historical wrapper finding-loss
regression. That regression must be rerun at native integration, including
the stored-direction gate and current-summary subscription behavior.

## 5. A remaining guard-discovery gap

The candidate cannot assume that a suitable NORMAL guard already exists
in every program. Extend the reader by one field:

```java
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g.h;
    Box q = new Box();
    q.f = p;
    return q;
}
```

The shown run-3 partial publication still has initial `p.f.*` and conclusion
`ret.M`. Its backward pair is `[ret.M ; p.f.*]`. Even when the global
limit exceeds 3:

```text
submitted / initial: ret.M/T,D -> ret.*/F,N (plus exact probe)
raw reader result:   ret.*/F -> p.f.g.h.*/F,N
paired budget:       FL(p.f.*)+1 = 2
published result:    ret.*/F -> p.f.g.NE/F,D
other writer result: ret.*/F -> p.f.M/F,D
```

The latter MAY can cover the cut child at handoff. Increasing the global
limit does not make this particular pair publish a NORMAL reader. The
generic Lean check proves the same cut for every larger limit. This is a
counterexample to obtaining a NORMAL guard merely from the global limit;
it is not a proof that no other paired row could ever learn that guard.

An edge-only follow-up is to retain **bounded observed guard prefixes**
before handoff compaction. Use the public prefix of an admitted cut edge,
not the discarded suffix:

```text
onAdmittedHandoffCandidate(edge):
    next = projectToNextRun(edge)
    guardTrie[next.owner, next.entryPort].insert(next.entry.path)
    performOrdinaryHandoffCompaction(edge)

nextC2(demand, submitted):
    use the same exhaustive query cover, also split by these observed guards
```

Here a cut to `p.f.g.NE` contributes `p.f.g`, even if a broader MAY row
absorbs that demand. If that guarded query later produces a partial reader
row, the paired budget can advance to 3. Each child point and the complete
residual must remain represented. No evidence words are composed through
calls. Guard prefixes stay within the ordinary AP limit; a guard does not
assert that a field is tainted.

The Lean model proves the **local** progress fact: for a read of length
`n`, using budget `k+1` when `k<n` yields a public prefix of length `k+1`
and decreases `n-k`. It does not yet prove that native scheduling,
direction/port projection and C2/C5 always retain and use the required
guard, or that all interacting demand families make progress. The
guard-history extension is therefore an investigation direction, not an
activated rule or a proved general solution.

## 6. Proof results and limits

The [Lean package](../../spec/lean/proposals/bounded-may-partition-20261114/README.md)
checks:

- Any finite point input belongs to a partition region. Restricting an
  arbitrary point relation to the complete partition preserves and reflects
  that relation, including the selected child's exact root.
- A single finite guard creates `2n+1` regions, each of depth at most `n`,
  with only EXACT/STAR query kinds.
- A retained correlated NORMAL prefix relation covers all of its aligned
  specializations for every suffix; no next-run observations are used.
- The old root MAY/MAY query family is replaced by the explicit finite
  family; exclusions reject only the selected read from the residuals.
  An unknown `h` read remains unresolved.
- Both old repeating owner offers generate no fresh publications in the
  declared R/W reference. Actual two-call replay preserves NORMAL source
  and sink support. The computed method-only and BB-method run-5 DATA/Target
  frontiers are empty.
- Precoverage rejects DEMAND and protected results. The cleaner check
  preserves the counterexample to EXACT-only admission.
- Concrete queries are unchanged; an original wrapper STAR offer still
  produces its required MAY result during opposite saved-reader replay.

Validation: **PASS, 8 modules, 163 audited declarations**, including 38
new claims and 125 dependency claims. The checker accepts only `propext`
and `Quot.sound` in axiom reports. Receipt and compiler outputs are outside
the Git repository:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  bounded-may-partition-20261114/proofs-v8/receipt.json
```

One limit check was corrected during model development: filtering an
over-limit child *after* excluding its branch would lose that region.
The checked producer now keeps the complete old coarse query whenever
its proposed guard partition does not fit the global limit.

**Not proved:** native C2 image construction for partitioned queries;
native all-argument/alias/rule/ND provider-service coverage; storage replay
and report correspondence; static and loop ports; a general progress measure
for arbitrary executable rules or unconfirmed findings. Concrete MAY/MAY
admission is unchanged by this candidate, so it is explicitly not a general
answer for every concrete-mark cycle. The arbitrary-relation partition
lemma does not establish those engine properties.

The native integration gate must reproduce the two original cycles and
the cleaner/wrapper regressions, then check the handoff row sets and final
findings with no hard cap. A finite guard snapshot and the reference's
normal stopping frontier are useful evidence; neither authorizes deleting
an unmodeled residual query.

No project scan was made. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**. The **run-5** result above is a new formal
reference experiment, not a project performance measurement.
