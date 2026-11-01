# Demand-relative summary restriction

Date: 1 November 2026. Status: specification for the next iteration.
The analyzer implementation is unchanged.

Use [proof-guide.md](proof-guide.md). The constructive models and checker
are in the [proof package](lean/proposals/demand-relative-summary-restriction-20261101/README.md).
The [proof dossier](demand-relative-summary-restriction-proofs.md) states
their scope and the runtime checks that remain necessary.

## 1. Selected changes

Let `Dp -> Dc` be an edge selected for handoff from the previous run.
The next run has the opposite direction:

```text
demand.entry = Dc       // selects the new initial A
demand.exit  = Dp       // selects the new conclusion B
```

For each complete matching demand row, first apply the existing paired
summary intersection. Then limit its selected DATA conclusion to:

```text
min(currentFieldLimit, FL(Dp) + 1)
```

Apply this rule to both NORMAL and DEMAND candidates. Admit only the
results. Do not retain an unrestricted summary collection.

These are major semantic changes, not only storage optimizations:

| Part | Current runtime | New rule |
|---|---|---|
| Summary intersection, C5 | A permitted descendant can retain its full chain up to the run limit | Apply the additional demand-relative limit after each paired intersection |
| Summary storage | Store raw candidates, then select publications | Restrict first; store only admitted results |
| NORMAL persistence | Read eligible NORMAL records from the raw collection | Read eligible NORMAL records from the admitted collection |
| Refinement selection | Classify the raw candidate before C5 | Classify each final admitted result |
| Full-coverage shortcut | Coverage of the raw result can stop some searches | Stop only with a proof that remaining rows add no final result; the reference operation visits all matching rows |

A new cut can turn a NORMAL relation into a broader DEMAND relation. It
can postpone a report or a native record until a later iteration. It must
not turn the broader result into NORMAL.

The current runtime is
`c4a71246519ee5432879ce82518823f1703f3aa4`.
The source pins in the proof receipt identify the reviewed files. This
document overrides its raw-summary admission and persistence order and
the conclusion limit at C5. It does not change the C2 emission table in
[the AP spec](ap.md) and [the exact-DEMAND extension](demand-layer-exact-initials.md).

## 2. Behavior that stays unchanged

Keep these mechanisms:

- Initial emission, starting layers, and separate NORMAL/DEMAND entry
  memberships. A previous demand's layer does not force the next initial
  to stay DEMAND.
- All instruction transfers, field writes, cleaners, rules, aliases,
  source permissions, static write effects, and CFG delivery.
- The global field limit inside the method. Do not use this new summary
  limit for instruction results or temporary values.
- Complete ND bindings and whole ND summary premises. Run-1 still has
  singleton origin arms; later FULL forward runs can have ND premises.
- FLOW summary normalization, mark exclusions, and the current protection
  rules for non-subsumable concrete relations.
- The current FLOW-backed replacement law. Change its input to admitted
  summary results; do not add a new coverage law or an alias guard.
- Persisted-record replay on every original call offer, before current
  demand admission. An old record already passed admission in its producer
  run. Do not apply a new current-demand gate to this replay.
- Complete predefined method models. They remain model inputs, not new
  inferred candidates. Their existing application and boundary-rule policy
  stay unchanged.
- The run-1 static completion used by run-2, and local-only demand lookup
  after run-2. Virtual completion rows use the same paired rule and limit.
- Typed ZERO and Target matching, backward ZERO-to-Target conversion,
  sink report IDs, and completed-barrier report collection.
- FULL as the acceptance mode, the known GROUP issues, positive field
  limits, and the current schedule `1,1,2,3,…`.

**Scope of “all summaries”:** every newly inferred AP summary, NORMAL or
DEMAND, uses the new gate. Typed terminal summaries keep their separately
selected protocol. In particular, NormalTarget remains a forward-only,
normal-only report relation. It does not acquire an AP-demand requirement.
DemandTarget retains its existing paired gate. Section 8 specifies this
boundary. There is no NORMAL AP exemption.

Do not add a grounding label, source-permission fallback, rejected-input
history, raw native cache, or new propagation service to implement this
specification. If implementation needs another semantic rule, report the
counterexample before making that change.

## 3. Terms

```text
N = NORMAL                  D = DEMAND
$ = EXACT                   * = STAR
[any] = MAY                 [any-taint] = MUST
FLOW = abstract mark slot   T, U = full concrete marks
E = field exclusion         mx = excluded concrete marks in a FLOW slot
```

A DATA leaf has a base, concrete accessor chain, tail, mark slot, field
exclusion, layer, and the existing non-subsumable annotation. A packed
value represents a finite set of these leaves. Its leaves can share
prefixes and mark sets.

`FL` counts named fields and array elements in the concrete chain. It
does not count the tail, base, mark, or static class accessor:

```text
FL(p)          = 0
FL(p.a.b)      = 2
FL(p.[index])  = 1
FL(S.C)        = 0
FL(S.C.f.g)    = 2
```

ZERO and Target are typed control endpoints. They have no `FL`. Do not
represent them as DATA facts with depth zero.

`A` is the current canonical original premise. It can be ZERO, one
initial, or the complete ND premise. Initial keys do not gain a demand-row
ID, depth budget, or layer field. Keep existing equality and hashing.

`B` is a candidate conclusion. A candidate is a transient value offered
to the summary admission operation. It is not a stored method summary.
Ordinary post-instruction storage remains distinct from summary storage.

## 4. Initial emission and its depth bound

This specification does not replace C2. Its relevant rules are:

```text
1. Check the base, mark, legal shape, direction, and global field budget.
2. Use one demand entry Dc and the actual submitted fact.
3. Keep the directed path relation and actual descent exclusions.
4. Emit the existing canonical initial and its existing starting layer.
```

A concrete `T` demand does not accept a different concrete `U`, or an
abstract FLOW offer without concrete support. A matching ancestor MAY
offer can supply a concrete exact demand as an exact DEMAND initial.
It cannot create a NORMAL exact witness.

For a MAY entry, an actual strict descendant exposes only the first new
counted field. At the same prefix, C2 uses the existing exact/MAY/MUST
cell. An ancestor offer uses the demanded prefix if that cell admits it.
A requested STAR can be emitted for a descendant offer in run-2 only.
Later restricted runs do not re-emit that STAR request. Keep the existing
FLOW EXACT-to-STAR summary normalization.

Thus, for each emitted singleton initial `a`:

```text
FL(a) <= currentFieldLimit
FL(a) <= FL(Dc) + 1
```

Normalization does not change this depth. The static class accessor does
not consume the one new field. Keep the named static anchor indivisible.
Do not introduce a broad concrete root/class static initial.

C5 must retain the existing structural image check:

```text
canStoreInitial(Dc, a)
```

It checks that the stored canonical initial has a legal C2 preimage that
is inside the entry demand. Check containment on that preimage, as the
existing normalization requires. A normalized FLOW STAR key can use its
raw EXACT preimage; do not require that stored STAR itself to pass the raw
containment test. Do not replace this operation with symmetric overlap or
with a depth comparison alone.

For an ND original, match a contributing member as the current C5 does,
but retain the **whole original** on the admitted result. The per-member
bound is not permission to replace the complete premise with that member.

## 5. Exact paired restriction, then abstraction

### 5.1 Complete pair selection

The reference result is a union over complete matching rows:

```kotlin
fun restrictCandidate(method, original, raw, run): Collection<Facts> {
    if (run.isRun1) return existingRun1SummaryPolicy(original, raw)

    val out = ExistingExactResultUnion()
    for (row in matchingCompleteRows(method, original, raw)) {
        // row.entry is Dc; row.exit is Dp from the SAME row.
        for (selected in existingPairedC5(original, raw, row, run.policy)) {
            when (val exit = row.exit) {
                is Data -> {
                    val budget = min(run.fieldLimit, FL(exit.pattern) + 1)
                    existingFieldCut(selected, budget) { out.add(it) }
                }
                Zero -> out.add(selected) // typed Reach result only
            }
        }
    }
    return out.results()
}
```

`matchingCompleteRows` must include every relevant local or virtual row.
An index can reject impossible rows before C5. It must not change this
reference result. No complete pair means no admitted summary.

Use the same exit row for both selection and the depth budget. Never use
the maximum or minimum `Dp` depth from an unrelated row. Never combine
one row's entry permission with another row's exit permission.

Run-1 has no preceding demand snapshot. Its existing summary policy is
the unrestricted first-run admission policy under its existing global
limit and static rules. There is no finite `Dp`-relative limit in run-1.
This is not a special exemption for NORMAL; both first-run layers use
that same policy.

### 5.2 Existing AP exit operation

The following defines the scalar exit operation that precedes the new
cut. Apply the existing demand-side normalization first: a FLOW STAR
selector's field exclusion is ignored. Do not erase exclusions from
actual facts or records.

Require equal DATA bases and intersecting mark slots. Two concrete marks
must be equal in FULL mode. A concrete mark must not be excluded by the
other FLOW slot. Two FLOW slots pass the existing mark-meet test. The
operation keeps the candidate's mark slot; a concrete selector does not
invent a concrete mark on a FLOW conclusion.

Let `p = Dp.path`, `q = B.path`. `admits(tail,E,suffix)` accepts an empty
suffix; EXACT rejects a nonempty suffix; MAY accepts it; STAR/MUST reject
it if its first accessor is excluded.

```text
q == p:
    EXACT or STAR B: keep B whole
    MAY or MUST B with EXACT Dp: use EXACT at p; keep B's layer
    MUST B with STAR Dp: retain MUST; union the relevant exclusions
    other MAY/MUST cells: keep the existing tail and exclusions

q is a strict descendant of p:
    if Dp admits the suffix: keep B
    otherwise: reject

p is a strict descendant of q:
    MAY/MUST B:
        require B's exclusion to admit descent
        rebase at p; use EXACT if Dp is EXACT
        use the existing MUST/STAR exclusion cell; otherwise empty E
    STAR B:
        require B's exclusion to admit descent; keep B whole
    EXACT B: reject

incomparable chains: reject
```

This operation preserves the selected layer. In particular, it does not
promote an exact DEMAND result to NORMAL. A correlated STAR stays whole
when its existing representability rule requires this.

### 5.3 New field cut

For each selected DATA leaf `b` and its row's positive budget `k`:

```text
if FL(b) <= k:
    keep b unchanged
else:
    keep the concrete prefix through k counted fields
    replace the lost suffix and old tail with MAY
    set the result layer to DEMAND
    use empty field exclusion for the cut piece
    retain the base, mark slot, FLOW mark exclusions, and protection
```

This is the existing field-cut operation. Do not shorten a correlated
NORMAL STAR to a shorter NORMAL STAR. That would assert a relation that
the original suffix correlation does not justify.

For a packed value, retain its within-budget pieces unchanged and emit
overflow pieces on DEMAND. Union cut memberships at shared prefixes. A
protected concrete membership remains protected after projection; an
unprotected copy cannot clear a protected copy. Keep the existing mark
set and exclusion union rules.

Every admitted DATA leaf for that row satisfies:

```text
FL(result) <= currentFieldLimit
FL(result) <= FL(Dp) + 1
```

An uncut DEMAND piece stays DEMAND. A cut NORMAL piece becomes DEMAND.
No part of this operation upgrades DEMAND to NORMAL.

### 5.4 Multiple rows and search completion

Use literal per-row union before the existing summary replacement law.
Keep independent NORMAL and DEMAND memberships and join protection as
the existing store requires. Do not invent a cross-layer dominance rule.

For example, let both entries accept the same initial and let:

```text
raw B:       p.a.b.c.$/T, NORMAL
row 1 Dp:    p.a.b.c.$/T       // budget >= 3: keeps the exact NORMAL leaf
row 2 Dp:    p.a.[any]/T       // budget 2: adds p.a.b.[any]/T, DEMAND
```

Raw coverage after row 1 does not prove that row 2 adds nothing. The
reference operation visits both. A production early exit is permitted
only if it proves that every remaining row's final, capped result is
already represented, including layer and protection. The old raw-coverage
test alone is insufficient. C2 entry-only lookup keeps its own unchanged
coverage rule; this warning concerns changed C5 results.

## 6. One admitted summary collection

There is no use for an authoritative unrestricted summary collection in
the new design. Its former roles use the admitted collection:

| Former raw-store use | New source |
|---|---|
| Summary deduplication | Final admitted memberships |
| FLOW-backed replacement | Admitted providers and admitted concrete memberships |
| NORMAL native persistence | Eligible admitted NORMAL rows |
| Summary census | Admitted rows; label separate transient candidate counters explicitly |
| Run-1 static survivor inspection | Admitted first-run rows under the unchanged first-run policy |

The logical pipeline is:

```kotlin
fun offerSummary(original, candidate) {
    val canonical = existingSummaryNormalization(original, candidate)
    for (piece in restrictCandidate(method, canonical.original, canonical.facts, run)) {
        val delta = admittedSummaries.add(canonical.original, piece) ?: continue
        pendingPublications.add(canonical.original, delta)
    }
}
```

`admittedSummaries.add` performs the existing deduplication, annotation
upgrade, and permitted FLOW-backed replacement. It receives no raw
candidate. Rejection changes no summary, publication, record, or demand
state. There is no stored rejected-candidate history.

The original premise stays canonical and unchanged by this gate. A
demand-row witness or budget is query state, not new compiler metadata in
fact equality or hashing. The proof model's finite provenance trace is
proof evidence, not a runtime raw-candidate store.

Ordinary MethodEdgeStore state still records post-instruction results.
It is not a second semantic summary collection. Its current FLOW-backed
representation preserves concrete memberships (`replaceCovered=false`).
Do not enable destructive raw FLOW replacement there as part of this
change. Summary replacement can remove a concrete relation only under an
admitted provider and the existing coverage/protection law.

Physical indexes or filtered views are permitted. They must contain only
admitted memberships and must not provide another insertion path. It is
not necessary to copy every row into a second demand store during the run.

## 7. Persistence and handoff

### 7.1 NORMAL records

At the completed barrier, persist eligible NORMAL rows from the admitted
set. Keep the existing native-record shape and direction rules. In
particular, ND and backward-ZERO rows do not acquire a new native format.
Keep legal NORMAL FLOW exclusions.

A raw NORMAL candidate that is rejected has no new native record. A raw
NORMAL candidate cut to DEMAND also has no new native record. Do not keep
its uncut NORMAL form as a fallback.

Do not purge valid records from earlier completed runs. Their original
admission remains valid; the selected every-offer call replay still uses
them before the current demand gate. This replay is not new summary
inference. Any new caller summary produced by application goes through
the caller's new gate.

### 7.2 Next-run demand

Use the existing completed-run handoff. Evaluate its existing selector on
the **admitted result**, not the candidate:

```text
select an admitted AP row when:
    its layer is DEMAND, OR
    its original is ND, OR
    direction is BACKWARD and its original is ZERO
```

The last two are existing AP guidance cases. They are not permission to
bypass C5, and they do not make a NORMAL AP row a DEMAND native record.

Then reverse each selected pair for the next demand snapshot:

```text
admitted A -> B     becomes     entry = B, exit = A
```

Use the existing endpoint normalization, mark normalization, ND projection,
and typed Target projection. Keep a complete current ND premise until its
existing handoff projection; do not weaken it inside summary admission.

There is no new `saveDemandForNextRun` operation. The name used in the
earlier discussion meant this existing barrier operation. In particular:

```text
raw NORMAL -> cut DEMAND -> ordinary handoff selects it
raw DEMAND -> uncut DEMAND -> ordinary handoff selects it
raw NORMAL -> rejected -> no summary and no frontier row
```

## 8. ZERO and terminal relations

Handle typed control rows as complete pairs:

| Demand entry | Current original allowed |
|---|---|
| ZERO or Target | ZERO only |
| DATA | A matching DATA member under the existing C2-image test |

An exit selector ZERO accepts the existing Reach/terminal slot, not an AP
DATA conclusion. A DATA exit accepts DATA and supplies its field budget.
Thus a ZERO-original AP summary with a DATA exit is still restricted and
capped. ZERO is not an unlimited-output exemption.

DemandTarget uses the existing complete entry match plus ZERO exit match.
It has no accessor chain and no field cut. Run-1 retains its existing
terminal admission policy. Do not store rejected DemandTarget memberships
as semantic summaries merely to deduplicate later offers.

NormalTarget keeps its selected lane: produce it only from a complete
NORMAL witness, compose it with NORMAL support only, ignore it backward,
and skip a persisted identical owned relation before new propagation.
Persisted ZERO-to-NormalTarget does not need replay. Collect report IDs
from the existing configured-root ZERO-to-NormalTarget rows. An AP cut
cannot itself create a normal report or source-action permission.

Source action permissions still require a real accepted backward source
action. C2 admission, a capped summary, a saved-record read, or demand
handoff alone does not create a SourceHit.

## 9. Principal examples

### 9.1 A backward result with excessive depth

```java
// Previous guide: p.[any]/T -> ret.[any]/T.
// Current backward initial: ret.f.$/T, NORMAL.
Box project(Box p) {
    return p.a.b.c;
}
// Body result at a sufficient global limit:
//   ret.f.$/T -> p.a.b.c.f.$/T, NORMAL.
// Existing C5 keeps the whole permitted descendant.
// New gate uses FL(Dp)=0:
//   ret.f.$/T -> p.a.[any]/T, DEMAND.
// Only this admitted form is stored and published.
```

The next opposite run can refine the new field prefix. No raw NORMAL
version is persisted. Protection and mark T survive the cut.

### 9.2 Why the budget uses Dp, not the current premise

```java
// Current forward guide:
//   entry Dc = p.[any]/T; exit Dp = ret.f.[any]/T.
// Actual p.$/T is NORMAL; C2 admits p.$/T, NORMAL.
Box wrap(Object p) {
    Box inner = new Box();
    inner.g = p;
    Box outer = new Box();
    outer.f = inner;
    return outer;
}
// Raw result at global limit 2:
//   p.$/T -> ret.f.g.$/T, NORMAL.
// New exit-relative budget: FL(ret.f)+1 = 2. Keep this precise result.
// A fixed FL(current premise)+1 budget would be 1 and would lose g again.
```

The body must also have limit 2. This example is not permission to use
the boundary limit inside the method.

### 9.3 A newly cut source still needs a real reverse action

```java
// Source rule: assign T at factory.ret.a.b.c.$.
Box factory() { return obtainBox(); }
void root() {
    Box value = factory();
    sinkT(value.a.b.c);
}
```

Consider a complete admitted ZERO/Target route, an already permitted first
source action, and a DATA exit guide `ret.[any]/T`. Keep the body limit at
3 for this finite boundary trace:

```text
forward source candidate: ZERO -> ret.a.b.c.$/T, N
first admitted result:   ZERO -> ret.a.[any]/T, D; no new native record

opposite run:
    exact sink seed supplies ret.a.b.c.$/T
    C2 under ret.a.[any]/T emits ret.a.b.*/T on D
    execute the actual reverse source action for ret.a.b.c/T
    record its actual source action ID; emit the ordinary terminal guidance

next forward DATA exit guide: ret.a.b.*/T
    budget 3 -> ret.a.b.c.$/T, N
```

The precise admitted relation itself can now supply a native record and
a NORMAL source-to-sink witness. No uncut raw cache supplied the missing
fields. A wrong mark or unrelated field must not create the source action
permission. The formal witness isolates this boundary trace; it does not
prove every source rule, call graph, or driver schedule.

### 9.4 Output compression does not remove all body work

```java
Node walk(Node p) {
    Node x = p;
    while (choose()) x = choose() ? x.left : x.right;
    return x;
}
```

Backward body processing can construct many inverse paths before it
offers a summary. Capping a publication does not undo these operations.
If existing C5 already selects one shallow endpoint, this change can
have no effect on that internal explosion.

For a different output with 16 depth-3 leaves under one first field, the
new cut can represent all 16 by one depth-1 MAY/DEMAND membership. The
proof package checks this finite output-work witness. It does not claim
a measured project speedup.

## 10. Correctness requirements

The required local refinement statement is:

```text
For every complete-row exact-C5 result b:
    there is an executable admitted result cut(b)
    which retains every candidate location/mark represented by b.
    Any lost geometry is explicitly DEMAND.
```

This is a sound abstraction of the selected result. It is not equality
with the old precise publication, and not an assertion that MAY is
definite taint. For FLOW, retain correlated geometry on uncut pieces;
cutting to MAY loses that correlation only on DEMAND. A cut cannot prove
a universal MUST assertion or a NORMAL report.

The proof obligations are:

1. C2 initial depth and structural-image validity; complete paired C5
   provenance and no row mixing.
2. Positive per-row budget, output depth bound, within-budget identity,
   candidate-location coverage, unchanged mark/protection, and no D-to-N
   promotion. Field exclusion removal on a cut is widening, not a kill.
3. Complete per-row union; no loss through an old early-stop test.
4. Rejected candidates have no semantic state; every stored, indexed,
   published, and newly persisted row has an admission witness.
5. A FLOW provider must itself be admitted before it can remove a concrete
   summary. Preserve the existing protected-membership and coverage laws.
6. Classify the final layer; a new cut enters ordinary handoff. Preserve
   the existing NORMAL ND and backward-ZERO guidance cases.
7. Keep typed control/terminal rules and actual source permissions.
8. Demonstrate finite refinement and native-record recovery without an
   unrestricted NORMAL fallback. Do not claim general convergence from
   the depth inequality alone.

The [dossier](demand-relative-summary-restriction-proofs.md) separates
checked constructive laws, finite witnesses, reused contracts, and runtime
adapter obligations. In particular, the package is not a proof of every
Kotlin AP operation, full finding equivalence, or all-project termination.

## 11. Implementation acceptance

Before implementation acceptance, use tests that exercise the real gate,
store, persistence, and handoff together:

- NORMAL rejected by C5: no stored summary, native record, or publication.
- NORMAL selected then cut: DEMAND publication and frontier; no raw native
  fallback. An in-budget NORMAL result remains persistable.
- Two complete rows with different budgets, both arrival orders; exact
  result union and monotone protection upgrades.
- Rejected FLOW cannot erase an admitted concrete summary. A cut FLOW
  cannot serve as a NORMAL provider or erase a NORMAL concrete summary.
  Keep permitted admitted DEMAND-to-DEMAND replacement and protection.
- Whole ND premise, wrong marks/bases, counted array accessors, static
  class anchors, and nonempty later-run exclusions.
- ZERO-original DATA output, ZERO/Target controls, DemandTarget, unchanged
  NormalTarget behavior, and the backward-ZERO guidance case.
- Current-summary application, every-offer saved-record replay, and the
  caller's own summary admission after either application path.
- Exact-DEMAND/source regressions, finite wrap/unwrap and conditional
  producer traces, and OWASP finding comparison.

Measure candidate count, exact-C5 results, extra-cut results, final admitted
memberships, NORMAL-to-DEMAND cuts, newly persisted records, outgoing
frontiers, and downstream deliveries. Include histograms of
`FL(raw), FL(Dp), FL(selected), FL(admitted)`, separated by layer and tail.
Keep candidate, admitted, and native counts distinct.

The latest unchanged-runtime campaign reached Stirling-PDF **run-8**
(run-7 complete/accepted), conductor **run-4** (run-3 complete/accepted),
thingsboard **run-2** (run-1 complete/accepted), and OWASP **run-5** complete.
No project was run with this new mechanism. Use the selected project
configuration for its future comparison and report the latest reached,
completed, and accepted run iteration. Do not infer a run-time reduction
from the finite output-compression proof alone.
