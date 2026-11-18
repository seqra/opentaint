# Exact reply support: termination of the new MUST case

15 November 2026. Synthetic data-flow reachability. FULL mode.
Follow [proof-guide.md](../../spec/proof-guide.md).
The [consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md#definite-full-reply-support)
contains the full contract. Production is unchanged.

**New reference: natural completion at run-7. Unchanged native regression:
run-31, policy ceiling.** The new stopping proof has no iteration limit.
The 18 old cold references retain their stops, latest **run-15**.

## 1. Change and reason

The original [MUST counterexample](bidirectional-provisional-must-nontermination-20261115.md)
has these inferred NORMAL records:

```text
M0: p.MUST/T   -> ret.$/U,N
Mf: p.f.MUST/T -> ret.$/U,N

actual: p.f.MUST/T,N
saved M0 result: ret.$/U,D     // native provisional lane
saved Mf result: ret.$/U,N    // native definite lane
```

The copies agree on the exact full-mark point and complete caller context.
The NORMAL copy proves everything the DEMAND point can eventually establish.
Keep that NORMAL copy and omit the identical DEMAND reply before observation.
Do not remove M0, Mf or a Target. No field path is expanded.

This is a new **cross-layer DATA subsumption rule**, limited to concrete
exact FULL replies with Empty E/mx. Native matching, initial emission, C5,
tail normalization, cuts, rule conditions and Target handling are unchanged.
Compare all scope/port/resume coordinates, complete caller original, full
mark and literal H. Compare composed support, not a record's declared layer.
Do not apply the rule to raw callee hypotheses or summaries.

## 2. Cold execution with late current replies

The checked schedule does not assume the new NORMAL current reply can
cancel an earlier provisional replay. Current publications can arrive in
separate batches. The fold acts on each complete already-ready saved batch.

| Completed run | make publication / replay | Root result |
|---|---|---|
| run-1 F/1 | `p.*/T -> ret.$/U,D` | D Target |
| run-2 B/1 | `ret.$/U -> p.M/T,D` | D Target; both producers permitted |
| run-3 F/2 | Infer M0; field query remains D | NT(0) plus D Target |
| run-4 B/3 | Paired C5 refines output to `p.f.M/T,D` | D Target; both producers permitted |
| run-5 F/4 | Infer Mf; earlier M0 provisional reply already delivered | NT(0), NT(1) plus D Target; make DATA demand empty |
| run-6 B/5 | Saved reverse M0/Mf only; no make actor | D Target; only a.f/T producer remains permitted |
| run-7 F/6 | Both saved records ready; exact reply folding removes D copy | Both retained NORMAL reports; no DATA or Target demand; stop |

The new proof computes the same complete cold state through run-6 as the
old counterexample. No Target is retracted. Run-7 has these block annotations:

```java
// Current demand: empty.
// Marked submitted input: p.f.MUST/T,N from a; b has no new marked offer.
// Emitted initials: none. No body actor or current subscription.
// Ready saved batch for a before folding: ret.$/U,D and ret.$/U,N.
// Delivered after folding: ret.$/U,N only.
Box make(Box p) {
    Box r = new Box();
    // Producer: CM(p.M,T) => assign U at r.$.
    return r;
}
// Fresh summaries: none. Saved M0 and Mf both remain.

// Demand: [Target | ZERO]. Submitted: ZERO,N. Initial: ZERO->ZERO,N.
void root() {
    Box a = new Box(); a.f = new Box(); // Producer: a.f.MUST/T,N
    Box b = new Box();                 // No new T permission needed
    Box x = make(b);                   // NT(0) already retained
    Box y = make(a);                   // y.$/U,N; no y.$/U,D
    // Observe U exactly at x and y.
}
// Fresh DEMAND summaries/Targets: none.
// Retained NORMAL reports: NT(0), NT(1).
```

The driver stops at the ordinary empty-refinement check. If forcibly run
again, run-8 becomes idle, and induction proves every later completed state
remains idle. The proof does not infer termination from a finite capture.

## 3. Safety and work checks

| Case | Required behavior |
|---|---|
| Only provisional M0 reply | Keep it on D |
| Both records, actual input D | Both composed replies stay D; no NORMAL provider may be borrowed |
| Same point but different H | Keep both memberships |
| Different complete original or continuation | Keep both |
| Layer-sensitive alias guard takes different routes | Preserve both routes; fold only after their effects or within an equal resolved route |
| Different full mark or concrete path | Keep both |
| Same-location MAY/NE/STAR/MUST or FLOW copy | This new rule does not apply |
| A late NORMAL current publication | Keep already executed effects; next saved batch can fold |
| ND binding | All arms remain required; compare the complete composed original |
| ZERO/Target or static-pool side effects | Keep the existing channels and rules |

The point filter preserves every NORMAL member and every observable point
key. Every deleted D member has an explicit retained N witness. Support-
monotone ordinary continuations and complete AND joins can use that witness
with no weaker support. A real later cut can still create D. No new mark,
location, relation, alias result or NORMAL support is inferred.

An unprocessed layer-sensitive branch is outside that continuation theorem:
its resolved native route must be part of the comparison key. The new case's
two mark-changing replies both have the same nonidentity return route.

Use the existing reply batch. A temporary NORMAL-key hash set and one filter
pass suffice. Output membership is a subset of the original batch. There is
no new caller history, evidence propagation, query, subscription or field
combination. Pending demotion affects effective support; do not commit it
early. Fold before the common continuation has emitted an observation.

## 4. Old acceptance set

Every captured reply packet, at every cold iteration in these references,
is unchanged by the added filter. The formal check preserves full AP keys
and layers; it does not compare only final counts.

| Prior reference | Natural stop |
|---|---|
| Nested; Prefix; RoundTrip | run-9 |
| PrefixPostfix; Growth | run-11 |
| Postfix | run-13 |
| Double | run-15 |
| OldMethod; OldBB; LongReader | run-5 |
| OrdinaryTwo | run-3 |
| Overwrite | run-9 |
| NestedNegative; NestedPositive; NestedExact | run-3 |
| NestedSurvivor; NestedDeep | run-5 |
| NestedLarger | run-11 |

All 18 complete traces are recomputed by the diagnostic runner, while the
new Lean theorems check absorption against every saved cold packet. The
protected uniform closure's complete reply packets are also unchanged:
its reference stop remains **run-3**. The selected standalone MUST-preserving
cleaner stays **run-1**; no cleaner operator is changed by this proposal.

## 5. Evidence and limits

- **67 new constructive claims** pass. Including the source-hash-checked old
  proof build and unchanged counterexample, the receipt covers **2,180
  declarations in 109 modules**. No custom axiom, proof hole, classical
  choice or external decision oracle is allowed.
- **41 native tests pass**, including five new candidate-adapter tests,
  the unchanged run-31 counterexample, rejected one-input candidates and
  earlier routing/overwrite/cleaner/provider components.
- The new native adapter uses the real definite/provisional record service
  and then filters committed native results. It is not a production change
  or an integrated native run-7 scan. The formal new run-7 reference has the
  selected NE C2/C5 policy and the new reply rule.
- No project scan or universal termination proof is claimed. Integration
  must batch saved results at the actual common resume point, retain every
  transfer-affecting continuation coordinate and preserve surviving effects.

```bash
python3 spec/lean/proposals/exact-support-absorption-20261115/check.py \
  --out /tmp/exact-support-proofs
python3 scripts/demand_experiments/point-write-progress/acceptance.py \
  --out /tmp/old-progress-references
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ExactSupportAbsorptionNativeTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalMustReplayCycleTest
```

[Proof package](../../spec/lean/proposals/exact-support-absorption-20261115/README.md).
Logs, JSON and compiled proofs remain outside the repository in
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/exact-support-absorption-20261115/`.
