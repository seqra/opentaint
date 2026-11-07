# Next iteration: avoid repeated queries and review STAR admission

Date: 7 November 2026. Status: proposal; no candidate is selected here.
Language: ASD-STE100 Simplified Technical English.

The current implementation is `7069fe2d7`. Its configured project campaign
is complete. Quality acceptance is open. The
[performance report](../reports/bidirectional-protected-guidance-storage-performance-20261106.md)
is the measurement authority. The
[STAR initial audit](bidirectional-star-initial-emission-audit-20261107.md)
adds two small-program experiments; it adds no project measurement.

This document joins the current performance candidates with the new admission
finding. It supersedes the proposal's summary, not its measurement evidence.
The [detailed query-work proposal](bidirectional-lazy-observations-sparse-output-frozen-inputs-next-iteration-20261106.md)
keeps the definitions, pseudocode, source anchors and proof obligations for
A–D. None of those changes fixes an admission rule.

## 1. Current state and required result

R/C/A means latest reached / fully completed / accepted forward report.

| Project | R/C/A | Status | Main measured work |
| --- | --- | --- | --- |
| OWASP | run-5 / run-5 / run-5 | Complete; 4,112 reference identities | No broad late-loop problem established |
| Conductor | run-4 / run-3 / run-3 | Timeout; seven identities match f945 | Loop observation in F3 and B4 |
| Thingsboard | run-1 / none / none | Timeout; no accepted report | Run-1 engine, then static completion |
| Stirling-PDF | run-5 / run-4 / run-3 | Timeout; 21 accepted identities | Loop observation in B4 and F5 |

The fixed-baseline no-FN gate does not pass. Thingsboard's 14 reference
identities are censored before the first accepted report. Stirling has four
missing f945 identities and eight additions; three gaps and all additions
are inherited from earlier bidirectional runs. LicenseKeyChecker is also
missing against 52f/8331. Its current first lost required fact is not known.
An old 21-to-22 report-count increase does not identify the added location.

No candidate may claim that the small getter finding is the License cause.
No candidate may waive a missing identity because the same method has another
finding. The source/sink identity and actual native route must be checked.

## 2. Performance rank

These candidates avoid work whose result cannot affect the answer. They do
not change the scalar policy, fields, layers, matching roles or literal
protection. Expected impact is a rank, not a promised speedup.

| Rank | Candidate | Current -> proposed | Why it should help; evidence limit |
| --- | --- | --- | --- |
| A | Delay complete enclosing loop observation | Compute admissions and enclosing results eagerly -> compute enclosing results only when nonemptiness/equality still needs them | Avoid saved replay, C5 and result unions. Loop observation owns 64.18% of Conductor B4 and 78.56%/81.78% of Stirling B4/F5 Java samples. The avoidable subset is not counted. |
| B | Finalize touched C5 output programs only | Scan/finalize all prepared programs -> visit programs which received a selected packet | Avoid empty bucket work. One complete current sample has Return raw base versus This demand output and selects nothing. The global untouched fraction is unknown. |
| C | Reuse frozen static-input normalization at each exact stage | Normalize the same immutable joined input for each writer visit -> reuse that stage's immutable result | Thingsboard static completion has 47.98% canonicalization Java samples and 52.45% allocation weight. Reuse frequency and retained memo size still need measurement. |
| D | Prepare C2 path-budget metadata once per query owner | Recount the same immutable path for each comparison -> use prepared field counts | Conductor F3 has a 13.07% fitsBudget leaf share. This overlaps larger scopes and is not an avoidable-work count. |

C is the first Thingsboard-specific candidate. A and B have the strongest
cross-project evidence. Do not sum sample shares or use allocation churn as
a retained-heap estimate. The current campaign had no OOM and no fresh heap.

The A decision is exact for one frozen original/scope/port/query context:

```text
C(v) = complete adjacent/repeat admissions and their labels
E(v) = complete enclosing DATA/Target results

if C(raw) is nonempty:
    do not compute E(raw) merely to prove nonemptiness

for each existing legal cut:
    if C(cut) != C(raw): reject the cut without E(cut)
    else compare complete E(raw) and complete E(cut)

if C(raw) is empty:
    evaluate E(raw); it may be the only consumer
```

Keep the existing trial order, certificate and selected cut. B uses the same
output programs and restriction result, with sparse finalization. C keys
reuse by the exact immutable row version and normalization stage. It assumes
no global canonical confluence or idempotence. D changes prepared metadata,
not field counting or AP equality.

## 3. Admission: a separate semantic decision

The original four-method loop/getter program has an expected-one-finding
check. Current runtime reaches natural run-5 with zero findings. Two isolated
policy copies both report in run-3 and complete naturally at run-5.

| Candidate | Changed initial outputs | FLOW start | Concrete start | Current bounded result |
| --- | --- | --- | --- | --- |
| E1 | Convert only emitted MAY/FLOW to STAR/FLOW | NORMAL | Unchanged | Original program passes |
| E2 | Convert emitted MAY for FLOW and concrete marks to STAR | NORMAL | DEMAND | Original program passes; native protected-header family grows 1 -> 32 |

The relevant normal relation comes from ordinary code:

```java
// Backward submitted ret.[any]/FLOW, D; demand ret.[any]/FLOW.
// Current initial ret.[any]/FLOW, D; candidate ret.*/FLOW, N.
Object getG(Object p) {
    return p.g;
}
// Current:   ret.[any]/FLOW -> p.g.[any]/FLOW, D.
// Candidate: ret.*/FLOW     -> p.g.*/FLOW, N. Field limit 1 fits g.
// Native opposite replay on p.g.[any]/T, D still returns ret.[any]/T, D.
```

Both candidates change the two central emission cells: same-path MAY input,
and ancestor MAY input under a deeper MAY demand. They update the exact raw
image too. They leave the rejected same-path STAR input under MAY demand
unchanged. They leave supplied MAY facts and field cuts unchanged. MUST is
not MAY and is not converted. ZERO and static anchors keep their grammar.

This is not a pure optimization. FLOW changes from DEMAND to a conditional
NORMAL start; concrete STAR changes suffix correlation while staying DEMAND.
Caller support must still be joined when the summary is applied. A saved
NORMAL relation does not turn the caller's MAY/DEMAND input into NORMAL.

The central contract must be changed as a unit:

```text
emitNew(d, a) = map selected emitted MAY outputs to STAR

canEmitNew(d, i):
    accept iff an actual a exists with emitNew(d, a) = i
    use explicit old-emission preimages, not emitNew(d, i) == i

canStoreNew:
    use that new raw image and the existing inside-demand check
    keep the existing FLOW EXACT-to-STAR summary normalization preimage
    keep paired exit, whole original, scope, port and budget checks

loop observation:
    use the same policy as delivered initial commands
    reprove the MAY-specific fast certificate for the new result/layer,
    or retain the exact trial fallback and measure its extra work
```

For E1, a rendered concrete mark keeps its old image and support layer.
For E2, current concrete-MAY image membership is removed and same-path
concrete STAR becomes a valid output under MAY demand. Do not change unrelated
EXACT-on-MAY support. Do not globally rewrite the initial interner or stored
demand templates.

The full-mark cost example has a selected exact-root cleaner followed by five
independently optional strong field writes. MAY keeps one protected empty-E
header. STAR retains 32 protected exclusion headers. These are actual native
AP/store results at one path depth. They do not identify a project cause or
prove a complete-program regression. E1 leaves that concrete cell unchanged.

The current exact same-initial/same-layer analysis can be shared. Caller
subscriptions and physical block links are installed before initial dedup.
Do not add another input archive merely because old MAY and STAR commands
can map to one new STAR command.

## 4. Proof and validation gates

No A–D implementation is selected here. Their exact-result proofs and native
adapter tests must pass before landing. No E contract is selected here either.
The current audit has 26 checked constructive Lean laws, five passing native
AP/store tests and two passing original-program candidate runs. The model's
ordinary FULL/empty-exclusion scope does not prove whole-driver equivalence.

Before selecting/implementing E, check at least:

- Exact emission/image and joint initial/layer behavior for both changed cells.
- Method, block, loop and run-2 static demand routes; full original and ports.
- Nested calls after a new STAR initial: same-path MAY-demand/STAR-input
  rejection remains and could remove a former inner admission. Test the
  complete driver, including saved-first and opposite-record alternatives.
- Native C5/Target entry checks and loop-observation/certificate behavior.
- Source, cleaner, ND, suffix correlation and protected-storage effects.
- Original regression with its unchanged expected-one NORMAL finding; exact
  and descendant-taint negative controls; both arrival orders where relevant.

Do not assert that a conditional local rejection is a complete-program FN.
Do not assert that the two passing programs prove global progress or safety.
Keep failed experiments and their scope in the evidence.

After a selected implementation, run the same four configured projects only:
FULL, 16 GiB, enabled statics/aliases, limits `1,1,2,...`, the saved IFDS/outer
budgets and direct `runProjectAnalyzer`. Reuse the fixed f945 baseline. Record
exact identities, every iteration frontier/time, reached/completed/accepted
labels, CPU/allocation profiles and OOM heap evidence if OOM occurs.

For each performance candidate, count work actually skipped and show that
the admitted result is unchanged. For E, compare the changed demand/record
shapes and actual finding routes; equal callback counts are not the contract.

## 5. Acceptance work still required

The current iteration is implemented and measured, but it is not a no-FN
success. The next useful quality observation is the actual License source
occurrence, then the first missing fact/gate in its current native route.
Binding generic annotation text to that source is insufficient. Preserve
the distinction between an accepted run-3 snapshot and an interrupted run-5.

Thingsboard needs an accepted first report before any quality equivalence
claim. Its timeout itself is established; it does not identify 14 separate
semantic omissions. Reducing query work may make that report reachable, but
the current samples cannot promise a completion time.

The pending initial-emission scope decision does not block source inspection
or diagnostic tests. It does block an unselected core policy change, as
required by `task.md` and the proof guide's semantic-scope rule.
