# Natural termination for the bidirectional analyzer

Status: PROPOSAL, revision 4 (consolidated), 23 November 2026. All
mechanisms are native prototypes behind flags on local branches (§11).
None is merged. The acyclic part is condensed in
[acyclic-convergence-proposal.md](acyclic-convergence-proposal.md).

This proposal replaces
[termination-driver-stop-proposal.md](termination-driver-stop-proposal.md).
It follows the [design guide](design-guide.md).

## 0. Summary

The iteration has one purpose: to decide each candidate report. The run-11
cutoff exists only because the demand never ends. This proposal ends the
analysis by its own state:

1. **Stop rules.** The driver stops only on an empty forward demand
   (`NO_DEMAND_EDGE`, as today) or on an exact fixed point
   (`FIXED_POINT`, §4): the state repeats, nothing persistent changes, and
   no run reads the field limit K in a binding way. No stop reads the
   report state. There is no numeric limit.
2. **Requirement AC.** Every acyclic method reaches zero forward demand
   rows by itself (§5, and the condensed proposal).
3. **Cyclic code.** Growth through loops and recursion is made finite by
   structural folds that do not refine more than the demand asks (§6).

State per project, with every report identical to native:

| Project | Native | Best measured configuration | Result |
| --- | --- | --- | --- |
| OWASP | `RUN_LIMIT` 11; driver 132-134 s | S + LG (§7) | `NO_DEMAND_EDGE` at run-7; driver 100-101 s |
| Stirling-PDF | `RUN_LIMIT` 11 when fast; can stall for 40 min in run-9 or run-11 | S + RX (§7) | `FIXED_POINT` at run-15; driver 71-72 s |
| Conductor | timeout in run-8 | S + CA (§6.2) | no natural end; run-8 now finishes; timeout later |
| ThingsBoard | memory guard in run-1 | — | not a termination problem |

The two best configurations were measured separately. Their combination
is not measured yet. Open problems are in §9.

## 1. Decisions and gate rules

| Date | Decision |
| --- | --- |
| 19 Nov | No iteration cutoff and no new numeric limit: they are hacks for a missing termination. |
| 20 Nov | No stop test that reads the report state. `QUIESCENT` and `DECIDED` are rejected (§8). |
| 20 Nov | Requirement AC (§5). Assumption: JVM pass rules have no `[any]` in `from` or `to`; `[any]` in source and sink conditions, and conjunctions, are allowed, because they make MAY only in backward runs. AC is measured on forward handoffs. |
| 20 Nov | G6, the primitive-tracking mark policy, uses the drop form (acyclic proposal §5.1). |
| 21 Nov | Callers do not matter for AC: each acyclic method must reach zero rows. |
| 21 Nov | No refinement deeper than the demand requests (the exact start is rejected). |
| 21 Nov | An EXACT cleaner does not apply to a MUST fact (acyclic proposal §5.5). |
| 23 Nov | Confirmed AND provisional results must stay identical to native. A change that looks like a precision gain is a failure: there is no trusted ground truth. |
| 24 Nov | The relative-cap rule (`acC5Exact`, C5B) is removed (acyclic proposal §5.6). |
| 24 Nov | Keep the provisional results: for `UserService#saveUser` the gate wins over AC (acyclic proposal §7 item 1). |
| 24 Nov | The four module fixtures that the cleaner rule changes are signed off. |
| 24 Nov | Robustness rule: the core must prevent fact explosion by itself, whatever the code, the rules or the alias analysis give it. The relative caps `FL(Dc)+1` (C2) and `FL(Dp)+1` (C5) are this mechanism; no rule may relax them on the basis of a property of the code or of an outer input. |

Gate for every rule (design-guide rules 4-6): module suite, jvm suite,
rule suite (585 cases), OWASP 3 interleaved launches per arm,
Stirling-PDF 2, Conductor 1; identical reports by SARIF identity and code
flows; wall time and peak memory not worse.

## 2. Starting point

Native runtime at HEAD, measured with shadow logs to run-31 or run-41.

| Case | End | Reports final at | Demand after that |
| --- | --- | --- | --- |
| OWASP | `RUN_LIMIT` 11 | run-3 | exact period 2 from H7 to run-41 |
| Conductor | timeout in run-8 | run-5 | diverges: 17,470 / 25,131 / 85,205 forward rows at H3 / H5 / H7 |
| Stirling-PDF | `RUN_LIMIT` 11 or timeout | run-5 | counts constant from H17, keys rotate, records grow |
| Rule suite | 583 natural, 2 at the cutoff | — | exact period 2 in both cutoff cases |

The updated rule spec ([demand-refinement-and-termination.md](demand-refinement-and-termination.md),
commits a0b18b4e1, 32b037292, a0a1978c6) adds two run-level stop proofs
to R41. Neither ran on a project: their scope bounds excluded all four.
Its only stop on real code is at run-11, the run of the cutoff. Its
closed run-pair check is the ancestor of `FIXED_POINT`. Of its rules,
only R37/R38 and R41 aim at sources that matter now; R38 is close to X
and RX of the acyclic proposal. Its work-removal items (joined record
index seal, loop replay skip, C5 index bypass) stay separate performance
items.

## 3. Why the demand does not end

The barrier builds a new demand store each time (`driver/HandOff.kt:75`).
A row is handed off when it is a DEMAND summary, any ND summary, a
backward ZERO summary or an outgoing DemandTarget (`ap/Demand.kt:136-140`).
So the driver has no memory of demand. It can only test "is the demand
empty".

The makers that keep it alive, measured on the projects:

| Maker | Effect | Where |
| --- | --- | --- |
| DemandTarget renewal at a sink with a complete ZERO target | A closed two-run cycle with no DATA row: forward the DEMAND hit emits a DemandTarget and a seed; backward the seed rebuilds the zero rows that admit the next hit | 919 forward rows at 431 OWASP roots; `bytesToWebResponse` on Stirling-PDF |
| A DEMAND callee reply next to a covering NORMAL reply | The layer is part of the group key, so MUST never covers MAY; the MAY fact renews a DemandTarget | OWASP `doSomething` families |
| Cleaner survivor | After an EXACT cleaner in a MUST region the remainder has no NORMAL form, so it becomes DEMAND | 151 of 164 open OWASP roots |
| Read at a strict prefix of a premise | A coarse premise gives a MAY reply that also reaches exact actuals | OWASP helpers; Stirling-PDF `saveUser` |
| Relative C5 cap `FL(Dp)+1` | A cut that does not read K | acyclic helpers; one `decodeMimeHeader` block |
| Pathless MAY fact copied by alias analysis | In a loop the MAY fact on the iterator is copied into every exit row; the demand gains one level per pair of runs | Conductor `replace` |
| Paths that repeat a segment through a cycle | No fixed point under a growing K | Stirling-PDF pipeline and regex loop; Conductor `getObject` |
| DemandTarget renewal in loop blocks | Like the first row, but the block has no complete target of its own | OWASP loop roots |
| STAR start from a backward MAY row | A forward start that is DEMAND by itself | Stirling-PDF `bytesToWebResponse` arms, `AuthController#login` |

Earlier rules removed demand at the handoff. Removal changes the next run,
and native regressions show lost findings when identical demand is
removed (`RepeatedDemandRelayTest`, `DistinctMarkOriginServiceTest`,
`UniformCoverageOriginAuditTest`). The rules here instead stop a maker
from producing demand, or prove that the state repeats.

## 4. Stop rule: `FIXED_POINT`

### 4.1 Definition

At a completed forward barrier of run `i`:

```text
if the forward handoff is empty:   end NO_DEMAND_EDGE   report C
else if FIXED_POINT(i):            end FIXED_POINT      report C + (L_i ∖ C) provisional
else if the policy cutoff holds:   end RUN_LIMIT        report C + (L_i ∖ C) provisional
else: continue
```

`FIXED_POINT(i)` holds when:

1. the canonical full-content key set of handoff `H_i` equals `H_{i-2}`,
   and `H_{i-1}` equals `H_{i-3}` (owner, scope, ports, both patterns with
   base, path, tail, exclusions and marks, control kind; independent of
   order);
2. barriers `i-1` and `i` add or remove no NORMAL record key and add no
   NormalTarget, rule contributor or confirmed report, and the seed set
   and the reached set `L` do not change;
3. runs `i-1` and `i` make no binding read of K: no global cut that cuts,
   no C5 clamp at `depth ≥ K` that cuts, no `fitsBudget` rejection.

### 4.2 Why it is a proof

Run `i+1` reads only the handoff, the persistent stores, K and fixed
inputs (`IterationDriver.kt:237-243`, `engine/RunConfig.kt:15-26`).
Conditions 1 and 2 make these inputs equal to those of run `i-1`, except
K. Condition 3 makes the run independent of K, because a read that fits
at K also fits at a larger K. By induction no later run changes the state.
`closedPairRepeats` and `limitReadStable` in
[ClosedRunPair.lean](lean/proposals/termination-rollback-20261118/ClosedRunPair.lean)
prove this for a deterministic run.

Condition 3 is necessary. In `RepeatedDemandRelayTest` and
`RepeatedDemandHiddenRenameTest` the state is equal for several runs and
only K changes; a later run confirms a finding. In the deep-chain
fixture D5 the K condition alone holds the stop back at run-5. In all 78
deep-chain variants the full test never holds before the finding is
confirmed.

### 4.3 Determinism

The proof needs a deterministic run. Canonical order
(`-Dorg.opentaint.bidi.canonicalOrder=true`, branch
`proto/deterministic-handoff-20261120`) breaks every tie at the barrier
by a content key: actor order, compaction tie-break, demand rows, record
order, seeds, report representative.

| Probe | Without | With |
| --- | --- | --- |
| Fuzz, 20,000 programs, identity-hash shift | 2 end-run changes | 0 |
| Rule suite, 2 launches | 1 of 585 barrier digests differ | 0 |
| OWASP, 6 launches | handoffs differ from barrier 1 | identical from barrier 2 |

Cost: about 1.4 s per OWASP analysis, all at the barrier. Still open: the
run itself is not confluent. Equal input content in a different order
can give a different output, and OWASP run-1 has two results (68,053 or
68,063 rows). Suspected engine sources: the member order of ND
combinations, a row published only if it arrives before the row that
covers it, and interning-order ids.

### 4.4 Gate

`FIXED_POINT` alone with canonical order: 0 false stops in every measured
analysis. OWASP stops at run-17 in 7 of 7 launches with identical SARIF
(+32 s wall against the cutoff, because of six extra runs). Rule suite:
identical reports; both cutoff cases stop naturally. Module suite: only
end-run assertions change, and two fault-injection fixtures publish one
more provisional entry because the stop comes before the injected fault.
Cost: at most 0.30 s per barrier for the key hash, 238 ms for the check.

## 5. Requirement AC: acyclic code converges

Full text: [acyclic-convergence-proposal.md](acyclic-convergence-proposal.md)
(revision 2: standalone on the native runtime, formal definitions).
Selected rules: the G6 drop form, DemandTarget subsumption X, relay
subsumption RX, the MUST-cover reply rule, and "an EXACT cleaner does not
apply to a MUST fact". Revision 2 withdraws "no relative C5 cap in
acyclic methods": the cap makes only passenger rows, and the same
acyclic owners stay open with and without it (acyclic proposal §5.6).

| Forward AC residual | OWASP | Stirling-PDF | Conductor (H7) |
| --- | --- | --- | --- |
| Native (run-11) | 711-735 rows | 49 (when run-11 completes) | 21 |
| AO-C5: the five rules on the native runtime (run-11) | 6 rows / 1 owner | 5 / 3 | 16 / 6 |
| S, on the NT stack (includes the withdrawn C5 rule) | 6 | 43 | 15 |
| S + RX, on the NT stack | 2 | 19 | 11 |

The S rows end at different runs (`FIXED_POINT`), so they are not
directly comparable with the run-11 rows. The rest: reads at a strict
prefix of a premise, DEMAND STAR starts, and alias self cycles from
pass-through models (a bounded analyzer artifact; acyclic proposal §7). For `UserService#saveUser` on
Stirling-PDF, AC and identical provisional output cannot both hold
(acyclic proposal §7).

## 6. Cyclic code

### 6.1 W: fold at a program cycle

Flag `-Dorg.opentaint.bidi.cycleFold=true`, forward runs only. Branch
`proto/cycle-fold-20261120`. Cut a path at the first accessor that the
applied relation adds and that already occurs above it on the same path;
the cut part is a DEMAND MAY tail. It applies only at a loop block's
repeat port (one full traversal) and at a call edge inside a recursive
call cycle. Finite repeats in acyclic code (`x.f.f`) stay exact.

- Stirling-PDF: the pipeline rotation
  (`outputFiles.(Iterable#Element)^n`) stops at H19; the regex loop's
  boundary cuts are gone from run-9; `FIXED_POINT` at run-33 with an
  identical report.
- Conductor: `getObject` stable at 12 rows from H5.
- Module suite and rule suite: 0 report changes, 0 lost natural stops;
  two recursion fixtures reach `FIXED_POINT` at run-7 and run-9.
- Folding in both directions lost a confirmed finding and three natural
  stops. Withdrawn.

### 6.2 CA: anchored MAY specialization in cyclic scopes

Flag `-Dorg.opentaint.bidi.cyclicWidening=fwd`. Branch
`proto/cyclic-widening-20261121`. In a loop block at its back-edge exit,
or at the method level of a recursive method, C5 restricts a MAY fact
only to the first counted accessor below the MAY node: `var(3).[any]`
against exit `var(3).a.b.c` gives `var(3).a.[any]`. It refines less than
the demand requests. It has no numeric parameter and reads neither K nor
the report state.

Trace of Conductor: the relative cap is not the driver. In each loop pass
of `ParametersUtils#replace` a pathless `var(3).[any]` lands on the
iterator. The alias stage copies callee replies onto every local that it
links to the argument; at the back edge C5 copies the pathless fact into
every exit row (46,594 of 58,157 publications). Backward C2 starts one
accessor below each entry. The ten accessors per level come from the
container models. Inferred root cause: models that return the receiver
(`this → result`) pollute the alias set.

| Conductor | S | S + CA (2 launches) |
| --- | --- | --- |
| `replace` loop rows | 33,006 at H7, growing | about 5,300 from H9, stable |
| Run-6 / run-7 | 349 s / 162 s | about 188 s / 27 s |
| Run-8 | does not finish | about 400 s |
| End | timeout in run-8 | no `FIXED_POINT` by run-21 (5,400 s budget) |

Reports identical everywhere; CA never fires in the module suites, the
rule suite or on OWASP. Still open: `replaceList` backward rows grow
(+3,300 at H18) and record keys rotate; backward runs cost 600-772 s.

### 6.3 LG: DemandTarget cover in loop blocks

Flag `-Dorg.opentaint.bidi.loopDtCover=true`. Branch
`proto/loop-dt-20261121`. A DEMAND witness in a loop block, whose method
root has a saved complete ZERO → NormalTarget for the same sink, emits no
DemandTarget and no seed when (a) every sink of the method that captured
a seed so far is covered the same way, and (b) the method relayed no
callee DemandTarget in this or the previous forward run.

- OWASP: the 93 cyclic rows of S are three loop roots, their post-loop
  blocks and two relays, kept by a closed cycle at two confirmed
  conjunctive sinks. With LG: `NO_DEMAND_EDGE` at run-7 in 3 of 3
  launches, identical SARIF, driver 100-101 s against 104-105 s for S.
- Module suites 0 report changes; new loop fixtures L1-L6 and D4 lose
  nothing; rule suite, Stirling-PDF and Conductor identical (LG never
  acts there).
- LG has no proof. Its guard avoids a native defect:
  `LoopOutputRestriction.restrictScalar` drops a growing loop output that
  no consumer admits, so a loop is not monotone in K. The same defect
  loses loop-grown chains of depth 3 or more with all flags off. It is
  live on Stirling-PDF (200,107 drops) and Conductor (672,433). The
  principled fix is to make the loop output restriction monotone in K.

## 7. Configurations and gates

| Name | Contents |
| --- | --- |
| NT | canonical order, `FIXED_POINT`, W, MUST-cover, X, G6 drop form |
| S | NT + no relative cap in acyclic methods + an EXACT cleaner does not apply to a MUST fact |
| S + RX | S + relay subsumption |
| S + LG | S + loop-block DemandTarget cover |
| S + CA | S + anchored MAY specialization |
| AO-C5 | the five acyclic rules on the native runtime: no canonical order, no `FIXED_POINT`, no W (acyclic proposal §6) |

S includes the relative-cap rule that the acyclic proposal (revision 2)
withdraws. The S measurements below were taken with it.

| Configuration | OWASP | Stirling-PDF | Conductor | Suites |
| --- | --- | --- | --- | --- |
| Native | `RUN_LIMIT` 11; driver 132-134 s | `RUN_LIMIT` 11 or a stall; 32 / 2 when it completes run-11 | timeout in run-8 | — |
| NT | `FIXED_POINT` 17; driver 124 s | `FIXED_POINT` 33; 590-646 s | timeout | rule suite identical; module changes only the intended G6 removals and two fault fixtures |
| S | `FIXED_POINT` 11; driver 105 s | `FIXED_POINT` 33 | timeout | 4 module fixture changes from the cleaner rule (signed off 24 Nov) |
| S + RX | rows 99 → 11 | `FIXED_POINT` 15; 71-72 s | timeout | rule suite identical; 49 representation assertions |
| S + LG | `NO_DEMAND_EDGE` 7; 100-101 s | identical (LG never acts) | identical | 0 report changes |
| S + CA | identical (CA never acts) | identical | run-8 finishes; no end by run-21 | 0 report changes |
| AO-C5 | `RUN_LIMIT` 11; driver 110.7-112.8 s against 150.2-153.1 s (both with the residual diagnostic) | `RUN_LIMIT` 11 in 56 s, no run-11 stall; reports equal the completed native run | timeout in run-8; H7 at 600 s against 666 s | rule suite identical; module: only the 4 cleaner fixtures |

All configurations keep the native reports on the three projects and the
rule suite. The mechanisms do not interact: in NT every end and every
failure equals one of the single mechanisms.

Failed configurations: S + the inside-read rule and S + unrefinable MAY
empty OWASP's demand at run-7, but remove the two native provisional
results on Stirling-PDF (acyclic proposal §7).

## 8. Rejected after test

| Idea | Why |
| --- | --- |
| `QUIESCENT` (revision 2), a fixed run constant | Reads the report state; `RepeatedDemandRelayTest` loses its run-9 finding |
| `DECIDED` (`L_i ⊆ C_i`) | Reads the report state. Native breaks: a deep field chain that ends in a boxed value (D5, D6, M4) hides the sink at every small K |
| Observer census, report-stability stop | Read the report state |
| Fixed point without the K condition, or on row counts | False stops; Stirling-PDF counts are constant while keys rotate |
| Closed run pair with scope bounds | The bounds excluded every project |
| Fold at every repeated accessor | 23 lost natural stops, at least 5 lost confirmed findings |
| Widening chosen by growth across runs | Every finite repeated path also grows while K grows |
| W in both directions | 1 lost confirmed finding, 3 lost natural stops |
| Influence-cone fixed point | The Stirling-PDF pipeline is inside the cone of the undecided reports |
| DemandTarget cover of a loop block by the root's target without a guard (XE) | Loses a finding in loop fixture D4 |
| Factored handoff rows, run-long C2 memo (Conductor) | Exact, but the rows are not the cost |
| Demand removal by key identity or report ID (R37 alone, R42) | Loses findings or leaves the Target |
| Provisional output at a timeout | Makes the wall clock a cutoff with output |
| Per-run time budget | A limit |
| Acyclic-code rules rejected after test | See acyclic proposal §8 |

## 9. Open problems and next steps

1. Gate the combination NT + AO-C5 + LG (+ CA) against native on all
   projects and suites, without the relative-cap rule. This is the
   candidate end state.
2. AC: DEMAND STAR starts (Stirling-PDF) and alias self cycles
   (Conductor `ExclusiveJoinTaskMapper#getMappedTasks`; source fix in the
   alias call model). The
   `saveUser` rows stay as an accepted exception: the provisional results
   win (acyclic proposal §7).
3. Make `LoopOutputRestriction` monotone in K. This fixes a native recall
   defect and may make LG's guard unnecessary.
4. Conductor: `replaceList` backward growth, the cost of late backward
   runs, and the alias-set precision of models that return the receiver.
5. Make the run confluent (§4.3), so that the `FIXED_POINT` proof holds in
   production.
6. Stirling-PDF stalls in a `decodeMimeHeader` loop block (the bimodal
   run-9). A work defect of its own.
7. Delete `HardRunLimitPolicy` and `RUN_LIMIT` when every reference
   project and suite ends with `NO_DEMAND_EDGE` or `FIXED_POINT`. The
   wall-clock timeout and the memory guard stay as resource budgets; a
   timeout publishes no provisional entries.

## 10. Semantic scope

Changed: the stop decision and a new `EndReason` `FIXED_POINT`, which
publishes `L∖C` like `RUN_LIMIT`; the barrier tie-break order; W and CA
in cyclic scopes; LG at loop-block sink witnesses; the acyclic rules
(acyclic proposal §9).

Unchanged: the run schedule and field-limit schedule, run-1 and run-2
static views, the handoff projection and compaction rules, the report
identities, and every rule that is not named above.

## 11. Evidence

All branches are local. Data is under
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/`.

| Item | Branch | Report (on the branch) |
| --- | --- | --- |
| Shadow fixed-point logging | `proto/fixed-point-shadow-20261119` | `docs/reports/fixed-point-shadow-20261119.md` |
| Fold at every repeat (rejected) | `proto/repeat-fold-20261119` | `docs/reports/repeat-fold-ablation-20261119.md` |
| `DECIDED` gate, attack fixtures, G6 variants, deep and string chains (rejected stop) | `proto/decided-stop-20261119`, `proto/decided-stop-attack-20261119`, `proto/decided-g6-20261119`, `proto/deep-chain-fixture-20261120`, `proto/string-chain-fixture-20261120` | the matching `docs/reports/*` |
| Canonical order, `FIXED_POINT` gate | `proto/deterministic-handoff-20261120` | `docs/reports/deterministic-handoff-20261120.md` |
| W | `proto/cycle-fold-20261120` | `docs/reports/cycle-fold-20261120.md` |
| Conductor volume trace | `proto/conductor-volume-20261120` | `docs/reports/conductor-volume-20261120.md` |
| OWASP drain diagnostic | `proto/owasp-drain-20261120` | `docs/reports/owasp-drain-20261120.md` |
| MUST-cover rule | `proto/dosomething-fix-20261120` | `docs/reports/dosomething-fix-20261120.md` |
| Acyclic census | `proto/acyclic-census-20261120` | `docs/reports/acyclic-census-20261120.md` |
| Complete backward rows (not a driver) | `proto/persist-complete-20261120` | `docs/reports/persist-complete-20261120.md` |
| X, G6 drop form | `proto/dt-subsumption-20261120`, `proto/g6-drop-xsub-20261120` | `docs/reports/dt-subsumption-20261120.md`, `docs/reports/g6-drop-xsub-20261120.md` |
| NT integration | `proto/termination-integration-20261120` | `docs/reports/termination-integration-20261120.md` |
| AC closure, S | `proto/ac-closure-20261121`, `proto/must-cleaner-20261121` | `docs/reports/ac-closure-20261121.md`, `docs/reports/must-cleaner-20261121.md` |
| Inside reads, unrefinable MAY (failed) | `proto/inside-read-20261121`, `proto/unrefinable-may-20261123` | `docs/reports/inside-read-20261121.md`, `docs/reports/unrefinable-may-20261123.md` |
| RX | `proto/stirling-ac-20261121` | `docs/reports/stirling-ac-20261121.md` |
| CA | `proto/cyclic-widening-20261121` | `docs/reports/cyclic-widening-20261121.md` |
| LG | `proto/loop-dt-20261121` | `docs/reports/loop-dt-20261121.md` |
| Acyclic-only stack AO / AO-C5, per-rule gates, fail-safe oracle | `proto/acyclic-only-20261123` | `docs/reports/acyclic-only-20261123.md` |
| Relative C5 cut rows are passengers; alternatives (A)-(D) | `proto/c5-passenger-20261123` | `docs/reports/c5-passenger-20261123.md` |
| Alias self cycles in acyclic code; R2, R4 prototypes | `proto/acyclic-growth-20261124` | `docs/reports/acyclic-growth-20261124.md` |
| MUST-cover without the acyclic scope: Conductor width census, cover item 3, MAY-only, AO-C5 without MUST-cover | `proto/must-cover-shape-20261124` | `docs/reports/must-cover-shape-20261124.md` |

## 12. Checklist and blind spots

```text
[x] Failure class and real trace: §2, §3, §6
[x] Ablation on the real case: drain diagnostic, per-maker ablations
[~] Native prototype, 3 launches: per rule on OWASP; Stirling-PDF and Conductor 1-2 launches
[x] Execution site and volume of each new operation: in each report
[x] Selected semantic scope: §10, acyclic proposal §9
[~] Proof scope: FIXED_POINT has a model proof for a deterministic run; no other rule has a proof
[x] Withdrawal condition: withdraw a rule on the first native case with a changed report
[x] Adversarial review and native counterexamples: §8
```

- The run is not confluent (§4.3). The fixed-point proof holds for the
  model; the evidence holds for the measured launches.
- Project gates have 1-3 launches per arm on a shared host.
- ThingsBoard was not run.
- The best OWASP and Stirling-PDF configurations were never run together.
- LG works around a native loop defect instead of fixing it.
