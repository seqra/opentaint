# Repeated demand rows after handoff

12 November 2026. Active investigation under
[demand-task.md](../../demand-task.md) and the
[campaign specification](../design/bidirectional-redundant-demand-elimination-campaign-20261110.md).
Production analyzer behavior is unchanged. Classification is not complete.

**Selected proof scope, 13 November:** the user kept the edge-only
contract. The instruction-model permission question is resolved.
Complete instruction-level AP models cannot supply an applicability
guard or completeness premise for retirement. The historical pending
question below is superseded by this decision.

**13 November scope correction:** the native counterpair has equal
captured histories, not a checked equality of every allowed channel.
It did not record raw C5 candidates. See the
[correction and next check](bidirectional-demand-history-scope-correction-20261113.md).
Raw C5 history is already within the campaign scope; this investigation
does not require the pending instruction-model permission.
The new four-control test checks 75 full raw packets plus the 203 legacy
events through H5. Both ordered projections agree. A later raw difference
appears at run-10, before the first post-restriction difference at run-11.
No new corpus row is classified by this generic test.

The [13 November follow-up](bidirectional-coarse-demand-recovery-20261113.md)
checks ancestor-output siblings, distinguishes current publications from
persisted knowledge, and traces a genuinely new backward record whose
forward inverse still preserves the finding. Verdict totals are unchanged.
The [NORMAL replay service audit](bidirectional-normal-replay-service-audit-20261113.md)
checks stronger providers and ZERO routes for the complete FLOW corpus,
and shows why equal unary/ND results need a paired caller adapter.

## Native target inventory

The deletion unit is one retained native demand row. A deletion removes
the whole row, including all its summary-origin contributions. The old
28,631-origin ledger is historical evidence, not the target set below.

| Project | Pair | Earlier rows | Later rows | Repeated rows | Methods | Boundary units |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| OWASP | run-9/run-11 | 1,153 | 1,153 | 1,153 | 463 | 534 |
| Conductor | run-5/run-7 | 30,646 | 88,792 | 23,303 | 166 | 281 |
| Stirling-PDF | run-7/run-9 | 1,105 | 986 | 933 | 59 | 131 |
| Total | | 32,904 | 90,931 | 25,389 | 688 | 946 |

There are 5,382 repeated method rows and 20,007 inner-block rows. The
complete captured definition inventory includes empty scopes: 36,803
methods and 46,055 block definitions. Definitions and directed boundary
interfaces are different inventories. Keep the block tree and both
physical ports on each boundary row.

The [capture audit](bidirectional-demand-row-capture-audit-20261112.md)
checks the native stores, barrier markers and source revisions. All nine
snapshots for the three pairs and their intervening runs are complete.

| Project | Latest reached | Latest completed | Latest accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

These are the original capture results. A separate diagnostic OWASP scan
also reached, completed and accepted run-11. It retained the same 2,633
finding identities. Its execution and the original execution stay separate.

## Accepted row-service cover

The row proof, complete observed bindings and independent checks passed.
The versioned ledger accepts these individual classifications:

| Project | Repeated rows | REDUNDANT | OPEN |
| --- | ---: | ---: | ---: |
| OWASP | 1,153 | 0 | 1,153 |
| Conductor | 23,303 | 4,437 | 18,866 |
| Stirling-PDF | 933 | 198 | 735 |
| Total | 25,389 | 4,635 | 20,754 |

Each certificate has actual distinct retained rows for both services:

```text
individualCut(X):
    K = original post-handoff rows minus {X}
    Z = find row in K with equal complete C2 entry service
    Y = find row in K with covered paired C5 output service
    return (Z, Y) if both exist
```

The C2 and C5 rows can differ. Two origins of the same X cannot supply
these witnesses. Full-mark point equivalence and empty-exclusion output
selector equivalence retain the existing scope. FLOW and GROUP entries
do not use concrete-point normalization. A point-to-MAY C5 adapter covers
only the proved same-path or first-counted-field case.

The [row-cut proof package](../../spec/lean/proposals/redundant-demand-row-20261112/README.md)
proves generic singleton and joint row cuts. Its 72 axiom audits passed.
All 4,635 observed native-row guard instances passed in 145 Lean batches.
The independent checker decoded 5,564 complete literal rows and rebuilt
every generated guard. The 11 existing native operator tests were reused
after their source, artifact and result hashes were checked. They were not
rerun. All 11 new offline adversarial controls passed.

The full independent corpus check reconstructs all 293,704 origin-to-row
memberships at the nine barriers. It also checks all 9,270 individual
service-witness memberships. A failed coverage test does not prove
necessity. No necessity verdict is accepted.

The separate joint plan removes 3,490 rows and retains every provider in
the same final K. The proof and independent review check all 90,931 rows
in original O, all 6,980 witness memberships, and 3,490 observed guard
instances in 110 Lean batches. The 1,145 individually redundant rows kept
as joint providers retain their individual REDUNDANT verdicts.

| Project | Joint removals | Individually redundant but kept | Final rows in K |
| --- | ---: | ---: | ---: |
| OWASP | 0 | 0 | 1,153 |
| Conductor | 3,372 | 1,065 | 85,420 |
| Stirling-PDF | 118 | 80 | 868 |
| Total | 3,490 | 1,145 | 87,441 |

These are offline proofs. No removal is installed in the analyzer.
They are coverage/subsumption certificates, not closed-evolution proofs.
The retained repeating families remain investigation targets. No claim
that repetition ends follows from these counts.

The joint plan retains 21,899 rows from the repeated target set: 1,153
OWASP, 19,931 Conductor and 815 Stirling-PDF. This is residual repetition,
not 21,899 new individual OPEN verdicts. The individual OPEN total remains
20,754. No evolution family has a checked closure/removal certificate yet.

## Evolution investigation

The first selected FLOW row belonged to
`BenchmarkTest01985#doSomething(HttpServletRequest, String)`:

```text
Forward handoff run-9 and run-11:
    entry: ret.bytes.[any]/FLOW
    output: arg(1).bytes.[].*/FLOW
row: a76bfe144f2f2ecdbdac6793c1da1e593f751339c9a222ad219c5eb81ad64621
target: 0d3aa013ee77e55276109939458d371bc082f6ebd0784230ce1dce5a87da872a
```

This row has no existing retained service cover. The snapshots prove
repetition; they do not record complete C2 offers, emitted initials or C5
parent dependencies. The graph stores exact demand nodes and all summary
projection producers, with the missing causal links explicit. Its folded
index has 253,009 observed nodes, with every run and field limit retained.
It does not invent `X → Y → X` from matching field names.

A separate historical passive capture observes a different method and
does not supply this row's late execution history. It cannot fill the
original run's missing inputs. This target stays OPEN. The new capture
does not reproduce its late demand, so it cannot supply that missing history.

### Current target and observed cycle

The new capture has 24 matching repeated FLOW rows in four methods. Their
complete demand sets match the original capture at each comparable barrier
from run-3 through run-11. Seven other selected methods lose their debt
after run-5. Their original rows stay OPEN; disappearance in a separate
execution is not a removal proof.

The coordinated queue now selects this original row, which also repeats in
the new capture:

```text
BenchmarkTest01000$Test#doSomething(HttpServletRequest, String)
X = (entry ret.[any]/FLOW ; output param.bytes.*/FLOW)
target: 1025a1973fd0c88c16ee906e3ad746a205f317f3daea0c3bca5b7683d533162a
row:    95b0a29e850ff1d5d9094e3d158c20bd8584fc34902f006f2535566935ca9378

H9: X
run-10 raw: ret.*/FLOW -> param.[any]/FLOW, DEMAND
    C5 selects param.bytes.[any]/FLOW; it does not create this MAY tail.
H10: Y = (entry param.bytes.[any]/FLOW ; output ret.*/FLOW)
run-11 raw: param.bytes.*/FLOW -> ret.[any]/FLOW, DEMAND
    C5 preserves this result; it does not create this MAY tail.
H11: X
```

Here `param` is the code's String parameter, native argument 1. The code is:

```java
public String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
            Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
```

The capture records all 135 submitted offers and their C2 families for
this method. Only STAR originals produce the observed raw MAY/FLOW demand
summaries. EXACT and MUST originals produce their corresponding NORMAL
results. The four repeating methods receive additional field STAR/FLOW
offers. A concrete root MUST offer cannot replace an abstract FLOW offer
by mark geometry alone. Caller context is not recorded at this offer hook;
do not infer cross-context input subsumption.

The diagnostic trace establishes this recurrence and locates uncertainty
before C5. It does not establish closure under later inputs or field limits.
The first capture did not record the intra-procedural MAY operation. A
second capture records the native operations described below. No row
verdict changed when the coordinated queue moved to this target.

### Native MAY creation in the constructor

The second diagnostic scan reached, completed and accepted run-11. It
retained the same 2,633 finding identities and sink fingerprints. All
3,362 observed synchronous micro-frames closed, with zero observer errors
or drops. This is a diagnostic run, not a performance comparison.

At the String constructor instruction, the observer records these cells.
The `callee` prefix denotes constructor formals. It does not denote the
enclosing method's `request` or `param` variable. Both compiled relations
are NORMAL (`edgeDemand=false`), with FLOW marks and empty exclusions.

```text
Forward run-11, global field limit 10:
    enclosing initial: param.bytes.*/FLOW
    actual:            callee.arg(0).*/FLOW, NORMAL
    compiled relation: callee.arg(0).[].*/FLOW -> callee.this.*/FLOW
    native result:     callee.this.[any]/FLOW, DEMAND

Backward run-10, global field limit 9:
    enclosing initial: ret.*/FLOW
    actual:            callee.this.*/FLOW, NORMAL
    compiled relation: callee.this.bytes.*/FLOW -> callee.arg(0).*/FLOW
    native result:     callee.arg(0).[any]/FLOW, DEMAND
```

The backward `<string-bytes>` relation has the same behavior. Run-9 also
records the forward case. These native results come from applying a deeper
read to an ancestor STAR fact, without a field-limit cut. Increasing the
limit does not resolve this particular operation when its input stays STAR.
It is separate from the saved-summary STAR-inside policy.

The capture contains all 28 NORMAL-to-MAY callbacks: six compiled-edge
callbacks and 22 LIMIT callbacks. The latter use boundary restriction
limits 1 or 2, rather than the global run limit. Keep these two causes
separate. The [small native regression](bidirectional-first-may-native-cell-20261112.md)
checks STAR, EXACT and MUST inputs in 24 cells, through both AP entry points,
in both directions and at limits 1, 3 and 11.

The selected method's demand sets and complete saved NORMAL packets match
the first capture, and its demand rows match the original barriers. The
whole selected-owner frontier varies between the two diagnostic executions:
24 repeated rows in four methods in the first; 48 in eight in the second.
No scheduling cause is established. Keep each execution's events together.

Micro-IDs prove synchronous nesting, not a complete work-queue dependency
graph. Do not infer a unique link from one micro-output to a later raw C5
candidate from literal equality alone. The capture explains the native MAY
creation. It does not prove that all future refinements are covered, or
that the repeated row is redundant.

The fixed saved basis also fails a universal precise-output cover test for
this current row. For fresh distinct opaque fields f and g, native C2 and
C5 admit this hypothetical NORMAL relation:

```text
ret.f.*/FLOW -> param.bytes.g.*/FLOW
```

All 31 saved scalar memberships were retained in the probe. Its NORMAL
readouts keep f after a known prefix; none covers `param.bytes.g.*`.
Two coarse saved-MUST readouts cover that region on DEMAND only. The
[constructive model](../../spec/lean/proposals/redundant-demand-1025-envelope-obstruction-20261112/README.md)
checks the field-word obstruction for every suffix; all four axiom audits
are empty. This hypothetical relation is not claimed to come from the
Java body. It rejects that sufficient cover test, without proving either
redundancy or valid sink loss.

The coarse opposite-MUST route also needs a progress proof. It can keep a
caller source path while failing to preserve this owner's output permission.
Of the six retained rows, only X accepts the hypothetical suffix-changing
result. The sibling root-MAY row admits the same initial but rejects that
output. Caller coverage alone does not prove owner re-entry.

The [coarse-observation model](../../spec/lean/proposals/redundant-demand-1025-envelope-obstruction-20261112/CanonicalObservationGap.md)
shows why equal finite histories do not close this gap: in the proved
empty-exclusion lane, root MAY/MUST can hide a child output for arbitrarily
many coarse rounds, while a later precise input distinguishes the transfer.
Its six axiom audits are empty. A native additive-PASS check now covers all
199 recorded owned-initial events, including 72 EXACT/FLOW companions.
Inserting its derived outputs into the corresponding complete frozen
summary stores changes no retained relation and produces no fresh
publication delta. A later precise input exposes the new NORMAL result;
retained providers do not cover it, and removing X loses its paired C5
output while preserving C2 admission.

This is a local AP component check. It does not establish identical
whole-program prefix scheduling or caller history, execute an augmented
JVM body, or show valid sink loss. The selected row stays OPEN. The complete
package is `cases/owasp-1025-closed-evolution-extension-v1/` in the external
archive. Finite observed compatibility remains weaker than future closure.

### Principal counterexample: a repeated FLOW row is still needed

The [deep-relay regression](bidirectional-repeated-flow-deep-relay-20261112.md)
now supplies a complete native sink-loss control for a generic repeated
FLOW row. A value moves through an eight-field temporary path and then
returns from that same path. The helper has no concrete-mark check.

```text
H3 = H5 = { relay: (ret.[any]/FLOW ; p.*/FLOW),
            main:  (Target ; Zero) }

Baseline, no cut:
    run-9, field limit 8: precise NORMAL copy; one confirmed finding.
    Natural end: COMPLETE / NO_DEMAND_EDGE.

Remove only relay's row after H5:
    Keep main's row, all NORMAL records, source seeds and NormalTargets.
    run-7, field limit 6: zero findings.
    Natural end: COMPLETE / NO_DEMAND_EDGE.
```

Neither control uses an iteration cap. The one configured sink has the
same rule and location in both controls. The exact H5 set difference is
one whole row. The restricted initials are NORMAL exact FLOW identities;
their stored premises normalize to STAR. Repeated endpoint geometry hides
the temporary depth which later permits a new NORMAL summary.

The source-pinned Gradle/JUnit test and sealed evidence checks pass. Its
four constructive Lean claims model the finite field-limit distinction;
the separate native controls establish the observed sink loss. This is a
native IR/pass-model case, not a JVM lowering or alias-equivalence test.

This case refutes repetition alone. It is not a necessity certificate for
OWASP target `1025a197…`: that unit has different retained providers.
Corpus classifications remain 4,635 REDUNDANT, zero NECESSARY and 20,754
OPEN. No closed-evolution removal predicate is accepted yet.

### Rejected precise NORMAL envelope test

A native scalar check refutes one sufficient removal test for this row.
Let h be a fresh opaque FIELD accessor. The demand can admit and retain
this hypothetical NORMAL relation:

```text
ret.bytes.h.*/FLOW -> arg(1).bytes.[].h.*/FLOW
```

The saved NORMAL diagonal maps that input to
`arg(1).bytes.[].bytes.h.*`; it keeps the extra `bytes` suffix. The full
29-membership saved basis has no precise NORMAL output that covers the
hypothetical output. Native MUST inversion does supply
`arg(1).bytes.[].[any]` on DEMAND. That is coarse coverage, not a precise
NORMAL delivery.

All 29 memberships, their read roles and ten input cells were checked.
Three constructive Lean claims prove the corresponding finite-word
obstruction. See the [model and trace](../../spec/lean/proposals/redundant-demand-envelope-obstruction-20261112/README.md).
This refutes the universal precise-envelope test. It does not show that
the Java method produces that hypothetical relation, nor that deleting X
loses a valid sink. X stays OPEN. A weaker eventual-refinement proof can
still use the coarse route, but that proof is not established.

### Complete residual FLOW envelope check

The same-layer NORMAL cover check now includes all 10,000 OPEN FLOW rows:

| Project | MAY entry | STAR entry | Total |
| --- | ---: | ---: | ---: |
| OWASP | 66 | 0 | 66 |
| Conductor | 9,365 | 31 | 9,396 |
| Stirling-PDF | 538 | 0 | 538 |

Every row admits a possible fresh NORMAL output that the retained rows
and saved NORMAL providers do not keep at NORMAL. Thus, none passes this
universal immediate-cover test. This does not prove that the actual unit
can produce that output, or that a valid sink needs the row.

The 31 STAR entries belong to three Conductor loop interfaces. Native
checks include all 69,295 DATA demand rows and 22,188 saved FLOW memberships
for those interfaces. Removing each X preserves its C2 family. Full C5
keeps the test output at NORMAL; C5 without X returns two coarser DEMAND
alternatives. Saved NORMAL replay does not give the precise output.

Native canonicalization retains only the shorter alternative. Its next
C2 start is also shorter than the proposed immediate recovery needs.
Counting both raw C5 outputs as independent next-run routes would therefore
be incorrect. A conditional two-step check can recover the precise NORMAL
relation if the original transfer can be analyzed again. The check does
not prove that this transfer remains available after deletion. Future
delivery, source permissions and a complete progress proof remain open.

The external package is `cases/flow-residual-envelope-scan-v1/`. It contains
the complete probe set, native results and six constructive field-budget
and path-alignment lemmas. No verdict changed.

`cases/flow-31-canonical-recovery-v1/README-v2.md` contains the conditional
recovery trace for all 31 rows and 62 wrong-port controls. It labels the
assumed transfers and submitted points explicitly. Its fresh full mark is
a symbolic probe, not an observed project source. Version 2 corrects the
FLOW mark-exclusion placement in the displayed inverse relation. Native
code and results are unchanged; the original sealed evidence is retained.

### Control effects need their own coverage proof

The [FLOW-family control audit](bidirectional-flow-family-control-boundary-20261112.md)
checks why AP result coverage alone is insufficient. A concrete initial can
trigger a new forward NormalTarget even when all its AP results already
have saved NORMAL providers. New NormalTargets bypass Target C5.

After run-1, a FLOW-only initial family cannot directly create a concrete
mark witness or Target. An old NORMAL ND contributor cache also requires a
current accepted concrete leaf before it restores contributors. Native
controls check both statements. Shared block-entry registration remains a
separate delivery obligation: an arrival can register a physical target
and replay other initials at it.

The [finite fan-out model](../../spec/lean/proposals/canonical-normal-fanout-20261112/README.md)
proves the registration join from an empty state for any finite offer
history. Ten theorem axiom lists are empty. Three native controls also
register both real targets before physical work starts. This is a local
join result. The liveness and alias coverage needed to connect it to all
native observations remains open. No FLOW-family removal rule is accepted.

The [dead-local alias fixture](bidirectional-dead-local-alias-wakeup-20261112.md)
shows why this adapter matters. An old concrete initial starts only at
target 3. A later FLOW initial registers target 4 and replays that old
initial there. Reversed alias and source stages then produce a source hit
and DemandTarget. Without FLOW admission, that source is not reached.
All 13 current FLOW AP coordinates have actual saved NORMAL providers.

The fixture supplies the old local and alias plan at a core boundary. It
does not prove that genuine JIR lowering and block input alias closure
permit that state. It refutes unconditional callback independence at this
operator boundary; it proves neither valid sink loss nor corpus necessity.

### Equal captured histories do not prove future closure

The [same-prefix native counterpair](bidirectional-same-prefix-latent-rename-20261112.md)
has identical ordered captured edge/input observations through H5 in four controls.
Both programs retain the NORMAL root copy. Program B has one extra
ordinary PASS relation, which coarse inputs hide until run-11.

```text
H3 = H5 = { helper: (ret.[any]/FLOW ; p.*/FLOW),
            main: (Target ; Zero) }

All four histories through H5: 203 equal observations each.
A-keep and B-keep histories: equal through run-10.

                    Natural last run     Final findings
A, keep X           run-13               {T}
A, remove X at H5   run-11               {T}
B, keep X           run-13               {T,U}
B, remove X at H5   run-11               {T}
```

Each cut removes only X and preserves all other rows, saved NORMAL records,
source seeds and NormalTargets. All controls finish with no demand; none
uses an iteration limit. The hidden relation is a field rename, not an
overwrite, alias operation or protected assignment.

This refutes deletion from those equal captured histories plus a retained root
copy. Five axiom-free Lean claims establish the finite-history distinction
and decision argument. The native fixture establishes the AP execution and
sink loss; the Lean model does not model the complete engine.
The fixture omits raw pre-C5 candidates. It therefore does not rule out a
predicate that also uses that allowed channel.

The case is not a necessity certificate for the selected OWASP row. A
separate corpus check of simple Conductor and Stirling wrappers found no
faithful deep-relay match. Generic examples do not change corpus verdicts.

The campaign still permits only demand, summary and initial-fact histories
as predicate inputs. The question of whether a complete instruction AP
transfer model can also serve as proof input is pending. No expanded proof
scope or analyzer change is assumed.

## Reproduce and retain the evidence

Portable tools are in [scripts/demand_campaign](../../scripts/demand_campaign/rows.py).
The complete data is outside Git under the archive root from
[external-data.json](external-data.json):

```text
docs/reports/data/redundant-demand-rows-20261112/
    manifest.json                     # input/output hashes and runtime pin
    inventory/                        # complete definitions, including empty units
    snapshots/<project>/...           # native post-handoff rows
    repeated/<project>.jsonl.gz        # full repeated and difference sets
    origin-to-row/                    # all producers of each row
    ledger.jsonl.gz                   # frozen OPEN baseline
    evolution/nodes.jsonl.gz
    evolution/completeness.json
    target-index/v1/                  # full B/M/D indexes and folded graph
    classifications/service-cover-v1/ # accepted ledger and certificates
    joint/v1/                        # separate final-K plan and proof
    state.json                       # active ledger/proof hashes
    receipts/
    selections/flow-trace-v2/         # current target; prior target stays OPEN
    cases/owasp-1025-causal-cycle-v1/ # checked C2/C5 recurrence
    cases/owasp-micro-recapture-v1/   # second complete diagnostic execution
    cases/owasp-1025-micro-analysis-v1/project-v2/ # corrected callee labels
    cases/first-may-native-cell-v4/   # 24 native AP cells, no engine scan
    cases/deep-relay-repeated-flow-v4/ # uncapped baseline and sole-row cut
    cases/same-prefix-hidden-rename-v4/ # equal-prefix uncapped counterpair
    cases/flow-residual-envelope-scan-v1/ # all 10,000 OPEN FLOW probes
    cases/flow-31-canonical-recovery-v1/ # conditional two-step AP trace
    cases/ap-family-control-boundary-v1/ # Target and ND control operators
    cases/canonical-normal-fanout-v1/ # finite join proof and native routing
    cases/dead-local-alias-wakeup-v1/ # cross-initial registration effect
    cases/conductor-stirling-deep-relay-triage-v1/ # no faithful match found
```

The runtime is `14d7b63369d94f49d4c551be8405ed7719f267cc`, FULL mode,
with field limits `1,1,2,...`. No old origin verdict was imported.
The graph records are incomplete for causal evolution; that limit is
separate from the complete repeated-row inventory.

Use `state.json` to find the active ledger. The initial manifest and OPEN
baseline ledger stay immutable. The accepted ledger has 4,635 REDUNDANT,
zero NECESSARY and 20,754 OPEN rows. Its OPEN queue has 10,000 FLOW,
2,364 plain concrete-mark, 3,831 Target and 4,559 remaining rows. The
versioned `selections/flow-trace-v2/` record identifies the current target.

The independent post-publication audit checks all 25,389 immutable row
payloads and 78 baseline input/output files. It also rechecks both cut
contexts, every provider membership and the current target's priority.
Its original receipt is `receipts/post-publication-independent.json`.
The queue update has a separate `post-selection-independent-v2.json`
receipt and nine adversarial selection controls. The previous state and
auditor stay in `receipts/auditor-history-v1/`.
The later `receipts/post-same-prefix-root-audit-v1.json` again checks all
25,389 row payloads, original files, individual and joint witnesses, and
the unchanged selected target. It accepts no additional classification.

```sh
python3 scripts/demand_campaign/rows.py --source "$ORIGINAL_CORPUS" --out "$NEW_DIRECTORY"
python3 scripts/demand_campaign/review_rows.py --source "$ORIGINAL_CORPUS" --out "$NEW_DIRECTORY" --receipt "$NEW_DIRECTORY/receipts/independent-row-review.json"
python3 -m unittest discover -s scripts/demand_campaign -p 'test_*.py'
python3 spec/lean/proposals/redundant-demand-row-20261112/check.py
```

Use a fresh output directory. The generator does not overwrite a durable
ledger. No necessity case or closed-evolution removal predicate is accepted
at this checkpoint. The objective remains all targets classified. The
complete-model certificate route is excluded by the selected scope.
Continue with edge-only operator laws and faithful native counterexamples;
keep unsupported rows OPEN.
