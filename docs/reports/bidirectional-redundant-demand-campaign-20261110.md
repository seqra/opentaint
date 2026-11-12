# Redundant demand elimination campaign

The evidence under `data/` is stored outside Git. See
[External report data](EXTERNAL_DATA.md) for its location and restoration.

Finalized 12 November 2026 at the user's request. **The campaign is stopped.**
The [dedicated patterns document](../design/bidirectional-demand-edge-redundancy-patterns.md)
collects the accepted rules with math, pseudocode, examples and proof links.
The fixed three run pairs contain **28,631 repeated method and generated
inner-block edges**. Exhaustive classification remains incomplete.
**8,915 targets are individually redundant and 19,716 remain OPEN.** A
separate offline joint plan selects **6,955** origins. It keeps **1,960**
individually redundant origins as providers. Do not remove all 8,915 together.
No necessity case has passed the required sink-loss gate. No removal is
installed in production.
The last selected target was OWASP `4378d285...`; the Conductor
`0c5f46ce...` case is deferred and remains OPEN. See sections 0.19, 0.21, 0.22 and 0.23.

The [queue status](data/redundant-demand-20261110/queue-status.json) and
[ledger](data/redundant-demand-20261110/ledger.jsonl.gz) are authoritative.
Earlier counts in the investigation history below are not current verdicts.
The separate [finalization record](data/redundant-demand-20261110/campaign-finalization.json)
records the user stop. Archived queue and next-action fields describe the
last research checkpoint; they are not instructions to restart the campaign.

## 0. Current proof contract and classifications

A predicate can use only demands, summary edges and submitted initial facts,
with their complete literal coordinates and run histories. Project source,
CFG properties, rule forms, JVM type analysis, source hits and report state
cannot decide eligibility. General analyzer semantics can prove a uniform
operator law over the allowed inputs.

Assume no iteration limit. The temporary run-11 setting is capture metadata,
not a reason to remove an edge. A proof must preserve every finite later
continuation, including new fields and later field limits.

The [contract correction](data/redundant-demand-20261110/contract-corrections/edge-only-unbounded-v1/receipt.json)
withdrew 1,831 source/cutoff-based verdicts. It restored 714 independent basis
proofs and reopened 1,117 targets. Those withdrawn source, CFG and hard-cutoff
arguments remain historical evidence only. The six eligible query families
then had 5,304 proofs. The ancestor-MAY extension added 334. The earlier
service-basis extension added 1,311, giving a jointly checked set of 6,949.
The user then selected separate individual verdicts and joint selection.
The [new acceptance](data/redundant-demand-20261110/q-separated-individual-joint-v1/acceptance.json)
publishes 1,966 more individual verdicts, for a total of 8,915. Each removes
only its own X from the original guidance O. Its witness may have its own
individual redundancy verdict. The separate joint certificates keep all
their providers outside the entire selected 6,955-origin cut.

| Project | Redundant | OPEN |
| --- | ---: | ---: |
| OWASP | 759 | 1,065 |
| Conductor | 7,833 | 17,953 |
| Stirling-PDF | 323 | 698 |
| Total | 8,915 | 19,716 |

The individual proof checks **20,256 witness memberships** in 8,915 separate
singleton cuts. The joint proof checks **16,168 witness memberships** against
one final retained set. These are different proof contexts. All 28,631
original target payloads and run-pair evidence remain intact.

Use the current read-only auditor:

```sh
python3 docs/reports/data/redundant-demand-20261110/tools/accept-separated-demand-classification-v1.py --live
```

Older immutable auditors check their frozen historical state. Do not derive
a joint cut from the current REDUNDANT_Q statuses or run the former combined
ledger's live auditor against this new contract. The active
[proof contract](data/redundant-demand-20261110/proof-contract.json) keeps
source/CFG/type/report/cutoff families withdrawn.

### 0.1 Accepted generalization: separate retained query services

The [service-basis specification](../../spec/retained-demand-service-basis.md)
and [acceptance](data/redundant-demand-20261110/q-retained-service-basis-v1/acceptance.json)
classify **1,311 additional concrete-mark origins**: 1,276 Conductor and 35
Stirling-PDF. There is no new OWASP, FLOW or Target verdict. The added set has
262 plain and 1,049 protected edges. Protection remains a literal original
membership; the predicate does not merge protected and plain edges.

Each complete projected row supplies two services. One actual final retained
row preserves initial admission (C2), including its support and cursor
profile. A possibly different retained row preserves paired summary
restriction (C5). For example, these are projected demand rows, with their
complete native scope and ports checked:

```text
X: entry a.f.$/T;       exit b.$/U   removed guidance origin
Z: entry a.f.*/T;       exit c.$/V   retained C2 witness
Y: entry a.f.[any]/T;   exit b.$/U   retained C5 witness
```

At late FULL runs, Z has X's complete concrete-point admission profile.
Y has the same paired output as X and accepts each of its stored point
images. This same-path MAY case extends the earlier first-counted-child
case. Y alone does not preserve C2; Z alone does not preserve C5.
Each complete ND projection and physical port needs both services.

The wider rule is not an OR of old whole-origin predicates. Services can
have different providers, and different projections can use different
adapters. All witnesses end directly at actual final retained origins.
No proof DAG, circular anchor or assumed semantic-cover flag is needed.

The accepted cut replaces **2,219 earlier certificates** whose old witnesses
would otherwise be removed. All 5,638 previous full proof rows are archived;
3,419 remain unchanged. The unsafe control that removes only the 1,311 new
origins and keeps the old dependencies is rejected. All 6,949 removals were
rechecked together against the final retained set.

### 0.2 Proof, native correspondence and publication

The complete observed Lean build passed at actual session 18223. All six
modules passed, with 73 constructive axiom audits. The only reported axioms
are `propext` and `Quot.sound`. The main observed check took 99.304 seconds;
the actual-field/unbounded consequence check took 11.367 seconds. These are
proof-build times, not analyzer performance measurements.

The [observed proof receipt](data/redundant-demand-20261110/cases/retained-service-basis-observed-v2/receipt.json)
binds the actual v3 sources, objects and logs. It covers 6,949 nonempty complete
origins, 6,372 full rows, 4,620 distinct service roots and 9,240 actual retained
service witnesses. The
[independent final review](data/redundant-demand-20261110/cases/retained-service-basis-final-review-v1/receipt.json)
passed at 4179/0 and again after sealing at 85771/0. The complete data decoder
also checks the native row and origin trees, absent-key fallbacks and full
literal coordinates. No ND member or port is sampled away.

All 11 native service tests pass. A separate fresh-accessor test passes too.
The fixed entry dictionary has 45 FIELD keys and one ELEMENT key. It is not
a bound on future facts. The formal consequence transports the fixed guard
checks to the actual accessor classifier and uses that classifier for every
future input and raw result. Unknown future fields cannot be treated as
uncounted by default.

The first two large observed proof attempts were interrupted only after
the complete v3 replacement passed. Their source and terminal logs remain.
The proof construction was corrected to keep the actual list grouping and
avoid Meta reduction of large closed values. No candidate data, theorem
statement, analyzer predicate or production transfer changed in that repair.

Root dry run 4296/0 and publication 27645/0 pass the complete dependency and
proof gates. The publication archives the old certificates and preserves all
unrelated ledger rows. No core code, project configuration or runtime filter
changed. No speedup is claimed: raw origins can already share stored demand
rows, so removal counts alone do not measure work saved.

The remaining OPEN priorities are 10,224 FLOW, 1,581 plain concrete, 4,326
Target and 5,551 protected/other edges. The Conductor FLOW target was still
selected at this checkpoint. Section 0.19 records the later selection.
Failure of the accepted predicate is not a necessity proof.

Latest original reached / completed / accepted forward remain OWASP
run-11 / run-11 / run-11, Conductor run-8 / run-7 / run-7 and Stirling-PDF
run-11 / run-10 / run-9. There is no new project scan.

### 0.3 Why the Conductor FLOW edge remains OPEN

The [edge-only obstruction](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/any-flow-multirow-obstruction-v1/receipt.json)
keeps the selected Conductor edge unclassified. In the reverse projection,
the candidate X and 21 retained child rows have the same entry:

```text
X:  q.[any]/FLOW -> p.*/FLOW
Y1: q.[any]/FLOW -> p.c1.*/FLOW
...
Y21:q.[any]/FLOW -> p.c21.*/FLOW
```

Here p and q abbreviate the complete literal prefixes in the archived
edge. They are not new program variables. Let h be a field outside the 21
child selectors. Consider a possible current NORMAL result:

```text
q.*/FLOW -> p.h.*/FLOW
```

X can retain this result at C5. The 21 child outputs are disjoint from h
and cannot retain it. In a later forward query, the root MAY guidance can
admit starts from a fresh concrete child point. The child guidance cannot
serve all such points. Five checked saved NORMAL records preserve the
fresh suffix; their full output set has no replacement root point.

Thus the retained child rows do not prove equal services for every future
query. This does not show that the original project will emit the displayed
NORMAL result, nor that deleting X loses a valid sink. No project source,
JVM type or finite observation can fill that proof gap. This is a rejected
redundancy argument; X remains OPEN, not NECESSARY.

### 0.4 Edge-only scope and missing original inputs

Use the owner and type strings in full literal keys only for identity. Do
not infer enum, immutability, assignability or library behavior from them.
Do not add extra type information to a key to bypass the input restriction.
The accepted predicates use demand rows and actual retained origins. The
current read-only live audit passes for all 6,949 removals and all 11,941
dependency memberships. The withdrawn source/CFG/type/cutoff families stay
withdrawn. Production is unchanged.

Three complete extension screens find no new candidate. Each checks all
21,682 OPEN origins and all 2,401 current retained anchors inside the
original repeated universe:

| Possible extension | Complete new matches |
| --- | ---: |
| [Exception/static concrete-point entry](data/redundant-demand-20261110/cases/service-basis-static-exception-census-v1/receipt.json) | 0 |
| [Concrete output selector covered by a FLOW selector](data/redundant-demand-20261110/cases/service-basis-output-mark-census-v1/receipt.json) | 0 |
| [ZERO/Target entry alias](data/redundant-demand-20261110/cases/service-basis-control-entry-alias-census-v1/receipt.json) | 0 |

These are candidate screens, not new proved laws or necessity results.
Their guards use literal edge coordinates and actual origin membership.
General engine code explains the operators; project type analysis does
not select an edge.

The [original-input inventory](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/exact-flow-initial-evidence-availability-v1/receipt.json)
checks the complete original Conductor stream: 1,616,863 records, zero
observer errors, and 2,395 full selected-owner records at runs 5/6/7. It
finds no captured submitted packets or pre-normalization C2 initial
families for this owner. **The evidence is missing.** This does not mean
that the initials did not execute. A stored STAR/FLOW premise cannot show
whether C2 emitted STAR or EXACT before normalization. A different native
execution cannot supply that original history. The proposed historical
EXACT-probe argument therefore remains unsupported.

### 0.5 A failed baseline exposes a block-admission gap

The [factory/write baseline](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/factory-write-baseline-terminal-validation-v1/receipt.json)
ran once, without an iteration cap or edge deletion. It completed runs
1/2/3 and stopped naturally at run-3 with no finding. Its test process
failed because the required baseline finding was absent. Runs 5 and 7
were not reached. This experiment cannot classify the selected edge.

The [sealed causal trace](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/factory-write-baseline-causal-analysis-v1/receipt.json)
identifies the first decisive same-port rejection in backward run-2:

```text
Owner method demand: ret.out.[any]/FLOW -> arg(0).*/FLOW
Submitted:           ret.out.[any]/T, DEMAND
C2 initial:          ret.out.*/FLOW, NORMAL

AL6 saved NORMAL:    output.*/FLOW -> ret.out.*/FLOW
Backward replay:     ret.out.*/FLOW -> output.*/FLOW

L5 demand at port13: output.Element.[any]/FLOW -> pending.*/FLOW
Offered at port13:   output.*/FLOW, NORMAL
L5 C2 initials:      none
```

Element fits the run-2 field limit of 1. The rejection follows the selected
policy: a shorter actual STAR cannot satisfy a deeper demand. AL6 replay
works before its empty current C2 lookup. Its run-1 transfer is NORMAL, so
it has no outgoing DATA demand. Do not invent a missing AL6 demand or blame
a field budget of 2 there.

Both root factory summaries, `ZERO -> ret.$/T` and `ZERO -> ret.$/U`, remain
NORMAL and persisted. Their persistence does not reopen main's unguided
prefix block at run-3. Saved prefix replay supplies only the first write
temporaries, not the completed 17/21-write values. No outgoing demand then
remains, so the driver stops.

The code-path component proves a finite valid T route through the ordinary
writes and reads. It does not prove a successful abstract execution or a
sink loss caused by deletion. The gap is already present in this unchanged
baseline. No C2, block, summary or stopping rule was changed to force the
example to pass. A correction to those rules would need a separate major
semantic decision.

The fixture reached/completed/accepted-forward barriers are run-3/run-3/
run-3, with zero findings. Original project frontiers stay OWASP run-11/
run-11/run-11, Conductor run-8/run-7/run-7, and Stirling-PDF run-11/run-10/
run-9. The ledger stays at 6,949 redundant, 21,682 OPEN and zero accepted
necessity cases.

### 0.6 Why direct FLOW silence does not prove retirement

A new [supporting model](data/redundant-demand-20261110/cases/late-pure-flow-type-isolation-v1/receipt.json)
proves a small operator fact: a late local FLOW
derivation stays in the FLOW constructor and does not directly trigger a
concrete mark check. Its constructive theorem covers arbitrary finite
schedules. These are AP constructor kinds, not JVM types. This is not a
removal predicate or a proof that a complete actor is isolated.

Three general engine couplings remain relevant:

1. A concrete caller fact can start a FLOW callee analysis. Applying its
   FLOW summary to that caller's concrete binding can produce TAINT and
   reach a sink. Silence inside the callee does not make its summary unused.
2. A FLOW summary can remove covered concrete DEMAND from shared storage.
   Removing the FLOW guidance later does not restore that earlier concrete
   guidance. A proof must cover the resulting next-run frontier too.
3. A FLOW offer can discover another target for an existing block interface.
   `MethodBlockRuntime.offerChild` then queues all existing initials at that
   target, including independent concrete or ZERO initials. Direct lineage
   silence does not preserve that additional work by itself.

Any wider predicate must replace these effects with demand, summary or
submitted-initial witnesses. It cannot assume that a project has no such
coupling from its source, CFG or JVM types. These open obligations classify
no additional edge.

### 0.7 The direct-return variant exposes the same loss in a nested call

The [fresh direct-return baseline](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/factory-write-no-out-baseline-v1/execution.json)
removes only the ordinary `out` wrapper, updates both sink paths, and uses
the corresponding output prefix in its observation. The old failed case
stays unchanged. Twenty constructive point-path audits pass before the
new native launch. No analyzer rule or outgoing demand was changed.

The single native test process completes with exit 1 because the baseline
finding is absent. Its engine completes every run from 1 through 11, then
stops with `NO_DEMAND_EDGE` and zero findings. This is an uncapped
`IncreasingLimits` execution; run-11 is its natural end, not a cutoff.
The fixture reached/completed/accepted-forward barriers are run-11/run-11/
run-11. This does not change the original project frontiers.

The more precise sink seed now fits limit 1. Actual backward run-2 starts
with `ret.Element.$/FLOW`, NORMAL. Saved AL6 replay gives
`output.Element.$/FLOW`, and L5 admits it under its same-path MAY demand.
Thus this experiment opens the earlier blocked cell.

The loss then occurs at the nested `readDeep` call:

```text
Saved run-2 demand for run-3 readDeep:
    arg(0).f1.[any]/FLOW -> ret.*/FLOW

Actual run-3 offers, separately:
    arg(0).$/FLOW, NORMAL       -> C2 emits nothing
    arg(0).*/FLOW, NORMAL       -> C2 emits nothing
    arg(0).a.*/FLOW, NORMAL     -> C2 emits nothing; disjoint path
```

The f1 field fits the current budget. The selected C2 policy rejects the
shorter EXACT and STAR facts. The owner emits only four NORMAL diagonals
at run-3 and no outgoing demand. It produces no summary at run-5/run-7,
so the required selected-origin repetition is absent. Remaining work in
main continues to the natural run-11 end, without the T finding.

This is a second failed baseline. It proves neither redundancy nor a
sink loss caused by deletion. Shortening the counted output prefix also
prevents a direct all-limit identification with the original Conductor
edge. No retry, deletion, production change or target classification was
made. The [independent terminal check](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/factory-write-no-out-terminal-independent-v1/receipt.json)
passes for all 5,523 journal records, 5,015 packed serializations, 6,351
nodes and all 11 completed barriers. CRC/END, hooks and offer frames are
complete, with zero observer errors. A failed baseline assertion remains
distinct from this successful evidence check.

### 0.8 Checked parts for a finite late-provider case

The [finite-start word model](data/redundant-demand-20261110/cases/finite-coarse-start-window-v1/proof-repair-receipt.json)
has 13 constructive audits. It models each fresh write and its field cut,
then reads the same prefix. Building `g` 25 times followed by `h`, then
reading those 25 `g` fields, gives a root MAY fact while the limit is at
most 25. From run-27 onward it gives exact `h` under `1,1,2,...`.

Under `p.[any]/FLOW` demand, those two inputs have different C2 families:

```text
actual p.[any]/T -> p.*/FLOW
actual p.h.$/T   -> p.h.*/FLOW and p.$/FLOW
```

The EXACT companion is not a STAR start. The model proves that this input
route cannot supply a coarse root STAR from run-27 onward. It does not
prove whole-driver termination or rule out other routes. The proof uses
actual `read(build)` operations, not an assumed precision switch. No finite
iteration horizon or future field alphabet is used.

The [training-only native probe](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/training-two-writer-native-v1/terminal-analysis-v1/receipt.json)
passes. A root V factory and one shallow h write supply H. H reads h and
puts it under seven or eight fresh output fields. Its native BACKWARD
NORMAL first persists at run-8. The eighth branch still supplies real
DEMAND, so H retains an h query. At run-9 H starts from exact h/FLOW and
persists a real FORWARD NORMAL with both full output paths. The V sink
becomes NORMAL and the uncapped engine stops naturally at run-9.

The [independent review](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/training-two-writer-native-independent-review-v1/receipt.json)
checks all 321 records, 222 packets, 277 nodes and nine complete barriers.
This is a component result. It has no owner root demand, deletion or
campaign classification.

An additional [dispatch model](data/redundant-demand-20261110/cases/paired-normal-dispatch-obstruction-v1/scope-clarification-v1/receipt.json)
now states its limit explicitly. Replacing an internal traversal with an
equal boundary reply can lose work from other initials. But that model
has no retained-Z or C2/body-preservation hypothesis. It does not refute a
C2-preserving paired-C5 replacement law. Preserving the same internal offer
restores equal dispatch in the model. Keep this distinction in any wider
proof; do not use the model as an unproved impossibility result.

### 0.9 Two further query-cover searches

The [multi-output inventory](data/redundant-demand-20261110/cases/multi-output-query-union-opportunity-v1/receipt.json)
finds six coarse-plus-finer FLOW structures in the complete OPEN set. None
establishes unqualified exact C5 coverage. Native per-row cuts and a raw
MAY query distinguish the missing answer. Equal scalar membership alone
also does not establish equal packed replies. These are query-oracle
obstructions, not native sink-loss examples.

The [equal-count ancestor screen](data/redundant-demand-20261110/cases/equal-count-class-output-ancestor-census-v1/receipt.json)
checks a different possibility: a strict ancestor output path with the same
counted field depth, where only CLASS accessors differ. Equal budgets would
avoid the usual extra-field cut obstruction. It finds no matching row or
complete origin among all 21,682 OPEN origins and 2,401 current anchors.
Every original CLASS-ending output is a concrete EXACT marker; no source
STAR/MAY output has that form. This is literal accessor analysis, not JVM
type analysis. No new law or verdict follows from either search.

### 0.10 The full finite-echo program reaches T at run-35

The [combined baseline](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-trained-owner-baseline-v1/terminal-analysis-v1/receipt.json)
runs ordinary source factories, finite fresh-write chains, H and an owner
with copy/read/write branches. It finishes naturally at run-35, with the
selected valid deep T sink first NORMAL at run-35. All 35 runs complete.
There is no iteration cap, deletion or source adjustment.

Its authoritative final stores repeat these complete plain FLOW origins at
run-5 and run-7, with empty field/mark exclusions:

```text
X:  arg(0).*    -> ret.[any], DEMAND
Y1: arg(0).c1.* -> ret.[any], DEMAND
Y2: arg(0).c2.* -> ret.[any], DEMAND
```

The [independent review](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-trained-owner-independent-review-v1/receipt.json)
checks all 5,026 records, 5,567 packets, 10,472 nodes, 35 barriers and 105
root-factory persistence memberships. It confirms exact full X/Y packet
repetition and the same valid T NormalTarget at run-35.

The native test process exits 1. Its assertion predicted BACKWARD H before
FORWARD H; the combined program actually learns FORWARD at run-9 and
BACKWARD at run-10. Both are after the removal barrier. A separate selector
also compares `MarkExclusions` to `MarkSet.EMPTY`, incorrectly printing an
empty repetition result. The unchanged raw evidence establishes repetition.
Both test errors remain visible; no test source was edited or rerun to turn
the failure green. The semantic finding/repetition gates pass offline.
Do not import the training-only probe's earlier BACKWARD record into this
different execution.

The [additive inventory correction](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-trained-owner-baseline-v1/terminal-inventory-erratum-v1/receipt.json)
also retains a header-only `Target -> ZERO` query at raw line 916. The raw
journal was complete, but the first derived run-7 subset skipped that row
because it has no AP-valued payload. The corrected subset has 50 records
and one control query. Any later control must preserve it. The original
sealed subset and its zero-control count remain historical errors.

At run-7, none of the 17 retained NORMAL packets has an h-bearing premise.
Earlier or pre-barrier h rows are not a retained run-7 provider. Seeds and
target-view text are separately labelled; they are not a typed heap-state
serialization. This baseline alone did not establish sole-origin necessity.
The later paired test is in section 0.11. The original Conductor block/port
mapping remains open. The campaign stays at 6,949 redundant and 21,682 OPEN.

The combined fixture reached/completed/accepted-forward barriers are
run-35/run-35/run-35. The original project frontiers remain OWASP run-11/
run-11/run-11, Conductor run-8/run-7/run-7, and Stirling-PDF run-11/run-10/
run-9. No project scan was repeated.

### 0.11 Removing one repeated demand loses a valid later sink

The [uncapped paired test](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-sole-root-pair-terminal-v2/receipt.json)
passes. Both controls use one immutable program and separate mutable
analysis state. They have equal complete state through run-7 and exactly
555 equal, ordered C2/C5 query records through that barrier. The test then
removes only X's outgoing normalized demand row in the deletion control.
It preserves Y1/Y2, all NORMAL records, seeds, targets and other guidance.

| Control | Natural end | Selected T sink | Other confirmed sinks |
| --- | --- | --- | --- |
| Baseline | run-35, `NO_DEMAND_EDGE` | NORMAL at run-35 | V at run-9; U at run-27 |
| Remove X after run-7 | run-31, `NO_DEMAND_EDGE` | Absent | V at run-9; U at run-27 |

The selected sink has the same physical statement 125 and rule identity in
both controls. It is not a finding from an earlier run. Both controls use
direct `IncreasingLimits`, FULL marks and no iteration cap. A resource
timeout is a test failure, not proof of absence.

The [independent execution review](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-sole-root-pair-terminal-independent-v1/receipt.json)
checks all 9,308 journal records, 10,217 packets, 19,386 nodes, 66 barriers
and 198 source-factory persistence snapshots. A separate
[concrete-path component](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-concrete-validity-v1/README.md)
proves the valid source/read/write/sink branch with nine constructive Lean
audits. That component does not model analyzer admission or convergence.

The actual normalized demand store changes from **11 rows to 10**. The
complete pre-guard run-7 capture has 50 records in both controls. Those raw
summaries and exports remain unchanged: the single removal occurs after
their publication, at the outgoing-guidance barrier. The header-only
`Target -> ZERO` control survives.

The principal matched backward run-8 query shows the first loss of root
guidance. Here `p` means the owner's code argument `arg(0)`; it is a base,
and `c1`, `c2` and `h` are fields. All displayed facts have empty exclusions.

```text
Same original:  ret.*/FLOW
Same raw:       p.[any]/FLOW, DEMAND

Baseline C5:    p.[any]/FLOW
                p.c1.[any]/FLOW
                p.c2.[any]/FLOW

Deletion C5:    p.c1.[any]/FLOW
                p.c2.[any]/FLOW
```

The final run-8 guidance keeps the root MAY entry only in the baseline.
The retained NORMAL owner packet already contains both `p.* -> ret.*`
and `p.* -> ret.u.*`. Those correlated copies do not supply every later
reader relation. Both controls learn H's NORMAL relations at forward
run-9 and backward run-10.

At forward run-27, **the same precise input** `p.h.$/T, NORMAL` reaches the
owner in both controls. The baseline C2 union emits three initials:
`p.h.*/FLOW`, `p.$/FLOW` and `p.h.$/FLOW`, all NORMAL. The deletion control
emits none. The baseline can therefore use the later reader relation and
reach the valid deep T sink at run-35. All source-factory NORMAL records
remain retained in both controls.

The [readable full trace](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-sole-root-pair-causal-note-v1/README.md)
also explains the delay after run-27. A raw NORMAL deep-seven result exists,
but paired restriction first stores shorter DEMAND. The final retained deep
prefix grows through depths 1, 2, 3, 5 and 7 at forward runs 27, 29, 31,
33 and 35. The trace preserves the complete packets, including the extra
`u` leaf at run-27. The final deep-seven summary is NORMAL at run-35.

This is a necessary-demand example for the small program. It disproves
the general claim that repetition plus a saved NORMAL identity makes a
root MAY demand redundant. It does **not** classify the original Conductor
edge. That edge has different field prefixes, an inner-block scope and a
larger provider set. Their complete binding remains required.

The paired fixture's reached/completed/accepted-forward runs are
35/35/35 and 31/31/31. Original project frontiers remain OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9. No project scan or production
analyzer change was made.

### 0.12 Semantic output containment is not enough

A new [constructive operator model and complete shape screen](data/redundant-demand-20261110/cases/c5-output-containment-compaction-obstruction-v1/receipt.json)
keeps current C2 admission identical. Replacing an EXACT concrete output
query with a covering MAY output can still change the final handoff:
a common FLOW summary compacts the plain MAY concrete debt, but retains
the EXACT debt. The next concrete admission can then differ. All 16
constructive audits pass.

The screen checks all 21,682 OPEN origins. It finds 113 relevant diagonal
concrete-entry shapes; 81 have a retained FLOW query with matching geometry.
A matching query is not a future raw FLOW provider or an observed shared
store. These counts establish no new removal predicate or project sink
loss. Applicability remains limited to demands, summary edges and
submitted initial facts. JVM types, source properties, report state and
the temporary iteration limit cannot justify a removal.

### 0.13 Individual redundancy and a joint removal set

The [complete original-state census](data/redundant-demand-20261110/cases/retained-service-individual-vs-joint-v1/receipt.json)
found 948 then-OPEN origins with exactly the same complete, nonempty
projection set as an already classified origin: 916 in Conductor and 32
in Stirling-PDF. Both members repeat in the required original run pair.
Every full mark, field key, scope and physical port is checked.

The first Conductor pair differs only in raw protection. Both emit the same
single next-run query. Keep the raw protected and plain summaries distinct.
Only their outgoing guidance contributions are interchangeable:

```text
Original guidance origins: O contains A and B
emit(A) = emit(B) = {q}

Remove only A: B still supplies q.
Remove only B: A still supplies q.
```

These are two separate, sound individual-removal certificates. They are
not a circular certificate for removing both. Removing both loses this
duplicate witness; a different proof would be needed to remove the entire
query group. This census alone proves no native sink loss from that group.

The former ledger used REDUNDANT_Q as membership in one jointly justified
removal set. It left the retained representative OPEN. That representative
could not pass a sole-edge necessity test in the
original O: its twin still supplies every query. The
[contract review and data explanation](data/redundant-demand-20261110/cases/retained-service-basis-exchange-doc-v1/README.md)
separate these baselines. The user selected separate classification and
joint-selection records. The [recorded decision](data/redundant-demand-20261110/contract-decisions/separate-individual-joint-v1/decision.json)
keeps the original sole-edge necessity test. A kept representative can now
be individually REDUNDANT without being selected for joint retirement.

The [full singleton-certificate package](data/redundant-demand-20261110/cases/retained-service-individual-certificates-v1/receipt.json)
extends that check beyond literal duplicates. It contains 8,915 separate
original-state single-edge certificates, including all 6,949 earlier Q
origins and 1,966 newly classified origins. The
[independent data review](data/redundant-demand-20261110/cases/retained-service-individual-certificates-independent-v1/receipt.json)
checks every complete origin, actual witness and native row binding. Each
certificate removes only its own X and retains its witnesses in O minus X.
The finite Lean binding and independent review passed. The separate
publication gate has now accepted these 8,915 individual verdicts. These
certificates do not justify one 8,915-edge removal set.

### 0.14 A smaller retained basis is possible

The [offline exchange search](data/redundant-demand-20261110/cases/retained-service-basis-exchange-sequence-v1/receipt.json)
uses the same proved service laws. It finds six sequential exchanges: keep
six former removal candidates and remove twelve previously retained
origins. The joint removal set grows from 6,949 to 6,955. The search was
first a dry run; it is now the separately accepted offline plan.

The [independent review](data/redundant-demand-20261110/cases/retained-basis-exchange-sequence-independent-v1/receipt.json)
checks every intermediate set against all 100,947 service profiles. All
67,944 origins outside the repeated universe stay fixed. The final set has
6,955 complete certificates and 16,168 per-projection service witnesses;
every provider is a final retained origin. The final search finds no direct
removal and no valid restore-one/remove-two exchange. Larger exchanges are
unsearched, so this is not a global minimum claim.

The [complete formal binding](data/redundant-demand-20261110/cases/retained-service-joint-6955-lean-v1/README.md)
now passes too. It checks the final 6,955-origin cut as one joint retained
set. It checks all 8,084 source projections and 16,168 service witnesses.
The lookup adds 27 rows and 27 complete origins to the earlier sealed data.
All 70 guard groups pass kernel reduction. The four new Lean modules have
222 passing axiom audits; only `propext` and `Quot.sound` occur.

The [independent compiled review](data/redundant-demand-20261110/cases/retained-service-joint-6955-independent-v1/README.md)
re-reads all 90,931 native rows and 96,575 origins. It checks every removal,
the full joint cut bitmap, all literal bindings and every retained witness.
Unknown rest rows and emissions remain arbitrary shared parameters. The
actual field classifier remains arbitrary outside the 46 stored field
identities. The proof covers all later runs, limits and natural continuation
lengths. It uses no iteration cutoff or project source/type property.

This completes the formal gate for the separate joint plan. The publication
gate accepted it after the user decision in section 0.13. Six restored
providers keep their individual REDUNDANT verdicts. The current ledger has
8,915 individual redundant verdicts and 19,716 OPEN targets. The offline
plan selects 6,955; production behavior is unchanged.

### 0.15 Fixed NORMAL replay preserves a fresh precise suffix

The [exact-input component](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/exact-fresh-normal-replay-frame-v1/receipt.json)
binds all 88 original AL3 packets, 155 scalar memberships and 243 direct or
opposite read views. It retains all seven physical port families. Its 38
constructive audits cover direct AP matching, graft and an optional field
cut for one precise full-T point containing a fresh field h.

The [finite-chain extension](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-old-normal-replay-chain-v1/receipt.json)
adds composition. All 49 audits pass. Every finite chain whose outputs stay
NORMAL preserves the suffix from h, the full mark, original premise, layer
and protection. It cannot reach the lifted deep target when that target
omits h. The proof permits arbitrary chain lengths and fresh field values.

This result ends before alias/caller projection. It does not cover a
DEMAND cut or reset followed by new C2 admission, future new providers,
coarse inputs or the missing original input history. The original Conductor
target remains OPEN.

No project scan was added. Reached/completed/accepted-forward frontiers
remain OWASP 11/11/11, Conductor 8/7/7 and Stirling-PDF 11/10/9. The live
ledger remains 6,949 classified and 21,682 OPEN.

### 0.16 The prefixed case keeps all 21 child demands

The [prefixed native case](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-prefixed-21-slot-terminal-v2/README.md)
tests the same root-versus-child question with the original path lengths.
P has one FIELD, `Iterable.Element`. Q has two FIELDs,
`tasksToBeScheduled` and `Iterable.Element`. Each name denotes its full
literal key. Owner and type strings are opaque identities.

```text
X:   arg(0).P.*    / FLOW -> ret.Q.[any] / FLOW, DEMAND
Yi:  arg(0).P.ci.* / FLOW -> ret.Q.[any] / FLOW, DEMAND
```

X and all 21 Yi repeat at run-5 and run-7. Both controls use one immutable
program and the normal `1,1,2,...` schedule, without an iteration cap.
After run-7, the deletion control removes only X's guidance contribution.
The native next-run store changes from 46 rows to 45. All 21 child rows,
the Target-to-ZERO row, NORMAL providers and confirmed targets remain.
The complete ordered query prefix has 1,632 equal events per control.

| Control | Selected valid T sink | Latest reached / completed / accepted forward |
| --- | --- | --- |
| Baseline | NORMAL at run-35 | run-37 / run-37 / run-37 |
| Remove only X after run-7 | Absent | run-31 / run-31 / run-31 |

Both controls stop naturally with `NO_DEMAND_EDGE`. The same auxiliary U
and training V findings remain. There is one native attempt, actual session
94021, exit 0. All 71,872 journal rows and 68 complete barriers were decoded.
The selected sink has the same location, rule object and physical site 226
in both controls. A separate [concrete-path proof](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefixed-21-concrete-validity-v1/README.md)
checks the valid source-to-sink branch with 17 constructive axiom audits.

The first matched service difference is backward run-8. The same original
and raw result at journal lines 2996 and 33089 produce 22 versus 21 C5
outputs. At forward run-27, the same precise `arg(0).P.h.$/T`, NORMAL,
produces three initials in the baseline and none after deletion. A second
equal offer at run-29 produces one versus none. The H helper's NORMAL
provider is already present in backward run-8 and forward run-9 in both
controls. A later provider alone does not replace the missing admission.

The primary [receipt](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/finite-echo-prefixed-21-slot-terminal-v2/receipt.json)
has SHA-256 `208832e997c5763860787f056ffd3e8bc242c8d38179ef0c032874240cd6735e`.
Root's full read-only recheck passes at 41617/0. An earlier root check
overlapped final artifact sealing and rejected the changing receipt; it
does not supply a passing result. No native evidence was changed.
The [independent terminal audit](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefixed-21-terminal-independent-v1/receipt.json)
also passes, including root recheck 33207/0. It independently decodes the
complete capture and checks the sole-edge deletion and selected sink.

This is a synthetic METHOD case with Argument0 and Return endpoints. It
does not reproduce the original LocalVar19, composite AL3 scope, seven
physical interfaces or all 88 original NORMAL packets. Thus it refutes a
general rule that retires X using only its 21 children; it does not classify
the original Conductor target. That target remains OPEN. The unrestricted
run-1 C2 history was not captured and is not reconstructed.
The [literal interface census](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefixed-21-original-mapping-gaps-v1/README.md)
and [remaining proof obligations](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefixed21-original-al3-lift-gaps-v1/README.md)
keep these boundaries explicit.
The [provider-kind correction](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefixed-21-original-mapping-provider-kind-erratum-v1/README.md)
clarifies that the 88 NORMAL packets are 74 FLOW, 10 TAINT and 4 REACH.
Their 155 scalar members include 132 FLOW, 19 nonzero concrete EXACT
relations and four canonical ZERO-to-ZERO controls. The four controls are
not additional nonzero concrete-mark relations. All these providers remain
part of the original mapping obligation.

The accepted ledger remains 6,949 redundant and 21,682 OPEN. Original project
frontiers remain OWASP run-11/run-11/run-11, Conductor run-8/run-7/run-7 and
Stirling-PDF run-11/run-10/run-9. There is no new project scan or production
change.

### 0.17 Individual service certificates now have a formal binding

The [individual-cut proof package](data/redundant-demand-20261110/cases/retained-service-individual-lean-v1/README.md)
now passes its formal gate for all 8,915 separate certificates. Each case
removes only its own origin X from the original guidance O. Its witnesses
must be in `O minus {X}`. This is not a proof that all 8,915 origins can be
removed together. The user has now selected separate individual verdicts
and joint selection in section 0.13. The later publication uses these
checked singleton instances without treating all of them as one cut.

The binding checks 20,256 explicit C2/C5 witnesses, 6,513 full native rows
and the complete emissions of 9,938 involved origins. The original domain
has 96,575 origins and 90,931 projection rows. Unspecified original rows and
emissions remain arbitrary shared functions, not empty sets. Actual field
classification outside the 46 stored entry-field identities is unrestricted.
The final theorem covers every later run, field limit and finite continuation
length. It does not use the run-11 cutoff, source, JVM types or report state.

There are 286 passing axiom audits. Only `propext` and `Quot.sound` remain.
The immutable logs keep all rejected and superseded attempts. In particular,
one compiled draft used an unintended classical axiom in a witness-inequality
helper. That draft is excluded. The final helper uses explicit decidable
equality, and its consequence module passes the constructive axiom gate.

The [receipt](data/redundant-demand-20261110/cases/retained-service-individual-lean-v1/receipt.json)
has SHA-256 `8d298320f8e116bc2998c90ff7d5f0870fd56a16ffd76d9e044f9bd332306d3f`.
Root's complete read-only data, object and axiom recheck passes at 56352/0.
The [independent compiled-proof review](data/redundant-demand-20261110/cases/retained-service-individual-formal-independent-v1/receipt.json)
passes at 41191/0. It parses the actual row/origin trees, all 90 guard groups
and every singleton certificate, and checks the compiled object provenance
and final axiom audits. Its receipt is
`04869fe24c740b5c6588b5f45e363707d225c67cc5489c5eafbf331c34e3a2f8`.
There was no native run, production change or new original-target verdict
in this proof build. The later publication accepted the 1,966 additional
individual verdicts. It still does not select all 8,915 for joint removal.
The original project iteration frontiers remain those in section 0.16.

### 0.18 A selector law adds no new stored-demand cases

The [output-selector kernel](data/redundant-demand-20261110/cases/demand-output-must-selector-kernel-v1/README.md)
proves one additional operator law. At the same DATA base, full path and
full mark, with empty selector field exclusions, a C5 output selector with
MUST, MAY or STAR gives the same complete restriction result and relative
field budget. This does not equate raw MUST facts, initial admissions or
saved-record applications. It acts only on an already-oriented C5 exit.

The formal component passes 17 new constructive claims and its 20 dependency
audits, using only `propext` and `Quot.sound`. The independent source audit
covers direct and prepared C5, protection, output-base support and loop
observations. It preserves negative examples for nonempty selector
exclusions, EXACT selectors and changes to the raw fact tail.

This law adds no campaign candidate. Handoff already converts MUST to MAY,
and the native builder rejects literal MUST at either DATA demand endpoint.
The [complete frozen census](data/redundant-demand-20261110/cases/demand-output-must-selector-census-v2/README.md)
checks all 90,931 projection rows, 96,575 origins and 28,631 targets. It finds
zero MUST endpoints, zero changed comparison keys and zero additional
whole-origin candidates. All per-target results are retained. No new tail
policy or builder change is proposed.

V2 uses an immutable ledger snapshot. Its summary and complete result dump
are byte-identical to V1, which used the then-current live ledger path.
The [independent final review](data/redundant-demand-20261110/cases/demand-output-must-selector-final-independent-v1/receipt.json)
checks that correction, the full census and the compiled proof. The durable
census receipt is `6ecde17162480e02766e9210f21c3b392cdb4910efbacb9426a835f128815393`.
The earlier individual-versus-joint counts are unchanged. No native analyzer
or project scan ran for this investigation.

### 0.19 The next FLOW target uses the complete original provider basis

This section records the selection checkpoint before the separate
classification publication in section 0.21.

The [new readiness inventory](data/redundant-demand-20261110/cases/flow-method-interface-readiness-v2/README.md)
examines 929 unresolved METHOD FLOW targets in 86 owners, after setting aside
the 8,915 individually supported cases. It reads the original persisted AP
snapshots to EOF: 248,802 OWASP packets, 221,000 Conductor packets and 240,597
Stirling-PDF packets. It retains both native directions, whole packets,
scalar memberships, owner inner-block interfaces and the three-run histories.

No complete zero-provider basis exists in this set. Eleven owners that
looked empty in an older filtered export have nonempty original bases.
For example, target `003af0b2...` has 16 NORMAL packets and 31 scalar
memberships. The old export omitted methods that were already classified
at its earlier checkpoint. Its absence was missing coverage, not zero
providers. A failed lookup in a filtered research file must not establish
an empty native store.

The coordinator has deferred the original Conductor `0c5f46ce...` target
without changing its OPEN status or discarding evidence. The prefixed
METHOD counterexample still does not map its LocalVar19, AL3 and seven-port
provider frame. The next [selected target](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/README.md)
is OWASP `4378d285...`, in
`BenchmarkTest01418.Test.doSomething`, repeated at run-9/run-11:

```text
X: arg(1).<string-bytes>.*/FLOW -> ret.[any]/FLOW, DEMAND
```

Its complete owner basis has 16 saved NORMAL packets and 29 scalar members:
28 FLOW and one ZERO identity. Seven members have MUST tails. All packets
use METHOD scope; there are no additional owner block interfaces, static
providers or nonzero concrete providers in this AP export. The paired
incoming store has six rows.

Another retained row has X's complete C2 entry but a different output.
The existing service-basis rules therefore preserve C2 but cannot replace
X's C5 permission. Saved NORMAL and MUST records also exist and run in the
caller before current demand admission. Their effect must be traced before
claiming necessity. Neither a failed C5 guard nor a local reply difference
is a valid sink-loss case.

The original raw submissions, C2 initial stream and cumulative NormalTarget
store remain missing evidence. Complete saved AP coverage does not prove
body completeness or future input closure. No source, CFG or JVM property
was used as a retirement guard or to infer those missing values.
The [independent original-stream audit](data/redundant-demand-20261110/cases/flow-method-interface-readiness-independent-v1/receipt.json)
reconstructs all 929 targets, 86 owners, full provider packets and histories.
Its separate [selected-archive check](data/redundant-demand-20261110/cases/flow-method-interface-readiness-independent-v1/selected-archive-bridge-v1/receipt.json)
binds the selected case's 16 packets, 29 scalar members, 55 current edge rows
and 18 three-run incoming links. Both checks pass without a native rerun.

The accepted ledger remains 6,949 redundant and 21,682 OPEN. The required
individual-versus-joint decision remains pending. Latest original reached /
completed / accepted forward remain OWASP run-11 / run-11 / run-11,
Conductor run-8 / run-7 / run-7 and Stirling-PDF run-11 / run-10 / run-9.
There is no new project iteration or production change.

### 0.20 The repeated root demand has separate C2 and C5 effects

This section records the operator checks before the separate classification
publication in section 0.21. It makes no original-target verdict.

All applicability tests use demand edges, summary edges and submitted initial
facts only. Owner and type strings are opaque keys. Project source, CFG,
JVM properties, rule forms, report state and the temporary run limit cannot
justify a removal. The selected OWASP `4378d285...` target remains OPEN.

The [original store history](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/run8-to-11-history-v1/README.md)
now includes the incoming guidance for each run, not only the rows produced
at that run's barrier:

| Barrier | Current NORMAL | Current DEMAND | Saved NORMAL packets / scalar members | New saved packets |
| --- | ---: | ---: | ---: | ---: |
| run-8 | 9 | 6 | 14 / 25 | not compared |
| run-9 | 14 | 6 | 16 / 29 | 2 |
| run-10 | 9 | 6 | 16 / 29 | 0 |
| run-11 | 14 | 6 | 16 / 29 | 0 |

The two new run-9 packets are NORMAL FLOW MUST relations. Their premises
are `arg(1).<string-bytes>.[].MUST` and `arg(1).bytes.[].MUST`. Each packet
has both `ret.<string-bytes>.MUST` and `ret.bytes.MUST` conclusions. They
add four scalar memberships. Thus the saved basis was not stable before
run-9. The complete current edge sets and outgoing projections at run-9
and run-11 are equal.

A projection produced at barrier r guides run-(r+1). The older sealed
`full-incoming-history.json` uses the producing barrier as its run label.
The new transition file states both barriers. Actual submitted facts and
C2 initial streams are still missing; they are not empty sets.

The [native operator fixture](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/native-frame-preparation-v2/README.md)
compiled and all four tests passed. The [sealed result](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/native-frame-results-v1/README.md)
checks all 112 typed events against the terminal XML and exact source pins.
It restores all 16 original packed
NORMAL records and their 29 scalar memberships. Native persistence retains
the complete packet grouping. The 58 direct/opposite positions are read
roles, not 58 successful applications. The seven MUST memberships remain
in their five original packets.

The full six-row demand store and the store with only X removed emit equal
ordered C2 initials for the six tested full-mark offers: root EXACT/NORMAL,
STAR/DEMAND and MAY/DEMAND, each plain and protected. The retained row Z
has the same complete C2 entry as X. Its paired output is the distinct
`arg(1).bytes.*` path. Equal C2 admission does not give it X's C5 permission.

One conditional native cell shows that distinction:

```text
Normalized current premise: ret.*/FLOW
Raw current conclusion:    arg(1).<string-bytes>.fresh-h.*/FLOW, NORMAL

All six demand rows:       retain the raw conclusion
Only X removed:            reject the raw conclusion
```

`fresh-h` is a full opaque FIELD key absent from all old prefixes. This is
a stated operator input, not a captured result from the original body.
The resulting conditional NORMAL relation produces a NORMAL exact full-T
fact at that new path. No immediate reply from the complete old frame
produces that same exact fact. Both protection memberships are tested.

The old frame still produces positive NORMAL exact results at the shorter
`arg(1).<string-bytes>` path. Its opposite-direction MUST records also
produce coarse MAY/DEMAND replies. These replies remain in the comparison;
later C2, caller work or new records may use them. The fixture separately
checks all five MUST packets with definite uniform inputs: ten positive
flag cells, fourteen scalar assertions and thirty nonuniform rejections.
An exact-only TAINT packet with a MUST header is not treated as uniform
taint when its any mask is empty.

The [root-MAY preimage proof](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/root-may-preimage-v1/README.md)
rules out one possible cause of X. At this empty-path output selector, a
positive C5 field cut cannot create a root MAY from a nonempty path. After
FLOW normalization and native packing, a final root MAY must come from a
raw root MAY/DEMAND or raw root MUST/DEMAND. Thus this root result was
already DEMAND before C5. It was not a NORMAL candidate newly demoted by
this field cut. The fourteen constructive Lean audits pass; only `propext`
and `Quot.sound` occur. This is a scalar preimage law, not complete native
metadata equality or a retirement proof.

These checks reject the weaker claim that equal initial admission plus
saved NORMAL records makes X redundant. They do not prove that the
original body produces the conditional cell or that deleting X loses a
valid sink. Original caller inputs, the raw producer path and later coarse
reply use still require evidence. No new edge is classified and no runtime
removal is installed. At this operator-check checkpoint, the ledger was
6,949 redundant and 21,682 OPEN. Section 0.21 records the later publication.

The [independent history review](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/history-independent-v1/README.md)
re-decodes the archived packed records and confirms the barrier orientation
and run-9 additions. It checks complete current rows for run-9/run-10/run-11.
The run-8 current totals remain bound to the original-stream extraction;
this package does not claim to archive all run-8 current rows.

An output-mark generalization was also checked against its existing full
census. A retained FLOW output selector could potentially cover a full-T
selector with the same paired geometry. The unchanged 90,931-row domain
has no such retained row pair, even before checking mark exclusions.
The [reuse check](data/redundant-demand-20261110/cases/service-basis-output-mark-reuse-v1/receipt.json)
confirms the current ledger and engine pins. No duplicate census, new
formal law or new classification follows from this zero-coverage idea.

Latest original reached / completed / accepted forward remain OWASP
run-11 / run-11 / run-11, Conductor run-8 / run-7 / run-7, and Stirling-PDF
run-11 / run-10 / run-9. The operator tests execute no new project iteration.
The failed first fixture compilation is retained; its only repair was an
explicit import of the engine's `Target` type in a new fixture version.

### 0.21 Individual verdicts and joint selection are now separate

The user selected separate records. The [publication acceptance](data/redundant-demand-20261110/q-separated-individual-joint-v1/acceptance.json)
is complete. It adds 1,966 individual redundancy verdicts and keeps the
original sole-edge necessity test. No reduced-plan necessity baseline is
used. The [predicate specification](../../spec/individual-retained-query-service-cover.md)
defines both executable checks and their proof scopes. The complete target
universe remains 28,631.

| Project | Individual REDUNDANT | Joint selected | REDUNDANT kept in plan | OPEN |
| --- | ---: | ---: | ---: | ---: |
| OWASP | 759 | 719 | 40 | 1,065 |
| Conductor | 7,833 | 6,009 | 1,824 | 17,953 |
| Stirling-PDF | 323 | 227 | 96 | 698 |
| Total | 8,915 | 6,955 | 1,960 | 19,716 |

Each individual certificate retains every original guidance origin except
its own X. The separate [joint plan](data/redundant-demand-20261110/joint-retirement-plan.json)
has one final retained set of 89,620 origins from the full 96,575-origin
domain. Its selected set is a subset of the individually redundant targets.
Six providers restored by the joint search keep their individual REDUNDANT
verdicts. The plan does not label them necessary.

The [independent publication review](data/redundant-demand-20261110/cases/individual-joint-publication-independent-v1/README.md)
checks all 28,631 target payloads and original run evidence. It keeps all
6,949 prior proof histories and old evidence. It checks all 20,256 individual
and 16,168 joint witness memberships. It rejects self-witnesses in a
singleton cut, witnesses inside the whole joint cut, and the unsupported
use of all 8,915 individual certificates as one deletion set.

Root published once at 89406 / 441f03 / exit 0. The new live auditor passes.
A separate post-publication check passes at 18578 / f8e543 / exit 0. The
active ledger is byte-equal to the immutable classification snapshot bound
by the joint plan. The plan can thus retain its fixed proof snapshot even
when later individual classifications are added. Its providers must remain
retained in that plan.

The remaining priority counts are 9,950 FLOW, 1,476 plain concrete-mark,
3,731 Target and 4,559 other edges. The selected OWASP `4378d285...` case
is still OPEN. No original necessity case has passed the valid sink-loss
test. No analyzer or production retirement change is included.

Further work on that case separates an old coarse reply from a new current
relation. The [MAY reset trace](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/may-reset-c2-resumption-v1/README.md)
binds all old replies and literal query rows. Opposite MUST replay produces
Argument-base MAY/DEMAND replies. Current Return-base C2 entries reject
them at the same interface. Conditional re-entry through historical forward
rows can start NORMAL FLOW work. It does not turn the concrete T reply into
a NORMAL T fact. Caller routing and body output remain separate obligations.

The [typed schema review](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/may-reset-typed-frame-independent-v1/README.md)
checks 29 compiled constructive claims for a declared unary model. It does
not prove that every native step maps into that model. The preparation's
over-approximation wording is design intent, not a certified native closure.
No retirement or necessity verdict uses this partial frame. A separately
supplied new NORMAL FLOW relation can still replay on an outer NORMAL T
caller; the old frame does not prove that new support absent.

The [input-capture audit](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/input-evidence-availability-v1/receipt.json)
finds no suitable original submitted/C2 stream in its reviewed capture
families. Scope records and normalized summaries do not supply that stream.
A passive owner-filtered recapture is prepared under the original project
configuration. It is not compiled or launched. Actual call-site admissions
must stay distinct from synthetic C2-image checks used inside restriction.
Both run-9 and run-11 must come from the same new execution; no old/new
trace is joined into one run pair.

Latest original reached / completed / accepted forward remain OWASP
run-11 / run-11 / run-11, Conductor run-8 / run-7 / run-7, and Stirling-PDF
run-11 / run-10 / run-9. No new project iteration ran during publication.

### 0.22 The fresh capture finishes, but does not reproduce the selected history

A new serial OWASP scan used the same frozen runtime, FULL marks, `1,1,2,...`
field limits, 8 GiB heap and 1,000-second analysis limit. Content checks match
all 67 project/rule inputs and all 22,912 model files. The scan reached and
completed **run-11**, and accepted forward **run-11**. It reports the same
**2,633** findings. Exact SARIF sink locations, fingerprints and multiplicities
match the original. The run-11 stop is capture metadata only.

The [complete comparison](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-comparison-v3/postflight-review-v1/README.md)
finds a different selected-owner history. Its full NORMAL packet set is a
subset of the original set; no new provider appears.

| Barrier | Original NORMAL packets / memberships | Fresh NORMAL packets / memberships |
| --- | ---: | ---: |
| run-8 | 14 / 25 | 10 / 19 |
| run-9 | 16 / 29 | 10 / 19 |
| run-10 | 16 / 29 | 10 / 19 |
| run-11 | 16 / 29 | 10 / 19 |

At run-9 and run-11, the original owner has 12 packed current rows, six outgoing
origins and six projections. All three fresh sets are empty. The fresh window
has no actual submitted offers, emitted C2 families, owned initial admissions,
raw summary candidates or C5 queries for this owner. Its journal is complete:
84 rows, zero callback errors, complete barriers and driver commits. This is
an observed empty window in the new execution. It says nothing about the
missing original C2 window.

The six original-only NORMAL packets contain six STAR and four MUST
memberships. They are two backward reader packets, two forward element-input
STAR packets and two forward element-input MUST packets. ZERO is shared. A
ControlZero display name is not a different constructor key. The
[exact delta](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-empty-window-comparison-v1/README.md)
keeps all complete packet shapes, directions, fields and protection data.

The first selected packet snapshot differs at run-8. The complete INFO/DEBUG
log comparison locates an earlier difference: the selected owner is analyzed
in both runs 1–5, but its outgoing run-5 row count is two in the original and
zero in the fresh run. The fresh owner is not analyzed after run-5. Target
counts match through run-4 and first differ at run-5. A still earlier global
frontier differs in backward run-2: 20,237 rows in 4,296 original method keys
versus 20,340 rows in 4,308 fresh keys. Thirteen opaque demand-count keys
differ there; the analyzed-key set is equal. Run-3/run-4 maps and frontier
counts agree again. Counts do not locate the first internal cause.
[Complete log comparison](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-whole-log-comparison-v3/receipt.json).

A separate read of the closed original trace now preserves all 355 selected
rows. The exact selected FLOW membership already occurs at run-3 and repeats
at run-5, run-7, run-9 and run-11. Its complete typed premise, conclusion
header, exclusions and plain flag match; this is not a name-only match.
[Original early history](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/original-selected-early-history-v1/receipt.json).
The fresh earlier submitted/C2 history was not captured. Matching findings do
not prove equal summary or demand history. Do not join the fresh empty window
to the original run pair, and do not import it as the original submitted facts.
Target `4378d285...` remains OPEN. No new redundancy or necessity verdict follows.

The passive observer was checked before the project launch. The first observer
compiled but failed JVM verification; it was preserved and never used for a
project scan. A fresh version passes `-Xverify:all`, all 49 expected hook
locations, 16 original full packets / 29 memberships, ZERO/empty/MUST/ND/
protection controls, and raw compact-store versus native packet decoding.
[Independent smoke review](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-smoke-independent-review-v3/receipt.json).
Its audit also records a corrected class-digest binding: an earlier parser
hashed the last Code attribute for some classes. A separate full-byte inventory
now binds all 1,096 raw classes, eight transformed classes and observer entries.
The observer JAR and frozen source were not changed during the scan.

The [portable new artifacts](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-artifacts-v3/receipt.json)
retain the closed journal, full analyzer log, classpath manifest and observer.
The [strict validation](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-validation-v3/capture-validation.json)
is separate from the failed history-compatibility check. Timings include
observer overhead and are not performance measurements.

Next, inspect the earlier selected history and the original observer's generic
export path. A broader run-1 to run-11 capture is in source preparation only.
Do not assume that export allocation or scheduling caused the difference.
Production source and all accepted classifications remain unchanged: **8,915
individual redundant, 19,716 OPEN, 6,955 joint selections**. Original frontiers
remain OWASP run-11 / run-11 / run-11, Conductor run-8 / run-7 / run-7, and
Stirling-PDF run-11 / run-10 / run-9 (reached / completed / accepted forward).

### 0.23 The earlier fresh trace shows the intended refinement step

The second new OWASP scan captures the selected owner in runs 1–11. It uses
the same frozen runtime and original configuration. It reaches, completes and
accepts forward **run-11**, with the same **2,633** findings. The closed journal
has 860 rows, 188 balanced contexts, 35 actual offers and emitted families,
48 owned-entry events, 153 raw candidates and 54 C5 queries. No callback error
or packet drop occurs. Run-1 owned entries are captured; a complete run-1
submitted-input pipeline is not claimed.
[Strict validation](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-validation-v4/capture-validation.json).

In this new execution, the same complete submitted packet is seen at run-3
and run-5. Its effective fact is `arg(1).<string-bytes>.$/T`, NORMAL. It is an
exact concrete point; its TAINT packet header's ANY_TAINT tag does not make
it a uniform subtree. Its field path, mark, exclusions and layer are equal.
The demand changes:

```text
run-3 admission
  demand entry:     arg(1).[any]/FLOW
  submitted:        arg(1).<string-bytes>.$/T, NORMAL
  emitted initials: arg(1).<string-bytes>.*/FLOW, NORMAL
                    arg(1).$/FLOW, NORMAL

run-3 summary path
  raw candidate:    arg(1).<string-bytes>.*/FLOW -> ret.[any]/FLOW, DEMAND
  C5:               keeps that candidate
  final store:      contains the selected X

run-4 summary restriction
  raw conclusion:   arg(1).[any]/FLOW, DEMAND
  C5 conclusions:   arg(1).bytes.[any]/FLOW, DEMAND
                    arg(1).<string-bytes>.[any]/FLOW, DEMAND
  handoff:          these child positions guide run-5

run-5 admission
  demand entry:     arg(1).<string-bytes>.[any]/FLOW
  submitted:        arg(1).<string-bytes>.$/T, NORMAL
  emitted initial:  arg(1).<string-bytes>.$/FLOW, NORMAL

run-5 summary path for that exact job
  raw return:       arg(1).<string-bytes>.$/FLOW -> ret.$/FLOW, NORMAL
  normalized/C5:    arg(1).<string-bytes>.*/FLOW -> ret.*/FLOW, NORMAL
  final store:      NORMAL results; no selected X
```

The `bytes` path follows the same admission change. Uniform-root offers start
MUST jobs separately. The fresh run-5 has no raw `ret.[any]/FLOW, DEMAND`
candidate. Thus this fresh X disappears before C5; C5 does not discard an
already produced X there. First observations and exact context links are
available, but the observer does not capture the summary-store fresh-delta
return and does not prove a unique first publisher.

The original and this fresh owner's complete states at run-3 **and run-4**
match: all current packets, retained NORMAL records, projections and complete
outgoing origins. At run-5 their four NORMAL current packets still match.
Only the original's two DEMAND packets are absent in the fresh state. Original
submitted facts and callee activity remain missing. Equal boundary state
cannot establish equal subsequent inputs or producer paths. The traced
admission step explains fresh run-3 to run-5; it does not explain why original
run-5 still emits X. No original input history is reconstructed from a STAR
summary premise.

The [detailed transition](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-selected-trace-results-v2/new-precision-transitions-b2-f3-b4-f5.json)
keeps all eight complete common packets, including their distinct full marks.
The [independent comparison](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-comparison-v4/postflight-review-v1/README.md)
and [portable closed capture](data/redundant-demand-20261110/cases/owasp-method-4378-flow-v1/passive-recapture-project-artifacts-v4/receipt.json)
keep the two execution histories separate.

The selected target and all verdict counts remain unchanged. This result
identifies a concrete earlier trace to investigate; it is not an elimination
predicate, a proof of necessity or a proof based on the run-11 cutoff.

## 1. Fixed runtime and completed captures

The runtime is `14d7b63369d94f49d4c551be8405ed7719f267cc`. The production
core, models, rules and scripts still match it. The
[manifest](data/redundant-demand-20261110/manifest.json) records the exact
source Gradle launches, configurations, observers and input hashes. Project
scans ran serially, with FULL marks and the `1,1,2,...` field-limit schedule.
Observer times are diagnostic measurements, not optimization results.

| Project | Compared runs | Removal after | Latest reached | Latest completed | Latest accepted forward | Findings |
| --- | --- | --- | --- | --- | --- | ---: |
| OWASP | run-9 / run-11 | run-11 | run-11 | run-11 | run-11 | 2,633 |
| Conductor | run-5 / run-7 | run-7 | run-8 | run-7 | run-7 | 7 |
| Stirling-PDF | run-7 / run-9 | run-9 | run-11 | run-10 | run-9 | 32 |

Conductor timed out in run-8. Stirling-PDF timed out in run-11. Their selected
comparison barriers are complete. All three captures preserve the complete
reference rule/location identities and sink fingerprints. See the comparison
receipts for [OWASP](data/redundant-demand-20261110/receipts/OWASP-v1-findings.json),
[Conductor](data/redundant-demand-20261110/receipts/conductor-v2-findings.json)
and [Stirling-PDF](data/redundant-demand-20261110/receipts/Stirling-PDF-v2-findings.json).

The earlier run is evidence only. Every classification concerns removal after
the later run completes and its NORMAL records are persisted. Keep the
earlier execution unchanged.

## 2. Complete outgoing target set

The comparison includes methods and generated inner blocks, with full method
contexts, decomposition paths and physical ports. Scalar membership preserves
complete ND premises and separate plain/protected flags. An inner-block edge
is a target even when it has no method-level result.

| Project | Repeated edges | Units with repetition | Owning methods | AP edges | Targets |
| --- | ---: | ---: | ---: | ---: | ---: |
| OWASP | 1,824 | 534 | 463 | 121 | 1,703 |
| Conductor | 25,786 | 281 | 166 | 22,027 | 3,759 |
| Stirling-PDF | 1,021 | 131 | 59 | 848 | 173 |
| Total | 28,631 | 946 | 688 | 22,996 | 5,635 |

OWASP has 66 FLOW and 55 protected concrete AP edges, plus 971 method Targets
and 732 inner-block Targets. Conductor has 21,485 inner-block edges and
4,301 method edges; its AP set has 14,648 plain and 7,379 protected memberships.
Stirling-PDF has 555 inner-block and 466 method edges. Its selected set includes
four NORMAL ND edges; do not relabel them as DEMAND or discard them.

The complete repeated sets, earlier-only sets, later-only sets, snapshots and
projection links are saved under [the corpus root](data/redundant-demand-20261110/).
The [corpus index](data/redundant-demand-20261110/corpus-index.json) identifies
the directory for each project. In particular, OWASP uses `v1-preflight`.
Each pair comes from one execution. Every completed projection check passes;
observer errors are zero. Outgoing scalar memberships and projected next-run
rows are different domains. The reconciliation files check both explicitly.

The old preliminary OWASP capture had 1,044 repeated raw-ID edges. It is
historical preparation evidence only. Its intermediate sets are not combined
with the frozen 1,824-edge OWASP set used by this campaign.

## 3. Method and block definitions

The original OWASP observer recorded some provider scopes before it recorded
their hierarchy. A separate completed capture supplies immutable definitions
and compiled source forms only. It supplies no replacement outgoing edge,
NORMAL provider, target membership or activity observation.

The [accepted provider overlay](data/redundant-demand-20261110/metadata-supplement/acceptance.json)
resolves 10,294 original provider unit addresses across 707 owners. The
[definition extension](data/redundant-demand-20261110/metadata-supplement/definitions-v2/acceptance.json)
covers all 9,278 original method keys that lacked a definition. All 2,804
overlapping original topologies match. The extension checks exact contexts,
bytecode/model inputs and generator layouts. The two nonlinear Stream model
bodies use bytecode and feature-input congruence, not a linear-body assumption.

See the [source argument](data/redundant-demand-20261110/tools/metadata-definition-source-v2.md)
and [independent checker](data/redundant-demand-20261110/tools/review-definition-extension-v2.py).
The original OWASP catalogs, target IDs and accepted certificates are unchanged.
An original entry observation does not prove that every exit was reached.
Keep block definitions, materialized summary interfaces and entered scopes
as separate inventory domains.

The [full inventory](data/redundant-demand-20261110/inventory/README.md)
contains 36,803 original full method keys, 46,055 block definitions and
79,079 materialized summary interfaces. The block definitions include 3,084
loop nodes and nodes without a materialized interface. Original pair activity
has 2,869 entry observations. It is separate from immutable definitions;
no fresh capture activity is imported. Every repeated target is referenced,
and no method definition or provider identity remains unresolved.

## 4. Accepted NORMAL replay coverage

**Historical, withdrawn under the current edge-only contract:** the 66 P
verdicts below require project-specific source/CFG information and are OPEN.

[Predicate P](../../spec/normal-backed-flow-demand-retirement.md) keeps its
original scope: method-level finite acyclic pure FLOW copies. A similar NORMAL
output is not enough. Every complete paired source origin needs an applicable,
independently retained NORMAL replay witness at the later barrier.

The first [six accepted certificates](data/redundant-demand-20261110/p-known-helper-v1/acceptance.json)
cover `BenchmarkTest01000$Test.doSomething`. They check all 24 clipped origins:
22 direct replay witnesses and two opposite-direction witnesses. The exact
source scope has 12 complete copy relations. Full accessor identities, native
read roles, observations and provider availability are checked.

The [eleven-helper package](data/redundant-demand-20261110/p-all-helpers-v2/acceptance.json)
adds 60 accepted certificates and rechecks the first six. Thus P covers all
66 repeated OWASP FLOW edges. It checks 264 origins against original run-11
providers only: 242 direct and 22 opposite replay witnesses. All 66 constructive
Lean certificates pass. The [independent source review](data/redundant-demand-20261110/p-all-helpers-v2/independent-review.md)
also checks the complete copy graphs, original provider memberships, actual
conditional sink leaves and the restricted FLOW check path. This package
does not extend P to inner blocks or concrete-mark rules. The retained NORMAL
basis covers all 66 removals together. The first six certificates remain
unchanged.

The [remaining P scope audit](data/redundant-demand-20261110/p-pending-cfg-audit-v1/acceptance.json)
checks all 765 other syntactic P candidates in 27 Conductor methods. Six
methods have reachable CFG cycles, so 64 targets fail P's existing finite
acyclic scope guard. The explicit entry paths and closed walks use original
physical ports. These edges stay OPEN for another predicate or a necessity
case. The other 701 candidates have acyclic CFGs. The
[native static-read check](data/redundant-demand-20261110/p-static-native-v1/acceptance.json)
rules out P for 219 of them, in seven methods. Each method has a reachable
compiled LOGGER read with a `StaticOperation.Read`. Full method identities,
topologies and entry paths match the original capture. The unchanged P adapter
rejects this operation. This is a negative scope check, not a classification
as redundant or necessary.

The [remaining native-form check](data/redundant-demand-20261110/p-remaining-native-v1/acceptance.json)
covers all 14 other acyclic scopes and 482 candidates. It preserves all full
method contexts, including the three type contexts and the enriched Optional
model. All 28 directional method forms are complete. The unchanged P adapter
rejects six scopes with source rules, seven with non-inlined callees and one
with a static-operation statement. These edges also stay OPEN.

Thus, [P evaluation is complete for the fixed universe](data/redundant-demand-20261110/receipts/p-complete-universe-v1.json):
66 positive certificates, 27,800 syntactic guard failures and 765 checked
native scope failures. There are no unknown P results. The complete
[per-edge P results](data/redundant-demand-20261110/p-results.jsonl.gz) keep
the later removal barrier and all evidence references. A false P result does
not establish necessity; another predicate can still cover the edge.

## 5. Accepted unchanged-projection coverage

[UnchangedProjectionCover](../../spec/unchanged-projection-cover.md) classifies
**115 Conductor edges**: 22 method edges and 93 inner-block edges. Its
[certificate package](data/redundant-demand-20261110/q-unchanged-projection-cover-v1/README.md)
contains every witness and the global filter result. There are no matches in
OWASP or Stirling-PDF.

For every normalized handoff row contributed by a removed edge X, an actual
outgoing anchor Y contributes the identical row. Y is outside the entire fixed
target set. Thus, no campaign removal can remove the anchor. The proof holds
for all accepted removals together and has no circular support.

The first case is `ParametersUtils.replace`:

```text
T = java/security/path-traversal.yaml:path-traversal#spring-path-source;1;$UNTRUSTED;2

Repeated X:   arg(0).MapKey.*/T -> ret.[any]/T,       DEMAND, protected
Unchanged Y:  arg(0).MapKey.*/T -> ret.[any-taint]/T, DEMAND, protected

Both contribute the same next-run row:
    entry = ret.[any]/T; exit = arg(0).MapKey.*/T
```

Y is present at the later barrier but is not a repeated target. Both raw
records remain. Only X's duplicate handoff contribution can be omitted.
Full owner, context, port, exclusion and mark coordinates are compared.

The constructive Lean model and all 115 observed certificates pass. Five
native component tests cover handoff normalization, ports, protection, ND,
controls and actual C2/C5 queries. The complete projected frontier is equal
before and after these removals. **This removes zero next-run permissions.**
The demand builder already deduplicates these rows. Do not claim reduced
analysis workload or a speedup from this result.

The [joint handoff check](data/redundant-demand-20261110/receipts/P66-and-projection-cover-joint-v1.json)
applies all 181 accepted removals offline to the original projection links:

| Project | Original projected rows | After P | After P and unchanged-projection coverage |
| --- | ---: | ---: | ---: |
| OWASP | 1,153 | 1,087 | 1,087 |
| Conductor | 88,792 | 88,792 | 88,792 |
| Stirling-PDF | 986 | 986 | 986 |

This is a handoff-set calculation. It is not a new engine run or a termination
result. NORMAL replay supplies the required transfers behind the retired P
guidance. The projection predicate supplies identical guidance from retained
anchors. Their joint proof keeps both mechanisms separate.

## 6. Accepted equivalent output selectors

[EquivalentDemandOutputSelectors](../../spec/equivalent-demand-output-selectors.md)
classifies [153 Conductor targets](data/redundant-demand-20261110/q-empty-exclusion-exit-equivalence-proof-v1/acceptance.json).
The complete C2 entry and owner/ports are equal. Only the output selector
differs: MAY versus STAR, both with empty field exclusion. Native paired C5
and its field budget return equal results for every current summary. This
does not replace an initial or a fact's MAY tail by STAR.

Every projected row has an actual later outgoing anchor outside the entire
fixed target universe. Thus all 153 removals are safe together and do not
depend on another campaign removal. The classified set has 77 FLOW and 76
concrete-mark edges, across 98 method and 55 inner-block memberships. Raw
protection and all current summaries stay unchanged. There are 116 distinct
retained anchors.

Twenty generic Lean audits and seven observed-package audits pass, with only
`propext` and `Quot.sound`. Six native tests pass, including an independent
fresh execution. They cover method/scoped C2 and C5, prepared programs, full
loop observations, ND originals, protection, exclusions and negative controls.
Independent review re-extracts every native projection and parses the finite
proof dictionaries back to their complete original coordinates. All 269
known emissions are complete. Other emissions stay arbitrary.

The [joint check](data/redundant-demand-20261110/q-empty-exclusion-exit-equivalence-proof-v1/joint-check.json)
starts after the prior 181 accepted removals. Conductor's explicit row count
changes from 88,792 to 88,676. Its 87,406 canonical query keys stay equal, as
do method/scope/port support and all controls. OWASP and Stirling-PDF stay
unchanged. This removes 116 distinct duplicate selector rows. It is not a
new engine run or a measured performance improvement.

The first witness is `ParametersUtils.replaceVariables`: a repeated
MUST/FLOW input relation and a retained STAR/FLOW sibling have the same
next-run entry, but MAY and STAR output selectors. The universal query law
proves their equivalence. The proof does not need an assumption about the
wrapper's callee or a bounded historical input set.

### 6.1 Symmetric output-selector coverage

The [symmetric extension](../../spec/symmetric-equivalent-demand-output-selectors.md)
adds [39 accepted certificates](data/redundant-demand-20261110/q-equivalent-output-selectors-symmetric-v2/acceptance.json):
34 Conductor and five Stirling-PDF. The existing query law is symmetric,
but the first matcher required an actual STAR anchor. These cases remove
a STAR output selector while an actual MAY output selector remains.
Both have empty field exclusion and the same full entry, geometry and ports.
The certificate retains the real MAY anchor; it does not invent a STAR row.

There are 14 FLOW and 25 concrete-mark targets: 20 method and 19 inner-block
edges, with 23 plain and 16 protected memberships. All 39 anchors are outside
the entire repeated universe. The independent review decodes all 78 complete
native emissions from the Lean expressions back to the original full keys.
All 27 constructive audits and six fresh MAY-only native tests pass.

The [joint check](data/redundant-demand-20261110/q-equivalent-output-selectors-symmetric-v2/joint-check.json)
preserves the canonical query set after all 373 accepted removals. Conductor's
explicit rows change from 88,676 after the prior filters to 88,642; Stirling's
change from 986 to 981. OWASP stays at 1,087. Owner/port support and controls
stay equal. This is an offline equality check. No runtime filter or measured
speedup is claimed.

### 6.2 Retained query basis

The [retained-basis extension](../../spec/retained-demand-query-basis.md)
adds [4,419 checked retirements](data/redundant-demand-20261110/q-retained-query-basis-candidate-v1/acceptance.json):
714 OWASP, 3,527 Conductor and 178 Stirling-PDF. It uses the same query law.
Its new feature is joint selection: a witness can be another repeated edge,
provided that it survives the complete cumulative removal set. Witnesses are
selected from the final retained basis, never from an intermediate pair.

The set has 278 FLOW, 2,669 plain concrete, 768 Target and 704 protected
concrete edges. There are 817 method and 3,602 inner-block memberships.
The 714 ND origins retain their complete premises and all projected members;
three are selected NORMAL ND origins. Retiring their guidance does not
remove their raw summaries or NORMAL records.

Every one of the 5,548 projected memberships has an actual retained witness.
There are 2,405 distinct anchors, all OPEN members of the repeated set.
The finite model binds 6,824 complete native emissions to 3,530 full raw
rows and 2,453 canonical query classes. Code representatives name query
classes; they are not retention witnesses. The independent review checks
this distinction, every physical port, full ND/control payload and all-Nat
lookup-tree bindings. All 37 constructive audits and nine fresh native tests
pass. The three closed finite checks have no axioms.

The [joint check](data/redundant-demand-20261110/q-retained-query-basis-candidate-v1/joint-check.json)
includes all 4,792 accepted removals and every previous dependency:

| Project | Rows before this extension | Rows after | Canonical query keys before and after |
| --- | ---: | ---: | ---: |
| OWASP | 1,087 | 1,087 | 1,087 |
| Conductor | 88,642 | 87,634 | 87,406 |
| Stirling-PDF | 981 | 912 | 901 |

Owners, block/port support and controls stay equal. This is an offline query
equivalence result, not a measured CPU or memory reduction. The production
analyzer is unchanged. Original reached/completed/accepted forward runs remain
OWASP run-11/run-11/run-11, Conductor run-8/run-7/run-7 and Stirling-PDF
run-11/run-10/run-9.

Every future removal must preserve or re-establish all accepted dependencies.
At this acceptance, the ledger checked 5,855 witness memberships. A necessary
classification keeps its edge; only redundancy removes guidance. A sole
provider in the selected final basis remains OPEN: deleting only that edge
from the original later barrier can still be harmless because other original
duplicates remain. Necessity requires a separate valid sink-loss test.

### 6.3 Retain one projection at the hard cutoff

**Historical, withdrawn:** the temporary iteration cap cannot justify a
current campaign verdict.

At the configured run-11 hard cutoff, the driver prepares the report and
persists NORMAL summaries before it checks outgoing demand. A nonempty
handoff at this barrier selects `RUN_LIMIT` and preserves the latest
forward provisional findings. One successful original projection is
enough to preserve this decision, the committed report and the saved
records. No analysis run consumes the remaining projections.

The [cutoff predicate](../../spec/retain-demand-at-hard-cutoff.md) adds
1,043 OWASP retirements, including 989 Target edges and 54 protected
concrete edges. It also supplied the proof for 714 earlier
OWASP query-basis retirements whose anchors are now removed. Their
original certificates remain available. With all accepted removals,
one of the 1,153 original projected rows remained. At that acceptance, its
protected concrete method origin was the one OWASP target still OPEN. Deleting that
edge alone from the original run-11 barrier still leaves other
projections, so the joint witness does not establish necessity.

Six Lean audits and 23 native tests pass. Native controls preserve a
confirmed and a provisional finding with one retained row, and lose the
provisional finding when the handoff is empty. The cumulative check at this
acceptance verified 5,849 dependencies and 2,361 distinct anchors in the repeated
set. Conductor's run-7 and Stirling-PDF's run-9 removal barriers precede
the cutoff and receive no verdict from this predicate.
[Cutoff acceptance](data/redundant-demand-20261110/q-retain-demand-at-hard-cutoff-v1/acceptance.json)

### 6.4 Concrete point and typed control output queries

The [new query predicate](../../spec/concrete-point-demand-queries.md)
adds 575 retirements, 574 Conductor and one Stirling-PDF. It has two
exact query laws.

- From run-3 onward in FULL mode, same-path concrete STAR and EXACT
  entries admit the same exact initial and the same stored premise.
  STAR field exclusions do not add another late-run initial. The
  predicate keeps a complete same-scope, same-port paired query witness.
- A typed Target or ZERO entry with a DATA exit can use the existing
  empty-exclusion MAY/STAR output-selector law. The typed entry and its
  complete paired output geometry stay equal.

The accepted set has 541 Target edges and 34 concrete AP edges.
There are 226 method Targets, 315 block Targets and 34 block AP
memberships. Five AP memberships are protected. The rule changes
guidance only and keeps each original protected or plain summary in
its raw store. All previous witnesses and all 575 new witnesses survive
the complete removal set.

Ten generic Lean audits, two closed finite audits and seven native
tests pass. Independent reconstruction binds 1,150 complete native
origins and all 575 source projections to retained witnesses. The
native controls include C2 layers, direct and prepared C5, complete ND
originals, protection, exclusions, named statics, typed control rows,
both directions and physical ports. Early-run and FLOW cases refute
extensions outside the selected point-entry scope.
[Acceptance and complete certificates](data/redundant-demand-20261110/q-query-refinements-joint-v1/acceptance.json)

| Project | Explicit rows before | Explicit rows after |
| --- | ---: | ---: |
| OWASP | 1 | 1 |
| Conductor | 87,634 | 87,060 |
| Stirling-PDF | 912 | 911 |

The complete semantic query classes stay equal. The encoded preparation
also has an auxiliary Conductor count of 87,625 with nine reserved
origins already absent. The table uses the full actual baseline.
Those nine split-witness candidates all belong to the accepted 575,
so they add no separate verdicts. Their broader law remains a checked
candidate. The cumulative audit now checks 6,424 dependencies and
2,903 retained anchors inside the repeated set.
[Independent full-baseline review](data/redundant-demand-20261110/q-concrete-point-demand-v1/review/finite-joint-v1/receipt.json)

### 6.5 Final confirmed report retirement

**Historical, withdrawn:** report state and the temporary cutoff are outside
the current contract. Section 0 gives the restored and reopened counts.

All 1,824 repeated OWASP origins are now classified as redundant.
The [terminal report predicate](../../spec/final-confirmed-report-demand-retirement.md)
adds the last verdict and supplies new proofs for 1,757 earlier Q verdicts.
The 66 P certificates retain their original proof.

The original run-11 report has 2,633 confirmed entries and zero provisional
entries. Under the pinned report builder, every latest forward ID is
therefore already confirmed. Both the nonempty and empty handoff produce
these exact confirmed entries and public status OK at run-11. Neither
outcome starts run-12.

The diagnostic reason can change from `RUN_LIMIT` to `NO_DEMAND_EDGE`.
The earlier retain-one proof had required reason equality, a stronger
condition than this finding-preservation proof. The new predicate keeps
the configured stop policy and preserves report IDs, descriptors, flags,
order, public status, run and direction.
[Accepted proof and declared diagnostic change](data/redundant-demand-20261110/q-final-confirmed-report-demand-v1/acceptance.json)

The constructive model has five new audits. Four native tests check both
real barrier branches, exact Entry objects on one retained Snapshot,
a provisional candidate, an earlier barrier and an incomplete final run.
An independent reconstruction checks all 1,824 native origins and their
1,153 projected rows. Removing all accepted OWASP guidance leaves zero
projected rows.

These 1,758 Q certificates use a retained report-state witness. The current
cumulative auditor validates their exact origin membership and the pinned
snapshot evidence. At that acceptance, it checked 4,667 native-origin dependencies and
2,902 retained origin anchors in the other proofs. Two negative controls
reject a changed snapshot and an origin dependency on a retired OWASP row.
[Snapshot evidence and original report log](data/redundant-demand-20261110/cases/owasp-final-basis-audit-v1/proposal.md)

The current certificates cover these exact summary interfaces and full method
keys. A method can contribute to more than one predicate.

| Predicate | Redundant edges | Interfaces | Owning method keys |
| --- | ---: | ---: | ---: |
| P: NORMAL replay coverage | 66 | 11 | 11 |
| Unchanged projection | 115 | 16 | 8 |
| Equivalent output selector | 153 | 36 | 22 |
| Symmetric output selector | 39 | 10 | 9 |
| Retained query basis | 3,704 | 76 | 44 |
| Concrete point and control output queries | 579 | 51 | 30 |
| Final confirmed report retirement | 1,758 | 523 | 452 |

### 6.6 Reapply the accepted point-query law

A complete recheck of all 22,220 then-OPEN targets adds two Conductor
verdicts under the existing point-query law. Their removal barrier is after
run-7. Conductor reached run-8, completed run-7 and accepted forward run-7.
The two origins were reserved only by an unaccepted candidate. Neither
origin was a dependency of an accepted proof.

Each source query has a concrete STAR entry. Its retained witness has a
same-path concrete EXACT entry. The complete method key, block, ports,
full mark and output selector are equal. Origin protection is not a demand
query coordinate. Raw plain and protected summary memberships stay separate;
this proof does not subsume a protected raw edge with a plain one.

Two native tests check 594 C2 and 896 C5 cells, including direct and prepared
restriction, layers, packet protection and ND premises. Eight finite Lean
audits bind the complete native coordinates to the accepted ten-audit
generic law. The independent decoder reconstructs both source origins and
their retained witnesses. No new semantic law or production change is added.
[Accepted reapplication](data/redundant-demand-20261110/q-concrete-point-query-fixedpoint-v2/acceptance.json)

At that acceptance, the cumulative check passed with 6,413 redundant origins, 4,669
origin dependencies, 2,902 retained anchors inside the repeated set and
1,758 retained report-state memberships. The selected FLOW case stays OPEN.

### 6.7 Replace one proof before removing its retained witness

A second complete check adds one protected Conductor origin under the same
point-query law. It also replaces the proof for one already redundant plain
origin. Both belong to loop block 2, repeat port 40, in the same Map/HashMap
`ParametersUtils.replace` context. Their removal barrier is after run-7.
Conductor reached run-8, completed run-7 and accepted forward run-7.

```text
T = the full Spring path-traversal source mark
P = var(3).Iterator.Element.Map$Entry.Value.*/T
C = var(9).Map$Entry.Value

Old redundant origin: P -> C.$/T, DEMAND, plain
New removed origin:   P -> C.$/T, DEMAND, protected
Retained witness:     P -> C.*/T, DEMAND, plain
```

The old proof depended on the protected origin. Removing that witness alone
fails the cumulative check. The new complete certificate instead uses the
retained STAR-entry query of the third origin, which is outside the repeated
target set. It proves the old EXACT-entry query again before removing the
protected origin. The full prior proof and its evidence references remain
in the immutable package. Every other accepted proof stays unchanged.
This is demand-query equivalence; it does not merge raw protection flags.

One native test checks sixteen ancestor C2 cells and 84 paired C5 cells,
including the nonempty Value path, both later directions, actual port 40,
exclusions, layers, current packet protection and direct/prepared lookup.
The ten generic Lean audits and fourteen new finite audits pass. The finite
codebook binds all complete method, field, mark, origin and port identities.
[Accepted proof replacement and removal](data/redundant-demand-20261110/q-concrete-point-query-rebinding-v3/acceptance.json)

The cumulative check now passes with 6,414 redundant origins, 22,217 OPEN
targets, 4,670 origin dependencies, 2,901 retained anchors inside the repeated
set and all 1,758 report-state memberships. The point law now supplies 579
verdicts: 541 Target, 32 plain concrete and six protected concrete edges.
One old query-basis verdict moved to the point law; it is not a new removal.

An [independent complete recheck](data/redundant-demand-20261110/cases/existing-query-laws-recheck-v1/README.md)
finds no more complete alternatives under the accepted point, output-selector,
symmetric-selector or query-basis laws. Six constructive inclusion laws and
90,931 native DATA/control rows establish that every old-key cover would
also be a point-key cover. All then-OPEN native emission families were
reconstructed. The final retained universe has no such complete cover,
even when unused candidate reservations and old anchor reservations are
ignored. This is a limit of these predicates, not a necessity verdict.

The [root review](data/redundant-demand-20261110/receipts/query-fixedpoint-and-flow-components-root-review-v2.json)
checks the evidence references of all 6,414 redundant origins and the complete
cumulative dependency set. It also reproduces the FLOW source/control receipt,
checks the debt-lineage pins and recompiles its 23 constructive audits.
Runtime parity and repository diff checks pass. The selected FLOW case remains
OPEN.

### 6.8 Source-safe NORMAL replay

**Historical, withdrawn:** project-specific source/CFG guards are not allowed.

The new [source-safe replay predicate](../../spec/source-safe-normal-replay-demand-retirement.md)
adds four Conductor verdicts. Its complete finite source closure includes
ordinary copies, same-mark conditional sources and selected cleaners. All
14 clipped ordinary-copy origins have original NORMAL witnesses. The marked
source and cleaner lane stays separate and retains protection.

All 28,631 original targets and all 22,217 then-OPEN targets were checked.
Four exact Optional origins pass. They share a full C2 entry with retained
origin `21aded9d…`. Seven local projected rows become three, with equal
complete entry support. Every other ledger row is unchanged. No earlier Q
depends on these four removed origins. The new certificates record their
entry-anchor dependencies; a control that removes the anchor is rejected.

There are 44 distinct constructive Lean audits: 26 generic, nine finite and
nine stage-superset laws. All eight native tests pass, including 3,807 aligned
cells. Independent source and full-filter reviews pass. The source correction
is explicit: extra stage passes form a conservative relation, and disabling
them leaves all 14 clipped origins unchanged. The proof uses P's represented
required concrete-path contract, not equal arbitrary MAY packets.

The [acceptance](data/redundant-demand-20261110/q-source-safe-normal-replay-v1/acceptance.json)
checks 4,674 retained-origin dependencies, 2,902 distinct retained anchors
inside U and 1,758 report-backed memberships. Totals are 6,418 redundant and
22,213 OPEN. Conductor has 4,410 redundant and 21,376 OPEN; other project
counts are unchanged. No analyzer retirement is installed.

### 6.9 Closed FLOW frontier and complete NORMAL boundary replay

**Historical, withdrawn:** the seven active source-guarded verdicts are OPEN
under the current edge-only contract.

The [new predicate](../../spec/flow-only-frontier-replay-retirement.md)
adds three Conductor classifications. It also replaces the four proofs from
section 6.8. The original seven Optional rows now have one complete proof.
The four old proof snapshots and all their evidence remain unchanged.

This law allows current FLOW starts and subscriptions to disappear. It does
not require equal C2 entry sets. The complete owner demand stays in a
nonstatic FLOW lane. Both child demand sets are empty. Typed operations,
paired C5 and handoff preserve this condition in later runs. FLOW cannot
satisfy the concrete rule guards in this closed source region. Legal saved
NormalTarget premises cannot match these FLOW starts. This argument does not
assume that old saved Targets are absent.

All selected boundary transfers have retained NORMAL replay in both
directions. Saved replay uses the original caller offer before C2. The
actual backward plans have four selected copy relations. The forward lane
has its own checked bound. All 67 saved directional memberships are checked:
55 FLOW copies, nine static concrete identities and three ZERO identities.
Four retained NORMAL providers cover all eight selected directional origins.
Their full native directions, marks, layers, protection and suffix relations
are bound to the original records. These providers are outside the outgoing
target set. No companion analysis or ZERO seed is added.

There are 65 combined constructive Lean audits and nine passing native tests.
The native tests cover three, two and zero remaining query rows, real C5 and
handoff, 32 backward replay cells and 56 call-policy controls. The first
native run had one invalid partial-plan fixture. Its archived correction
uses a complete forward plan; the combined nine-test run finishes with
exit 0. Analyzer source code is unchanged.

The [accepted package](data/redundant-demand-20261110/q-flow-only-frontier-replay-v1/README.md)
checks all 28,631 original targets and all 22,213 then-OPEN targets. It adds
three classifications and explicitly replaces four earlier proofs. Every
other 28,624 ledger row and every original raw edge stay unchanged. Independent
source, full-filter and acceptance-tool reviews pass. Removing the old anchor
without replacing all four dependent proofs is rejected.

The cumulative check has 4,698 dependencies, 2,901 retained anchors inside U
and 1,758 report-backed memberships. Totals are 6,421 redundant and 22,210
OPEN. Conductor has 4,413 redundant and 21,373 OPEN. OWASP and Stirling-PDF
counts are unchanged. No necessity case or production removal is added.
Latest reached / completed / accepted forward remain OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9.

## 7. Remaining work

The user selected this investigation order. The
[queue policy](data/redundant-demand-20261110/queue-policy.json) and
[complete open queue](data/redundant-demand-20261110/priority-queue.jsonl.gz)
record it:

| Priority | Edge class | Open edges |
| --- | --- | ---: |
| 1 | FLOW demand | 10,151 |
| 2 | Unprotected concrete mark | 2,038 |
| 3 | Target | 3,337 |
| 4 | Protected concrete mark and other edges | 6,684 |

After each new predicate passes its proof gate, the global filter still checks
all priorities. The coordinator selects a new explanation from the highest
nonempty priority only.

A predicate can use the complete summary and input history from run-i through
run-(i+2). It need not use only the selected edge's shape. The original barrier
observer did not record submitted-fact or emitted-C2 payload streams. It did
record complete final summaries, native records and handoff rows. Do not treat
its entry observations as complete input history. A history-dependent proof
must obtain the missing evidence before it can pass.

A necessity case must make the valid sink unreachable when only the selected
edge is removed after the later barrier. Identify the same sink by its location
and rule in both controls. Keep all other outgoing demand, saved NORMAL
providers and confirmed NormalTarget routes. The baseline must reach the sink
after the barrier. A completed deletion control must show that no remaining
route reaches it.

The last completed target is a Conductor FLOW relation in the exact enriched
`Optional.map(Function)` context for the lambda in
`SubWorkflowTaskMapper.getSubWorkflowVersion`. Its target ID is
`33399e0ea4ae5745e66cf5eaf4337a030dc8de48fecdfa07cfaa293f3c64ec72`.
It repeats at run-5/run-7, with removal only after run-7. The paired relation is
`this.* / FLOW -> ret.[any] / FLOW`, DEMAND. Section 6.9 classifies it and the
other two remaining Optional rows. All seven original Optional targets now
have complete redundancy certificates. The current selection is the Conductor
inner-block FLOW edge in section 7.6. Section 7.5 records the source capture used by both proof
packages; its earlier three-row checkpoint is historical.

The Stirling-PDF target `002f5730…` remains OPEN and is deferred within the
same FLOW priority. Its complete successor-query evidence is in section 7.4.
The Conductor URI case below also remains OPEN and deferred. Deferral changes
no verdict or evidence.

### 7.0 Deferred Conductor FLOW investigation

The earlier selected target is a FLOW relation in Conductor's
`ParametersUtils.replaceVariables`, with the complete original type context.
It repeats at run-5/run-7 and is evaluated for removal after run-7. This is a
five-instruction method with six originally repeated FLOW relations. The next
selected edge has a STAR/FLOW premise at `arg(2)` and a MAY conclusion at
`ret.uri`, with fifteen mark exclusions. The retained NORMAL basis has a
more precise `ret.uri.value.*` conclusion. The next check must determine
whether every producer of the MAY result is covered, or whether it also
contains a field-read/MAY route that is not covered. A similar NORMAL row
alone is not a certificate. The latest
original Conductor result remains reached run-8, completed run-7 and accepted
forward run-7.

The exact wrapper's native forms are now captured. It has a real call-and-return
body, not a substituted model body. Its original run-7 basis contains 51 NORMAL
scalar memberships. The accepted query-equivalence predicate resolves the
earlier MUST-to-MAY target. The new STAR-premise target is not covered by it.
Its complete original summary history for runs 3 through 7 and all paired
demand projections are saved in the same case directory. Its complete future
replay/admission proof remains open. The coordinator retains that evidence
while it tests the Stirling-PDF successor-query method.

The [exact barrier trace](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/root-barrier-trace.md)
rules out one simple explanation. The wrapper's incoming run-7 pair permits
two output fields, so its retained `ret.uri.value.*` NORMAL relation is not
cut by that pair. The same MAY relation already appears at the four-argument
callee interface in both run-5 and run-7. The next check covers that callee's
two loops and complete compiled plans. No new classification follows from
this observation. Equal entry admission alone does not prove equal paired
summary publication.

Five [native component tests](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/source-consumer-audit.md)
confirm this distinction. Complete C2 admission stays equal for 96 offers
after removing X alone. Paired C5 changes. The original NORMAL basis replaces
the coarse STAR/MAY effects, but ten precise operator cells need a complete
producer proof. A missing intermediate result is not a valid sink-loss case.

An independent paired-query review checks all 36 original wrapper rows.
The retained same-entry row exits at `arg(0)`. The two retained rows
that exit at `arg(2)` have unrelated content entry paths. They cannot
replace X's C5 permission for a URI original. This gives a local query
countercell and leaves the complete sink-reachability question open.
[Complete paired-query review](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/query-union-review-v2/README.md)

The one-edge source audit also checks the seven original findings.
They were confirmed by the completed run-7 barrier and remain retained.
The two filesystem findings have a source-backed gRPC path through
external payload loading. A simple task-ID-to-File example also keeps
the saved root NORMAL transfer. These examples do not isolate X.
The required necessity test must lose a valid post-barrier sink after
only X is removed.
[One-edge deletion requirements and source trace](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/sole-deletion-case-v1/README.md)

The [alias source review](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/alias-source-review-v1/conclusions.json)
finds all 270 local URI-related micro-edges in ALIASES stages. Their paths
contain one, two or three copies of `(File.uri, URI.value)`. The alias model
provider extracts pass actions without evaluating their conditions. At
`StringBuilder.toString`, the recorded pass catalog includes a URI-value copy
guarded for `java.io.File`, while the executable native pass stage uses root
copies. The alias unions can therefore identify a root with that field word
and generate repeated paths. This explains a concrete source of path growth;
it does not yet prove all contributors to X redundant.

The wrapper has no ALIASES stage, and the existing input-alias-closure contract
covers genuine aliases only. Do not assume that saved replay reconstructs
every may-alias path. The producer proof must include the callee's loops,
recursive and other dynamic calls, cleaners, source guards and restrictions.
Source-only capture supplies immutable plans, not replacement activity or
new providers for the original run pair. The URI case remains OPEN.

The complete source-channel check now covers all 78 concrete source
occurrences and 116 selected cleaners. Thirteen constructive component
audits pass: nonzero FLOW cannot satisfy those guards, and the cleaners
preserve field geometry while adding mark exclusions. Source-only preparation
also resolves the seven other direct bodies. In particular, the actual
enriched `ReadContext.read` model returns `this`; it is not an unknown empty
body. These results narrow the missing ordinary transfer/alias invariant.
They do not establish a new retirement predicate or a lost valid sink.

The [local entry audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/c2-entry-retention-v1/receipt.json)
strengthens the 96-offer C2 check. After the accepted filters, the wrapper
has 32 paired rows. Removing X leaves 31. Both have exactly the same 28
entry keys and zero control rows. Native C2 uses the entry index, so it
returns the same admissions for every fixed offer at that wrapper. The
paired C5 difference remains. Both original root NORMAL providers are
[retained](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/root-provider-retention-v1/receipt.json).
No previous certificate uses X as a witness.

The [closed field-word check](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/balanced-native-binding-v2/receipt.json)
passes 50 observed, 20 generic finite and 15 internal Lean audits. Its
1,084-node graph has 134,799 balanced pairs and 1,011 empty-level states.
The proof has no path-depth bound. It proves that every genuine public
URI-starting result in the conditional copy graph preserves its input word.
It does not prove that the graph includes all required native transfers.
The prospective exclusion of false alias writers must still be justified.

The [future bridge review](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/future-bridge-review-v1/README.md)
checks four complete forward source packages. None has a primitive URI
read. Two actual saved forward URI relations can read URI in reverse, so
the primitive result cannot be applied to saved records without proof.
The [restricted FLOW audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/restricted-flow-channel-review-v1.md)
also checks that actor creation does not seed ZERO. A FLOW fact cannot
directly supply a concrete rule witness. A published FLOW summary can
still transfer a separate concrete input, and that route must be covered.

One more gap concerns different demand rows. A backward MAY result can
admit a forward FLOW companion which a different C5 row uses. The future
proof must cover all needed outputs from that companion, including non-URI
ones. Proving that the selected URI output is spurious would not suffice.
The unrestricted alias graph can generate three `CharSequence.content`
fields, while the historical retained URI-free return prefixes stop at two.
The candidate guard that rules out new writes to the original String removes
this growth path. Its remaining `arg(2) -> arg(1)` candidate is a separate
false alias to check.

The [native AA capture](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/aa-provenance-v1/README.md)
records 79,207 rows, including all 1,032 external assignments and the actual
nested graph frames. All 18 literal URI equations come from two `toString`
call sites whose File guards are false. Alias analysis merges those equations
without testing the guards. All 135 original URI alias edges match native
before/after witnesses. The [root-join trace](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/aa-root-join-v1/README.md)
shows that the arg(1) candidate comes from merging distinct Replacement
objects at a shared abstract list element. It is not a bytecode write to
the DocumentContext. No analyzer iteration ran in this capture.

The [builder content audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/uri-input-validity-v1/content-flow-mask-review.md)
traces the genuine FLOW writers of `CharSequence.content` to the mandatory
selected-cleaner stage. The fifteen full mark keys match the retained
`ret.content.*` NORMAL provider. Concrete descendant marks can survive an
exact-root clean and have their own protection.

The [native caller capture](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/direct-wrapper-callers-source-v1/README.md)
resolves three observed callers to the selected wrapper key. These are two
map contexts and one list context. The public `replace(String)` call and the
empty list context resolve to a different wrapper key. In each exact caller,
the backward result binds to `taskId` and reaches the predecessor and repeat
ports of the owning loop. The backward suffix preserves the mark, layer and
exclusions. The capture ran before the analysis driver.

The [original paired-demand audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/parent-handoff-audit-v1/receipt.json)
decodes 237,431 rows for the four original caller contexts and their blocks
from run-5 through run-7. Among 75,312 retained run-7 rows at the six first
backward output ports, fourteen select the `taskId` result. They all select
root STAR/FLOW and pair it with an entry at the repeat port. The native C5
test checks those fourteen rows using hypothetical offers. The root MAY result
survives as DEMAND. A one-field exact URI result keeps its URI prefix and
NORMAL layer. A two-field result is cut after URI and becomes DEMAND.
Prepared and direct C5 agree on all tested cells.
[Native C5 receipt](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/parent-first-port-native-v1/receipt.json)

The next backward destinations have no `taskId` entry row. The nine saved
opposite-direction NORMAL records transport the result through the repeat
and preceding blocks to method C5. A second audit finds 58 saved block
records across all fourteen selectors and 21 saved method records across
four method selectors. They reproduce the same root MAY result when the
offered path is a strict ancestor, permits the next field, and its mark
exclusions are within the saved mask.
[Backward replay audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/parent-backward-replay-source-v1/README.md)

All fourteen prospective forward block queries match original run-6 rows.
Saved NORMAL summaries cover the direct `taskId` container writes and can
also reproduce the coarse result at the enclosing method boundary under
the historical selectors. Four native tests check the reversed block
handoff, direct saved replay, recursive C5 cuts, and saved continuation
to method C5. An actual run-9 handoff would depend on the results of run-8.
[Forward handoff audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/parent-forward-handoff-v1/README.md)

The backward source and saved-record audit checks 19 exact method contexts.
No captured micro-edge or saved record writes a literal `File.uri` access
path in the backward direction.
The three exact caller methods have URI-free FLOW entry selectors. Their
15 URI-bearing block entry selectors all end in URI. The four-argument
helper has deeper entries. Its caller wrapper has six root FLOW exit
selectors with a one-field restriction budget. Eight Lean audits and five
native tests check C2, C5 and summary application. The fourteen caller
loop pairs reject a concrete or ZERO original. The remaining differences
at these boundaries are on FLOW paths. A source-only capture subsequently
bound both remaining call sites to the same enriched `HashMap` constructor.
Its backward transfers add no literal field. Its original run-7 records
have no URI path, and its handoff has no demand for current analysis.
Computed-summary replay and the later handoff still need proof. The edge
remains OPEN. The original latest reached, completed and accepted forward
runs are run-8, run-7 and run-7.
[Literal URI trace](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/backward-uri-coordinate-review.md)
[Constructor source and replay audit](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/hashmap-source-v1/README.md)

A supplemental Conductor scan with the pinned runtime and configuration
reached run-8, completed run-7 and accepted forward run-7. The selected
edge occurs once in each final wrapper store at run-5 and run-7. At both
barriers, the raw C5 input already has the MAY conclusion and all fifteen
mark exclusions. Normalization and restriction keep that result.
[Journal receipt](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/journal-capture-v1/receipt.json)

In the complete run-6 window, 38,444 FLOW facts and 3,417 concrete facts
were submitted to the exact wrapper. No FLOW submission contained a
literal `File.uri` field. Twelve root MAY submissions emitted an initial
with that field, four from FLOW and eight from concrete inputs. Run-8
timed out before any method C2 query reached this wrapper. The observed
run-6 offers can match the retained URI descendant replay, and the
later offer set and handoff still need proof. The original comparison
and target remain unchanged.
[Admission windows and fact traces](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/journal-windows-v1/README.md)

A separate source-permission check retains four actual gRPC NORMAL
producers. Their backward replay returns the exact class marker. Forward
saved replay needs that marker but does not need a new getter permission.
Ten constructive Lean audits and three native tests pass. The native
checks cover 42 original marker identities, 168 applications in both
directions and layers, and 18 paired marker exits in the three direct
callers. The actual route to the enclosing entry-source action remains
unproved; its test uses a labeled canonical entry fixture. Thus, a missing
getter permission alone is not a sink-loss proof. The selected edge stays
OPEN. Conductor's latest reached, completed and accepted forward runs
remain run-8, run-7 and run-7.
[Marker replay scope and evidence](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/genuine-flow-completion-v1/README.md)

The later source-only binding checks all 7,210 configured roots. Forty-eight
have an actual gRPC marker entry source; nine have native routes to the
three direct callers. The complete relevant cone has 104 original method
keys and matching block/port layouts. Its original store has 558 exact
marker identities. Six of 27 shortest source routes have method-level
identities in both directions at every nonproducer node. That count does
not prove delivery at every internal boundary. The metadata capture
entered no analysis iteration. Earlier incomplete attempts remain separate.
[Actual entry sources and native routes](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/genuine-flow-completion-v1/entry-route-source-v3/README.md)

The [alias feedback binding](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/alias-feedback-source-guard-v1/README.md)
accounts for all 187 rows excluded by the conditional genuine-copy graph:
135 URI writers and 121 input feedback rows, with 69 rows in both sets.
The other 52 feedback rows copy a root word. The readonly-input source
argument checks 21 ordinary producers and keeps all 531 ordinary FLOW
transports. Six constructive Lean audits pass. These are guards on genuine
positive transfers, not a claim that the native approximate alias rows
do not execute.

The [full conditional output basis](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/normal-basis-coverage-v1/README.md)
also checks the non-URI outputs enabled by later FLOW admission. Three
original NORMAL records cover argument identity, root return and the
masked content return under that contract. Ten constructive Lean audits
and three native tests pass. The tests check 2,736 concrete cells and
360 abstract cells. Their nineteen full marks are eighteen archived keys
and one unexcluded fixture key. Concrete selected-cleaner descendant
survivors are outside the FLOW-mask contract. An
[independent review](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/reviewed-full-basis-v1/README.md)
reconstructs the original providers and reproduces the proof receipt.
Native C2/C5 and future loop-boundary guidance still need a combined proof.

The [backward ingress check](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/backward-seed-companion-v1/README.md)
finds a limit in the no-URI argument. All 216 captured backward sink
pattern occurrences are URI-free root requirements. But an externally
supplied concrete exact URI result can cross original NORMAL block
records, a retained repeat demand and the captured Map.put alias stage.
Wrapper C2 then emits exact URI/FLOW. Two native tests check this local
route and the exact physical ports. The external exact input has no
proved project derivation. The route refutes an unqualified ingress
invariant; it is not a valid sink-loss example.

The [source/control gate](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/genuine-flow-completion-v1/source-control-noninterference-v1/README.md)
closes one separate obligation. All 75,967 original rows at the six first
caller outputs are DATA rows. Exactly fourteen can select the task-ID result.
They require a FLOW original. One native test rejects all 336 non-FLOW
original/output/layer cells and fourteen invalid mixed FLOW/taint ND
constructors. Twelve constructive Lean audits pass. Thus this direct FLOW
difference cannot itself trigger a source or Target. No proof of every
enclosing marker route is needed for this direct gate. A later pure-FLOW
precision difference can still affect another current analysis.

The [debt-lineage component](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/debt-lineage-v1/README.md)
checks that remaining risk with three complete ordinary-code programs.
Both valid sinks remain reachable at runs 5, 7 and 9 for write depths 3, 5
and 7. Twenty-three constructive Lean audits and two native tests pass.
The exact-output C5 cell can produce a STAR/FLOW contribution, but the full
store also has an independent MAY contribution which covers it. Once the
writer fits, retained NORMAL replay supplies the route. These controls do
not contain a final STAR-only demand whose removal loses a sink.

The same component shows why atomic FLOW coverage is insufficient: a
coarse MAY result can satisfy a later STAR demand when a more precise child
does not. A same-prefix MAY query can restore the identical exact FLOW
companion. The unresolved gate is a complete future replay/admission proof
through paired C5 and the loop consumers. Historical equality alone cannot
close it.

None of these FLOW components adds a removal verdict. The selected edge stays
OPEN. The campaign has 6,414 redundant edges and 22,217 OPEN edges.
Conductor's latest reached, completed and accepted forward runs remain
run-8, run-7 and run-7.

### 7.1 Checked limits on the remaining FLOW proof

The [typed ancestry component](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/debt-lineage-v2/README.md)
adds fourteen constructive audits, 24 native typed cells and two complete
driver histories. A nonzero C2 start needs a DATA entry, but that entry need
not descend from a nonzero DATA original. A real Target/DATA row can admit
ZERO in the backward run, publish ZERO-to-DATA, and create the next forward
DATA query. One test first admits its full seven-field exact input at run-9;
it had already started the ordinary FLOW root in run-1.

The second history reaches both sinks by run-11 without ever starting its
full exact conditional input in current C2. Its ordinary NORMAL writer is
available before run-4. A backward NORMAL conditional-source record is
available before run-9 and its opposite replay supplies U. A missing current
initial alone therefore does not show a lost finding. The original Conductor
capture remains reached/completed/accepted forward run-8/run-7/run-7.

The [marked-rule component](data/redundant-demand-20261110/marked-rule-guidance-v1/README.md)
proves only a local storage property. FLOW replacement cannot remove
cross-mark T-to-U results, protected results, exact leaves, or true ZERO/ND
originals. A unary assignment back to its original mark is protected by the
same-mark or cycle test. Passes keep existing protection and cannot add it.
Twenty-one constructive audits, three native tests and an independent
23-file source review pass. The native tests check 96 storage cells,
64 actual assignment-and-field-cut cells, two pass cells and six C5 cells.
This does not prove that every survivor passes C5 or supplies future guidance.

Two further complete searches do not add removal certificates:

- The [field-exclusion audit](data/redundant-demand-20261110/cases/demand-field-exclusion-query-audit-v1/README.md)
  checks all 90,931 native rows and all 22,217 OPEN targets. Every query
  output exclusion is already empty. The only two nonempty entries are
  within the accepted late concrete Point law and have no retained
  equivalent. Concrete output STAR exclusions can affect C5; they cannot
  be erased as a general rule.
- The [sequential-block audit](data/redundant-demand-20261110/cases/p-sequential-blocks-v1/README.md)
  finds 908 FLOW block targets which fail only P's syntactic method guard.
  Of 191 sequential targets, 186 have flat leaf scopes and thirty have no
  next-backward loop-observer lookup. Those thirty still have an actual
  unsupported callee in the whole-scope copy grammar. The same scope is
  also a forward loop consumer later. Nine constructive frame laws show
  why a one-direction negative lookup is not an all-future certificate.

A [productive-exit check](data/redundant-demand-20261110/cases/p-sequential-same-entry-v1/receipt.json)
narrows the latter source obligation. Removing those thirty rows would leave
the same three literal C2 entry keys, supported by seven retained rows. The
47-node productive slice excludes the unsupported `terminate` branch.
The [completed source capture](data/redundant-demand-20261110/cases/p-sequential-productive-forms-v1/productive-feasibility-v1/README.md)
now supplies all 47 instruction forms in both directions, including all twenty
calls per direction. It ran before the iteration driver and submitted no facts.
It changes no original run or campaign classification.

The capture rejects a proposed copy shortcut. Instruction 150 moves the
backward fact from `var(11)` to `var(31)`. Call 123 then binds `var(31)` to
`ExecutionDAOFacade.updateWorkflow`. Its source calls external payload handling,
which can write `inputPayload` and `outputPayload`. Thus the fact can reach a
relevant write even though the call does not mention its earlier local base.
Stored NORMAL summaries alone do not establish that the callee has no effect.

All forty complete call plans and 26 unexpanded callee memberships remain in
the evidence. A complete callee and rule proof, NORMAL coverage and future
loop-observer equivalence are still required. No new removal predicate or
necessity case follows from this capture. The
[capture root review](data/redundant-demand-20261110/receipts/productive-source-capture-root-review-v4.json)
checks 182 archive pins and twelve productive-audit pins. Counts remain
6,414 redundant and 22,217 OPEN. Original Conductor remains run-8 reached,
run-7 completed and run-7 accepted forward.

### 7.2 Baseline diagnostic: a protected child can still lose guidance

The [complete cleaner control](data/redundant-demand-20261110/cases/parameters-uri-flow-shadow-v1/protected-child-cleaner-control-v1/README.md)
finds a real limit on the proposed marked-route shortcut. Both controls use
the same source, wrapper, sink identity and field-limit schedule. Only the
exact-root selected cleaner is switched on. No summary or demand is injected.

```java
// Source rule assigns T only at source().h.$.
Box source(); // Source API; its rule marks Return.h.$.

Box wrap(Box p) {
    Box r = new Box();
    r.c = p;
    removeTAtExactRoot(r); // Does not remove T at r.c.h.
    return r;
}

void main() {
    Box x = source();
    Box r = wrap(x);
    sinkT(r.c.h);
}
```

| Run | Actual decisive facts and summaries |
| --- | --- |
| run-1, limit 1 | Source stores NORMAL `ZERO -> ret.h.$/T`. Wrapper stores NORMAL `p.*/FLOW -> ret.c.*/FLOW`, with mark exclusion `{T}`. Its concrete child survivor is `p.*/T -> ret.c.*/T`, DEMAND and protected. |
| run-2, limit 1 | The supplied `ret.c.[any]/T` answers the same-path STAR demand with `ret.c.$/T`, DEMAND. Reversing the write gives protected `ret.c.$/T -> p.$/T`, DEMAND. |
| run-3, limit 2 | The saved source still supplies actual `p.h.$/T`, NORMAL, at the wrapper call. The exact-root `p.$/T` demand rejects it. The saved FLOW writer excludes T and cannot replay the marked copy. |

Without the cleaner, saved NORMAL FLOW replay reaches the sink with a NORMAL
witness in run-3. With the cleaner, the analyzer completes run-3 with no finding.
The source NORMAL remains present in both controls. This is a baseline missed
flow; no campaign edge was removed. Three native diagnostic tests and the
eleven-law local model pass. Passing tests here mean that the diagnostic is
reproduced, not that the missed flow is correct behavior.

The source cause has two parts. Nonstatic selected cleaning adds a packet-wide
mark exclusion even for this spatially disjoint child. Concrete protection
keeps that child, but its later exact demand cannot refine the actual deeper
point. The selected partial-root STAR-to-MAY repair does not change this
disjoint child. Thus protected storage survival alone is not a valid future
guidance witness.

This is not a necessity case for the selected URI X: it removes no edge,
has no run-5-or-later deletion barrier, and is not the captured ParametersUtils
configuration. The original wrapper has no protected concrete STAR conclusion
in its captured run-3/run-5/run-7 stores. That historical count does not prove
that no such shape can appear later. The proposed global proof must use actual
replay/admission witnesses instead of assuming that every protected row remains
usable. No production fix or new semantics is installed by this investigation.

The [root review](data/redundant-demand-20261110/receipts/marked-guidance-ancestry-and-cleaner-root-review-v3.json)
checks the new component pins, recompiles the four proof fragments and verifies
the baseline controls and independent review. The authoritative ledger is
byte-identical to the previous 6,414-verdict checkpoint. These checks add
evidence and reject an unsafe proof shortcut; they add no removal verdict.

### 7.3 Deferred protected case

The protected concrete MUST-to-EXACT relation in `Thing2.doSomething` is
deferred by the user priority. Its
[checkpoint](data/redundant-demand-20261110/cases/thing2-protected-replay-v1/deferred-checkpoint.md)
keeps the completed component proofs and exact remaining gates. Deferral is
not a classification; this case remains OPEN.

The [native case preparation](data/redundant-demand-20261110/cases/thing2-protected-replay-v1/README.md)
has six passing component tests and 70 replay lanes. The
[source audit](data/redundant-demand-20261110/cases/thing2-protected-replay-v1/source-observation-audit.md)
explains a real same-T assignment:

```java
String doSomething(String i) {
    if (i == null) return "";
    // Constructor pass copies i.* to the builder and builder.content.*.
    String r = new StringBuilder(i).toString();
    // The toString source checks CM(builder.$, T) OR CM(builder.[any], T).
    // It assigns T at r.$. Same-T assignment makes this result protected.
    return r;
}
// Repeated: i.[any-taint]/T -> ret.$/T, DEMAND, protected.
// Also retained: the same relation on NORMAL, and a DEMAND MUST-to-MUST sibling.
```

The constructor pass does not add protection. The toString source does.
Ordinary returned FLOW passes through eight selected-mark return resets.
The conditional source result enters after those resets. This explains why
the NORMAL FLOW records exclude T while the protected T result survives.

In a native local-transfer test, precise `i.bytes.$/T` can produce a protected
exact result through this source. The raw offer has no return match in the
complete original NORMAL basis. This is a real gap in a proposed
NORMAL-replay-only proof. It is not yet a necessary-edge case: removing only
the selected edge keeps its MUST-to-MUST demand sibling, which may preserve
the same analysis and source permissions. The next check compares both
guidance rows with the sibling alone. No edge is classified from the local
transfer test.

The [third live native comparison](data/redundant-demand-20261110/cases/thing2-protected-replay-v1/live-probe-v3/result.json)
uses separate caches and stores for each side and each offer. It uses the
production native-record lanes and commits their pending demotion at the
local boundary. All six backward source-hit sets match. All 108 forward
action sets and combined current/saved replay comparisons match. Of 108 C5
pairs, 28 have an extra protected root EXACT/DEMAND row on the full side.
Each such difference has an original protected exact-root NORMAL replay
witness. A literal MUST provider alone is not sufficient for this proof.
The earlier comparisons are historical preparation; they are not the final
replay evidence.

The [independent root rerun](data/redundant-demand-20261110/receipts/thing2-root-component-rerun-v1.json)
checks the final 17-theorem producer model and the 38-theorem component model.
Both pass Lean with only `propext` and `Quot.sound`. The
[common-demand matrix](data/redundant-demand-20261110/cases/thing2-protected-replay-v1/common-native-v1/receipt.json)
also checks 2,160 entry offers and 1,476 paired C5 cases. These are component
checks, not a retirement proof. The complete typed plan, packed handoff,
caller context and future source permissions still need a checked model.
The MUST-to-MUST sibling is a live dependency and is itself a campaign target.
No circular removal is permitted.

The component uses run-12/run-13 policies. These are not new completed project
barriers. The latest original OWASP reached, completed and accepted forward
iteration remains run-11. The selected edge remains OPEN.

The campaign must continue until every target has a checked redundancy
certificate or a faithful native necessity case. Such a case must reproduce
repetition from run-i to run-(i+2), with i at least 3, and make a valid sink
unreachable when only the selected edge is deleted after the later run.
No unexplained remainder is a completed result.

### 7.4 Complete successor-query investigation

The [component package](data/redundant-demand-20261110/cases/successor-query-trace-v1/README.md)
has thirteen constructive Lean laws, five passing native protocol tests and
a passing observer test that completes eleven native runs. The proof checks
every ordered demand answer in one complete successor run. It includes C2,
C5, prepared plans, prepared C5 and empty-base decisions. Equal C2 alone is
not enough. The source and observer reviews pass within this component scope.
The proof still needs the full native state and scheduling correspondence.

The fresh Stirling-PDF capture reached run-11, completed run-10 and accepted
forward run-9. Run-11 reached the configured timeout. The scan has the same
32 finding fingerprints and location counts as the original scan. Its
run-10 query stream is complete: 761,028 occurrences and 246,479 distinct
ordered queries, zero observer errors and a successful run-10 commit.
The portable export keeps every query, packet DAG, initial ID and dictionary.
The root check validates all exported occurrences and receipt hashes.
The native baseline replayer then reproduced all **246,479 distinct ordered
answers**, with zero errors, zero mismatches and no new packet DAG nodes.
Four replay smoke tests also pass. The passing native code and all baseline
answers are archived separately from subsequent tests.

The fresh state is not a replacement for the original state. All 7,190 input
models and the rule/configuration hashes match, but five extra NORMAL summary
memberships already appear at run-3. Outgoing demand first differs at run-5.
At run-9, 25 original memberships are absent and 14 fresh memberships are
added. The [full comparison](data/redundant-demand-20261110/cases/successor-query-trace-v1/capture-compatibility-v1/comparison.json)
keeps these differences explicit. Equal findings do not prove equal handoff
state. The full run-9 saved NORMAL basis also differs: 254,667 original and
254,662 fresh scalar memberships, with 14 original-only and nine fresh-only.
Seed contents were not exported. The first logged frontier-count difference
is at run-2. These facts prevent a direct historical-state substitution.

The [controlled query test](data/redundant-demand-20261110/cases/successor-query-trace-v1/native-replay-v1/query-deletion-receipt-v1.json)
removes exactly one projected row from the fresh immutable query snapshot.
All other 955 rows and their order remain unchanged. Both original and fresh
projection maps show that this row has only the selected outgoing origin.
This is a native query test; it does not run the analyzer with a deletion.

All 246,479 queries execute without error. Removing the row changes 826
prepared-C5 answers at the selected method. C2, ordinary C5, plan availability
and empty-base answers remain equal. Of the changes, 784 are packet-order
permutations. The other 42 remove one MAY packet covered by a retained MAY
ancestor with the same full header: base, layer, mark exclusions, field
exclusions and protection. These 826 distinct queries represent 55,777 actual
occurrences; the 42 content changes represent 1,624 occurrences.

One principal cell is query 4180. All marks below are FLOW with the same
seventeen concrete mark exclusions on the candidate and results.

```text
Complete original: ret.CharSequence.content.* / FLOW
Raw candidate:     arg(0).[any] / FLOW, DEMAND

Before removing X: arg(0).String.bytes.[any] / FLOW, DEMAND
                   arg(0).[any] / FLOW, DEMAND
After removing X:  arg(0).[any] / FLOW, DEMAND
```

The [native consumer controls](data/redundant-demand-20261110/cases/successor-query-trace-v1/c5-delta-consumer-review-v1/)
all pass. Final ordinary summary and publication membership sets agree for
all 826 isolated C5-answer differences. Ordered publication-delta lists still
differ in 32 cells. When each answer is tested alone, the exact loop observer
keeps the covered child: its component signature differs in all 42 content
cells. An actual observation also unions other saved-record contributions;
these controls do not prove that its full aggregate changes. A valid future
C2 query can also distinguish each raw packet pair, without proving that the
pair reaches that query in the project. Prepared method-root C5 is used by
both real root-summary publication and the enclosing loop observer. The
query address alone does not identify which consumer produced an occurrence.

Thus equal final summary sets do not establish equal loop handling. The
next consumer proof must include complete observation aggregates and their
actual call provenance, or establish a sound relation that covers them. The
strict ordered-query retirement check does not pass for this fresh case.
This is not a necessity certificate: no valid sink was made unreachable, and
the frozen original state has not been rebound. The remaining work is a
complete consumer-preservation proof or a faithful completed sink-loss case.
No edge is classified from these tests, and no production filter is installed.

Original latest reached/completed/accepted-forward runs remain OWASP
11/11/11, Conductor 8/7/7 and Stirling-PDF 11/10/9. Counts remain 6,414
redundant and 22,217 OPEN. The complete campaign goal remains active.

### 7.5 A smaller source closure for the next FLOW proof

The source-readiness pass checks all 10,158 OPEN FLOW targets. Of these,
7,884 have a nonempty output mark-exclusion set. Relaxing P's empty-mask guard
alone is insufficient: the captured acyclic candidates also have unresolved
native callees. The smallest useful missing closure belongs to enriched
`Optional.map(Function)` with the exact lambda context from
`SubWorkflowTaskMapper.getSubWorkflowVersion`. Seven repeated FLOW targets
and 35 original NORMAL memberships are saved for this interface. Five target
rows already have independently retained C2 entry selectors.

The narrow source-only capture completed in 65.963 seconds with exit 0. Its
closed stream reports 963 records, zero errors, three resolved method/context
keys, 30 physical instructions, six directional CFGs and twenty directional
call plans. The three bodies are the enriched `Optional.map`, its resolved
five-instruction lambda wrapper and `lambda$getSubWorkflowVersion$1(Object)`.
The observer follows actual native callee keys. It supplies no AP input and
does not enter `IterationDriver` or construct a new-core method actor.
This adds no reached analysis iteration; original Conductor remains 8/7/7.

The finite prefix construction is complete. Its three public row sets have
11, four and four rows. All 14 clipped ordinary-copy origins for the seven
targets have original NORMAL witnesses. The 35 original NORMAL memberships
include 34 distinct edge IDs: one edge occurs in both native directions.
Native witnesses use the direction as part of their key.

The actual source stage goes from BOUND to REWRITTEN. The selected cleaner
stage goes from RETURNED to REWRITTEN. Source outputs bypass that cleaner
branch and survive as protected outputs. The new proof keeps the source and
cleaner lane separate; it does not call these outputs dead.

The source-safe replay component passes 26 generic and nine finite Lean
audits. A versioned stage-pass correction adds nine constructive audits and
checks all 202 ordinary touched-source guards. The sealed adapter adds some
untouched call-stage passes, while native stage transfer does not. These
extra routes are conservative. Disabling the extra passes gives the same
three public row sets and the same 14 clipped origins. The original sealed
adapter and receipts remain unchanged; the correction is explicit.

Eight native bridge tests pass. They include 3,807 aligned replay cells,
54 incoming-mask cells, 30 actual source-branch cells, reverse source rejection,
ordinary-pass protection checks and protected copy/cut/C5/storage checks in
both arrival orders. The tests use fresh typed field IDs and actual native
direct/opposite replay roles. Independent source review finds no blocker
within P's required concrete-path contract. Arbitrary MAY packet equality
and full driver equality are not claimed.

The [new predicate](../../spec/source-safe-normal-replay-demand-retirement.md)
requires complete native NORMAL coverage and a retained equal C2 entry.
The global candidate checks all 28,631 original targets, including all
22,217 OPEN targets at its input checkpoint. It matches four Optional origins.
They share entry `ret.Optional.Element.Optional.Element.[any]/FLOW` with
retained target `21aded9d…`. Seven actual projected rows become three, with
unchanged complete C2 entry support. No earlier accepted Q depends on the
four trial origins. The anchor and the other two Optional rows remain OPEN.

The [accepted package](data/redundant-demand-20261110/q-source-safe-normal-replay-v1/README.md)
has full per-target answers and four certificates. Independent global-filter
review and the final cumulative dependency gate pass. Section 6.8 gives the
accepted totals. The new current row and the retained entry witness remain
OPEN. No production retirement has been installed.

Section 6.9 is the later checkpoint. Its new proof removes the remaining
three rows and replaces the four anchor-dependent proofs. The older package
and its source capture stay unchanged.

### 7.6 Conductor: a composite after-block and its loop consumer

The current target is `0c5f46ce…`, in `DeciderService.decide(WorkflowModel,
List)` with the exact `arg(1) == LinkedList` context. It repeats at run-5 and
run-7. Any removal must occur after run-7. It remains OPEN. Classification
counts stay at 6,421 redundant and 22,210 OPEN.

The [complete original-state export](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/original-state-v1/README.md)
keeps every owner interface, projection and NORMAL membership for runs 3–7.
The selected region is block 3, the outer loop's after-block. Its own
instruction list is empty because it is a container. Its children have
11, 142 and 109 instructions. Thus, this region has 262 descendant
instructions and contains another loop. An empty container list is not an
identity transfer.

The relevant source has this structure. The omitted statements remain in
the full captured body; this excerpt is not a replacement program.

```java
List<TaskModel> pendingTasks = new ArrayList<>();
for (TaskModel task : workflow.getTasks()) {       // Outer loop L2.
    if (/* original task filters */) pendingTasks.add(task);
    // Other original statements.
}

// AL3: entry normal363, actual CFG edge 32 -> 70.
Map<String, TaskModel> tasksToBeScheduled = new LinkedHashMap<>();
preScheduledTasks.forEach(/* original scheduling lambda */);
for (TaskModel pendingTask : pendingTasks) {       // Nested loop L5.
    // Original timeout, retry, and next-task handling.
}
List<TaskModel> unScheduledTasks = tasksToBeScheduled.values().stream()
    .filter(/* original reference-name filter */).collect(Collectors.toList());
if (!unScheduledTasks.isEmpty()) outcome.tasksToBeScheduled.addAll(unScheduledTasks);
// Other original completion and error handling.
return outcome;
// AL3 exit: METHOD_EXIT.
```

`var(19)` is `pendingTasks`. The selected forward edge is:

```text
DEMAND:
pendingTasks.Iterable.Element.*/FLOW
    -> ret.tasksToBeScheduled.Iterable.Element.[any]/FLOW

Persisted NORMAL, same interface:
pendingTasks.Iterable.Element.*/FLOW
    -> ret.tasksToBeScheduled.Iterable.Element.*/FLOW
```

Both have empty field and mark exclusions and no protection. The NORMAL
forward record exists from run-3; its backward counterpart exists from
run-4. No shorter root-to-root provider exists at this interface.

The [complete owner capture](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/source-v2/receipt.json)
has 331 physical instructions in each direction, 314 call plans, 2,313
stages and 83 resolved callee keys. The closed stream has 12,731 records
and zero errors. It contains six boundaries, 123 source/static-operation
rows and 24 sink rows. It enters no iteration driver or method actor and
submits no AP facts. The first capture attempt failed an object-key-order
comparison; its error trace is kept. The corrected comparison preserves
every list, instruction, port and scalar value.

The [callee census](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/callee-readiness-v1/receipt.json)
binds 1,479 saved NORMAL memberships. In the run-7 handoff, 77 callee methods
have no demand and six have only Target-entry control demand. Therefore,
nonzero next-run-8 calls have no current callee admission. They still apply
saved NORMAL records first. This is a next-run fact, not a run-9 or future
closure proof. Unexpanded callee bodies remain explicit.

The selected next-backward interface has 27 demand rows: 22 FLOW, one
concrete and four Target controls. All 22 FLOW entries are identical.
Sole removal preserves that entry through 21 other rows. A supporting
constructive Lean model checks 19 laws for entry unions, residual point
coverage and loop-observer decisions. It does not assume that a diagonal
NORMAL relation covers every non-diagonal field transfer.

Four [native diagnostic tests](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-diagnostic-v3/run-receipt.json)
pass. They check 1,922 equal C2 cells, 612 C5 cells, 1,000 prepared-C5 checks
and 32 full loop-observer cells. C5 differs in 252 representative cells;
the full observer differs in 22. The matrices include synthetic controls
and do not establish that every tested pair occurs in the project.

The principal historical FLOW cell is:

```text
Original:
ret.tasksToBeScheduled.Iterable.Element.*/FLOW

Raw C5 conclusion:
pendingTasks.Iterable.Element.[any]/FLOW, DEMAND

With X:       root MAY plus 21 child MAY results.
Without X:    the same 21 child MAY results; root MAY is absent.
STAR control: unchanged.
```

The corresponding observer uses all 22 saved NORMAL memberships of the
backward adjacent block. Its offer is `var(27).Iterator.Element.[any]/FLOW`,
DEMAND. `Iterator.Element` and `Iterable.Element` are distinct accessors.
Adjacent and repeat admission sets are empty in both controls. Enclosing
results change from 22 to 21, but both full observations remain nonempty.
This one-field input has no shorter proper-prefix trial. An unequal
signature alone does not prove a changed loop cut or a lost sink.

The [five-test extension](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-diagnostic-v5/run-receipt.json)
also applies six original growing loop relations and runs the real
restriction operation. All five tests pass. For example, one saved forward
relation and its backward read view are:

```text
Saved FORWARD NORMAL, loop repeat235 -> repeat235:
iterator.Iterator.Element.*/FLOW -> iterator.*/FLOW

BACKWARD read view:
iterator.*/FLOW -> iterator.Iterator.Element.*/FLOW

Offer:    iterator.Iterator.Element.[any]/FLOW, DEMAND
Applied:  iterator.Iterator.Element.Iterator.Element.[any]/FLOW, DEMAND
```

Both gates keep the applied fact. A retained child demand selects
`pendingTasks.Iterable.Element.Iterator.Element.*`. After adjacent replay,
it retains the single two-field result in both controls. The budget-1
trial has 22 old or 21 new enclosing results, while the raw observation
has one result. The trial differs from the raw observation on both sides,
so neither gate makes the cut. Six controls and two repeat steps have
zero gate-output differences; both controls drop the same two unrelated
cases. The suspected drop is refuted for these tested cells. This is not
a proof for every new summary, field word, exclusion set or future run.

The [guarded source kernel](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/next8-flow-source-kernel-v1/README.md)
keeps all 3,729 FLOW micros in the selected subtree, the CallPoint DAGs,
CFG arcs, untouched guards and packed saved records. It adds no implicit
pass to an Edges stage. Fourteen constructive primitive-kind laws pass.
All owner sources and sinks require concrete marks; the six GEN forms
and selected cleaner action chains are empty. The two saved MUST records
remain explicit adapter obligations rather than ordinary STAR copies.

The [cyclic invariant checker](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/cyclic-prefix-invariant-v1/README.md)
has 23 constructive laws. Exact prefix composition and a checked finite
postfixed annotation imply coverage of every finite graph execution,
including loop repetitions. No finite unroll bound is used. The model
also proves that a pure output-prefix-pushing loop cannot have a finite
certificate in this correlated-row language. An actual source-graph
binding and annotation certificate are still absent. The abstract
limitation does not classify the selected project edge.

The [field-exclusion census](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/field-exclusion-census-v1/README.md)
finds five introduced fields: `DeciderOutcome.terminateTask`,
`DeciderOutcome.isComplete`, `TaskModel.executed`,
`TaskModel.reasonForIncompletion` and `TaskModel.status`. The union contains
no `Iterator.Element`, `Optional.Element`, `MapKey` or `MapValue`. Successful
C2 emissions for the selected backward entry have empty field exclusions.
Ten supporting E-table laws pass. This is not yet a global reachable-E
invariant through every block operation.

A source-complete residual transfer bound and a future caller/loop proof
remain required. No operator difference is treated as necessity. No
production change or classification is made here.

Latest reached / completed / accepted forward remain OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9. The source capture and native
fixtures add no reached project iteration.

#### 7.6.1 A changed loop decision, without a necessity verdict

The [six-test extension](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-diagnostic-v6/run-receipt.json)
passes. It adds a field `f` that is absent from the 21 retained child
selectors. It applies the actual growing loop records `5383b2bb…` and
`ed2aa857…`, with two parent originals. The native first-field C2 cell
admits the second parent original. Four conditional component cases give:

```text
Offer at loop repeat:
iterator.f.[any]/FLOW, DEMAND

After the saved growing loop relation:
iterator.Iterator.Element.f.[any]/FLOW, DEMAND

After the adjacent saved relation:
pendingTasks.Iterable.Element.f.[any]/FLOW, DEMAND

With X:     the enclosing demand accepts the result; loop gate KEEP.
Without X:  no consumer accepts the result; loop gate DROP.
```

Four NORMAL STAR controls have equal outputs. The earlier five tests and
their counts stay unchanged. Thus, the six earlier growing controls do not
prove that every loop decision stays equal. The new test disproves that
general claim for the supplied component inputs.

This is not a project source path or a sink-loss case. The field and offer
are fixture inputs, and the boundary adapter assumes that the local is
live. A retained whole-AL NORMAL relation can still carry a correlated
suffix through a separate route. That route must be checked before the
edge can be called necessary or redundant.

The [fresh-field word model](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/fresh-field-provenance-v1/README.md)
adds 21 checked constructive laws. A prefix copy whose two literal prefixes
do not contain `f` preserves the complete suffix after the first `f`.
This holds for every finite execution, including cycles. At fixed public
input and output roots, that word transfer is covered by the diagonal
NORMAL relation. A separate negative control states the limit: a root MAY
fact can represent an `f` point without an explicit `f` in its path. The
word proof alone does not establish that point's source derivation.
Native MUST views, cuts, layers, exclusions, ports and future handoffs
still need their own source binding.

The [all-target child-selector census](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/paired-child-selector-census-v1/README.md)
checks all 28,631 ledger rows. Among the 10,151 OPEN FLOW targets, 206 have
at least two retained child selectors with the same complete entry:
132 in Conductor and 74 in Stirling-PDF. The selected target has 21.
This is a literal shape census, not a redundancy predicate. All 206 remain
OPEN, and all 6,421 accepted classifications stay unchanged.

Latest reached / completed / accepted forward remain OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9. No new project scan, production
change or edge removal is part of this evidence.

#### 7.6.2 Complete literal matrix and the remaining root-parent cases

The [literal field census](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/literal-field-universe-v1/README.md)
adds demand and owner-record literals to the 74-key source-kernel alphabet.
The checked union has 86 full typed keys: 76 FIELD, one ELEMENT and nine
CLASS. Twelve TaskModel fields occur in the demand or owner records but
not in the source-kernel alphabet. A source-only enumeration would miss
these keys. This finite union is not a bound on future submitted suffixes.

The [seven-test native extension](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-diagnostic-v7/run-receipt.json)
tests every one of the 77 nonclass keys as a one-field suffix, with two
original growing loop records and two parent originals. All seven tests
pass. The complete 308-cell result is:

| Component result | Cases |
| --- | ---: |
| Equal before/after loop output | 84 |
| KEEP before, DROP after | 224 |
| Changed first-field-parent cases | 112 |
| Changed root-parent cases | 112 |

Every changed first-field-parent case has two native NORMAL replay
witnesses. The stored backward row uses direct replay. The stored forward
row uses `SAVED_OPPOSITE`. In each supplied context, both return the complete
old enclosing fact packet. The 224 replay witnesses keep the full field
keys, records, physical interfaces, layers, exclusions and original keys.
All 308 gate cells and all replay witnesses are embedded in the data files.
The [independent review](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-v7-independent-review-v1/receipt.json)
rebuilds the typed union and checks the archived native XML and both roles.

Each replay equality applies to the supplied MAY packet. It does not prove
the same dependency for every more precise input represented by that packet.
For example, identity and identity plus an `f.a -> f.b` transfer can have
the same image on a packet that can contain both fields. With T only at
`f.a`, the extra transfer is needed to reach `f.b`. The NORMAL identity alone
does not provide it. Thus, even the 112 matching first-field packets still
need a source-derived relation bound before they support retirement.

The distinction is:

```text
First-field parent:
  submitted: ret.tasksToBeScheduled.Iterable.Element.f.[any]/FLOW, DEMAND
  initial:   ret.tasksToBeScheduled.Iterable.Element.f.*/FLOW, NORMAL
  old enclosing result:
             pendingTasks.Iterable.Element.f.[any]/FLOW, DEMAND
  retained whole-AL NORMAL replay on the supplied fact:
             the same old enclosing fact packet

Root parent:
  initial:   ret.tasksToBeScheduled.Iterable.Element.*/FLOW
  tested loop offer: iterator.f.[any]/FLOW, DEMAND
  source derivation from that root initial: not established
  complete replacement proof: not established
```

These are component inputs, not recorded project offers. The common
adapter assumes that the local is live. The test does not prove that all
root-parent cases occur, nor that any changed case loses a valid sink.
The remaining proof must bind actual source paths and caller contexts for
both parent families. The 112 root-parent cases also lack the conditional
packet replacement established for the first-field inputs.

Two additional checks constrain that proof:

- The [backward FLOW shape component](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/next8-tail-exclusion-confinement-v1/source-bridge.md)
  passes 25 constructive laws. For the stated internal run-8 FLOW jobs,
  tails stay STAR, EXACT or ANY; field exclusions use only the five checked
  labels; ANY has empty exclusions. It includes all 760 owner FLOW records,
  1,124 callee FLOW records and both MUST-origin backward read views. It
  does not turn those MUST read views into correlated copies or prove a
  source-origin bound or run-9 closure.
- The [primitive-mark audit](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/primitive-mark-source-audit-v1/README.md)
  checks all 1,536 frozen declarations, not only the 104 allocated keys.
  The 196 conservatively eligible names are ordinary. This does not make
  primitive descendant fields unreachable: the concrete mark policy checks
  the root and raw array spine, and backward forms omit forward type
  filters. An object fact at `task.workflowPriority` can survive until a
  primitive-value filter actually handles that payload.

The [literal field-birth model](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/literal-field-birth-v1/README.md)
adds ten constructive laws. In a prefix copy, an explicit output field must
come from the input word or the literal output prefix. A checked reachable
node set and the absence of a reachable literal producer prove absence
through every finite cyclic walk. This is an AST-word component. The
actual base/phase graph, saved block routes and C2/C5 literal producers
must still be bound before the law can be used on a native path.

No new retirement predicate is accepted. Counts remain 6,421 redundant and
22,210 OPEN. Latest reached / completed / accepted forward remain OWASP
11/11/11, Conductor 8/7/7 and Stirling-PDF 11/10/9.

#### 7.6.3 Source routes, a corrected method name and an incomplete point search

The [runtime route audit](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/block-runtime-schema-audit-v1/README.md)
binds all 675 owner BLOCK FLOW views and 85 METHOD views. Saved block
summaries run before C2, including when C2 creates no child state. Block
interfaces retain their exact ports; the graph cannot replace them with
one shared instruction output.

The [base-and-phase diagnostic](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/base-phase-reachability-v1/README.md)
has one seed: AL3's normal METHOD_EXIT with base `ret`. It uses 5,848
schemas and reaches 2,155 states. Of these, 1,965 can also reach the selected
exit 363 with base `pendingTasks`. There are 415 literal-birth transitions
on such routes. Fifteen of the 56 fields outside the retained child set
have a literal producer there; 41 have none in this compiled graph.

The loop gate contributes no literal producer. It returns the raw packet,
a prefix cut, or nothing. Its C2/C5 observations do not publish their
results. Actual C2 admission and C5 summary publication remain separate
literal producers in the graph.

The [complete prefix-occurrence check](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/prefix-occurrence-audit-v1/README.md)
also checks input prefixes. Forty of those 41 fields are absent from all
relevant input, output and demand-selector prefixes and the public roots.
The exception is `DeciderOutcome.tasksToBeUpdated`, with six input-prefix
occurrences. Absence from output literals alone does not make a field a
fresh symbol. None of these graph counts proves native field absence or
pointwise NORMAL coverage.

The earlier notes named the `3335db70…` method incorrectly. Its exact
captured key is `WorkflowDef.getTaskByRefName(String)`, entry 12 with
EmptyMethodContext. The [identity erratum](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/must-callee-identity-erratum-v1/README.md)
keeps the old sealed files and records the corrected label. Their full
native method IDs were already correct.

The [two-body metadata capture](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/must-two-callee-source-independent-review-v1/README.md)
completed with zero errors, in 69.525 seconds. It adds no AP fact or
analyzer iteration. Its 40 directional instructions show:

```java
// getTaskByRefName: actual native call sequence, simplified names.
return collectTasks().stream()
    .filter(/* reference-name predicate */).findFirst().orElse(null);

// getStatus: actual local field transfer.
return this.status;
```

The lookup is a collection selection. The source of `collectTasks()` and
other helper bodies remains unexpanded. No complete recursive-flow proof
follows from the ordinary summary's Element coordinate. The native MUST
lookup view at instruction 98 is reachable in the base graph, but its
result cannot reach the selected output. The instruction-134 occurrence
is unreachable there; `getStatus()` calls at 2 and 10 are outside AL3.
These are conditional graph results, not a native closure proof.

The [eighth native test](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-diagnostic-v8/run-summary.md)
passes and confirms the MAY-image proof limit. It uses a clearly fictional
offset row. The diagonal and diagonal-plus-offset have equal canonical
MAY outputs in both arrival orders. On precise `f.a.$/T`, only the offset
also emits `f.b.$/T`. Eleven constructive Lean laws prove the same logical
counterexample. This is not a campaign necessity case or project finding.

The [reversed point-prefix prototype](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/reversed-point-prefix-prototype-v1/README.md)
is explicitly INCOMPLETE. It stops with 1,620 configurations and 1,186
queued configurations after it finds a repeatable six-edge prefix cycle.
The stored backward NORMAL loop row shrinks `MapValue.MapValue.*` to `*`;
its loop growth gate therefore bypasses restriction. Reversing that row
for the proof search pushes two MapValue fields on each cycle.

This is a cycle in a conditional proof graph. It is not evidence of a
nonterminating analyzer run. All 11 reached input prefixes within the
selected public root have retained NORMAL word witnesses, but the queue
is not empty. Neither those partial witnesses nor four checked cycle
repetitions establish coverage of every possible prefix. The native
required-point compiler, current-summary bridge, field/type guards and
future handoff proof remain open.

The [fixed-exit check](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/reverse-fixed-exit-independent-v1/README.md)
adds one identical 20-edge exit from the cycle to the public input. Together
with the checked entry and cycle, it gives this conditional backward word
family:

```text
ret.tasksToBeScheduled.Iterable.Element
    .(MapValue.MapValue)^n.Iterator.Element.f.s
  -> pendingTasks.Iterable.Element.f.s
```

At `n=0`, two retained NORMAL word relations cover the result. For every
`n>=1`, none of the 69 does. Each retained relation can shorten an input
word by at most three fields. This family shortens it by `2+2*n`, at least
four. Twenty constructive Lean laws prove noncoverage for every positive
`n` and every common suffix, with four finite path controls also archived.
Thus, the retained whole-AL NORMAL basis alone cannot close this conditional
point graph. Native typing, source validity and actual summary admission
remain required checks. There is no sole-edge deletion or lost-sink result.

The [native forward-filter probe](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/path-filter-metadata-independent-review-v1/README.md)
checks 385 immutable accessor paths at 11 exact existing filters. It runs
no AP fact or analyzer iteration. There are 135 accepted and 250 rejected
cells. The same classpath's hierarchy checks reject Map compatibility
for both Iterator and TaskModel.

| Supplied explicit path | Iterator filter | TaskModel filter | Outcome filter |
| --- | --- | --- | --- |
| MapValue.MapValue | Reject | Reject | Reject |
| Iterator.Element.MapValue | Accept | Reject | Reject |
| TaskModel.workflowTask.MapValue | Reject | Accept | Reject |
| Outcome.tasksToBeScheduled.Iterable.Element.MapValue | Reject | Reject | Accept |
| No explicit accessor at root | No accessor check | No accessor check | No accessor check |

Accept stops descent after the first valid named field. For example, the
Outcome filter does not inspect the later MapValue field in that row.
These are path-only results; the probe does not apply primitive mark policy.
The source census binds the measured encodings to 113 filter locations:
five Iterator, 99 TaskModel and nine Outcome. It does not assert that a
particular project fact visits all 113 locations.

This evidence does not establish a cut on every route. Backward forms
omit the forward filters, and saved row `6d23d957…` applies no statement
type filter. Saved replay runs before the inline child body. A proof must
therefore check saved routes, wildcard inputs, source origins and exact
block admission as well as the rejecting instruction filters. The demand
remains OPEN.

No edge is newly classified. Latest reached / completed / accepted forward
remain OWASP 11/11/11, Conductor 8/7/7 and Stirling-PDF 11/10/9.

#### 7.6.4 Native owner-job preparation

The next test will use the real method runtime instead of the conditional
point graph. The [live bridge compiled successfully](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-owner-bridge-preparation-v1/README.md).
This checkpoint ran no AP job. The packed loader and callback are still
being prepared. No native route or new redundancy result is claimed.

The test will restore the original owner packets and callee FLOW packets.
It will compute METHOD C2 from a stated conditional incoming fact, then use
the real method graph, block liveness, summary application and C5. It must
replace ordinary root startup: ordinary Start also adds ZERO work. It must
not seed DATA in addition to that startup.

The source audit confirms that backward execution disables previous
rule-contributor caches and forward source permissions. An isolated FLOW
test can therefore examine this route without reconstructing those missing
histories. This does not prove equivalence of independent Source/Target work
or the whole original run-8. Conditional facts are not evidence of facts
submitted in the original project run.

One distinction is now an explicit test target. The point graph can reverse
the saved shrinking MapValue relation. Native matching must first obtain
its complete premise. A same-direction STAR input cannot use the
opposite-direction inside-match policy. The test must show whether real C2,
saved replay and current summaries can supply that premise.

The compiled bridge keeps the IterationDriver guard active and exports the
full typed catalogs after the callback too. A separate observer must
distinguish actual loop deliveries from read-only loop observations. The
existing bounded logger cannot prove absence if it drops records.

Classifications remain 6,421 redundant and 22,210 open. Original latest
reached / completed / accepted forward remain OWASP run-11 / run-11 /
run-11, Conductor run-8 / run-7 / run-7, and Stirling-PDF run-11 / run-10 /
run-9. No production behavior changed.

#### 7.6.5 Completed conditional native controls

Two native backward run-8 jobs now completed. They use the actual JIR method
and liveness, the frozen 581 owner and 1,088 callee FLOW packets, and all
other demand. The second job removes only the selected block query. Both
use the same conditional NORMAL offer:

```text
ret.tasksToBeScheduled.Iterable.Element.*/FLOW
```

This is a stated test input. Its arrival in the original project is not
proved. Each job admits one NORMAL STAR initial through native METHOD C2,
creates one owner actor and reaches quiescence. Neither creates a Target or
sink seed. The exact runtime classpath matches source-v2. The callback source
is pinned at `8307e79d…`; later source-hit assertions were not in this build.

The [complete archived controls](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-owner-star-comparison-v1/)
and [independent full-packet comparison](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-owner-star-packet-review-v1/comparison.json)
show why packet counts alone are insufficient:

| Output | Selected query retained | Selected query removed |
| --- | ---: | ---: |
| Method packets | 2 | 2, unchanged |
| Loop5 packets | 28 | 28, unchanged |
| AL3 packets | 2 | 2, both changed |
| All scalar memberships | 156 | 172 |

The comparison preserves full typed fields, marks, exclusions, layers,
protection, ports and packet grouping. Five scalar memberships disappear;
21 appear. The lost DEMAND membership ends at
`pendingTasks.Iterable.Element.[any]`. Its replacement packet has the 21
retained first-child ANY positions. This is a real interface difference,
not a finding-loss result.

The other four lost memberships are NORMAL STAR relations. Their outputs
are `pendingTasks.Iterable.Element` followed by `HeaderIterator.headers` or
`HeaderElementIterator.headerElements`, with or without an intervening
`Iterator.Element`. These are analyzer accessor paths, not claims that the
Java TaskModel declares those fields. All four have
[exact retained NORMAL witnesses](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-owner-star-normal-coverage-v1/README.md)
at run-7. They have the same complete input prefix and physical interface.
The witnesses are four memberships in one original restored packed record.
This check does not cover the lost root ANY demand.

The observed native loop route also differs from an unbounded explicit-word
interpretation. `var(27)` is the nested loop's iterator temporary. All facts
below have empty E and mx:

```text
Actual loop offer: var(27).*/FLOW, NORMAL

Saved opposite read, from original record 8d8e0bcb…:
    var(27).MapValue.*/FLOW -> var(27).*/FLOW
    STAR-inside matching is allowed for this opposite-direction read.
Result: var(27).[any]/FLOW, DEMAND
Parent completion: fresh = true

Next actual offer: var(27).[any]/FLOW, DEMAND

Saved direct BACKWARD record 6d23d957…:
    var(27).MapValue.MapValue.*/FLOW -> var(27).*/FLOW
    The actual ANY input admits this match.
Result: var(27).[any]/FLOW, DEMAND
Growth gate: not required; the saved relation shrinks.
Parent completion: fresh = false
```

Both controls contain these positive events. This observed application does
not construct an explicit MapValue² input or cause an endless sequence of
fresh facts. It also does not prove that every possible input follows this
route. The separate observer has zero errors and balanced depth counters.
The ordinary logger drops 2,777 and 2,582 records, so it is not a complete
pipeline trace and cannot establish absence of another route.

The [independent native decoder validation](data/redundant-demand-20261110/cases/decider-linkedlist-after-block-v1/native-packed-semantic-validation-v1/README.md)
now passes for all 1,669 frozen packets. It uses the same decoder source as
the two controls and returns before method analysis. This validates the
fixed input representation; it does not exercise absent protection/mx cases
or establish original provider iteration order.

The remaining work is to analyze the changed root ANY coverage for all
required input families and
prove future preservation or construct the required valid sink-loss case.
No new predicate or necessity verdict is accepted. Counts remain 6,421
redundant and 22,210 open. Latest original reached / completed / accepted
forward remain OWASP run-11 / run-11 / run-11, Conductor run-8 / run-7 /
run-7, and Stirling-PDF run-11 / run-10 / run-9.
