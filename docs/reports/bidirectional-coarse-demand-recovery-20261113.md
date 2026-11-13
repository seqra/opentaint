# Coarse demand recovery: native tests and proof limits

13 November 2026. This continues [the demand campaign](bidirectional-demand-row-campaign-20261112.md).
The accepted state remains **4,635 REDUNDANT, zero NECESSARY and 20,754 OPEN**.
The separate checked joint cut has 3,490 rows. No analyzer behavior changed.

| Project | Latest reached | Latest completed | Latest accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

These are the archived project runs. The new tests are native components
and small fixtures, not new project scans. Their runtime source is pinned
at `14d7b63369d94f49d4c551be8405ed7719f267cc`.

## Candidate: equal entry and shorter output

For next-run demand rows `X = (A; B)` and `Z = (A; B0)`, test this candidate:

```text
candidate(X, Z):
    require X != Z
    require identical complete unit and physical ports
    require identical entry A
    require B and B0 have the same base constructor and base
    require both outputs are STAR/FLOW, with empty E and mx
    require B0.path is a strict prefix of B.path
    require FL(B0) < FL(B)           // CLASS accessors count as zero
```

Z preserves the entry service. It can restrict a new NORMAL output more
than X does, due to its smaller relative field budget. A removal theorem
would therefore need eventual refinement, not equal immediate results.
**No such theorem is accepted.**

The complete later-handoff scan gives:

| Project | OPEN FLOW rows | Candidate rows |
| --- | ---: | ---: |
| OWASP | 66 | 0 |
| Conductor | 9,396 | 1,090 |
| Stirling-PDF | 538 | 319 |
| Total | 10,000 | 1,409 |

There are 1,413 sibling memberships. The scan uses all original later rows,
including nonrepeated rows. It reads no next-run result, type property or
CFG eligibility condition. Complete outputs and a recomputation checker are
in `cases/coarse-sibling-cover-inventory-v1/` in the external archive.
All 1,409 candidates have a MAY entry. None of the earlier 31 STAR-entry
probes has this literal equal-entry ancestor sibling. Those probes checked
equal C2 results for their specified exact offer, not equal admission for
all possible offers. Keep the two scopes separate.

**Scope correction:** the selected OWASP row has no ancestor-output sibling:

```text
X: (ret.[any]/FLOW ; arg(1).bytes.*/FLOW)
Z: (ret.[any]/FLOW ; arg(1).<string-bytes>.*/FLOW)
```

Its sibling has the same entry but a different named output field. The
generic ancestor test below cannot classify that row. The complete six-row
original state is retained in the inventory package. Earlier design notes
that described a root sibling are superseded by
`sibling-z-counterpair-preparation-v1/DESIGN-CORRECTION-v2.md`.

## H5 test: current publication was absent, old knowledge was retained

The generic fixture produces both rows through ordinary handoff:

```text
H3 and H5:
    X = (ret.[any]/FLOW ; arg.bytes.*/FLOW)
    Z = (ret.[any]/FLOW ; arg.*/FLOW)
```

It removes only X after H5. Both worlds retain all other demand, saved
NORMAL records, source permissions and NormalTargets. All four uncapped
controls finish naturally at run-13. The delayed finding is retained.

The first interpretation overstated the recovery result. A full record
audit gives this trace:

```text
N = ret.*/FLOW -> arg.bytes.[].*/FLOW, NORMAL

run-4: N publishes and persists in all controls.
H5:    N is retained before the cut.
run-6: keep publishes N again; cut does not publish it in its current store.
        Both still retain the old N record.
run-8: cut publishes N again; no lost persistent knowledge is recovered.
```

All 26 full retained-record comparisons, A/B across runs 1–13, are equal.
The native result is valid, but it does not test recovery without old N.
The sealed original case is `sibling-z-hidden-rename-v2/`; the independent
correction is `sibling-z-persisted-provider-audit-v3/`.

## H9 test: a new backward record is lost, but the finding remains

The next fixture removes X after H9. X and Z repeat at H7/H9. It checks that
the following B-only record is absent before the cut:

```text
M = ret.f.*/FLOW -> arg.bytes.g.*/FLOW, NORMAL
```

The actual native trace is:

```text
run-10 BACKWARD:
    same three submissions and four initial deliveries in keep/cut
    actual: ret.f.$/U, NORMAL
    starts: ret.f.*/FLOW and the exact FLOW companion
    keep publishes and persists M; cut does not

H10, both:
    (arg.bytes.[any]/FLOW ; ret.f.*/FLOW)

run-11 FORWARD:
    actual: arg.bytes.g.$/U, NORMAL
    starts: arg.bytes.g.*/FLOW and arg.bytes.$/FLOW
    both publish/persist arg.bytes.g.*/FLOW -> ret.f.*/FLOW, NORMAL
    both reach the delayed U finding
```

M remains absent from the cut's BACKWARD records through termination. Its
FORWARD inverse is new in both controls at run-11. Thus loss of one NORMAL
record does not by itself prove loss of an eventual finding.

All four controls finish naturally at run-13, without an iteration cap.
Only X is removed, once. This does not test repeated filtering at every
later handoff. Operational event order varies; the complete allowed prefix
event multisets and cut-state coordinates are checked. No unique raw-C5
parent link is inferred from a matching final summary.

The complete logs, all retained records, submitted packets and initial
deliveries are in `cases/sibling-z-late-cut-hidden-rename-v2/`. The source
Gradle/JUnit test and sealed checker pass. This is a generic native PASS
fixture, not a JVM reconstruction or a corpus verdict.

## Mixed starts obstruct a local progress proof

The [mixed-initial component](bidirectional-mixed-initial-demand-cycle-20261113.md)
shows a different result with fixed independent EXACT and STAR offers.
Both starts can normalize to the same summary premise. A reader's root MAY
then covers the child MAY that would have guided deeper refinement.

```text
normalize(p.a.g.$/FLOW) = normalize(p.a.g.*/FLOW) = p.a.g.*/FLOW

Retained local query cycle after the coarse cut:
    A = {(ret.[any]/FLOW ; p.a.g.*/FLOW)}
    B = {(p.a.g.[any]/FLOW ; ret.f.*/FLOW),
         (p.a.g.[any]/FLOW ; ret.*/FLOW)}
    A -> B -> A
```

The native component keeps and replays every inferred NORMAL provider.
The constructive model proves local cycle closure at every later step.
It does not model caller feedback from saved replay; its offers and initial
X/Z rows are assumed. No ordinary repeated handoff history or valid sink
loss is established. Thus it blocks the simple local monotone-progress
argument, but does not classify any candidate row or refute every possible
whole-program replacement proof.

Two ordinary-call baselines now test those assumptions. Both use mutable
parameters P and Q, a direct call, a wrapper call and an eight-field
temporary relay. They inject no demand or initial and remove no row.

```text
Baseline 1:
    direct offer P.a.g.$/T; wrapper offer P.a.g.$/FLOW
    no STAR mixture; natural completion at run-11

Baseline 2, after an extra ordinary wrapper PASS:
    run-4/run-6 direct:  P.a.g.$/T, NORMAL
    run-4/run-6 wrapper: P.a.g.$/FLOW and P.a.g.*/FLOW, NORMAL
    normalized-premise MAY suppression occurs
    X=(P.a.g.[any]/FLOW;Q.f.*/FLOW) repeats at H3/H5
    ancestor Z=(P.a.g.[any]/FLOW;Q.*/FLOW) exists at H3, but is absent at H5
    run-8: the STAR offer disappears
    run-9: S first persists NORMAL
    run-11: both direct and wrapper findings; natural completion
```

Thus ordinary calls can produce the mixed starts, but this construction
does not preserve the local cycle or the required sibling at the cut.
Cutting X at H5 would remove its C2 entry and would test a different claim.
No cut is made. These results are in `mixed-offer-ordinary-history-v1/`
and `mixed-offer-ordinary-history-v2/`, with complete native histories and
checked receipts. The diagnostic wall-time guard does not fire.

## Block routing: a definition witness is a separate obligation

The [earlier alias fixture](bidirectional-dead-local-alias-wakeup-20261112.md)
supplies an old local at a core boundary. It does not prove a genuine JIR
alias state. A new native control adds the ordinary earlier copy `X = Y`.
Backward liveness then keeps both physical routes for X; the source hit
exists before the later FLOW arrival in both variants.

The [definition-witness audit](../../spec/lean/proposals/block-alias-closure-audit-20261112/README.md)
checks assignment, phi, catch, formal and generated-local paths. Eight
axiom-free claims give the finite definition/mention and no-kill liveness
adapters. The full frontend and genuine-alias correspondence remains
outside the checked kernel model. Source-hit and Target state cannot be
treated as diagnostic callback counts.

For the candidate above, identical entry service preserves first-postcut
admissions and their registration effects. Later query evolution still
needs proof. No source or CFG condition is added to candidate eligibility.

## Current disposition

The ancestor-output candidate remains unproved. The selected OWASP row
remains OPEN and outside that candidate. No new predicate or necessity case
is accepted. The pending question about complete instruction AP models
has no answer; the original edge-only proof-input contract remains in force.

All large evidence is under the existing external archive at
`docs/reports/data/redundant-demand-rows-20261112/cases/`.
