# Retain one demand projection at the hard cutoff

This predicate applies at the completed final forward barrier under the
production hard run limit. It retires outgoing guidance contributions in the
campaign. The current production driver, field schedule and report policy
provide the behavior for the proof.

## Rule

Use the exact state of a successfully committed final forward barrier. Keep
its raw summary stores, NORMAL records, source and rule observations, seeds
and report snapshot. The only changed state is the set of outgoing demand
projections. A complete engine result alone can still fail the barrier guard
or be cancelled before the report commits.
Choose one actual projection and one of its actual origins. The origin must
survive all accepted removals at this barrier.

```text
canRetireAtHardCutoff(barrier, outgoing, removals, anchor):
    return barrier.committedSuccessfully
       and barrier.direction == FORWARD
       and barrier.policy is the configured production HardRunLimitPolicy
       and barrier.index == barrier.policy.lastForwardRun
       and outgoing.hasSuccessfulProjectionFrom(anchor)
       and anchor not in removals
```

Check the complete projection of every origin. A projected row remains if
at least one origin remains. Keep every premise member and physical port
in the witness. The predicate can retire a method edge or a block edge,
including a DATA or DemandTarget origin. The row that preserves the cutoff
decision can belong to a different owner.

## Before and after

The complete engine results supply report preparation and NORMAL
persistence. `HandOff.of` projects the selected rows. `IterationDriver`
checks for an empty outgoing demand map before it checks the hard policy.
At the last forward run, a nonempty map gives `RUN_LIMIT`.

The retained origin keeps the map nonempty after removal. The hard policy
again returns `RUN_LIMIT`. Its `continueAfter` test short-circuits before
it reads the delegate. No later analysis run consumes any projected row.
Both executions commit the same already-prepared report snapshot. The
report therefore has the same confirmed findings, latest forward
provisional findings, and final status, run, direction and reason.

```text
Completed run-11. Both projected rows are present.
    A: Zero -> DemandTarget
    B: p.[any-taint]/T -> ret.content.[any]/T, DEMAND, protected
    Reports prepared: confirmed location c, reached location s

Retire A's guidance and keep B's projection.
    Demand remains nonempty.
    Result: RUN_LIMIT. Return c as confirmed and s as provisional.

If both projections are removed, demand is empty.
    Result: NO_DEMAND_EDGE. The provisional finding s is absent.

At run-9 under the same run-11 policy, a nonempty set can guide run-10.
    The cutoff predicate rejects removal at that barrier.
```

An incomplete final run does not have the required committed barrier. The
predicate preserves the stop reason even when the snapshot happens to have
zero provisional findings. Outgoing row and owner counts are diagnostics
for this configured policy.

## Proof and joint witnesses

The retained origin yields an original successful row in both variants.
Thus both maps are nonempty. On the completed final forward run, the native
branch test has the same outcome independently of the other rows. The
original run results and all observations remain available for persistence
and report preparation. With the same terminal reason and report snapshot,
the final reports are equal. No next C2, C5, replay, source, target, alias or
call consumer runs. The proof applies to the complete removal set at once.

`RetainDemandAtHardCutoff.lean` proves the terminal branch and report result
for any unchanged snapshot. `ObservedHardCutoffRetirement.lean` checks the
retained row over the full OWASP projection table. The native tests supply
complete engine snapshots to the real barrier with both rows, either row
alone, an empty handoff, and an earlier barrier. The existing integration
tests cover the complete run-11 cutoff, a timeout, and a failed final barrier.

OWASP's selected pair reached, completed and accepted forward run-11.
It has 1,824 original outgoing origins and 1,153 unique projected rows at
that barrier. Every original origin belongs to the repeated set. The
predicate keeps one protected concrete method origin and its single native
projection. It adds 1,043 retirements and gives 714 earlier query-basis
verdicts a new proof where their old anchors are removed. Their historical
proof packages remain available. The chosen origin stays open as the
cutoff witness. Its role in the joint deletion does not meet the campaign's
one-edge sink-loss test.

Conductor's removal barrier is run-7, and its original reached, completed
and accepted forward runs are 8, 7 and 7. Stirling-PDF's removal barrier is
run-9, and its original values are 11, 10 and 9. These barriers precede the
hard limit. The predicate gives no verdict for them. This proof does not
estimate savings in analysis iterations before the cutoff.

[Acceptance and native proof](../docs/reports/data/redundant-demand-20261110/q-retain-demand-at-hard-cutoff-v1/acceptance.json)
