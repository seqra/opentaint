# Final confirmed report demand retirement

The predicate `FinalConfirmedReportDemandRetirement` applies after a
successfully committed final forward barrier in the pinned FULL analyzer.
Its selected hard limit is run-11.

The operation removes outgoing demand contributions. It retains the exact
completed report state, raw summaries, NORMAL records, source permissions
and rule observations.

## Guard

```python
def can_retire_final_report_demand(barrier, policy, report):
    return (
        barrier.committed_successfully
        and barrier.direction == FORWARD
        and policy.is_configured_production_hard_limit
        and barrier.run == policy.last_forward_run == 11
        and report.latest_reached_ids <= report.confirmed_ids
    )
```

The guard is a query on retained state. It does not require another outgoing
origin. Every removed origin still needs its complete native projection
and a certificate for this exact barrier.

## Selected observations

Before removal, a nonempty handoff stops with `RUN_LIMIT`. After complete
removal, the same policy stops with `NO_DEMAND_EDGE`. Both outcomes have
status COMPLETE at forward run-11 and start no run-12.

The diagnostic reason and demand counters can differ. The exact report
entries, descriptors, confirmation flags, order, public status, final run,
direction and run-1 mark mode are preserved. This extends the earlier
retain-one predicate, which also preserved the diagnostic reason.

## Report proof

`ReportBuilder.build` starts with the confirmed map. Under `RUN_LIMIT`
it adds latest forward candidates by ID with `putIfAbsent`. Every latest
ID in the guard already exists in the confirmed map. Thus the insertion
adds no entry and replaces no descriptor or flag.

Under `NO_DEMAND_EDGE`, the builder returns the same confirmed entries.
The public JVM status conversion reads the COMPLETE status and gives OK
for both outcomes. At this barrier, both policies return End and have no
later consumer of demand, source permissions, aliases or summaries.

The proof applies to every immutable report state satisfying the guard
and every retained subset of outgoing guidance, including the empty set.
It preserves the whole Entry values and supports joint removal.

## Native binding

OWASP reached, completed and accepted forward run-11. The original log
records 2,633 confirmed entries and zero provisional entries. In the pinned
builder, each latest ID absent from the confirmed map creates an entry with
`provisional=true`. Thus the recorded zero count proves the subset guard.

The complete original outgoing set has 1,824 origins and 1,153 projected
rows. Every origin belongs to the repeated run-9/run-11 set. The new proof
replaces 1,757 earlier OWASP Q certificates and covers the final open origin.
The existing 66 P certificates retain their original proof.

A typed `COMMITTED_FINAL_CONFIRMED_REPORT` witness identifies the retained
report state. It pins the original log, original receipts, source, proof,
native tests and eligible origin table. The cumulative auditor checks
each target's membership in that table and all native-origin dependencies
from other predicates.

## Counterexamples

If a latest candidate is absent from the confirmed map, `RUN_LIMIT`
reports it provisionally and `NO_DEMAND_EDGE` omits it. The guard rejects
that snapshot.

At run-9, outgoing demand can start run-10. A final-report guard cannot
justify removing that demand. A failed or incomplete run-11 also lacks the
required committed report state.

`FinalCutoffReportSnapshot.lean` proves the guard and report law
constructively. Four native tests use the actual barrier and report
builder. They include both successful endings on the same snapshot,
an unconfirmed candidate, an earlier barrier and an incomplete final run.

[Complete proof, source binding and native tests](../docs/reports/data/redundant-demand-20261110/cases/owasp-final-basis-audit-v1/proposal.md)
