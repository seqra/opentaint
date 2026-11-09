# Run-11 limit and provisional findings

9 November 2026. Selected user decisions: use this limit by default for all
bidirectional scans. Use only the latest completed forward run for provisional
findings. This specification supplements the main migration specification.

## Selected semantic changes

| Part | Before | After |
| --- | --- | --- |
| Default iteration policy | Continue while outgoing demand exists and time remains | Stop after the complete forward run-11 barrier, or an earlier existing stop |
| Report at this limit | Return confirmed root NORMAL terminals only | Keep confirmed terminals; add latest-forward reached sink identities as provisional |
| Result state | Policy stop does not identify a hard limit | Use `RUN_LIMIT`; do not describe it as convergence |

Run-11 is forward. The default field limits remain `1,1,2,3,...,10`.
The optional RUN_INDEX schedule remains unchanged. The legacy
`--iteration-limit` option remains ignored with its existing diagnostic in
the bidirectional core. It does not set this limit.

These changes do not alter C2, C5, field transfer, mark handling, layers,
summary application, static handling, loop restriction, or Target propagation.
`DemandTarget` remains anonymous. The new sink observation is report data;
it does not add a transfer edge, initial, seed or request.

## Limit

Apply the limit to the default production iteration policy. Keep explicit
finite policies in native tests available. Do not start run-12 under the
default policy. Run-11 must finish its engine, worker joins and existing
barrier before it can supply results.

Keep earlier empty-demand convergence. A failed engine or barrier keeps its
existing TIMEOUT/OOM/FAILED behavior; it does not become a successful limit
stop. No iteration limit can bound the cost of one engine run.

## Sink identities and report selection

Use the existing physical `SinkKey(method, statement, ruleId)` and
`ReportCatalog`. Record an ID only when the existing forward sink handler
has a valid complete witness and is about to emit its Target arm. This includes
NORMAL witnesses with a conditional premise and DEMAND witnesses. Do not
record an ID when one ND condition is still missing. Do not infer a hit from
prescan, an unexecuted rule, a backward source permission, or a seed alone.

Collect IDs per run owner and include nested block owners. Read this state
only after all owners join. At a successful forward barrier, replace the
latest reached-ID snapshot. Do not union it with earlier candidate snapshots.
Backward barriers keep the latest forward snapshot unchanged. A failure before
the atomic commit keeps the previous snapshot. If existing guard cleanup fails
after commit, keep the committed normal state, as before. An abnormal ending
does not expose provisional entries in either case.

Nested block states share the method owner's current-run reached-ID set. The
joined method snapshot therefore includes them without a new Target delivery
channel. Candidate interning can allocate the physical ReportId first. The
first NORMAL witness must still supply the representative context and bound
rule for that ID; later candidate observations must not replace it. This keeps
the existing confirmed-report metadata policy.

Let C be the existing accumulated confirmed report-ID set. Let L be the
latest completed forward reached-ID set. At `RUN_LIMIT`:

```text
entries = [confirmed(id) for id in C]
entries += [provisional(id) for id in L if id not in C]
```

Use one entry per ID. Confirmation wins regardless of arrival order. A
candidate from an earlier forward run which is absent from L is not reported,
unless it is already confirmed in C. Keep existing confirmed report retention.
At earlier convergence and abnormal stops, keep the existing confirmed-only
report policy. Provisional observations do not enter NORMAL summary storage.

Provisional means: the forward analysis reached this configured sink under
the current abstraction. It does not mean that a concrete source-to-sink path
is proved. Later refinement can discard it. A conditional local NORMAL
witness is not a confirmed entrypoint finding.

## Output

Keep the existing vulnerability rule ID, location and fingerprint. Carry a
default-false provisional flag with the returned vulnerability. Default values
preserve legacy and Go output. For a provisional SARIF result, add the tag
`opentaint:provisional` and a clear message that later refinement can discard
the finding. Do not change severity or mark the finding as a confirmed path.
Preserve other SARIF properties. Confirmed output remains unchanged.

Adding report metadata can change data-class equality. Audit all uses: report
deduplication must use the existing physical ID and confirmation must win.
Do not use the new flag to alter AP equality or summary subsumption.

## Principal cases

1. A confirmed sink at run-1 and an anonymous Target in every later forward
   run: finish at run-11 with one confirmed finding, not two entries.
   `fileToStringUnsafe` is the measured straight-line example.
2. A sink reached only by DEMAND in run-11: return one provisional entry.
   Keep the Target and source guidance unchanged before the limit.
3. A candidate reached in run-3, rejected in run-5, absent in run-11: omit it.
4. An ND sink missing one condition: no witness, no provisional report.
5. A sink inside a nested loop block: include the actual reached identity
   through the ordinary joined owner snapshot; add no special Target routing.
6. No outgoing demand at run-3: stop there with the existing convergence
   reason and confirmed-only findings.
7. OOM during run-11 or its barrier: preserve the last committed confirmed
   report. Do not use a partial run-11 candidate set.

## Proof and validation obligations

The constructive Lean model in
`lean/proposals/run11-cutoff-20261109/Reports.lean` proves confirmed retention,
latest-only provisional membership, confirmed priority, absence of provisional
output before a limit stop, removal of discarded candidates and the empty
candidate case. It uses executable finite lists, with no classical choice.
The cap model must prove forward parity and the bounded next-run decision.
These local proofs do not prove concrete reachability of provisional reports
or equivalence to unlimited refinement. The selected report set is C plus L
from this bounded execution.

Source correspondence must show: capture follows complete witness validation;
joined snapshots cover method and nested block owners; forward replacement is
atomic with existing report commit; backward and failed barriers do not replace
it; only `RUN_LIMIT` exposes provisional entries. Test each principal case.
Audit output equality, metadata defaults and SARIF serialization.

Restart source-only rules validation from the new committed runtime. Preserve
the old campaign as superseded. Keep heap, timeout, aliases, statics, FULL mode
and field schedule unchanged. Report confirmed/provisional findings separately
and retain strict rule gate results. Do not waive a false positive merely
because it is provisional. Always give reached, completed and accepted-forward
run labels; distinguish `RUN_LIMIT` from empty-demand convergence.
