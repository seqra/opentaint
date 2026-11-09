# Run-11 cutoff validation

9 November 2026. Implementation ready for committed-runtime validation.
The selected [specification](../../spec/bidirectional-run11-cutoff.md) changes
default execution and reporting. It preserves transfer and demand handling.

Default bidirectional scans stop after complete forward run-11. The existing
field limits stay `1,1,2,3,...,10`. Empty-demand convergence can stop earlier.
At the limit, confirmed findings win over provisional findings for the same
physical sink. Only the latest completed forward run supplies candidates.
Provisional SARIF findings have the tag `opentaint:provisional` and a notice
that later refinement can discard them. Rule IDs and fingerprints stay intact.

## Native checks

| Gate | Tests | Failures | Skips | Result |
| --- | ---: | ---: | ---: | --- |
| Full common dataflow | 2,550 | 0 | 0 | Pass |
| Full JVM dataflow | 467 | 0 | 0 | Pass |
| Focused SARIF and legacy-option check | 4 | 0 | 0 | Pass |
| Broad root suite, bidirectional opt-in | 1,083 | 20 | 11 | Failed; retained |

The native persistent-demand case reaches, completes and commits **run-11**;
it does not construct run-12. Other cases test earlier convergence, failed
final barriers, latest snapshot replacement, ND completion, nested ownership,
anonymous Target deduplication and serialized SARIF confidence. The first
build exposed one missing explicit test import. The corrected build passes
the selected mechanism checks.

All eleven earlier real finding failures remain, with the same expected and
actual finding sets. The broader root command adds five duplicate cleaner
matrix failures and four contract mismatches: three legacy iteration-limit
assertions and one old implicit-position assertion. These extra cases were
not measured in the earlier narrower gate. They are not established new
regressions. No assertion was weakened or excluded. The strict gate is failed.

The constructive proof package has **22 local laws and five executable
examples**. It proves the bounded control decision and finite report/snapshot
selection. It does not prove a concrete path for a provisional finding.

## Fresh campaigns

The old unbounded rule JVM was stopped as superseded. Its prefix has 360
complete Java samples with matching finding counts, one genuine timeout and
one controlled stop. Upload reached **run-1275423**, complete through
**run-1275422**, accepted forward **run-1275421**. File.toString reached
**run-524406**, complete and accepted through **run-524405** when stopped.
That old campaign has no final Java/Go JSON gate and is not a passed suite.

The new full source-only Java/Go rules campaign is pending the runtime commit.
Keep its strict JSON gate, analyzer status, declaration coverage and confirmed/
provisional counts separate. The subsequent four-project measurements use
the configured memory and timeouts. They run serially after the rule campaign.
Reuse the fresh pinned-main baseline. Do not reuse old current-run iteration
counts as measurements of this implementation.

The [data](data/bidirectional-run11-cutoff-validation-20261109.json) contains
the complete native totals, all twenty failed identities and their earlier
comparison, proof receipts and exact prepared campaign commands. Acceptance
is not passed. This report will record reached, completed and accepted-forward
run labels for the new campaigns as they finish.
