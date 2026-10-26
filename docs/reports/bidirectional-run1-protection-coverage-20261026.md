# Run-1 protection and FLOW coverage — 2026-10-26

Thingsboard retains **2,081,089 concrete raw-summary output memberships after run-1** in the diagnostic run. **943,638** have a non-subsumable annotation. **131,034** memberships pass all other FLOW replacement tests and remain only because protection blocks their removal (6.30% of the retained concrete total).

A missing flag is not sufficient for subsumption. An edge also needs a matching FLOW proof, input shape, output geometry, mark, tail, layer, and summary effect class. The tables below separate flag presence from actual replacement eligibility.

## Current concrete memberships at the run-1 barrier

### Raw summaries

| Project | FLOW annotations | Concrete memberships | With a flag annotation | Without a flag annotation | Flag share of concrete |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 246,922 | 2,081,089 | 943,638 | 1,137,451 | 45.34% |
| Conductor | 36,666 | 20,187 | 20 | 20,167 | 0.10% |
| Stirling-PDF | 4,876 | 24,772 | 2,249 | 22,523 | 9.08% |
| OWASP | 11,235 | 111,133 | 413 | 110,720 | 0.37% |

### Selected publications

| Project | FLOW annotations | Concrete memberships | With a flag annotation | Without a flag annotation | Flag share of concrete |
| --- | --- | --- | --- | --- | --- |
| Thingsboard | 246,922 | 2,081,125 | 943,675 | 1,137,450 | 45.34% |
| Conductor | 36,666 | 20,187 | 20 | 20,167 | 0.10% |
| Stirling-PDF | 4,876 | 24,772 | 2,249 | 22,523 | 9.08% |
| OWASP | 11,235 | 111,133 | 413 | 110,720 | 0.37% |

This census covers raw and selected summary relations at the completed run-1 barrier. Raw summaries supply persistent records; selected summaries supply run-2 demand. Transient method-point rows are released at the handoff and are not included. FLOW annotations are shown separately. The protection classification applies to concrete TAINT memberships; ZERO control entries and implicit defaults are outside this mark census.

A membership is one output path, tail, layer, and concrete mark under its owning method and initial premise. A packed row can hold several memberships. Shared trie branches count at each field path. These are current stored annotations, not counts of globally distinct AP objects or all facts processed during run-1.

Raw summaries and selected publications are separate stores. Their counts must not be added. The non-subsumable flag is output metadata; ordinary fact equality does not include it. The protected count is the stored mask size. A wider ANY membership can also be kept when it contains a protected descendant. The coverage comparison measures that effect directly.

## Actual FLOW replacement eligibility

### Raw summaries

| Project | Removable with flags honored | Blocked only by flag | Not covered for other reasons | Ignoring flags: removable total |
| --- | --- | --- | --- | --- |
| Thingsboard | 0 | 131,034 | 1,950,055 | 131,034 |
| Conductor | 0 | 0 | 20,187 | 0 |
| Stirling-PDF | 0 | 15 | 24,757 | 15 |
| OWASP | 0 | 0 | 111,133 | 0 |

### Selected publications

| Project | Removable with flags honored | Blocked only by flag | Not covered for other reasons | Ignoring flags: removable total |
| --- | --- | --- | --- | --- |
| Thingsboard | 0 | 131,070 | 1,950,055 | 131,070 |
| Conductor | 0 | 0 | 20,187 | 0 |
| Stirling-PDF | 0 | 15 | 24,757 | 15 |
| OWASP | 0 | 0 | 111,133 | 0 |

The first three columns form a disjoint partition of the retained concrete total. The last column is the sum of the first two. All four “Removable with flags honored” counts are zero. The current stores have no remaining concrete membership that another pass of the current normalizer would remove. This does not count the memberships that FLOW already removed during run-1.

“Blocked only by flag” means that the current summary normalizer keeps the membership with its annotation but removes it when the annotation alone is cleared on a temporary copy. All other gates remain active. This is stronger than a field-path-only match. It preserves the existing tail, layer, mark-exclusion, diagonal-mark, input-shape, and same-base identity/effect checks.

A flagged membership can remain for another reason even when its flag is ignored. Such a membership belongs in “Not covered for other reasons.” Its flag is present but does not account for its current retention. Other gates can include a missing FLOW proof, an unsupported initial, a cross-mark result, different tails, a mark exclusion, or the same-base identity/effect distinction. For example, the current replacement cell does not use a FLOW STAR output to remove a TAINT ANY output.

## Static and nonstatic flag-only blocking

| Project | Raw static concrete memberships | Static flag-only blocking | Nonstatic flag-only blocking |
| --- | --- | --- | --- |
| Thingsboard | 902,474 | 97,565 | 33,469 |
| Conductor | 3,502 | 0 | 0 |
| Stirling-PDF | 15,037 | 1 | 14 |
| OWASP | 2,062 | 0 | 0 |

Static/nonstatic classification uses the output base. It does not count distinct static fields. These values describe forward run-1 summaries; they must not be confused with the much larger backward run-2 method-state counts in the [16 GiB investigation](bidirectional-run2-16g-memory-20261026.md).

This census does not count concrete edges that FLOW already removed before the barrier. Those edges are absent from the current stores. Measuring a historical number of unique avoided edges would need a different counter; repeated rejected offers would not give that number.

## Counts from the original timed 16 GiB runs

| Project | Original run-1 raw concrete memberships | Original protected annotations | Diagnostic raw concrete memberships | Diagnostic protected annotations |
| --- | --- | --- | --- | --- |
| Thingsboard | 2,081,317 | 943,493 | 2,081,089 | 943,638 |
| Conductor | 20,181 | 20 | 20,187 | 20 |
| Stirling-PDF | 24,774 | 2,249 | 24,772 | 2,249 |
| OWASP | 111,133 | 413 | 111,133 | 413 |

The original completion logger records total/protected memberships. It does not record flag-only coverage. The extra figures come from a separate diagnostic cohort. Each diagnostic result is reconciled with its own ordinary completion census, including packed mark rows and scalar rows. Counts from separate runs are not subtracted.

Clearing flags on the current summary values would make no additional membership removable on Conductor or OWASP, and only 15 on Stirling-PDF. Thingsboard has 131,034 such raw memberships. This is a boundary measurement, not an ablation of protection throughout execution.

The flag-only total is a measure of retained guidance. It is not a measured memory saving or a predicted run-2 speedup. One summary can be applied in many callers. Removing protection would change demand semantics; this experiment does not remove it from the analysis.

## Method, progress, and checks

The production checkout remains unchanged at revision `30b50b20029394eee9c34acb5afce934b08591b9`. An isolated checkout adds a read-only numeric census at the joined run-1 barrier. The census calls the existing [summary normalizer](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/FlowBackedSummaries.kt) and [FLOW coverage operation](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/FlowBackedCoverage.kt). It clears protection only on temporary copies. It never removes or replaces a stored analyzer edge.

The diagnostic uses FULL marks and `-Xmx16g`, with the same project inputs, statics, aliases, rule selection, and timeouts as the timed campaign. It stops after the ordinary run-1 report and handoff. Its extra census time is excluded from the performance comparison.

| Project | Diagnostic latest reached / completed / accepted forward | Timed campaign latest reached / completed / accepted forward |
| --- | --- | --- |
| Thingsboard | run-1 / run-1 / run-1 | run-2 / run-1 / run-1 |
| Conductor | run-1 / run-1 / run-1 | run-2 / run-1 / run-1 |
| Stirling-PDF | run-1 / run-1 / run-1 | run-2 / run-1 / run-1 |
| OWASP | run-1 / run-1 / run-1 | run-11 / run-11 / run-11 |

Four targeted tests pass: a covered protected result; a flag with no FLOW proof; a same-base identity that must remain; and shared geometry with two field-path memberships. The read-only test checks that the store census is unchanged. Every measured diagnostic total, protected count, and decoded-row count matches the existing completion census. Every eligibility partition reconciles exactly.

The [machine-readable evidence](bidirectional-run1-protection-coverage-20261026.json) contains the source/patch binding, manifests, completion markers, count oracles, test result, and latest iteration records. Raw diagnostic evidence is under `/drive-testcomp/opentaint-go-rules/run2-16g-20261026/run1-coverage`. The patch is diagnostic-only; it is not applied to the working branch. The exact [diagnostic patch](/drive-testcomp/opentaint-go-rules/run2-16g-20261026/run1-coverage/diagnostic.patch) is retained with the evidence.
