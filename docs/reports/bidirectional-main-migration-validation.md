# Main migration: implementation and validation

9 November 2026. Status: in progress. This report does not claim that the
acceptance gates pass. Project measurements and the next-iteration proposal
are pending.

Latest reached/completed project iteration: not available yet. The pinned
main baseline has completed OWASP and Conductor. It uses the legacy engine, so a bidirectional
`run-N` label does not apply to that engine.

## Source and scope

The selected pre-migration revision is `13357151d`. The rebase target is
`54ad708fe1c4f551956d3d572866de1534415fa1`. The rebase kept the merge history.
Commit `7288c1bda` removes obsolete side-branch variants which the old merge
replay retained. The common bidirectional production and test trees now
match the selected pre-migration trees exactly.

The adapter implementation is committed as `9b21b3716`. Native development
results below were collected on this migration patch before that commit.
The final two test-observation corrections still need a rerun. Do not treat
these results as the post-commit project or rules campaign.

The adapter implements the
[migration specification](../../spec/main-migration.md) and
[implementation proposal](../design/bidirectional-main-migration-implementation-20261109.md):

- Decode main's `Exact` and `AnyAccessorAfter` action positions.
- Remove implicit array, Spring and String-byte reach. Keep explicit reach.
- Keep source-definition reset scope through the existing cleaner primitive.
- Select default getter rules only when the prepared explicit list is empty.
- Keep branch rule selection, mark ownership, aliases and prescan hooks.
- Ignore the legacy iteration cap in bidirectional mode and log it once.

The four-tail algebra, C2/C5, fields, layers, stores, Targets, loops and
iteration schedule are unchanged. Main's configuration, IR and model trees
are retained. No convergence or field-transfer fix is part of this migration.

The [actual file inventory](data/bidirectional-main-migration-actual-files.csv)
lists the changes against the selected pre-migration revision. It uses only
`works-as-on-main` and `works-as-on-bidir`; shared files have separate rows.
Extra paths outside the planned inventory adapt three prescan test
constructors, remove two deleted Go serialized-condition branches, update
existing report test helpers and add the small native coverage examples.
These edits do not add another analyzer mechanism.

## Native evidence

The [data file](data/bidirectional-main-migration-validation.json) contains
the native failure messages, source pins, settings and cleanup receipt.
Counts below are separate suites, not sums of repeated development runs.

| Gate | Tests | Failure/error | Skipped | Result |
| --- | ---: | ---: | ---: | --- |
| Common dataflow | 2,535 | 0 | 0 | PASS |
| JVM bidirectional adapter | 351 | 0 | 0 | PASS |
| Configuration equality | 5 | 0 | 0 | PASS |
| Go selected view | 10 | 0 | 0 | PASS |
| Root selectors, first attempt | 147 | 16 | 3 | FAIL; triage in progress |
| Root selectors, second attempt | 151 | 13 | 3 | FAIL; includes four small coverage cases |
| Sequence selector, third attempt | 13 | 2 | 0 | FAIL; final observer corrections await rerun |
| Explicit bidirectional cleaner reach | 3 | 0 | 0 | PASS |
| Query/compiler suite | 276 | 0 | 26 | PASS with existing disabled cases |
| Lean component laws | 70 | 0 | — | PASS |

The 70 laws comprise 51 specification laws and 19 implementation-seam laws.
They include 14 named finite examples. They do not prove whole-program
convergence or all native analyzer behavior.

The root selector run passes the six binding controls, cap isolation, both
real engine-selection tests, provider selection, alias closure, killed-static
writer cases and the Spring form tests. It also exposes failures that must
remain visible:

| Cases | Observation | Next check |
| --- | --- | --- |
| Seven sequence cases | Old ZERO, ANY-initial, source reach, companion and raw-summary expectations differ | Trace current normalized relations and replace only stale observation assertions |
| Two local-static cases | The old witness geometry assertion does not match the current observation seam | Trace the static Target and seed identities |
| Two Spring cases | `inside-static` is missing; `direct` and `registry` remain | Trace the write, static read, demand and Target route |
| Five cleaner matrix cases | Deeper field flows are missing within the nine-run policy; shallow and stack cases remain | Trace refinement and source permissions; do not label this a proved permanent false negative yet |

The three root skips are explicitly gated on the bidirectional test
environment. They were then run in that environment and all three passed.
No test was disabled to make the migration pass. Real finding assertions
remain in place. A source review is not a waiver for these failures.

### Small cleaner example

The committed fixture has no loop or static field in these two methods:

```java
// Entry source assigns T at x.$ and x.[any-taint].
// The clean rule removes T exactly at its argument root.
// The sink rule checks T exactly at its argument root.
void shallowAfterRootClean(Node x) {
    clean(x);
    sink(x.next);
}
void deepAfterRootClean(Node x) {
    clean(x);
    sink(x.next.next);
}
```

Both examples miss their required finding within the tested bound. Both
reach and complete **run-9**, then stop by `POLICY`. The static-read control
and its later-clear control both pass.

| Run | Observed route |
| --- | --- |
| run-1 forward | Entry rule produces `ZERO -> x.[any-taint]/T`, NORMAL. Exact cleaning keeps the MUST shape but changes its layer to DEMAND. The read and sink produce DemandTarget. |
| run-2 backward | The shallow case reaches `x.next.$/T`, NORMAL, at the entry source. The source hit retains the original `ZERO -> x.[any-taint]/T` action relation and its original action ID. |
| run-3 forward | Source replay creates the same root MUST. Exact cleaning makes it DEMAND again. |
| run-4 through run-9 | The same source-hit and forward-replay route repeats as the field limit increases. |

The backward source visit and producer permission exist. The replay does not
retain the query's child geometry. This is a measured refinement cycle, not
a proof of permanent non-termination. The common core code is unchanged by
the migration.

Keeping an extra child MUST beside the root MUST is not a complete fix:
canonicalization can remove that child before the cleaner. A later design
must prove that producer projection, canonicalization and selected partial
cleaning work together. This report does not select or implement that change.

## Project and rule campaign

The user authorized a fresh baseline because no result exists for the exact
main pin. The baseline runs from an external, clean, detached source checkout.
All implementation work remains in the primary repository. Both engines use
source Gradle tasks.

| Project | Heap | IFDS budget | Outer budget |
| --- | ---: | ---: | ---: |
| OWASP | 8 GiB | 1,000 s | 1,200 s |
| Conductor | 8 GiB | 1,080 s | 1,200 s |
| Thingsboard | 12 GiB | 1,080 s | 1,200 s |
| Stirling-PDF | 8 GiB | 1,080 s | 1,200 s |

Use FULL marks, the `1,1,2,3,...` schedule, aliases and static propagation for
the new core. Do not reuse the old 16 GiB campaign as a current result.

The first pinned-main result is OWASP: **OK, 2,633 findings**, with
`TraceGenerationStats=2633`, equal to main's workflow threshold. Prescan took
34.021 s, full scan took 75.269 s, and command wall time was 156.357 s.
There was no memory warning or OOM. The normal CPU window crosses from full
scan into trace generation; use phase times when reading it. The bidirectional
result and location comparison are still pending.

Conductor's pinned-main run ended with **MemoryManager OOM**, exit 253, after
187.377 s of command wall time. The partial report contains seven findings;
it does not prove that main found every path. Peak RSS was 10,050,641,920 bytes.
The warning snapshot cost 14.151 s; the snapshot at the guard OOM cost another
14.647 s. Both costs are part of the observed run and must be reported apart
from analyzer work. The exact OOM heap is retained for later analysis.

Before this campaign, 44 old raw profile files were removed: 2,787,014,646
bytes. Logs, SARIF and decoded evidence were kept. The current campaign uses
bounded JFR, CPU windows and OOM snapshots. Main's memory guard has no dump
property, so an external log observer requests a heap dump without changing
the pinned source. Record capture cost with the measurement.

The final report must include exact finding locations against main, reached
and completed iterations, engine/barrier times, timeout/OOM events, hot paths
and retained memory. The actual Java bidirectional rules suite must pass both
analyzer status and result checks. Go stays on its existing engine. The next
proposal will use these measurements and rank work avoidance before storage
or instruction-level tuning.
