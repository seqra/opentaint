# Field-limit schedules: iteration times and demand frontiers

Date: 28 October 2026. Experiment: `3284369b2c55065ec99abb327cd9c557a7cbacbd`.
Saved current runtime: `2273c824510ed9366ccd2aa65935f8d3561c38d1`.

The `1, 2, 3, ...` schedule gives worse resource results on three projects and
no completed-run improvement on thingsboard. Keep `1, 1, 2, 3, ...` as the
default. The alternate schedule remains available as an opt-in experiment.

## 1. Configuration and scope

Compare the saved [current report](bidirectional-demand-storage-predefined-performance-20261028.md)
with one new run of each selected project. Do not rerun the saved current
campaign or the legacy `f945f92` baseline.

| Setting | Saved current | Experiment |
|---|---|---|
| Schedule | `REPEAT_RUN1`: 1, 1, 2, 3, ... | `RUN_INDEX`: 1, 2, 3, 4, ... |
| Run-1 mark mode | FULL | FULL |
| Static propagation / default aliases | Enabled | Enabled |
| OWASP heap / analyzer timeout | 8g / 1,000 s | Same |
| conductor heap / analyzer timeout | 8g / 1,080 s | Same |
| thingsboard heap / analyzer timeout | 12g / 1,080 s | Same |
| Stirling heap / analyzer timeout | 8g / 1,080 s | Same |
| Outer timeout | 1,200 s | Same |
| Execution | Gradle `runProjectAnalyzer`, sequential projects | Same |

Select the new schedule with:

```text
-Dopentaint.bidi.fieldLimitSchedule=RUN_INDEX
```

The measurement helper exposes `--field-limit-schedule RUN_INDEX`. Its default
is `REPEAT_RUN1`. See the [experiment scope](../design/bidirectional-run-index-field-limits-experiment-20261028.md)
for code and input validation details.

The selected semantic change is the field budget. The run-2 static input
validator must accept bounded named-field suffixes at the current limit,
such as `C.f.g/T` at limit 2. Both input and seed admission use this limit.
Broad concrete root/class marks, backward MUST inputs, tail/exclusion rules,
run-1 grammar and AP transfer remain unchanged. Special transitive demand
lookup still belongs to incoming run-2 only. No other next-iteration
optimization is included.

The only equal-direction, equal-budget comparison is run-1. Later equal run
numbers have different budgets. Equal later field limits occur at opposite
directions in the two schedules. These results compare precision schedules,
not two implementations at equal precision. They are single measurements.

Prelaunch and final content audits pass: 25 datasets and four models. All
four actual JVM commands use the pinned commit and expected settings. All
analyzers have exited. No schedule or static-input validation error occurred.

## 2. Completion and accepted field budgets

`Reached / complete` gives the latest started engine and latest completed
engine. `Accepted / L` gives the accepted forward run and its field limit.
All current reports remain resource-limited candidate reports.

| Project | Saved outcome | Saved reached / complete | Saved accepted / L | New outcome | New reached / complete | New accepted / L |
|---|---|---|---|---|---|---|
| OWASP | TIMEOUT | run-12 / run-11 | run-11 / 10 | TIMEOUT | run-10 / run-9 | run-9 / 9 |
| conductor | OOM | run-4 / run-3 | run-3 / 2 | OOM | run-2 / run-1 | run-1 / 1 |
| thingsboard | TIMEOUT | run-2 / run-1 | run-1 / 1 | TIMEOUT | run-2 / run-1 | run-1 / 1 |
| Stirling-PDF | TIMEOUT | run-6 / run-5 | run-5 / 4 | OOM | run-2 / run-1 | run-1 / 1 |

The accepted forward field limits change from **10 / 2 / 1 / 4** to
**9 / 1 / 1 / 1**, in the project order above. This is a lower accepted
budget on OWASP, conductor and Stirling. It does not establish a set-wise
ordering of all intermediate facts or candidate findings.

## 3. Iteration times and demand frontiers

Times are engine seconds. `D` is the outgoing demand membership count at a
completed frontier. It is not a scalar fact, operation or queue count.
`—` means unavailable. An interrupted engine has no completed outgoing
frontier. Its time is the observed time until failure or timeout, not the
time required to complete the work. F means forward; B means backward.

### OWASP

| Run | Saved L | Saved seconds | Saved D | New L | New seconds | New D |
|---|---:|---:|---:|---:|---:|---:|
| run-1 F | 1 | 94.144 | 111,374 | 1 | 94.687 | 111,374 |
| run-2 B | 1 | 36.433 | 112,741 | 2 | 41.247 | 164,763 |
| run-3 F | 2 | 32.298 | 392 | 3 | 32.328 | 364 |
| run-4 B | 3 | 40.904 | 204,035 | 4 | 45.169 | 257,567 |
| run-5 F | 4 | 31.092 | 162 | 5 | 31.532 | 164 |
| run-6 B | 5 | 51.229 | 330,891 | 6 | 63.432 | 478,443 |
| run-7 F | 6 | 31.839 | 162 | 7 | 34.281 | 164 |
| run-8 B | 7 | 90.398 | 772,739 | 8 | 157.660 | 1,363,811 |
| run-9 F | 8 | 35.473 | 162 | 9 | 32.450 | 164 |
| run-10 B | 9 | 316.428 | 2,543,689 | 10 | 422.712 TIMEOUT | — |
| run-11 F | 10 | 35.377 | 162 | — | — | — |
| run-12 B | 11 | 155.504 TIMEOUT | — | — | — | — |

### conductor

| Run | Saved L | Saved seconds | Saved D | New L | New seconds | New D |
|---|---:|---:|---:|---:|---:|---:|
| run-1 F | 1 | 14.387 | 33,089 | 1 | 14.850 | 33,088 |
| run-2 B | 1 | 56.167 | 641,505 | 2 | 150.780 OOM | — |
| run-3 F | 2 | 42.982 | 261,363 | — | — | — |
| run-4 B | 3 | 282.283 OOM | — | — | — | — |

### thingsboard

| Run | Saved L | Saved seconds | Saved D | New L | New seconds | New D |
|---|---:|---:|---:|---:|---:|---:|
| run-1 F | 1 | 354.334 | 1,928,079 | 1 | 356.598 | 1,927,981 |
| run-2 B | 1 | 328.264 TIMEOUT | — | 2 | 328.755 TIMEOUT | — |

### Stirling-PDF

| Run | Saved L | Saved seconds | Saved D | New L | New seconds | New D |
|---|---:|---:|---:|---:|---:|---:|
| run-1 F | 1 | 13.319 | 26,469 | 1 | 13.065 | 26,469 |
| run-2 B | 1 | 28.187 | 492,667 | 2 | 103.118 OOM | — |
| run-3 F | 2 | 6.760 | 72,648 | — | — | — |
| run-4 B | 3 | 18.079 | 224,886 | — | — | — |
| run-5 F | 4 | 796.302 | 197,579 | — | — | — |
| run-6 B | 5 | 198.846 TIMEOUT | — | — | — | — |

Conductor's saved run-4 includes the automatic capture interval of about
15.796 s. Saved Stirling run-5 includes a manual capture of 15.489 s. The new
Conductor and Stirling run-2 times include automatic capture intervals of
16.180 s and 17.698 s. No manual capture is taken in the new campaign. These
are capture wall intervals; do not equate the whole interval with a GC pause.

## 4. Run-1 control and joined work

The next field limit cannot affect run-1 AP processing. Keep its engine and
joined binding costs separate. The small control-count differences below
must not be attributed to the future field budget. Aggregate counts do not
prove equality of every demand row.

| Project | Saved engine, s | New engine, s | Saved joined, s | New joined, s | Saved D | New D |
|---|---:|---:|---:|---:|---:|---:|
| OWASP | 94.144 | 94.687 | 0.091 | 0.099 | 111,374 | 111,374 |
| conductor | 14.387 | 14.850 | 0.363 | 0.389 | 33,089 | 33,088 |
| thingsboard | 354.334 | 356.598 | 239.536 | 243.384 | 1,928,079 | 1,927,981 |
| Stirling-PDF | 13.319 | 13.065 | 0.155 | 0.149 | 26,469 | 26,469 |

| Project | Saved barrier, s | New barrier, s | Saved full run-1 interval, s | New full run-1 interval, s |
|---|---:|---:|---:|---:|
| OWASP | 2.386 | 2.310 | 96.628 | 97.105 |
| conductor | 0.310 | 0.319 | 15.071 | 15.570 |
| thingsboard | 7.330 | 11.624 | 601.308 | 611.631 |
| Stirling-PDF | 0.229 | 0.226 | 13.710 | 13.446 |

Run-1 engine times remain close. Thingsboard's roughly four-minute joined
phase is still present. This schedule change cannot solve the run-1 engine
or joined writer workload.

## 5. Observed change after run-1

OWASP has a completed comparison at run-2: engine time rises by 13.2%, and
outgoing demand rises by 46.1%. At run-8, engine time rises from 90.398 s to
157.660 s, while demand rises from 772,739 to 1,363,811. Its forward frontiers
remain small, but its larger backward runs consume the budget before the
saved accepted field limit is reached.

Conductor and Stirling fail with OOM in the first backward run. Neither has
an outgoing run-2 frontier. This is evidence of an earlier resource failure,
not a measurement of their final demand volume. A smaller total wall time
caused by earlier failure is not an acceleration.

Thingsboard receives nearly equal run-2 time: 328.264 s saved and 328.755 s
new. Both times end at the budget, so they do not measure completion speed.
Both runs remain incomplete. New C2 search states are 2,713,908 versus
1,675,872; new C5 states are 4,924,178 versus 4,603,109. These are work counters,
not retained fact counts or completed demand frontiers.

### Why a larger limit can change both volume and layers

Consider this code:

```java
Object get(P p) { return p.f.g; }
```

A backward returned-mark requirement can produce a field result such as:

```text
unbounded result: p.f.g / EXACT / T, NORMAL
limit 1:         p.f   / ANY   / T, DEMAND
limit 2:         p.f.g / EXACT / T, NORMAL
```

This is an example of the existing cut, not a measured dominant shape.
The larger limit can retain exact results and avoid some cuts. It can also
keep many different second fields that limit 1 merged. Thus outgoing DEMAND
can shrink while exact/native or active state grows. Frontier totals alone
cannot identify the memory owner or prove which effect dominates a project.
No fresh retained-heap census is claimed in this experiment.

## 6. Process memory and captures

RSS includes heap and nonheap process memory. It is not live heap size.

| Project | Saved wall, s | New wall, s | Saved peak RSS, GiB | New peak RSS, GiB |
|---|---:|---:|---:|---:|
| OWASP | 1040.751 | 1042.762 | 9.494 | 9.870 |
| conductor | 466.007 | 237.445 | 9.787 | 9.657 |
| thingsboard | 1171.230 | 1169.165 | 13.893 | 14.094 |
| Stirling-PDF | 1107.876 | 161.403 | 9.550 | 9.423 |

The automatic guard captures are from run-2, with run-1 complete and accepted:

| Project | Capture wall interval, s | Serialized HPROF bytes |
|---|---:|---:|
| conductor | 16.180 | 11,434,138,046 |
| Stirling-PDF | 17.698 | 11,926,826,415 |

Serialized bytes are not reachable heap bytes. Both heaps and all four
continuous JFR recordings are retained and hash-bound. No MAT run, manual
dump or extra analyzer configuration is used for this comparison. Native
windows that miss a short run-1 are marked skipped, not zero CPU. No new
CPU-family or retained-memory conclusion is inferred without that analysis.

## 7. Saved-current finding locations

Both sides below are accepted partial reports. The saved accepted runs are
run-11, run-3, run-1 and run-5; the new accepted runs are run-9, run-1, run-1
and run-1. These are candidate locations, not confirmed path witnesses.

| Project | Saved unique | New unique | Kept | Missing | Added |
|---|---:|---:|---:|---:|---:|
| OWASP | 4,112 | 4,112 | 4,112 | 0 | 0 |
| conductor | 10 | 41 | 10 | 0 | 31 |
| thingsboard | 5,089 | 5,089 | 5,089 | 0 | 0 |
| Stirling-PDF | 31 | 148 | 31 | 0 | 117 |

No saved-current identity is missing. Conductor and Stirling add candidates
while accepting only run-1. Do not classify those additions as proved false
positives or new vulnerabilities. The comparison does not prove complete
analysis equivalence or no false negatives. It also does not replace the
legacy-baseline finding audit in the saved report.

All input-difference lists are empty. The generic comparison tool labels
these results `INCOMPLETE_OR_INVALID_INPUT_COMPARISON` because the analyses
are resource-limited. The label is not evidence of an input mismatch here.

## 8. Validation and reproducibility

Before launch, 2,023 common dataflow tests and 445 JVM dataflow tests pass,
with zero failures, errors or skips. The project classes build succeeds.
All 43 measurement-helper tests pass. The schedule model has 116 owned
declarations with empty axiom sets and eight executable controls. It proves
schedule arithmetic and unchanged direction/mark selection, not AP
equivalence or a performance bound.

The tests include actual depth-2 static inputs and seeds, prior coarse demand
intersection, the unchanged default, captured schedule settings and local-only
incoming demand after run-2. The selected source and helper hashes match the
pinned commit. No future optimization is added during measurement.

[Embedded data](data/bidirectional-run-index-field-limits-performance-20261028.json)
contains both schedules' phase records, exact counters, strict comparison,
input audits, source/command bindings, capture markers and artifact hashes.
Raw captures stay outside Git under:

```text
/drive-testcomp/opentaint-go-rules/run-index-field-limits-20261028
```

Old raw captures were removed before this campaign after hash/handle checks:
41 files, 53,146,632,030 logical bytes. All prior compact analysis, logs,
SARIF, source/tool bindings and committed data remain. The cleanup receipt
supersedes the old report's statement that its raw captures remain available.
No saved-current or legacy-baseline analyzer was rerun.

The completed comparison does not support switching the default. Retain the
new flag for controlled future experiments.
