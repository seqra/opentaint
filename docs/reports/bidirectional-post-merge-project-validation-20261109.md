# Post-merge project validation

9 November 2026. State: **EXACT ACCEPTED FINDING AND LOCATION PARITY**.

All three project scans have the same accepted finding identities and locations as the
[performance report](bidirectional-subsumption-initial-demand-performance-20261108.md).
No finding was added or lost after the merge. All three commands still time out.
This result compares accepted snapshots. It does not establish convergence or repair
the previously documented coverage gaps.

## Runtime and fixed controls

The primary checkout ran commit `1c5659be0e73856df12d995783d56676f598763a` on `saloed/bidirectional`.
The reference ran `334234c24e9008f4a2614b8213b8b2e73b6ba9e1`. Both use core tree
`8b38a03586138acbbf5aaadd94b5fb301d6c9cad`. No analyzer code changed for this validation.

The actual runtime classpath has 92 entries. The comparison found 65 exact
artifact byte matches, 25 JARs with identical entry names, contents and order,
and two absent NO-SOURCE outputs. The 25 JAR containers differ only in container
metadata. Their reference artifact hashes remain intact. All logical runtime
artifacts match. The coordinator verified the source revision and frozen
runtime artifacts before and after each project.

Each scan used Gradle `runProjectAnalyzer`, FULL marks, 16 GiB, aliases and
statics enabled, and field limits `1,1,2,3,...`. Each IFDS budget was 1,080
seconds; each outer timeout was 1,200 seconds. Java, models, serialized rules,
test revision, profiling settings, runner arguments and actual JVM commands
match the reference after checkout/output path normalization. The projects ran
in sequence. Neither the f945 baseline nor OWASP was rerun.

## Accepted finding comparison

The comparison checks `(rule ID, sink fingerprint, complete method signature)`.
It also checks the complete location multiset: source path, region, IR
instruction index and instruction text. Equal counts alone are insufficient.

| Project | Reference findings | Merged findings | Lost / added | Exact locations |
| --- | ---: | ---: | ---: | --- |
| Stirling-PDF | 22 | 22 | 0 / 0 | Equal |
| conductor | 7 | 7 | 0 / 0 | Equal |
| thingsboard | 13 | 13 | 0 / 0 | Equal |

Conductor retains both Graal findings. The known f945 gaps remain unchanged:
Thingsboard lacks one unsafe-reflection identity; Stirling lacks the same
three strict identities and retains the same eight additions. This validation
establishes parity with the performance report, not universal no-FN behavior.

## Iteration endpoints

Each cell gives `reference → merged`. An engine completion is separate from
a committed handoff. The accepted forward run owns the exported report.

| Project | Command | Latest reached | Engine complete | Fully committed | Accepted forward |
| --- | --- | --- | --- | --- | --- |
| Stirling-PDF | TIMEOUT → TIMEOUT | run-52 → run-54 | run-51 → run-53 | run-51 → run-53 | run-51 → run-53 |
| conductor | TIMEOUT → TIMEOUT | run-14 → run-14 | run-13 → run-13 | run-13 → run-13 | run-13 → run-13 |
| thingsboard | TIMEOUT → TIMEOUT | run-2 → run-2 | run-1 → run-1 | run-1 → run-1 | run-1 → run-1 |

Stirling fits two more iterations into the fixed budget. Different timeout
endpoints can result from elapsed-time differences. They do not imply a change
in the accepted findings. None of these scans reaches a fixed point.

## Time and memory

| Project | Command seconds, reference → merged | Peak RSS GiB, reference → merged | Run-1 engine seconds, reference → merged |
| --- | ---: | ---: | ---: |
| Stirling-PDF | 1,118.898 → 1,115.608 | 14.689 → 15.665 | 19.626 → 17.842 |
| conductor | 1,128.404 → 1,130.392 | 18.299 → 18.366 | 15.918 → 16.949 |
| thingsboard | 1,126.542 → 1,127.433 | 18.348 → 18.360 | 521.169 → 509.609 |

RSS includes native memory outside the Java heap. No OOM was reported in these
validation commands. Thingsboard logged three high-memory warnings. These are
separate from an OOM. These are single instrumented scans. Timing differences
do not isolate host effects or establish a causal performance change.

| Selected phase | Reference seconds | Merged seconds |
| --- | ---: | ---: |
| Stirling run-6 engine | 13.921 | 13.068 |
| Stirling run-8 engine | 34.336 | 32.906 |
| Conductor run-10 engine | 340.793 | 343.472 |
| Conductor run-12 engine | 375.681 | 375.278 |
| Thingsboard run-1 static binding | 292.711 | 289.341 |
| Thingsboard run-1 report barrier | 21.545 | 25.134 |

## Internal frontier differences

Execution counters are not identical. The data packet lists every difference
in common committed runs. The first differences are:

| Project / run | Field | Reference | Merged |
| --- | --- | ---: | ---: |
| Stirling-PDF run-2 | handoff_edges | 255,159 | 255,170 |
| Stirling-PDF run-2 | demand_method_keys | 4,199 | 4,201 |
| conductor run-1 | handoff_edges | 114,135 | 114,305 |
| thingsboard run-1 | handoff_edges | 6,249,488 | 6,249,498 |

These counters prevent a claim of identical execution. The source and logical
runtime contents match, and the exact accepted findings and locations match.
This validation does not identify the cause of the small internal count differences.

## Evidence and capture lifecycle

The [portable evidence](data/bidirectional-post-merge-project-validation-20261109.json)
contains both exact finding sets, location multisets, every run time and frontier,
settings checks, source/runtime pins and all terminal statuses. The source output is:

    /drive-testcomp/opentaint-go-rules/post-merge-validation-20261109

Previous owned raw JFR/CPU captures were removed before this campaign:
51 files, 2,795,428,591 logical bytes. Their decoded profile evidence, reports,
SARIF, logs and configurations remain. The cleanup receipt is embedded in the
data packet. New captures are retained in this validation directory. Heavy
profile or heap analysis was not run beside an active measured analyzer.
