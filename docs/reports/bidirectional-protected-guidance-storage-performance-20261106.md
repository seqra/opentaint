# Protected guidance storage: performance and quality, 6 November 2026

The selected storage runtime `7069fe2d73a32443d98163fc67970a3114983712` recovers the two Conductor identities that were absent from the saved 8331 and 4182 reports. Its seven Conductor identities match f945 and 52f. It still times out in backward run 4. OWASP completes with all 4,112 reference identities. Thingsboard has no accepted forward report. Stirling-PDF keeps the same 21 identities as 4182 and times out in forward run 5.

The main measured late-run cost is loop consumer observation. The new protection wrappers have zero sampled ownership in Conductor runs 3 and 4. The measurements do not support an H-wrapper or exclusion-family explanation for that slowdown.

The [portable evidence](data/bidirectional-protected-guidance-storage-performance-20261106.json) embeds all nine final outputs, exact identity sets and changes, all iteration/frontier records, reader sources and controls, corrections, runtime/configuration pins, and the source-only work audit. Each embedded UTF-8 artifact has its byte length and SHA-256. Raw JFR, collapsed stacks, SARIF, and analyzer logs are represented by recorded hashes and derived evidence; these large raw files are not needed to read the reported results.

## Configuration and completion

All four commands use the same saved project models, rules, and budgets as 4182. Analysis uses FULL marks, a 16 GiB Java heap, enabled statics and aliases, and limits `1,1,2,3,4,…` in alternating forward/backward runs. The IFDS budget is 1,000 seconds for OWASP and 1,080 seconds for the other projects; the outer command budget is 1,200 seconds. Gradle uses a separate registry for each project. That registry property belongs to the Gradle client, not the analyzer JVM. No f945, 52f, 8331, or 4182 baseline was rerun.

The native default check passed before the campaign. It has 3,040 available successful results: 2,578 fresh core results and 462 reused successful JVM results. This is separate from end-to-end program recovery.

“Reached” means the run started. “Engine complete” requires its COMPLETE engine record. “Full complete” also requires the frontier/target result and evidence that the driver committed the iteration. “Accepted” is the latest committed forward report. A barrier emitted during cleanup is insufficient. A timeout does not prove convergence.

| Project | Command | Reached / engine complete / full complete / accepted | Findings | Command wall s | Peak RSS GiB |
| --- | --- | --- | --- | ---: | ---: |
| OWASP | OK | 5/5/5/5 | 4112 | 230.29 | 16.59 |
| conductor | TIMEOUT | 4/3/3/3 | 7 | 1131.98 | 18.16 |
| thingsboard | TIMEOUT | 1/none/none/none | no accepted report | 1122.82 | 18.23 |
| Stirling-PDF | TIMEOUT | 5/4/4/3 | 21 | 1116.90 | 13.71 |

The Conductor and Stirling counts are accepted snapshots before the timed-out run. Thingsboard has an empty SARIF snapshot but no accepted forward iteration; it cannot pass a findings-equivalence gate. The legacy f945 runs have no bidirectional run labels.

## All reached iterations and demand frontiers

Engine time and joined static binding are separate logged durations. In Thingsboard run 1 they are 518.580 and 425.523 seconds; their sum is 944.103 seconds. A dash means no completed value was recorded. It does not mean zero. Reports are cumulative; a backward frontier does not create a new accepted forward report.

| Project | Run | Limit | Engine s | Static bind s | Outgoing edges / method keys | Target demand | Reports | Seeds |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| OWASP | 1F | 1 | 91.114 | 0.403 | 188869 / 4446 | 14087 | 3227 | 8066 |
| OWASP | 2B | 1 | 38.626 | — | 29176 / 4354 | 2463 | 3227 | 10758 |
| OWASP | 3F | 2 | 13.143 | — | 178 / 78 | 80 | 4112 | 35 |
| OWASP | 4B | 3 | 0.200 | — | 135 / 44 | 42 | 4112 | 65 |
| OWASP | 5F | 4 | 0.163 | — | 0 / 0 | 0 | 4112 | 0 |
| conductor | 1F | 1 | 16.893 | 1.534 | 122225 / 6763 | 7896 | 2 | 60 |
| conductor | 2B | 1 | 30.642 | — | 280255 / 9366 | 404 | 2 | 1589 |
| conductor | 3F | 2 | 213.835 | — | 257270 / 668 | 11320 | 7 | 9 |
| conductor | 4B | 3 | 787.973 | — | — / — | — | — | — |
| thingsboard | 1F | 1 | 518.580 | 425.523 | — / — | — | — | — |
| Stirling-PDF | 1F | 1 | 19.486 | 0.439 | 80628 / 2023 | 5400 | 7 | 1026 |
| Stirling-PDF | 2B | 1 | 31.411 | — | 299365 / 4204 | 472 | 7 | 1766 |
| Stirling-PDF | 3F | 2 | 6.082 | — | 4689 / 146 | 139 | 21 | 74 |
| Stirling-PDF | 4B | 3 | 390.893 | — | 39545 / 118 | 113 | 21 | 706 |
| Stirling-PDF | 5F | 4 | 614.349 | — | — / — | — | — | — |

The “outgoing demand” label is the native handoff count. It can include eligible NORMAL records as well as DEMAND records; it is not a DEMAND-layer-only census. The JSON retains the printed frontier counts, static statistics, relation censuses, body work, and completion evidence.

## Exact findings versus saved controls

Identity is the rule ID, sink fingerprint, and full sink method signature. Counts alone are insufficient. Minus means a saved identity is missing; plus means an identity is added. Timeout comparisons describe accepted snapshots, so they remain provisional as final-coverage statements.

| Project | versus f945 | versus 52f | versus 8331 | versus 4182 |
| --- | --- | --- | --- | --- |
| OWASP | −0 / +0 | −0 / +0 | −0 / +0 | −0 / +0 |
| conductor | −0 / +0 | −0 / +0 | −0 / +2 | −0 / +2 |
| thingsboard | −14 / +0 | −0 / +0 | −0 / +0 | −0 / +0 |
| Stirling-PDF | −4 / +8 | −1 / +0 | −1 / +0 | −0 / +0 |

Conductor recovers the Graal findings at `PythonEvaluator.evaluate(String,Object)` (`8rLVjoe1V3DqzuJubn3Pc1RsFnegW1yHtQ/fuKX0gXQ=`) and `ScriptEvaluator.getSource(String)` (`EzmrpG1FD3CwGwVTQXyOH0FmoHson/4xsYBeDYPJbF8=`). The other five identities remain present. This establishes current report recovery. It does not identify which storage transition is necessary for each real-project route or isolate the first cause.

Stirling's four f945 gaps are `ProcessExecutor.runCommandWithOutputHandling`, `LicenseKeyChecker.getLicenseKeyContent`, and exact returned-value identities in `PipelineController.handleData` and `ConvertEmlToPDF.convertEmlToPdf`. All eight f945 additions and three of those gaps already exist in saved 52f/8331 evidence. Earlier audits identify a command receiver-reset discontinuity and representative-return coordinate drift, with their stated runtime limits; they are not fresh storage regressions.

The remaining difference from 52f/8331 is the LicenseKeyChecker fingerprint `OrIElyKyTPnc8RuEwzxEDt+d0He9J67gdnfHejprzfs=`. Saved 52f and 8331 had 21 reports at forward run 3 and 22 at forward run 5. Current 7069 and 4182 both stop before accepting run 5. The old per-run counts do not identify which exact key arrived in run 5. This missing identity is an observed snapshot difference, with a later-report explanation possible and a semantic cause unproved. Same-method alternate returns do not waive any strict identity gap.

The License audit pins the missing sink at `Files.exists(path)`, IR14, source line 98. It follows the saved controller/premium-key route and checks current source/model support. The current first missing required fact and rejecting native gate remain **unproved**. The older static-alias correction is already present in the compared lowerer files, and an unrelated getter RED result is not a License witness. The full audit is embedded in the portable evidence.

Thingsboard's 14 missing f945 identities are censored by timeout before the first accepted report. All three saved bidirectional controls also have no accepted report. Neither equality with those empty snapshots nor the 14-reference gap establishes final coverage.

## Time and memory

The table compares the matching 4182 command setup. These are single executions, with startup, profiling, and finite analysis budgets. Near-equal timeout wall times do not mean equal throughput. The f945 reference is used for quality; its earlier configuration and phase setup do not support a controlled speed claim here.

| Project | 4182 wall s | 7069 wall s | 4182 RSS GiB | 7069 RSS GiB |
| --- | ---: | ---: | ---: | ---: |
| OWASP | 204.31 | 230.29 | 17.75 | 16.59 |
| conductor | 1129.76 | 1131.98 | 17.93 | 18.16 |
| thingsboard | 1131.90 | 1122.82 | 18.18 | 18.23 |
| Stirling-PDF | 1109.61 | 1116.90 | 16.02 | 13.71 |

Conductor forward run 3 rises from 61.863 seconds in 4182 to 213.835 seconds. It also exports 257,270 handoff edges in 668 method keys, versus 174,269 in 660, and produces seven reports rather than five. More required guidance can increase work. The current data do not separate that workload increase from repeated processing cost. Its backward run 4 consumes the remaining 787.973 engine seconds and has no completed frontier. Stirling run 4 is 390.893 seconds versus 388.219 in 4182; both runs then time out in forward run 5.

No command reports OOM and no fresh heap snapshot exists. Thingsboard records four high-memory guard observations and three explicit `System.gc()` full pauses. This is memory pressure evidence, not an OOM. Peak RSS includes JVM/native memory and can exceed the 16 GiB heap. Whole-command GC pause shares are 2.63% OWASP, 1.63% Conductor, 4.78% Thingsboard, and 0.70% Stirling. Allocation sampling measures churn; RSS and post-GC occupancy do not identify retained owners. No retained-heap conclusion is available.

## Measured CPU and allocation work

The following shares use disjoint classifications of sampled Java execution stacks and weighted allocation samples within one continuous recording window. They are not wall-time fractions. Inclusive helper ownership is a separate overlapping measure. Its margins cannot be added to the disjoint scope shares or to one another.

| Window | Java samples | Largest scope | CPU sample share | Allocation-weight share | H-owned sample union |
| --- | ---: | --- | ---: | ---: | ---: |
| Conductor F3 | 19,280 | Loop consumer observation | 34.37% | 36.63% | 0 |
| Conductor B4, timed out | 191,271 | Loop consumer observation | 64.18% | 48.56% | 0 |
| Stirling B4 | 12,069 | Loop consumer observation | 78.56% | 86.46% | 7 |
| Stirling F5, timed out | 18,345 | Loop consumer observation | 81.78% | 87.92% | 1 |
| Thingsboard R1 static completion, timed out | 31,445 | Fact canonicalization | 47.98% | 52.45% | 0 |

Conductor B4's other large scopes include fact canonicalization (8.21%) and block saved replay (7.97%). The separate conditional set of 127,489 stacks that contain the observer partitions into saved-record application (73,641), C5 enclosing restriction (15,863), C2 initial admission (12,983), and other components. This conditional denominator differs from the disjoint owner count because outer scopes can own a stack that also contains the observer. The components do not add to a new whole-run denominator. Common leaf work includes `PreparedOutputPrograms.intersect`, collection iterators/equality, and `RestrictedInitialPolicy.fitsBudget`.

Conductor F3's combined public/block relation census also records zero protected memberships in admitted and outgoing rows. Together with zero sampled H-wrapper ownership in F3/B4, this prevents a measured attribution of that slowdown to `addWithProtection`, `embedRawProtection`, or `withCurrentProtection`. Zero samples do not prove zero executions. A separate bounded native probe confirms an exclusion-family mechanism in an AP/group fixture; the appendix states its scope. It does not establish real-project enabling or a Conductor cause.

Thingsboard requires a separate scope warning. Its continuous recording begins 106.213 seconds after the run-1 start. The approximate engine window is therefore only partly sampled. Within the observed part it has 78,212 Java samples: fact canonicalization is 21.64%, direct calls 19.89%, and the independent H-wrapper union 17.78% (19.07% of allocation weight). The static-completion window has a different denominator and must not be combined with it. The earlier `normal.collapsed` capture has 42,529 samples and the near-limit capture 7,626; they include native/GC stacks and have no per-stack timestamps. They remain separate evidence. The near-limit capture is largely GC work; it cannot be substituted for the Java-only continuous proportions.

The source-only work audit identifies possible repeated current-group restoration, H projection, per-delta scans, and packed affected-mark rebuilding. It preserves the existing incremental DATA order and literal typed H rule. Those costs are candidates for later investigation, not the measured cause of Conductor's late-run cost. The [next-iteration proposal](../design/bidirectional-lazy-observations-sparse-output-frozen-inputs-next-iteration-20261106.md) uses the current profiles to rank pure observation/restriction and sparse-output work. No speedup or eligibility intersection is established by these marginal profiles.

## Runtime and reader provenance

The initial pre-launch freeze was incomplete for five JARs. After OWASP finished, the original launcher stopped with `REVIEW_REQUIRED` because Gradle had packaged those JARs before JavaExec. The old five JAR byte hashes did not match; the old bytes are unavailable. Root verified that all 3,617 non-manifest ZIP entries match compiled/resource outputs older than the original freeze, all compile tasks were UP-TO-DATE/NO-SOURCE, and the five JAR tasks completed before the first analyzer log. Root accepted a reviewed post-packaging runtime binding. This is not retroactive pre-launch hash equality.

The append-only continuation retained OWASP and ran only the remaining three projects. All four are terminal in `combined-manifest.json`. The original launch file remains `REVIEW_REQUIRED`; it is preserved rather than treated as a complete campaign authority. Source/configuration pins, corrected classpath, proof, acceptance, continuation source, and the qualification are embedded.

The postprocessing preparation had two errors. The iteration module imported the selected revision but then replaced it with a local 4182 constant. The first all-stage stopped before iteration parsing. Root preserved that helper and used a wrapper that overrides only the revision binding after import. The summary helper also had an accidental tuple dictionary key. Root made a corrected copy with that single key fixed. Parser logic, metrics, raw inputs, guards, and original frozen helper pins were unchanged. The original all/review receipts remain failed `STARTED` records and are not completion evidence.

The later root completion record binds all nine output hashes, confirms EOF log reads, 71 scope/ownership checks, 17 Java anchor controls, and protected-wrapper classifier controls. Profile processing used continuous-first selection; overlapping recordings/windows were not summed. Source-only checks in this report preparation independently verify the embedded bytes, identity set differences, configuration pins, terminal labels, and those receipts. No analyzer or profile reader was launched to write this report.

## Remaining correctness boundary

The storage repair fixes the recorded backward fine-guide loss. The frozen small loop program still completes naturally at run 5 with no NORMAL finding. Its later getter boundary rejects a NORMAL `g.STAR/FLOW` input under a `g.ANY/FLOW` demand using the unchanged admission policy. The historical 52f same-program control also misses the finding. See the [repair reproducer](bidirectional-concrete-guidance-repair-reproducer-20261106.md) and [historical control](bidirectional-guidance-historical-control-and-data-bridge-20261106.md). Those facts neither prove a real-project first cause nor select a new admission rule or termination policy. The appendix below is separate from this campaign's measurements. The separate sealed no-loop control below does not change that original result.


## Appendix: bounded native exclusion-family probe

After all four commands and profile processing ended, root ran two native AP/group tests. Both passed. The portable output check passed 521 checks and contains 12 whole root-header snapshots. The mode is forward, FULL, non-run-1, field limit 2; the fixture keeps all paths at depth at most one. It uses current native source/cleaner/field-lowering operations and `TaintGroup`; it does not run the whole driver or a real project.

The source alone produces a plain NORMAL MUST/T root. Without a primer, five optional field-clean steps leave one plain header and no H. An EXACT root cleaner first converts the root into protected DEMAND MUST/T. Each optional strong field clean then transports that H and adds the chosen field to E. The join keeps literal protected tail/E coordinates:

```text
optional field steps          0  1  2  3   4   5
plain NORMAL root headers     1  1  1  1   1   1   (no H)
primed DEMAND H root headers   1  2  4  8  16  32
```

These are actual supplied typed root headers, with the full E sets saved in JSONL. They are not a growing path-depth family or merely extra helper replays. The observer reads whole root headers without another AP operation; stripping it recovers the prepared current-schedule source exactly. Preparation files retain their earlier PREPARED state; the later root receipt and XML establish the executed result.

The bounded result confirms this AP/group mechanism for five field choices. It does not prove that a real project enables the primer/branch sequence, that the full driver preserves the family, or that the family causes Conductor's cost. In particular, the current Conductor F3 census and F3/B4 sampled H-wrapper ownership are zero. No protected-membership or C2 policy change is selected by this probe.


## Appendix: separate three-method getter control

A second post-campaign native control removes the loop and mapper. It keeps the two ordinary field writes and resolved getters. All referenced objects/element slots are initialized in its finite IR:

```text
s = exact T source
temp.g = s
next.f = temp
x = getF(next)       // return arg0.f
y = getG(x)          // return arg0.g
out.Element.h = y
exact observeT(out.Element.h)
```

Root's frozen run exits 0, reaches and completes run 3, accepts forward run 3, and produces one NORMAL finding with natural `COMPLETE / NO_DEMAND_EDGE`. The source, IR contract, init/configuration, freeze, source pins, full console logs, and root outcome are embedded. It uses native source/sink rules and ordinary calls; it injects no demands, initials, or saved summaries.

This is a different three-method straight-line program. The original loop-plus-mapper program remains RED at natural run 5. The positive control shows that the native two-getter route can succeed. It is not recovery of the original program, an identification of its first cause, or evidence about the missing LicenseKeyChecker route.
