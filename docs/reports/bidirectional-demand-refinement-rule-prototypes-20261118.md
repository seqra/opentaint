# Demand refinement rule prototypes

The comparison point is the current FULL analyzer at `758ad99ff`.
Its production sources, rules and project runner match `0438facd2`.
Each prototype starts from that revision in a separate detached
worktree. The current checkout supplies the same native test sources
to every worktree.

## Decision criteria

- **USELESS** means an implemented rule resolved none of the measured
  termination cases. This label concerns termination in this suite.
- **COSTLY** means a rule resolved a case, but at least one configured
  project measured worse on at least one comparison metric. The label
  records the measured delta. Attributing that delta to a rule needs
  activation evidence and a matched repeat. The comparison includes
  the latest reached run, latest completed engine, stop reason,
  finding identities, elapsed time and memory.
- **Native parity** means the proposed behavior is already implemented.
  It has no independent runtime change to measure.
- A natural stop requires an empty frontier, complete status and
  preservation of required reachability. A missing confirmed
  observation is a regression. A vanished provisional observation
  requires its own trace before it counts as a fix. A run-101 cutoff
  establishes that the case still repeats within the measured range.

The four project scans use the production run-11 cutoff and the heap,
timeout and inputs in [task.md](../../task.md). The termination tests
and the selected compiled OWASP entry use run-101. Each benchmark
uses the source Gradle runner. Historical project measurements and
fresh measurements remain identified separately.

## Native baseline

The instrumented suite passed 138 tests and recorded 92 test cases
with at least one driver invocation. It reproduced the six acyclic
run-101 cutoffs. The compiled OWASP `doSomething` selected-entry scan
completed run-101 and reached the cutoff with two confirmed identities.
Its two fixture paths and source rule identities are the same as the
[extended baseline](bidirectional-termination-baseline-run101-20261118.md).

| Project | Reached / completed / accepted forward | Status | Wall s | Peak RSS GiB |
| --- | --- | --- | ---: | ---: |
| OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 | 9.781 |
| Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 | 9.749 |
| ThingsBoard | run-1 / none / none | Memory guard | 611.630 | 13.762 |
| Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 | 9.777 |

Each analyzer log records engine time at the completed checkpoints.
The fresh control records host load while the fixture worktrees build.

## Project comparisons

Compare each variant with the fresh native control above. The launch
manifests check inputs, memory, timeout, field schedule and profile
settings. The full receipts include engine and barrier times and exact
finding identities.

The earlier native campaign has the same production and rule trees,
models, field schedule and instrumentation. Its peak RSS was
9.663 GiB on OWASP, 10.145 GiB on Conductor, 13.720 GiB on ThingsBoard
and 9.897 GiB on Stirling-PDF. These are separate runs. Their resource
range helps interpret small differences in the fresh comparison.
[Earlier measurements](bidirectional-work-reduction-performance-20261112.md)

| Rule | Project | Reached / completed / accepted forward | Status | Wall s, native → variant | Peak RSS GiB, native → variant | Exact locations, lost / added |
| --- | --- | --- | --- | ---: | ---: | ---: |
| R13 | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 256.636 | 9.781 → 9.714 | 0 / 0 |
| R13 | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,125.337 | 9.749 → 10.188 | 0 / 0 |
| R13 | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 347.955 | 13.762 → 13.817 | No accepted report |
| R13 | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,109.192 | 9.777 → 10.062 | 0 / 0 |
| R26 | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 228.609 | 9.781 → 9.627 | 0 / 0 |
| R26 | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,119.994 | 9.749 → 10.068 | 0 / 0 |
| R26 | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 345.224 | 13.762 → 13.798 | No accepted report |
| R26 | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,110.341 | 9.777 → 10.335 | 0 / 0 |
| R35 | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 226.931 | 9.781 → 9.597 | 0 / 0 |
| R35 | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,122.229 | 9.749 → 10.071 | 0 / 0 |
| R35 | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 338.631 | 13.762 → 13.757 | No accepted report |
| R35 | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,109.321 | 9.777 → 9.933 | 0 / 0 |
| R41 geometry | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 229.630 | 9.781 → 9.579 | 0 / 0 |
| R41 geometry | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,121.634 | 9.749 → 10.008 | 0 / 0 |
| R41 geometry | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 345.307 | 13.762 → 13.744 | No accepted report |
| R41 geometry | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,108.428 | 9.777 → 9.821 | 0 / 0 |
| R36 | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 223.858 | 9.781 → 9.621 | 0 / 0 |
| R36 | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,121.206 | 9.749 → 9.946 | 0 / 0 |
| R36 | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 337.773 | 13.762 → 13.698 | No accepted report |
| R36 | Stirling-PDF | run-11 / run-11 / run-11 | Complete, run limit | 1,149.314 → 152.859 | 9.777 → 9.783 | 0 / 2 |
| R41 closed root | OWASP | run-11 / run-11 / run-11 | Complete, run limit | 266.022 → 223.656 | 9.781 → 9.546 | 0 / 0 |
| R41 closed root | Conductor | run-8 / run-7 / run-7 | Timeout | 1,128.739 → 1,121.402 | 9.749 → 9.956 | 0 / 0 |
| R41 closed root | ThingsBoard | run-1 / none / none | Memory guard | 611.630 → 335.814 | 13.762 → 13.901 | No accepted report |
| R41 closed root | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,106.762 | 9.777 → 9.929 | 0 / 0 |
| Native repeat | Stirling-PDF | run-11 / run-10 / run-9 | Timeout | 1,149.314 → 1,109.513 | 9.777 → 10.101 | 0 / 0 |

R13's first OWASP pass retained all 2,633 locations. Its driver time
rose from 160.421 s to 177.382 s while end-to-end time fell. Run-1
engine time was 79.048 → 92.072 s and run-2 was 25.508 → 34.158 s.
The H2 pair count was 20,032 → 20,036 and H3 stayed at 1,064.
The wall and engine measurements point in different directions.
A matched repeat is necessary to establish a performance change.

R13's Conductor pass kept all seven accepted locations. Both engines
timed out during run-8. The variant's peak RSS was 0.439 GiB higher.
The same increase is visible before the timeout. One-second sampled
peak RSS rose from 9.503 to 9.951 GiB in run-4 and from 9.591 to
9.969 GiB in run-6. Run-6 engine time fell from 499.159 to 388.747 s
and processed packets from 3,076,064 to 2,996,498. The **COSTLY**
label records the measured RSS regression on this pass. A matched
repeat is needed before attributing it to R13. Median heap after a
collection was 4,819 → 4,818 MiB in run-4 and 5,279 → 5,258 MiB
in run-6.

Both ThingsBoard scans hit the guard before the first completed
engine or accepted result. The wall comparison includes a longer
native prescan and heap export. At the start of export the Java heap
held 11,619,968,024 bytes in the native scan and 11,622,028,496 bytes
in the R13 scan. The shorter wall time measures an earlier failure.

On Stirling-PDF, the completed run-9 engine took 725.199 s in the
fresh control, 171.459 s with R13 and 160.007 s in the earlier native
campaign. At `decodeMimeHeader` the corresponding candidate offers
were 276,072, 90,266 and 90,216. The R13 sample matches the scale
of the earlier unchanged analyzer. The difference against the fresh
control alone cannot establish a speedup. Both fresh scans timed out
in run-11 with the same 32 accepted locations from run-9. R13 used
0.285 GiB more peak RSS on that pass.

The full OWASP scan handed R26 8,401 roots. Its single-root
prototype guard therefore retained native cleaner semantics in the
project scan. All 2,633 accepted locations match. This comparison
measures the guarded prototype on that input.
Conductor supplied 7,210 roots, and all seven accepted locations
matched. Its peak RSS rose by 0.319 GiB against the fresh control,
an observed **COSTLY** result. The 10.068 GiB sample lies below the
earlier unchanged analyzer's 10.145 GiB. This comparison measured
the guard and native transfer. Run-6 also took
387.554 s with this inactive cleaner guard, close to R13's 388.747 s.
That repeat weakens a speedup claim from R13's run-6 time alone.
ThingsBoard had 30,791 roots and hit the guard in run-1.
Stirling-PDF had 3,719 roots. It finished run-9 in 582.490 s with
276,083 candidate offers at `decodeMimeHeader`, close to the fresh
control's 276,072. The earlier native measurement had 90,216 offers.
These differing work counts occurred with native cleaner behavior.
The prototype reached run-11, retained the same 32 locations and
used 0.558 GiB more peak RSS than the fresh control.

R35's closed-callee guard also requires one root. It kept native
transfer on all four configured projects. Its Conductor peak was
0.322 GiB higher than the fresh control and within 0.003 GiB of
R26's inactive-guard sample.

R41's geometry ablation removed seven origins at the full OWASP
H4 handoff, eight at H5 and five at H6. Its H11 frontier had 1,002
pairs, down from 1,111 in the fresh control. Both scans completed
run-11 and exported the same 2,633 exact locations. Driver time was
160.421 → 158.598 s.

On Conductor, the geometry ablation removed 71 origins at H2.
H2 stored 477,877 pairs, down from 477,983 in the fresh control.
At each handoff from H3 through H7, all 128 attempts returned an
unsupported compiled-form result. Five owners contributed rows
to H5, with 50 attempts on one owner. The diagnostic repeated
the form check per origin. The spec's reuse of a verified scope
within one frozen handoff would address checks with matching scope
and input coverage. The Conductor scan retained the same seven
locations at the run-8 timeout. Peak RSS was 0.259 GiB higher
than the fresh control.

R36's partition counter remained zero on all four projects. Stirling-PDF
completed run-11 in 152.859 s and accepted 34 locations. The fresh
control timed out in run-11 with 32 locations from run-9. The new
accepted report contains all 32 earlier locations and two additional
ones. Both scans ran native cleaner transfer. A repeat from unchanged
sources under the same settings also varied substantially at run-9.

| Stirling-PDF run-9 work | Fresh control | Native repeat | R36 build |
| --- | ---: | ---: | ---: |
| Engine time, s | 725.199 | 390.653 | 4.450 |
| Restricted call offers, whole run | 7,576 | 7,562 | 7,576 |
| Body packets processed, `decodeMimeHeader` | 7,190 | 7,085 | 7,041 |
| Raw summary packets offered, `decodeMimeHeader` | 276,072 | 194,012 | 9,283 |
| Loop boundary limit offers, `decodeMimeHeader` | 6,389,744 | 4,375,223 | 38,074 |
| Prepared C5 queries, `decodeMimeHeader` | 28,991,481 | 19,699,439 | 119,383 |

The expensive pass generates work while replaying and restricting
loop-boundary outputs. Ordinary call input volume and body processing
were nearly unchanged. This is the same stage identified by the
[earlier native profile](bidirectional-work-reduction-performance-20261112.md#8-stirling-deep-images-before-shallow-restriction).

The unchanged repeat also timed out in run-11, completed run-10 and
kept the same 32 locations from run-9. Its peak RSS was 0.324 GiB
above the fresh control. That control variation is larger than
several measured prototype deltas.

The closed-root R41 guard made zero proof attempts at every completed
handoff of the full project scans. All reached and completed runs and
accepted locations matched the fresh control. Conductor peaked at
9.956 GiB and Stirling-PDF at 9.929 GiB, increases of 0.207 and
0.152 GiB against the fresh control.

## Rule results

| Rule | Native termination result | Project result |
| --- | --- | --- |
| R13 · reject strict-child overwrite keep on an EXACT FLOW point | The exact-origin nested-write fixture changed from run-101 with two outgoing pairs and one provisional observation to natural run-3 with zero pairs and zero observations. Confirmed observations in the suite were preserved. The compiled OWASP entry still reached and completed run-101 with the same two confirmed identities. | **COSTLY** on peak RSS in Conductor and Stirling-PDF. All four scans finished with the same reached and completed runs as the fresh native control. Accepted locations agree. |
| R01–R03 · NE cuts and transfer, with NE admission and projection | **USELESS** in the corrected prototype. The first version stopped the compiled OWASP entry at run-5 and lost confirmed observations elsewhere. The C2/C5 repair restored those observations and the OWASP run-101 cutoff. | Skipped. |
| R04 · add an EXACT start to the same-head MAY family | **USELESS**. No natural stop added. OWASP reached and completed run-101 with both observations. The alternating conditional fixture grew from 4 to 7 pairs at run-101. | Skipped. |
| R06 · qualify the possible STAR ancestor binding | **USELESS** in the late restricted prototype. No ordinary natural stop added. OWASP reached and completed run-101 with both observations. One deferred recursive control changed from natural run-5 to the run-101 cutoff. | Skipped. |
| R07 · preserve the exclusion at the actual head | **USELESS**. No natural stop added. OWASP reached and completed run-101 with both observations. The exclusion component test exercised the changed admission. | Skipped. |
| R08 · keep the full head and exclusion of an eligible deeper MUST offer | **USELESS**. No natural stop added. OWASP reached and completed run-101 with both observations. The exclusion component test exercised the changed admission. | Skipped. |
| R10 · prepare one level of child starts | **USELESS** in the late restricted prototype. No natural stop added. The global-cut fixture completed run-101 with 7 pairs instead of 6. Its protected variant completed run-99 before the fixture timeout, with 240 pairs instead of 7 at baseline run-101. OWASP completed run-101 with both observations. | Skipped. |
| R27 · prefer ready EXACT, NORMAL and control work | **USELESS**. All 138 tests passed. No change in recorded native end states. OWASP reached and completed run-101 with both observations. | Skipped. |
| R29 · preserve literal protection on transfer and cuts | **USELESS**. All 138 tests passed. No recorded change to termination. OWASP reached and completed run-101 with both observations. | Skipped. |
| R20 · qualify raw C2 membership before C5 | **USELESS** in isolation on native tails. All 138 tests passed. OWASP reached and completed run-101 with both observations. The rule is required for the tested NE integration. | Skipped. |
| R31 · mask only intersecting FULL FLOW suffix cones | **USELESS**. No natural stop added. OWASP reached and completed run-101 with both observations. | Skipped. |
| R32 · use the same-head nonstatic run-2 STAR identity | **USELESS**. All 138 tests passed with an adapter that accepts the new raw STAR start. No natural stop added. OWASP reached and completed run-101 with both observations. | Skipped. |
| R34 · apply a possible saved direct STAR read | **USELESS** for termination. The native component comparisons recovered observations in two broad-read cases. OWASP reached and completed run-101 with both observations. | Skipped. |
| R26 · keep NORMAL support for a selected root point cleaner with a complete terminal observer guard | The uniform root cleaner changed from the run-101 cutoff to natural run-1 and confirmed the same observation. The exact observer control still passed. This prototype accepts only the closed, same-method normal-exit case. | **COSTLY** on peak RSS in the fresh Conductor and Stirling-PDF comparisons. All accepted locations and run endpoints matched. The single-root guard kept native cleaner transfer on all four projects. |
| R35 · guarded selected point cleaner below the root | The direct slice was **USELESS**. The closed-callee variant follows the cleaner's bound carrier through an empty analyzed callee and the remaining call stages. The descendant-point fixture changed from the run-101 cutoff to natural run-1 and confirmed the same observation. | **COSTLY** on peak RSS in the fresh Conductor and Stirling-PDF comparisons. The guard stayed inactive on all four projects. All accepted locations and run endpoints match. |
| R36 · partition surviving NORMAL uniform taint after a subtree clean | The nested BELOW, selected whole-subtree and RemoveAll fixtures changed from the run-101 cutoff to natural run-3. Both added exclusion controls passed. An existing exclusion stays at its original head and blocks descent into an excluded field. The selected compiled OWASP entry still reached and completed run-101. | **COSTLY** on peak RSS against the fresh Conductor pass. All four scans recorded zero partition calls. Stirling-PDF completed run-11 and reached two more locations. |
| R37 · discharge uniquely served origins at a closed acyclic root | **USELESS** in the copy-only scope. All 138 tests passed. OWASP reached and completed run-101 with both observations. | Skipped. |
| R38 · discharge NoRoute origins at a closed acyclic root | **USELESS** in the copy-only scope. All 138 tests passed. OWASP reached and completed run-101 with both observations. | Skipped. |
| R41 · retire a FLOW relation with independent saved replay | The geometry ablation stopped the compiled OWASP entry at run-7 with both observations, and the global-cut and root-MAY cases at run-7 and run-5. The closed-root variant additionally checks the compiled caller closure and its independently confirmed observation. It stopped both synthetic cases at run-7. It retained the OWASP demand through run-101. | Both builds measured **COSTLY** against fresh peak RSS on Conductor. The geometry variant removed origins on OWASP, Conductor and Stirling-PDF. The single-root guard stayed inactive on all full projects. Both builds matched all accepted locations and run endpoints. The work allowance and a wider continuation certificate remain open. |
| R42 · check complete same-lane uniform service | **USELESS** in the provider ablation and the closed-root prototype. Removing whole origins with a matching NORMAL MUST provider reduced the global-cut frontier from 6 to 3 at run-101. The Target remained. Both variants passed all 138 tests, and OWASP completed run-101 with the same two observations. | Skipped. The continuation certificate covers the tested single-observer root scope. |
| §8.1 · singleton handoff compaction and adjacent C5 entry reuse | **USELESS** for termination. Each prototype passed all 138 tests. Neither added a natural stop. The C5 prototype reuses an exact entry ticket in the existing prepared-plan walk and preserves each paired exit. | Skipped under the termination-first gate. |

### Native rules and dependencies

| Rules | Prototype boundary |
| --- | --- |
| R05, R09, R21 and R23 | The NE worktrees exercise NE-specific C2, paired exit selection and distinct MAY/NE rows. A baseline with only native tails has no NE row to drive these operations. |
| R11/R12 | Prepared children use the existing transfer and output admission, with each child keeping its own bound origin. The additional admissible children belong to the R10 prototype. |
| R14/R15 | Saved-first replay and the definite and provisional MUST lanes are native, including when current C2 is empty. |
| R16/R19/R24 | Ordinary replies retain NORMAL and DEMAND as separate memberships. Certified removal is the R42 experiment. |
| R18/R22 | Native publication runs C5 before summary-store admission and retains its FLOW normalization. The change to the raw entry test is R20. |
| R25 | Native exact service compaction checks its final retained provider basis. The NE experiment keeps NE distinct from the older key relation. |
| R28/R30/R33 | Keep native typed control, complete ND application and handoff mask behavior. The NE prototype carries the new DATA tail through the existing handoff. |
| R17, R39 and R40 | R17 was removed from the spec. The spec postpones the loop and recursive retirement rules R39 and R40. |
| §8.1 C5 output sharing | Native prepared C5 already shares one output program per full exit selector and cap within an exact owner, port, original and policy query. The separate C5 prototype tests reuse of the remaining repeated entry checks. |
| §8.1 current application | Native replay deduplicates a publication's exact `(premise, member)` posting, and publication delivery deduplicates caller handles across trie walks. The publication store emits fresh membership and selects its final retained part before delivery. An additional merge across different authorizations needs equal bound output and effect, which the identical-posting shortcut cannot establish. |

R01–R03 share the NE representation. The experiment also implements
the NE-specific admission, exit selection and distinct storage needed
to exercise the new tail in a native scan. It changes nonstatic cuts
and retains the native static completion view. Independent C2
changes for existing MAY inputs stay outside this worktree.

### Nonempty MAY

The selected OWASP helper kept two DATA pairs at H3 in both
executions. At H4, two of its four prototype pairs ended in NE,
where the baseline had four MAY pairs. At H5, the prototype had
zero helper DATA pairs and an empty full frontier. The baseline
kept two helper pairs and continued.

| Acyclic fixture | Baseline reached / completed and outgoing pairs | Initial NE | NE with corrected C5 |
| --- | --- | --- | --- |
| Global cut | run-101 / run-101, 6 | run-101 / run-101, 302 | run-101 / run-101, 302 |
| Nested replay | run-101 / run-101, 5 | run-58 / run-57, 474 | run-65 / run-64, 511 |
| Overwrite replay | run-101 / run-101, 5 | run-63 / run-62, 495 | run-64 / run-63, 522 |

Both NE versions exhausted their 60-second fixture budgets on the
nested and overwrite cases. With the initial NE version, the
Conductor mapper recovery fixture lost its confirmed observation and
stopped at run-3.

The E29 mapper isolates the first missing relation. It is a C2/C5
disagreement at run-2.

| Stage | Baseline | Initial NE prototype |
| --- | --- | --- |
| Submitted return fact | `ret.[].M/T,D` | `ret.[].NE/T,D` |
| Paired demand | `p.*/F → ret.[].M/F` | `p.*/F → ret.[].NE/F` |
| Requested initial | `ret.[].*/F,N` | `ret.[].*/F,N` |
| Raw backward body result | `p.f.M/F,D` and `p.M/F,D` | `p.f.NE/F,D` and `p.M/F,D` |
| Published relation used by run-3 | `ret.[].*/F → p.M/F,D` | None. The native denotation test rejects the legal STAR start under NE. |

The separate R01–R03 + R20 worktree recognizes that STAR start
through the constructive raw C2 image. The E29 control again stops
at run-5 with its confirmed observation. The full native comparison
found six failures and preserved every baseline confirmed observation.
The global-cut fixture still completed run-101 with 302 outgoing pairs.
The same repair restored the OWASP helper's six forward and eight backward
pairs from H7/H8. The selected entry again reached and completed run-101.
The initial run-5 stop depended on the missing C5 service.

### Prepared children

R10 added possible child bindings from frozen deeper guides and saved
record guards. It used the previous qualified-input protocol with the
other transfer changes disabled. In a second worktree, the same
protocol ran with child preparation disabled. All 138 tests passed
there. The plain and protected global-cut fixtures again had 6 and 7
pairs at run-101. The isolated difference associates the 240-pair
protected frontier with enabling prepared children in this protocol.
The hidden-rename fixture also recovered its expected run-3 guidance
with child preparation disabled. The original fixture has all four
expected outcomes again, through runs 11 and 13.

| Protected fixture handoff | Helper pairs, protocol control | Helper pairs, prepared children |
| --- | ---: | ---: |
| H3 | 6 | 6 |
| H4 | 4 | 5 |
| H5 | 6 | 9 |
| H7 | 6 | 15 |
| H19 | 6 | 47 |
| H49 | 6 | 127 |

The first new helper row at H4 has a depth-one MAY entry and a
depth-one EXACT exit. In run-4 the old `ret.M/T` demand and
`ret.M/T,D` actual start the added `ret.f.$/T,D` and
`ret.f.*/T,D` queries. In run-5 the resulting
`p.f.M/T → ret.f.$/T` pair admits another child at `p.f.f`.
Run-6 can then start at `ret.f.f`. Each query extends its own
head by one field. Its projected demand can supply a longer head
for the next handoff.

### Same-lane uniform service

The R42 handoff shadow checks the same raw MUST initial, method or
physical block ports, output base, mark or FLOW mark exclusion, literal
protection and unexcluded uniform region. It applies the saved provider
with the native matcher. The selected compiled OWASP entry had no
applicable candidate.

The independent ablation removed each matched origin before handoff
compaction. The global-cut fixture retained its confirmed observer and
one Target at run-101. The protected global-cut fixture still had seven
pairs at run-101. This isolates the limit of the provider-side optimization.
Even when it removes the three pairs, the surviving continuation can
renew demand. The [uniform origin control](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/UniformCoverageOriginAuditTest.kt)
shows a later exact path from a second origin that an equal observer
identity and an overlapping NORMAL provider can leave unserved.

The closed-root prototype additionally requires the compiled
single-origin continuation check used for scoped R41. It reproduced
the same 6-to-3 reduction in the global-cut fixture while keeping the
confirmed observation and its Target. The protected fixture and the
compiled OWASP entry still reached run-101. This narrower removal
also yielded zero new natural stops.

Live R42 has a separate enablement condition. The current publisher
detaches incremental batches of fresh memberships. Additional
replies for the same caller binding can arrive later. The spec
requires a complete existing packet or a frozen continuation
certificate before live folding can run.

### R41 on the compiled OWASP entry

The geometry ablation found the first two independently aligned
provider origins at H4. They account for four paired rows. The
baseline renewed the helper demand. In the ablation the caller
continued on its own demand until H7 became empty.

| Completed handoff | Native DATA + Target pairs | Geometry ablation pairs | Native / ablation Target rows |
| --- | ---: | ---: | ---: |
| H4 | 13 | 9 | 1 / 1 |
| H5 | 9 | 4 | 7 / 4 |
| H6 | 26 | 15 | 1 / 1 |
| H7 | 17 | 0 | 11 / 0 |

Both executions kept the same two confirmed locations. The project
measurements include the ablation's fixed diagnostic inspection budget.
The spec requires an allowance from work already saved.

The separate singleton-compaction audit found zero singleton groups
at H4, where the ablation discharged the first two origins. All five
backward handoffs through H10 had zero singleton groups. H3 and H5
each had one group with one row. Singleton compaction therefore
provides zero allowance at the observed H4 discharge. The native
allowance path needs a separately audited saving at an eligible seal
before it can run this certificate.

The closed-root variant requires a finite compiled call closure with
one unguarded marking action at root entry and one observation at
root exit. It rejects an extra marking action, an extra observer,
cleaners, recursion, loops and unsupported call forms. It also
requires a confirmed ZERO-to-NormalTarget for the observer. The only
input origin is then independently served. The eligible origins in
the two synthetic cases stopped at run-7 with their confirmed
observations. The compiled OWASP entry run supplies two roots, so it
keeps the native handoff under the closed-root guard. It completed
run-101 with both findings. This variant still uses the diagnostic
budget.

### R13 nested-write trace

The only marked source is below `x.g`. The read branch needs `x.f`,
which has no mark. The write branch copies `x` below `ret.f`.
That places the only marked subtree at `ret.f.g`, which the
following overwrite removes. Neither branch can reach the observer.

The baseline also starts a conditional EXACT FLOW probe at `x.$`.
The strict-child keep for `x.f.g = new Node()` can convert it into
`x.f.M/F,D`. The read branch can then produce `ret.M/F,D` and renew
the provisional observer. The prototype rejects that strict-child
result and keeps `x.$/F{f},N`. Three tests with baseline-specific
expectations fail in the prototype, covering the strict-child edge,
its read result and the run-101 cutoff. The component control with
the real marked input still produces no output in either branch.
[Fixture](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/AcyclicTerminationBaselineTest.kt)

## Reproduction

Local worktrees, patches, fixture receipts, project profiles and
comparison scripts live under
`demand-refinement-rule-prototypes-20261118.n00xyl/` in the
[external report archive](EXTERNAL_DATA.md). The native tests record
the last completed barrier, the stop reason, outgoing pair and Target
counts, and confirmed and provisional rule/location identities per
driver invocation.
