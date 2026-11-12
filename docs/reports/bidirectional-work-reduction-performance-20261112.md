# Bidirectional work reduction: validation and performance, 12 November 2026

Measured runtime: `472288cf34ddf75290e3fab4d6f5cbc0a366646c`.
Core tree: `845413a861a3bbc50492785efb88124aa419e924`.
The implementation is committed in the main repository. The working tree was
clean during the scans. The fixed finding baseline is
`54ad708fe1c4f551956d3d572866de1534415fa1`. Its saved results were reused;
the baseline was not run again.

## 1. Result and acceptance limits

| Project | Stop | Latest reached | Latest completed | Accepted forward | Findings | Exact baseline missing / extra |
| --- | --- | --- | --- | --- | ---: | ---: |
| OWASP | RUN_LIMIT | run-11 | run-11 | run-11 | 2,633 | 0 / 0 |
| Conductor | TIMEOUT | run-8 | run-7 | run-7 | 7 | 0 / 0 |
| Stirling-PDF | TIMEOUT | run-11 | run-10 | run-9 | 32 | 8 / 16 |
| Thingsboard | guard OOM | run-1 | none | none | 0 | 15 / 0 |

OWASP and Conductor preserve all saved baseline locations and fingerprints.
The incomplete Conductor baseline also ended with OOM; this comparison does
not prove complete project coverage. RUN_LIMIT is not natural convergence.
Stirling has eight return-location differences that need witness-path
validation. Thingsboard cannot publish its first forward result before OOM.
Thus the full exact-location no-FN acceptance gate is **not established**.
The baseline is a legacy scan and has no bidirectional run number.

The main costs are different:

- **OWASP, through run-11:** method-form and predicate construction dominate
  early runs. Engine/barrier guards clear the managed form payloads.
- **Conductor, through run-8:** local summary matches expand into millions of
  result callbacks, C2 queries and complete loop observations.
- **Stirling, through run-11:** saved block-summary applications generate deep
  string/byte field combinations before shallow loop/C5 restriction. A small
  demand frontier does not bound this work.
- **Thingsboard, run-1:** concrete method/block memberships and standing
  subscriptions fill the heap. Static writer storage is small. Static-origin
  requests can still cause ordinary argument/local work downstream.

The compact [validation receipt](bidirectional-work-reduction-validation-20261112.json)
records source/config hashes, native gates and terminal frontiers.
The next proposals are in
[the next-iteration design](../design/bidirectional-full-mark-and-loop-work-next-iteration-20261112.md).
No new transfer or cache fix from this investigation was added to the runtime.

## 2. Implemented scope and gates

The [implementation proposal](../design/bidirectional-work-reduction-implementation-20261112.md)
is implemented: exact-service handoff compaction R1/R2/exact R4, impossible C2
candidate pruning, early negative loop probes with same-trial C2 reuse,
optional unresolved-call diagnostics, and exact FULL caller-input packing.
Residual R3 MAY removal stays disabled. Its eventual-refinement proof is open.
Field transfer, sources/sinks, protection, field limits and the selected
persisted-summary-first call policy stay unchanged. Private storage sharing
does not introduce a synthetic FLOW initial or a public mark kind.

| Gate | Tests | Failures | Skips | Result |
| --- | ---: | ---: | ---: | --- |
| Common dataflow, full suite | 2,589 | 0 | 0 | Pass |
| JVM dataflow, full suite | 467 | 0 | 0 | Pass |
| Broad root suite, bidirectional mode | 1,083 | 20 | 11 | Fail; same prior failures and asserted values |
| Source Java/Go rules | 786 successful | 0 FP / 0 FN | 0 | Pass; 22 disabled |

The four constructive Lean models pass 79 local claims. Native tests bind
those claims to packet snapshots/deltas, ports, literal protection and delivery
order. This is not a proof of all Kotlin code. See the
[runtime binding](../../spec/lean/proposals/in-handoff-compaction-20261112/runtime-binding.md).
The 20 root failure identities and expected/actual assertion values match the
previous validation. Sixteen complete messages match; four include changing
trace order. No assertion or finding expectation was weakened.

The source-only rules pipeline took 83.467 s. It used
[the Gradle rules procedure](../rule-testing.md), rebuilt Java/Go models and the
Go server from source, and downloaded no CI artifact. All 585 active Java
samples have bidirectional start/end evidence. All 201 Go samples passed on
their existing engine. Java collected 607 of 609 declarations: 585 passed and
22 were disabled. Two known RMI interface declarations were not collected;
they are coverage gaps, not passed tests.

Java latest reached/completed/accepted labels agree for each sample:
449 at run-1, 128 at run-3, three at run-5, two at run-7, one at run-9,
and two at run-11. The two capped samples are
`UnsafeFileUploadServlet#doPost` and
`PassthroughFileModelSamples#fileToStringUnsafe`. The other 583 stop with no
demand. Rule classifications and these frontiers match the preceding campaign.

## 3. Configuration and measurement units

All four scans use source Gradle `:runProjectAnalyzer`, FULL marks,
aliases/statics enabled and limits `1,1,2,...`. Heavy scans run in sequence.
No CLI, alternate heap, disabled-feature control or baseline rerun was used.

| Project | Java heap / timeout | Current wall s | Current peak RSS GiB | Fixed baseline wall s / stop | Baseline findings |
| --- | --- | ---: | ---: | --- | ---: |
| OWASP | 8 GiB / 1,000 s | 224.920 | 9.663 | 156.357 / OK | 2,633 |
| Conductor | 8 GiB / 1,080 s | 1,120.904 | 10.145 | 187.389 / OOM | 7 |
| Stirling-PDF | 8 GiB / 1,080 s | 1,109.304 | 9.897 | 52.109 / OK | 24 |
| Thingsboard | 12 GiB / 1,080 s | 339.216 | 13.720 | 439.652 / OOM | 15 |

Wall time includes preparation/report work. Java heap and process RSS differ.
Current profiles/statistics add cost. The legacy and multi-run engines perform
different work. These are observed times, **not per-feature speedup estimates**.
OWASP is slower in wall time; Conductor/Stirling time out; Thingsboard still
fails before its first result. No same-revision disabled-optimization control
was authorized or measured, so net runtime gains from individual changes are
unknown. Current operation counts below show what work was removed or remains.

The model SHA-256 values match the saved baseline:

| Project | Model SHA-256 |
| --- | --- |
| OWASP | `e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873` |
| Conductor | `3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d` |
| Stirling-PDF | `b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4` |
| Thingsboard | `1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3` |

Each source command is `./gradlew :runProjectAnalyzer --console=plain -I
<project>/benchmark.init.gradle -x :opentaint-ir:go:buildGoServer`.
The init file configures the task's Java heap and project/output/timeout/rules
arguments, `--ifds-bidirectional`, debug logs and fingerprints. It enables
`org.opentaint.bidi.formStatistics`, `org.opentaint.bidi.optimizationStatistics`,
continuous JFR, GC logs and guard heap snapshots. Source Go compilation was
already completed before the Java project scans. All literal commands, JVM
arguments, source/model hashes and exits are retained in the manifests.

CPU captures request 30 s after 60 engine seconds and near the time limit.
JFR timestamps separate engine/handoff phases. OWASP's first named CPU capture
crosses run-1, handoff and early run-2; its whole file is not a run-1 profile.
Thingsboard ends before a near-limit capture. Its normal capture is wholly
inside run-1. The extra run-1 end-dump attach failed after process exit;
continuous JFR and the normal CPU capture are available.

Table units used below:

```text
Handoff rows = normalized builder insertions, including typed Target/control rows.
Target origins = outgoing method + inner-block Target origins before compaction.
Do not add these two columns. One ND origin can project several handoff rows.
Raw projections = member-by-leaf obligations before normalized builder insertion.
A point membership includes its store/scope; it is not a unique AP or CPU event.
Missing aborted-run frontiers are unavailable, never zero.
```

CPU samples, sampled allocation weights, retained heap and wall time measure
different things. Inclusive frames overlap. Disjoint tables below assign each
sample once. Top-24 method counters are partial censuses. Equal demand counts
do not prove equal rows or redundancy.

## 4. Iteration times and frontiers

Run-1 static binding is separate from engine/barrier time: OWASP 0.430 s,
Conductor 1.266 s and Stirling 0.403 s. Thingsboard reaches no handoff.
The barrier includes report/next-run preparation, not only demand compaction.

### OWASP: reached/completed/accepted run-11

| Run | Direction / limit | Engine s | Barrier s | Handoff rows | Target origins | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | forward / 1 | 79.917 | 2.841 | 68,053 | 6,929 | 2,120 |
| run-2 | backward / 1 | 22.580 | 0.857 | 20,029 | 1,965 | 2,120 |
| run-3 | forward / 2 | 9.340 | 0.820 | 1,064 | 1,129 | 2,633 |
| run-4 | backward / 3 | 3.967 | 0.577 | 2,173 | 481 | 2,633 |
| run-5 | forward / 4 | 3.324 | 0.610 | 967 | 912 | 2,633 |
| run-6 | backward / 5 | 5.526 | 0.486 | 2,004 | 430 | 2,633 |
| run-7 | forward / 6 | 4.000 | 0.536 | 1,017 | 947 | 2,633 |
| run-8 | backward / 7 | 3.396 | 0.561 | 2,095 | 430 | 2,633 |
| run-9 | forward / 8 | 3.428 | 0.604 | 1,017 | 947 | 2,633 |
| run-10 | backward / 9 | 3.579 | 0.476 | 2,095 | 430 | 2,633 |
| run-11 | forward / 10 | 3.169 | 0.526 | 1,017 | 947 | 2,633 |

### Conductor: reached run-8; completed/accepted run-7

| Run | Direction / limit | Engine s | Barrier s | Handoff rows | Target origins | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | forward / 1 | 19.556 | 1.912 | 127,044 | 7,921 | 2 |
| run-2 | backward / 1 | 41.308 | 6.395 | 478,078 | 206 | 2 |
| run-3 | forward / 2 | 8.051 | 0.997 | 17,448 | 3,760 | 5 |
| run-4 | backward / 3 | 109.977 | 0.792 | 29,928 | 39 | 5 |
| run-5 | forward / 4 | 9.181 | 0.783 | 25,028 | 3,932 | 7 |
| run-6 | backward / 5 | 383.349 | 1.794 | 150,270 | 39 | 7 |
| run-7 | forward / 6 | 94.874 | 0.962 | 86,763 | 4,512 | 7 |
| run-8 | backward / 7 | 372.341, partial | unavailable | unavailable | unavailable | not committed |

### Stirling-PDF: reached run-11; completed run-10; accepted run-9

| Run | Direction / limit | Engine s | Barrier s | Handoff rows | Target origins | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | forward / 1 | 21.127 | 0.839 | 66,172 | 6,105 | 7 |
| run-2 | backward / 1 | 13.783 | 2.809 | 265,841 | 603 | 7 |
| run-3 | forward / 2 | 4.224 | 0.811 | 1,596 | 743 | 28 |
| run-4 | backward / 3 | 4.062 | 0.719 | 4,844 | 295 | 28 |
| run-5 | forward / 4 | 1.165 | 0.584 | 1,224 | 371 | 32 |
| run-6 | backward / 5 | 7.089 | 0.654 | 1,327 | 100 | 32 |
| run-7 | forward / 6 | 9.443 | 0.661 | 969 | 252 | 32 |
| run-8 | backward / 7 | 16.863 | 0.684 | 1,117 | 40 | 32 |
| run-9 | forward / 8 | 160.007 | 0.732 | 868 | 178 | 32 |
| run-10 | backward / 9 | 17.107 | 0.597 | 1,111 | 39 | 32 |
| run-11 | forward / 10 | 795.610, partial | unavailable | unavailable | unavailable | not committed |

### Thingsboard: reached run-1; none completed/accepted

Run-1 engine time is 183.641 s, including the 27.839 s live heap-dump operation.
There is no completed frontier, report barrier or static binding result.
The current result therefore has no accepted findings. The 60 s run-1 engine
target is not met on Thingsboard or OWASP.

## 5. Findings and the Stirling location gap

OWASP matches all 2,633 baseline results by rule, physical URI/full region,
logical method, multiplicity and fingerprints. Conductor matches all seven
on the same keys. Stirling has 16 exact matches, eight baseline-only regions
and 16 current-only regions. All 21 baseline full-method/rule keys occur among
29 current keys. This broader match cannot prove the same source-to-sink path.

The eight baseline-only locations have a same-full-signature/rule current
candidate. All are `java.security.xss#sink#1` at return instructions:

| Method | File (relative to project source) | Baseline region | Current candidate |
| --- | --- | --- | --- |
| `ConvertEmlToPDF#convertEmlToPdf` | `app/core/src/main/java/stirling/software/SPDF/controller/api/converters/ConvertEmlToPDF.java` | 133:17–134:77 | 148:13–149:84 |
| `PipelineController#handleData` | `app/core/src/main/java/stirling/software/SPDF/controller/api/pipeline/PipelineController.java` | 90:17–91:93 | 130:13–130:24 |
| `JobController#getFileMetadata` | `app/core/src/main/java/stirling/software/common/controller/JobController.java` | 278:17–287:43 | 291:13–292:79 |
| `AdminSettingsController#getSettingValue` | `stirling/software/proprietary/security/controller/api/AdminSettingsController` | line 381 | line 388 |
| `InviteLinkController#generateInviteLink` | `stirling/software/proprietary/security/controller/api/InviteLinkController` | line 242 | line 246 |
| `InviteLinkController#validateInviteToken` | `stirling/software/proprietary/security/controller/api/InviteLinkController` | line 387 | line 391 |
| `InviteLinkController#acceptInvite` | `stirling/software/proprietary/security/controller/api/InviteLinkController` | line 477 | line 482 |
| `UserController#inviteUsers` | `stirling/software/proprietary/security/controller/api/UserController` | line 518 | line 521 |

The last five URIs are class-style locations in SARIF, not invented `.java`
paths. Source inspection confirms different return arms, including success,
error and null responses. Current exit reporting uses the synthetic
`JMethodExitNormalInst`. Its `SinkKey(method,node,rule)` does not retain the
witness return. `JIRBidiAnalysis` exports a simple result without a path;
`TraceMessageBuilder` selects the last return when no trace supplies one.
This explains a concrete location-selection gap. These reporting sources have
no diff from pre-optimization `a375bf7c4` to the measured runtime: the mechanism
predates this optimization. It does not prove that all eight baseline source
paths survive.

Eight additional full-method/rule keys are XSS results in
`WebResponseUtils.bytesToWebResponse`, `WebResponseUtils.multiPartFileToWebResponse`,
`FilterController.fileSize`, `pageCount`, `pageRotation`, `pageSize`,
`UserController.register` and `AuthController.login`. Their TP/FP status is
unverified. Return relocation does not explain these extra keys. A future
reporting fix must retain actual witness provenance, not select another return
by a heuristic.

Thingsboard's 15 baseline results are absent because the driver does not accept
a failed first forward iteration. The incomplete run exits before its report
barrier. This is a resource failure with an unaccepted frontier; it is not
evidence of 15 independent rejected transfer paths.

## 6. OWASP: repeated form construction

Reached/completed/accepted: run-11. The run-1 report barrier costs 2.841 s,
while engine run-1 costs 79.917 s. Per-run JFR Java execution samples show:

| Engine | Form payload lookup/build | Actual call-plan construction | Sampled allocation churn | Churn under form payload |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 47.54% | 40.43% | 129.56 GB | 48.67% |
| run-2 | 56.30% | 52.24% | 41.59 GB | 56.30% |

These inclusive scopes overlap. Allocation weights estimate churn, not live
heap. The final counters contain 582,003 successful forward payload builds,
195,829 reversals, 2,014,434 predicates and 10,849,928 predicate nodes.
A payload can be a statement, call plan, entry or exit object. It is not a
unique method. Summed build time across workers is not engine wall time.

Both `RunManager.run` and `IterationDriver.withBarrierGuard` use
`MemoryManager.runWithMemoryManager`. Its `finally` clears all managed soft
reference groups, including `bidi-method-forms`, even after a low-memory
success. The owner survives while its payload becomes cold. Backward misses
build the forward payload and then reverse it. OWASP has no high-memory/reset
notice. The counters do not separate each first build from each rebuild.

The rule provider caches resolved rules, not compiled new-core predicate DAGs.
Lowering also normalizes the already normalized mark residual again. Exact
immutable graph/template reuse can avoid repeated construction, while a
changed form-payload lifetime can avoid later rebuilds. Site and occurrence
wrappers must stay separate. In particular, backward sink compilation is
required by `ZERO -> fireSinkSeeds -> Seed.PredicateSink -> plan.sinks`.
Removing it would remove backward source seeds.

The handoff selector itself is small on OWASP: ten passes cost 205.098 ms.
They reduce 33,813 origins to 30,069 (3,744 origin certificates). Raw projections
fall from 39,098 to 34,985; the normalized builder accepts 33,478 rows.
The units differ, so 4,113 raw cuts are not 4,113 measured published-row savings.
No uncompacted normalized-builder counterfactual was collected.

Caller packing consumes 0.554% of run-1 Java CPU and 0.214% of sampled churn.
Its released directory totals have 30,783 packed sources in 13,044 families
(2.36 sources per family), 13,406 cells, 29,087 diagonal memberships and 3,557
changing pairs. Another 28,456 groups use scalar fallback. These are cumulative
released totals, not simultaneous retained bytes or a byte-saving estimate.

## 7. Conductor: loop observation and callback expansion

Reached run-8; completed/accepted run-7. The late growth also affects forward
run-7. It is not confined to backward runs. The two leading
`ParametersUtils.replace(Map,DocumentContext,String)` contexts perform over
6.1 million scalar loop queries and 13.9 million prefix trials in run-6.
The HashMap context alone has:

```text
4,188,721 scalar baselines + 9,422,567 proper-prefix trials
- 3,416,026 early negatives = 10,195,262 full observations
```

The early probe avoids 3,416,026 full observations for these same current
queries. This is an operation-count comparison with the full observer, not a
measured speedup against an earlier revision.

| Completed run-6 work | Count |
| --- | ---: |
| C2 direct queries | 40,253,036 |
| C2 trie candidates | 85,101,491 |
| C5 row attempts / exact rejects | 52,646,154 / 43,235,822 |
| C5 selected packets | 9,410,332 |
| Top-24 current local native matches | 3,605,947 |
| Top-24 current DATA callbacks | 20,799,228 |
| Top-24 C2 queries / native starts | 43,303,412 / 39,692,749 |

A current local match yields 5.77 DATA callbacks on average in the printed
sample. Each callback can start scalar/budget observation. An outer actor
item or matched packet is not one inner query. Saved-reader counters mix real
saved replay and pure observations; they cannot all be called propagation.
Aborted run-8 body snapshots with zero actors are unavailable, not zero work.

A decoded run-6 pure-observer example is:

```text
P:      ret.Map.Entry.Value.*/FLOW
Demand: ret.[any]/FLOW -> arg(0).MapKey.[any]/FLOW
Raw:    arg(2).HeaderIterator.headers.MutablePair.right.MapValue.MapValue.
        ImmutablePair.right.*/FLOW, NORMAL; excluded mark IDs [74,80]
Result: paired output selector rejects the raw result
```

This is avoidable-looking construction followed by rejection, but no general
removal proof yet exists. A method-entry source can convert DATA to Target/Zero
before final restriction. A root demand with only Target/Zero therefore does
not prove a DATA result useless. Keep the current root/source/control guards.
Any earlier output selector needs a whole-boundary native proof and fallback.

## 8. Stirling: deep images before shallow restriction

Reached run-11; completed run-10; accepted run-9. Incoming handoff rows change
from 1,117 before run-9 to 1,111 before run-11. Target origins change 40 to 39.
These are not increasing global incoming counts. Yet the partial run-11 does
4.22 times as many C5 row operations and takes at least 4.97 times run-9 engine
time. Almost all output budgets remain 1 or 2 despite the higher field limit.

| Work | run-9 complete | run-11 partial |
| --- | ---: | ---: |
| C2 direct queries | 5,060,842 | 19,762,451 |
| C5 row attempts (including control rows) | 37,960,245 | 160,061,504 |
| C5 prepared-program queries | 8,790,224 | 37,087,674 |
| C5 selected packets | 14,757,771 | 62,840,922 |
| Output budget 1 or 2 | 99.869% | 99.975% |
| Fresh ordinary caller deltas | 627 | 553 |

The dominant `EmlProcessingUtils.decodeMimeHeader(String)` actor has 65 live
local input groups, 438 current DATA rows and only 7,107 processed body packets
in run-9. It nevertheless performs 1,316,623 scalar restrictions, 2,590,856 full
observations, 1,648,947 prefix trials and selects 24,154,515 saved records.
The prepared C5 cache records 8,766,404 hits and 477 preparations. Rebuilding
the plan is not the main cost. Most candidate packets are TAINT (82,636 of
90,216); 57,946 have depth 8. New global caller/static/cleanup work is small.

The disjoint all-thread CPU partition separates nested observer work from its
outer saved-replay caller:

| CPU class | run-9, 4,420 samples | run-11, 4,610 samples |
| --- | ---: | ---: |
| Actual saved replay outside pure observer/probe | 36.83% | 23.58% |
| Pure full loop observer | 27.38% | 37.18% |
| Pure negative probe | 1.79% | 3.54% |
| GC | 31.74% | 35.23% |
| Other/JIT | 2.26% | 0.48% |

The source loop uses `matcher.find`, `StringBuilder.append`, regex accessors,
Base64 decoding and `decodeQuotedPrintable`. It has no explicit deep object
writer. Composed model accessors generate the path words. Current accessor
IDs decode as `1096=CharSequence#content`, `1332=String#bytes`,
`1336=String#<string-bytes>`. Mark T91 is the full mark
`java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2`.

```text
Current premise: arg(0).content.$/T91
Dc: arg(0).[any]/T91       Dp: ret.*/T91       output budget: 1

raw1: ret.content.content.content.bytes.bytes.bytes.bytes.[any]/T91,D,plain
raw2: ret.content.content.content.bytes.<string-bytes>.<string-bytes>.bytes.[any]/T91,D,plain
C5(raw1) = C5(raw2) = ret.content.[any]/T91,D,plain

Another selector, Dp=ret.content.$/T91, budget=2:
raw3: ret.content.content.content.bytes.<string-bytes>.content.<string-bytes>.[any]/T91
C5(raw3) = empty
```

The key pipeline is:

```text
completed block -> offer next/repeat block
 -> replay saved summaries FIRST
 -> match/apply each saved relation -> field bound -> loop restriction
    -> raw complete observation
    -> each proper prefix: negative C2 probe, then full observation if needed
    -> saved adjacent composition and enclosing paired C5
 -> completion storage deduplicates the final result
 -> current-demand admission and current summaries
```

Different long paths have the same short C5 image in these samples. That is
not yet a proof that adjacent C2, repeat C2 and all enclosing observations
are equal. Removing them based only on this C5 row would be unsound. The next
design must factor the complete consumer image before enumerating every long
image, with exact equality and a native fallback. Actual saved replay on each
offer remains required even when current demand is empty.

## 9. Thingsboard: OOM owners and exact mark dimensions

Reached run-1; none completed/accepted. A live heap dump runs at
17:54:41.610–17:55:09.449 UTC (27.839 s). MAT finds 300,756,167 reachable objects
using 11,383,228,536 bytes. The 18,527,524,474-byte HPROF is a file size, not a
live-byte count. These top-level class dominator groups are disjoint:

| Owner group | Retained bytes | Share |
| --- | ---: | ---: |
| UnitRunner | 3,912,707,616 | 34.37% |
| SubscriptionManager | 1,627,544,792 | 14.30% |
| IR RAM entity storage | 1,623,874,560 | 14.27% |
| JIRTaintRulesProvider | 794,348,320 | 6.98% |
| JIRMethodEntries | 759,255,096 | 6.67% |
| RunManager | 725,092,608 | 6.37% |

IR storage is measured for attribution; it is not a proposed optimization.
The main immediate actor children include block runtimes 1,436,077,368 B,
method point stores 727,006,008 B, body statistics 538,208,712 B, rule services
218,705,112 B, method summary stores 208,276,144 B, and point-resume state
158,634,104 B. These children must not be added again to their parent totals.
Block entry links include 407,157,952 B of scalar local input directories
(931,888 groups), 166,498,512 B of published DATA maps, 86,462,392 B of Target
indexes and 20,750,456 B of deliveries. Candidate tries are included in the local
input directory total.

The enabled statistics observer is material: 1,974,142 copied bounded samples
retain 434,987,328 B, inside approximately 538 MB of body statistics. These are
measurement objects, not ordinary AP facts. No uninstrumented control was run.
The removed unresolved-call archive is absent: all 82,224 owners have null
archive state.

### Stored memberships and caller representation

| Point/dedup scope census | Count |
| --- | ---: |
| TAINT memberships | 12,017,206 |
| FLOW memberships | 1,364,296 |
| ZERO memberships | 1,027,578 |
| Total | 14,409,080 |
| DEMAND memberships | 12,904,564 |
| LocalVar conclusions | 9,098,030 (63.14%) |
| Static conclusions | 764,258 (5.30%) |
| Static original premises | 3,810,299 (26.44%) |

This counts each of 94,058 stores separately, excluding publication copies
and Target rows. It is not a processed-event count or a global AP set.
Literal protected memberships are 345,527 at points and 89,578 in RunSummaryStore
payloads. Protected/plain memberships stay separate.
The 6,748 PathNode objects are initial/premise interned paths, not all conclusion
paths. No native conclusion-depth distribution was collected.

| Standing caller storage | Count |
| --- | ---: |
| Logical groups | 2,731,925 |
| Packed sources / scalar fallback | 2,247,145 / 484,780 |
| Packed families / cells | 165,998 / 237,754 |
| Diagonal literal mark pairs | 3,164,471 |
| Mark-changing literal pairs | 61,076 |
| Source-to-cell postings | 3,184,239 |
| Decoded snapshots since creation | 17,795,331 |

Diagonal pairs are 98.11% of all stored pairs; mean sources per family are
13.54. CallerInputValues, including packed and scalar fallback authorities, retains
1,334,327,816 B. Source posting maps/sets
account for 568,641,968 B within it; the separate caller candidate trie retains
239,024,720 B. Storage packing still decodes native groups for scalar consumers.
It does not remove repeated mark-level transfer or source-handle work.
Only 17.95% of literal caller originals are static, but a nonstatic input can
come from an upstream static supply. This is not a static causal ablation.

### Static and request owners

The global static service retains 35,658,408 B. Its FLOW writer directory has
840 rows and 791,600 B. Local writer directories have 952 rows. The old huge
writer matrix is not the main retained owner in this snapshot.
The global state has 46 static fields, 5,699 requested FULL-mark memberships,
766 processed, 16 reached-only, and 70,694 pending interest rows.

Committed method requests contain 2,483,841 mark memberships in 30,743 rows
(20,429,312 B); local requests have 647,827 in 8,305 rows (4,816,656 B);
actor temporaries have 280,909 in 3,857 rows (8,279,040 B). Large membership
counts here are not multi-gigabyte request storage.

The main remaining static family is a held FLOW image at a resume site:

```text
callee nonstatic mark request
 -> caller subscription whose ORIGINAL is static
 -> requestStaticGroups(CallStageInput, complete original/image)
 -> needGroups -> Run1PointResume

key = site + original + image base/tail/E/layer + CallResumeState
value = full mark -> immutable FLOW image
```

There are 56,331 point rows and 1,442,910 pending marks. A single root is shared
by all marks in 49,370 rows (87.64%); these rows hold 92.50% of the pending
memberships. TenantId.tenants accounts for 53,063 rows and 1,269,407 memberships.
The largest exact header family has 13,565 points and 714,962 pending marks:

```text
original: C.TenantId.tenants.*/FLOW, empty E
image:    This.[any]/FLOW, DEMAND, empty E
site:     CallStageInput

Representative: RuleChainActorMessageProcessor.onUpdate(TbActorCtx), line 134,
inst 76, stage 3, block 2 / entry 32 (also independently entry 82).
One immutable image root is shared by 221 FULL marks in 13 rule groups.
```

This is not 221 writers or alias targets. Other rows have different images
for different marks and cannot be combined as a Cartesian product. Point maps
retain 139,448,832 B; point-key maps retain 6,642,928 B (field sums can overlap).
PointReady removes supplied memberships before callback and removes an empty
row. A globally processed mark can still have an in-flight local callback;
not every pending membership is a never-written group.

### CPU and partial operation counts

The 42,438-sample run-1 profile assigns each stack once:

| CPU stage | Share |
| --- | ---: |
| GC | 41.270% |
| Transfer/routing | 13.983% |
| Summary storage/subsumption | 12.314% |
| Summary matching/application/delivery | 10.144% |
| Form cache/build/specialization | 6.859% |
| JIT | 4.762% |
| Direct static protocol | 2.194% |
| Ordinary requests | 2.071% |
| Rules/cleaners | 1.906% |
| Packed decode | 1.388% |
| Input merge/encode | 0.801% |
| Other | 2.307% |

The inclusive `FormsCache.withForm` share (35.692%) includes its whole callback;
it is not form-construction CPU. Direct static bookkeeping is small in this
window, but static-origin facts can cause transfer/storage work elsewhere.

After cancellation, counters record 8,025,031 body steps in 71,953 actors,
4,058,862 abstraction input arrivals, 3,531,996 fresh caller deltas,
17,795,341 decoded snapshots, 17,241,377 request mark scans and 14,195,995
cleanup selected steps. These units differ. Partial counter totals and the
slightly earlier live heap need not be equal. The trace shows real retained
work and OOM; it provides no evidence of a semantic infinite loop and no
proof that all these repeated operations are redundant.

## 10. One integration issue reserved for the next iteration

A completed pure probe reuses C2 within its own full observation, as designed.
It does not insert the completed answer in `LoopQueryScratch.admissions`.
Another identical query in the same quantum can repeat C2. The old full-observer
path populated that cache. This is a technical cache-integration issue, not a
finding/layer change. The proposal did not describe insertion explicitly;
no extra runtime fix was added during this campaign.

The complete stream currently loses per-view/query provenance, including
complete empty answers. A repair must retain that provenance and insert only
complete materialized native answers under the old 32-key/128-answer/quantum
policy. Never cache partial/aborted or liveness-skipped queries as empty.
The counters do not measure repeated exact keys, so no saved-call count or
speedup factor can be assigned to this omission yet.

## 11. Evidence, controls and next decision

All bulky data is outside git at
`/drive-testcomp/opentaint-go-rules/work-reduction-20261112/`:

| Evidence | Path under that root |
| --- | --- |
| Runtime/native/Lean binding and test totals | `implementation-validation.json`, `native/integrated-final/receipt.json`, `native/root-final/comparison.json` |
| Rules and actual engine audit | `rules-summary.json`, `rules/manifest.json`, `rules/result/test-result.json` |
| Exact command/config/result per project | `projects/<project>/bidi/{manifest.json,summary.json,analyzer.log,reports/}` |
| Finding and per-run counters | `analysis/OWASP/`, `analysis/conductor/`, `analysis/Stirling-PDF/` |
| Time-sliced form/predicate profiles | `profiles/OWASP/` |
| Thingsboard CPU and partial counts | `analysis/thingsboard/cpu-and-counters.{md,json}` |
| Current heap tables, all controls and hashes | `heap-analysis/thingsboard-run1-key-tables.json`, `heap-analysis/decode-receipt.json` |
| Full heap source binding / exact layout adapters | `heap-tools/binding.json` |
| Cache integration source trace | `native/loop-completed-probe-cache/source-audit.md` |

Old raw snapshots/profiles and indexes were removed after decoded evidence and
absent old processes were checked: 40 files, 41,976,393,433 B. New captures and
MAT indexes remain outside the repository. The Thingsboard heap SHA-256 is
`126ee9667ba5c99c8fb25a60d8bcedf118a5bb08855f95b986be979fad360a6e`.
All final heap queries completed. The adapter was checked against actual
production caller storage (three sources, nine exact changing/diagonal pairs,
primitive key zero, scalar fallback) and native summary census weights/flags.
An initial failed path-view query was corrected and rerun; guessed old store
class names are unavailable, not zero. No old layout was counted as current.

The next work should avoid whole mark-level transfers and complete loop
observations, rather than only accelerate a trie lookup. Exact FULL batching
is the main Thingsboard candidate; complete consumer-plan factoring targets
Conductor/Stirling; form reuse targets OWASP. Each requires the proof and
native parity gates in the next proposal. The present data does not establish
a twofold speedup for any candidate.
