# Demand-relative summary restriction: project results and workload

Date: 1 November 2026. **Status: campaign complete.** All four commands have
ended. No project reported OOM. Three commands reached their time limits.

Measured revision: `86ad3b70b5b834d60bc0fe96a91091174265c827`.
Its analyzer code is identical to implementation commit
`0ffa5ed8b42dbe193973b4fb4701af28b35716b3`.
Mode: FULL. Heap: 16 GiB. Field limits: `1,1,2,3,…`.

OWASP completes **run-5** and retains all 4,112 saved baseline identities.
Its analysis takes 98.882 seconds. Run-1 takes 64.342 seconds and still
exceeds the 60-second engine target. This is one measurement, not a stable
speedup estimate.

Conductor completed **run-5** and timed out in **run-6**. Its run-4 now
finishes in 76.862 seconds; the preceding measured runtime timed out in
run-4 after 1,009.021 seconds. This proves progress past that former limit.
The accepted run-5 report retains all seven baseline findings. Full
analysis still does not converge within the time budget.

Thingsboard reaches run-2 and accepts run-1. Stirling-PDF reaches run-8
and accepts run-7. Their findings are unchanged from the immediate prior
version. Both retain baseline differences described below. The result
does not meet the no-FN goal for all projects.

| Project | Command result | Latest reached / completed / accepted | Command, s | Peak RSS, GiB |
|---|---|---|---:|---:|
| OWASP | OK | run-5 / run-5 / run-5 | 173.284 | 11.419 |
| Conductor | TIMEOUT | run-6 / run-5 / run-5 | 1,122.031 | 18.166 |
| Thingsboard | TIMEOUT | run-2 / run-1 / run-1 | 1,123.155 | 18.549 |
| Stirling-PDF | TIMEOUT | run-8 / run-7 / run-7 | 1,108.204 | 17.835 |

The retained [campaign data](data/bidirectional-demand-relative-campaign-20261101.json)
contains the configurations, source and model hashes, complete location
differences, per-run counters, profile scopes, and capture receipts.

## 1. Change, validation, and comparison

The [selected spec](../../spec/demand-relative-summary-restriction.md) and
[implementation proposal](../design/bidirectional-demand-relative-summary-restriction-implementation-20261101.md)
change summary admission:

```text
Previous selected edge: Dp -> Dc
Current complete row:   entry=Dc, exit=Dp

candidate A -> B
    -> exact paired C5
    -> cut at min(current field limit, FL(that row's Dp)+1)
    -> admitted store
    -> fresh publication
    -> eligible NORMAL record / selected outgoing demand
```

`FL` counts fields and array elements. A static class anchor costs zero.
The gate applies to new NORMAL and DEMAND DATA summaries. A cut produces
MAY/DEMAND. No unrestricted NORMAL fallback remains. This is a selected
semantic change: it can delay a NORMAL record and require more iterations.

The body still uses its global field limit. C2 initial emission, rule and
cleaner transfer, aliases, complete ND originals, source permissions,
typed Targets, and every-offer native replay keep their current rules.
No local widening or previous-point guidance was added.

The [implementation validation](bidirectional-demand-relative-implementation-validation-20261101.md)
records 2,232 common-core tests, 452 JVM tests, 25 further tests with
diagnostics enabled, and 54 Python tests, all passing. The constructive
checker passes 182 theorems and 303 audited declarations and binds the
implementation source. This does not prove full Kotlin correctness,
whole-project equivalence, convergence, or a performance bound.

The fixed finding baseline is `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.
Its saved reports are reused; it was not run again. The immediate
performance comparison is `c4a71246519ee5432879ce82518823f1703f3aa4`, using
the same FULL/16 GiB configuration and project model hashes. Those older
results are comparison evidence, not results for the new code.

## 2. Experiment method

The campaign uses `runProjectAnalyzer` directly:

```text
./gradlew :runProjectAnalyzer --console=plain \
  -I <project>/bidi/benchmark.init.gradle \
  -x :opentaint-ir:go:buildGoServer
```

Static handling and aliases are enabled. Optimization statistics and JFR
are enabled. Form statistics are disabled. The test-input revision is
`bbdbcc5fd35d976d93348760ea60561e4670f68c`. The IFDS budget is 1,000 seconds
for OWASP and 1,080 seconds for each real project. The outer budget is
1,200 seconds. No alternate analyzer configuration or legacy-baseline
rerun is part of this experiment.

Raw files are in `../demand-relative-summary-restriction-20261101`.
Before launch, 15 previous capture files were checked by hash and removed:
849,804,055 bytes. Previous reports, logs, manifests, and the derived
comparison summaries were retained. The saved legacy baseline was untouched.

The first live capture reader could miss an engine-end marker when a
large diagnostic line displaced it from the 64 KiB log tail. OWASP has no
separate end-of-run JFR dumps. Its closed continuous recording contains
all five runs. An external incremental watcher supplies the remaining
end-of-run dumps and records their actual capture times. It does not
change analyzer code or configuration.

Each CPU capture starts after 60 observed engine seconds and requests
30 seconds. A capture can cross into the next run. Such a capture is a
mixed window; it is not assigned wholly to its starting run. The report
uses JFR timestamps and engine markers for the per-run comparison.
Capture commands and their wall cost are separate observer evidence.

After the campaign, the capture harness was fixed to stream complete
control lines with bounded memory and retain completed-run IDs. Six new
parser tests cover large diagnostic lines, split markers and nested
marker text. All 60 campaign/profile Python tests pass. This observer-only
fix was not used to rerun any analyzer measurement. It changes no analyzer
setting. The separate comparison parser's OOM substring heuristic remains;
the authoritative checks below qualify its false diagnostic-symbol hits.

The run-1 joined-completion time is 0.098 seconds for OWASP, 0.550 for
Conductor, 226.906 for Thingsboard and 0.237 for Stirling. The following
table gives the interval from each `BIDI_RUN_END` log marker to the next
run's start. These are observed handoff/report/diagnostic intervals, not
CPU time. Run-1's joined phase is before its END marker and is excluded
from this table; its `engineTime` also excludes that phase.

| Project | After run-1 | After run-2 | After run-3 | After run-4 | After run-5 | After run-6 | After run-7 |
|---|---:|---:|---:|---:|---:|---:|---:|
| OWASP | 1.177 s | 0.114 s | 0.178 s | 0.005 s | — | — | — |
| Conductor | 1.308 s | 0.792 s | 0.501 s | 0.069 s | 0.205 s | — | — |
| Thingsboard | 17.786 s | — | — | — | — | — | — |
| Stirling-PDF | 0.428 s | 0.433 s | 0.354 s | 0.135 s | 0.178 s | 0.177 s | 0.193 s |

## 3. OWASP: run-5 complete and accepted

`Demand` counts explicit normalized handoff rows, including typed control
rows. `Target` is a separate diagnostic which overlaps that population.
Do not add the two as disjoint counts.

| Run | Direction / limit | Engine, s | Outgoing demand | Outgoing Targets | Reports |
|---|---|---:|---:|---:|---:|
| run-1 | Forward / 1 | 64.342 | 9,507 | 6,310 | 3,885 |
| run-2 | Backward / 1 | 23.852 | 10,073 | 1,600 | 3,885 |
| run-3 | Forward / 2 | 8.781 | 158 | 64 | 4,112 |
| run-4 | Backward / 3 | 0.185 | 110 | 36 | 4,112 |
| run-5 | Forward / 4 | 0.129 | 0 | 0 | 4,112 |

The final stop reason is `NO_DEMAND_EDGE`. The latest reached, completed,
and accepted iteration is run-5. All 4,112 baseline identities match;
there are no added or removed identities. The observed command time is
173.284 seconds. The previous same-configuration analysis time was
101.108 seconds, versus 98.882 seconds here. This approximately 2.2%
difference is too small for a stable speedup claim from one run.

### Restriction and remaining body work

These counters count complete-row attempts and packed packets. They do
not count unique scalar facts. One selected packet can produce both a
kept packet and a cut packet.

| Run | DATA row attempts | Selected packets | Above-budget inputs | NORMAL-to-DEMAND output packets |
|---|---:|---:|---:|---:|
| run-2 | 86,769 | 13,714 | 0 | 0 |
| run-3 | 2,170 | 781 | 88 | 87 |
| run-4 | 796 | 62 | 20 | 10 |
| run-5 | 6 | 4 | 0 | 0 |

Run-2 cannot have a relative cut beyond its existing global limit of 1.
The new cuts occur in later runs. The final frontier still becomes empty;
the change does not reproduce the earlier OWASP demand cycle.

The captured cuts are not limited to loop methods. A run-3 sample from
`org.owasp.benchmark.helpers.Thing2.doSomething(String)` has a NORMAL FLOW result
with two fields. Its complete row has `FL(Dp)=0`. C5 keeps the result and
the new limit then emits a one-field MAY/DEMAND result. This helper is
acyclic. A cut count alone cannot establish a loop cause.

Run-5 still processes body packets of depth 4, but retains only four FLOW
summary annotations and no outgoing demand. Thus the gate can remove
summary work without removing the body work already done before C5.
This observation is not evidence of an OWASP workload explosion.

## 4. Conductor: run-6 timeout, run-5 complete and accepted

| Run | Direction / limit | Engine, s | Outgoing demand | Method keys with demand | Targets | Native crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | Forward / 1 | 14.073 | 36,372 | 6,615 | 5,663 | 0 | 2 |
| run-2 | Backward / 1 | 14.692 | 154,144 | 9,366 | 360 | 167,440 | 2 |
| run-3 | Forward / 2 | 14.597 | 22,827 | 683 | 1,560 | 632,967 | 5 |
| run-4 | Backward / 3 | 76.862 | 33,973 | 467 | 33 | 4,678,865 | 5 |
| run-5 | Forward / 4 | 70.007 | 102,890 | 438 | 4,497 | 3,760,179 | 7 |
| run-6 | Backward / 5 | 862.169, timeout | No completed frontier | — | — | — | 7 accepted |

The latest reached run is run-6; the latest completed and accepted run is
run-5. The command takes 1,122.031 seconds. There is no OOM signal. Peak
process RSS is 18.17 GiB; RSS includes native memory outside the 16 GiB
Java heap. The prior run timed out in run-4 and accepted run-3. This patch
advances the analysis and restores findings, but does not make the whole
command finish within budget.

All seven baseline identities match. There are no added or removed
identities against the fixed baseline. Against the immediate c4 report,
the five prior identities remain and two return: the script-evaluation
sink at `ScriptEvaluator.java:253` and the Python-evaluation sink at
`PythonEvaluator.java:63`. This is finding-identity evidence; it is not a
proof of source-to-sink trace equivalence.

### What the restriction removes

Run-4 selects 235,596 packed C5 result packets. Of these, 140,448 exceed
their row budgets. The cut produces 115,198 NORMAL-to-DEMAND callback
packets. Of the 122,404 selected packets with maximum depth 3, only 580
admitted callback packets still have maximum depth 3. These are attempt
populations, not unique retained fact counts.

The previous run-4 profile placed 72.3% of Java samples in current-summary
delivery. In the new complete run-4 phase, delivery is 22.4%. The old phase
was a much longer incomplete run, so these percentages are not equal-time
measurements. Together with the new depth distributions and completed
run-4, they support the explanation that the gate reduces inter-method
feedback. They do not establish that every remaining cost is local.

### Remaining work: calls at loop points

Run-4 processes 8,185,369 scalar packets and admits 5,935,499 fresh post-S
packets. Of these, 82.4% of processed packets and 83.2% of fresh packets
occur at points in cyclic CFG components. Three full method keys account
for 85.2% of processed packets:

| Method in `ParametersUtils`, context `arg(0) == HashMap` | Processed packets | Fresh post-S packets | Summary candidate offers |
|---|---:|---:|---:|
| `replace(Map, DocumentContext, String)` | 3,093,420 | 2,124,157 | 40,425 |
| `replaceList(List, String, DocumentContext)` | 2,424,533 | 1,885,176 | 47,762 |
| `replaceVariables(String, DocumentContext, String, int)` | 1,452,765 | 910,580 | 2,175 |

Their counted packet headers are 89.4% FLOW; 88.6% have maximum
depth 3. These are packet distributions, not a count of all denoted paths.
The Java bodies contain collection loops and recursive calls:

```java
// Reduced display of the actual ParametersUtils source.
Map<String, Object> replace(Map<String, Object> input, Context io, String taskId) {
    Map<String, Object> out = new HashMap<>();
    for (Entry<String, Object> e : input.entrySet()) {
        Object value = e.getValue();
        Object changed;
        if (value instanceof String) changed = replaceVariables(value.toString(), io, taskId);
        else if (value instanceof Map) changed = replace((Map) value, io, taskId);
        else if (value instanceof List) changed = replaceList((List) value, taskId, io);
        else changed = value;
        out.put(e.getKey(), changed);
    }
    return out;
}
Object replaceList(List<?> values, String taskId, Context io) {
    List<Object> out = new LinkedList<>();
    for (Object value : values) {
        if (value instanceof String) out.add(replaceVariables(value.toString(), io, taskId));
        else if (value instanceof Map) out.add(replace((Map) value, io, taskId));
        else if (value instanceof List) out.add(replaceList((List) value, taskId, io));
        else out.add(value);
    }
    return out;
}
```

One actual run-4 C5 sample from `replaceList` is:

```text
I = Iterable#Element
C = CharSequence#<rule-storage>
H = HeaderElementIterator#<rule-storage>

whole original A: ret.I.I.C.* / FLOW
complete Dc:      ret.I.I.[any] / FLOW
complete Dp:      arg(1).[any] / FLOW
budget:          1
candidate branch B: arg(1).H.H.H.[any] / FLOW, DEMAND
exact C5 result:    same branch, maximum FL=3
admitted branch:    arg(1).H.[any] / FLOW, DEMAND
E={}, mx={}; protection=false
```

The whole packet can have other branches. The displayed first branch is
captured data, not a reconstructed parent/creator trace. These accessors
are virtual model payload channels. `arg(1)` is the String `taskId`, but
the field-owner name alone does not prove an impossible Java heap access
or permit its removal. Current backward transfer deliberately drops the
forward type filters and guards. Restoring them requires another semantic
contract and proof.

The profile distinguishes work at loop points from ordinary local transfer:

| Disjoint scope | Complete run-4 Java samples | Closed run-6 CPU window, among stacks with a bidi frame |
|---|---:|---:|
| Direct call processing | 46.61% | 52.97% |
| Saved-summary replay | 23.82% | 28.62% |
| Current-summary delivery | 22.42% | 8.00% |
| Ordinary instruction transfer | 3.15% | 5.00% |
| C5 restriction | 1.63% | 3.49% |
| Other | 2.37% | 1.92% |

The run-4 column uses 2,699 Java samples. The run-6 window contains 21,477
all-thread CPU samples, of which 15,515 have a bidi frame. GC/JIT/native
work is outside the second denominator. These two columns are different
sample populations; do not subtract them as an equal-time CPU comparison.

At run-6 timeout, the joined stopped owners have processed **135,335,334**
steps and offered **1,140,925** summary candidates. There is no completed
run-6 frontier. These counters are not inferred from the prior 438 demand
method keys. They show why a small boundary frontier can still permit a
large body/call workload.

The whole run-6 JFR phase has 99,261 Java samples: direct calls 51.53%,
saved replay 35.52%, current delivery 3.86%, ordinary transfer 3.91%,
C5 2.81%, and other work 2.36%. It estimates 4,490.98 GiB of allocated
bytes and 15.252 seconds of GC pauses. These bytes are sampled cumulative
allocation, not simultaneously retained heap. This longer phase confirms
the call/replay pattern seen in the separate CPU window.

The supported conclusion is that call processing and replay dominate the
remaining run. A cyclic CFG point does not identify the operation which
created a path. Local reversed reads, recursive summary composition, and
aliases can all supply feedback. The captured row proves late collapse;
it does not, by itself, prove which of those routes created `H.H.H`.

## 5. Thingsboard: run-2 timeout, run-1 complete and accepted

| Phase | Current, s | Immediate prior, s |
|---|---:|---:|
| Prescan | 121.653 | 140.238 |
| run-1 engine, limit 1 | 393.147 | 437.728 |
| Joined static writer completion | 226.906 | 225.956 |
| run-2 engine, limit 1 | 317.712, timeout | 254.776, timeout |

The current run-1 starts at 18:47:07.223 UTC. Its report barrier ends at
18:57:45.062 UTC: 637.839 seconds including engine, joined completion,
and other handoff work. The prior complete interval was 681.958 seconds.
The larger run-2 time is remaining-budget exposure, not an equal-window
throughput regression. Neither version completes run-2.

Run-1 emits 4,621,396 outgoing demand rows in 30,211 method keys, with
2,714,707 Target demands and 13 reports. The prior count was 4,621,432,
with the same Target count and report identities. Run-1 processes
14,892,455 body packets and admits 19,316,690 fresh post-S packets.
There is no completed run-2 frontier. After worker join at timeout,
20,478 stopped actors report 4,227,689 steps and 486,431 summary offers.
The ordinary incomplete result exports no actors; its zero snapshot count
must not be read as zero work.

### The dominant run-2 work is a query graph

| Run-2 operation | Count |
|---|---:|
| DATA complete-row C5 attempts | 187,754,710 |
| Exact C5 rejections | 187,192,289 |
| Selected C5 packets | 562,421 |
| Control-route DATA rows, explicit and derived together | 187,455,760 |
| Above-budget packets / NORMAL-to-DEMAND cuts | 0 / 0 |
| Static graph composition attempts and accepted compositions | 1,491,475,747 |
| Duplicate graph-state admissions | 1,455,563,087 |

Exact C5 rejects 99.7004% of attempted DATA rows. The static control
route supplies 99.8408% of DATA row attempts. Both run-2 limits are one,
so the new relative cap cannot reduce them further. This is a large
auxiliary search workload at a small field limit.

The pure run-2 JFR phase has 148,090 Java samples. C5 accounts for
96.51%; direct calls account for 2.25%. More precise stack checks put
94.49% in `walkTargetOrigins` below `retainSummary`, outside
`acceptsTarget`. There are no `acceptsTarget` samples in this phase.
The search starts from terminal inputs and walks static predecessors
before the provided raw output selects the resulting origin. Each query
has a new visited set. Thus it repeatedly constructs origins which the
provided output cannot use. Caching the final `acceptsTarget` boolean
alone would leave this main path intact.

The outer search stack cannot distinguish ZERO-to-DATA from ZERO-to-Reach
candidates. The profile establishes the shared search cost; it does not
prove which raw kind starts most searches. The confirmed DATA callback
subset occupies 4.18% of Java samples. A fix must cover both raw kinds.

### Actual rejected rows

All 64 retained row samples have a ZERO matching member, route 2, and
null selected/admitted outputs. In 62 samples, the entire raw packet's
base differs from Dp's base. This is a definite whole-packet rejection:
all leaves in one packet have that same base. The two same-base samples
remain unclassified because a displayed branch/mark list is incomplete.

| Actual Dp, all at budget 1 | Raw first branch / packet header / shown marks | Sufficient rejection |
|---|---|---|
| `arg(7).*/mark123` | `arg(1).[any]/mark64`, DEMAND | Different argument base |
| `S.TbMsgCallback.EMPTY.*/mark71` | `arg(7).<field68664>.[any]/mark85`, DEMAND | Static versus argument |
| `S.__spring_registry__.EventService.*/mark92` | `this.<field51632>.[any-taint]/mark92`, NORMAL | Static versus receiver, even with the shown same mark |
| `arg(2).*/mark113` | `this.<field51632>.[any-taint]/mark102`, NORMAL | Argument versus receiver |
| `S.TbCallback.EMPTY.*/mark100` | `this.<field51632>.[any-taint]/mark96`, NORMAL | Static versus receiver |

These are process-local mark/accessor IDs. The two unresolved field IDs
stay unresolved. The sampler's first branch is not its full packed tree.
The 62/64 share is not a statistical estimate for all 187 million rows.
All 64 verbatim rows and available dictionary names are embedded in
[the row evidence](data/bidirectional-demand-relative-thingsboard-rows-20261101.json).

Typed Target/Zero entries use an AP ZERO adapter for exact DATA C5. The
sample string does not retain typed-entry or local/derived provenance.
Do not label a particular sampled row as derived solely from that string.
The source path and profile independently establish that the derived
terminal-origin traversal is expensive.

### The run-1 handoff is another large, separate phase

Joined completion processes 2,351,008 unique writer rows from 26,402,673
writer offers. It visits **222,460,912** candidate inputs, matches
28,027,977, and produces 27,927,716 bound output callbacks. Writer binding
alone takes 220.565 seconds of the 226.906-second joined phase.

The inventory observes 2,700,170 primitive candidate memberships and
467,941 lost candidate memberships. Lost writes remain needed for
guidance when an exit effect removes a result. Pool supply at the write
and caller-to-static demand guidance are separate operations.

The existing input-key duplicate counter is zero. Its key includes call
instruction and stage. It therefore does not establish that all inputs
produce different guide bindings. Sharing exact equal guide inputs across
call sites is a candidate, but its useful quotient size is not measured.
Do not promise a large saving before that measurement.

## 6. Stirling-PDF: run-8 timeout, run-7 complete and accepted

| Run | Direction / limit | Engine, s | Outgoing demand | Method keys | Targets | Native crossings | Reports |
|---|---|---:|---:|---:|---:|---:|---:|
| run-1 | Forward / 1 | 12.263 | 23,973 | 1,904 | 2,887 | 0 | 7 |
| run-2 | Backward / 1 | 6.499 | 115,128 | 4,205 | 344 | 12,972 | 7 |
| run-3 | Forward / 2 | 3.943 | 48,022 | 3,691 | 96 | 42,507 | 21 |
| run-4 | Backward / 3 | 4.695 | 26,171 | 3,673 | 80 | 146,816 | 21 |
| run-5 | Forward / 4 | 3.547 | 9,677 | 3,582 | 67 | 240,659 | 22 |
| run-6 | Backward / 5 | 312.734 | 7,393 | 3,582 | 52 | 2,788,136 | 22 |
| run-7 | Forward / 6 | 2.733 | 12,673 | 3,582 | 71 | 411,397 | 22 |
| run-8 | Backward / 7 | 716.631, timeout | No completed frontier | — | — | — | 22 accepted |

The prior run-6 took 312.047 seconds and run-8 timed out after 716.925
seconds. These differences are small. The patch does not reduce the
dominant backward workload in this project.

Run-6 processes 7,358,355 body packets and admits 7,024,419 fresh post-S
packets, while offering 59,304 summary candidates. Cyclic CFG points
account for 6,734,000 processed and 6,684,408 fresh packets. Two full keys
in `AdminSettingsController` dominate:

| Method | Processed | Fresh post-S | Summary offers |
|---|---:|---:|---:|
| `updateSettings(UpdateSettingsRequest)` | 4,490,227 | 4,296,884 | 8 |
| `updateSettingsSection(String, Map)` | 2,485,164 | 2,427,661 | 48,955 |
| `PdfAttachmentHandler.processInlineImages(String, EmailContent)` | 223,218 | 169,616 | 433 |

The two controller keys mainly carry protected TAINT packets. At run-8
timeout they process 5,633,084 and 5,633,102 packets respectively. The
inline-image method processes 3,317,245, mainly FLOW packets. The three
keys together account for 98.8% of 14,758,657 stopped-owner steps. Many
packets have depth equal to the current body limit, 5 or 7.

The captured paths contain repeated virtual model fields. For example,
one run-8 protected TAINT branch is
`[2044,2044,2048,2048,2044,1084,2036].[any]/mark89`, under original ZERO.
This is a captured path, not a proved creator chain. Point cycles can
combine local operations, aliases, and call results. The observation
does not permit deleting protected edges or imposing a local cut without
a new semantic design.

Run-6 C5 selects 23,720 packets and cuts 1,107 above-budget inputs;
873 callback packets change NORMAL to DEMAND. Run-8 selects 34,347 and
cuts 4,442, with 3,418 NORMAL-to-DEMAND outputs. These cuts happen after
the expensive call/body work. They do not control the full local state.

| Pure JFR scope | run-6, 17,169 Java samples | run-8, 38,870 Java samples |
|---|---:|---:|
| Direct call processing | 80.98% | 84.58% |
| Saved-summary replay | 15.40% | 11.92% |
| Ordinary instruction transfer | 2.92% | 2.96% |
| Current-summary delivery | 0.04% | 0.02% |
| C5 | 0.02% | 0.01% |

Protection transport and AP field cuts occur inside these call scopes;
do not add their inclusive percentages as separate costs. Run-6 has
956.21 GiB sampled allocation and 4.349 seconds of GC pause. Run-8 has
2,176.96 GiB and 15.706 seconds. The result supports removing redundant
call continuations, while checking whether most expensive continuations
actually have different keys. It does not support another C5-only fix
for Stirling.

## 7. Finding comparison and remaining quality gaps

| Project | Fixed baseline | Same identities | Missing identities | Added identities | Change from c4 |
|---|---:|---:|---:|---:|---|
| OWASP, accepted run-5 | 4,112 | 4,112 | 0 | 0 | None |
| Conductor, accepted run-5 | 7 | 7 | 0 | 0 | Two recovered |
| Thingsboard, accepted run-1 | 14 | 13 | 1 | 0 | None |
| Stirling-PDF, accepted run-7 | 17 | 14 | 3 | 8 | None |

The comparison uses rule ID, sink fingerprint, and method signature.
Complete locations and raw comparison records are in the campaign data.
A changed return anchor is not automatically the same trace.
The [quality review data](data/bidirectional-demand-relative-quality-review-20261101.json)
also embeds selected legacy/current SARIF results, complete selected
trace locations, source excerpts and the current guide counts.

Thingsboard misses `ReflectionUtils.java:27`, `Class.forName(targetType)`.
The input is dynamic before validation. It is not dismissed as a
constant-only baseline artifact. The accepted report is still run-1,
and the driver never completes run-2. This establishes a pre-existing
coverage gap in an incomplete time-budget-limited analysis, but does not prove that a later completed run
would recover this exact finding. There is no new missing identity from
this patch; the exact permission/trace cause remains open.

The saved legacy result has two controller-to-sink paths through
`RuleChainMetaData.nodes`, `RuleNode.type`, and either
`RuleChainDataValidator.validateRuleNode` or
`BaseRuleChainService.setSingletonMode`. The current run-1 guide map has
1 row for ReflectionUtils, 37 for validateRuleNode, and 21 for
setSingletonMode in their default contexts. These totals do not identify
the exact mark/Target pair on the missing path.

Stirling misses the command sink at `ProcessExecutor.java:183`,
`new ProcessBuilder(command)`. Its caller can build a dynamic command
list from request data. It remains a real coverage question, not a proved
constant-only FP. Its method still has demand guidance in accepted
run-7. That fact alone does not prove eventual recovery or identify the
missing source permission.

The legacy command trace carries a request URL through `List.add` to the
command's ARGS mark. The source adds that URL, then `--pdf-forms`, then
a temporary output path. The current source model can install an
unconditional output reset for a conditionally assigning source. A later
bound `add` can therefore remove an accumulated ARGS mark without a
replacement, while the legacy caller-local unresolved route can bypass
that bound receiver reset. This is an identified differential transfer
mechanism, already present before this patch. The campaign does not
record the actual ARGS/action lineage at those calls, so it does not
prove this was the unique first loss on this project path. After run-7,
the `(List,File)` overload has 5 guide rows in the exact-ArrayList context,
3 in the subtype-ArrayList context, and 4 in the default context.

The other two missing Stirling identities are controller exits. New
identities occur in the same methods at later returns:

| Controller | Baseline return line | Current return line |
|---|---:|---:|
| `ConvertEmlToPDF.convertEmlToPdf` | 133 | 148 |
| `PipelineController.handleData` | 90 | 130 |

The current Simple exporter follows `vulnerabilityLocation` to
`statementLocation`, then `tryResolveNormalGeneratedLocation` and
`tryResolveExitLocation`. Without a real return witness in its thread
flow, the latter selects the final `JIRReturnInst`. The saved current
locations match those exact final returns. This identifies an exporter
location/fingerprint defect; it does not prove equivalence of the old
and current internal branch witnesses.
The eight additions comprise these two, four `FilterController` return
anchors at lines 107, 146, 175 and 210, and `WebResponseUtils` anchors
at lines 42 and 58. All eight have no SARIF code flow. In particular,
a displayed `return null` is not evidence that the original internal
sink witness was null. Do not classify these additions as valid or false
without resolved traces. The new iteration has not changed this set.

Thus OWASP and Conductor meet the identity comparison. Thingsboard and
Stirling do not yet meet the full baseline quality gate. There is no
new measured finding loss against c4, but this is not a no-FN claim for
the complete analyzer.

## 8. Memory and observation limits

No MemoryManager OOM or JVM OOM occurred. No new heap dump was produced.
Consequently there is no fresh retained-heap dominator analysis for this
campaign. The largest RSS is Thingsboard's 18.55 GiB. A 16 GiB heap plus
native, code, JFR, thread and mapped-file memory can exceed 16 GiB RSS.

| Phase | Sampled cumulative allocation, GiB | GC pause, s | GC user CPU, s |
|---|---:|---:|---:|
| Conductor run-6 | 4,490.98 | 15.252 | 213.02 |
| Thingsboard run-2 | 1,915.63 | 9.191 | 126.11 |
| Stirling run-6 | 956.21 | 4.349 | 62.57 |
| Stirling run-8 | 2,176.96 | 15.706 | 219.57 |

Sampled allocation measures churn. These multi-terabyte totals are not
live heap measurements and do not prove a leak. GC pause is elapsed pause
time; GC user CPU sums parallel work. Profile percentages refer to Java
samples in the stated phase, not all process CPU.

Some diagnostic method lists contain the class name `OutOfMemoryError`.
A substring match is not an OOM event. The campaign data records these
false parser signals separately from authoritative exits, memory-manager
events, and heap files. They do not change TIMEOUT to OOM.

Run-1 engine times are 64.342 seconds for OWASP, 14.073 for Conductor,
393.147 for Thingsboard and 12.263 for Stirling. OWASP and Thingsboard
still miss the 60-second target. Thingsboard also has a separate large
handoff. This experiment cannot establish an unbounded-memory claim or
general termination from the absence of OOM within these time limits.

## 9. Reduced production controls and what they establish

The completed run-1 summary census separates concrete memberships from
FLOW annotations. Neither is a count of scalar packets processed:

| Project, run-1 | Admitted concrete | Admitted protected | Admitted FLOW | Outgoing concrete | Outgoing protected | Outgoing FLOW |
|---|---:|---:|---:|---:|---:|---:|
| OWASP | 110,595 | 444 | 11,229 | 2,074 | 231 | 1,123 |
| Conductor | 17,209 | 22 | 36,490 | 14,385 | 20 | 16,403 |
| Thingsboard | 1,800,687 | 1,737,145 | 216,203 | 1,779,161 | 1,737,144 | 138,250 |
| Stirling-PDF | 24,528 | 2,273 | 4,870 | 19,044 | 2,271 | 2,055 |

Protected membership is a flag population. It does not mean that a
corresponding FLOW provider actually exists. This census cannot split
protected rows into “covered except for flag” and “not geometrically
covered.” The bounded project samples also do not enumerate every
relevant FLOW provider. No new whole-project subsumption-reason total
is claimed. The portable data includes the actual census and samples.

Production `FlowBackedSummaryStoreTest` supplies exact provider controls:

```text
All edges below are DEMAND; the full input geometry is x.*.

Provider: x.*/FLOW -> y.[any]/FLOW
Marked:   x.*/T    -> y.f.[any]/T, unprotected
Result: FLOW covers it; marked summary is absent, in both arrival orders.

Same provider and marked row, now protected:
Result: marked guidance is restored; FLOW and protected T both remain.

Only provider: x.*/FLOW -> y.f.[any]/FLOW
Marked outputs under x.*/T: y.f.[any]/T, y.g.[any]/T, y.f.[any]/U
Result: remove f/T; keep g/T (no covered path) and f/U (cross-mark relation).

Provider: x.*/FLOW -> y.[any]/FLOW
Marked:   x.*/T    -> y.$/T
Result: tail mismatch; keep the marked exact fallback.
```

These are controlled provider sets, not reconstructed Thingsboard edges.
They explain why geometric/flag distinctions matter without inventing a
FLOW provider for an actual captured protected project row.

Seven committed controls passed after the campaign. Their full stdout
and XML receipt are in the campaign data. They use production AP/call/actor
operations. They do not substitute for a project run.

| Control | Observed result | Interpretation |
|---|---|---|
| Backward field loop, limits 1/3/5/7 | 21/81/321/1,281 processed; 15/63/255/1,023 point leaves; three admitted summary leaves at every limit | A bounded summary relation does not bound the body relation |
| Forward version, limits 2/4/6 | 17 processed at each limit | The tested forward transfer does not generate the reversed path language |
| 64 reverse aliases | 65 finishes, two fresh stored leaves; 64 equal x continuations | Dedup after S does not remove work before that boundary |
| Forward identity with aliases | One finish at every width | Existing identity/alias guard explains this directional difference in this control |
| Two reversed saved record views | Two replay/suffix callbacks, one stored leaf | Per-stage dedup alone cannot merge separate replay invocations |
| Shallow summary/suffix product | 12 application-path attempts, four distinct paths, depth two | Shallow summaries still permit application products; not 12 distinct caller keys |
| Ancestor/child application | Broad covers child, yet child is fresh; ANY root versus STAR child images | Geometric coverage alone does not establish equivalent continuations |

An additional [captured Conductor control](data/bidirectional-demand-relative-captured-conductor-control-20261101.json)
uses copied serialized model actions, production engine/actors, C2, C5 and
pub/sub under the fixture scheduler. It supplies a shallow sink seed and
a root source rule, with no predefined deep summary.
Its loop creates the actual family
`arg(1).S.H.V.*/FLOW, NORMAL`, then admits
`arg(1).S.[any]/FLOW, DEMAND`, at budget one. `S` and `H` are the captured
StrTokenizer and HeaderElementIterator payload fields; `V` is MapValue.
The test observes `x.H.V` before the call and `x.S.H.V` at its backward
successor. The S model step supplies the extra S prefix in this control.

The loop-only control records 402 unique processed edge observations
with one subscription. Adding recursive calls gives 2,191 with 163
subscriptions. The recursion-only case has an acyclic local CFG and 79
unique processed edge observations with maximum depth two. These set
counts differ from the campaign's processed packet-event counters.
These are reduced untyped IR controls, not real-JIR replays. They prove
that this production mechanism can create the late-cut family; they do
not prove unique creator provenance for each captured project branch.
The embedded source, YAML, extractor and execution receipt make this
result reviewable without an external experiment directory.

## 10. Design conclusions and next iteration

The output gate improves Conductor's inter-method feedback enough to
complete the former slow run. It does not remove all inter-method work:
application products, saved replay and current delivery still exist.
Nor does it bound distinct originals, marks, method keys or local paths.
The statement “only intra-procedural explosion remains” is not established.

The strongest next target is **select relevant terminal origins before
static demand search**, including the ZERO/Reach case. It can avoid a
large family of graph operations which the raw output cannot use.
The second target is **merge equal call-stage results before their shared
suffix**, with protection OR and complete continuation keys. Its measured
local opportunity is 64 equal continuations to one. Project duplicate
ratios must determine its actual impact. **Share equal joined writer
inputs** is third and conditional on a useful measured quotient.

The [next-iteration proposal](../design/bidirectional-demand-relative-workload-next-iteration-20261101.md)
states current/new behavior, code and facts, proof obligations, and
acceptance measurements. These candidates are not implemented in this
iteration. New local widening or previous-point restriction would change
semantics and needs a separate selected design and proof.
