# Loop demand tries and local summary delivery: performance report

4 November 2026. Measured analyzer:
`52f32dd437d438aec4a700a02c18d94c31d58093`.

The [selected implementation](../design/bidirectional-loop-propagation-demand-trie-implementation-20261104.md)
is complete and committed. All four main commands have ended. OWASP completes
run-5. Conductor times out in run-6. Thingsboard times out in run-1 static
completion. Stirling-PDF completes run-8 and times out in run-9. No main
command fails with OOM.

The largest measured improvement is Stirling forward run-7: **507.119 s →
221.182 s**, or 2.29 times faster. Conductor forward run-5 improves from
232.558 s to 130.704 s. Conductor backward run-4 changes little. Remaining
work comes from repeated summary applications and complete loop observations,
not only rejected prefix trials. Thingsboard has a separate large join
between static writer relations and retained caller/block inputs.

These are version outcomes under the same configuration. Incoming frontiers
can differ. They are not isolated measurements of one operation.

## 1. Scope, validation and evidence

The patch adds a frozen demand trie, accepted C5 output programs, ordered
scalar selection, and certified rejection of early prefix budgets. It selects
local standing inputs before native matching, shares complete matches, selects
saved output positions before reverse mark enumeration, and prepares DATA
routes before publication. Unsupported cells retain native fallbacks.

No analyzer semantic change was selected. The contract still includes complete
premises, physical ports, layers, field/mark exclusions, protection, requests,
Targets, actual transfer effects and ordered outputs.

All **2,474 common tests** and **461 JVM tests** pass: 2,935 tests, no failures
or skips. The runner build passes. Validation takes 2 min 47 s. Three
constructive Lean packages pass: **111 theorems and 213 audited declarations**.
These finite models do not verify the Kotlin implementation. The
[validation receipt](data/bidirectional-loop-demand-trie-validation-20261104.json)
pins sources, native controls, runner, models and cleanup.

The four main configurations use `runProjectAnalyzer`, FULL marks, a 16 GiB
heap, field limits `1,1,2,...`, statics enabled and aliases enabled. The IFDS
timeout is 1,000 s for OWASP and 1,080 s for the other projects. Outer timeout:
1,200 s. No other analysis configuration was tested. The fixed quality baseline
is saved `f945f92c5ae554ff4f5fc7696ee5a269210478bb`; it was not rerun.

The performance control is the saved
[`e558b496a` campaign](bidirectional-joined-state-loop-consumers-packed-guidance-performance-20261103.md).
Runtime remains at `52f32dd`. Previous raw captures were hashed and removed:
33 files, 1,591,472,819 bytes. Existing reports and user files were preserved.

Portable data, with full representative facts and provenance:

- [Finding identities and comparisons](data/bidirectional-loop-demand-trie-20261104-quality.json).
- [Selected native counters and configuration](data/bidirectional-loop-demand-trie-20261104-workload.json).
- [CPU/allocation profiles and denominators](data/bidirectional-loop-demand-trie-20261104-profiles.json).
- [GC, RSS and warnings](data/bidirectional-loop-demand-trie-20261104-memory.json).
- [Per-run process CPU and all-thread CPU captures](data/bidirectional-loop-demand-trie-20261104-cpu-memory.json).
- [Exact Conductor trace examples](data/bidirectional-loop-demand-trie-20261104-conductor-trace.json).
- [Actual Thingsboard binding outputs and diagnostic limits](data/bidirectional-loop-demand-trie-binding-jdi-20261104.json).
- [Source analysis and OWASP frontier differences](data/bidirectional-loop-demand-trie-20261104-source-analysis.json).
- [Campaign, reader sources, controls and artifact hashes](data/bidirectional-loop-demand-trie-20261104-provenance.json).

The main campaign uses aggregate diagnostics, with exact fact tracing disabled.
Bounded diagnostics are separate runs and supply no normal performance timings.

## 2. Outcomes and finding quality

Latest labels mean **reached / completed / accepted forward report**.

| Project | Latest labels | Outcome; command wall time | Strict finding identities |
| --- | --- | --- | --- |
| OWASP | run-5 / run-5 / run-5 | Complete; 194.300 s | All 4,112 baseline identities; no additions |
| Conductor | run-6 / run-5 / run-5 | Timeout; 1,122.952 s | All 7 baseline identities; no additions |
| Thingsboard | run-1 / none / none | Timeout; 1,113.524 s | No accepted report; quality is censored |
| Stirling-PDF | run-9 / run-8 / run-7 | Timeout; 1,108.416 s | 22 identities; 3 missing and 8 added against f945 |

OWASP and Conductor also match saved 86ad, 050b and e558 identities exactly.
Stirling matches their 22 identities. Its three fixed-baseline gaps predate
this patch. Thingsboard exports zero identities, as in 050b/e558. This does
not establish no FN: run-1 never commits a report. The 14 fixed-baseline and
13 86ad identities absent from this timeout are censored observations.

The strict fixed-baseline quality gate **does not pass for all projects**.
Equality to the latest performance control does not replace this gate.

### Existing Stirling gaps

| Missing f945 identity | Evidence and limit |
| --- | --- |
| `PipelineController.handleData`, XSS return | The old identity names a branch return; the current identity names the representative final JIR return. This explains the location change, but does not prove the old branch witness remains. |
| `ConvertEmlToPDF.convertEmlToPdf`, XSS return | Same branch-return versus final-return difference. The exact old location is absent. |
| `ProcessExecutor.runCommandWithOutputHandling`, command sink, line 183 | Native reproduction and actual lowered calls show a receiver-state discontinuity: unresolved `add(URL)` transfers ARGS, then `add("--pdf-forms")` clears the receiver even when its source guard is false. The complete first-loss path for this finding is not captured. |

All missing/added fingerprints, signatures and sink locations are in the
finding data. The earlier [receiver-reset investigation](bidirectional-stirling-command-receiver-reset-20261103.md)
contains the native control. No unselected Spring, rule, receiver or report
location fix is included in this patch.

## 3. Iteration times and demand frontiers

The logger uses `engine time = elapsed RunManager call - static binding time`.
Joined seal/release is a separate aggregate inside the logged work; do not
subtract it again. A partial timeout interval has no completed frontier and
does not establish a whole-iteration speed ratio.

### OWASP — complete through run-5

| Run | Direction / limit | Engine s | e558 engine s | Barrier s | Demand | Target demand | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | 76.105 | 77.437 | 2.052 | 162,368 | 14,087 | 3,227 |
| run-2 | BACKWARD / 1 | 26.954 | 26.994 | 0.182 | 27,419 | 2,463 | 3,227 |
| run-3 | FORWARD / 2 | 14.700 | 16.603 | 0.251 | 176 | 80 | 4,112 |
| run-4 | BACKWARD / 3 | 0.497 | 0.289 | 0.001 | 135 | 42 | 4,112 |
| run-5 | FORWARD / 4 | 0.160 | 0.574 | 0.023 | 0 | 0 | 4,112 |

Stop reason: `NO_DEMAND_EDGE`. Run-1 static binding takes 0.419 s; joined
seal/release takes 0.191 s. Run-1 engine time still exceeds 60 s.

Run-1 gains two explicit demand rows overall. `BenchmarkTest00100` gains six
(38 → 44); `BenchmarkTest00105` loses four (26 → 22). The same 4,446 method
keys remain. Run-2 has six offsetting per-method changes and the same total.
Run-3–5 method/count maps match exactly. Counts are successful normalized
insertions, not callbacks. The affected run-1 methods are absent from retained
exact-row samples, so the cause is unproved. Equal findings do not prove
equal internal demand.

### Conductor — run-6 timeout, run-5 accepted

| Run | Direction / limit | Engine s | e558 engine s | Demand | Target demand | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | 15.024 | 14.834 | 120,070 | 7,896 | 2 |
| run-2 | BACKWARD / 1 | 22.793 | 22.188 | 238,762 | 404 | 2 |
| run-3 | FORWARD / 2 | 26.052 | 33.947 | 46,632 | 4,225 | 5 |
| run-4 | BACKWARD / 3 | 277.610 | 281.981 | 130,791 | 39 | 5 |
| run-5 | FORWARD / 4 | 130.704 | 232.558 | 220,052 | 9,062 | 7 |
| run-6 | BACKWARD / 5 | 578.659, partial | 463.287, partial | unavailable | unavailable | 7 retained |

Run-5 is 43.8% faster in this pair. Run-4 improves by 1.55%. Run-6 has a
longer partial interval because earlier savings leave more budget. It is not
evidence of a 24.9% run-6 slowdown.

### Thingsboard — run-1 does not commit

| Stage | Current s | e558 s | Meaning |
| --- | ---: | ---: | --- |
| run-1 engine residual | 678.522 | 686.278 | About 1.13% lower |
| run-1 static binding | 259.298, partial | 240.471, partial | Deadline-truncated; no throughput ratio |
| run-1 joined seal/release | 0.788 | See control | Aggregate, not an extra subtraction |

The aborted body census observes **73,668 actors, 19,185,001 processed packet
events and 12,197,145 candidate offers**. The later post-release zero snapshot
is unavailable work, not zero work. Likewise `no-completed-binding` means
final writer/prune/freeze counts are unavailable; their printed zeros do not
describe an empty static stage.

### Stirling-PDF — run-8 completes, run-9 times out

| Run | Direction / limit | Engine s | e558 engine s | Demand | Target demand | Reports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD / 1 | 17.494 | 18.150 | 74,445 | 5,400 | 7 |
| run-2 | BACKWARD / 1 | 13.598 | 13.677 | 274,935 | 469 | 7 |
| run-3 | FORWARD / 2 | 5.252 | 4.590 | 1,436 | 137 | 21 |
| run-4 | BACKWARD / 3 | 3.199 | 4.431 | 3,155 | 102 | 21 |
| run-5 | FORWARD / 4 | 7.209 | 13.002 | 1,957 | 105 | 22 |
| run-6 | BACKWARD / 5 | 43.479 | 58.166 | 8,792 | 79 | 22 |
| run-7 | FORWARD / 6 | 221.182 | 507.119 | 4,346 | 103 | 22 |
| run-8 | BACKWARD / 7 | 260.877 | 444.341, partial | 18,971 | 84 | 22 |
| run-9 | FORWARD / 8 | 489.862, partial | not reached | unavailable | unavailable | 22 retained |

Run-6 improves by 25.25%; run-7 by 56.39%. Run-8 completes where the control
times out. Full-versus-partial time does not establish equal-work speedup.
The accepted report remains run-7. Run-9 has no committed frontier.

## 4. Remaining CPU and allocation work

The final classifier is `loop-demand-trie-20261104-v4-real-call-domains`, with
50 passing synthetic controls and source pins. Each exclusive stage counts
a Java stack once. The observer union also includes observer-side selection
outside the main frame; it can differ slightly from one disjoint scope row.
Allocation weights measure sampled churn, not retained bytes.

Continuous JFR is rolling and omits some early events. Its event envelope
does not prove complete phase coverage. Do not sum overlapping run, late-window
and IFDS profiles. All-thread CPU captures have a separate denominator.

| Phase | Java samples | Loop-observer share | Main exclusive stages, as share of all Java samples |
| --- | ---: | ---: | --- |
| Conductor run-4 | 6,508 | 44.91% | C2 22.97%; local delivery 14.94%; other observer 11.43%; prefix search 7.39% |
| Conductor run-5 | 11,578 | 60.87% | C5 selection/bookkeeping 17.32%; C5 preparation/lookup 16.84% |
| Conductor run-6, partial | 52,587 | 72.72% | C2 17.86%; C5 selection/bookkeeping 11.28%; C5 preparation 9.22%; other observer 7.38% |
| Stirling run-6 | 1,364 | 40.91% | Real-call resume 22.07%; real-call field cut 12.17%; call cleanup 5.79% |
| Stirling run-7 | 8,027 | 82.90% | Observer reverse AP 11.90%; C2 10.94%; direct AP 10.60%; saved positions 8.42% |
| Stirling run-8 | 7,369 | 45.98% | Real-call resume 18.05%; real-call field cut 14.87%; C2 7.38%; result union 6.92% |
| Stirling run-9, partial | 21,462 | 85.48% | Observer reverse AP 14.65%; C2 12.74%; direct AP 10.78%; saved positions 10.45% |

The issue is **not backward-only**. Forward runs 7 and 9 also perform large
numbers of observations. A small frontier bounds admitted results, not all
input/output pairs, suffix grafts, call contexts or consumer checks.

Conductor run-6 spends 67.24% of observer Java samples in raw baseline checks,
29.19% in candidate checks, and 3.57% unattributed within that distinction.
The latter includes certificate-call-site stacks. Within the observer union,
C5 is 46.26% and C2 is 24.56%.

Its run-6 sampled allocation weight is 2.735 TB. Sites include field cuts
(7.60%), trie leaf iteration (6.19%), node construction (3.23%), node equality
(2.98%) and AP path construction (2.97%). Temporary structure work is large.
It does not imply a 2.735 TB live heap. Prepared-program array allocation is
not a dominant site; removing that array cannot be claimed as the solution.

Stirling run-9 has 1.456 TB sampled allocation weight: field cuts 9.15%, trie
leaf iteration 6.19%, node equality 4.41%, AP paths 3.90%, saved selection
3.64%. Avoiding an empty observer application removes downstream work across
several sites, if its empty-output proof is valid.

### Thingsboard has two different joins

The retained run-1 engine has 73,381 Java samples. Exclusive stages include
real-call residual input work (9.17%), subscription matching (8.59%), delivery
matching (6.15%), call resume (6.01%), subscription field cuts (5.68%), delivery
AP (4.71%) and subscription AP (4.69%). The explicit `other/other` remainder
is **25.40%**; it is not assigned to statics. In the last 30 engine seconds,
`SubscriptionManager.subscribe` is inclusive in 88.68% of 645 Java samples.
Inclusive percentages overlap.

The reconstructed static-completion window has 18,225 Java samples.
**98.24%** fall in joined writer binding:

| Exclusive stage | Java samples | All-Java share | Allocation weight |
| --- | ---: | ---: | ---: |
| Input matching | 8,138 | 44.65% | About 441 GB; 60.68% |
| Input selection/scan | 4,665 | 25.60% | About 106 GB; 14.57% |
| Native summary application | 3,525 | 19.34% | About 92 GB; 12.61% |
| Field limit | 1,426 | 7.82% | About 62 GB; 8.56% |
| All other stages | 471 | 2.58% | Remainder |

The start is reconstructed from a duration and post-close marker, not an exact
native substage marker. Stacks directly identify selection and matching;
the unavailable final counters do not prevent this attribution.

## 5. Conductor: trace the application product

`ParametersUtils.replace` and `replaceList` rebuild nested containers and
call each other recursively. Container models add/remove fields at each
operation. Backward direction reverses the existing transfers. Physical
calls and local loop feedback both contribute relations.

```java
Map<String, Object> replace(Map<String, Object> input, ...) {
    Map<String, Object> result = new HashMap<>();
    for (Entry<String, Object> e : input.entrySet()) {
        Object value = e.getValue();
        // String: replaceVariables; Map: replace; List: replaceList.
        Object newValue = ...;
        result.put(e.getKey(), newValue);
    }
    return result;
}
```

Both logged owners have context `[{arg(0) == java.util.HashMap}]`. Preserve
this suffix for `replaceList`; it is not a Java argument-type proof.

### Completed run-4: the two hot owners

| Operation | e558 | Current | Change |
| --- | ---: | ---: | ---: |
| Processed instruction packets | 550,664 | 574,907 | +4.40% |
| Fresh post-statement packets | 779,416 | 827,751 | +6.20% |
| Applied DATA boundary offers | 51,125,035 | 64,394,823 | +25.96% |
| Raw full observations | 13,183,146 | 14,003,544 | +6.22% |
| Prefix trial observations | 17,212,947 | 6,252,062 | −63.68% |
| All full observations | 30,396,093 | 20,255,606 | −33.36% |

The trie skips 10,790,772 earlier budgets. Every remaining tested candidate
passes in these owners. Their C2 count is 40,511,212, exactly two per full
observation, as in the control; 30,928,742 reach native C2. Required raw
baselines remain numerous after trial pruning.

Publication selection reduces a linear-pair bound of 94,358,841 to 7,173,466
candidate pairs: 92.40% pruned. Yet there are 5,183,604 native matches and
**60,565,427 current DATA callbacks**: 11.68 callbacks per match, 437.47 per
fresh local input offer. Native application and the loop gate still run.
ND combinations, Target callbacks and pre-publication dead locals are zero
in these owners.

The run logs 24 owners selected by steps, out of 49 loop methods. These are
not all-method totals. Completion deduplication follows the expensive gate.

### Exact diagnostic — reached run-4, completed/accepted run-3

A separate run captures the first 4,096 exact events from `replace` in run-4,
then stops its verified analyzer by design. Actual Gradle exit: 1. This is
not completed run-4 quality or timing evidence. Capture span: 0.303714 s.
All events decode, with zero malformed events or partial fact expansions.
Post-cap attempts are unknown because the diagnostic stops.

There are 889 complete applied → kept → completion frames. All applied facts
are FLOW: 373 NORMAL and 516 DEMAND, with 21 complete singleton premises,
no applied protection and no ND premise. Concrete reverse candidates occur,
but no TAINT is applied in this prefix.

| Completion | Non-growing relation | Growing relation | Total |
| --- | ---: | ---: | ---: |
| Fresh | 229 | 307 | 536 |
| No fresh delta | 321 | 32 | 353 |

Thus 39.71% produce no new delta. **This is not an exact-cache hit rate.**
All 339 growing decision keys and all 393 full observer keys are distinct.
Simulated capacities 32, 128 and 512 give zero exact decision hits here.

Actual fanout includes **18 complete premises × 10 output geometries ×
2 physical exits = 360 relation events** for one `var(9).*/FLOW` premise.
Outputs include container Element, Map.Entry.Value, Pair.right and rule-storage
fields. These are actual alternatives, not proof of impossible aliases.
The shared direct lane cannot distinguish current unary application from
same-direction saved replay.

### One complete fact path

`MV` is `Map#MapValue`; `EL` is `Iterable#Element`. E/mx are empty, protection
is absent. Catalogue IDs are from this diagnostic alone.

```text
Original P = ret.MV.MV.*/FLOW, id11568. P stays unchanged.

66:   offer ret.MV.MV.*/FLOW NORMAL to AL block3 / ROOT_EXIT
171:  offer var(9).MV.MV.*/FLOW NORMAL to loop block2 / input43
3042: offer var(9).MV.MV.*/FLOW NORMAL to loop block2 / input40
3047: select I = var(9).*/FLOW, id62
             O = var(3).EL.*/FLOW, output7
      Native result under P: var(3).EL.MV.MV.*/FLOW NORMAL.
3048: stored I -> O grows. P length is not the growth test.
3049: raw observation:
      adjacent = {}
      repeat = {var(3).EL.*/FLOW NORMAL,
                var(3).EL.MV.*/FLOW NORMAL}
      enclosing = {}
3050: var(3).EL.MV.[any]/FLOW DEMAND has the same complete observation.
3051: keep that depth2 candidate.
3052: completion at block2/output7 under P returns a fresh delta.
```

All 54 proper captured cuts change NORMAL STAR depth3 to DEMAND ANY depth2.
Every first tested cut passes. Three other depth3 images remain at depth3.
The global bound is three; it does not cut these raw images first.

Fresh deltas use existing routes and post-statement stores. Publication uses
native C5 and paired demand. Handoff retains demand for the next run. This
prefix ends before a current body C5 publication, so it does not trace this
exact delta to handoff. The complete campaign supplies C5/frontier counts.

Another P is `ret.[any]/FLOW`. Its completion already has
`var(3).[any]/FLOW DEMAND`. A later growing
`var(3).EL.[any]/FLOW DEMAND` has a distinct query key, is observed, then
produces no delta. All 32 growing non-fresh cases have such an earlier ANY
prefix of depth at most one at the same P and point. A possible early check
must cover **every possible kept cut**, not just the raw result. These cases
are 9.44% of captured growing frames, not a whole-run saving estimate.

The trace shows finite depth and continuing distinct work. It establishes
neither an infinite processing loop nor termination for every possible input.
The large measured count is an application/observation product.

## 6. Thingsboard: matching repeats per writer output

The engine records 5,162,282 created caller-input groups and 9,261,231 created
index postings. These cumulative creation counts are not all live inputs,
not writer counts and not per-writer candidates. Final zero live gauges can
follow cleanup without erasing the earlier work.

Detached leases own cumulative caller/local inputs and raw write relations.
The full row key is `(actual owner, complete I, raw output O)`. Complete rows
are deduplicated. Static-original rows use the bridge graph instead.

```text
for each queued writer (owner, I, O), in FIFO order:
    borrow owner inputs; create a new per-writer visited-input set
    select root inputs by position, or scan all detached local groups
    matched = native satisfying(actual, I)
    apply native I -> O to each match
    preserve raw mx, then run1Cover -> field limit -> run1Cover
    seed exact parent owner/original -> bounded static result
    enqueue derived parent writer when original is nonstatic
```

Several output columns can share `(owner,I)`. Matching depends on complete I
and actual input, not O; selection/matching still repeat for each O. Detached
locals scan all groups because their live positional index is released during
detach. Root callers retain indexed selection but repeat it per output too.

```java
void set(Box p) { C.f = p; C.g = p; }
void caller(Box q) { set(q); }
```

```text
writer1: set/p.* -> C.f.*; writer2: set/p.* -> C.g.*
actual: caller/q.* -> set/p.suffix
Current: select/match p.* twice; apply both outputs.
Candidate: reuse complete input selection/match; still apply both outputs.
```

This is a showcase, not an asserted Thingsboard method. A bounded writer
diagnostic supplies actual rows separately. Global supply `C.f/T` cannot
replace producer guidance `q/T -> C.f/T`. Reach under a nonzero original is
not ZERO-source authority. Both rules must remain unchanged.

Input-first batching can change writer FIFO and dynamic seed discovery order.
The next design must preserve those orders or prove equivalent catalogue
observations. It must not retain an unbounded second matched-Facts collection.

### Actual Thingsboard output facts — reached run-1, no completed/accepted run

A separate field-only JDI run uses the same analysis configuration with a
loopback debugger. Pauses/deoptimization make its timings unsuitable for
comparison. It runs once and stops by design after 97 event attempts. Its
analyzer, debugger and client are verified absent afterward. One SIGTERM is
sent to the verified owned analyzer; no daemon or process group is signaled.
Debugger exit is 0; Gradle exit is 1. No diagnostic quality report is accepted.

There are **32 complete output events**, all decoded without error. The queue
attempt, 32 input-candidate attempts and 32 matched-input attempts are whole
event DROPs: **65 `NOT_INT` errors**. The external serializer supports a
primitive-backed path but fails on boxed Integer elements in the interner's
immutable `List<Int>`. Source layout and two offline controls reproduce this
limitation. The generic DROP has no per-event stack; discarded facts cannot
be recovered. No partial replacement or second run is used.

All outputs belong to writer ID1375, owner entry-object11640,
`onMsg(TbContext,TbMsg): void`, root scope `(0,-1)`. Their input parent is
entry-object11838, `onRuleChainToRuleNodeMsg(RuleChainToRuleNodeMsg): void`,
the same root scope, call stage3. Declaring-class caches are null in the
capture. The method descriptors and object identities are retained; no
declaring class or source-variable correspondence is guessed.

Define the actual output field F:

```text
F = STATIC[ClassStaticAccessor("__spring_registry__")]
          [FieldAccessor("__spring_registry__",
             "org.thingsboard.server.service.apiusage.TbApiUsageStateService",
             type="org.thingsboard.server.service.apiusage.TbApiUsageStateService")]

Attempt1, parent canonical initial30:
  P      = this.*/FLOW, E={}
  actual = arg(0).[any]/FLOW, DEMAND, E={}, mx={FULL#1,FULL#3}
  output = F.[any]/FLOW,      DEMAND, E={}, mx={FULL#1,FULL#3}

Attempt4, parent canonical initial656:
  P      = this.*/FULL#124, E={}
  actual = arg(0).[any]/FULL#124, DEMAND, E={}, protection=null
  output = F.[any]/FULL#124,      DEMAND, E={}, protection=null
```

`FULL#1` and `FULL#3` are the exact jjwt-hs256 and jjwt-none-alg marks.
`FULL#124` is the exact pair
`(@group:30:R:java/security/ssrf.yaml:ssrf;%%ordinary%%,
java/security/ssrf.yaml:ssrf#source#1;0;$UNTRUSTED;2)`.
The data embeds full dictionaries and complete actual/bounded/final DAGs.

The stream has two FLOW and 30 TAINT outputs, 28 distinct complete output
patterns and 32 distinct complete parent initials. Equal output geometry
under different originals is not redundant qualified guidance. The largest
observed same-parent/same-initial multiplicity is one. These pre-`onBound`
events do not prove the callback completed or reveal the raw writer row.

**Repeated queued writer-premise width remains unmeasured.** This diagnostic
therefore does not establish cache hits, a whole-queue mark matrix or a
factor-two saving. The main profile proves the expensive stage; the proposed
match reuse still needs its own reuse/admission measurements.

## 7. Memory and GC

| Project; latest reached | Peak RSS GiB | Maximum heap after pause GiB | Final heap after pause GiB | Total pause s | Full GC events | OOM heaps |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| OWASP; run-5 | 17.811 | 10.105 | 4.158 | 5.940 | 0 | 0 |
| Conductor; run-6 | 18.356 | 14.259 | 5.461 | 13.772 | 0 | 0 |
| Thingsboard; run-1 | 18.272 | 14.993 | 9.039 | 50.197 | 3 | 0 |
| Stirling-PDF; run-9 | 14.979 | 8.028 | 8.028 | 9.156 | 0 | 0 |

RSS includes native, metadata, code and profiler pages; it can exceed Xmx.
After-young-GC occupancy can include dead old objects. It is not a retained
owner census. No new OOM heap exists for dominator/layout analysis. Capture
hooks were configured, but no OOM triggered them.

Thingsboard has four high-memory warnings and three Full GCs. It recovers
and times out. Conductor run-6 reclaims about 2.739 TB across observed pauses,
with a final post-pause heap near 5.46 GiB. These totals indicate churn; they
do not prove a growing retained leak.

Conductor run-4 uses about 436.36 process CPU seconds over 277.609 wall seconds
(1.57 average cores), with 1.597 s GC pause. Run-6 uses 1,693.10 CPU seconds
over 578.659 s (2.93 cores), with 3.840 s pause. Process CPU includes native
GC/JIT. Java shares omit those threads. Small pause time does not prove small
GC CPU.

### Native CPU is separate from Java execution sampling

The denominator below is all collapsed CPU stack weights, including native
threads. The remaining portion is other CPU, not necessarily Java. G1/GC-worker
and compiler predicates are pinned in the data. No percentage is converted
to wall seconds or added to the Java-only percentages above.

| Project | Observed 30 s capture | Samples | Native GC % | JIT % | Other CPU % |
| --- | --- | ---: | ---: | ---: | ---: |
| OWASP | Mixed run-1/run-2 | 7,485 | 37.31 | 23.70 | 38.98 |
| Conductor | run-4 normal | 4,576 | 35.14 | 0.13 | 64.73 |
| Conductor | run-5 normal | 8,616 | 26.72 | 0.00 | 73.28 |
| Conductor | run-6 normal | 13,165 | 32.51 | 0.02 | 67.47 |
| Conductor | run-6 near limit | 4,303 | 30.68 | 0.00 | 69.32 |
| Thingsboard | run-1 engine normal | 42,718 | 39.08 | 4.53 | 56.39 |
| Thingsboard | run-1 static completion, near limit | 5,909 | 49.43 | 0.05 | 50.52 |
| Stirling-PDF | run-7 normal | 3,050 | 2.20 | 0.00 | 97.80 |
| Stirling-PDF | run-8 normal | 3,326 | 10.79 | 0.00 | 89.21 |
| Stirling-PDF | run-9 normal | 3,058 | 2.35 | 0.03 | 97.61 |
| Stirling-PDF | run-9 near limit | 3,095 | 4.04 | 0.00 | 95.96 |

Normal captures start about 60 s after their iteration begins. The OWASP
capture crosses the run-1/run-2 boundary; collapsed stacks have no event times
for an exact split. Thingsboard near-limit is in static completion, although
the wrapper still labels run-1 as engine-active. Conductor and Thingsboard
have substantial native GC CPU alongside the temporary Java allocations.

## 8. Counter limits and next work

Prepared `c5RowAttempts`, `c5Candidates` and `c5Restrict` count output-program
finalization visits, including empty buckets. They are not old per-row packet
restrictions. Use the separate accepted-occurrence, output-program, scalar
stream and candidate counters.

Conductor run-4 prepares 3,132,470 entry occurrences, accepts 992,899, and builds
936,703 output programs. It enumerates 3,183,953 scalar members and visits
5,209,762 candidate programs. No overflow or factory fallback is logged.
Programs/accepted occurrences is 94.34%, not a duplicate ratio: an accepted
occurrence can have no DATA output.

Publication pairs, native matches, callbacks, fresh storage deltas and unique
handoff rows measure different work. `localNdCombinations` counts actual
binding/output emissions, including upgrades. Saved selection counters cover
real replay and the pure observer. Batch-dependent diagnostics may change;
semantic observations must remain equal.

Unknowns remain explicit: whole-run redundant observer images, candidate
totals in the canceled binder, complete missing Stirling paths, and retained
object owners without an OOM heap. No universal factor-two saving is claimed.

The [next proposal](../design/bidirectional-joined-writer-observer-work-next-iteration-20261104.md)
targets repeated complete-premise writer matching and provably empty pure
observer work, with sparse C5 finalization as a smaller option. It states
current/new behavior, examples and proof obligations. No next-iteration
runtime change is included here.

The [frontier-growth investigation](bidirectional-stirling-conductor-frontier-growth-20261104.md)
traces the Stirling forward-run increases and Conductor run-4/run-5 changes
to exact method counts, FLOW path shapes and distinct processing costs.
