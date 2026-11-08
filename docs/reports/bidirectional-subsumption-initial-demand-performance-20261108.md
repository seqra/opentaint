# Subsumption and STAR initial emission: project measurements

8 November 2026. Runtime: 334234c24e9008f4a2614b8213b8b2e73b6ba9e1.
Core tree: 8b38a03586138acbbf5aaadd94b5fb301d6c9cad.

The implementation is complete. **Project acceptance fails:** three analyses
time out, and four strict baseline identities are absent from the accepted
reports. OWASP converges. Conductor preserves all seven baseline identities,
including both Graal findings. Thingsboard now commits run-1. Stirling's
forward path explosion is much smaller, but later backward work repeats.

## 1. Runtime, controls and proof scope

Implementation is on branch task/subsumption-initial-demand-20261108.
It starts from selected revision 52829d5890ec3b3145cc996a1d8162d85cb8ceda.
The selected baseline has the same core as saved 52f32dd437d438aec4a700a02c18d94c31d58093.
The dirty original worktree and withdrawn special-tail prototype were preserved.

The implementation commits are e1838296f69ceadd04d51d0499800881bd617ff5 and
334234c24e9008f4a2614b8213b8b2e73b6ba9e1. The second commit repairs four stale
ANY-only validators. Selected C5 can produce a FLOW STAR demand, including
a normalized exact FLOW output. The repair preserves that paired row through
method and block handoff. It adds no new transfer or admission rule.

The complete native suite passes **2,510 common-core and 461 JVM tests**.
The constructive package passes 1,245 component declarations and 16 handoff
bridge proofs. This is not a proof of the complete Kotlin analyzer, universal
no-FN behavior or convergence. A separate strict receiver-reset diagnostic
has two tests and one failure; section 4 preserves that coverage failure.

The selected changes include independent plain/protected memberships,
MAY/MUST canonicalization, aligned NORMAL FLOW relation subsumption,
opposite-record-only STAR inside matching, no ANY owned premises, the
complete C2 companion family, paired C5 restriction, the selected cleaner
repair and the own-ZERO loop-gate bypass. These are the semantic changes in
the finalized spec. No new tail, grounding state, StrongQueries route,
field-transfer rule, alias policy or stop rule was added.

All measured commands use Gradle runProjectAnalyzer, FULL marks, 16 GiB,
aliases and statics enabled, and limits 1,1,2,3,... with alternating direction.
The saved models and budgets are unchanged: OWASP 1,000 seconds; the other
projects 1,080 seconds; outer timeout 1,200 seconds. No baseline was rerun.
The strict finding reference is f945f92c5ae554ff4f5fc7696ee5a269210478bb.

The 52f saved control is used only for same-configuration performance
comparison. It has the selected preimplementation core. The separate
7069 campaign and the aborted e183 attempt are not substituted for it.
Single instrumented scans do not isolate host effects or prove a causal
speedup for one atomic change.

Evidence root:

    /drive-testcomp/opentaint-go-rules/subsumption-initial-demand-20261108/handoff-fixed

Preparation and runtime receipts pin models, rules, Java, helper commands,
classpath and references. The coordinator checks unchanged core/artifacts
before and after each project. Projects ran in sequence. Heavy JFR review
started after all four commands ended. Old owned captures and the aborted
attempt's captures were removed with receipts; its logs and status remain.
The latest campaign's captures remain available.

## 2. Terminal outcome

An engine completion is not a committed iteration. Commit also needs the
frontier and a later run start or completed driver. A cleanup barrier does
not prove commit. The table uses those separate checks.

| Project | Command | Reached | Engine complete / committed | Accepted forward | Strict missing / added |
| --- | --- | --- | --- | --- | --- |
| OWASP | OK | run-5 | run-5 / run-5 | run-5 | 0 / 0 |
| Conductor | TIMEOUT | run-14 | run-13 / run-13 | run-13 | 0 / 0 |
| Thingsboard | TIMEOUT | run-2 | run-1 / run-1 | run-1 | 1 / 0 |
| Stirling-PDF | TIMEOUT | run-52 | run-51 / run-51 | run-51 | 3 / 8 |

| Project | Command seconds | Peak RSS GiB | Run-1 engine seconds | At most 60 seconds |
| --- | ---: | ---: | ---: | --- |
| OWASP | 209.363 | 17.730 | 80.926 | No |
| conductor | 1128.404 | 18.299 | 15.918 | Yes |
| thingsboard | 1126.542 | 18.348 | 521.169 | No |
| Stirling-PDF | 1118.898 | 14.689 | 19.626 | Yes |

RSS includes native memory. An incomplete timeout is not a completed speedup.
Only Conductor and Stirling meet the 60-second run-1 engine target.

## 3. Change against the selected saved control

| Project / phase | Saved 52f | Current 334234 | Interpretation |
| --- | ---: | ---: | --- |
| OWASP run-1 | 76.105 s | 80.926 s | Slower in this scan; both converge at run-5 |
| Conductor run-4 | 277.610 s | 6.051 s | Much less work at this iteration |
| Conductor run-5 | 130.704 s | 7.025 s | Much less work at this iteration |
| Conductor terminal | Timeout run-6; accepted run-5 | Timeout run-14; accepted run-13 | More refinement fits, but no convergence |
| Thingsboard run-1 | Timeout; 678.522 engine + 259.298 binding seconds, incomplete | Complete; 521.169 engine + 292.711 binding + 21.545 barrier seconds | First report commits; the old partial interval is not a complete timing control |
| Stirling run-7 | 221.182 s | 0.868 s | Forward path explosion greatly reduced |
| Stirling run-8 | 260.877 s | 34.336 s | Backward work reduced, but remains expensive |
| Stirling terminal | Timeout run-9; accepted run-7 | Timeout run-52; accepted run-51 | Repeated later iterations consume the budget |

The selected canonical semantics reduce real workload. This does not mean
that every implementation path is efficient. The new canonical maintenance
also introduces full-state work which the old implementation did not do on
its common path. Sections 5 and 6 separate those facts.

## 4. Strict finding comparison and unresolved coverage

| Project | Baseline identities | Current identities | Missing | Added |
| --- | ---: | ---: | ---: | ---: |
| OWASP | 4,112 | 4,112 | 0 | 0 |
| Conductor | 7 | 7 | 0 | 0 |
| Thingsboard | 14 | 13 | 1 | 0 |
| Stirling-PDF | 17 | 22 | 3 | 8 |

Comparison uses rule ID, sink fingerprint and complete method signature.
The data packet retains exact identity sets and locations. Additional
identities are not automatically false positives. Timeout comparisons
describe accepted snapshots, not a completed analysis.

Thingsboard misses unsafe reflection in
ReflectionUtils.getAnnotationProperty(String,String,String), fingerprint
QqsVp4+sxVrhcl8zO3TCQnLuKU/flyz9avYbI4/f3YY=.
The dynamic Class.forName input is instruction 1. Instruction 0 uses a
constant annotation type and is a separate call; constant-base removal
does not explain the missing identity. Both saved dynamic paths remain in
the current source/model. The current run-1 analyses the helper, validator,
service and controller; the helper has one outgoing demand row. The full
unsafe-reflection mark is registered. The first lost fact is **not known**.
The accepted report is run-1 and run-2 times out. Neither eventual recovery
nor a lowering defect is proved. This omission remains a strict failure.

Stirling's three omissions are:

| Rule / method | f945 location | Current evidence |
| --- | --- | --- |
| OS command injection / ProcessExecutor.runCommandWithOutputHandling(List,File) | IR 8, Java line 183 | Current reduced receiver-reset witness fails |
| XSS / PipelineController.handleData | IR 50, Java lines 90–91 | Current report is at IR 109, Java line 130 |
| XSS / ConvertEmlToPDF.convertEmlToPdf | IR 103, Java lines 133–134 | Current report is at IR 126, Java lines 148–149 |

The command witness uses a real native driver and call stages:

    command.add(sourceT()); // Generates exact receiver mark A.
    command.add("literal"); // Guard is false; unresolved return cleanup removes A.
    sinkA(command);         // Required finding is absent.

The direct-use control reports. The strict extra-literal test fails.
Both complete FULL run-1. The preserved fixture was run unchanged in a
separate checkout at the measured commit: two tests, one failure, zero
errors. The six audited production lowering/rule files match the older
real-JIR audit. This proves a current reduced loss. It does not prove the
first actual loss in the full Stirling run. No unselected cleanup fix was
applied.

For XSS, the exporter uses a return found in a trace when available.
Otherwise it selects the last JIR return. Bidirectional reports use Simple
traces and have no code flow. This explains the different representative
coordinates. It does not prove that the old branch witness is preserved.
Both identities remain missing. The eight additions are XSS identities,
including those two later coordinates; they are not a waiver of the losses.

## 5. Thingsboard run-1: shallow facts, large delivery and guidance joins

Run-1 processes 18,857,462 body packets, admits 28,539,928 fresh post-statement
packets and offers 14,104,167 boundary candidates. These are stage events,
not distinct logical facts. Field limit is one. The loop growth gate is
bypassed, so deep-prefix loop queries cannot explain this run-1 cost.

The derived pre-binding JFR window allocates an estimated 2,719.53 GB.
Summary pub/sub stacks account for 66.12% of Java CPU samples and 77.06%
of allocation weight. Ordinary initial replay is 26.38% CPU; DATA delivery
is 21.28%. Diagonal admission is 18.91% CPU and 22.82% of allocations.
These inclusive figures overlap.

A sampled block route is:

    BlockSummaryLinks delivery
      -> applyMatched / run1Cover
      -> MethodBlockRuntime.onApplied
      -> completion admission
      -> FlowBackedSummaries
      -> DiagonalRelations.addAll
      -> temporary TaintGroup reconstruction and canonicalization

The new diagonal adapter reconstructs the existing selected mark/class
projection before it can reject a duplicate. A fresh insertion clears that
mark/class from the scoped rows and re-encodes the retained projection.
The baseline used full reconstruction only for conflicting typed headers.
Independent protection classes and canonical semantics do not require a
full rebuild on every offer. Actual duplicate rates and projection sizes
were not counted, so no speedup is asserted from source alone.

The separate joined static binding takes 292.711 seconds. Writer application
takes 284.235 seconds of it. Exact native counts are:

    Writer offers                       31,622,618
    Admitted / processed writer keys     2,969,858
    Candidate input visits             462,365,666
    Matched inputs                      33,190,272
    Bound outputs                       33,099,986
    Within-writer duplicate input keys           0

Only 7.18% of candidate visits match. The binding window allocates an
estimated 780.24 GB. OwnedJoinedStaticWriterBinding accounts for 97.57%
of its CPU samples. It selects and matches actual inputs per writer row.
Different output columns can share an owner and complete premise, so this
can repeat selection/matching. That multiplicity is not measured. Detached local inputs no longer have the live
position index and are scanned; physical root inputs remain indexed.
There is no local/root visit split in the counters.

These outputs are **caller-owned static guidance**, not pool supplies.
They produce W attachments or static B bridges, including killed-at-exit
and recursive parent routes needed by run-2. An executed static write
supplies the pool separately. Skipping this join because the pool already
has C.f/T would lose origin guidance.

The final catalog contains 2,753,000 W attachments and 331,581 own B
memberships. Their sum is 3,084,581. At least 30,015,405 of the 33,099,986
bound callbacks cannot add a new final W/B membership. This is a bound
on that effect, not an exact duplicate-event count or an ANY-cell hit rate.
Other seed sources also contribute to the final catalog. Boundary setup
and parent scheduling must remain valid.

For one narrow FULL cell, concrete STAR/T premise to concrete static
ANY/U output, the actual suffix is erased by the existing application.
One successful support per complete parent owner/original and raw output
is sufficient for the same thin guide. This is not true for STAR outputs,
which can carry different suffixes. The next proposal keeps that boundary.

The static pool's 1,117 STATIC-origin FLOW registrations and 384 nonstatic
FLOW registrations are not the 2.97 million joined writer keys.
Sampled hot body rows contain Spring-registry statics, generated XSS marks,
ANY/DEMAND outputs and protection. The sample is too small to give a global
static fraction. Pool frames also omit later work which they enqueue.
Do not infer payload causation from a stack-family percentage.

## 6. Conductor: repeated complete loop queries

In run-10, the printed 24 of 27 loop owners have:

    Loop-output offers                 7,821,073
    Gate bypasses                      2,429,461
    Gated packet applications          5,391,612
    Scalar memberships checked         9,296,702
      dropped                            598,351
      prefix-cut                       8,218,452
      retained raw                       479,899
    Complete observations             30,687,125
      raw baseline checks              9,296,702
      additional prefix trials        21,390,423
    Body instruction packet events     1,542,893

Both outcome partitions are exact. Relation applications, scalarization
and pure observations do not each create a body instruction event.
This is work amplification, not proof that an identical fact was processed
twice at one instruction.

ParametersUtils.replace accounts for 97.19% of those observations. Its loop
reads map entries, recursively maps nested maps/lists and writes another map.
It makes 59,648,726 C2 calls: two per observation. Native calls return
169,682,916 rows. About 96.1% of run-10 trie candidates are successful
ANY-demand/ANY-input cases. Removing impossible STAR matches is not the
main opportunity here.

The repeated route is:

    Apply a loop summary and bound its result
      -> scalarize a growing result
      -> observe raw
           adjacent C2
           saved adjacent replay plus enclosing C5
           repeat C2
      -> repeat that whole observer for successive prefix budgets
      -> insert the selected result in the completion owner

The old first-budget certificate is deliberately disabled: it does not
cover the complete new initial-emission family. It must not be restored
without a new proof for primary initials, both companion mechanisms,
paired outputs, layers, H and physical ports.

Run-12 repeats the pattern: 9,954,984 scalars, 32,961,384 observations and
183,277,161 returned C2 rows. Complete observation takes 67.91% of Java
CPU samples and 64.96% of allocation weight. C2 is 47.59% CPU; actual C5
is 4.40%. Forward run-13 has a different mix: C2 is 2.63% CPU and TAINT
canonicalization is 40.90%. The backward slowdown is not explained by
the outgoing demand count alone.

## 7. Stirling: repeated bounded FLOW work

Backward run-30 takes 39.060 seconds. EmlProcessingUtils.decodeMimeHeader,
in default and StringBuilder contexts, accounts for 92.25% of processed
body packets. They are FLOW packets. The default context's packet/depth
histograms are identical in runs 16, 18 and 30: 243,403 processed packets,
300,525 fresh packets and 133,825 candidates. Maximum depth is 11 while
the respective global limits are 15, 17 and 29.

This is different from Conductor. FLOW canonicalization takes 89.19% of
run-30 Java CPU samples and 84.70% of its 102.28 GB allocation estimate.
Loop observation is only 2.01% CPU. Allocation stacks pass through:

    ScopedEdgeStore.addPacket
      -> ConclusionGroup.addAll
      -> FlowGroup.addAll
      -> subtractSubsumed
      -> FlowAlgebra.subtract

The new FlowGroup first inserts the offer, then scans retained headers
against the other headers, performs MUST merge/fill passes, scans again,
and compares against the previous basis. This work also runs when the
insertion found no fresh change. The baseline's common path worked on
the pending offer. This is current-iteration implementation amplification,
not evidence that the selected canonical laws should be removed.

From run-15 onward the printed forward and backward counts repeat at
782 and 884. Exact row identity is not exported. Some forward
processInlineImages events reach the saturated depth-16+ histogram bin;
their uncapped maximum is unknown. Thus the report does not claim a global
fixed point, absence of deeper growth or a safe new stopping rule.
The next experiment must record exact semantic state hashes/diffs and
uncapped depths before it can establish those facts.

## 8. Allocation and memory

No JVM OOM or MemoryManager OOM stop occurs. No heap dump exists.
Thingsboard reports three high-memory threshold events. These are not
OOM events. Its sampled maximum after-GC use is about 15.70 GB, or
14.62 GiB, under the 16 GiB heap cap.

GB below means decimal GB. Allocation weights estimate allocated bytes,
not live or retained bytes. Summed GC event durations are not a wall-time
fraction or a sum of STW pauses. Run-1 marker envelopes include binding;
the Thingsboard split is duration-derived and has unlogged close overhead.

| Window | Allocated GB | Max after-GC GB |
| --- | ---: | ---: |
| OWASP run-1 envelope | 145.16 | 7.37 |
| Conductor run-1 envelope | 54.14 | 9.66 |
| Thingsboard run-1 envelope | 3,499.78 | 15.70 |
| Thingsboard pre-binding | 2,719.53 | 15.66 |
| Thingsboard binding | 780.24 | 15.70 |
| Stirling run-1 envelope | 58.12 | 5.81 |
| Conductor run-12 | 1,003.20 | 13.00 |
| Conductor run-13 | 341.00 | 13.37 |
| Stirling run-30 | 102.28 | 7.78 |
| Stirling run-31 | 2.47 | 7.88 |

The whole Thingsboard envelope and its two split rows overlap; do not add
all three. Observed JFR event ranges bracket all ten windows; this does
not prove uninterrupted sampling. After-GC use
shows pressure, but cannot identify retained owners. No retained-heap
layout or leak proof is claimed without a dump. The periodic
maxMemory-minus-freeMemory gauge is not used as actual heap consumption.

Run-1 construction is another, separate cost: OWASP has 48.02% of Java
CPU samples in FormsCache payload work, including 41.98% in call-plan
building and 19.87% in alias construction. This is first-use evidence,
not proof of cache rebuild thrashing. It does not explain the dominant
Thingsboard or later Stirling windows.

## 9. Next work and portable evidence

The [next proposal](../design/bidirectional-canonical-admission-static-guidance-loop-query-next-iteration-20261108.md)
ranks three work-removal targets: incremental canonical owner updates,
factored static guidance binding, and complete-family loop query planning.
It also lists the unresolved finding traces and the exact state/depth
diagnostics needed for Stirling. No new core change followed the measured
commit.

Committed data files retain exact identities, locations, all iteration
times/frontiers, native counters and selected fact annotations, JFR metrics,
complete sampled stacks, coverage and source hashes. The evidence index
lists any omitted repeated raw strings. External raw logs/captures remain
under the evidence root; the report does not depend on an untracked
shape-probe-results directory.

Portable files:

- [Evidence index and hashes](data/bidirectional-subsumption-initial-demand-evidence-index-20261108.json).
- [Exact quality, command and iteration data](data/bidirectional-subsumption-initial-demand-quality-20261108.json).
- [All aggregate and numeric owner counters](data/bidirectional-subsumption-initial-demand-work-20261108.json).
- [Principal fact examples, controls and XSS audit](data/bidirectional-subsumption-initial-demand-principal-evidence-20261108.json).
- [All captured C5 component samples](data/bidirectional-subsumption-c5-samples-20261108.json).
- [Ten JFR windows, coverage, complete sampled stacks and source comparisons](data/bidirectional-subsumption-profiles-20261108.json).
- [Reflection audit, current failing receiver fixture and joined-guidance source audit](data/bidirectional-subsumption-coverage-causes-20261108.json).

The work packet omits repeated full debug body snapshots and unquoted sample
rings. It retains every reported aggregate, numeric owner counter and quoted
principal coordinate. The raw originals remain hash-pinned outside Git.
The reduced failing fixture and its native trace/XML are embedded in the
coverage packet.

## 10. All measured iteration times and frontiers

Handoff counts are native exported guidance counts; they can include
eligible NORMAL guidance. They are not distinct processed facts or solely
DEMAND-layer memberships. The last timeout rows are partial.

### OWASP

| Run | Direction | Limit | Engine s | Static bind s | Barrier s | Handoff / method keys | Target demand | Reports | Committed |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| run-1 | FORWARD | 1 | 80.925825 | 0.397418 | 2.870046 | 130117 / 4446 | 14087 | 3227 | yes |
| run-2 | BACKWARD | 1 | 25.650292 | — | 0.946862 | 25999 / 4224 | 2463 | 3227 | yes |
| run-3 | FORWARD | 2 | 14.954606 | — | 0.940382 | 173 / 78 | 80 | 4112 | yes |
| run-4 | BACKWARD | 3 | 0.327155 | — | 0.697394 | 129 / 44 | 42 | 4112 | yes |
| run-5 | FORWARD | 4 | 0.222418 | — | 0.69549 | 0 / 0 | 0 | 4112 | yes |

### Conductor

| Run | Direction | Limit | Engine s | Static bind s | Barrier s | Handoff / method keys | Target demand | Reports | Committed |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| run-1 | FORWARD | 1 | 15.917709 | 1.177843 | 2.104194 | 114135 / 6763 | 7896 | 2 | yes |
| run-2 | BACKWARD | 1 | 28.984014 | — | 2.792315 | 479523 / 9364 | 206 | 2 | yes |
| run-3 | FORWARD | 2 | 6.594972 | — | 0.972312 | 13516 / 383 | 3947 | 5 | yes |
| run-4 | BACKWARD | 3 | 6.05147 | — | 0.584775 | 14254 / 242 | 39 | 5 | yes |
| run-5 | FORWARD | 4 | 7.025134 | — | 0.609754 | 10305 / 198 | 4024 | 7 | yes |
| run-6 | BACKWARD | 5 | 9.663147 | — | 0.573959 | 12605 / 194 | 39 | 7 | yes |
| run-7 | FORWARD | 6 | 11.505788 | — | 0.601057 | 12085 / 189 | 4782 | 7 | yes |
| run-8 | BACKWARD | 7 | 32.080759 | — | 0.587691 | 15500 / 189 | 39 | 7 | yes |
| run-9 | FORWARD | 8 | 17.723457 | — | 0.736049 | 14518 / 187 | 3653 | 7 | yes |
| run-10 | BACKWARD | 9 | 340.793424 | — | 1.388563 | 29755 / 187 | 39 | 7 | yes |
| run-11 | FORWARD | 10 | 30.681772 | — | 0.663354 | 20728 / 187 | 3823 | 7 | yes |
| run-12 | BACKWARD | 11 | 375.680781 | — | 1.783161 | 35843 / 187 | 39 | 7 | yes |
| run-13 | FORWARD | 12 | 71.532146 | — | 0.711273 | 36947 / 187 | 3981 | 7 | yes |
| run-14 | BACKWARD | 13 | 86.584921 | — | — | — / — | — | — | no |

### Thingsboard

| Run | Direction | Limit | Engine s | Static bind s | Barrier s | Handoff / method keys | Target demand | Reports | Committed |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| run-1 | FORWARD | 1 | 521.168831 | 292.710897 | 21.544809 | 6249488 / 30247 | 3495768 | 13 | yes |
| run-2 | BACKWARD | 1 | 105.548173 | — | — | — / — | — | — | no |

### Stirling-PDF

| Run | Direction | Limit | Engine s | Static bind s | Barrier s | Handoff / method keys | Target demand | Reports | Committed |
| --- | --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| run-1 | FORWARD | 1 | 19.625944 | 0.411397 | 0.916011 | 73276 / 2023 | 5400 | 7 | yes |
| run-2 | BACKWARD | 1 | 11.463936 | — | 1.493246 | 255159 / 4199 | 518 | 7 | yes |
| run-3 | FORWARD | 2 | 3.452462 | — | 0.692045 | 1383 / 431 | 647 | 21 | yes |
| run-4 | BACKWARD | 3 | 3.024076 | — | 0.518214 | 2155 / 415 | 130 | 21 | yes |
| run-5 | FORWARD | 4 | 0.776932 | — | 0.50077 | 860 / 86 | 107 | 22 | yes |
| run-6 | BACKWARD | 5 | 13.921449 | — | 0.492668 | 1090 / 80 | 52 | 22 | yes |
| run-7 | FORWARD | 6 | 0.868166 | — | 0.480158 | 784 / 74 | 110 | 22 | yes |
| run-8 | BACKWARD | 7 | 34.335955 | — | 0.477902 | 983 / 70 | 44 | 22 | yes |
| run-9 | FORWARD | 8 | 1.461708 | — | 0.49384 | 767 / 70 | 115 | 22 | yes |
| run-10 | BACKWARD | 9 | 41.941898 | — | 0.479593 | 969 / 70 | 44 | 22 | yes |
| run-11 | FORWARD | 10 | 3.31283 | — | 0.488137 | 803 / 70 | 118 | 22 | yes |
| run-12 | BACKWARD | 11 | 43.470633 | — | 0.497119 | 965 / 69 | 44 | 22 | yes |
| run-13 | FORWARD | 12 | 2.401581 | — | 0.481318 | 784 / 59 | 118 | 22 | yes |
| run-14 | BACKWARD | 13 | 42.607007 | — | 0.499902 | 886 / 59 | 39 | 22 | yes |
| run-15 | FORWARD | 14 | 4.519133 | — | 0.513359 | 782 / 59 | 118 | 22 | yes |
| run-16 | BACKWARD | 15 | 41.349026 | — | 0.478771 | 884 / 59 | 39 | 22 | yes |
| run-17 | FORWARD | 16 | 2.953625 | — | 0.47333 | 782 / 59 | 118 | 22 | yes |
| run-18 | BACKWARD | 17 | 41.078364 | — | 0.473947 | 884 / 59 | 39 | 22 | yes |
| run-19 | FORWARD | 18 | 4.026913 | — | 0.476452 | 782 / 59 | 118 | 22 | yes |
| run-20 | BACKWARD | 19 | 41.119105 | — | 0.477046 | 884 / 59 | 39 | 22 | yes |
| run-21 | FORWARD | 20 | 1.655152 | — | 0.473769 | 782 / 59 | 118 | 22 | yes |
| run-22 | BACKWARD | 21 | 41.146568 | — | 0.4787 | 884 / 59 | 39 | 22 | yes |
| run-23 | FORWARD | 22 | 1.33176 | — | 0.479869 | 782 / 59 | 118 | 22 | yes |
| run-24 | BACKWARD | 23 | 41.305859 | — | 0.478422 | 884 / 59 | 39 | 22 | yes |
| run-25 | FORWARD | 24 | 3.007188 | — | 0.475836 | 782 / 59 | 118 | 22 | yes |
| run-26 | BACKWARD | 25 | 41.578956 | — | 0.471773 | 884 / 59 | 39 | 22 | yes |
| run-27 | FORWARD | 26 | 5.674883 | — | 0.468954 | 782 / 59 | 118 | 22 | yes |
| run-28 | BACKWARD | 27 | 41.66755 | — | 0.480311 | 884 / 59 | 39 | 22 | yes |
| run-29 | FORWARD | 28 | 1.319757 | — | 0.471265 | 782 / 59 | 118 | 22 | yes |
| run-30 | BACKWARD | 29 | 39.060234 | — | 0.47914 | 884 / 59 | 39 | 22 | yes |
| run-31 | FORWARD | 30 | 1.233542 | — | 0.474652 | 782 / 59 | 118 | 22 | yes |
| run-32 | BACKWARD | 31 | 40.735639 | — | 0.476662 | 884 / 59 | 39 | 22 | yes |
| run-33 | FORWARD | 32 | 1.208695 | — | 0.489423 | 782 / 59 | 118 | 22 | yes |
| run-34 | BACKWARD | 33 | 40.442659 | — | 0.478236 | 884 / 59 | 39 | 22 | yes |
| run-35 | FORWARD | 34 | 4.184005 | — | 0.469634 | 782 / 59 | 118 | 22 | yes |
| run-36 | BACKWARD | 35 | 40.509427 | — | 0.484301 | 884 / 59 | 39 | 22 | yes |
| run-37 | FORWARD | 36 | 3.930635 | — | 0.476562 | 782 / 59 | 118 | 22 | yes |
| run-38 | BACKWARD | 37 | 40.451525 | — | 0.47681 | 884 / 59 | 39 | 22 | yes |
| run-39 | FORWARD | 38 | 1.32908 | — | 0.477518 | 782 / 59 | 118 | 22 | yes |
| run-40 | BACKWARD | 39 | 40.531538 | — | 0.492713 | 884 / 59 | 39 | 22 | yes |
| run-41 | FORWARD | 40 | 2.89574 | — | 0.470681 | 782 / 59 | 118 | 22 | yes |
| run-42 | BACKWARD | 41 | 40.522002 | — | 0.525916 | 884 / 59 | 39 | 22 | yes |
| run-43 | FORWARD | 42 | 2.925521 | — | 0.471111 | 782 / 59 | 118 | 22 | yes |
| run-44 | BACKWARD | 43 | 40.436547 | — | 0.476266 | 884 / 59 | 39 | 22 | yes |
| run-45 | FORWARD | 44 | 1.94705 | — | 0.480743 | 782 / 59 | 118 | 22 | yes |
| run-46 | BACKWARD | 45 | 40.614455 | — | 0.480128 | 884 / 59 | 39 | 22 | yes |
| run-47 | FORWARD | 46 | 1.775825 | — | 0.478729 | 782 / 59 | 118 | 22 | yes |
| run-48 | BACKWARD | 47 | 40.403538 | — | 0.474747 | 884 / 59 | 39 | 22 | yes |
| run-49 | FORWARD | 48 | 1.420241 | — | 0.475015 | 782 / 59 | 118 | 22 | yes |
| run-50 | BACKWARD | 49 | 40.43491 | — | 0.477143 | 884 / 59 | 39 | 22 | yes |
| run-51 | FORWARD | 50 | 1.414757 | — | 0.479984 | 782 / 59 | 118 | 22 | yes |
| run-52 | BACKWARD | 51 | 33.070839 | — | — | — / — | — | — | no |
