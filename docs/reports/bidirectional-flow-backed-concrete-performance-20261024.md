# FLOW-backed concrete relations: fixed project measurements

Measurements: 24 October 2026. Capture analysis closed: 25 October 2026.
Status: implementation, local validation, all 12 fixed project commands,
profiles and all six OOM heap analyses are closed. Project acceptance failures
remain explicit below.

## Result and scope

The implementation is commit `5ec1b30be614a0cfdc31ec3102bfa2f9301ee21e`.
Thingsboard now completes **run-1 in 392.439 s**, then reaches **run-2 OOM**.
Its latest COMPLETE engine and accepted forward report are **run-1**. The
fresh scalar reference reaches **run-1 OOM**. The change therefore removes
that run-1 memory failure for this observation. It does not meet the
60-second run-1 engine target. The reference has no completed run-1 time,
so its OOM time is not a speed baseline for a completed run.

Conductor and Stirling-PDF complete run-1 in 13.673 s and 25.288 s. Their
run-1 times are almost unchanged from the reference. Both then reach
**run-2 OOM**, as does the reference. One observation per configuration
does not establish a statistical speedup.

OWASP completes and accepts **run-11** in both bidirectional versions. The
candidate's run-1 is 93.900 s versus 88.639 s in the reference: 5.94% longer
in these single observations. Its whole command is 870.421 s versus
857.467 s. The optimization does not improve this project's measured time.

This report measures the selected
[FLOW-backed relation change](../../spec/run1-flow-backed-concrete-relations.md).
The [local validation report](bidirectional-flow-backed-concrete-validation-20261024.md)
records the tests and proof boundary. No extra analyzer optimization was
added during the project campaign. The
[next proposal](../design/bidirectional-flow-backed-next-iteration-20261024.md)
must be reviewed before implementation.

## Revisions and fixed inputs

| Role | Revision | Core tree |
| --- | --- | --- |
| Candidate | `5ec1b30be614a0cfdc31ec3102bfa2f9301ee21e` | `e3ede1a36d3b04d79a23cc93285f385ecd968dbf` |
| Scalar bidirectional reference | `40e20d16f03ab046df75a53a489bb331b065a9c1` | `c986cba8f1ea0531f7db2a4c91a10c90c2743fd4` |
| Fresh remote main, legacy engine | `f945f92c5ae554ff4f5fc7696ee5a269210478bb` | `04ca0001e29a6d1b070f5f8dff27d007da5c77dd` |

Main has a saved diagnostic-only MemoryManager snapshot patch. It does not
change transfer or rule semantics. Candidate and reference runtime sources
are clean at launch. Source, input, rule and helper guards bind the commands.
The test repository is `bbdbcc5fd35d976d93348760ea60561e4670f68c`.

All commands use Gradle `runProjectAnalyzer` directly, Java 17, the configured
project model and extensions, FULL run-1 marks, statics enabled, the default
alias analysis, IR batch size 2,000, and disabled multi-release JAR lookup.
OWASP uses the CI rule scope. Conductor uses its configured extension rules,
passthrough and compiled dataflow models. No alternative heap, timeout or
alias configuration was tested.

| Project | Heap | Analyzer timeout | Outer command limit |
| --- | ---: | ---: | ---: |
| Thingsboard | 12 GiB | 1,080 s | 1,200 s |
| Conductor | 8 GiB | 1,080 s | 1,200 s |
| Stirling-PDF | 8 GiB | 1,080 s | 1,200 s |
| OWASP | 8 GiB | 1,000 s | 1,200 s |

The evidence root is
`/drive-testcomp/opentaint-go-rules/run1-flow-backed-20261024`.
All project commands are fresh. No earlier report supplies a current result.
The preparation receipt records removal of 132 previous capture/index files
with a total length of 244.24 GiB. This does not include unrelated user files.
Large shared IR and dependency trees are not exhaustively content-hashed;
their resolved paths, project models and command/source guards are recorded.

The [terminal receipt](../../../run1-flow-backed-20261024/preparation/terminal.json)
closes all 12 commands, with unchanged sources, inputs and helpers and no
postprocessing error. No analyzer, test, MAT or profile-decoder workload ran
beside a timed command. All capture decoding starts after that receipt.
The minimum sampled host available memory is at least 31.82 GiB; no sample
falls below its analyzer heap plus 2 GiB. Existing host swap use is nonzero,
so this is not proof of zero paging. The experiment is serial and has one
observation per side; cache warmth and scheduling are not randomized.

The two main patch hashes differ only because the benchmark manifest hashes
the stripped diff text and the launch receipt hashes raw diff bytes. The
[source binding](../../../run1-flow-backed-20261024/validation/main-diagnostic-source-binding.json)
checks both against the same saved 16-line diagnostic patch.

## Time and iteration progress

Engine time is the `BIDI_RUN_END` interval. It excludes prescan and the report
barrier. Whole command time also includes Gradle, initialization, prescan,
later iterations, capture pauses and export. An OOM engine interval includes
the blocking live heap dump. These coordinates must not be interchanged.
An accepted forward report is a state committed to the report builder. It
does not mean that the final precision or performance acceptance gate passes.

| Project / engine | Whole command, s | Run-1 engine, s | Run-2 engine, s | Latest reached | Latest COMPLETE | Accepted forward report |
| --- | ---: | ---: | ---: | --- | --- | --- |
| Thingsboard / main | 217.422 | N/A | N/A | Legacy | N/A | Legacy |
| Thingsboard / reference | 375.322 | 198.545, OOM | Not started | run-1 | None | None |
| Thingsboard / candidate | 775.808 | 392.439, COMPLETE | 149.784, OOM | run-2 | run-1 | run-1 |
| Conductor / main | 93.168 | N/A | N/A | Legacy | N/A | Legacy |
| Conductor / reference | 150.777 | 13.566, COMPLETE | 69.746, OOM | run-2 | run-1 | run-1 |
| Conductor / candidate | 147.551 | 13.673, COMPLETE | 67.265, OOM | run-2 | run-1 | run-1 |
| Stirling-PDF / main | 48.097 | N/A | N/A | Legacy | N/A | Legacy |
| Stirling-PDF / reference | 188.843 | 25.291, COMPLETE | 114.170, OOM | run-2 | run-1 | run-1 |
| Stirling-PDF / candidate | 181.684 | 25.288, COMPLETE | 107.438, OOM | run-2 | run-1 | run-1 |
| OWASP / main | 119.209 | N/A | N/A | Legacy | N/A | Legacy |
| OWASP / reference | 857.467 | 88.639, COMPLETE | 40.109, COMPLETE | run-11 | run-11 | run-11 |
| OWASP / candidate | 870.421 | 93.900, COMPLETE | 40.263, COMPLETE | run-11 | run-11 | run-11 |

Thingsboard's candidate run-1 report barrier takes 9.433 s; the full iteration
takes 401.895 s. The frontier has 2,379,523 demand edges in 73,599 method keys,
38,017 analysed methods, 44 unresolved methods, and 102,187 DEMAND report
entries with no CONFIRMED entry. Completion here means the run-1 engine
reached its fixed point. It does not mean the later refinement finished.

OWASP is the only bidirectional project command that completes all required
refinement. Its full iteration times are below. Both latest reached and
accepted reports are **run-11**; every listed engine is COMPLETE.

| Iteration | Direction / field limit | Reference engine, s | Candidate engine, s | Reference barrier, s | Candidate barrier, s |
| --- | --- | ---: | ---: | ---: | ---: |
| run-1 | Forward / 1 | 88.639 | 93.900 | 1.828 | 1.928 |
| run-2 | Backward / 1 | 40.109 | 40.263 | 0.187 | 0.195 |
| run-3 | Forward / 2 | 32.003 | 31.962 | 1.372 | 1.395 |
| run-4 | Backward / 3 | 43.685 | 43.972 | 0.179 | 0.209 |
| run-5 | Forward / 4 | 34.492 | 34.624 | 1.527 | 1.500 |
| run-6 | Backward / 5 | 54.109 | 54.276 | 0.228 | 0.230 |
| run-7 | Forward / 6 | 38.345 | 34.886 | 1.443 | 1.440 |
| run-8 | Backward / 7 | 92.690 | 93.685 | 0.493 | 0.473 |
| run-9 | Forward / 8 | 36.472 | 34.822 | 1.397 | 1.398 |
| run-10 | Backward / 9 | 273.419 | 284.487 | 2.547 | 2.929 |
| run-11 | Forward / 10 | 36.831 | 37.438 | 1.421 | 1.571 |

## Finding comparison

The comparison keeps strict rule, method, instruction and source-span
locations separate from result multiplicity. A matched location is useful
coverage evidence. A same-method alternate return is not a strict match.
An OOM report is incomplete and cannot pass the final precision gate.

| Project | Main unique locations / occurrences | Candidate unique locations / occurrences | Main locations missing | Additional unique locations | Candidate report iteration |
| --- | ---: | ---: | ---: | ---: | --- |
| Thingsboard | 14 / 14 | 5,482 / 99,073 | 0 | 5,468 | run-1; latest reached run-2 OOM |
| Conductor | 7 / 7 | 41 / 42 | 0 | 34 | run-1; latest reached run-2 OOM |
| Stirling-PDF | 17 / 17 | 148 / 973 | 2 | 133 | run-1; latest reached run-2 OOM |
| OWASP | 4,112 / 4,112 | 4,112 / 9,179 | 0 | 0 | run-11 COMPLETE and accepted |

Conductor and Stirling-PDF have the same complete finding multisets in the
candidate and scalar reference. The two PDF missing locations are inherited;
they are not waived. The source investigation finds a concrete export fault:
the bidirectional report records the synthetic method exit, exports a Simple
trace, and the location resolver chooses the last return when no path is
available. This moves the reported controller return to another return,
including a `return null`. It does not prove coverage of the original tainted
return path. The strict location gate therefore fails for both revisions.

Thingsboard retains all 14 main locations, but its additional candidates are
large. Run-2 did not complete, so they were not fully refined. Treat them as
main-unmatched candidates, not as 5,468 individually validated false positives.
The reference has no accepted forward report; its empty export cannot support
a semantic false-negative comparison with the completed candidate run-1.

The [fresh return controls](../../../run1-flow-backed-20261024/validation/fresh-pdf-return-controls.json)
bind all three PDF SARIF files and the two project source files. Main has
one full thread flow for each missing location. Both bidirectional versions
have 18 occurrences at the EML constant error response and nine at the
Pipeline `return null`, with no code flow for these rows. This confirms the
relocation and the missing path evidence; repeated occurrences do not repair
either strict missing location.

OWASP retains all 4,112 main locations, with no additional unique location.
Its 9,179 occurrences exactly match the scalar reference's multiset. But
the strict CI trace-total check still fails: main has 4,112, and each
bidirectional version has 9,179 Simple traces. The 5,067 additional
occurrences are not an allowed callback diagnostic count. The source uses
different export keys: legacy merges by rule ID and statement; bidirectional
keeps complete bound sink keys and exports each separately. This permits
multiple rows at one public sink location. The exact bound-field difference
behind each duplicate is not recorded in SARIF. The current optimization
does not change that inherited export policy.

## Run-1 workload: Thingsboard

The candidate has a finite run-1 fixed point. Increasing event totals followed
by COMPLETE are evidence of a large workload, not a nonterminating loop in
this command. An event is an InFlight event handler, not one AP operation.
The command's run-2 OOM is a separate failure.

The fact grammar bounds one AP value. It does not bound the number of
method points, original premises, caller contexts, call stages, layers and
mark-specific relations that use it. A caller subscription retains those
coordinates so that later requests and summaries reach the correct origin.
One AP value can therefore occur in many distinct relation or subscription
keys. Current scalar candidate lookup can then visit the same geometry
again for each different mark. This is auxiliary relation work as well as
fact transport; it is not evidence of impossible AP shapes.

| Run-1 counter | Total | Scope |
| --- | ---: | --- |
| Input arrivals | 12,797,011 | Abstraction delivery attempts |
| Initial candidates / new initials | 21,324,749 / 849,362 | Canonical initial admission attempts / fresh admissions |
| Request matcher calls | 12,479,064 | Direct request lookup calls |
| Fresh request members | 4,166,425 | Cumulative authoritative membership admissions |
| Request member scans | 40,487,408 | Outgoing caller/request processing, not unique requests |
| Request answers / climbs | 8,590,654 / 8,493,175 | Cumulative request handling work |
| N2 accepted deltas / created groups | 10,366,790 / 5,494,866 | Cumulative caller subscription work, not live counts |
| Known-static-input supply leaf visits | 20,765,066 | Before scalar materialization and AP replay |
| Static supply offered / fresh temporary members | 20,954,625 / 879,697 | Deduplication within temporary actor batches |
| FULL return cleanup inputs / selected steps | 11,432,665 / 23,737,363 | Executed cleanup block input/step counters |

The initial set already rejects 20,475,387 of those 21,324,749 candidates
before starting the method body. Do not describe them as repeated full
method analyses. They still incur earlier input, projection and admission
work. Likewise, cumulative groups and member offers are not live heap rows.

The supply collector rejects 20,074,928 offered memberships as duplicates
within its current temporary batches: **95.80%** of all offered memberships.
This is not a lack of deduplication. Deduplication happens after scalar output
construction, AP composition, run-1 limits and slicing. Thus the engine can
spend substantial work to rediscover an already pending result.

The `fresh temporary` count is not a global unique count. A new actor or a
replaced batch can admit the same field/mark again. The final static service
contains only 145 supplied regions and 2,117 supplied memberships, in a
different coordinate system. Dividing 20.9 million by 2,117 would not give
a valid count of avoidable local operations.

The
[source investigation](../../../run1-flow-backed-20261024/validation/supply-avoidance-source-note.md)
identifies a restricted exact omission: inspect the existing temporary
membership before the pure known-input projection. Under the one-output
projection identity, at least 19,885,369 direct leaf visits finish in an
already pending member. This is a source-derived conditional bound, not a
measured skip count or an engine speedup. The next implementation must prove
that FULL projection identity and count actual skipped work.

### What the selected optimization actually compresses

| Candidate run-1 measurement | Thingsboard | Conductor | Stirling-PDF |
| --- | ---: | ---: | ---: |
| Raw concrete output memberships | 2,080,902 | 20,197 | 24,772 |
| Raw protected output memberships | 943,551 | 20 | 2,249 |
| Diagonal geometry rows | 86,821 | 2,120 | 518 |
| Diagonal mark rows | 1,132,328 | 3,239 | 1,540 |
| Scalar concrete rows | 18,868 | 6,678 | 2,246 |
| Neutral batch evaluations / memberships | 3,888,633 / 7,834,964 | 41,077 / 43,312 | 6,130 / 8,076 |
| Bulk store packets / memberships | 714,962 / 1,353,268 | 8,354 / 8,512 | 1,180 / 2,399 |

All rows describe completed **run-1**. All three candidate commands later
reach **run-2 OOM**. The summary census counts raw/selected summary outputs,
not all method-point facts. Thingsboard's selected protected total is one
membership larger than raw, due to conservative annotation retention.

Thingsboard has about 13.04 diagonal mark rows per geometry row. This is a
storage coordinate, not a mean premise count or runtime batch width. About
45.34% of its retained raw concrete output memberships are protected. This
does not measure the fraction of all offered outputs that could be removed.
The earlier stress-store sample was biased and had no protection flags; its
90% candidate coverage was never a whole-project deletion estimate.

The actual mean neutral batch width is about 2.015 memberships. The mean
direct bulk store packet width is about 1.893. These are smaller than the
summary geometry sharing factor. Changed work arrives in deltas; shared
storage geometry does not automatically create wide worklist batches. The
neutral evaluation counter also includes unchanged processing, so counter
differences do not directly measure no-op work or fallback costs.

The implementation reduces retained relation geometry and some publications.
It does not remove local concrete observations, request processing, caller
subscriptions, computed static supplies or all FULL return cleanup. These
remaining operations explain why fewer stored relations alone are not a
promise of a 60-second engine. Profiles below must establish their time share.

Skipping static intraprocedural facts does not skip all static-derived caller
work. A read can create `I(C.f,Ti) -> local x/Ti`; passing x to a helper uses
ordinary argument binding and caller subscriptions for that relation. Its
current value is nonstatic, while its original premise is static. This can
repeat for different marks without propagating a static current value along
the CFG. The current heap exports do not establish what fraction of caller
inputs has this origin.

## CPU, allocation and GC evidence

The candidate Thingsboard `run1.jfr` has 69,329 stacked Java execution
samples in the full 392.439 s run-1 engine window. Sampled allocation weight
is 1,840,618,863,064 bytes. This is a JFR allocation estimate, not retained
heap or an exact byte counter. There are 1,982 fully contained GC events,
with 30.017 s in summed pauses, about 7.65% of the engine interval.

| Candidate Thingsboard run-1 family | Java sample share | Interpretation |
| --- | ---: | --- |
| `enterCallees` | 39.37% | Call entry, subscription and nested replay work |
| `SubscriptionManager.subscribe` | 33.49% | Included in much of that entry work |
| Actual `JIRCallPlanBuilder` construction | 17.48% | Construction, not every cached form borrow |
| `PublicationIndex.candidates` | 6.55% | Position lookup plus publication payload construction |
| Publication borrowing | 5.18% | Included in candidate work; not an additional share |
| `satisfying` | 8.02% | Full matching across its call sites |
| Request abstraction | 5.76% | Input/request/seed handling |
| Return cleanup chain | 2.68% | Not the dominant CPU family in this recording |
| Known-static-input computed binding | 1.53% | Large offer count, small Java CPU share |

These are inclusive shares of stacked Java samples. They overlap and are
not wall-clock shares. `FormsCache.withForm` appears in 82.89% of samples
because it holds a borrowed form while the callback executes. Calling all
of that cache overhead would be wrong. Similarly, the broad protection
wrapper appears in 17.27%, but most of its sampled frames take the plain
no-mask branch. The protected ordinary replay branch has 761 recorded
frame occurrences, about 1.10 per 100 samples. Nested wrappers can repeat
a frame; this is not a distinct or exclusive CPU share. The broad wrapper
share is not flag overhead.

A second CPU-only pass reconciles the same 69,329 samples and partitions
the 27,296 `enterCallees` samples by the nearest meaningful work owner:

| Disjoint work inside `enterCallees` | Share of all run-1 Java samples |
| --- | ---: |
| Full matching | 6.15% |
| Publication materialization | 5.29% |
| IR lookup/graph work | 4.09% |
| Summary normalization/admission | 3.13% |
| Rule resolution | 2.84% |
| Static pool handling | 2.56% |
| Local AP transfer | 2.50% |
| Input admission | 1.46% |
| Candidate scanning | 1.38% |
| Summary AP application | 1.24% |

These selected rows are not the whole partition. Only three call-plan
construction samples occur under this entry cohort. Therefore its costs
and the separate builder family must not be confused. The profile supports
reducing scalar caller joins and materialization. It does not show that
all of this work is redundant or eligible for one bulk packet.

The independent native window covers run-1 engine +60 to +90 seconds.
It contains 40,776 sample weights. It confirms entry, subscription, matching,
publication borrowing and call-plan construction as hot families. GC-worker
ancestry accounts for 38.44% and JIT ancestry for 3.51% of that window's
weights. These include concurrent VM work omitted from Java execution
samples. They do not mean a 38.44% stop-the-world pause or wall-time share.
Allocation reduction can therefore matter beyond its direct Java CPU cost.

Direct static supply composition contributes 8.70% of sampled allocation
weight but only about 1.06% of Java samples. Avoiding its duplicate projection
is useful allocation work; it is insufficient as the sole CPU explanation
or a basis for a two-times engine promise. The next proposal ranks the
caller pipeline above this small direct CPU scope.

The bounded decoder reads one event at a time. Official JDK `jfr print`
reproduces a checked method/line/BCI stack, and native sampling independently
confirms the broad hot families. Recorded stack names and sampling are
still observations, not proofs of exact operation counts.

All 12 profile leaves are decoded and bound to their source and engine
windows in the [profile report](../../../run1-flow-backed-20261024/validation/profiles-analysis.md)
and [machine-readable receipts](../../../run1-flow-backed-20261024/validation/profiles-analysis.json).
There are no decoder failures. The GC log independently records 2,057
completed run-1 pauses totalling 30.102 s for candidate Thingsboard. Its
event/boundary policy differs from the JFR GC-cycle policy, so the two pause
counts need not match.

| Project / side | Run-1 Java samples | Sampled allocation weight, GiB | JFR GC pauses, s | Latest reached / COMPLETE / accepted |
| --- | ---: | ---: | ---: | --- |
| Thingsboard / reference | 43,250 | 841.122 | 48.403 | run-1 OOM / none / none |
| Thingsboard / candidate | 69,329 | 1,714.210 | 30.017 | run-2 OOM / run-1 / run-1 |
| Conductor / reference | 3,910 | 40.416 | 0.851 | run-2 OOM / run-1 / run-1 |
| Conductor / candidate | 4,191 | 41.841 | 0.885 | run-2 OOM / run-1 / run-1 |
| Stirling-PDF / reference | 4,944 | 66.975 | 0.845 | run-2 OOM / run-1 / run-1 |
| Stirling-PDF / candidate | 4,974 | 67.627 | 0.871 | run-2 OOM / run-1 / run-1 |
| OWASP / reference | 4,624 | 131.817 | 2.385 | run-11 / run-11 / run-11 |
| OWASP / candidate | 4,822 | 138.062 | 2.550 | run-11 / run-11 / run-11 |

The reference Thingsboard row is an incomplete run-1 prefix; its engine
also includes the blocking OOM snapshot. Its lower total allocation is not
an equal-progress improvement over the completed candidate. For the other
three projects both rows cover complete run-1 engines.

Conductor and PDF spend 52.71% and 58.20% of candidate run-1 Java samples
under real call-plan construction. Their summary candidate/matching shares
are small. OWASP's builder share is 27.71%. Construction occurs on a payload
miss, but the final form census mixes run-1 and run-2. It does not distinguish
necessary first builds from repeat builds after reference loss. Do not
propose a cache rewrite on the assumption that every build is redundant.

Conductor and PDF finish run-1 before the requested +60-second native trigger;
their native windows are unavailable, not zero. Candidate OWASP has a pure
run-1 native window. The reference OWASP native window crosses the end of
run-1 and is excluded from run-1 totals. Reference Thingsboard's run-1 dump
returned code zero with `No data`: it is a failed capture. Its continuous
recording and pure native run-1 window are separately valid. No project
lasts to its near-time-limit native trigger. Continuous recordings retain
the other observed phases; any rollover/window limits are explicit in the
receipts. Main profile rows use the legacy full-scan phase, never a run-1
label.

## OOM snapshots and physical owners

Six MemoryManager OOM snapshots are present. Main has no OOM. Snapshot byte
length is not physical retained Java heap size: HPROF encoding and references
have a different layout. A class histogram is not an exclusive owner census.
Retained owner unions can overlap and must not be added.

| Side / project | Snapshot run | Heap used at guard, GiB | HPROF length, bytes | Latest COMPLETE / accepted |
| --- | --- | ---: | ---: | --- |
| Reference / Thingsboard | run-1 | 10.832 | 18,247,563,637 | None / none |
| Candidate / Thingsboard | run-2 | 10.832 | 18,269,653,083 | run-1 / run-1 |
| Reference / Conductor | run-2 | 7.215 | 11,613,655,395 | run-1 / run-1 |
| Candidate / Conductor | run-2 | 7.219 | 11,592,504,624 | run-1 / run-1 |
| Reference / Stirling-PDF | run-2 | 7.219 | 12,045,961,075 | run-1 / run-1 |
| Candidate / Stirling-PDF | run-2 | 7.221 | 12,019,286,735 | run-1 / run-1 |

Candidate snapshots are all from run-2. They must not be used as live current
run-1 owner censuses. Run-1 actors and their packed stores can already be
released. The completed run-1 census and time-filtered profiles supply the
current run-1 evidence. The reference Thingsboard snapshot describes an
incomplete scalar run-1; it is not a same-progress candidate comparison.

That reference run-1 heap has 1,743 live `InitialAp` objects, 12,253,324
`TaintTree` headers, 3,559,231 trie nodes, 4,160,328 `GroupKey` objects and
3,802,804 caller input Entry/Key pairs in 158,830 accumulators. It has
72,343 method edge stores, including ZERO/control-only analysis. These are
physical object counts, not equal coordinates or unique semantic fact counts.
The small initial domain does not bound final local bases, stored method
points or caller-qualified relations. The export does not classify each
caller row as FLOW/TAINT or as an eligible diagonal cohort. That remains
unknown; the next proposal does not label all 3.8 million rows packable.

The exact retained owner unions for this incomplete run-1 include 2.668 GB
for method execution, 0.869 GB for raw/selected summaries, 1.519 GB for
publications/subscriptions, 0.474 GB for static services/points and 0.723 GB
for method forms. These decimal GB values overlap. They show substantial
relation and caller machinery in addition to the AP grammar. They cannot
be added to obtain an exclusive heap partition.

The same heap has 4,087,846 `TaintMethodExitSink` objects. The
[source check](../../../run1-flow-backed-20261024/validation/exit-sink-retention-source-note.md)
shows that these are final reporting rules, not the ignored after-sink
tracking actions. Ignoring `trackFactsReachAnalysisEnd` empties an action
list; it does not remove a reporting sink. Strong resolver caches and
original/selected rule copies are possible retention paths, but this export
has no per-sink incoming-field census. Their exact contribution is unknown.
The count does not justify dropping exit rules or changing their premises.

All six reports pass their source/layout/query controls: 18 queries per
reference report and 33 per final candidate report. The
[physical summary](../../../run1-flow-backed-20261024/validation/source-bound-heap-summary.json)
binds each HPROF, source layout, query validation and report archive by hash.
The [heap analysis](../../../run1-flow-backed-20261024/validation/source-bound-heap-analysis.md)
gives the per-capture layout and ownership limits.
No query cap or missing schema is treated as an empty store. The six original
captures were analysed serially; the expanded Conductor report reuses its
closed heap and cached index.

The table uses decimal GB. Each owner column is an exact retained union of
the named classes; these columns overlap and must not be added.

| Side / project | Snapshot | Physical heap | Method execution | Raw/selected summaries | Publication/subscriptions | Incoming demand/queries | Static service/points | Forms |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Reference / Thingsboard | run-1 | 11.361 | 2.668 | 0.869 | 1.519 | 0.000 | 0.474 | 0.723 |
| Candidate / Thingsboard | run-2 | 11.388 | 2.184 | 0.701 | 1.226 | 0.923 | 0.000 | 0.927 |
| Reference / Conductor | run-2 | 7.613 | 1.611 | 0.456 | 0.834 | 0.077 | 0.000 | 0.214 |
| Candidate / Conductor | run-2 | 7.617 | 1.611 | 0.458 | 0.851 | 0.073 | 0.000 | 0.214 |
| Reference / Stirling-PDF | run-2 | 7.615 | 3.851 | 0.472 | 0.755 | 0.054 | 0.000 | 0.221 |
| Candidate / Stirling-PDF | run-2 | 7.625 | 3.804 | 0.477 | 0.779 | 0.053 | 0.000 | 0.224 |

Conductor's two run-2 snapshots have almost the same retained-owner scale.
PDF's largest measured dataflow owner is method execution, about 3.8 GB in
both versions. The remaining OOMs are large scalar later-run states; the
selected compact mechanism is enabled only for FULL run-1. Candidate
`FlowBackedSummaries`, `DiagonalRelations` and compact mask owner counts are
zero in all three run-2 snapshots. That is not a same-progress memory
comparison with the reference Thingsboard run-1 failure.

| Candidate run-2 snapshot | Scalar TAINT headers | Headers with non-null annotation | Extra shallow bytes versus 32-byte headers at the same count |
| --- | ---: | ---: | ---: |
| Thingsboard | 9,521,644 | 0 | 76,173,152 |
| Conductor | 6,798,991 | 0 | 54,391,928 |
| Stirling-PDF | 12,175,260 | 81 | 97,402,080 |

The class layout grows from 32 to 40 bytes per TAINT header. A null annotation
still occupies its field and padding. The eight-byte same-count overhead is
about 0.67–1.28% of these physical heaps. It is a real cost of the change,
but does not explain the multi-GB owner state. The PDF residual annotations
must not be generalized away: their exact owning paths are not established
by this export. Zero compact owners does not mean zero layout cost or zero
retained annotation objects.

IR RAM storage is also substantial. It is the largest single dominator in
the Conductor pair, about 2.25 GB, and retains about 0.98 GB in PDF. The
candidate Thingsboard instance retains about 2.25 GB. IR storage remains
outside the optimization scope. These values are individual dominators,
not additional disjoint columns to add to the owner table.

## Acceptance and next action

Implementation and local validation are complete. The fresh common suite
has 1,896 passing tests; JVM has 440, Go has 1,323 and configuration equality
has five. The application suite has the same 11 failures and 13 skips among
1,034 cases on both sides, with exact failed assertions and case multisets
checked. The Lean build checks 460 declarations and 32 executable controls,
with no unexpected axioms. This does not prove the complete Kotlin/IR engine.
The selected AP proofs and direct controls use the original AP operations;
the general runtime still has inherited StrongQueries usage.

The selected iteration's implementation, measurements and next proposal are
complete. The project acceptance gates do not all pass: Thingsboard and
OWASP exceed 60 seconds in run-1; all three real projects later OOM in run-2;
PDF has two strict missing main locations; OWASP exceeds its CI occurrence
count; Thingsboard has many unrefined additional candidates.

The next proposal ranks exact mark-mask call processing first, with a required
cohort census before implementation. Early incompatible-mark rejection is a
smaller supported step in the same hot pipeline. Entry admission and duplicate
static supply projection follow. No current measurement establishes a
two-times engine improvement. The next iteration must retain the current
rule, field, cleaner, initial grammar and handoff contracts rather than
remove necessary work to improve a counter.
