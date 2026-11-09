# Run-11 cutoff: final validation and workload report

9 November 2026. Measured runtime: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
This report replaces the pending validation record for that change. It also
replaces old current-runtime measurements for selection of the next iteration.
The fixed main baseline remains `54ad708fe1c4f551956d3d572866de1534415fa1`.

The default run-11 cutoff works. The fresh rule-test gate passes. The project
acceptance gate does **not** pass: Conductor and Stirling-PDF time out,
Thingsboard has an OOM before its first accepted report, and the broad root
native suite has 20 failures. No unselected core fix was added to hide them.

## Selected behavior and source scope

All default bidirectional scans stop after the complete forward **run-11**
barrier. An earlier empty-demand stop still has priority. Field limits remain
`1,1,2,3,...,10`; time and memory budgets are unchanged. The legacy
`--iteration-limit` remains ignored with a diagnostic on this engine.

At RUN_LIMIT, return confirmed findings plus provisional targets from the
**latest completed forward run only**. Do not restore targets discarded by
refinement on earlier runs. Confirmed findings take priority for the same
physical sink. SARIF marks a provisional finding with `opentaint:provisional`
and the notice “Provisional finding. Later refinement may discard this finding.”
Fingerprints and rule identities remain unchanged.

This is a selected execution/reporting change. It is not a fixed-point proof.
Transfer, C2 initial admission, C5 summary restriction, FULL marks, statics,
loops, protection and demand storage have no additional change. The source
audit verifies byte equality for all 76 AP/store operators and the three loop
observation/restriction sources between the prior and measured runtimes.

A failure before the atomic report commit preserves the prior snapshot.
Existing memory-guard cleanup can fail after that commit. In that case the
accepted NORMAL reports survive an abnormal end. Provisional output remains
disabled for timeout, OOM and other abnormal ends.

See the [specification](../../spec/bidirectional-run11-cutoff.md),
[implementation proposal](../design/bidirectional-run11-cutoff-implementation-20261109.md)
and [constructive proof package](../../spec/lean/proposals/run11-cutoff-20261109/README.md).

## Project outcome

“Reached” means that an engine started. “Complete” means its engine completed.
“Accepted forward” means that a completed forward result was committed.
Peak RSS includes native memory; it is not the configured Java heap.

| Project | End | Reached | Complete | Accepted forward | Confirmed / provisional | Command wall s | Peak RSS GiB |
| --- | --- | --- | --- | --- | ---: | ---: | ---: |
| OWASP | OK/RUN_LIMIT | run-11 | run-11 | run-11 | 2633 / 0 | 242.364 | 9.903 |
| conductor | TIMEOUT/ABNORMAL | run-8 | run-7 | run-7 | 7 / 0 | 1122.013 | 10.205 |
| thingsboard | OOM/ABNORMAL | run-1 | none | none | 0 / 0 | 373.917 | 13.860 |
| Stirling-PDF | TIMEOUT/ABNORMAL | run-11 | run-10 | run-9 | 32 / 0 | 1108.552 | 9.910 |

OWASP alone completes the new cutoff. Conductor and Stirling retain their
earlier accepted confirmed reports after timeout. Thingsboard has no accepted
iteration. No project emits a provisional result in this campaign. The project
wrapper exits zero because orchestration finished; this does not make its
three failed analyses successful.

All four commands use source Gradle `:runProjectAnalyzer`, not the CLI.
OWASP uses the CI project, 8g and 1000 seconds. Conductor and Stirling use 8g
and 1080 seconds. Thingsboard uses 12g and 1080 seconds. The configured project
models, aliases, static propagation, FULL mode, test revision and field-limit
schedule match the prior campaign. All source/configuration parity checks pass.
Projects ran serially. No heavy heap decode ran during these measurements.
The [data record](data/bidirectional-run11-cutoff-validation-20261109.json)
embeds exact manifests, commands, JVM options and all iteration rows.

## Findings and fixed-main comparison

The baseline was run once after the user's instruction to run it. This final
campaign reuses those results. Main uses the legacy engine, so it has no
bidirectional run label. It must not be called run-0.

Comparison uses exact rule, path, full source region, method, instruction index
and instruction text. All current finding locations and identities are
**identical to the pre-cutoff bidirectional output** at `9b21b3716`.
The new cutoff introduces no observed location loss or addition in these four
outputs. This is not a proof about paths not analyzed before a timeout.

| Project | Main end | Main wall s | Main findings | Exact shared | Main only | Current only |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| OWASP | OK | 156.357 | 2633 | 2633 | 0 | 0 |
| conductor | OOM | 187.389 | 7 | 7 | 0 | 0 |
| thingsboard | OOM | 439.652 | 15 | 0 | 15 | 0 |
| Stirling-PDF | OK | 52.109 | 24 | 16 | 8 | 16 |

OWASP preserves all 2,633 exact locations. Conductor preserves all seven
exported baseline locations, but its baseline is itself an OOM result and its
current scan is incomplete. That comparison cannot establish whole-project
absence of false negatives.

Thingsboard loses 15 exported baseline findings because run-1 never commits.
This is a real output/acceptance failure. It does not establish 15 separate
transfer bugs. The retained catalog's 11 NORMAL witness IDs are also not 11
accepted findings.

Stirling has 16 exact matches, eight baseline-only locations and 16 current-only
locations. Each of the eight missing locations has a current exit-rule report
with the same rule and full method at another physical return. The synthetic
exit descriptor selects a physical return without witnessed path provenance.
This explains the relocation candidate, but does not prove equivalence of
every source path. Keep the eight exact losses visible. Eight additional
current reports are in other methods; they are not classified as false
positives without a path investigation.

The complete compressed finding packet below includes every baseline, old and
new finding row, fingerprints, full locations and all comparison keys.

## Native and rule-test gates

| Native gate | Tests | Failures | Skips | Result |
| --- | ---: | ---: | ---: | --- |
| Full common dataflow | 2,550 | 0 | 0 | Pass |
| Full JVM dataflow | 467 | 0 | 0 | Pass |
| Focused SARIF and legacy-option checks | 4 | 0 | 0 | Pass |
| Broad root suite with bidirectional opt-in | 1,083 | 20 | 11 | Failed |

All 11 earlier measured finding failures remain with the same expected and
actual finding sets. The broader command adds five inherited cleaner-matrix
duplicates, three legacy iteration-limit assertions and one old implicit
root/element-position assertion. These nine were newly covered by this
command; they are not established new runtime regressions. No test was
weakened, excluded or waived. Full identities, messages and comparison receipts
are in the data record.

The native cutoff case reaches, completes and commits run-11 without creating
run-12. Tests with explicit finite policies retain those policies; the broad
root suite is not claimed to reach run-11 in every case.

The Lean 4.35 package passes 22 local laws and five executable examples. It
proves finite cutoff control and report/snapshot selection. It uses no
`Classical.choice`, `sorry` or added axioms. Standard extensionality/quotient
lemmas are recorded in the axiom receipts. It does not prove a concrete path
for a provisional target or equivalence to unlimited refinement.

The fresh source-only Java/Go rule campaign runs both `:runProjectAnalyzer`
and `:checkRuleTestResults`. The actual Gradle gate exits zero in **85.943 s**:

```text
Rule tests: OK 786 | Skip 0 | FP 0 | FN 0 | Disabled 22
```

| Language | Successful | Disabled | Declared | Collected |
| --- | ---: | ---: | ---: | ---: |
| Java | 585 | 22 | 609 | 607 |
| Go | 201 | 0 | 201 | 201 |
| Total | 786 | 22 | 810 | 808 |

All 585 executable Java cases actually start on BIDIRECTIONAL and complete:
583 stop with NO_DEMAND_EDGE and two with RUN_LIMIT. Go uses its existing
engine. No Java run exceeds run-11. The two RMI interface declarations
`DangerousRemoteService#invoke` and `SafeRemoteService#invokeById` remain
uncollected because the fixture selector excludes their abstract/interface
classes. They are coverage gaps, not passed or disabled tests.

| Capped Java case | Reached / complete / accepted forward | Driver time | Confirmed / provisional |
| --- | --- | ---: | ---: |
| `UnsafeFileUploadServlet#doPost` | run-11 / run-11 / run-11 | 403.048 ms | 1 / 0 |
| `PassthroughFileModelSamples#fileToStringUnsafe` | run-11 / run-11 / run-11 | 36.904 ms | 1 / 0 |

The old uncapped Upload timed out after reaching run-1275423, completing
run-1275422 and accepting forward run-1275421. The old File case was stopped
as superseded at reached run-524406, complete/accepted forward run-524405.
All 360 completed old-prefix cases retain the same confirmed count. That
prefix is not a full unbounded-suite baseline.

Actual SARIF has 519 results: 340 JVM confirmed identities across independent
cases and 179 Go findings. It has zero provisional tags. Three separate native
SARIF tests verify a positive provisional result and its serialized tag; the
real rules campaign does not exercise that positive path. No warning/OOM
event or memory capture occurs in the fresh rule campaign.

## Iteration times and demand frontiers

Engine time excludes joined static completion. The barrier column is the
later handoff/report barrier. Joined static completion is separate and also
contributes to total iteration time: about 0.344 s on OWASP run-1, 1.530 s on
Conductor run-1 and 0.424 s on Stirling run-1. Thingsboard does not reach it.
For example, Conductor run-1 has 18.213 s engine time, 1.530 s joined static
completion and 1.803 s barrier time, plus small logging gaps: 21.562 s total.

Handoff patterns include DATA and controls. Raw Target demand is a different
counter and can include nested blocks. Do not subtract it from handoff patterns
to infer DATA cardinality. Counts alone do not prove convergence or cost.

### OWASP

Latest reached **run-11**; complete **run-11**;
accepted forward **run-11**.

| Iteration | Direction | Field limit | Engine status | Engine s | Barrier s | Handoff patterns | Raw Target demand | Confirmed |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD | 1 | COMPLETE | 80.721 | 2.380 | 68063 | 6929 | 2120 |
| run-2 | BACKWARD | 1 | COMPLETE | 25.336 | 0.732 | 20234 | 1965 | 2120 |
| run-3 | FORWARD | 2 | COMPLETE | 9.100 | 0.788 | 1064 | 1129 | 2633 |
| run-4 | BACKWARD | 3 | COMPLETE | 4.150 | 0.560 | 2233 | 481 | 2633 |
| run-5 | FORWARD | 4 | COMPLETE | 3.258 | 0.576 | 947 | 898 | 2633 |
| run-6 | BACKWARD | 5 | COMPLETE | 5.724 | 0.558 | 2021 | 430 | 2633 |
| run-7 | FORWARD | 6 | COMPLETE | 3.127 | 0.572 | 975 | 923 | 2633 |
| run-8 | BACKWARD | 7 | COMPLETE | 7.475 | 0.504 | 2100 | 430 | 2633 |
| run-9 | FORWARD | 8 | COMPLETE | 4.453 | 0.532 | 975 | 923 | 2633 |
| run-10 | BACKWARD | 9 | COMPLETE | 6.161 | 0.573 | 2100 | 430 | 2633 |
| run-11 | FORWARD | 10 | COMPLETE | 3.142 | 0.560 | 975 | 923 | 2633 |

### conductor

Latest reached **run-8**; complete **run-7**;
accepted forward **run-7**.

| Iteration | Direction | Field limit | Engine status | Engine s | Barrier s | Handoff patterns | Raw Target demand | Confirmed |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD | 1 | COMPLETE | 18.213 | 1.803 | 127044 | 7921 | 2 |
| run-2 | BACKWARD | 1 | COMPLETE | 33.642 | 2.423 | 477645 | 206 | 2 |
| run-3 | FORWARD | 2 | COMPLETE | 8.776 | 0.880 | 17574 | 3745 | 5 |
| run-4 | BACKWARD | 3 | COMPLETE | 145.882 | 0.733 | 30841 | 39 | 5 |
| run-5 | FORWARD | 4 | COMPLETE | 10.193 | 0.710 | 30684 | 3942 | 7 |
| run-6 | BACKWARD | 5 | COMPLETE | 446.449 | 1.313 | 151443 | 39 | 7 |
| run-7 | FORWARD | 6 | COMPLETE | 185.386 | 1.016 | 90179 | 4501 | 7 |
| run-8 | BACKWARD | 7 | TIMEOUT | 193.522 | not complete | — | — | — |

### thingsboard

Latest reached **run-1**; complete **none**;
accepted forward **none**.

| Iteration | Direction | Field limit | Engine status | Engine s | Barrier s | Handoff patterns | Raw Target demand | Confirmed |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD | 1 | OOM | 218.517 | not complete | — | — | — |

### Stirling-PDF

Latest reached **run-11**; complete **run-10**;
accepted forward **run-9**.

| Iteration | Direction | Field limit | Engine status | Engine s | Barrier s | Handoff patterns | Raw Target demand | Confirmed |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| run-1 | FORWARD | 1 | COMPLETE | 20.402 | 0.792 | 66172 | 6105 | 7 |
| run-2 | BACKWARD | 1 | COMPLETE | 12.657 | 1.414 | 265835 | 602 | 7 |
| run-3 | FORWARD | 2 | COMPLETE | 3.703 | 0.891 | 1726 | 743 | 28 |
| run-4 | BACKWARD | 3 | COMPLETE | 3.902 | 0.602 | 4849 | 295 | 28 |
| run-5 | FORWARD | 4 | COMPLETE | 1.003 | 0.686 | 1356 | 371 | 32 |
| run-6 | BACKWARD | 5 | COMPLETE | 7.460 | 0.592 | 1333 | 100 | 32 |
| run-7 | FORWARD | 6 | COMPLETE | 22.223 | 0.667 | 1092 | 252 | 32 |
| run-8 | BACKWARD | 7 | COMPLETE | 17.427 | 0.703 | 1138 | 40 | 32 |
| run-9 | FORWARD | 8 | COMPLETE | 574.465 | 0.863 | 986 | 178 | 32 |
| run-10 | BACKWARD | 9 | COMPLETE | 18.021 | 0.627 | 1133 | 39 | 32 |
| run-11 | FORWARD | 10 | TIMEOUT | 368.624 | not complete | — | — | — |

The cutoff reduces OWASP command wall time from the prior bidirectional
timeout of about 1037.5 s to 242.4 s. This is bounded execution, not a faster
transfer algorithm or proved convergence. The other projects retain the same
large workload categories. Conductor run-6 is 446.4 s versus 438.3 s before;
Stirling run-9 is 574.5 s versus 554.1 s before. Single-run differences and
different capture/scheduling points do not prove a causal cutoff regression.

## CPU and allocation: different projects have different causes

Continuous JFR starts with each process. Conductor run-4/run-6/run-8 snapshot
phase counts and disjoint scopes exactly match the continuous recording.
Other snapshot inventory checks verify metadata and coverage. Prefix events
are not added to totals. There are 31 engine rows. Async CPU windows cover
normal workload and the long near-budget engines.
All decoders and profilers are terminal. Weighted JFR allocations estimate
churn; they are not live retained memory. Java execution percentages and async
all-thread CPU percentages have different denominators.

| Phase | Engine s | Java samples | Main disjoint work | Sampled allocation GB | GC pause s |
| --- | ---: | ---: | --- | ---: | ---: |
| Conductor run-4 BACKWARD | 145.882 | 3,012 | virtual-loop C2 24.17%; other observation 17.13% | 451.36 | 0.909 |
| Conductor run-6 BACKWARD | 446.449 | 14,424 | virtual-loop C2 36.72%; calls 19.72% | 1296.48 | 3.296 |
| Conductor run-8 BACKWARD | 193.522, timeout | 15,683 | virtual-loop C2 83.85% | 367.88 | 0.939 |
| Stirling run-9 FORWARD | 574.465 | 28,772 | actual saved replay 56.12%; virtual saved application 18.75% | 1617.13 | 2.868 |
| Stirling run-11 FORWARD | 368.624, timeout | 17,536 | actual saved replay 42.80%; virtual saved application 24.15% | 1019.80 | 2.070 |
| Thingsboard run-1 FORWARD | 218.517, OOM | 45,848 | calls 44.91%; delivery 7.39% | 1022.53 | 51.978 |

Conductor's late backward hot path repeatedly tests virtual loop-prefix
candidates with C2 before selecting a restriction. The last 30 seconds of
run-8 have 94.40% of Java samples in that C2 category. Ordinary C5 is only
1.90% over the whole run. The cost is constructing/querying candidate
observations, not just the small final demand frontier. A captured compatible
trie query visits 4,666 terminals although only two can emit for its tail.
That is a real avoidable search family, not a measured global 2,333-fold gain.

Stirling's late forward hot path differs. Actual saved-summary replay and
virtual saved-summary applications account for most work. In run-9/run-11,
`Intrinsics.areEqual` is the sampled leaf in 26.72%/21.20%; trie child mapping
and subtraction dominate allocations. Ordinary C5 is approximately 0.01%.
GC pause is small relative to engine duration. The profile does not count
which replay offers are duplicates, so a delta-based replay saving must still
be measured. A small handoff frontier does not bound saved-provider fanout or
the number of virtual observations.

Do not label the enclosing `FormsCache.withForm` callback as form construction.
The narrow payload-build scope is only 0.43%/0.12%/0.06% in Conductor
run-4/run-6/run-8 and 0.07%/0.13% in Stirling run-9/run-11. Cache rebuilding
cannot explain these late stalls. It remains relevant early: payload building
is 62.47% of Conductor run-1, 32.69% of Thingsboard run-1 and 50.26% of OWASP
run-1. These inclusive scopes overlap rule binding and alias analysis.

OWASP run-11 still allocates an estimated 8.03 GB. Its narrow payload-build
scope is 22.63%, but there are only 137 Java samples. Repeated condition
compiler/predicate allocation is a secondary candidate, not evidence for the
late Conductor/Stirling cause.

The run-11 witness/catalog work is about 0.01% in Thingsboard. No
ReportCatalog monitor wait is recorded above the configured JFR threshold.
This does not prove zero CPU cost or absence of shorter waits.

## Rule binding serializes early cache misses

`TaintConfiguration.ResolverView.cached` checks its cache, then holds
`synchronized(cache)` while it resolves a missing method. The cache is shared
per storage kind, so misses for different methods can block one another.
The unresolved-call callback is a different mechanism.

| Project | Aggregate blocked thread seconds at this resolver | Dominant phases |
| --- | ---: | --- |
| OWASP | 2.508 | prescan/run-1 |
| Conductor | 157.307 | prescan 148.274; run-1 9.399 |
| Thingsboard | 610.909 | prescan 418.850; run-1 198.461 |
| Stirling | 107.249 | prescan 67.183; run-1 40.128 |

These are sums over blocked threads and differently classified event windows,
not elapsed wall-time additions; phase-window totals can differ slightly.
No such waits are recorded in the late Conductor or Stirling engines above.
A per-key binding design may improve early scaling, but does not solve the
measured late loop work. Resolver thread safety, reentrancy and epochs need
proof before that change.

## Thingsboard run-1: retained state and exact multiplicity

The OOM heap has **309,054,681 reachable objects / 11,375,418,560 bytes**.
The 18,568,670,081-byte HPROF also includes file overhead and unreachable data.
The offline parser's larger heap is a decode setting, not an analyzer rerun.

| Disjoint top-level owner | Retained bytes | Share |
| --- | ---: | ---: |
| UnitRunner | 4,343,927,952 | 38.19% |
| IR RAM storage | 1,618,623,720 | 14.23% |
| SubscriptionManager | 981,979,984 | 8.63% |
| RunManager | 888,069,432 | 7.81% |
| Bound rule provider | 801,212,672 | 7.04% |
| Method entries | 773,642,496 | 6.80% |

IR storage is out of scope. Nested owner sizes overlap this partition and
must not be added to it. The global static service is only 57.46 MB, with
1,023 FLOW writer rows. The large fanout lives in call-point/request/input
state outside that service.

### Input state is not one subscription population

The complete typed owner query splits 4,093,620 AddedFactAccumulator entries:

| Role | Entries | Pure identity-mark eligible | Exact mark-erased templates | Scalar fallback |
| --- | ---: | ---: | ---: | ---: |
| Callee subscription inputs | 3,437,574 | 2,904,846 | 299,300 | 532,728 |
| Unresolved-call diagnostic observations | 656,046 | 655,214 | 60,146 | 832 |
| Total | 4,093,620 | 3,560,060 | 359,446 | 533,560 |

Identity eligibility keeps the exact accumulator owner, caller/callee method,
call point/stage/scope, original/current geometry, layers, exclusions and both
protection memberships. Only the paired full mark `(T,T)` becomes a parameter.
It does not erase mark identity or introduce a mark group. The complete packet
has all 4,426 collision-free shape definitions, 22 multiplicity rows and 12
native examples; the largest displayed packs contain 28 FULL marks.

The eligible relation family has a 9.904-fold logical row quotient. Including
fallback gives 893,006 entries, a 4.584-fold whole-population quotient. These
are **entry counts, not heap or speed predictions**. Entry+Key shallow bytes
are 196,493,760; other retained owners remain. Existing `NeutralRelationBatch`
provides exact identity-mark packing, but extending its ownership/view path
requires a new proof and tests. No such runtime change was made.

The diagnostic observation archive has a separate avoidable-work cause.
`JIRInterpreter` always implements `UnresolvedCallObserver`, even when
`externalMethodTracker` is null. The common engine therefore stores complete
TAINT observations before calling a callback that returns immediately.
The measured commands do not enable `--track-external-methods`. These 656,046
entries serve no enabled observation in this configuration. With tracking on,
the consumer needs method/position/pass-rule information and a diagnostic
callback count; it does not return transfer or demand facts. A capability
check can skip the disabled store. A compact enabled view needs its own
observation-preservation proof; callback counts may vary as already agreed.

### Pending static-derived mark requests

There are **2,827,665 pending FULL-mark memberships at 102,081 points**;
91.525% are at CallStageInput. `TenantId.tenants` and
`TenantId.SYS_TENANT_ID` account for 2,613,482 memberships (92.425%). The first
is a mutable canonicalizing map; the second is an identity obtained through
it. They are not enum constants, so the enum-alias filter cannot remove them.

90,206 points already share one immutable image root across their marks.
At some points, equal geometry instead has many distinct roots. A native
example is:

```text
AccessValidator#validateApiUsageState, CallInst31, line319, stage3
original: S.TenantId.SYS_TENANT_ID.*/FLOW, E={}, mx={}
current:  this.{ValidationCallback.action, ValidationCallback.response}.[any]/FLOW
layer:    DEMAND
pending:  221 FULL marks from13 top-level groups
```

This point has 221 distinct roots with the same complete two-path geometry.
Other samples already share one root. Across the population, per-mark logical
leaf counting is 4,616,532 versus 193,806 distinct per-point coordinates, a
23.8204-fold logical repetition. That is not a physical memory multiplier.
PendingFlowImages wrappers occupy 45,242,640 shallow bytes and 71,748,272 bytes
as the sum of individual retained sizes; 93.67% retain only their 16-byte
wrapper. Merging them can avoid union work and wrappers, but cannot alone
explain or remove the entire 11.38 GB reachable heap.

### Rules and the new report observer

There are 4,083,550 bound exit-sink objects, 196,010,400 shallow bytes, from
129 serialized exit-sink templates. The rule-provider owner retains 801.21 MB.
This supports avoiding eager full binding for prescan discovery. It does not
justify dropping negative guards, metadata or context-dependent eligibility.

The new reached-report sets have 6,696 memberships; 65,649 of 72,294 unique
sets are empty. Their individual retained-size sum plus the catalog retained
size is 6,599,776 bytes, about 0.0580% of reachable heap. This is owner-subtree
accounting, **not** a joint-removal incremental-size bound. It does not show a
new multi-gigabyte observer cause. The older OOM snapshot has the same major
owners and static-derived mark fanout. Different schedules and GC points do
not support a precise before/after retained-byte ratio.

## Remaining correctness and design limits

The selected cutoff bounds iteration count. It does not settle the intrinsic
Target/source-demand cycles found in the old uncapped rule campaign. The two
capped rule cases both have confirmed findings; neither proves arbitrary
provisional candidates are feasible concrete paths.

Three unresolved acceptance areas remain explicit: exact-root selected
cleaning with uniform-taint source queries; scoped Spring ZERO guidance at
block ports; and honest physical exit locations. The native failures are
retained as evidence. A future repair needs a separate selected contract and
counterexample-driven proof. No GroundingSupport, field semantics change,
SoftReferenceManager rewrite, WeakIdentityCache, blanket ZERO scan or new
tail kind was introduced.

## Next iteration and reproducible evidence

The [new ranked proposal](../design/bidirectional-run11-next-iteration-20261109.md)
separates three workload families: prune rejected loop C2 searches on
Conductor; avoid exact per-mark input/journal expansion on Thingsboard; and
test delta-based saved replay against Stirling's existing input groups.
It keeps technical representation changes separate from algorithmic work
avoidance and from unresolved semantic fixes. These changes are proposals,
not part of the measured runtime.

The reported counters, all finding rows and full native failure messages are
stored in the repository. The gzip files preserve complete parsed JSON
packets. Profile function/allocation rankings are top-30 and stack examples
are bounded; all per-engine/disjoint-scope tables and source hashes are
included. Their SHA-256 below is for the decompressed JSON; compressed hashes
are in the main data record. Use `gzip -dc <path>` to inspect them.

| Packet | JSON bytes | gzip bytes | JSON SHA-256 |
| --- | ---: | ---: | --- |
| [bidirectional-run11-rule-validation-20261109.json.gz](data/bidirectional-run11-rule-validation-20261109.json.gz) | 1,977,780 | 102,567 | `332033dfbea82e8b44d6a0540f021c36743aaa4e8986939ce504d9fb2ae4ad78` |
| [bidirectional-run11-profiles-20261109.json.gz](data/bidirectional-run11-profiles-20261109.json.gz) | 3,928,946 | 349,497 | `56872e4b972b9953d1f08267a96470219605b1d855e8cd72f2086f48e2d4c23a` |
| [bidirectional-run11-thingsboard-memory-20261109.json.gz](data/bidirectional-run11-thingsboard-memory-20261109.json.gz) | 25,755,064 | 939,815 | `16146a33c166983642c34c9270a6a279ca30e16d3ffad99dba3322acebb76b4b` |
| [bidirectional-run11-findings-20261109.json.gz](data/bidirectional-run11-findings-20261109.json.gz) | 19,830,387 | 1,402,471 | `c0b7a7cf9146e1d3e41ef768bfd24888d25e647eaf86527fe6e5b59fdf393bbc` |

The main data record also embeds fresh command manifests, fixed-main
summaries, final rule audit, all 31 engine rows, native triage and proof
receipts. Original captures remain external; the parsed evidence is embedded.
Cleanup removed 135 older decoded HPROF/JFR/MAT files (163,138,998,423 bytes)
after checking retained decoded counterparts. Four older unparsed baseline
heaps remain because they have no exact decoded replacement. Current raw
captures and all current decoded evidence were preserved. No analyzer,
profiler or memory query remains active.
