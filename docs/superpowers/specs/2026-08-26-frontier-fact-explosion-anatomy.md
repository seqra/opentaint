# The frontier arm's fact explosion, measured end to end

`saloed/31-any-unroll-manager-design`, 2026-08-26. Arm under test: **TIFA never-unroll** (HEAD
`f615da6c2`) with `anyUnrollLimit=100`, `anyUnrollKindPolicy=rescore`,
`anyUnrollRescoreStrategy=bfs`. Workload: Netflix Conductor, one Spring handler
(`WorkflowResource#rerun`), one taint rule, 8 GB, 300 s IFDS budget. Harness
`scoped-harness/scoped-run.sh`; see [[conductor-single-endpoint-witness]].

This is the diagnosis document for the arm that shipped in
`2026-08-26-tifa-never-unroll-implementation.md`. That change bought 2.5x the events and left the
run still not converging. The question here is only: **what exactly is growing, who grows it, and
what is supposed to stop it.**

Every number below is from a run in `scoped-runs/`; the counter that produced it is named so the
claim can be re-derived rather than believed.

---

## 0. The shape of the answer, in one paragraph

The analyser is enumerating **non-repeating access-path sequences over the reachable field set of a
Spring object graph**. Nothing bounds how long such a sequence may get except a depth gate that is
applied only to method-entry facts, that freezes within the first 15-20 seconds of a 180-270 second
run, and that then leaves **241,903 entry edges parked and never processed**; nothing bounds how wide
a node may get at all; and the only semantic pruner -- the type filter -- is **vacuous at 86.7% of
the steps it lets through**, because the position type is `java.lang.Object` or a type variable
(67.8%) or an interface (18.8%). The work that results is overwhelmingly **summary application**:
85.2% of all propagated fact mass is a callee summary grafted onto a caller fact, which re-roots the
caller's remainder -- 52% of its own fact, because the matched premise is 1.35 links long and the
fact is 13-17 deep. Roughly half the node mass hangs off ONE base: `AccessPathBase.ClassStatic` is a
`data object`, a single global base for every static in the program.

The decisive experiment is section 9. Refusing the type-unjustified steps converges the run in 36-40
seconds with 96-492x less stored mass -- and reports **zero findings**, in every one of the three
ways of splitting them. **The same steps carry all of the volume and all of the signal**, so the
lever cannot be to cut them; it has to be to *abstract* them.

---
## 1. What was measured, and how

Ten runs. All use the frontier flags above; `census-A` and `census-B` use the shipped jar, the rest
use a jar carrying the new counters (the counters are off unless their property is set, so the two
are the same analyser).

| run | jar | extra | what it produced |
|---|---|---|---|
| `census-A` | `tifaclean-638d876b95` | `tifaDiag tifaTop=150 tifaLongLabels apOpDiag anyManagerDiag` | per-`(method, base)` accumulator census with TYPED field labels |
| `census-B` | `tifaclean-638d876b95` | `summaryPremiseDiag summaryPremiseTop=120` | the premise census |
| `census-C` | `census-34f7bd1c9b` | `edgeCensus apOpDiag tifaDiag` | producer attribution, store totals, demand breadth |
| `census-D` | `census2-6ade042fa8` | as C, plus the vacuous-accept table | which positions the type system cannot constrain |
| `census-E` | `census2-6ade042fa8` | JFR `settings=profile` | where the CPU actually goes |
| `census-F` | `census4-52e4d526f1` | as C, plus the depth-gate backlog counters | how much the depth gate silently parks |
| `abl-object` | `census4-52e4d526f1` | `rejectVacuousFieldSteps=object` | ablation: no `Object`/type-var steps |
| `abl-iface` | `census4-52e4d526f1` | `rejectVacuousFieldSteps=interface` | ablation: no interface steps |
| `abl-vacuous` | `census3-738e88615f` | `rejectVacuousFieldSteps=all` | ablation: neither |
| `ctrl-nostar` | `census2-6ade042fa8` | as D, `rulesets/single-rule-nostar` | the CONVERGING control, same counters |

New instrumentation written for this investigation, all off by default:

- **`EdgeStoreDiagnostics`** (`-Dopentaint.edgeCensus=true`), `ap/ifds/EdgeStoreDiagnostics.kt`. Hooks
  `MethodAnalyzerEdges.add` -- the single funnel every stored `(statement, fact)` passes through --
  and the two tree storages' merge points. It separates three masses that the engine never
  distinguished: what a producer OFFERED, what the store RETAINED, and what it HANDED BACK to be
  propagated again. A thread-local producer tag, mirroring `TifaDiagnostics.callSite`, bills each
  add to one of START / TIFA_SEED / INPUT_REFINE / DELAY_REPLAY / SEQUENT / CALL / SUMMARY /
  SIDE_EFFECT / SIDE_EFFECT_REQ. Also counts the depth gate's parked backlog.
- **TIFA demand histograms** (`TifaDiagnostics.recordDemand`): `|E|`, trie children and fact children
  at every walk state. The premise family is sequences over the demanded set, so its width is the
  quantity that matters and nothing measured it.
- **Type-filter accept REASONS** (`JIRFactTypeChecker`): every accepted field step is classified as
  genuinely type-checked, or waved through because the position is `java.lang.Object`, a type
  variable, or an interface -- plus a bounded top-N table of the exact `(position type -> field)`
  pairs. Rejections are split by accessor kind.
- **`ApOpDiagnostics.I-filterTypes`**: the graft's type-filter memo -- calls, hit rate, and the node
  mass its misses walk.
- **`-Dopentaint.rejectVacuousFieldSteps=<object|interface|all>`**: an unsound ablation that refuses
  the steps the type system could not justify, one vacuity class at a time, to bound the size of the
  prize and to find out which class carries the signal.

---

## 2. The population

`census-C`, at the low-memory stop (2,291,251 events, 239 s):

```
edgeStore calls=8471388 firstInserts=2258045 growths=1684844 noops=4528499 noopShare=53.46%
edgeStore offeredMass=247529113 storeMass=72048222 propagatedMass=202577244
          propagatedPerStored=2.81 propagatedPerGrowth=51.38
edgeStore unchangedEnqueued=21524766 unchangedSuppressed=2125983
          slotsOpened=1857245 slotMerges=1657409 mergesPerSlot=0.89 maxSlot=3009
```

A **slot** is one `(final base, initial base, premise, statement)` key, and it holds ONE merged tree
-- the store is not a set of facts. So:

| quantity | value |
|---|---|
| stored slots | **1,857,245** |
| stored nodes | **72,048,222** (with path multiplicity) |
| nodes per slot | **38.8** |
| largest single slot | **3,009** |
| merges per slot after creation | **0.89** |
| summary premises (census-B) | **119,458** over **14,696** methods |
| worst method's premises | **11,682** (`WorkflowExecutorOps#rerunWF`) |
| longest premise | **7 links** |

Two readings follow immediately, and they matter for the mitigation:

1. **Facts are small; there are simply an enormous number of them.** The mean slot is 39 nodes and
   the largest in the whole run is 3,009. Nothing here is a runaway single tree.
2. **A slot is born big and barely grows.** `mergesPerSlot = 0.89`, and `offeredMass / calls = 29.2`
   nodes against `storeMass / slots = 38.8`. The mass arrives with the fact; it is not accumulated
   in place. Re-propagation of merged trees costs a factor of **2.81**, which is real but is not the
   explosion.

The TIFA accumulator is the one place where a large tree does appear -- `MethodSameBaseInitialFact.added`
merges every fact that ever arrived at a `(method, base)` pair, and `census-A` finds 11,250 such
pairs with the largest at **115,985** nodes, depth 17. That tree is a union over ~10,000 arrivals,
not a fact.

---

## 3. Who adds it

`census-C`, by producer, of 202,577,244 propagated nodes:

| producer | calls | share of calls | no-ops | propagated nodes | share |
|---|---:|---:|---:|---:|---:|
| **SUMMARY** (a callee summary grafted onto a caller fact) | 6,794,917 | **80.2%** | 4,015,914 | **172,681,189** | **85.2%** |
| CALL (call-to-return) | 999,441 | 11.8% | 299,937 | 21,643,970 | 10.7% |
| SEQUENT (ordinary intra-procedural flow) | 443,227 | 5.2% | 105,607 | 7,786,660 | 3.8% |
| INPUT_REFINE | 79,934 | 0.9% | 59,774 | 133,135 | 0.07% |
| TIFA_SEED | 69,056 | 0.8% | 0 | 314,790 | 0.16% |
| START | 35,102 | 0.4% | 0 | 775 | 0.00% |
| DELAY_REPLAY | 2,819 | 0.03% | 466 | 14,426 | 0.01% |

By edge kind, `FACT_TO_FACT` is 7,920,235 of 8,471,388 calls and **99.97%** of propagated mass.

**Summary application is the fact producer.** Everything else is rounding. And 59% of summary
applications add nothing at all -- 4.0M of 6.8M calls are no-ops -- so the graft is run, the type
filter is run, `concat` allocates, and the result is already known.

Concentration by method, of the same 202.6M:

| method | propagated | share | calls | entry points |
|---|---:|---:|---:|---:|
| `WorkflowExecutorOps#decide(WorkflowModel)` | 97,795,797 | **48.3%** | 2,465,004 | **1** |
| `WorkflowExecutorOps#rerunWF(...)` | 58,358,316 | **28.8%** | 2,593,877 | **1** |
| `WorkflowExecutorOps#startWorkflow(StartWorkflowInput)` | 7,050,257 | 3.5% | 166,884 | 1 |
| `WorkflowExecutorOps#terminateWorkflow(...)` | 7,002,293 | 3.5% | 364,323 | 1 |
| `WorkflowTestService#testWorkflow(...)` | 5,482,359 | 2.7% | 215,566 | 1 |

**Two methods are 77% of the work, and each has exactly ONE method entry point.** This is not a
calling-context explosion. It is a *premise* explosion inside a single context: `rerunWF` holds
11,682 summary premises, and the store holds one slot per `(premise, statement)`.

---

## 4. Why the facts have that shape: the type system is vacuous where it matters

`census-A` was run with `-Dopentaint.tifaLongLabels=true`, which renders a field edge as
`declaringClass#field:fieldType` instead of `.field`. That makes the exact dump of the largest
accumulator (`TIFATREE`, 1,080 distinct nodes, 40,506 edges, `size=115,985`, depth 17) type-checkable
by hand. Classifying every consecutive link pair `A#f:T -> B#g:U` over 79,623 weighted pairs:

| category | pairs | share |
|---|---:|---:|
| **vacuous: `T` is `java.lang.Object`** | **70,021** | **87.94%** |
| exact, `T == B` | 4,630 | 5.81% |
| array step | 2,841 | 3.57% |
| vacuous: an interface on one or both sides | 1,963 | 2.47% |
| a real subtype relation | 144 | 0.18% |
| genuinely impossible | 16 | 0.020% |

and the branching is where the vacuity is:

- A node reached through an `Object`-typed edge has **mean out-degree 85.9**. Every other node has
  **7.0**. That is a **12.3x** difference, and `Object` edges are only 11.9% of all edges.
- **Suppressing `Object`-typed edges removes 115,954 of the tree's 115,985 nodes: 100.0%.**
- Positions with a real type terminate cleanly: `long`, `int`, `Long`, `Integer`, `TaskModel$Status`
  and `protobuf.Any` all have **mean fanout 0.00**; `String` has 0.04.

The whole-run counters agree, and they are what the new `Field steps:` line reports (`census-D`, at
the stop):

```
Field steps: accepted 2469697 [typed 329069 (13.32%), vacuousObject 1675470 (67.84%),
                               vacuousInterface 465158 (18.83%), unknownField 0]
             | rejected typed 65968466 notRef 7335164
Access rejects: field 73303630 element 199481 value 0 any 1419 mark 151 | acceptOther 11352
```

**Of every field step the type filter allows, 86.7% is allowed because the filter had nothing to
say.** 67.8% because the position is `java.lang.Object` or a type variable, 18.8% because it is an
interface. Only 13.3% is a check that could have failed and did not.

### Where the `Object` positions come from

They are not a defect of the program under analysis. They are **the taint model's own approximation
accessors**, and they are declared `java.lang.Object` at the source. In the model config the shape is
`.<class>#<field>#<type>`, e.g. `core/opentaint-config/java-config/.../fastjson-2.0.60.yaml`:

```
- .java.lang.String#<serialized-value>#java.lang.Object
```

and in code, `SpringRuleProvider.kt:220-235`:

```kotlin
private const val javaObject = "java.lang.Object"
private val iterableElement  = PositionAccessor.FieldAccessor("java.lang.Iterable", "Element", javaObject)
private val optionalElement  = PositionAccessor.FieldAccessor("java.util.Optional", "Element", javaObject)
private val repositoryContent = PositionAccessor.FieldAccessor(javaObject, "__repo__", javaObject)
```

`JIRMethodGetDefault.kt:31` does the same for `<get-default>`.

Of the 4,788 `Object`-typed edges in the largest tree, **3,791 (79%) are these synthetic accessors**,
and they gate **93.9%** of all traffic through `Object` positions:
`String.<serialized-value>`, `Optional.Element`, `HttpHeaders.headerValue` / `headerValues`,
`ByteArrayOutputStream.buffer`, `Map.MapKey`, `Map.MapValue`, `Map$Entry.Key` / `Value`,
`Iterable.Element`, `Iterator.Element`, `Object.<get-default>`, `StompHeaders.entries`. Several of
them -- `HttpHeaders.headerValue`, `HttpHeaders.headerValues`, `StompHeaders.entries`,
`HeaderIterator.content`, `StrTokenizer.content` -- **do not exist as fields at all**; they are pure
models.

The end-of-run table of the exact positions, `census-D` (`Vacuous accepts, top 25`):

```
175793 | java.lang.Object    -> java.lang.String#<serialized-value>
109020 | java.lang.Object    -> org.apache.commons.lang3.text.StrBuilder#buffer
105688 | java.util.Map<K, V> -> org.springframework.http.HttpHeaders#headerValue
105651 | java.util.Map<K, V> -> org.springframework.http.HttpHeaders#headerValues
 84300 | java.lang.Object    -> com.netflix.conductor.model.TaskModel#inputData
 83608 | java.lang.Object    -> com.netflix.conductor.model.TaskModel#inputPayload
 82847 | java.util.Map<K, V> -> java.util.Map#MapValue
 80002 | java.lang.Object    -> com.netflix.conductor.model.WorkflowModel#workflowDefinition
 72917 | java.lang.Object    -> java.lang.Iterable#Element
 70571 | java.lang.Object    -> java.util.Iterator#Element
```

Read the first row literally: **the deserialised value of a `String` is an `Object`, and from an
`Object` the analyser may take the deserialised value of a `String` again.** 310 of the 445
`<serialized-value>` edges in the largest tree are immediately followed by another one; 17 of the 150
deepest paths carry three in a row; and each occurrence fans out to about 60 `WorkflowModel` /
`TaskModel` accessors.

Two smaller findings from the same dump, both worth fixing on their own:

- **Array types are erased to `Object` in the accessor.** `StrBuilder.buffer` is declared `char[]`
  and prints as `java.lang.Object` -- so an array field is an unconstrained position.
- **One genuinely wrong link gates 27.1% of the largest tree.**
  `ConductorProperties.stack : java.lang.String` -> `StrBuilder#buffer` appears 3 times, sits on
  41 of the 150 deepest paths and 65 of the 80 arrival-ladder entries, and the node immediately
  after it has out-degree 164 spanning 28 unrelated declaring classes.

### The gate already has a red test for this, and has had for weeks

`core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/test/kotlin/.../JIRFactTypeCheckerUnrollFilterTest.kt`
is the pair of failures the gate has carried through every session of this investigation
(3,484 tests, 2 failures, unchanged by any change made here). Its own header says what it is for:

> The any-accessor unroll asks `accessPathFilter` whether a candidate field may follow a prefix, and
> the filter's whole discriminating power comes from the declared `fieldType` of the prefix's last
> accessor. **Every field modifier emitted by `model/java/config` declares `java.lang.Object` as that
> type**, so these tests pin what the filter can still reject once a path has crossed one modelled
> field.

The three cases, and their status:

| test | prefix | candidate | expected | actual |
|---|---|---|---|---|
| `concrete field type rejects an unrelated field` | `StringBuilder#value : String` | `URL#host` | `Reject` | **passes** |
| `object typed model field rejects an unrelated field` | `Iterable#Element : Object` | `URL#host` | `Reject` | **FAILS** |
| `chained model fields reject an unrelated field` | `Iterable#Element : Object` x2 | `URL#host` | `Reject` | **FAILS** |

So the unit-level statement of everything in this section already exists, already fails, and has been
attributed to "pre-existing" in three implementation notes. **A `java.net.URL#host` may follow the
element of an `Iterable`, and nothing in the engine says otherwise.** Section 8's M1 changes the
expected result from `Reject` to `Widen` -- these two cases become the acceptance test for it.

### This is the branching factor

`TifaDiagnostics.recordDemand`, added here, samples the demanded accessor set `|E|` at every walk
state. `census-D`: `mean 4.87, max 179`, and the histogram has a fat tail --
**5.5M walk states with `|E| >= 16`, 2.9M of them in 32..63 and 2.0M in 64..127.** A level that
demands 60 accessors is a level standing at an `Object`.

---

## 5. What is supposed to stop it, and what actually does

There are four candidate bounds in the engine. Three of them do not bind, and the fourth binds by
accident.

### 5.1 The type filter -- binds hard, but only after the fact exists

It refuses 73,303,630 field steps and allows 2,469,697 (`census-D`). That is a 96.7% refusal rate,
and it is the only reason the run is finite at all. But it runs **downstream**: the fact is built,
merged into a slot, propagated, grafted -- and the filter is applied per graft point, per traversal.
`ApOpDiagnostics.I-filterTypes`, added here (`census-C`):

```
apop I-filterTypes calls=14134605 hits=8027293 hitRate=56.79% misses=6107312
                   rejectedHits=2275649 rejectedMisses=731032
                   inNodes=127482498 outNodes=123832347 nodesPerMiss=20.87
```

The memo is keyed on `(delta node identity, position type)`, so 57% of graft points are free. The
other 43% walk **127.5M nodes**, against `concat resultNodes = 156.9M` for the entire run -- the
graft spends nearly as much walking to decide what to graft as it does grafting. And those 127.5M
node walks remove **3%** of node mass (`outNodes/inNodes = 97%`): almost every refusal is a light
branch, while the heavy spines pass.

This is also, precisely, the throughput collapse. Per progress interval on `tifa-clean-1`,
`d(accessChecks)/d(events)` tracks events/s one-for-one:

| interval | events/s | access checks per event | interval reject rate |
|---:|---:|---:|---:|
| 1 | 37,866 | 0.9 | 48.8% |
| 16 | 8,671 | 0.8 | 20.8% |
| **17** | **540** | **1,782** | 99.4% |
| **18** | **26.7** | **37,610** | **99.96%** |
| 20 | 8,123 | 2.5 | 29.8% |
| **23** | **11.8** | **85,796** | **99.99%** |

At interval 18 the analyser performed **10,117,089 accessor checks to advance 269 events** and threw
away 10,113,535 of them. The run does not slow down uniformly; it periodically enters a regime where
one event costs a thousand times normal, and that regime is exactly a rejection burst.

### 5.2 `limitFieldAccess` -- binds, and gives the shape of the space

It cuts every occurrence of a field at any depth, so **no field may repeat in a chain**. That is what
turns "all sequences" into "all NON-REPEATING sequences", i.e. `sum_k N!/(N-k)!` rather than `N^k`.
With `N` on the order of the whole program's field set at an `Object` position, this is not a bound
that helps.

### 5.3 Breadth -- nothing bounds it at all

Confirmed again here and unchanged from [[no-widening-nothing-bounds-breadth]]: there is **no
widening operator**. Every breadth-touching operation either removes depth (`installAbove`), removes
one child while adding that child's children (`absorbCoveredByAnyPrefix`), or hoists to the root and
so *increases* root breadth (`limitFieldAccess`). The `[any]` subsumption walk is the one real
subsumption operator and it is idle here (below).

### 5.4 The fact-depth gate -- the only bound that actually limits the population, and it binds by accident

`NormalMethodAnalyzer.edgeExceedLimit` parks an entry edge whose initial fact is deeper than the
unit's `factDepthLimit`. The limit starts at `INITIAL_ALLOWED_FACT_DEPTH = 3` and is raised by
`TaintAnalysisUnitRunner.resumeDelayedAnalyzers` -- **only when the unit runs out of work**.

On the exploding arm the unit never runs out of work:

| | star arm (`census-B`) | `ctrl-nostar` |
|---|---|---|
| `Increase unit ... fact limit` lines | 104 | 104 |
| highest limit reached | **9** (8 in `census-C`/`census-F`) | **18** |
| last raise, as a fraction of the scan | **8.1%** (14.6 s of 179.6 s) | throughout |
| premise link histogram | 0:6,581 1:1,706 2:3,211 3:5,312 4:9,270 5:14,724 **6:39,448 7:18,201** | -- |

**58.6% of all premises sit at 6 or 7 links, and 7 is exactly the cap the units froze at.** Every
package that holds premise mass -- `core.execution` (68.3%), `service` (12.3%),
`core.execution.tasks` (11.3%) -- has final limit exactly 7 and observes exactly 7. The distribution
is not converging; it is **pinned against its own ceiling**, and 91.9% of the run passed with that
ceiling frozen.

So the honest statement of the situation is: *the premise population is bounded today by a
scheduling artefact*. The gate was designed as a fairness device -- raise the limit when there is
nothing better to do -- and it has become the de-facto widening operator, implemented as "park the
edge and never look at it again".

### 5.5 What is NOT the cause: the `[any]` machinery

Every one of these is a zero on a workload that is failing:

- `E-delta anyPremise calls = 0`; `I-filter anyTail = 0`; `anyDelta = 0` at all 30 `G-site` rows;
  `receiverCarriesAny = 0` at all `H-base` rows.
- `any: 0` on 150 of 150 `added`-tree rows; `anyEdges` non-zero on 3 of 150 `PROFILE` lines.
- **0 of 119,458 summary premises carry an `[any]`.**
- TIFA arrivals `any/concrete = 402 / 1,394,592` (0.03%); incoming nodes `11,472 / 85,741,486` (0.01%).
- 135 of 149 live `[any]` DAGs have `total < 2`.

And yet TIFA pays `anyDescents = R3b = 25,625,872` -- **52.6% of all 48.7M walk states** -- and the
manager answers `queryReads = 25,866,119`, for 0.01% of the fact mass. On `ctrl-nostar` all of these
are exactly **0**.

The `[any]` bookkeeping is not the explosion. It is a large constant cost paid on top of it, and no
further `[any]`-side work -- unroll bounds, absorption directions, manager policy -- can move this
workload. That closes the line of investigation that
[[any-unroll-manager-outcome]], [[absorbing-prepend-outcome]] and [[tifa-never-unroll-result]] were
on.

---

### 5.6 Where the CPU and the allocation actually go

`census-E`, JFR `settings=profile`, 232.7 s, 21,317 `ExecutionSample`, 60,009
`ObjectAllocationSample`. Steady state is `t` in [30 s, 228 s), 79.7% of samples:

| bucket | share of CPU |
|---|---:|
| access-tree fact representation (`AccessNode` merge 16.5%, create 10.7%, interning 9.9% + 3.4%, filter 1.0%) | **50.0%** |
| class/type resolution -- `JIRFactTypeChecker$AccessorFilter` -> `JIRClasspathImpl.findClassWithCache` | **28.0%** |
| the IFDS driver itself | 11.8% |
| **`AnyUnroll`** | **0.05%** |
| **`AccessTreeAnySuffixMatcher`** | **0.01%** |

Three things this settles.

**The type filter is 28% of CPU, and the largest single frame in the whole recording is
`JIRClasspathImpl.findClassWithCache` at 7.6% self.** Despite the name it is not a map lookup:
`JIRClasspathImpl.kt:81` walks `featuresChain.call { it.tryFindClass(...) }`, once per accessor per
filtered fact. `JIRFactTypeChecker.fieldClassType` calls it on every field step -- 75.8M times in
`census-D`. **Memoising the accessor -> declaring-class resolution is a pure-performance change worth
most of that 7.6%**, and it belongs in M5.

**The hot leaves are proportional to WIDTH, not depth.** The two hottest JDK frames are
`ArraysSupport.mismatch` (7.47%, 98.8% of it under `AccessTreeInterner$InternStrategy.equals`'s
`accessors.contentEquals`) and `Arrays.binarySearch0` (6.10%, in `createElementAndField` and
`accessorIndex`). Both scale with the number of accessor edges on a node. Every measured recursion
depth is flat across the run. That is the same conclusion section 5.3 reaches from the counters,
arrived at from the profiler.

**The `[any]` machinery costs 0.06% of CPU.** Section 5.5 said it was off the critical path by volume;
the profiler says it is off the critical path by time as well.

Allocation and GC say the run is not CPU-bound at all:

- **314.6 GB allocated, ~1.35 GB/s**, 96% on the ten IFDS workers. `AccessNode` and companions are
  46%; by type, `Object[]` 17.0% + `int[]` 15.4% + `AccessNode[]` 9.6% = **42% is accessor and child
  arrays** -- again width. `Object2ObjectOpenCustomHashMap.<init>` alone is **7.92 GB of empty
  interner buckets**, implying 2-3 x 10^7 distinct node shapes interned, about 10 per IFDS event.
- **GC is 27.30 s = 11.73% of wall**, of which 18.81 s is **17 G1 Full GCs, every one triggered by
  `System.gc()` from `MemoryManager$GCNotificationListener`**. Heap-after-GC climbs monotonically
  2.53 GB -> **7.16 GB against an 8 GB cap** and never plateaus: this is retained state, not garbage.
- The ten workers together use about **1.5 of 20 hardware threads** through the fixed point. The
  analysis is memory-bound, not compute-bound, and the parallelism is idle.
- Lock contention is small but real and concentrated: 6.41 s total, 85% of it on one monitor,
  `TaintConfiguration$TaintRulesStorage` via `getConfigForMethod`.

---

## 6. The control: what "not exploding" looks like on the same counters

`ctrl-nostar` is the same jar, same flags, same counters, with `rulesets/single-rule-nostar` -- the
one arm that converges. It finishes in **38.4 s with `rc 0`** and reports **0 findings**, so it is a
control, not an option; the star source is what finds the two vulnerabilities.

| counter | star (`census-D`) | `ctrl-nostar` | ratio |
|---|---:|---:|---:|
| events | 2,272,533 | 188,730 | 12.0x |
| edge-store `add` calls | 8,075,582 | 845,726 | 9.5x |
| **slots opened** | **1,833,541** | **107,062** | **17.1x** |
| **stored nodes** | **78,315,691** | **648,778** | **120.7x** |
| propagated nodes | 170,245,017 | 1,932,039 | 88.1x |
| merges per slot | 0.84 | 0.26 | 3.2x |
| TIFA walk states | 48,701,254 | 147,996 | **329x** |
| `[any]` descents | 25,625,872 | **0** | -- |
| field steps accepted | 2,469,697 | 20,184 | 122x |
| field steps rejected | 73,303,630 | 3,842 | **19,079x** |
| SUMMARY share of propagated mass | 85.2% | 79.4% | -- |
| highest fact-depth limit | **8-9** | **18** | -- |

Two things stand out. **Stored mass grows 121x for 12x the events** -- the per-event cost of the star
arm is an order of magnitude worse, which is the throughput collapse restated. And **the converging
arm's depth ladder climbs to 18**: when a unit does go idle, the gate lifts and depth stops
mattering. Depth is not what separates the two arms; breadth is.

---

## 7. The mechanism, stated once

Putting sections 2-6 together, the loop is:

1. `$*UNTRUSTED` seeds a **whole-object** fact on a Spring handler parameter. Without it the same
   workload converges in 38 s -- and finds nothing (section 6).
2. A caller subscribes at a call site; the callee's initial-fact abstraction receives the fact and
   emits premises. **Every one of the 12 sampled growth stacks in both replicates is this path**
   (`callStatementStep -> propagateFactCallFact -> resolveMethodCall -> subscribeOnMethodSummaries ->
   submitMethodInitialFact -> MethodSameBaseInitialFact.addInitialFact`), not the unroller and not
   `concat`.
3. The premise walk extends a prefix by the accessors demanded at it. At a position with a real type
   the demand set is small and the chain terminates (mean fanout 0.00-0.04 for primitives and final
   classes). **At a position typed `java.lang.Object` -- which is what every model accessor leaves
   behind -- the demand set is the entire program's field set**, and the mean out-degree is 85.9.
4. Each new premise opens `~15` new `(premise, statement)` slots, and each slot is filled by a
   summary application that re-roots the caller's remainder -- 52% of the caller's fact, because the
   matched premise is 1.35 links long and the fact is 13-17 deep.
5. Those facts flow back up as new caller facts, which produce new premises at the caller, and the
   loop closes. **85% of all propagated mass is step 4.**
6. Nothing widens. The only bound that binds is the depth gate, and it froze 8% of the way into the
   run, leaving 58.6% of the premise population piled against its ceiling.

Two amplifiers sit on top of this and are independent of it:

- **`AccessPathBase.ClassStatic` is a `data object`** -- ONE base for every static in the program,
  with the class name as the first accessor. `<static>` is **48.8%** of the accumulated `added` mass
  (106 of the top 150 `(method, base)` pairs) and **42.0-50.9%** of `concat`'s result nodes across
  replicates (`apop H-base`). Every method that touches any static receives the merged static state
  of the whole application.
- **Virtual dispatch replicates whole trees.** Rows #3-#13 of the `added` table are byte-identical --
  `added = 123,254`, `depth = 13`, `distinct = 1,432`, the same `levels` histogram -- differing only
  in which `WorkflowSystemTask#start` implementation owns them. That is **1,355,794 nodes = 11
  copies of one tree**, all reached from one call site (`rerunWF:1958`, the largest `G-site` at 25.9%
  of node mass).

---

## 8. Mitigations, ranked by measured share

Two constraints from earlier work frame every entry here. [[fact-explosion-mechanism]]: every
reduction attempt so far has been *sound-but-lossy* or *lossless-but-useless*, and the `L=0` arm
managed to be both at once. [[conductor-fact-explosion-findings]]: measure findings AND
wall/progress on both arms, never one.

### M1. Widen where the type system cannot constrain -- the primary proposal

**What.** When an access path is about to be extended by a concrete field accessor at a position
whose static type carries no information (`java.lang.Object`, a type variable, an unresolved type),
do not enumerate the fields reachable from there. Emit a single **`[any]`** edge instead.

**Why it is the right shape.** `[any]` means *zero or more* field/element steps, so replacing the set
`{p.f : f a field}` by `p.[any]` is an **over-approximation**: it can add flows, never remove them.
That is the opposite polarity from every previous attempt in this investigation -- the risk is false
positives, not lost findings -- and it is exactly what the accessor was designed to denote.

**Reach.** 86.7% of every field step the filter allows happens at such a position (67.8% `Object` /
type variable, 18.8% interface). A node below an `Object` edge branches 12.3x wider than any other
node, and suppressing `Object`-typed edges empties 100.0% of the largest accumulated tree.

**The machinery is already there and is idle.** Under never-unroll, an `[any]` is never materialised:
R3b/R3c/R4 answer demand through it by reading (section 5.5 -- 25.6M descents today for 0.01% of the
mass). And `AccessTreeAnySuffixMatcher` is the engine's ONE real subsumption operator (`[any].X` kills
a stored `a.[any].X` at any depth, on every channel) -- it currently never fires because nothing
produces `[any]`s below the root.

**Where.** The predicate is already computed: `JIRFactTypeChecker.AccessorFilter.checkAccessor`
decides `Accept` for exactly these cases and the new `Vacuity` classification names them. It needs a
third answer -- `Widen` -- honoured in two places: `AccessTree.filterAccessNode`, which would replace
the child edge by an `[any]` edge, and `TreeInitialFactAbstraction`'s R3c/R2 emit arms, which would
emit `p.[any]` once instead of `p.a` per demanded `a`.

**Which vacuity class.** Section 9 separates them, and the answer is **`OBJECT` and `TYPE_VAR`, not
`INTERFACE`** -- 67.8% of accepted steps rather than 86.7%. Two reasons. An interface position still
carries a real constraint (only fields of classes that could implement it), whereas an `Object`
position carries none. And an interface position sits EARLY -- it is the Spring bean reference at the
head of the spine -- so widening there would put an `[any]` near the root, which is the regime the
`[any]` budget work already measured as expensive (16.5 graft points at 100 nodes/call,
[[any-unroll-manager-outcome]]). The `Object` positions sit deep, below the model accessors, exactly
on top of the subtree that explodes.

**What must be measured before believing it.** The two-modes result
([[any-unroll-manager-outcome]], [[fact-explosion-mechanism]]): keeping an `[any]` makes the graft
attach at 16.5 points at 100 nodes/call instead of 2.72 at 25. That measurement was taken with the
`[any]` at the ROOT, coming from the star source. Here it would sit deep, below a model accessor,
replacing the subtree that is actually exploding. Whether the trade is favourable is an experiment,
not a deduction. The bounding ablation is `-Dopentaint.rejectVacuousFieldSteps=true` (section 9).

### M2. Give the model accessors a real type where the model knows one

`.java.lang.String#<serialized-value>#java.lang.Object` is in the model config verbatim, and
`SpringRuleProvider` hard-codes `fieldType = javaObject` for `Iterable#Element`, `Optional#Element`
and `Object#__repo__`. Some of these have a knowable type and some do not:

- **Arrays are erased.** `StrBuilder#buffer` is `char[]` and reaches the filter as
  `java.lang.Object`. Fixing the accessor's declared type is mechanical and sound.
- **`Optional#Element`, `Iterable#Element`, `Map#MapValue`** have a type whenever the generic
  signature is available. Threading it through is real work but is a strict precision gain.
- **`String#<serialized-value>`** genuinely cannot be typed -- deserialisation produces an arbitrary
  object. This one wants M1, not M2. It is also the top row of the vacuous table at 175,793 hits,
  and it self-composes: 310 of 445 of its edges are immediately followed by another one.

Also fix the one real type violation: `ConductorProperties.stack : java.lang.String ->
StrBuilder#buffer` gates 27.1% of the largest tree, and the node after it has out-degree 164 across
28 unrelated declaring classes.

### M3. Split `AccessPathBase.ClassStatic` per class

It is `data object ClassStatic` in `Accessors.kt:33` -- one base for the whole program -- and the
class name is *already* the first accessor (`ClassStaticAccessor(typeName)`, `Accessors.kt:148`). So
making the base `ClassStatic(typeName)` moves information that already exists from the first accessor
into the base. Nothing is lost and nothing is approximated.

The effect is to stop the broadcast: today a method that touches `Foo.x` is handed the merged static
state of every class in the application. `<static>` is **42.0-50.9%** of `concat`'s result nodes and
**48.8%** of the accumulated `added` mass -- two independent counters -- so this is the single
largest mechanical reduction available, and it is orthogonal to M1.

Known risk: `MethodAnalyzerEdges.AbstractStaticEdges` special-cases depth-0 static edges into a
tree-free exclusion-only storage keyed on `AccessPathBase.ClassStatic`; that fast path has to keep
working per class.

### M4. Make the depth gate a decision rather than an accident

`factDepthLimit` starts at 3 and rises only when a unit idles, so on this workload it freezes at 7-9
after 14.6 s and parks every deeper entry edge **for the rest of the run**. Two honest options:

- park -> **widen**: when an entry fact exceeds the limit, abstract its tail to `[any]` and admit it,
  instead of deferring it indefinitely; or
- keep deferring, but say so: report the parked backlog (the new
  `edgeStore delayed/replayed/stillParked` counters exist for this) and treat the limit as a declared
  k-limit rather than a fairness heuristic.

Either way the current behaviour -- a soundness-relevant cut applied by whichever unit happened not
to idle -- should not remain implicit.

### M5. Performance-only, no semantic change

- **Memoise `FieldAccessor -> declaring class`.** `JIRFactTypeChecker.fieldClassType` calls
  `cp.findTypeOrNull(accessor.className)` on every field step -- 75.8M times in `census-D` -- and
  `JIRClasspathImpl.findClassWithCache` is a `featuresChain` walk, not a map lookup. It is **the
  single largest frame in the JFR recording at 7.6% self**, inside a 28% type-resolution bucket. A
  `ConcurrentHashMap<FieldAccessor, JIRClassType?>` is the whole change. Do this one first: it is
  hours of work and changes nothing observable.
- **A receiver-side memo in `concat`.** 47.6-48.1% of the 14.1M graft points re-visit a receiver node
  already grafted in the same call; `concatToLeafAbstractNodes` memoises only the delta side.
  Ceiling ~48% of graft work. See [[concat-graft-is-mostly-revisit]].
- **A cheaper `filterTypes`.** 43% of graft points miss the memo and walk 127.5M nodes to remove 3%
  of mass.
- **Drop the dead `[any]` bookkeeping.** 25.6M R3b offers and 25.9M manager `queryReads` for 0.01% of
  the fact mass and **0.06% of CPU**; `J-trimCF` is entered 2.68M times with 278 real `[any]` cases
  and a 34% memo hit rate.
- **De-duplicate virtual-dispatch fan-out.** 11 byte-identical copies of one 123,254-node tree
  (1,355,794 nodes) across `WorkflowSystemTask#start` implementations, from one call site.
- **The `MemoryManager` calls `System.gc()`**: 17 G1 Full GCs, 18.81 s of the run's 27.30 s of STW.
  Heap-after-GC never plateaus, so the sweeps are not recovering anything -- they are a symptom being
  treated. Worth revisiting once the population is bounded, not before.

### Ranking

| | lever | measured share | soundness | cost |
|---|---|---|---|---|
| 1 | **M1** widen at unconstrained positions | 67.8% of allowed field steps (`Object`/type var); 12.3x branching | over-approximates (FP risk, not FN) | design + measurement |
| 2 | **M3** per-class static base | 42-51% of node mass | exact | mechanical |
| 3 | **M2** type the models | subset of M1's 86.7% | exact | per-model work |
| 4 | **M4** deliberate depth gate | 58.6% of premises sit at the cap | makes an implicit cut explicit | small |
| 5 | **M5** memoisation and dead code | 7.6% of CPU (class lookup), up to 48% of graft work | none | small |

---

## 9. The bounding ablation

`-Dopentaint.rejectVacuousFieldSteps=all` refuses every field step the type system could not justify.
It is **unsound** and exists only to put a number on M1's ceiling and its floor.

`-Dopentaint.rejectVacuousFieldSteps=<mode>` takes `object` (positions with no nominal type --
`java.lang.Object`, a type variable), `interface`, or `all`, so the three vacuity classes can be
separated. All three arms were run on the same jar with the same flags.

| | star arm (`census-D` / `census-F`) | `abl-object` | `abl-iface` | `abl-vacuous` (all) | `ctrl-nostar` |
|---|---:|---:|---:|---:|---:|
| what is refused | nothing | `Object` / type var | interfaces | both | (no star source) |
| outcome | low memory / timeout | **`rc 0`, 40.1 s** | **`rc 0`, 35.8 s** | **`rc 0`, 36.4 s** | `rc 0`, 38.4 s |
| events | 2,272,533 | 290,729 | 112,280 | 110,015 | 188,730 |
| **`Total vulnerabilities`** | **2** | **0** | **0** | **0** | **0** |
| edge-store `add` calls | 8,075,582 | 1,056,368 | 648,394 | 639,321 | 845,726 |
| slots opened | 1,833,541 | 235,538 | 71,225 | 66,529 | 107,062 |
| **stored nodes** | **78,315,691** | **819,103** | **174,725** | **158,997** | 648,778 |
| propagated nodes | 170,245,017 | 1,304,464 | 219,196 | 203,043 | 1,932,039 |
| largest slot | 465-476 | 72 | 36 | 36 | 872 |
| merges per slot | 0.85 | 0.17 | 0.05 | 0.05 | 0.26 |
| highest fact-depth limit | **8** | **46** | 31 | 31 | 18 |
| edges still parked at the stop | **241,903** | 0 | 0 | 0 | -- |

Three readings, and the third is the one that decides the design:

1. **The entire explosion lives in the steps the type system cannot justify.** Refusing the `Object`
   class alone drops stored mass 96x and converges in 40 s; refusing all of it drops it 492x.
2. **So do both findings.** Every arm reports `Total vulnerabilities: 0`. The flow to both sinks runs
   through a container or an `Object`-typed model accessor.
3. **Each vacuity class is independently load-bearing.** Cutting *only* interfaces converges just as
   hard as cutting everything (174,725 vs 158,997 stored nodes) -- because the spine starts at a
   Spring bean reference, which is interface-typed, so the chain dies at its first link. Cutting only
   `Object` leaves a larger residue (819,103) because the interface steps still build the bean spine
   before the models erase it.

That is the cleanest possible statement of why the lever must be **widening** and not **cutting**:
the same steps carry all of the volume and all of the signal, so any rule that drops them drops the
findings, while `p.[any]` keeps the path and collapses the branching.

The depth-gate reading is the other half of the same picture, and `census-F` -- the star arm re-run
with the new backlog counters -- makes it exact:

| | star arm (`census-F`) | `abl-vacuous` |
|---|---:|---:|
| entry edges deferred by the depth gate | **243,830** | 2,895 |
| of those, later replayed | **1,927** | 2,895 |
| **still parked when the run stopped** | **241,903 (99.2%)** | **0** |
| limit raises | 428 | 1,814 |
| highest limit reached | **8** | **31** |

**A quarter of a million entry edges are parked and never looked at again.** That is not a
k-limit anybody chose; it is what `resumeDelayedAnalyzers` does when the unit never idles, and it is
the only thing keeping the premise population finite (section 5.4). The gate is not a bound the
analysis is designed around -- it is what happens when the analysis has time to breathe, inverted.

---

## 10. What this closes, and what it opens

**Closed.** The `[any]` machinery is off the critical path of this workload and cannot be the lever
(section 5.5): 0 of 119,458 premises carry an `[any]`, 0.01% of arriving node mass carries one, 135
of 149 live `[any]` DAGs have `total < 2`, and `ctrl-nostar` reports exactly zero for every
`[any]` counter. The line of work through [[any-unroll-manager-outcome]],
[[absorbing-prepend-outcome]], [[any-greedy-predecessor-is-sound]] and [[tifa-never-unroll-result]]
has taken that mechanism as far as it goes; what remains of it here is a 25.6M-descent constant cost
to be deleted, not a lever to be tuned.

**Also closed:** the re-propagation of merged slot trees, which was a live suspicion when the
`edgeCensus` counters were written. `propagatedPerStored` is 2.17-2.81 and `mergesPerSlot` is 0.84-0.89
-- slots are born big and barely grow, so re-propagation is a constant factor, not the explosion.

**Open, and in this order:**

1. **Implement `Widen` (M1) and measure it against the two-modes result.** The prediction is that an
   `[any]` placed *below* a model accessor behaves differently from one at the root, but that is a
   prediction. The arms are: findings (must stay at 2), stored nodes, `slotsOpened`, `C-graft
   pointsPerCall`, and `stillParked`.
2. **Per-class static base (M3)** -- independent of M1, exact, and worth 42-51% of `concat`'s output
   on its own.
3. **The depth gate (M4).** 241,903 parked entry edges is not a number anybody chose. Whatever
   replaces it should be visible in the log.
4. Only then the performance items (M5), because they change no results and their ceiling is known.

---

## 11. Reproducing

```bash
H=/drive-testcomp/opentaint-go-rules/opentaint-w3-benchmark-results/scoped-harness
cd $H && ./buildjar.sh census                      # jars/census-<sha>.jar

COMMON="-Dopentaint.anyUnrollLimit=100 -Dopentaint.anyUnrollKindPolicy=rescore \
        -Dopentaint.anyUnrollRescoreStrategy=bfs"
DIAG="-Dopentaint.edgeCensus=true -Dopentaint.edgeCensusTop=40 \
      -Dopentaint.apOpDiag=true -Dopentaint.tifaDiag=true -Dopentaint.tifaTop=40"

./scoped-run.sh census-C jars/census-<sha>.jar $COMMON $DIAG          # the population and its producers
./scoped-run.sh census-A jars/census-<sha>.jar $COMMON \
    -Dopentaint.tifaDiag=true -Dopentaint.tifaTop=150 -Dopentaint.tifaLongLabels=true
./scoped-run.sh census-B jars/census-<sha>.jar $COMMON \
    -Dopentaint.summaryPremiseDiag=true -Dopentaint.summaryPremiseTop=120

# the three ablations
./scoped-run.sh abl-object  jars/census-<sha>.jar $COMMON $DIAG -Dopentaint.rejectVacuousFieldSteps=object
./scoped-run.sh abl-iface   jars/census-<sha>.jar $COMMON $DIAG -Dopentaint.rejectVacuousFieldSteps=interface
./scoped-run.sh abl-vacuous jars/census-<sha>.jar $COMMON $DIAG -Dopentaint.rejectVacuousFieldSteps=all

# the converging control
RULES=$H/rulesets/single-rule-nostar ./scoped-run.sh ctrl-nostar jars/census-<sha>.jar $COMMON $DIAG
```

What to read where:

| line | file | what it answers |
|---|---|---|
| `EDGESTORE edgeStore ...` | `console.log` | the population, the producers, the depth-gate backlog |
| `edgeStoreLive ...` | `analyzer.log`, per progress tick | the growth CURVE -- a single end-of-run total cannot say whether it is converging |
| `TIFA tifa demand ...` / `...Buckets=` | `console.log` | the branching factor |
| `Field steps:` / `Access rejects:` / `Vacuous accepts, top 25` | `analyzer.log`, `--verbosity=debug` | where the type system stops constraining |
| `apop I-filterTypes ...` | `console.log` | what the graft's type filter costs |
| `Increase unit ... fact limit: N` | `analyzer.log` | the depth ladder, and when it froze |

Everything is off unless its property is set, and `ctrl-nostar` reports zero for every counter the
star arm reports millions of -- which is the cheapest way to check that a counter is measuring what
its name says.
