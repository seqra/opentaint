# Restricted demand handling versus the original AP contract

The follow-up [restricted fact-management design](../design/bidirectional-restricted-fact-management-20261027.md)
traces the static gap through nonstatic wrappers. It shows that a repair on
static input/output bases alone does not suffice. Section 8 below describes
the intended ordinary authority; it does not prove that current retained
productive pairs are already complete after static erasure. The user has
now selected [static demand closure and run-1 exit routing](../../spec/restricted-demand-static-closure.md).
It completes guidance at handoff while retaining original AP demand gates.
The observations below describe the reviewed implementation, which remains
unchanged.

Date: 27 October 2026. Source review and bounded AP controls. Analyzer
implementation unchanged.
Current checkout: `a2882fa9db18690b43659b8080ab0cba30036743`;
runtime `core` tree: `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
Pre-SQ implementation: `fa0bd5887e7b25ef912852a19d701c0a21302bcb`.

No project experiment was started. The latest Thingsboard timed result referenced
by the current implementation reports reached **run-2**, completed **run-1**.
The separate protection diagnostics reached and completed **run-1**. This review
does not extend either measurement.

## 1. Conclusion and correction

The current restricted-run pipeline changes the original AP demand contract at
three main execution points:

1. An actual input can start a nonzero analysis without a demand match.
2. A FLOW demand no longer starts its shared FLOW analysis when the actual input
   has a concrete mark. The current code selects concrete queries instead.
3. An admitted query authorizes publication of computed raw summaries without
   the original entry/exit demand-pair restriction.

These changes apply to all bases, both directions, and every restricted run.
They are larger semantic changes than the selected exception for missing run-1
static-to-static relations. They are not only query deduplication or an
implementation of the original AP emitter.

Two additional changes feed the restricted runs at the run-1 boundary:

4. Every published run-1 summary is selected as guidance, including NORMAL
   singletons which the original AP routes to records only.
5. `forceRun1Layer` forces every run-1 taint result to DEMAND, including in FULL
   mode. It can demote an AP-normal EXACT start or result before persistence.

The preceding explanation incorrectly treated these current behaviors as
independently necessary gap repairs. No additional required gap is established
by that explanation. In particular, the ANY-to-EXACT example compares possible
query identities; it does not establish a missing required demand. A normal
EXACT relation belongs in the normal-record path. The current run-1 wrapper can
change that layer, so an exact guide in today's runtime does not establish a
gap in the original algorithm. The separate EXACT query needs a necessity
argument which accounts for both record routing and the changed phase policy,
not only a query-set inclusion theorem.

The selected static exception remains necessary because run-1 deliberately
omits static-to-static relations. It must authorize the required static starts
and static answers. The original AP rules remain the reference for other work.
This review identifies the required scope; it does not claim a completed proof
of a narrowed Kotlin implementation for every current adapter.

## 2. The original restricted-run contract

The reference is [AP section 6.3](../../spec/ap.md#63-restricted-run-the-emission),
[section 6.4](../../spec/ap.md#64-summary-restriction-restricted-runs-in-the-callee),
and sections 8.5 through 8.7. The pre-SQ runtime implements the same ordinary
emission and restriction structure. Later concrete-STAR and FLOW-subsumption
changes do not authorize replacement of this demand policy.

Let an immutable demand pair be `D = (D-c, D-p)`, oriented for the current run.
`D-c` describes the method input. `D-p` describes the permitted output; it can
be absent. In a backward run these are at the forward exit and entry.

### 2.1 Initial emission reads demand

```kotlin
fun onAdded(actual: Facts) {
    for (demand in incomingDemand.near(method, actual)) {
        for (initial in ops.emit(demand, actual)) {
            startOnce(initial)
        }
    }
}
```

For a concrete demand entry, emission intersects the actual input with the
entry, including its mark. For an abstract FLOW entry, emission uses the FLOW
form of the demand. One canonical FLOW initial can serve many incoming marks.
There is no default nonzero start merely because an input arrived.

The original ZERO discovery/start rules remain their own rules. A record is
also a separate answer route: it does not cause a new method initial.

### 2.2 Publication reads the complete pair

```kotlin
fun onComputedSummary(original: Premise, raw: Facts) {
    retainRaw(original, raw)
    for (demand in incomingDemand.covering(method, original)) {
        ops.restrict(original, raw, demand).forEach(::publish)
    }
}
```

The operation checks whole-premise containment in `D-c`, then the output mark,
base, field path and tail against `D-p`. An absent `D-p` gives no ordinary
publication. Representable output geometry is narrowed. The existing AP limits
on narrowing correlated STAR and abstract marks still apply.

Backward ZERO-premise balanced return is an explicit exception. It does not
authorize every nonzero summary. Multi-premise publications keep the complete
premise even when restriction uses one member's matching demand pair.

### 2.3 Demand and records have different roles

Raw NORMAL singleton summaries are persisted as records. They do not need a
next-run demand merely because they are absent from that demand store. DEMAND
summaries, normal conjunctions, and backward ZERO summaries use their existing
selection rules. Record replay and demand-guided method execution are separate.

Thus the statement “there is an actual T input but no explicit T demand” is
not itself a proof of a gap. A FLOW guide or an applicable normal record may
already supply the required relation.

## 3. Current runtime differences

| Boundary | Original AP | Current runtime | Source |
|---|---|---|---|
| Missing demand entry | No nonzero emission | Canonical initial derived from actual input | `StrongQueries.admit`, lines 39–51 |
| Abstract demand entry, concrete input | Emit shared FLOW initial | Filter abstract guide from guide-based starts; keep actual concrete query | `StrongQueries.admit`, lines 31 and 55–65 |
| Publication | Restrict by matching entry/exit pair | Publish raw answer when the whole query premise is admitted | `RunMethodAnalyzer.published`, lines 754–761 |
| New query authorization | No independent authorization state | Revisit raw summaries and queue permitted answers | `RunMethodAnalyzer.addLink`, lines 134–142 |
| ZERO publication | Existing backward balanced-return exception | Also permits already computed ZERO results after any query admission | `StrongQueries.permits`, lines 95–97 |
| Scope | Demand-guided restricted runs | SQ owner in every restricted run, all bases and both directions | `RunMethodAnalyzer`, lines 36–38 |
| Run-1 NORMAL singleton selection | Persist as record, omit from selected demand | Select every published run-1 row and also persist eligible NORMAL records | `RunMethodAnalyzer.queuePublications`, lines 743–750 |
| Run-1 concrete EXACT starting layer | AP primitive starts NORMAL; later operations determine its layer | `forceRun1Layer` demotes every TAINT result even in FULL mode | `RunMethodAnalyzer`, lines 196–204 and 228–233 |
| Static ANY input after run-1 | Ordinary demand/record behavior plus selected static exception | Also add same-field EXACT initial | `StrongQueries.completeStaticFull`, lines 82–89 |

The current code still uses the AP scalar `emit` primitive. However, the first
call synthesizes its pattern from the actual input. That is a different choice
of authority from reading an incoming demand entry. Reusing the primitive does
not preserve the original higher-level demand contract.

The AP implementation still contains the original operations in `Demand.kt`
and `Reference.kt`. The changed method pipeline chooses different inputs to
those operations or bypasses them. This is principally a control-policy change,
not a missing AP primitive.

Admission preserves actual marks; SQ does not invent a concrete T from FLOW.
This safety property does not establish that every admitted concrete analysis
is demanded or needed.

### 3.1 Two boundary changes which can create extra guidance

Current run-1 selection is:

```kotlin
val selected = config.run1 ||
    ops.demandPart(premise, facts, config.direction) != null
```

For a NORMAL singleton, `demandPart` gives no selected demand under the original
rule. The first term nevertheless selects it after run-1. Once normal-record
persistence was restored, such a row could supply both a record and an extra
guidance pair. This is not the original record-only routing.

The layer adapter is:

```kotlin
if (!config.run1) return value
val runtime = ops.runtimeFact(value, mode)
return if (runtime is TaintTree || runtime.base == STATIC ||
           Run1StaticService.hasStaticMember(premise))
    runtime.withLayer(Layer.DEMAND)
else runtime
```

This is applied to starts and results. It has no GROUP-only guard. Therefore:

```text
AP primitive:        p/EXACT/T -> p/EXACT/T, NORMAL
run-1 phase adapter: p/EXACT/T -> p/EXACT/T, DEMAND
```

The user-selected GROUP abstraction needs its own DEMAND policy. The current
static-erasure spec also explicitly states the all-taint policy for FULL mode.
That later overlay is a major difference from the original AP layer contract;
it must be reviewed as such. This review does not silently remove the overlay
or change GROUP semantics. In particular, extra demand created by this adapter
cannot be used as proof that the original AP requires a broader SQ policy.

## 4. How the change multiplies neutral body work

Consider the ordinary method:

```java
Object identity(Object p) {
    return p;
}
```

Use the same incoming backward demand for both policies:

```text
D-c: ret/[any]/FLOW
D-p: arg(0)/*/FLOW

actual call inputs: ret/[any]/T1, ..., ret/[any]/Tk
```

Original AP execution:

```text
emit from the abstract entry:
  ret/*/FLOW                     // one canonical initial, NORMAL start

backward body:
  ret/*/FLOW -> arg(0)/*/FLOW

restrict by D-c/D-p and publish:
  retain the required FLOW relation

caller subscriptions:
  instantiate that relation for each actual Ti
```

Current SQ execution:

```text
ignore the abstract guide as a source of starts
admit actual marked initials:
  ret/[any]/T1, ..., ret/[any]/Tk // k distinct initials, DEMAND starts

backward body:
  ret/[any]/Ti -> arg(0)/[any]/Ti, DEMAND, for each i

publication:
  admitted premise permits each raw marked answer
```

With no other starting route, the current concrete queries do not generate the
shared FLOW original. The example changes one neutral body analysis into k
marked analyses. Caller-specific marked answers are needed in either policy;
repeating the neutral callee body is the extra work. The marked DEMAND answers
can also contribute marked demand to the next handoff.

An actual AP/SQ control confirms one FLOW/NORMAL initial versus eight distinct
TAINT/DEMAND initials for eight incoming marks and the same FLOW guide. It also
executes the original FLOW body transfer and restriction. This is an
operation-count example, not a new Thingsboard measurement. Field
tails and summary layers differ between the two execution policies, so the
current policy is not simply the old policy plus a harmless fallback.

Applying one persistent FLOW record does not suppress `LinkIn` or SQ admission.
`RunMethodCallServices.enterCallees` queues subscription and link delivery.
`SubscriptionManager.replay` separately reads records. The existing current
policy can therefore start additional body work even when a record supplied
one answer. The unsafe shortcut “one record answered, so skip the whole method”
is not selected: a record alone need not cover every required dependency.

## 5. Publication can enlarge the next frontier

Suppose the incoming demand permits this pair:

```text
D-c = ret/[any]/T
D-p = arg(0)/[any]/T
```

An analysis can compute several raw outputs. For example, a branchy return can
produce outputs at both `arg(0)` and `arg(1)` under its backward original.

```text
raw result: ret/[any]/T -> arg(1)/[any]/T

original restriction by the shown pair: reject (different exit base)
current SQ permission:                 publish, if ret/[any]/T was admitted
```

This is a comparison for the stated demand snapshot, not a claim that a valid
run-1 producer must omit the second branch. It shows the policy difference:
being a computed answer is enough for current SQ publication, while original
AP publication also requires the demand pair. Extra DEMAND publications can
enter callers and the next demand store.

The current complete-premise permission test prevents partial ND authorization.
It does not restore the entry/exit pair test. A whole admitted premise and a
whole demand-covered relation are different predicates.

## 6. Historical source of the wider contract

The relevant commits are:

| Commit | Evidence |
|---|---|
| `fa0bd5887e7b25ef912852a19d701c0a21302bcb` | Pre-SQ: `addLink` emits from demand; `published` uses ordinary restriction except existing backward ZERO return |
| `28a123f0eac937e8f2feca9ee5dd84e38fa8f979` | Introduces SQ for all restricted runs, filters abstract guide starts, bypasses restriction for admitted premises, and disables run-1 record persistence |
| `ab6c3cd006cb62e6a017c0e3c32d96573d2214e3` | Restores run-1 normal-record persistence; leaves the broad SQ policy |
| `b68b3a1c9389c8d1b8ab6ad513af0c586a546895` | Erases run-1 static/static summaries and adds same-field EXACT completion |

The older `run1-field-writes.md` section 7.2 cites the loss of executable
nonstatic normal records as one reason for all-base current queries. That
assumption no longer describes the runtime. The current driver persists
normal records before handoff, including after run-1. This historical rationale
does not justify the remaining blanket policy.

Record restoration is not the same as restoring the complete original layer
policy. The current `forceRun1Layer` still demotes every `TaintTree`. Thus some
relations which would qualify as NORMAL records under the AP rules are now
DEMAND before the record filter sees them. The record filter correctly rejects
those changed values; the layer change occurs earlier.

The broader behavior is already present in the first SQ implementation. It is
not caused solely by the later static-erasure patch. Later documents and tests
carry that behavior forward, but repeating a contract does not establish that
it is necessary for the originally selected static gap.

## 7. What the current tests and proofs actually establish

`StrongQueriesTest` deliberately supplies inputs with no old guide and checks
that all bases are admitted. `StrongQueryPipelineTest` checks that an absent
old exit cannot veto the computed answer. These are tests of the implemented
broad policy. They do not construct a run-1 witness whose necessary nonstatic
demand is missing under the original AP algorithm.

`Run1StaticQueryCompletion.lean` compares actual SQ queries plus possible old
concrete-guide starts with a completed query batch. Its arbitrary guide domain
includes EXACT guides. It proves query-identity coverage of that reference;
it does not prove that each extra EXACT query is needed after accounting for
normal records, selected demand production and original FLOW execution.

The original AP has constructive C2 emission and C5 restriction certificates.
The later FLOW-backed proofs explicitly use those contracts without general
SQ. They retain marked dependency barriers and use FLOW for neutral transport.
Those local proofs do not establish a whole current JVM iteration theorem;
they also provide no authority to replace the gates with all-base permission.

## 8. Required scope for the next design

The selected gap is:

```java
void copy() { C.out = C.in; }
```

Run-1 deliberately exports no `C.in -> C.out` static/static summary. When
run-2 receives an actual `C.out/T` requirement, it must still analyze the body
and return a derived `C.in/T` requirement. Neither endpoint permission can
depend on the erased explicit pair.

This needs both input admission and computed static-output permission. These
are two parts of the same static gap, not independent reasons to authorize all
bases. Cross-mark or cross-group static/static relations are also erased, so
the exception must not be reduced to same-field or same-mark identities.

The intended division is:

| Work | Authority |
|---|---|
| Ordinary nonstatic initial | Original AP emission from demand, including FLOW entries |
| Ordinary nonstatic output | Original AP entry/exit restriction; existing records stay available |
| Missing run-2 static/static analysis | Selected static exception applied to an actual input |
| Its computed static/static answer | Same selected exception, preserving actual derivation and complete premise |
| Static/nonstatic productive boundary | Retained productive demand or normal record; do not grant general descendant-query permission |
| ZERO discovery, sink seeds and backward balanced return | Existing explicit rules |
| Later handoffs | Ordinary demand and record rules; do not automatically inherit a run-1 exception |

All required nonstatic, mixed, source and sink dependencies must be accounted
for by retained productive summaries, records and seeds. A missing required
pair there is a guidance/producer issue to investigate. General SQ admission
must not silently mask it.

No additional necessary exception has been demonstrated by this review. A
narrowing proposal must still check these productive boundaries, source-hit
publication, complete ND support and the existing cleaner regressions. The
review does not turn the absence of another counterexample into a universal
completeness proof. It also does not authorize implementation changes.

## 9. Reproduction and source anchors

```sh
git show 28a123f0e^:core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt
git show 28a123f0e -- core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt
git show 28a123f0e -- core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt
git show ab6c3cd00 -- core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt
git show b68b3a1c9 -- core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/StrongQueries.kt
```

Current runtime sources:

- [StrongQueries.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/StrongQueries.kt): actual starts, concrete-guide filtering, EXACT completion and premise permission.
- [RunMethodAnalyzer.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt): `addLink`, `queuePublications`, `published`, and `restrictBy`.
- [Demand.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Demand.kt) and [Reference.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt): original emitter, FLOW form, demand restriction and demand selection operations.
- [IterationDriver.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt) and [RecordStore.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/RecordStore.kt): barrier persistence and native NORMAL singleton selection.
- [HandOff.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandOff.kt): outgoing pair construction, sink/source seeds and run-2 static policy.
- [RunMethodCallServices.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodCallServices.kt) and [SubscriptionManager.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/SubscriptionManager.kt): independent link delivery, summary replay and record replay.

Proof and test sources:

- [Static query-completion model](../../spec/lean/ApSpec/Run1StaticQueryCompletion.lean).
- [FLOW-backed handoff without general SQ](../../spec/run1-flow-backed-concrete-relations-proofs.md#7-handoff-replacement-without-general-strongqueries).
- [StrongQueriesTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/StrongQueriesTest.kt) and [StrongQueryPipelineTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/StrongQueryPipelineTest.kt).

The review reads source and history and runs the bounded controls below. It
does not claim a new project result, benchmark improvement, or a completed
all-run proof.

## 10. Bounded actual AP/SQ controls

The external control compiles against the current AP and SQ classes. It uses
one CPU, a 512 MiB compiler heap, and a 256 MiB execution heap. It starts no
Gradle task, project analyzer, method runner or analysis iteration.

All six checks pass:

```text
PASS initial-sharing reference=1/FLOW/NORMAL current=8/TAINT/DEMAND
PASS reference-FLOW-body-and-restriction
PASS wrong-exit reference=reject SQ-premise-permission=true
PASS absent-exit reference=reject SQ-premise-permission=true
PASS absent-guide reference=0 current=1
PASS exact-start=NORMAL
```

The publication controls compare the original restriction with SQ's actual
premise-permission predicate. The separately reviewed `published` branch turns
that permission into raw publication. They do not invoke the private method
or measure a whole actor. The EXACT check concerns the starting layer; it
does not claim that an EXACT tail alone determines every propagated layer.

The first launch mistakenly retained a previous control's main class. Its
output is excluded. The corrected launch explicitly names `DemandScopeReview`;
the receipt records the correction. Both runs were local bounded controls.

The full source and corrected receipt are embedded below. External paths are
reproduction labels; they are not required to read the control data.

### 10.1 Control source

```kotlin
package org.opentaint.dataflow.bidi.engine
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures

object DemandScopeReview {
 @JvmStatic fun main(args:Array<String>) {
  val f=StoreFixtures(); val m=f.manager; val ops=f.ops
  val mode=ApMode(false,Direction.BACKWARD,1)
  val ret=AccessPathBase.Return; val arg=AccessPathBase.Argument(0)
  val guide=DemandPattern(f.pattern(ret,tail=Tail.ANY,mark=MarkSlot.STAR),
    f.pattern(arg,tail=Tail.STAR,mark=MarkSlot.STAR))
  val inputs=(1..8).map{f.fact(ret,tail=Tail.ANY,mark=MarkSlot.Concrete(f.mark("T$it")),layer=Layer.DEMAND)}
  val reference=linkedSetOf<InitialAp>(); val current=linkedSetOf<InitialAp>()
  val sq=StrongQueries(ops,mode)
  for(input in inputs) {
   reference.addAll(ops.emit(guide,input))
   current.addAll(sq.admit(input,sequenceOf(guide)))
  }
  check(reference.size==1 && reference.single().isFlow)
  check(current.size==8 && current.all{it.mark is MarkSlot.Concrete})
  check(ops.startFact(reference.single(),mode).layer==Layer.NORMAL)
  check(current.all{ops.startFact(it,mode).layer==Layer.DEMAND})
  val edge=PathEdge(PathFact(ret,emptyList(),Tail.STAR,MarkSlot.STAR),
    PathFact(arg,emptyList(),Tail.STAR,MarkSlot.STAR),ExclusionSet.Empty)
  val oldBody=CollectingOut()
  ops.applyEdge(ops.startFact(reference.single(),mode),reference.single(),edge,true,mode,oldBody)
  check(oldBody.results.size==1 && oldBody.results.single() is FlowTree)
  check(ops.restrict(reference.single(),oldBody.results.single(),guide).isNotEmpty())
  val wrongExit=m.factsOf(PathFact(AccessPathBase.Argument(1),emptyList(),Tail.ANY,current.first().mark),
    ExclusionSet.Empty,Layer.DEMAND)
  check(ops.restrict(current.first(),wrongExit,guide).isEmpty())
  check(sq.permits(current.first()))
  check(ops.restrict(current.first(),wrongExit,guide.copy(exit=null)).isEmpty())
  val absent=StrongQueries(ops,mode)
  val absentStarts=absent.admit(inputs.first())
  check(absentStarts.size==1)
  val exactSq=StrongQueries(ops,mode)
  val exact=exactSq.admit(f.fact(ret,tail=Tail.EXACT,mark=current.first().mark)).single()
  check(ops.startFact(exact,mode).layer==Layer.NORMAL)
  println("PASS initial-sharing reference=1/FLOW/NORMAL current=8/TAINT/DEMAND")
  println("PASS reference-FLOW-body-and-restriction")
  println("PASS wrong-exit reference=reject SQ-premise-permission=true")
  println("PASS absent-exit reference=reject SQ-premise-permission=true")
  println("PASS absent-guide reference=0 current=1")
  println("PASS exact-start=NORMAL")
 }
}
```

### 10.2 Corrected execution receipt

<details>
<summary>Commands, source hash, return codes, launch correction and output</summary>

```json
{
  "scope": "Standalone actual AP and StrongQueries policy controls; no analyzer run, no Gradle, no production edits",
  "compile": {
    "command": [
      "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
      "-Xmx512m",
      "-XX:ActiveProcessorCount=1",
      "-cp",
      "/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-compiler-embeddable/2.1.0/988bf980588bbbcfa1ba19c1ffd7aa869b335a31/kotlin-compiler-embeddable-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.intellij.deps/trove4j/1.0.20200330/3afb14d5f9ceb459d724e907a21145e8ff394f02/trove4j-1.0.20200330.jar:/home/sobol/.gradle/caches/8.10/workerMain/gradle-worker.jar:/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/fixture-cache:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/java/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-configuration-rules/configuration-rules-common/build/libs/configuration-rules-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-ir/opentaint-ir-api-common/build/libs/opentaint-ir-api-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-utils/common-util/build/libs/common-util.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.detekt.sarif4k/sarif4k-jvm/0.5.0/d3060993cd73b57ee61b260841bedcabb7dcbb02/sarif4k-jvm-0.5.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.microutils/kotlin-logging-jvm/3.0.5/82f2256aeedccfd9c27ea585274a50bf06517383/kotlin-logging-jvm-3.0.5.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-collections-immutable-jvm/0.3.8/6119a57df1ad662593dfe21954898183c6c933b4/kotlinx-collections-immutable-jvm-0.3.8.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test-junit5/2.1.0/3d386bb97b74923e498d46193f7a380de10734a4/kotlin-test-junit5-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test/2.1.0/bab38f61fdb1c90a68fce9666b3f9fe419aeef72/kotlin-test-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-coroutines-core-jvm/1.10.0/37966d769934a42566dec1ca2e1da6e5565c4e06/kotlinx-coroutines-core-jvm-1.10.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk7/2.1.0/d77bee6c7bc849e7b9bf4b83e94e8fd1dfc0ea8a/kotlin-stdlib-jdk7-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.charleskorn.kaml/kaml-jvm/0.73.0/abeffe03e958d06cfa6496ecf7c3be9e566c33cf/kaml-jvm-0.73.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-json-jvm/1.7.3/6701e8c68d9e82387ce72ee96e8ddf058208d58f/kotlinx-serialization-json-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-core-jvm/1.7.3/1f226780b845ff9206474c05159245d861556249/kotlinx-serialization-core-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.krzeminski/snakeyaml-engine-kmp-jvm/3.1.1/542190d973fb66f3568fbcec1a3a8210e2f705dc/snakeyaml-engine-kmp-jvm-3.1.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.squareup.okio/okio-jvm/3.10.2/6a2cc3acd5a83e66075a2f6c5b0608b6043fa34c/okio-jvm-3.10.2.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/net.thauvin.erik.urlencoder/urlencoder-lib-jvm/1.6.0/6b922dd3ff960b08873c10395545e08355e250c9/urlencoder-lib-jvm-1.6.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib/2.1.20/aa8ca79cd50578314f6d1180c47cbe14c0fee567/kotlin-stdlib-2.1.20.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk8/2.1.0/c4a51be16c840b969ed706bc25d5836b099d188a/kotlin-stdlib-jdk8-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.unimi.dsi/fastutil-core/8.5.13/dd3d3ed477b7c1aee8176f6684813f48304769f9/fastutil-core-8.5.13.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/info.leadinglight/jdot/1.0/8e84489791d7fe20bf1631e791152b554cfea4ba/jdot-1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains/annotations/23.0.0/8cc20c07506ec18e0834947b84a864bfc094484e/annotations-23.0.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.slf4j/slf4j-api/2.0.3/deef7fc81f00bd5e6205bb097be1040b4094f007/slf4j-api-2.0.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-launcher/1.10.1/ce85bf5e38bee0989ded9bd468dd4ff78dc0cfa8/junit-platform-launcher-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-engine/1.10.1/f32ae4af74fde68414b8a3d2b7cf1fb43824a83a/junit-platform-engine-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-api/5.10.1/eb90c7d8bfaae8fdc97b225733fcb595ddd72843/junit-jupiter-api-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-commons/1.10.1/2bfcd4a4e38b10c671b6916d7e543c20afe25579/junit-platform-commons-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-engine/5.10.1/6c9ff773f9aa842b91d1f2fe4658973252ce2428/junit-jupiter-engine-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.opentest4j/opentest4j/1.3.0/152ea56b3a72f655d4fd677fc0ef2596c3dd5e6e/opentest4j-1.3.0.jar",
      "org.jetbrains.kotlin.cli.jvm.K2JVMCompiler",
      "-no-stdlib",
      "-no-reflect",
      "-jvm-target",
      "17",
      "-classpath",
      "/home/sobol/.gradle/caches/8.10/workerMain/gradle-worker.jar:/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/fixture-cache:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/java/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-configuration-rules/configuration-rules-common/build/libs/configuration-rules-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-ir/opentaint-ir-api-common/build/libs/opentaint-ir-api-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-utils/common-util/build/libs/common-util.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.detekt.sarif4k/sarif4k-jvm/0.5.0/d3060993cd73b57ee61b260841bedcabb7dcbb02/sarif4k-jvm-0.5.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.microutils/kotlin-logging-jvm/3.0.5/82f2256aeedccfd9c27ea585274a50bf06517383/kotlin-logging-jvm-3.0.5.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-collections-immutable-jvm/0.3.8/6119a57df1ad662593dfe21954898183c6c933b4/kotlinx-collections-immutable-jvm-0.3.8.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test-junit5/2.1.0/3d386bb97b74923e498d46193f7a380de10734a4/kotlin-test-junit5-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test/2.1.0/bab38f61fdb1c90a68fce9666b3f9fe419aeef72/kotlin-test-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-coroutines-core-jvm/1.10.0/37966d769934a42566dec1ca2e1da6e5565c4e06/kotlinx-coroutines-core-jvm-1.10.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk7/2.1.0/d77bee6c7bc849e7b9bf4b83e94e8fd1dfc0ea8a/kotlin-stdlib-jdk7-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.charleskorn.kaml/kaml-jvm/0.73.0/abeffe03e958d06cfa6496ecf7c3be9e566c33cf/kaml-jvm-0.73.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-json-jvm/1.7.3/6701e8c68d9e82387ce72ee96e8ddf058208d58f/kotlinx-serialization-json-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-core-jvm/1.7.3/1f226780b845ff9206474c05159245d861556249/kotlinx-serialization-core-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.krzeminski/snakeyaml-engine-kmp-jvm/3.1.1/542190d973fb66f3568fbcec1a3a8210e2f705dc/snakeyaml-engine-kmp-jvm-3.1.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.squareup.okio/okio-jvm/3.10.2/6a2cc3acd5a83e66075a2f6c5b0608b6043fa34c/okio-jvm-3.10.2.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/net.thauvin.erik.urlencoder/urlencoder-lib-jvm/1.6.0/6b922dd3ff960b08873c10395545e08355e250c9/urlencoder-lib-jvm-1.6.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib/2.1.20/aa8ca79cd50578314f6d1180c47cbe14c0fee567/kotlin-stdlib-2.1.20.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk8/2.1.0/c4a51be16c840b969ed706bc25d5836b099d188a/kotlin-stdlib-jdk8-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.unimi.dsi/fastutil-core/8.5.13/dd3d3ed477b7c1aee8176f6684813f48304769f9/fastutil-core-8.5.13.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/info.leadinglight/jdot/1.0/8e84489791d7fe20bf1631e791152b554cfea4ba/jdot-1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains/annotations/23.0.0/8cc20c07506ec18e0834947b84a864bfc094484e/annotations-23.0.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.slf4j/slf4j-api/2.0.3/deef7fc81f00bd5e6205bb097be1040b4094f007/slf4j-api-2.0.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-launcher/1.10.1/ce85bf5e38bee0989ded9bd468dd4ff78dc0cfa8/junit-platform-launcher-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-engine/1.10.1/f32ae4af74fde68414b8a3d2b7cf1fb43824a83a/junit-platform-engine-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-api/5.10.1/eb90c7d8bfaae8fdc97b225733fcb595ddd72843/junit-jupiter-api-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-commons/1.10.1/2bfcd4a4e38b10c671b6916d7e543c20afe25579/junit-platform-commons-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-engine/5.10.1/6c9ff773f9aa842b91d1f2fe4658973252ce2428/junit-jupiter-engine-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.opentest4j/opentest4j/1.3.0/152ea56b3a72f655d4fd677fc0ef2596c3dd5e6e/opentest4j-1.3.0.jar",
      "-Xfriend-paths=/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main",
      "-d",
      "/drive-testcomp/opentaint-go-rules/restricted-demand-review-20261027/classes",
      "/drive-testcomp/opentaint-go-rules/restricted-demand-review-20261027/DemandScopeReview.kt"
    ],
    "exit_code": 0,
    "seconds": 2.068474069237709
  },
  "source_sha256": "d1232bef0351752ccb555a48d9eab5890ba5e2e6e033a3adad1ce314de416fe7",
  "run": {
    "command": [
      "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
      "-Xmx256m",
      "-XX:ActiveProcessorCount=1",
      "-cp",
      "/drive-testcomp/opentaint-go-rules/restricted-demand-review-20261027/classes:/drive-testcomp/opentaint-go-rules/protection-necessity-20261027/ap/classes:/home/sobol/.gradle/caches/8.10/workerMain/gradle-worker.jar:/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/fixture-cache:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/java/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-configuration-rules/configuration-rules-common/build/libs/configuration-rules-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-ir/opentaint-ir-api-common/build/libs/opentaint-ir-api-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-utils/common-util/build/libs/common-util.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.detekt.sarif4k/sarif4k-jvm/0.5.0/d3060993cd73b57ee61b260841bedcabb7dcbb02/sarif4k-jvm-0.5.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.microutils/kotlin-logging-jvm/3.0.5/82f2256aeedccfd9c27ea585274a50bf06517383/kotlin-logging-jvm-3.0.5.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-collections-immutable-jvm/0.3.8/6119a57df1ad662593dfe21954898183c6c933b4/kotlinx-collections-immutable-jvm-0.3.8.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test-junit5/2.1.0/3d386bb97b74923e498d46193f7a380de10734a4/kotlin-test-junit5-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test/2.1.0/bab38f61fdb1c90a68fce9666b3f9fe419aeef72/kotlin-test-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-coroutines-core-jvm/1.10.0/37966d769934a42566dec1ca2e1da6e5565c4e06/kotlinx-coroutines-core-jvm-1.10.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk7/2.1.0/d77bee6c7bc849e7b9bf4b83e94e8fd1dfc0ea8a/kotlin-stdlib-jdk7-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.charleskorn.kaml/kaml-jvm/0.73.0/abeffe03e958d06cfa6496ecf7c3be9e566c33cf/kaml-jvm-0.73.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-json-jvm/1.7.3/6701e8c68d9e82387ce72ee96e8ddf058208d58f/kotlinx-serialization-json-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-core-jvm/1.7.3/1f226780b845ff9206474c05159245d861556249/kotlinx-serialization-core-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.krzeminski/snakeyaml-engine-kmp-jvm/3.1.1/542190d973fb66f3568fbcec1a3a8210e2f705dc/snakeyaml-engine-kmp-jvm-3.1.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.squareup.okio/okio-jvm/3.10.2/6a2cc3acd5a83e66075a2f6c5b0608b6043fa34c/okio-jvm-3.10.2.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/net.thauvin.erik.urlencoder/urlencoder-lib-jvm/1.6.0/6b922dd3ff960b08873c10395545e08355e250c9/urlencoder-lib-jvm-1.6.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib/2.1.20/aa8ca79cd50578314f6d1180c47cbe14c0fee567/kotlin-stdlib-2.1.20.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk8/2.1.0/c4a51be16c840b969ed706bc25d5836b099d188a/kotlin-stdlib-jdk8-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.unimi.dsi/fastutil-core/8.5.13/dd3d3ed477b7c1aee8176f6684813f48304769f9/fastutil-core-8.5.13.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/info.leadinglight/jdot/1.0/8e84489791d7fe20bf1631e791152b554cfea4ba/jdot-1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains/annotations/23.0.0/8cc20c07506ec18e0834947b84a864bfc094484e/annotations-23.0.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.slf4j/slf4j-api/2.0.3/deef7fc81f00bd5e6205bb097be1040b4094f007/slf4j-api-2.0.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-launcher/1.10.1/ce85bf5e38bee0989ded9bd468dd4ff78dc0cfa8/junit-platform-launcher-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-engine/1.10.1/f32ae4af74fde68414b8a3d2b7cf1fb43824a83a/junit-platform-engine-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-api/5.10.1/eb90c7d8bfaae8fdc97b225733fcb595ddd72843/junit-jupiter-api-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-commons/1.10.1/2bfcd4a4e38b10c671b6916d7e543c20afe25579/junit-platform-commons-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-engine/5.10.1/6c9ff773f9aa842b91d1f2fe4658973252ce2428/junit-jupiter-engine-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.opentest4j/opentest4j/1.3.0/152ea56b3a72f655d4fd677fc0ef2596c3dd5e6e/opentest4j-1.3.0.jar",
      "org.opentaint.dataflow.bidi.engine.DemandScopeReview"
    ],
    "exit_code": 0,
    "seconds": 0.11444802582263947
  },
  "launch_correction": "First launch retained an earlier main class and ran only previous local controls; not counted. This corrected launch names DemandScopeReview explicitly.",
  "output": "PASS initial-sharing reference=1/FLOW/NORMAL current=8/TAINT/DEMAND\nPASS reference-FLOW-body-and-restriction\nPASS wrong-exit reference=reject SQ-premise-permission=true\nPASS absent-exit reference=reject SQ-premise-permission=true\nPASS absent-guide reference=0 current=1\nPASS exact-start=NORMAL\n",
  "checks_pass": true
}
```

</details>


## 11. Second review: STAR tails, concrete marks and balanced seed returns

Date: 27 October 2026. Source snapshot `eab0b032c7c85e248a3b5d1fdf2c14cea3609aca`;
runtime core remains `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
The latest referenced Thingsboard campaign reached **run-2**, completed
**run-1**, and accepted **run-1**. This review starts no project or engine
iteration. No production implementation was changed.

The [complete proposal](../../spec/restricted-demand-static-closure.md)
is corrected in sections 2, 3.2, 3.4, 3.6, 3.7 and 14. The changes below
are demand-adapter changes; ordinary field transfer, mark protection,
cleaners, aliases and full later-forward ND guards remain unchanged.

### 11.1 Run-1 has no ND edge

The current `RunMethodAnalyzer.checkPremise` requires one InitialAp in
run-1. A complete ND **condition** is still checked, then each contributing
original produces a separate singleton relation. A PremiseSet cannot enter
run-1 method facts, summaries, subscriptions or static seeds. Thus normal
ND summary selection is only a later-forward case, never a run-1 case.

### 11.2 The backward-ZERO rule is original

F57 introduced balanced seed returns on 6 October in `efd7b6373`.
`Backward.DB.zret` returns a ZERO-origin sink requirement through the call
where caller ZERO entered the callee, without a demand-restriction premise.
`6b2b0fd5b` on 7 October states explicitly that the callee does not restrict
that summary and the caller does not perform a satisfaction test. The first
RunMethodAnalyzer (`b65b46d76`, 11 October) already implements this route.

For `helper(q) { sinkT(q); }`, the backward seed yields ZERO → q/T at the
method entry. The matching caller ZERO receives the requirement through
that call's reversed binding. Requiring an ordinary nonzero return-summary
pair would lose a locally consumed argument. This is seed propagation,
not a concrete input assumption or a normal reusable program-flow record.
The original AP sections 4.3, 6.4 and 9.2 already retain the rule. The earlier
comparison's original column was incomplete; this is not a new SQ exception.

### 11.3 A mark gate is not symmetric set intersection

| Operation | Inputs | Required result |
|---|---|---|
| Entry emission | Demand T, actual FLOW | None, even if T is not excluded |
| Entry emission | Demand FLOW, actual T | Shared FLOW initial, not T |
| Exit reduction | Demand T, conclusion FLOW | Keep FLOW if T is not excluded; never turn it into T |
| Exit reduction | Demand FLOW, conclusion T | Keep T |

Whole-premise entry containment still runs before the exit mark gate. A
concrete entry cannot authorize a FLOW original. Correlated STAR conclusions
are also retained whole; cutting them to EXACT can change the pair relation.
The current scalar AP agrees on 14 targeted cases, including exclusions,
mark mismatch, absent exits and EXACT exit versus STAR conclusion.

### 11.4 Real discrepancies found

1. **STAR handoff widening is not original normalization.** Original
   `Abs.normFact` preserves kind and field E and normalizes only mark
   exclusions. Current `HandOff.toBackward` changes STAR to ANY and clears
   E; `28a123f0e` introduced that rewrite on 16 October with SQ. The previous
   proposal incorrectly preserved it. The corrected proposal removes it
   and replaces the blanket typed STAR-entry rejection with the stated
   original guard. The producer proof must exclude abstract STAR entries
   with nonempty E, which original C2 does not cover.
2. **Concrete STAR descent can attach E to the wrong path.** Actual
   x/STAR/{f}/T and demand x.g/ANY/T both cover x.g.f/T when g differs
   from f. Current `commonPart` emits x.g/STAR/{f}/T, which excludes that
   location. Required result: x.g/STAR/{}/T. After the strict descent is
   admitted, ancestor E must be rebased before the tail meet. This case
   belongs to the selected concrete-STAR extension; the original proof
   assumption that concrete inputs have no STAR tail cannot justify it.
3. **Preserving STAR demand exposes the MUST/STAR cell.** Current `meet`
   asserts that this pair cannot occur. The restored forward demand can
   encounter a MUST input. Required location intersection at the same
   path: MUST/(E1 union E2), preserving the MUST kind and current start
   layer. The current probe confirms the assertion; it does not claim
   that the assertion is reachable under today's non-STAR builder.

The corrected proposal explicitly includes these adapter changes. No
runtime field-write, alias, cleaner or mark-generation rule is changed.
These results do not prove a whole JVM iteration or a universal project
failure. The typed and packed adapters remain implementation acceptance
obligations.

### 11.5 Complete local receipt

[MarkBoundaryReview.lean](../../spec/lean/proposals/restricted-demand/MarkBoundaryReview.lean)
checks 18 declarations with no new axiom, choice or placeholder. In
addition to the original mark gates, it proves the general first-accessor
rebasing law and an executable admitted-location counterexample/correction.
[EmissionRestrictionProbe.kt](../../spec/lean/proposals/restricted-demand/EmissionRestrictionProbe.kt)
calls the current scalar AP. It passes 14 expected behavior checks and
confirms two defects/adapter gaps. The complete outputs are embedded below
and are also in
[boundary-review-checks.json](../../spec/lean/proposals/restricted-demand/boundary-review-checks.json).

```json
{
  "state": "SECOND_REVIEW_CHECKED_PROPOSAL_CORRECTED_IMPLEMENTATION_UNCHANGED",
  "reviewed_checkout": "eab0b032c7c85e248a3b5d1fdf2c14cea3609aca",
  "runtime_core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
  "latest_referenced_project_iteration": {
    "reached": "run-2",
    "completed": "run-1",
    "accepted_forward": "run-1"
  },
  "new_project_runs": 0,
  "new_engine_iterations": 0,
  "production_edits": 0,
  "formal": {
    "source": "spec/lean/proposals/restricted-demand/MarkBoundaryReview.lean",
    "source_sha256": "2f471322b608594766a1b784f303559e05555f9989f268e56d9710a6e61b2aff",
    "import": "ApSpec.AbsDefs",
    "exit_code": 0,
    "seconds": 0.29023538529872894,
    "audited_declarations": 18,
    "output": "'MarkBoundaryReview.concrete_entry_does_not_invent_mark' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_entry_rejects_abstract_even_when_mark_not_excluded' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_entry_preserves_actual_mark' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_entry_rejects_other_mark' depends on axioms: [propext]\n'MarkBoundaryReview.abstract_entry_emits_shared_flow' depends on axioms: [propext]\n'MarkBoundaryReview.abstract_entry_does_not_copy_actual_mark_exclusions' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_entry_cannot_authorize_flow_premise' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_exit_keeps_correlated_abstract_conclusion' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_exit_rejects_excluded_mark' depends on axioms: [propext]\n'MarkBoundaryReview.concrete_exit_keeps_other_mark_exclusions' depends on axioms: [propext]\n'MarkBoundaryReview.exact_exit_does_not_decorrelate_star' depends on axioms: [propext]\n'MarkBoundaryReview.abstract_exit_does_not_erase_concrete_mark' depends on axioms: [propext]\n'MarkBoundaryReview.original_normalization_preserves_star_and_field_exclusion' does not depend on any axioms\n'MarkBoundaryReview.admitted_descent_rebases_exclusion' depends on axioms: [propext]\n'MarkBoundaryReview.must_star_intersection_uses_exclusion_union' does not depend on any axioms\n'MarkBoundaryReview.ancestor_and_request_cover_location' does not depend on any axioms\n'MarkBoundaryReview.wrongly_copied_exclusion_loses_location' depends on axioms: [propext]\n'MarkBoundaryReview.corrected_rebasing_keeps_location' does not depend on any axioms\n",
    "scope": "Original scalar mark gates and normalization; generic ancestor-exclusion rebasing; E-union intersection law and an explicit lost-location/corrected-location witness. Not a whole JVM/typed adapter proof."
  },
  "actual_scalar_AP": {
    "source": "spec/lean/proposals/restricted-demand/EmissionRestrictionProbe.kt",
    "source_sha256": "6b8a55c1c803aed8c9461e7dd445163e6f451b0a10be3a67cdee624a4f44879e",
    "runtime_core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
    "current_reference_class_sha256": "5476d2cc70cc658c450506f3f0aadb193b238e4b77aaddca6750fd89d1d6c661",
    "compile_exit_code": 0,
    "run_exit_code": 0,
    "seconds": 2.081396132707596,
    "passed_current_behavior_checks": 14,
    "confirmed_defects_or_adapter_gaps": 2,
    "output": "PASS emission T-demand + FLOW-input = none\nPASS emission T-demand + FLOW-excluding-U-input = none\nPASS emission T-demand + T-input = T\nPASS emission T-demand + U-input = none\nPASS emission FLOW-demand + T-input = shared STAR/FLOW\nPASS emission FLOW-demand + FLOW-excluding-T-input = shared STAR/FLOW\nPASS restriction T-entry rejects entire FLOW-premise\nPASS restriction T-exit keeps FLOW mark and STAR tail\nPASS restriction T-exit rejects FLOW excluding T\nPASS restriction T-exit keeps FLOW excluding only U\nPASS restriction EXACT T-exit does not cut correlated STAR\nPASS restriction FLOW-entry/exit retains actual T\nPASS restriction U-exit rejects concrete T\nPASS restriction absent exit = none\nCONFIRMED inherited-field-exclusion bug: actual=x.g/STAR/{f}/T intended=x.g/STAR/{}/T; x.g.f is wrongly lost\nCONFIRMED STAR-demand adapter gap: current meet rejects MUST-input with STAR-entry; required by preserved STAR demands in later forward runs\n",
    "scope": "Current scalar AP emission/restriction. 14 expected behavior checks; confirms inherited-E defect and MUST/STAR adapter gap. No method actor or project run; implementation unchanged."
  },
  "history": {
    "balanced_seed_return_design": {
      "decision": "F57",
      "date": "2026-10-06",
      "commit": "efd7b637374b6011f69964ebfdac6c8f6562f941"
    },
    "explicit_no_restriction_wording": {
      "date": "2026-10-07",
      "commit": "6b2b0fd5b"
    },
    "first_analyzer_implementation": {
      "date": "2026-10-11",
      "commit": "b65b46d766790956bbfd50efaf74e706271eddf3"
    },
    "STAR_to_ANY_widening": {
      "date": "2026-10-16",
      "commit": "28a123f0eac937e8f2feca9ee5dd84e38fa8f979"
    }
  },
  "remaining_acceptance_obligations": [
    "Typed preserved-STAR builder and scalar/packed emission correspondence",
    "MUST-input/STAR-entry cell with the original guarantee and layer handling",
    "Producer proof of original abstract STAR/nonempty-E exclusion guard",
    "General marked/correlated extension scope beyond original non-STAR concrete inputs"
  ]
}
```
