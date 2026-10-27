# Restricted-run fact management with original AP demand

Date: 27 October 2026. Status: **baseline design; static demand completion selected**.
The analyzer implementation is unchanged. The selected follow-up is
[static demand closure and run-1 exit routing](../../spec/restricted-demand-static-closure.md).

Reference: [AP sections 6.3, 6.4, 8.5–8.7 and 9.2](../../spec/ap.md), with the
selected concrete-STAR and FLOW-replacement extensions. Runtime core under
review: `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
See the [scope review](../reports/bidirectional-restricted-demand-scope-review-20261027.md).

No project was rerun. The referenced Thingsboard campaign reached **run-2**,
completed **run-1**, and accepted **run-1**. The controls below start no analysis
iteration. This document does not claim a new performance result.

## 1. Selected design and semantic scope

Every restricted run uses demand to select its initial facts and publications.
Use the existing AP operations. An actual input is data to match against demand;
its arrival does not grant an independent execution or publication permission.

| Boundary | Current runtime | Baseline design |
|---|---|---|
| Initial emission | Actual-input queries plus concrete guide intersections | Original AP emission from all matching demand entries, including FLOW |
| Missing entry demand | Canonical actual input can start | No nonzero initial from that arrival |
| Summary publication | Admitted query can bypass exit demand | Original complete entry/exit restriction |
| Late actual caller | Can trigger an authorization scan over all raw summaries | Read already published answers and records; do not rescan unrelated raw answers |
| NORMAL singleton handoff | Run-1 can select it as both guide and record | Original record-only routing |
| Static completion | General SQ plus same-field EXACT expansion | Frozen static demand closure, defined in the selected follow-up; no general query permission |

These are **major changes** to the current admission and publication policy.
They restore the ordinary AP demand contract. They are not representation-only
optimizations. The design applies to both restricted directions.

Keep the following behavior:

- Run-2 is backward, FULL, field limit 1. Run-3 is forward, FULL, limit 2;
  later limits grow under the current policy. No run has field limit zero.
- Keep current field transfer, strong later-run writes, exclusions, rule
  conditions/actions, cleaners, aliases, source/sink identities and ND support.
- Keep the selected correlated concrete STAR seed. Do not change it back to
  ANY to reproduce an older start table.
- Keep the existing FLOW coverage test, protected marked dependencies and
  annotation transport. A control below exposes a static interaction which
  the repair must cover; it does not authorize a new protection flag.
- Keep ZERO discovery, sink seeds, source-hit handling, balanced backward ZERO
  return, and ordinary native-record application.
- Sections 8 and 10 analyze the current run-1 static procedure and its erased
  static/static rows. The selected follow-up retains thin static seeds and
  routes producer results through NormalExit. It does not restore static
  CFG propagation.
- Keep the selected run-1 layer override for this baseline. Its all-taint
  DEMAND policy in FULL mode is a separate scope issue; this document does not
  silently promote those facts to NORMAL.

Demand selection at the handoff is restored to the original rule. This does
not change a raw fact's layer. A run-1 TAINT already marked DEMAND remains
selected. A genuinely NORMAL singleton supplies its record only.

No IR, rule specialization, reference manager, cache, or caller-context change
is part of this design. No GroundingSupport is added. This document follows
[proof-guide.md](../../spec/proof-guide.md).

## 2. Storages and ownership

| Storage | Owner and lifetime | Key and value | Purpose |
|---|---|---|---|
| Incoming demand | Shared immutable view for one run | Method and normalized entry/optional exit patterns | Select starts and outgoing pairs |
| Native records | Shared read-only view during the run; persistent across barriers | Method, native direction, complete initial; NORMAL conclusion | Reuse proven normal relations and permitted reversed views |
| Caller inputs/subscriptions | Caller runner, one run | Callee, call/stage, complete caller original, layer and typed input header; merged actual facts | Apply old or future callee answers to their real caller inputs |
| Initials | Method actor, one run | Complete canonical initial, including mark, tail and legal E | Start each demanded assumption once across all callers |
| Point facts | Method actor, one run | Statement, complete original premise, typed header; merged facts and protection | Deduplicate processed facts and keep real local rule observations |
| Worklist | Method actor, one run | Newly admitted point/annotation deltas and resume location | Propagate only admitted work under the existing fair schedule |
| Raw summaries | Method actor, one run | Complete original and typed conclusion header | Keep computed exit relations; provide NORMAL persistence |
| Selected publications | Method actor, one run | Original and restricted conclusion | Supply the next handoff under the original selection rule |
| Published summaries | SummaryStorage/publication index, one run | Complete premise and restricted conclusion | Replay existing answers and notify subscribers of fresh deltas |
| Pending publication batch | Method actor, detached at its existing queue barrier | Fresh publication deltas | Send the admitted batch through ordinary publication deduplication |

There is no callee added-fact history. Caller subscriptions already retain the
actual data needed to apply an answer. There is no `admittedQueries` permission
set, per-query exit permission or query-triggered raw-summary backfill in this
baseline. There are no later-run mark requests or R/P request updates.

Keep typed headers and full premise identity. Do not merge two originals into
one arbitrary mark product. Caller references do not become part of canonical
method initial keys. Protection is merged by OR at its exact coordinates;
it is not a new ordinary fact key.

## 3. Arriving call input

Registration retains the existing two independent answer routes:

```kotlin
fun enterCallee(callee: MethodKey, ref: CallerRef, actual: Facts) {
    // Register before reading existing publications. Later publications notify
    // this same directory. The complete AP predicate checks each candidate.
    subscriptions.registerAndReplay(callee, ref, actual)
    records.replayApplicable(callee, ref, actual)

    sendToCalleeOwner(LinkIn(callee, actual))
}
```

These names describe the existing protocol, not an extra record-replay pass.
Keep the actual registration/replay implementation's arrival-order guarantee.
An answer which arrives first is found by replay. An input which arrives first
is found by the later publication notification.

One record answering one part does not certify that every demanded body path
is answered. Do not skip all method execution after the first record match.
A record does not itself create an initial.

On the callee owner:

```kotlin
fun onAdded(actual: Facts) {
    if (actual is Reach) {
        existingZeroInputRule(actual)
        return
    }

    val candidates = linkedSetOf<DemandPattern>()
    for (leaf in ops.leaves(actual)) {
        candidates += demand.near(method, leaf)
    }
    for (pattern in candidates) {
        for (initial in ops.emit(pattern, actual)) {
            startOnce(initial)
        }
    }
}

fun startOnce(initial: InitialAp) {
    validateDirectionAndBound(initial)
    if (!initials.add(initial)) return
    admitAtEntry(initial, ops.startFact(initial, mode))
}
```

The original emitter handles each leaf's real E/mx and mark. Do not synthesize
a demand from the input itself. Do not filter out abstract guide entries.
Concrete demands cannot get T from a FLOW input. A group selector, where the
selected mark-domain adapter permits it, retains the actual FULL identity.

```text
entry demand                 emitted original
ret/[any]/FLOW                ret/*/FLOW, shared across incoming Ti
ret/[any]/T                   the actual intersection with T
no matching entry            none
```

There is no unconditional ANY-to-EXACT start. A concrete guide can produce its
ordinary exact intersection. A normal EXACT relation also has its record path.
Backward MUST initials remain invalid. Apply the existing field limit and
static grammar checks without inventing a broad marked root/class input.

## 4. Processing point facts

```kotlin
fun admitAt(node: Statement, original: PremiseKey, offered: Facts) {
    val bounded = existingFieldLimitAndChecks(offered)
    val fresh = pointFacts.add(node, original, bounded) ?: return
    worklist.add(EdgeDelta(original, node, fresh))
}

fun process(delta: EdgeDelta) {
    existingStatementsRulesAndCalls(delta) { next, original, result ->
        admitAt(next, original, result)
    }
}
```

Ordinary deltas and protection growth must both progress. Keep the present
unchanged-fact handling and counted queued continuations. Do not remove local
concrete membership merely because a summary FLOW row can replace it.

Restricted execution raises no mark requests. A concrete dependency barrier
must get its marked initial from demand or its permitted record path. This
invariant is central to the static gap in section 8.

## 5. Computed summaries and publication

The raw value and the published restriction have different owners and roles:

```kotlin
fun onSummary(original: PremiseKey, offered: Facts) {
    val rawDelta = rawSummaries.add(original, offered) ?: return
    val selected = ops.demandPart(original, rawDelta, direction) != null

    val pieces = if (direction == BACKWARD && original.isZero) {
        listOf(rawDelta) // Existing balanced-return exception.
    } else {
        val out = linkedSetOf<Facts>()
        original.forEachMember { member ->
            for (pattern in demand.covering(method, member)) {
                out += ops.restrict(member, rawDelta, pattern)
            }
        }
        out.toList()
    }

    for (piece in pieces) {
        // Retain the whole original, including all ND members.
        if (selected) selectedPublications.add(original, piece)
        pendingPublications.add(Publication(original, piece))
    }
}
```

Actual code can combine selected-store and publication-index deduplication.
The semantic rule is the union of the ordinary restriction results. Do not
drop a required annotation delta. Do not publish a narrower record instead
of retaining the raw NORMAL relation for persistence.

Restriction requires whole-member containment, not overlap. It checks D-p's
mark, base, field path and tail. An absent D-p gives no ordinary publication.
Each ND publication retains its complete premise; caller application still
requires all members. Keep the existing backward ZERO exception alone.

There is no branch equivalent to:

```kotlin
if (currentQueries.permits(original)) publish(rawDelta)
```

The incoming demand is immutable. Every permitted exit for a computed original
is already available when that summary is first restricted. A later caller
does not create a new exit permission. It reads the published answer from
SummaryStorage. Thus ordinary input arrival needs no scan over raw summaries.

## 6. Applying answers and records

```kotlin
fun onPublication(subscription: Subscription, publication: Publication) {
    val matched = ops.satisfying(
        subscription.added, publication.premise.member(member), mode
    ) ?: return
    existingWholePremiseJoinAndSummaryApplication(subscription, publication, matched)
}
```

Use the existing summary composition, mark correlation, ND join, binding-back,
aliases, exclusion rules, layers and protection transport. A shared FLOW answer
is instantiated against each caller's actual Ti. It does not make the callee
execute separately for every Ti.

ZERO satisfies a static premise only in run-1. Later runs need the real static
input. Record application keeps native direction and permitted reversal views;
it does not grant extra initial or publication permissions.

## 7. Barrier and next-run ownership

```kotlin
fun afterCompleteRun() {
    joinAllCountedWorkAndPublicationDelivery()
    persistEligibleRawNormalSingletons(rawSummaries)
    val nextDemand = projectSelectedPublications()
    val nextSeeds = existingSinkOrSourceHitProjection()
    releaseRunLocalStores()
    startNextRun(nextDemand, nextSeeds, records.readOnlyView())
}
```

NORMAL singleton records do not also become selected demand. Keep normal
multi-premise and backward ZERO selection, and project each required premise
member. Selection does not change a layer. Keep nonempty legal E in NORMAL
records. Keep the existing demand normalization and current FULL sink/source
occurrence identities.

Normal singleton omission from demand is not a gap by itself. An unproved
partial or demand-layer result cannot be made into a normal record to avoid
the decision below.

## 8. The remaining gap from run-1 static handling

The baseline above is complete as a fact-management policy. It is not yet a
complete integration with the current run-1 static approximation. That
approximation removes dependencies which original AP demand would use.

Use the selected early-static rules, no aliases or external models, and no
unrelated native record. The following are derived run-1 exports, not a new
project capture. The controls start from these exports and test the original
AP operations and restriction gates.

### 8.1 Static callee entry and answer

```java
void copy() { C.out = C.in; }
Object get() { copy(); return C.out; }
```

Run-1 omits `C.in -> C.out` in `copy`. The read in `get` produces
`C.out -> return`; it does not receive and locally propagate the removed
static copy relation to produce `C.in -> return`.

```text
run-1 get export:       C.out/FLOW -> ret/FLOW, DEMAND
backward get guide:     ret/[any]/FLOW -> C.out/*/FLOW

run-2 actual ret/T
  -> demanded ret/*/FLOW
  -> C.out/*/FLOW before the backward copy() call
```

With only explicit original demand, `copy` can have no matching start. That
is the known static-relay gap. A repair must also permit its computed answer.
It must run the real body; it cannot assume identity through writes.

### 8.2 A static-only callee repair still leaves the wrapper exit blocked

Grant `copy` a correct entry and answer for the previous example. It computes:

```text
copy answer:            C.out -> C.in
get raw backward edge:  ret -> C.in
get old permitted exit: C.out
```

The original `get` restriction rejects C.in because it differs from C.out.
The missing pair is at a **nonstatic original** in `get`, not only at the
static original in `copy`. An S-to-S default in the callee alone does not
close this boundary.

The same issue can require a nonstatic output:

```java
void set(Object p) { C.out = p; }
Object get(Object p) { set(p); return C.out; }
```

The early run-1 procedure can retain both productive pairs in `get`:

```text
forward exports:  arg(0) -> C.out,  C.out -> ret
backward guides:  C.out -> arg(0),  ret -> C.out

run-2 body:       ret -> C.out -> arg(0)
required answer:  ret -> arg(0)
```

Neither existing pair authorizes that answer under C5. The `ret -> C.out`
pair has the wrong exit base. The `C.out -> arg(0)` pair has the wrong entry
base for the complete original `ret`. Ordinary restriction does not compose
these pairs transitively. Records cannot repair this case by assuming the
missing NORMAL `arg(0) -> ret` relation already exists.

The FLOW controls compute a NORMAL raw backward answer; they do not demote
it. That new answer can enter records at the next barrier, but it was not
in the read-only record view for the current run. Its later persistence is
not permission to return it to the waiting caller now. This is a witness
about preservation of the required finite run-2 derivation, not a claim
that every possible later execution has been enumerated.

This is a further boundary of the same run-1 static erasure/early-emission gap.
It does not justify granting every query in every method unrestricted results.
My earlier suggestion that an exception on static input/output bases alone
would suffice did not cover this wrapper case.

### 8.3 Marked dependency barriers must also remain reachable

A field-only widening is not a complete repair. A shared FLOW initial can
reach a selected cleaner inside the static bridge:

```java
void bridge() {
    Box x = new Box();
    x.value = C.in;
    removeTAtExactRoot(x);
    C.out = x.value;
}
Object get() { bridge(); return C.out; }
```

For the legal bounded inputs used by the control:

```text
shared ret/FLOW -> C.out/FLOW -> x.value/FLOW
  selected cleaner excludes T from FLOW
  -> C.in/FLOW excluding T

even if the static exit is widened:
  this FLOW answer gives no C.in/T answer to caller ret/T

marked ret/T -> C.out/T -> x.value/T
  exact-root cleaner preserves this descendant
  -> C.in/T, protected
```

The actual AP control gives zero caller-T answers on the FLOW route and one
on the marked route. It also confirms that a plain STAR static-read T
relation can be removed by its matching FLOW relation. The current static
pool read materialization does not automatically copy a remote writer's
protection into that plain read.

Thus the repair must account for required marked starts and their wrapper
continuations. It cannot invent T from an abstract input after run-1, remove
the selected cleaner, or rely on general SQ to hide the missing guide.
This is a local legal-AP witness, not a new whole-JVM false-negative result.

## 9. Selected repair: static demand completion

The user selected completion of demand at the run-1-to-run-2 handoff. Keep
the original emitter and C5 publication. Collect the static/static relations
which run-1 does not publish to callers. Make them visible to transitive
callers and compose through static positions, including productive wrapper
pairs and colored mark dependencies. The complete selected contract is in
[static demand closure and run-1 exit routing](../../spec/restricted-demand-static-closure.md).

That specification separates an eager least fixed point from an equivalent
factored demand view. Only guidance is completed. It creates no executable
NORMAL summary or general actual-query permission. Shared static carry stays
a separate demand family. There is no ANY-to-EXACT query expansion.

The user also selected routing run-1 static producer conclusions to
`graph.exitInst`: the NormalExit boundary after return. Only exit rules and
common summary emission run there. Producer write effects remain immediate;
the skipped body and return transfer do not execute on the shortcut.

The controls below are the original baseline/gap evidence, before this
repair was selected. Their exact missing pairs are witnesses of the gap,
not proofs of the full completion algorithm. The follow-up provides the
constructive closure model and finite design oracle. No analyzer code has
been changed and no new performance result is claimed.

## 10. Proof and validation scope

The [local model](../../spec/lean/proposals/restricted-demand/RestrictedDemand.lean)
uses the original `emitW` and `restrictI` operations. Ten constructive theorems
check demand-sourced emission/publication, shared FLOW emission, acceptance
of a static callee answer, rejection of the changed wrapper exits, and
executable exact missing pairs which admit those answers. No repair policy
is proved by choosing those individual pairs.

The original C2/C5 certificates in `ApSpec.CurrentDemand` supply the general
emission/restriction contracts. Point-store, publication-index, ND and typed
adapter correspondence remain their existing obligations. This proposal
does not claim a whole current JVM iteration theorem.

Seven actual Kotlin AP/store control outcomes pass. They cover the copy and
setter wrapper gaps with FLOW and concrete T originals, hidden selected
cleaning under a widened static exit, and static-read FLOW subsumption.
They do not run the method actors or compile the example Java programs.

All ten Lean declarations pass the axiom audit with only `propext` and
`Quot.sound`. There is no classical choice, new axiom or unproved placeholder.
The successful run imports the minimal original AP definitions. Earlier
failed setup attempts are excluded from this result.

Implementation gates for the selected repair include:

- Demand-only nonstatic starts, shared FLOW initials, C5 exit rejection,
  absent exits, nonempty legal E, and no concrete mark from FLOW.
- Complete ND support, protected dependencies, both publication/input arrival
  orders, and late caller replay without raw-summary authorization scans.
- ZERO discovery and balanced return, sink/end-fact seeds, source hits,
  native records and normal singleton record-only handoff.
- Static copy/setter wrappers, marked static barriers, actual strong kills,
  class markers, changed marks/groups, recursion and both directions.
- OWASP and the configured project campaign after implementation. Record the
  latest reached/completed/accepted iteration and compare complete semantic
  results; do not infer equivalence from an OOM prefix.

The following appendix embeds the control source, outputs and receipts.

### 10.1 Exact local results

This receipt is the historical baseline/gap check. Its
`REPAIR_UNSELECTED` state and `decision_required` field describe that check's
time, not the current selected policy in section 9. The follow-up has a
separate receipt for the closure model.

```json
{
  "state": "LOCAL_BASELINE_AND_GAP_CHECKED_REPAIR_UNSELECTED",
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
    "source": "spec/lean/proposals/restricted-demand/RestrictedDemand.lean",
    "source_sha256": "4059e4ef9fc79dff4cc55d1e8774f86e81143096e7e839c13742693c2a31def4",
    "import": "ApSpec.AbsDefs",
    "theorems": 10,
    "exit_code": 0,
    "observed_axioms": [
      "propext",
      "Quot.sound"
    ],
    "scope": "Original demand gates and local wrapper rejection/missing-pair witnesses. No whole-JVM or repair-policy proof."
  },
  "actual_AP_controls": {
    "source_sha256": "cad0796ef7c739e9ef66817fa7f9a942cc1a4c29e572b0f1c5d1ed4dadcd5b7a",
    "compile_exit_code": 0,
    "run_exit_code": 0,
    "scenario_outcomes": 7,
    "output": "PASS hidden-selected-cleaner/FLOW widenedStaticExit=allows callerTAnswer=0\nPASS copy/FLOW calleeStaticAnswer=allowed wrapperChangedField=blocked exactMissingPair=allows\nPASS setter/FLOW calleeProductiveAnswer=allowed wrapperNonstaticExit=blocked exactMissingPair=allows\nPASS static-read/T ordinarySTARreadRelation=subsumedByFLOW noNewProtectionAssumed\nPASS hidden-selected-cleaner/T widenedStaticExit=allows callerTAnswer=1\nPASS copy/T calleeStaticAnswer=allowed wrapperChangedField=blocked exactMissingPair=allows\nPASS setter/T calleeProductiveAnswer=allowed wrapperNonstaticExit=blocked exactMissingPair=allows\n",
    "scope": "Actual AP reverse-shaped edge applications, selected cleaning, restriction, summary application and static-read summary subsumption. Run-1 exports are derived from selected static rules; no frontend or actor run."
  },
  "decision_required": [
    "Complete static-related demand, including wrapper entry/exit and marked dependencies",
    "Explicit static-related query exception with a defined wrapper scope"
  ]
}
```

### 10.2 AP control source

<details>
<summary>Full Kotlin control; temporary values only</summary>

```kotlin
package org.opentaint.dataflow.bidi.engine
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.RunSummaryStore

object RestrictedDemandGap {
 @JvmStatic fun main(args:Array<String>) {
  for(concrete in listOf(false,true)) checkCase(concrete)
 }
 private fun checkCase(concrete:Boolean) {
  val f=StoreFixtures(); val m=f.manager; val ops=f.ops
  val mode=ApMode(false,Direction.BACKWARD,1)
  val ret=AccessPathBase.Return; val arg=AccessPathBase.Argument(0)
  val cls=m.accessors.index(ClassStaticAccessor("C")); val out=f.field("out"); val input=f.field("in")
  val t=MarkSlot.Concrete(f.mark("T")); val mark=if(concrete)t else MarkSlot.STAR
  fun p(base:AccessPathBase,path:List<Int> = emptyList(),tail:Tail=Tail.STAR,atom:MarkSlot=mark)=f.pattern(base,path,tail,atom)
  val outPath=listOf(cls,out);val inPath=listOf(cls,input)
  val getter=DemandPattern(p(ret,tail=Tail.ANY),p(STATIC,outPath))
  val writer=DemandPattern(p(STATIC,outPath,Tail.ANY),p(arg))
  val actual=f.fact(ret,tail=Tail.ANY,mark=t,layer=Layer.DEMAND)
  val original=ops.emit(getter,actual).single()
  check(original.isFlow == !concrete)
  fun edge(from:Pattern,to:Pattern)=PathEdge(from.fact,to.fact,ExclusionSet.Empty)
  fun apply(value:Facts,initial:PremiseKey,e:PathEdge):Facts {
   val out=CollectingOut();ops.applyEdge(value,initial,e,true,mode,out);return out.results.single()
  }
  val retToStatic=edge(p(ret,atom=MarkSlot.STAR),p(STATIC,outPath,atom=MarkSlot.STAR))
  val atCall=apply(ops.startFact(original,mode),original,retToStatic)
  val current=ops.leaves(atCall).single()
  val helperInitial=m.initial(current)
  val copy=edge(p(STATIC,outPath,atom=MarkSlot.STAR),p(STATIC,inPath,atom=MarkSlot.STAR))
  val copyAnswer=apply(atCall,helperInitial,copy)
  val staticDefault=DemandPattern(p(STATIC,tail=Tail.ANY),p(STATIC,atom=MarkSlot.STAR))
  check(ops.restrict(helperInitial,copyAnswer,staticDefault).isNotEmpty())
  check(ops.restrict(original,copyAnswer,getter).isEmpty())
  check(ops.restrict(original,copyAnswer,DemandPattern(getter.entry,p(STATIC,inPath))).isNotEmpty())
  val x=AccessPathBase.LocalVar(7);val value=f.field("value")
  val toX=edge(p(STATIC,outPath,atom=MarkSlot.STAR),p(x,listOf(value),atom=MarkSlot.STAR))
  val xInput=apply(atCall,helperInitial,toX)
  val cleaned=CollectingOut();ops.clean(xInput,helperInitial,Cleaner(x,null,CleanReach.EXACT,t.mark),mode,cleaned)
  val fromX=edge(p(x,listOf(value),atom=MarkSlot.STAR),p(STATIC,inPath,atom=MarkSlot.STAR))
  val hiddenBarrier=apply(cleaned.results.single(),helperInitial,fromX)
  val broadExit=getter.copy(exit=p(STATIC,atom=MarkSlot.STAR))
  val broadPublished=ops.restrict(original,hiddenBarrier,broadExit).single()
  val supplied=CollectingOut();ops.applySummary(actual,original,broadPublished,mode,supplied)
  check(supplied.results.isNotEmpty()==concrete)
  println("PASS hidden-selected-cleaner/"+(if(concrete)"T"else"FLOW")+" widenedStaticExit=allows callerTAnswer="+supplied.results.size)
  val set=edge(p(STATIC,outPath,atom=MarkSlot.STAR),p(arg,atom=MarkSlot.STAR))
  val setAnswer=apply(atCall,helperInitial,set)
  check(ops.restrict(helperInitial,setAnswer,writer).isNotEmpty())
  check(listOf(getter,writer).flatMap{ops.restrict(original,setAnswer,it)}.isEmpty())
  check(ops.restrict(original,setAnswer,DemandPattern(getter.entry,p(arg))).isNotEmpty())
  println("PASS copy/"+(if(concrete)"T"else"FLOW")+" calleeStaticAnswer=allowed wrapperChangedField=blocked exactMissingPair=allows")
  println("PASS setter/"+(if(concrete)"T"else"FLOW")+" calleeProductiveAnswer=allowed wrapperNonstaticExit=blocked exactMissingPair=allows")
  if(!concrete) {
   val readInitial=m.initial(p(STATIC,outPath,atom=MarkSlot.STAR))
   val markedInitial=m.initial(p(STATIC,outPath,atom=t))
   val readFlow=m.factsOf(p(ret,atom=MarkSlot.STAR).fact,ExclusionSet.Empty,Layer.DEMAND)
   val readT=m.factsOf(p(ret,atom=t).fact,ExclusionSet.Empty,Layer.DEMAND)
   val store=RunSummaryStore(m,flowBacked=true)
   check(store.add(readInitial,readFlow)!=null)
   check(store.add(markedInitial,readT)==null)
   println("PASS static-read/T ordinarySTARreadRelation=subsumedByFLOW noNewProtectionAssumed")
  }
 }
}
```

</details>

### 10.3 Lean source and kernel output

<details>
<summary>Full local model and ten axiom audits</summary>

```lean
/-
  Proposal model. No production behavior changes.
  Original AP demand gates, plus local witnesses for static-erasure gaps.
  The wrapper raw answers are checked by a separate actual AP control.
  No whole-JVM, complete-run or selected repair-policy theorem is claimed.
-/
import ApSpec.AbsDefs

namespace RestrictedDemandDesign
open ApSpec ApSpec.Abs ApSpec.Handoff
set_option autoImplicit false

def emitBatch (ds : List DemandEdge) (a : PFact) : List PFact :=
  ds.filterMap (fun d => emitW d.din a)

def publishBatch (ds : List DemandEdge) (j : PFact) (g : AFact) : List AFact :=
  ds.filterMap (fun d => restrictI j g d)

theorem emitted_has_demand (ds : List DemandEdge) (a j : PFact)
    (h : j ∈ emitBatch ds a) :
    ∃ d, d ∈ ds ∧ emitW d.din a = some j := by
  exact List.mem_filterMap.mp h

theorem published_has_pair (ds : List DemandEdge) (j : PFact) (g out : AFact)
    (h : out ∈ publishBatch ds j g) :
    ∃ d, d ∈ ds ∧ restrictI j g d = some out := by
  exact List.mem_filterMap.mp h

theorem empty_demand_starts_none (a : PFact) : emitBatch [] a = [] := rfl
theorem empty_demand_publishes_none (j : PFact) (g : AFact) :
    publishBatch [] j g = [] := rfl

-- S=1, return=2, argument=3; class accessor=4, named fields=5 and 6.
def staticOut : PFact := ⟨1,[4,5],.star (.set []),.star⟩
def staticIn : PFact := ⟨1,[4,6],.star (.set []),.star⟩
def argument : PFact := ⟨3,[],.star (.set []),.star⟩
def returned : PFact := ⟨2,[],.star (.set []),.star⟩
def retEntry : PFact := ⟨2,[],.any,.star⟩
def getGuide : DemandEdge := ⟨retEntry,some staticOut⟩
def writerGuide : DemandEdge :=
  ⟨⟨1,[4,5],.any,.star⟩,some argument⟩
def actualReturn (t : Mark) : PFact := ⟨2,[],.any,.conc t⟩
def rawStatic : AFact := ⟨staticIn,false⟩
def rawArgument : AFact := ⟨argument,false⟩
def staticCarry : DemandEdge :=
  ⟨⟨1,[],.any,.star⟩,some ⟨1,[],.star (.set []),.star⟩⟩

theorem flow_initial_shared (t : Mark) :
    emitBatch [getGuide] (actualReturn t) = [returned] := rfl

theorem static_callee_answer_is_permitted :
    publishBatch [staticCarry] staticOut rawStatic = [rawStatic] := rfl

theorem wrapper_rejects_changed_static_exit :
    publishBatch [getGuide] returned rawStatic = [] := rfl

theorem wrapper_rejects_nonstatic_exit_even_with_writer_pair :
    publishBatch [getGuide,writerGuide] returned rawArgument = [] := rfl

-- Executable exact missing pairs, not a selected completion algorithm.
def missingStaticPair : DemandEdge := ⟨retEntry,some staticIn⟩
def missingArgumentPair : DemandEdge := ⟨retEntry,some argument⟩

theorem missing_static_pair_permits_answer :
    publishBatch [getGuide,missingStaticPair] returned rawStatic = [rawStatic] := rfl

theorem missing_argument_pair_permits_answer :
    publishBatch [getGuide,writerGuide,missingArgumentPair] returned rawArgument =
      [rawArgument] := rfl

#print axioms emitted_has_demand
#print axioms published_has_pair
#print axioms empty_demand_starts_none
#print axioms empty_demand_publishes_none
#print axioms flow_initial_shared
#print axioms static_callee_answer_is_permitted
#print axioms wrapper_rejects_changed_static_exit
#print axioms wrapper_rejects_nonstatic_exit_even_with_writer_pair
#print axioms missing_static_pair_permits_answer
#print axioms missing_argument_pair_permits_answer
end RestrictedDemandDesign
```

```text
'RestrictedDemandDesign.emitted_has_demand' depends on axioms: [propext, Quot.sound]
'RestrictedDemandDesign.published_has_pair' depends on axioms: [propext, Quot.sound]
'RestrictedDemandDesign.empty_demand_starts_none' depends on axioms: [propext]
'RestrictedDemandDesign.empty_demand_publishes_none' depends on axioms: [propext]
'RestrictedDemandDesign.flow_initial_shared' depends on axioms: [propext]
'RestrictedDemandDesign.static_callee_answer_is_permitted' depends on axioms: [propext]
'RestrictedDemandDesign.wrapper_rejects_changed_static_exit' depends on axioms: [propext]
'RestrictedDemandDesign.wrapper_rejects_nonstatic_exit_even_with_writer_pair' depends on axioms: [propext]
'RestrictedDemandDesign.missing_static_pair_permits_answer' depends on axioms: [propext]
'RestrictedDemandDesign.missing_argument_pair_permits_answer' depends on axioms: [propext]
```

</details>

### 10.4 Successful execution receipts

<details>
<summary>Commands, source hashes and successful return codes</summary>

```json
{
  "lean": {
    "command": [
      "lean",
      "-j",
      "1",
      "-M",
      "512",
      "-o",
      "/drive-testcomp/opentaint-go-rules/restricted-demand-design-20261027/RestrictedDemand.olean",
      "/drive-testcomp/opentaint-go-rules/opentaint-w3/spec/lean/proposals/restricted-demand/RestrictedDemand.lean"
    ],
    "exit_code": 0,
    "seconds": 0.29671940207481384,
    "source_sha256": "4059e4ef9fc79dff4cc55d1e8774f86e81143096e7e839c13742693c2a31def4",
    "output": "'RestrictedDemandDesign.emitted_has_demand' depends on axioms: [propext, Quot.sound]\n'RestrictedDemandDesign.published_has_pair' depends on axioms: [propext, Quot.sound]\n'RestrictedDemandDesign.empty_demand_starts_none' depends on axioms: [propext]\n'RestrictedDemandDesign.empty_demand_publishes_none' depends on axioms: [propext]\n'RestrictedDemandDesign.flow_initial_shared' depends on axioms: [propext]\n'RestrictedDemandDesign.static_callee_answer_is_permitted' depends on axioms: [propext]\n'RestrictedDemandDesign.wrapper_rejects_changed_static_exit' depends on axioms: [propext]\n'RestrictedDemandDesign.wrapper_rejects_nonstatic_exit_even_with_writer_pair' depends on axioms: [propext]\n'RestrictedDemandDesign.missing_static_pair_permits_answer' depends on axioms: [propext]\n'RestrictedDemandDesign.missing_argument_pair_permits_answer' depends on axioms: [propext]\n"
  },
  "actual_AP": {
    "scope": "Actual AP gates, hidden selected cleaner and summary-store controls; no project/Gradle/actor run",
    "source_sha256": "cad0796ef7c739e9ef66817fa7f9a942cc1a4c29e572b0f1c5d1ed4dadcd5b7a",
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
        "/drive-testcomp/opentaint-go-rules/restricted-demand-design-20261027/classes",
        "/drive-testcomp/opentaint-go-rules/restricted-demand-design-20261027/RestrictedDemandGap.kt"
      ],
      "exit_code": 0,
      "seconds": 2.061293050646782
    },
    "run": {
      "command": [
        "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
        "-Xmx256m",
        "-XX:ActiveProcessorCount=1",
        "-cp",
        "/drive-testcomp/opentaint-go-rules/restricted-demand-design-20261027/classes:/drive-testcomp/opentaint-go-rules/restricted-demand-review-20261027/classes:/drive-testcomp/opentaint-go-rules/protection-necessity-20261027/ap/classes:/home/sobol/.gradle/caches/8.10/workerMain/gradle-worker.jar:/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/fixture-cache:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/java/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-configuration-rules/configuration-rules-common/build/libs/configuration-rules-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-ir/opentaint-ir-api-common/build/libs/opentaint-ir-api-common.jar:/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-utils/common-util/build/libs/common-util.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.detekt.sarif4k/sarif4k-jvm/0.5.0/d3060993cd73b57ee61b260841bedcabb7dcbb02/sarif4k-jvm-0.5.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/io.github.microutils/kotlin-logging-jvm/3.0.5/82f2256aeedccfd9c27ea585274a50bf06517383/kotlin-logging-jvm-3.0.5.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-collections-immutable-jvm/0.3.8/6119a57df1ad662593dfe21954898183c6c933b4/kotlinx-collections-immutable-jvm-0.3.8.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test-junit5/2.1.0/3d386bb97b74923e498d46193f7a380de10734a4/kotlin-test-junit5-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-test/2.1.0/bab38f61fdb1c90a68fce9666b3f9fe419aeef72/kotlin-test-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-coroutines-core-jvm/1.10.0/37966d769934a42566dec1ca2e1da6e5565c4e06/kotlinx-coroutines-core-jvm-1.10.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk7/2.1.0/d77bee6c7bc849e7b9bf4b83e94e8fd1dfc0ea8a/kotlin-stdlib-jdk7-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.charleskorn.kaml/kaml-jvm/0.73.0/abeffe03e958d06cfa6496ecf7c3be9e566c33cf/kaml-jvm-0.73.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-json-jvm/1.7.3/6701e8c68d9e82387ce72ee96e8ddf058208d58f/kotlinx-serialization-json-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlinx/kotlinx-serialization-core-jvm/1.7.3/1f226780b845ff9206474c05159245d861556249/kotlinx-serialization-core-jvm-1.7.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.krzeminski/snakeyaml-engine-kmp-jvm/3.1.1/542190d973fb66f3568fbcec1a3a8210e2f705dc/snakeyaml-engine-kmp-jvm-3.1.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/com.squareup.okio/okio-jvm/3.10.2/6a2cc3acd5a83e66075a2f6c5b0608b6043fa34c/okio-jvm-3.10.2.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/net.thauvin.erik.urlencoder/urlencoder-lib-jvm/1.6.0/6b922dd3ff960b08873c10395545e08355e250c9/urlencoder-lib-jvm-1.6.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib/2.1.20/aa8ca79cd50578314f6d1180c47cbe14c0fee567/kotlin-stdlib-2.1.20.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains.kotlin/kotlin-stdlib-jdk8/2.1.0/c4a51be16c840b969ed706bc25d5836b099d188a/kotlin-stdlib-jdk8-2.1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/it.unimi.dsi/fastutil-core/8.5.13/dd3d3ed477b7c1aee8176f6684813f48304769f9/fastutil-core-8.5.13.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/info.leadinglight/jdot/1.0/8e84489791d7fe20bf1631e791152b554cfea4ba/jdot-1.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.jetbrains/annotations/23.0.0/8cc20c07506ec18e0834947b84a864bfc094484e/annotations-23.0.0.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.slf4j/slf4j-api/2.0.3/deef7fc81f00bd5e6205bb097be1040b4094f007/slf4j-api-2.0.3.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-launcher/1.10.1/ce85bf5e38bee0989ded9bd468dd4ff78dc0cfa8/junit-platform-launcher-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-engine/1.10.1/f32ae4af74fde68414b8a3d2b7cf1fb43824a83a/junit-platform-engine-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-api/5.10.1/eb90c7d8bfaae8fdc97b225733fcb595ddd72843/junit-jupiter-api-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.platform/junit-platform-commons/1.10.1/2bfcd4a4e38b10c671b6916d7e543c20afe25579/junit-platform-commons-1.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.junit.jupiter/junit-jupiter-engine/5.10.1/6c9ff773f9aa842b91d1f2fe4658973252ce2428/junit-jupiter-engine-5.10.1.jar:/home/sobol/.gradle/caches/modules-2/files-2.1/org.opentest4j/opentest4j/1.3.0/152ea56b3a72f655d4fd677fc0ef2596c3dd5e6e/opentest4j-1.3.0.jar",
        "org.opentaint.dataflow.bidi.engine.RestrictedDemandGap"
      ],
      "exit_code": 0,
      "seconds": 0.14841531217098236,
      "output": "PASS hidden-selected-cleaner/FLOW widenedStaticExit=allows callerTAnswer=0\nPASS copy/FLOW calleeStaticAnswer=allowed wrapperChangedField=blocked exactMissingPair=allows\nPASS setter/FLOW calleeProductiveAnswer=allowed wrapperNonstaticExit=blocked exactMissingPair=allows\nPASS static-read/T ordinarySTARreadRelation=subsumedByFLOW noNewProtectionAssumed\nPASS hidden-selected-cleaner/T widenedStaticExit=allows callerTAnswer=1\nPASS copy/T calleeStaticAnswer=allowed wrapperChangedField=blocked exactMissingPair=allows\nPASS setter/T calleeProductiveAnswer=allowed wrapperNonstaticExit=blocked exactMissingPair=allows\n"
    }
  }
}
```

</details>
