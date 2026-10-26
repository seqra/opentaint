# Correlated concrete initials in run-1

Date: 26 October 2026. Status: **proposed; analyzer code is unchanged**.
Language: ASD-STE100 Simplified Technical English. Technical terms are defined below.

Read this spec with its [proof dossier](run1-correlated-concrete-initials-proofs.md).
The baseline is `f4954c26403bc7ecb8b64018f8aabdd479fd022d`, core tree
`e3ede1a36d3b04d79a23cc93285f385ecd968dbf`. The latest referenced Thingsboard
measurement has **run-1 COMPLETE; run-2 OOM**, including the 16 GiB experiment.
This proposal has no new project measurement. See the
[run-1 census](../docs/reports/bidirectional-run1-protection-coverage-20261026.md)
and [16 GiB report](../docs/reports/bidirectional-run2-16g-memory-20261026.md).

## 1. Selected changes

For FULL run-1, start a concrete STAR initial with the same STAR conclusion.
Keep the DEMAND layer. Preserve that tail through operations which preserve
the initial suffix. Add the equal-output-path STAR cell to summary subsumption.

```text
Current: (x.*, T) -> (x.[any], T), DEMAND
New:     (x.*, T) -> (x.*, T),     DEMAND
```

**This is a semantic change.** It removes an initial approximation. It also
changes the legal conclusion grammar. It is not a factory-only optimization.

| Mechanism | Current | New | Affected contract |
| --- | --- | --- | --- |
| Concrete initial result | Independent output suffix, ANY | Same input/output suffix, STAR | AP start, W2 |
| Same-suffix transport | Concrete STAR is erased or rejected | Legal concrete STAR is retained | Normalization, transfer, summaries |
| Summary replacement | Proved ANY/ANY cell | Existing ANY cell plus equal-path STAR/STAR cell | FLOW coverage, application, handoff |
| Typed representation | No concrete STAR conclusion | A distinct concrete STAR header | Constructors, keys, decode, readers |

The following contracts stay unchanged:

- FULL is the default run-1 mode. GROUP mode keeps its current behavior.
- Public run-1 field limit is 1. Run-2 and later direction/limit rules stay unchanged.
- Requests select the same initials. A request is mark-only. It has no field
  exclusion. Concrete inputs do not relay requests.
- Initial field paths, marks and layers do not change. There is no run-1 ANY
  initial. ZERO and exact global class markers keep their current seeds.
- Every run-1 field exclusion E is Empty. Complete field overwrites kill;
  disjoint fields survive. A residual that needs an exclusion update moves
  to DEMAND and keeps its tail and Empty E.
- Rule conditions, fixed-target assignments, sources, sinks, all contributing
  origins, cleaners and non-subsumable flags keep their current contracts.
- Static activation, the three request sets, writer selection, static summary
  erasure and the universal static DEMAND fallback stay unchanged.
- FLOW priority, barriers, alias-effect classification, normal record
  persistence and original demand emission/restriction stay unchanged.

There is no new grounding support, actual-input validation, dependency graph,
mark token or rule specialization. StrongQueries is not part of the proof.

This spec overrides the concrete-STAR exclusion in [AP W2](ap.md#23-well-formedness-rules),
AP start/normalization, and the ANY-only limit in
[FLOW-backed relations](run1-flow-backed-concrete-relations.md), only in the
FULL run-1 cells defined here. Historical Lean theorems keep their old scope.
In particular, an old W2 proof does not prove the new conclusion invariant.

## 2. Meaning and legal shapes

`T` is one full mark. `F` is an abstract FLOW mark. `N` is NORMAL and `D` is
DEMAND. `p`, `q` and `s` are sequences of field accessors. `$` is EXACT.
`[any]` is a may tail. `[any-taint]` is the existing must tail.
These three tails and STAR are different values.

```text
I = (x.p.*, T)
I -> (y.q.*, T)       means x.p.s/T -> y.q.s/T
I -> (y.q.[any], T)   permits x.p.s/T -> y.q.r/T for independent s and r
```

STAR binds the output suffix to the suffix of the **original initial**.
It does not assert that all fields carry T. An actual input must still supply
the mark. Emitting a mark request does not prove that such an input exists.

The new concrete STAR conclusion is legal only when all these tests pass:

```kotlin
mode.run1 && mode.markMode == FULL
original is InitialAp && !original.isZero
original.tail == STAR && original.exclusion.isEmpty()
original.mark == Concrete(T) && !T.isGroup
conclusion.mark == Concrete(T)
conclusion.exclusion.isEmpty() && conclusion.layer == DEMAND
// The seed or the selected transfer preserves the original suffix.
```

The grammar alone does not prove the last condition. A known copy/summary
operation must establish it. Do not test only equal marks and output paths.
Do not add a runtime support label. The original already owns the suffix.

The existing initial grammar applies. A non-static nonexact initial has a
base and an empty concrete path. A static nonexact initial names class and
field, `S.C.f.*`. A bare class mark remains EXACT, `S.C.$/T`. A whole-static
root is not a new concrete initial. Do not emit a nonexact class-wide mark.

Concrete STAR under ZERO, an ND premise, a different initial mark, an EXACT
initial, or another run is outside this extension. Exact and must sources
do not acquire STAR. In particular, STAR is not another name for must-taint.

## 3. Initial emission

Apply the change after the current request/input match has selected an initial.
Do not change which request matches or widen the actual input at this step.

```kotlin
fun start(initial: InitialAp, mode: ApMode): Facts = when {
    mode.run1 && mode.markMode == FULL &&
        !initial.isZero && initial.tail == STAR && initial.mark is Concrete -> {
        checkRun1Initial(initial)
        taintTree(initial.base, DEMAND, leafAt(initial.path, initial.mark),
            exclusion = Empty, nonExactTail = STAR, nonSubsumable = false)
    }
    else -> currentStart(initial)
}
```

`nonExactTail` is pseudocode for a typed header. It must not use the current
default `DEMAND => ANY`. An initial answer is not a rule assignment. It does
not set the non-subsumable flag.

Use the same start contract when a static point selects its canonical concrete
STAR original. Keep the current static point and call stage. Do not replay
the method from entry. Raw pool membership remains mark availability; it does
not carry a writer's suffix into a reader.

## 4. Transfer and deliberate loss of correlation

Use the current AP geometry cases. Replace the final W2 erasure only when the
new owner and transfer conditions hold. A change to layer alone does not
change a field tail.

| Operation on a legal concrete STAR row | Result |
| --- | --- |
| Identity or copy at the tracked prefix | STAR, same original suffix, D |
| Input is below a copy premise | Append the known path remainder; keep STAR and D |
| Read premise is strictly below the tracked prefix | ANY/D, unless the target is EXACT |
| Explicit may target | ANY/D |
| Field-limit overflow | ANY/D at the retained prefix |
| Ordinary call bindings and diagonal STAR summary | Compose the suffix; keep STAR if the actual input is STAR |
| Summary applied to an actual ANY or EXACT value | Keep the computed ANY or EXACT result; do not recover STAR |
| Complete overwrite | Kill, as now |
| Disjoint write/cleaner/filter | Keep the original tail |
| Field write needs a residual exclusion | Keep STAR, Empty E and D; do not introduce ANY only for demotion |
| Source, fixed rule target, ND output | Use its existing EXACT, ANY or must target |

For example, a read below the tracked prefix consumes part of the unknown
suffix. The fixed original cannot rebind that suffix:

```java
Object read(Object p) { return p.f; }
```

```text
Seed:         p.*/T -> p.*/T, D
Read witness: input p.f.s/T -> return.s/T
Result:       p.*/T -> return.[any]/T, D
Invalid:      p.*/T -> return.*/T   // This would return f.s, not s.
```

A known concrete output path can grow without loss:

```java
Box wrap(Object p) { Box b = new Box(); b.value = p; return b; }
```

```text
Before: p.*/T -> p.[any]/T -> b.value.[any]/T -> return.value.[any]/T, D
After:  p.*/T -> p.*/T     -> b.value.*/T     -> return.value.*/T, D
FLOW:   p.*/F -> return.value.*/F, N or D
```

The new marked result has the same suffix as the FLOW result. Field-limit
overflow can still change both results to ANY. This example does not claim
that an arbitrary setter or library method has a precise copy summary.

### 4.1 Cleaners and rule actions

A selected FULL cleaner still requests T on FLOW, excludes it from FLOW and
uses the current spatial rows on concrete T. A surviving selected-T result
keeps the existing non-subsumable flag. RemoveAllMarks can kill.

Handle concrete STAR explicitly in the spatial cleaner. In particular:

```text
Input:  I -> x.*/T
Action: remove T strictly below x
Output: I -> x.$/T, D, non-subsumable
```

The root can survive. Do not retain the entire STAR row for this case merely
because the current `tail.isAny` helper excludes STAR. EXACT is an independent
root result. For other partial cleans use the current E-free residual policy.
Do not add a strong field validation step or change GROUP cleaners.

A CM check uses the current overlap/mark test. A concrete STAR observation
is not a must-taint observation. It stays DEMAND. Do not treat a hypothetical
STAR initial as a source or as proof that all of its fields carry T.

An assignment to a fixed position uses its current target. It does not inherit
the triggering row's suffix. The same rule applies to a same-T assignment,
a cross-mark assignment, sink end facts and an all-origin ND result.
All-ZERO cube tests and ZERO generation keep their current behavior.

### 4.2 Statics and suffix ownership

ZERO satisfies a static premise only during run-1. It activates the current
static reader procedure. It does not supply a suffix itself.

The current code retains a static original: the FLOW path resumes under the
published static initial; the concrete path selects a canonical static
initial in `applyStaticInput`/`concreteInitial`. Keep this contract:

```text
I(S.C.f.*/T) -> local.*/T, D    // Legal if the read preserves that suffix.
I(S.C.f.*/T) -> return.*/T, D   // Legal through the same conditional copy.
ZERO         -> return.*/T     // Not authorized by a static pool reply.
```

Pool supplies from different writers have independent suffixes. Keep the
current region/mark union. Do not equate a writer suffix with a reader suffix.
A raw pool reply or a join which no longer retains the selected original uses
the existing ANY/EXACT representation. If an adapter actually removes the
binder, it must emit an independent ANY/D result. It must not emit STAR under
ZERO or another original. This is a boundary condition, not a new static route.

No new `S -> S` summaries are stored or sent to callers. Static-to-static
summary erasure and implicit later-run guidance remain in force.

## 5. FLOW replacement

Changing the seed does not make the current ANY-only matcher accept STAR.
Add a separate STAR cell at the existing summary admission points.
Do not remove a concrete seed or skip its local checks because FLOW exists.
Actual T processing is still needed for CM, sources, cleaners and sinks.

```kotlin
fun coversStar(e: MarkedLeaf, f: FlowLeaf): Boolean =
    sameSummaryScopeAndInitialGeometry(e, f) &&
    e.initial.tail == STAR && e.inputMark == e.outputMark &&
    e.tail == STAR && f.tail == STAR &&
    e.finalBase == f.finalBase && e.finalPath == f.finalPath &&
    e.fieldExclusion.isEmpty() && f.fieldExclusion.isEmpty() &&
    e.outputMark !in f.markExclusion &&
    !e.nonSubsumable &&
    (f.layer == NORMAL || e.layer == DEMAND) &&
    sameAliasEffectClass(e, f)
```

The FLOW tree must have an **output leaf at that exact path**. A trie node
without an output leaf is not enough. Test each output path and mark. Keep
method, endpoint, exit kind, call stage and the existing scope guards.

For STAR, a proper path prefix is insufficient:

```text
FLOW:  p.*   -> return.f.*
TAINT: p.*/T -> return.f.g.*/T
Input suffix []: FLOW ends at return.f; TAINT ends at return.f.g.
Result: not covered.
```

Keep the existing prefix test for ANY/ANY. Do not add cross-tail coverage,
EXACT/must coverage, cross-mark coverage or protected-result coverage here.
Do not turn an existing ANY row into STAR because a matching FLOW row arrives.

Use the current non-subsumable rules: assignment checks the triggering
conclusion mark; local and call cycles are protected; protection from a
summary is sticky; identical plain/protected rows merge into the protected row.
For same-path STAR identities, the current FLOW and TAINT alias-effect tests
agree. No global change to `hasNoMemoryEffect` is required.

The retained FLOW row replaces a covered, unprotected STAR marked summary
and its redundant T demand. Keep the current concrete processing and producer
hooks before summary normalization. Do not remove a static supply, a sink
occurrence or a rule-generated demand as a side effect of summary compression.

## 6. Handoff to run-2

Keep the current handoff operation. Read a retained forward STAR conclusion
as an ANY backward entry pattern. Keep its full mark T:

```text
Forward marked demand: I(x.*/T) -> y.q.*/T, D
Backward guide:         entry y.q.[any]/T; exit x.*/T
```

This conversion applies to **patterns**, not to the run-1 stored conclusion.
A pattern has no bound input/output suffix. Its location set is unchanged.
No concrete STAR executable conclusion is added to run-2 or later runs.
Concrete STAR D rows do not become normal records.

If the marked row is replaced, the corresponding FLOW record or FLOW demand
remains. The original AP emitter can start its FLOW query on an actual marked
input. The same-mark, unprotected transport has the same instantiated result.
Original whole-premise restriction still applies. The existing assignment,
cleaner and cycle protection keeps the separate marked guides at dependency
barriers. No actual-input-only query or StrongQueries permission is added.

The proof claim is retention of concrete witnesses and ordinary demand
coverage. It is not equality of the old coarse candidates. The new seed is
strictly smaller than the old seed. Run-2 may therefore see fewer false candidates.

## 7. Inventory of ANY construction

This inventory covers production code for the bidirectional analyzer at the
pinned core tree. Legacy analyzers, tests and historical reference fixtures are
outside this source inventory. In the paths below, `B` means
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`;
`J` means the adjacent `opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi`.
An ANY literal can construct a fact, an edge target, a read view or a pattern.
These are separate cases.

### 7.1 Operations which create an executable ANY result

| Source and operation | Why ANY exists now | Rule after this proposal |
| --- | --- | --- |
| `B/ap/Demand.kt: initialFacts`; `B/ap/Reference.kt: startFact` | Concrete STAR seed is projected to ANY | New FULL run-1 seed retains STAR; other run/mode cells stay as now |
| `B/ap/Reference.kt: normalize`; `B/ap/ApManager.kt: factsOf` | W2 erases concrete STAR; the typed factory calls this normalizer | Retain only legal correlated FULL run-1 results. General W2 remains outside this extension |
| `B/ap/EdgeApplication.kt: flow`, ancestor hit; `Reference.kt: above` | A read/binding/summary premise consumes an unknown suffix prefix | ANY/D unless target is EXACT; unchanged |
| `B/ap/EdgeApplication.kt: taint`, ancestor hit | Same loss for concrete may or new STAR input | Keep ANY/D for STAR/may; current must-specific result stays separate |
| `B/ap/EdgeApplication.kt: taint`, at a STAR target | A non-must concrete leaf is always emitted as ANY today | Keep STAR for legal same-suffix input; retain ANY for ANY input |
| `B/ap/EdgeApplication.kt: flow/taint`, explicit ANY target; `Reference.kt: below/above` | An explicitly independent target drops correlation | ANY/D; unchanged. An existing ANY value also stays ANY through a copy |
| `B/ap/Limit.kt: limitFacts/FieldLimitCut`; `Reference.kt: limit` | A concrete path exceeds the field budget; folded leaves use `LeafAlgebra.asAny` | Cut branch becomes ANY/D with Empty E. The kept branch retains its own tail |
| `J/interp/JIRRuleForms.kt: RulePos.star`, `CopyAllMarks`; `RulePos.fact`, `CopyMark` | A final AnyField pass target is may, not must | Keep the explicit ANY target. Do not reinterpret it as STAR |
| `B/engine/RunMethodLocalServices.kt: seedFact`; `B/ap/ApOps.kt: targetTree` | A backward sink seed with an AnyField requirement becomes an executable concrete ANY value | Keep ANY/D. The original sink pattern and the SEED field cut still apply |
| `B/ap/Reference.kt: reverse` and micro-edge reversal | Reversing a may/fixed edge can require an independent suffix | Keep the existing reversal table and demand bit; no new run-1 producer policy |

The ancestor-hit and explicit-target rows include local edges, call bindings,
alias micro-edges and applied method summaries. These use one AP transfer
kernel. They are not separate permission to widen all call results.

Source/GEN AnyField targets use `RulePos.sourceFact`, hence **ANY_TAINT**.
They are not direct ANY producers. Later transfer or a field cut can produce
ANY from them. Moving a must result to DEMAND alone must not do so.

### 7.2 Representation paths and static materialization

| Source | Current behavior | Required handling |
| --- | --- | --- |
| `B/ap/ApOut.kt: Results.flow/taint`; `Conclusions.kt`; `ApManager.kt` | Omitted tail arguments infer ANY from DEMAND; TAINT normal defaults to must | Pass STAR explicitly on the selected new paths. Layer is not a reason to erase a tail |
| `B/ap/Summary.kt: leafKinds` | A summary leaf becomes an edge with the stored ANY header | Compile the actual STAR/ANY/must header; do not erase STAR |
| `B/store/DiagonalRelations.kt: decode`; `B/engine/NeutralRelationBatch.kt: emit` | Current diagonal packets decode with an explicit ANY tail | Keep packets typed by tail, or use the scalar STAR fallback. An ANY packet cannot decode to STAR, or vice versa |
| `B/engine/Run1StaticService.kt: facts` | `factsOf` converts a canonical field STAR/full-mark reply to ANY | Keep raw membership independent. At an existing selected concrete STAR original, use the new start contract; keep raw ANY where no such binder exists |
| `B/engine/RunMethodAnalyzer.kt: knownStaticInput` | Rebuilds the canonical input through `factsOf`, which erases concrete STAR | Use the new scoped seed under that known static original |
| `B/engine/Run1PointResume.kt: direct/packed answers`; `RunMethodCallServices.kt: applyStaticInput/applyStaticSummary` | Rebuilds scalar facts and applies a saved FLOW/summary image | Select the existing static original, then preserve only a same-suffix result. An ANY saved image stays ANY |

Generic reconstruction sites such as scalar summary extraction, return cleanup,
protection replay and diagnostic decode must preserve the supplied tail. They
do not have independent widening permission. `withLayer` must preserve it too.
Raw APIs without a valid selected owner continue to use the general normalizer.

### 7.3 ANY patterns, demands and transient read views

| Source | Object built | Meaning |
| --- | --- | --- |
| `B/driver/HandOff.kt: toBackward`, `located` | Backward entry/demand pattern | STAR -> ANY; must -> ANY; keep concrete marks |
| `B/store/DemandStore.kt: implicitStaticPair` | Universal static field/group query pattern | Existing static completion; not a propagated run-1 fact |
| `B/engine/StrongQueries.kt` | Later-run query/completion pattern | Current STAR/must -> ANY query conversion; unchanged and not used to justify this feature |
| `B/engine/RunMethodCallServices.kt: cleanChain` | Field-cleaner feedback pattern | BELOW/descendant reach uses ANY; exact reach uses EXACT |
| `B/engine/Run1StaticService.kt: intersect` | Region selector | Same-depth intersection uses ANY if a selector is ANY; it has no shared suffix |
| `J/interp/JIRRuleForms.kt: RulePos.fact`, condition literals | CM AnyField pattern | Match a descendant; this does not assign ANY to an initial |
| `B/ap/Reference.kt: mustRecordReadView` | Transient must-summary read view | Replaces must with ANY for a demand view; native stored record stays unchanged |
| `B/ap/Reference.kt: field-cleaner feedback helper` | Feedback pattern | A must observation uses concrete ANY; no executable STAR erasure |
| `B/ap/Reference.kt: emit` and `B/ap/Demand.kt: emitInitials` | Restricted-run initial selected by a demand meet | A concrete ANY demand may select an ANY initial later; run-1 grammar still rejects it |

The `Tail.ANY` tests in `Groups.kt`, `Facts.kt`, `Primitives.kt`,
`RuleStatement.kt`, `Summary.kt` selectors and `FlowBackedCoverage.kt` are
consumers/validators, not new semantic producers. Audit their handling of the
new legal STAR type. An arbitrary blanket replacement of `isAny` is unsafe.

## 8. Representation and implementation obligations

The following pseudocode describes the boundary. It is not a new generic
normalization policy:

```kotlin
fun finishCorrelatedCopy(owner: InitialAp, value: RawResult, mode: ApMode): Facts {
    if (mode.isRun1Full && value.keepsOriginalSuffix &&
        owner.tail == STAR && owner.mark == value.mark && !owner.isZero) {
        return encodeWithExplicitTail(value, STAR, DEMAND, Empty)
    }
    return currentNormalizeAndEncode(value)
}
```

`keepsOriginalSuffix` is a result of the selected transfer branch, not a
stored per-edge Boolean or a support object. An actual above/cut/may branch
has already lost correlation and cannot enter this branch. Other existing
STAR FLOW results retain the current field-write contract.

The typed TAINT nonexact header must distinguish STAR, ANY and ANY_TAINT.
One trie payload channel can serve a nonexact mark set if its header retains
that distinction. Include the header in grouping, equality and hashing. Keep
EXACT siblings and non-subsumable masks exact. A STAR branch cannot inherit
an ANY sibling's header when roots merge. The protection Boolean remains
metadata with explicit OR admission; do not put it into semantic edge equality.

Same-premise TAINT admission needs an explicit STAR case. Deduplicate equal
STAR paths/marks and OR their flags. Do not apply a must-leaf descendant rule
to a STAR leaf because both use the current `any` payload channel. Existing
ANY coverage can cover a STAR pair only under that same original and the
existing protection gate; it must not reclassify the retained ANY as STAR.
This is distinct from the new cross-premise FLOW replacement cell.

Audit constructors, canonicalization, groups, selection, restriction, mark
checks, scalar leaves, summary compilation, call adapters, flags and packet
decode. Adding STAR only to `initialFacts` will fail validation or erase it on
the next operation. A typed STAR fallback is acceptable before packet support.

## 9. Proof and validation gates

The [Lean module](lean/ApSpec/Run1CorrelatedConcreteInitials.lean) checks the
unchanged AP denotation, new seed identity, strict precision gain, copy
composition, descent/cut covers, equal-path STAR specialization, exact
application equality, the prefix counterexample and the original emitter.
The [dossier](run1-correlated-concrete-initials-proofs.md) states the limits.

Before implementation is accepted, run differential tests for:

1. FULL and GROUP start tables, ZERO, exact class marks, scalar/packed decode.
2. Copies, reads above/below a prefix, aliases, limits and mixed STAR/ANY/EXACT
   branches. Test suffixes `[]`, `[f]`, `[g]` and `[f,g]`, with field limit 1.
3. Full kill, disjoint and exclusion-needing field writes; all partial cleaner
   reaches; selected-mark survival and flag union.
4. Sources, cross-mark/same-mark rules, cycles, zero and nonzero ND origins.
   Do not inherit a source suffix from its trigger.
5. Static late write/read activation, canonical direct/packed replies, retained
   static anchors, ZERO activation, computed supplies and erased S-S rows.
6. STAR exact-path and ANY prefix summary replacement, excluded/protected
   negatives, alias-effect tests, repeated deltas, FLOW arriving first or last.
7. Original handoff, emission and restriction on marked witnesses, including
   protected dependencies and static fallback. Do not use StrongQueries in
   the test oracle.

Compare concrete witness retention and observations. Do not require equality
of deliberately removed coarse pairs. No whole-engine refinement or performance
result follows from the local Lean proofs alone.

Measure the completed run-1 census before and after: STAR/ANY/EXACT/must marked
memberships, covered plain rows, flag-blocked rows, emitted requests, summary
publications, engine time and retained bytes. Include the latest reached
iteration, such as run-2 OOM, in each report. Keep the same project commands.

The expected saving is fewer same-mark summary rows, publications and backward
T demands where the **seed was the only cause of ANY**. Above-prefix reads,
cuts, source targets and protected results remain. STAR can also split a
previously shared ANY header. The net memory/time gain must be measured; the
existing uncovered counts do not predict it.
