# ThingsBoard BaseOnly engine issues (2026-08-05)

## Scope and reference run

The measurements use the ThingsBoard model at
`opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml` and the normal shallow
BaseOnly/full Tree pipeline. The retained side-effect requirement index run produced 17 shallow
discoveries and 12 SARIF results, matching the comparison run.

The largest shallow-phase increments in that run were:

| Method | New steps | New handled summaries | Unprocessed at last shallow snapshot |
|---|---:|---:|---:|
| `EntityActionService#pushEntityActionToRuleEngine` | 112,999 | 21,778 | 0 |
| `AuditLogServiceImpl#constructActionData` | 49,744 | 11,842 | 0 |
| `TbMsgProto.Builder#buildPartial0` | 41,850 | 0 | 0 |
| `DaoUtil#convertDataList` | 25,287 | 2,708 | 26,512 |
| `EntityActionService#processNotificationRules` | 17,463 | 9,519 | 0 |
| `ActorSystemContext#persistDebugAsync` | 17,028 | 5,046 | 146 |
| `BaseSqlEntity#equals` | 3,404 | 11,540 | 0 |

This shows three different costs: repeated side-effect lookup, unconstrained polymorphic calls, and
pure intraprocedural field/branch propagation. They must not be treated as one problem.

## 1. Repeated side-effect requirement application

### Evidence

Before memoization, the first 10,000 calls to `NormalMethodAnalyzer#addSideEffectRequirement`
contained 8,739 and 8,549 duplicate `(current initial, requirement)` pairs in two sampled streams.
At 20,000 calls, 17,418 were duplicates, while the repeated work produced only two or three new
initial edges.

The storage lookup also linearly scanned every requirement under the same access-path base in
`BaseOnlySideEffectRequirementApStorage.RequirementStorage#filterTo`.

### Retained mitigation

- `NormalMethodAnalyzer#addSideEffectRequirement` memoizes exact BaseOnly
  `(current initial, requirement)` pairs for one analysis lifecycle.
- `BaseOnlySideEffectRequirementApStorage.RequirementStorage#filterTo` uses
  `BaseOnlyInitialAccessIndex` for conservative candidate lookup and retains
  `baseOnlySummaryInitialMatches` as the authoritative predicate.

The indexed run reduced prescan from 116.6s to 98.7s and shallow analysis from 57.8s to 47.8s in
the controlled pair. Full Tree time stayed effectively unchanged (33.1s versus 32.6s), and both
runs produced 17 shallow discoveries and 12 SARIF results.

## 2. Generic collection element type is lost

### Source pattern

`DaoUtil.java:100`:

```java
public static <T> List<T> convertDataList(Collection<? extends ToData<T>> toConvert) {
    for (ToData<T> object : toConvert) {
        converted.add(object.toData());
    }
}
```

### Evidence

At the IR statement `%13 = object.toData()`, `JIRCallResolver#resolveVirtualMethod` receives only
the non-exact constraint `ToData`. It resolves 78 concrete `toData()` targets. The method reached
25,287 steps and still had 26,512 unprocessed edges at the last shallow snapshot.

Call-site diagnostics show values such as `List<E>` and `ArrayList<E>`. The concrete type is often
available only through the generic return type of the reaching definition or through substitution
of the caller class's type variables.

### Incorrect operation

`JIRCallResolver#resolveValueTypeConstraints` discards `AliasApInfo` whenever it has non-empty
accessors. Consequently, an alias such as `arg(0).[element]` cannot consult the method context.
The current `MethodContext` model can constrain only a base (`this` or an argument), not an
accessor-scoped value such as a collection element.

### Required mitigation

1. Add accessor-scoped type constraints to method contexts.
2. Recover generic return types from reaching definitions and substitute class/method type
   variables using the caller context.
3. Let `resolveValueTypeConstraints` query a constraint for `AliasApInfo(base, accessors)` instead
   of dropping every non-empty accessor path.

This should turn the loop receiver into one (or a small set of) concrete entity types. A broad
polymorphic proxy does not solve the lost premise and previously increased summary aggregation.

## 3. Class-static wildcard facts are propagated into every context and call

### Evidence

`BaseController#checkEntityId` has 779 distinct `MethodEntryPoint` contexts: 36 receiver types,
29 argument-0 types, and 48 exact lambda classes (751 receiver/lambda pairs). The contexts are not
duplicates caused by conjunction ordering.

Across a diagnostic shallow run, those contexts produced 13,280 recorded statement entries.
10,583 entries were static-only. The exact initial fact `<static>.*/{}` alone was recorded 3,620
times. Typical repeated statements include:

```text
user = this.getCurrentUser()
%4 = user.getTenantId()
%5 = findingFunction.apply(%4, entityId)
%13 = this.checkEntity(user, entity, operation)
```

### Operation chain

1. `BaseOnlyInitialFactAbstraction#abstractOneBranch` abstracts a concrete class-static path at its
   first unexcluded `ClassStaticAccessor`, producing `<static>.*/{}`.
2. `JIRMethodCallFactMapper#factIsRelevantToMethodCall` returns `true` for every
   `AccessPathBase.ClassStatic`, independent of the called method.
3. `JIRMethodCallFactMapper#mapMethodCallToStartFlowFact` maps the class-static fact into every
   resolved callee.
4. Context-specific analyzers repeat that propagation, even when their relevant call-target sets
   are identical.

### Rejected mitigation: merge static inputs into the empty context

A prototype redirected BaseOnly class-static inputs and subscriptions to the existing
empty-context analyzer. It kept 17 shallow discoveries and reached 17.3s before cancellation, but
concentrated all exclusion/final variants into one fact set, hit the 7.8GB low-memory stop, and
produced only two final findings. Contexts currently partition state as well as duplicate work.

### Required mitigation

Filter class-static propagation before callee insertion. A safe design needs a transitive static
access footprint per method/context-equivalence class:

- a concrete static fact is sent only when its class accessor is in the footprint;
- a wildcard static fact is intersected with the footprint (or skipped when all footprint entries
  are excluded);
- footprint growth must notify existing subscriptions to preserve eventual consistency.

Merging contextual fact sets after insertion is not a viable substitute.

## 4. Method contexts encode caller types, not behavior equivalence

### Evidence

Each `checkEntityId` context usually contains only one or two facts at a statement; the 75,067
cumulative steps are caused by many analyzers rather than one oversized per-statement fact set.
About 80% of diagnostic statement entries were static-only, but receiver and lambda contexts still
select call targets.

A prototype that dropped a receiver constraint when direct `this` calls appeared to have the same
targets reduced this method from roughly 80,000 to 2,400 steps. It worsened total work because
mapping the method to `EmptyMethodContext` also weakened entry fact filtering and moved the
explosion into callees.

### Required mitigation

Introduce a method-specific behavior signature, not blanket context erasure. Contexts may share an
analyzer only when they induce the same:

1. virtual/lambda call-target sets for context-derived receivers; and
2. method-entry fact type filtering.

If multiple types form one equivalence class, the shared context must represent their union for
fact filtering. Selecting one representative type or using `EmptyMethodContext` is not equivalent.

## 5. `Object` parameters are deliberately uncontextualized, but demand-driven refinement is missing

### Evidence

Lombok-generated `BaseSqlEntity#equals(Object)` applies 11,540 summaries for 3,404 shallow steps
(17,310 summaries for 5,106 cumulative steps). Its body narrows the argument and calls methods such
as `other.canEqual(this)` and entity getters.

`JIRCallResolver.MethodContextCreator#attachContext` skips every parameter declared as
`java.lang.Object`, even when a narrowed alias becomes a virtual receiver. This keeps the receiver
broad across the entity hierarchy.

### Rejected mitigation: context every `Object` argument

Removing the global skip created tens of thousands of additional contexts/soft references and hit
the 7.8GB shallow low-memory stop. Global Object-argument sensitivity is worse than the original
problem.

### Required mitigation

Add a constraint only when a method-local cast/type test produces an alias that is later used as a
virtual receiver. The constraint belongs to that narrowed alias/access path; it should not make all
`Object` parameters context-sensitive.

## 6. Generated builder methods are a pure intraprocedural field problem

`TbMsgProto.Builder#buildPartial0(TbMsgProto)` is a generated sequence of about twenty guarded
field copies. It adds 41,850 shallow steps and handles zero summaries. Summary-storage indexing or
summary field generalization therefore cannot reduce its internal work.

Possible mitigations are deliberately separate from the preceding issues:

- a generated-code summary for protobuf builder copies; or
- fact-set field generalization, if its semantics are designed and accepted independently.

Enabling summary-storage field generalization alone cannot affect this hotspot.

## 7. Exit compatibility postprocessing discards a rewritten result

### Incorrect operation

`NormalMethodAnalyzer#handleUnchangedStatementEdge` obtains `processedEdges` from
`JIRMethodSummaryEdgeProcessor`, but propagates the original `edge` from inside the loop:

```kotlin
processedEdges.forEach { processedEdge ->
    val edgeUnchanged = processedEdge === edge
    propagateEdge(edge, edgeUnchanged)
}
```

The JVM postprocessor filters an F2F final fact against the initial fact's type compatibility at a
method exit. For an unchanged path edge, a non-null filtered replacement is therefore ignored and
the unfiltered edge becomes the method summary. Changed statement flow uses `processedEdge`
correctly, so a postprocessor which rewrites an edge has statement-history-dependent behavior.

### BaseOnly impact

This is a general correctness defect, but it is not a confirmed ThingsBoard BaseOnly performance
cause. `BaseOnlyFinalFactAp#filterFact(FactCompatibilityFilter)` currently returns either the same
fact or `null`; it does not produce a rewritten fact. A rejected fact produces an empty
`processedEdges` list in both versions, while an accepted fact is semantically unchanged. Tree can
return a pruned replacement, so the wrong variable is observable there.

An earlier short diagnostic appeared to show a large BaseOnly speedup and finding loss. That run
used a shorter effective phase budget and a different rule set, and is not a valid comparison. A
300-second diagnostic confirmed many BaseOnly exit-filter rejections, but did not establish that
changing this variable changes BaseOnly behavior.

### Required mitigation

1. Add a postprocessor contract test where an accepted edge is rewritten.
2. Change `handleUnchangedStatementEdge` to propagate `processedEdge`.
3. Independently add Tree-versus-BaseOnly compatibility-filter differential tests; the observed
   BaseOnly rejections are substantial and deserve validation, but are not evidence of this bug.

The one-line propagation fix was used only as a diagnostic and was reverted.

## 8. Normal and exceptional CFG successors are collapsed

### Source pattern

`EntityActionService#pushEntityActionToRuleEngine` contains almost its entire body in one
`try/catch (Exception)`. The body has many assignments and calls, including:

```java
String strCustomerId = extractParameter(String.class, 1, additionalInfo);
...
} catch (Exception e) {
    log.warn(...);
}
```

### Evidence

At the final diagnostic snapshot, the catch statement alone retained 1,543 entries and 1,998
finals, and rejected 37,713 duplicate additions. `ActorSystemContext#persistDebugAsync` showed the
same shape: its catch retained 1,620 entries and 2,624 finals and rejected 16,812 duplicate adds.
Observed catch facts include values assigned by calls inside the protected region, for example an
`extractParameter` result:

```text
arg(6)[*].*/E -> var(183)[*].*/E
    at catch (e: java.lang.Exception)
```

If `extractParameter` transfers control to the catch, `var(183)` was never assigned. This is not a
valid exceptional-path state.

### Incorrect operation

1. `JApplicationGraphImpl.JMethodGraphImpl#successors` concatenates normal `successors` and
   exceptional `catchers` into one sequence.
2. `MethodInstGraph#build` stores the union in one unlabeled compact graph.
3. `NormalMethodAnalyzer#propagateEdgeToSuccessors` sends the post-statement edge to every member
   of that union.

Thus a statement's normal-completion result is propagated to its exception handler. The graph no
longer contains enough information for the analyzer to choose different normal and exceptional
transfer functions. Besides the performance cost, this can create false-positive flows through a
return value or write that did not complete.

### Required mitigation

- Preserve normal-versus-exceptional edge kind in `MethodInstGraph`.
- Send ordinary post-statement facts only to normal successors.
- Define an exceptional transfer from the statement's input state to catchers. Until exceptional
  callee summaries exist, this transfer must not invent a return value or normal call effect.
- Apply the same distinction in forward/backward trace traversal and reaching definitions.

## 9. BaseOnly facts carry large object-level exclusion payloads

BaseOnly compresses the access path into interned integer slots, but still stores exclusions as the
common `ExclusionSet.Concrete(PersistentSet<Accessor>)`. On the full ThingsBoard rule set, a single
rendered fact contained 237 exclusion entries, including 152 distinct synthetic
`unsafe-deserialization` taint marks observed across the run.

This is not a semantic error by itself: the marks are distinct, and repeated rendered field names
can be distinct declaration-qualified `FieldAccessor` objects. It is nevertheless a representation
mismatch. Every otherwise compact BaseOnly fact retains an object-level persistent set, and union,
containment, equality, and serialization operate on full `Accessor` objects. The cost becomes most
visible in the hot methods whose facts combine many independently generated rule marks.

### Required mitigation

Design a BaseOnly-internal exclusion representation over `AccessorIdx`, with canonical sharing.
Keep conversion to `ExclusionSet` at API/serialization boundaries. Preserve declaration-qualified
field identity and keep structural and taint-mark exclusions semantically distinct; merely dropping
large mark sets would be unsound.

This should be measured as allocation/CPU work, not expected to reduce analyzer step count.

## 10. Value-insensitive contexts leave large enum switches unpruned

`AuditLogServiceImpl#constructActionData` contains 35 `ActionType` case labels and reached 208,609
steps with 59,076 handled-summary batches in the diagnostic run. Its callers pass an `ActionType`
through several layers, and some roots use concrete constants. `MethodContext` records receiver and
argument *type* constraints only; no enum/constant value reaches the callee CFG. Consequently the
analyzer traverses every switch arm even when an upstream value is known.

This is a confirmed missing precision feature and a plausible contributor, but not yet a validated
mitigation: many calls also pass a genuinely unknown `actionType`, so an enum-value context must be
demand-driven and bounded. The experiment should first count call sites with a singleton reaching
enum constant, then compare the reachable CFG and summaries for those contexts. Do not introduce
unbounded general constant-sensitive contexts.

## 11. Hot-path allocation cleanups are not the main issue

`JIRAnalysisManager#getEdgePostProcessor` creates an exit-summary processor for every statement
edge even though it immediately returns the input at non-exit statements. An isolated prototype
returned `null` before allocation at non-exits. On the same built-in-rule workload, prescan was
90.132s before and 90.188s after; shallow was 20.160s before and 20.844s after; both produced two
SARIF results. This is harmless cleanup, not a measurable ThingsBoard mitigation.

New summary events group F2F summaries before dispatch, and the analyzer groups again after
`prepareFactToFactSummary`. The second grouping cannot be removed generally because the JVM rule
rewriter may refine an initial fact. Fact-side-effect events do have an avoidable repeated grouping,
but it should be treated as a micro-optimization rather than a root-cause fix.

## 12. Full call-target caching is not a valid mitigation

Caching `JIRCallResolver` results removed substantial CPU per propagation in one run, but retaining
all target lists caused a low-memory stop. Reusing forward target lists during trace/rule resolution
also reduced final findings (12 to 2/3 in the rejected variants). Caching only forward resolution
restored all 12 findings but still hit low memory and did not reduce propagation steps.

The useful conclusion is that target construction is repeatedly expensive, but full result-list
memoization hides rather than removes the redundant propagation. Keep the existing compact
override cache; fix generic constraints and callee relevance instead.

## Mitigation order

1. Keep the exact side-effect application memo and indexed requirement lookup.
2. Add generic/accessor-scoped type contexts for collection elements.
3. Add pre-insertion class-static relevance filtering with eventual-consistency notifications.
4. Add behavior-equivalent context sharing only after type-filter equivalence is represented.
5. Add demand-driven refinement for narrowed `Object` aliases.
6. Fix the generic postprocessor propagation bug; validate BaseOnly compatibility separately.
7. Preserve exceptional CFG edge identity and use exceptional transfer semantics.
8. Prototype a BaseOnly-internal compact exclusion representation.
9. Measure bounded enum-value contexts on the 35-way `ActionType` switch.
10. Treat generated protobuf field-copy methods separately.
