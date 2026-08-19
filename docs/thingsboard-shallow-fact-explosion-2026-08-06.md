# ThingsBoard shallow fact explosion

Date: 2026-08-06

## Verdict

The current ThingsBoard shallow-scan cost is not caused primarily by field enumeration. It is a
product of three independent dimensions:

```text
method type contexts × initial-to-final fact alternatives × branch-heavy CFG statements
```

The dominant repeated facts are already suffix-abstract (`.*`). Consequently, lowering the F2F
summary field-generalization threshold cannot collapse them. Summary generalization also runs only
after a path edge reaches a method exit, after the intraprocedural cost has already been paid.

The first mitigation should be a transitive class-static access footprint. It allows global facts
to bypass callees that cannot observe or modify them, without merging contextual fact sets or
weakening virtual-call resolution.

## Concrete source pattern

Two generic service methods account for the largest repeated work:

- `EntityActionService#pushEntityActionToRuleEngine` accepts the interface/base values
  `EntityId`, `HasName`, and `User`, contains a long `if/else` chain, and calls methods on all three
  values.
- `AuditLogServiceImpl#constructActionData` is reached through generic
  `<E extends HasName, I extends EntityId>` callers and contains a large `switch (actionType)`.

Representative source:

```java
public void pushEntityActionToRuleEngine(EntityId entityId, HasName entity, ..., User user, ...) {
    ...
    metaData.putValue("userName", user.getName());
    ...
    entityNode = JacksonUtil.OBJECT_MAPPER.valueToTree(entity);
    metaData.putValue("entityName", entity.getName());
    metaData.putValue("entityType", entityId.getEntityType().toString());
    ...
}
```

```java
private <E extends HasName, I extends EntityId> JsonNode constructActionData(
        I entityId, E entity, ActionType actionType, Object... additionalInfo) {
    ObjectNode actionData = JacksonUtil.newObjectNode();
    switch (actionType) {
        case ADDED:
        case UPDATED:
            ...
        case ATTRIBUTES_UPDATED:
            ...
        // many more cases merge at one exit
    }
    return actionData;
}
```

`JIRCallResolver.MethodContextCreator#createContexts` materializes the Cartesian product of the
receiver/argument type alternatives. Across the observed run this produced:

| Method | distinct contexts |
|---|---:|
| `pushEntityActionToRuleEngine` | 108 |
| `constructActionData` | 62 |

The contexts include concrete pairs such as `(AssetId, Asset)`, `(DeviceId, Device)`,
`(RuleChainId, RuleChain)`, and variants with `SecurityUser`.

## Fact and statement evidence

A diagnostic classified every processed edge in the two methods.

### `pushEntityActionToRuleEngine`

```text
recorded steps:       224,330
F2F:                  187,286
Z2Z:                   37,044
all non-zero shapes:  abstract suffix
ClassStatic bases:    126,038
Argument bases:        21,301
Local bases:           20,406
This bases:            19,541
contexts:                 108
```

The hottest statements are joins and parameter-to-local assignments:

```text
3,745  goto index 294
3,566  goto index 334
3,498  %186 = entityNode
3,444  %183 = additionalInfo
3,438  %181 = actionType
3,437  %182 = user
```

### `constructActionData`

```text
recorded steps:       118,065
F2F:                  102,069
Z2Z:                   15,996
all non-zero shapes:  abstract suffix
ClassStatic bases:     59,516
Argument bases:        18,986
Local bases:           14,502
This bases:             9,065
contexts:                  62
```

The common switch join alone was processed 8,846 times:

```text
8,846  goto index 241
1,605  return actionData
1,435  goto index 64
```

The class-static facts include generated Semgrep automaton state, for example:

```text
<static><static>(java/security/xss.yaml:xss-in-spring-app;sink_135;_<S>_;pos).*/...
<static><static>(java/security/xss.yaml:xss-in-spring-app;sink_136;_<S>_;pos).*/...
```

## Exact operation chain

1. `TaintRuleGenerationCtx#stateVarPosition` represents a global automaton state as a
   `PositionBase.ClassStatic` value.
2. `BaseOnlyInitialFactAbstraction#abstractOneBranch` turns it into a compact suffix-abstract
   BaseOnly fact.
3. `JIRMethodCallFactMapper#factIsRelevantToMethodCall` returns `true` for every
   `AccessPathBase.ClassStatic`, without considering the callee.
4. `JIRMethodCallFactMapper#mapMethodCallToStartFlowFact` copies the fact unchanged into every
   resolved callee.
5. `JIRCallResolver.MethodContextCreator#createContexts` creates context-specific callees.
6. `MethodAnalyzerStorage#add` creates a separate analyzer for every full `MethodEntryPoint`.
7. `MethodEdgesInitialToFinalBaseOnlyApSet` preserves the initial-to-final correlation at every
   statement, so each context traverses the large switch/branch body for every surviving
   alternative.

There is no single incorrect BaseOnly access-path operation in this chain. The representation is
compact per fact, but the engine schedules the same global-state problem once per local type
context.

## Why field generalization does not address it

- Every sampled non-zero fact in the hot methods was already suffix-abstract.
- `BaseOnlyF2FFieldGeneralizer#eraseFieldForSummaryGeneralization` rejects accesses with a static
  slot.
- `MethodInitialToFinalBaseOnlyApSummariesStorage` sees an edge only at method exit. It cannot
  remove work inside the method being summarized.
- Raising/lowering the summary threshold can reduce downstream summary dispatch, but cannot
  remove the `contexts × facts × statements` product in these methods.

## Rejected experiments

| Experiment | Result | Reason |
|---|---|---|
| Route all shallow facts through `EmptyMethodContext` | Did not finish in the normal window | Losing receiver constraints greatly widens virtual dispatch |
| Route only `ClassStatic` facts through `EmptyMethodContext` | About 3.20M steps, effectively unchanged | Hot methods shrink, but unconstrained dispatch moves the work into callees |
| Join exact contexts into disjunctive type sets only for `ClassStatic` | 3.66M steps; shallow 100.4s | Alternatives cross-pollinate and create more summaries/facts |
| Persist exact unchanged-edge deduplication | No step reduction; substantially more retained memory | Exact duplicate replay is not the dominant term; alternatives differ by facts/exclusions |
| Store unchanged BaseOnly edges in the normal fact set | 3.64M steps; shallow 111.2s | Fact-state merging/republication costs exceed duplicate savings |

The experiments were diagnostics only and were reverted.

## Mitigation design

### 1. Build a transitive class-static footprint

For each analyzable method, collect the class-static accessors that the method may observe or
modify:

- explicit static field reads/writes;
- taint-rule conditions and actions using a `ClassStatic` position at method entry/exit or a call
  statement;
- the footprints of every possible callee, including all conservative virtual/lambda targets.

Compute the union to a fixed point over the conservative call graph. Recursive SCCs share one
fixed-point value.

### 2. Filter after concrete call resolution

The current `factIsRelevantToMethodCall` check happens before a concrete callee is known. Keep the
ordinary local/argument relevance test there, but check a `ClassStatic` fact against the resolved
callee footprint in `JIRMethodCallResolver` before creating/subscribing to its analyzer.

- A concrete static accessor is propagated only if it belongs to the footprint.
- A wildcard static fact is propagated only if the footprint contains an accessor not removed by
  its exclusions.
- If the fact is irrelevant, apply the identity call-to-return effect; do not drop it.

This preserves the caller fact while avoiding the callee CFG and its method contexts.

### 3. Preserve eventual consistency

The footprint may grow when a lambda or a newly resolved virtual target appears. A growth event
must revisit existing class-static call subscriptions. Publication is monotone: accessors are only
added, never removed.

### 4. Keep context precision

Do not replace the callee context with `EmptyMethodContext`, and do not union independent type
alternatives in one fact set. The footprint filter removes irrelevant global work before analyzer
creation while leaving ordinary type filtering and dispatch unchanged.

### 5. Test obligations

1. A class-static state changed directly in a callee must be propagated.
2. A state changed only in a transitive callee must be propagated.
3. An irrelevant callee must return the state unchanged without creating its analyzer for that
   state.
4. A late lambda/virtual target must grow the footprint and activate an existing subscription.
5. Tree/BaseOnly differential dataflow tests must show no lost reachability.
6. ThingsBoard must retain the same shallow discoveries and final sink hashes while reducing the
   two hot methods' `ClassStatic` steps.

## Secondary direction

Generated branch-heavy methods with no summary callbacks (for example protobuf
`buildPartial0`) are a separate intraprocedural problem. A summary-storage generalizer cannot
reduce their own CFG work. Address them later with generated-code summaries or a separately
specified fact-set widening policy; neither should be mixed into the class-static footprint fix.
