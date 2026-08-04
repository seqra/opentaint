# BaseOnlyField fuzz regression root-cause report

## Post-fix reevaluation

After the BaseOnly fixes, the complete corpus was rerun on 2026-07-16:

- all 38 setter cases pass in both Tree and BaseOnlyField;
- all 41 mixed cases pass in both Tree and BaseOnlyField;
- the 39 getter cases are not forward regressions.

The getter corpus originally used `Integer` payload fields. BaseOnly intentionally drops facts on primitives and boxed primitives, so those zero-vulnerability results were expected. Replacing `Integer` with the reference payload `String` made BaseOnly create every pre-trace vulnerability: 38 cases reported one vulnerability and `twoGetterCandidates` reported two. Trace resolution then filtered all 40 BaseOnly vulnerabilities. The same behavior was reproduced by the standalone `ReceiverGetterRegressionSample`.

There are therefore no remaining forward-analysis failures in this fuzz corpus. All three fuzz suites and their dedicated samples were removed. The standalone getter representative was also removed from `JavaDataFlowReachabilityTest` because it tests a trace-resolution failure, not reachability.

## Scope and result

The corpus contains 118 independently executed differential tests:

- 38 `BaseOnlySetterFuzzTest` cases;
- 39 `BaseOnlyGetterFuzzTest` cases;
- 41 `BaseOnlyMixedFuzzTest` cases.

For every original case, Tree reached the sink and BaseOnlyField did not. A combined run confirmed 118/118 failed BaseOnly assertions. Later pre-trace inspection revised the classification: 79 were genuine forward failures, while the 39 getter cases used intentionally unsupported boxed-primitive payloads.

The confirmed forward failures reduce to one BaseOnly operation defect:

| defect | affected cases | incorrect BaseOnly operation |
|---|---:|---|
| BO-1 | 79 (38 setter + 41 mixed) | `BaseOnlyAccessOps.appendFinal` rejects a field delta when the destination is a whole-value wildcard solely because their abstraction slots differ. |

## BO-1: `appendFinal` rejects a valid wildcard refinement

### Exact evidence

The first setter case produced this operation trace (accessor indices are interned; `-1` is absent and `-2` is abstract):

```text
prefix = var(1).*/{.label}                  packed=(-1,-1,-2), apSlot=2
delta  = .payload![setter-fuzz-taint].$    packed=(-1, 0, 2), firstSlot=1
BaseOnlyAccessOps.appendFinal(prefix, delta, fieldSensitive=true) = null
```

The corresponding mixed trace is:

```text
prefix = var(1).*/{.tag}                   packed=(-1,-1,-2), apSlot=2
delta  = .value![mixed-fuzz-source].$      packed=(-1, 0, 2), firstSlot=1
BaseOnlyAccessOps.appendFinal(prefix, delta, fieldSensitive=true) = null
```

The rejection is the `prefix.apSlot != slotOfFirstAccessor(suffix)` guard in `BaseOnlyAccessOps.appendFinal` (`BaseOnlyAccessOps.kt:101-109`). `BaseOnlyFinalFactAp.concat` (`BaseOnlyFinalFactAp.kt:102-106`) consequently returns `null`, so method-summary application emits no successor fact. The guard conflates the packed slot that happens to hold the abstraction marker with the wildcard's logical path position.

Tree applies the same summary delta to its whole-value wildcard with `concatToLeafAbstractNodes` and produces, respectively:

```text
var(1).payload![setter-fuzz-taint].$
var(1).value![mixed-fuzz-source].$
```

That is the required BaseOnly behavior too. A whole-value wildcard covers every field; refining it with a field-qualified delta is valid. BaseOnly may retain a less precise wildcard as an overapproximation, but it must not return `null`.

### Setter cases (38/38)

For every row below, the fact is present after the payload write. The first listed call applies an identity/side-effect summary for a different field. That application reaches the BO-1 operation above and drops the payload fact. Aliases, helpers, casts, branches, arrays, and dispatch change the route to the call but not the killing operation.

| test case | first summary application that drops the fact | protected tainted field |
|---|---|---|
| `directUnrelatedStringSetter` | `setLabel` (`label`) | `payload` |
| `sourceLocalThenSetter` | `setLabel` (`label`) | `payload` |
| `sourceThroughIdentity` | `setLabel` (`label`) | `payload` |
| `valueAliasChain` | `setLabel` (`label`) | `payload` |
| `receiverAliasBeforeWrite` | `setLabel` (`label`) | `payload` |
| `receiverAliasForKillingSetter` | alias call `setLabel` (`label`) | `payload` |
| `receiverAliasForRead` | `setLabel` (`label`) | `payload` |
| `distinctAliasesForEveryOperation` | metadata alias call `setLabel` (`label`) | `payload` |
| `castReceiverAtSetter` | cast receiver call `setLabel` (`label`) | `payload` |
| `castReceiverAtGetter` | `setLabel` (`label`) | `payload` |
| `castValueBeforePayloadWrite` | `setLabel` (`label`) | `payload` |
| `factoryAllocatedReceiver` | `setLabel` (`label`) | `payload` |
| `receiverThroughIdentityHelper` | `setLabel` (`label`) | `payload` |
| `payloadWriteThroughHelper` | `setLabel` (`label`) | `payload` |
| `payloadReadThroughHelper` | `setLabel` (`label`) | `payload` |
| `writeAndReadThroughHelpers` | `setLabel` (`label`) | `payload` |
| `twoUnrelatedStringSetters` | first `setLabel` (`label`) | `payload` |
| `threeUnrelatedSettersMixedTypes` | first `setLabel` (`label`) | `payload` |
| `primitiveSetterKillsIdentity` | `setCount` (`count`) | `payload` |
| `booleanSetterKillsIdentity` | `setEnabled` (`enabled`) | `payload` |
| `nullMetadataSetter` | `setLabel` (`label`) | `payload` |
| `metadataLocalSetter` | `setLabel` (`label`) | `payload` |
| `metadataIdentitySetter` | `setLabel` (`label`) | `payload` |
| `overwriteMetadataTwice` | first `setLabel` (`label`) | `payload` |
| `branchBeforeKillingSetter` | first `getCount` read summary (`count`); later `setLabel`/`setCategory` calls reject too | `payload` |
| `bothBranchArmsKillIdentity` | first `getCount` read summary (`count`); both `setLabel`/`setCategory` arms reject too | `payload` |
| `branchSelectsSafeMetadata` | first `getCount` read summary (`count`); later `setLabel` rejects too | `payload` |
| `loopKillingSetter` | first loop `setCount` (`count`) | `payload` |
| `doWhileKillingSetter` | first `setCount` (`count`) | `payload` |
| `arrayCarriesReceiverAlias` | array-alias call `setLabel` (`label`) | `payload` |
| `arrayCarriesTaintedValue` | `setLabel` (`label`) | `payload` |
| `holderCarriesReceiverAlias` | `new Holder(box)` constructor field-assignment summary (`box`); later `setLabel`/`setCategory` calls reject too | `payload` |
| `nestedScopeAliasesReceiver` | nested alias call `setLabel` (`label`) | `payload` |
| `sinkValueLocalAfterGetter` | `setLabel` (`label`) | `payload` |
| `sinkValueAliasChainAfterGetter` | `setLabel` (`label`) | `payload` |
| `getterResultThroughIdentity` | `setLabel` (`label`) | `payload` |
| `subclassReceiver` | inherited `setLabel` (`label`) | `payload` |
| `interfaceTypedReceiver` | interface-dispatched `setLabel` (`label`) | `payload` |

### Mixed cases (41/41)

The raw all-case diagnostic contained a `BO-CONCAT ... result=null` record for every method below. Except where noted, the rejected delta is `.value![mixed-fuzz-source].$`; the prefix is a whole-value wildcard carrying an exclusion for the field written by the listed call.

`holderCarriesReceiverAlias` is the important occupied-field variant of the same defect. Its observed prefix is `var(4).box.*` (packed `(-1,8,-2)`) and its delta begins with `.payload`. Tree yields `.box.payload!mark.$`. BaseOnly cannot retain both fields in its one-field representation, but must return a sound marked-descendant overapproximation (at least `.box!mark.$`) rather than `null`.

| test case | first relevant summary application / exclusion |
|---|---|
| `directSetterThenTag` | `setTag` / `tag` |
| `sourceInLocal` | `setTag` / `tag` |
| `identityBeforeStore` | `setTag` / `tag` |
| `identityAfterLoad` | `setTag` / `tag` |
| `aliasBeforeStore` | `setTag` / `tag` |
| `aliasBeforeMutation` | alias `setTag` / `tag` |
| `aliasBeforeLoad` | `setTag` / `tag` |
| `helperStore` | `setTag` / `tag` |
| `helperMutation` | `touch` -> `setTag` / `tag` |
| `helperSink` | `setTag` / `tag` |
| `boxIdentityBeforeStore` | `setTag` / `tag` |
| `boxIdentityBeforeLoad` | `setTag` / `tag` |
| `fluentStore` | `setTag` / `tag` |
| `fluentMutation` | `withTag` / `tag` |
| `fluentChain` | chained `withTag` / `tag` |
| `fluentLoad` | `withTag` / `tag` |
| `doWhileMutation` | first loop `setTag` / `tag` |
| `tryFinallyMutation` | `setTag` / `tag` (the `count` write is independently affected) |
| `switchMutation` | `setTag` / `tag` or `setCount` / `count` |
| `twoUnrelatedMutations` | first `setTag` / `tag` |
| `primitiveMutation` | `setCount` / `count` |
| `objectMutation` | `setOther` / `other` |
| `nullableMutation` | `setOther` / `other` |
| `inheritedMutation` | inherited `setTag` / `tag` |
| `interfaceDispatchMutation` | interface-dispatched `setTag` / `tag` |
| `supplierSource` | `setTag` / `tag` |
| `loadedIntoLocal` | `setTag` / `tag` |
| `loadedThroughTwoLocals` | `setTag` / `tag` |
| `identityTwiceBeforeStore` | `setTag` / `tag` |
| `identityTwiceAfterLoad` | `setTag` / `tag` |
| `tagBeforeAndAfterStore` | second `setTag` / `tag` |
| `countBeforeTagAfterStore` | post-store `setTag` / `tag` |
| `helperStoreAndMutation` | `touch` -> `setTag` / `tag` |
| `helperMutationTwice` | first `touch` -> `setTag` / `tag` |
| `fluentStoreHelperMutation` | `touch` -> `setTag` / `tag` |
| `fluentMutationHelperSink` | `withTag` / `tag` |
| `twoBoxesFirstTainted` | `first.setTag` / `tag` |
| `twoBoxesSecondTainted` | `second.setTag` / `tag` (the clean first-box write does not kill the tainted second-box fact) |
| `synchronizedMutation` | synchronized `setTag` / `tag` |
| `tryCatchMutation` | try `setTag` / `tag` (catch `setCount` is independently affected) |
| `castBeforeLoad` | `setTag` / `tag` |

## Getter reclassification: no forward defect

The earlier collapsed-F2F diagnosis was disproved by two checks:

1. Persisting the collapsed F2F edge (after restoring its abstraction marker) did not change any of the 39 outcomes.
2. With a reference payload, intra-procedural fact inspection for the minimal getter showed the tainted fact at the sink and the analyzer logged `Total vulnerabilities: 1` before trace generation.

The minimal reference-payload operation sequence was sound:

```text
delta:  final=![tainted].$ initial=.*
concat: prefix=.* delta=![tainted].$ result=![tainted].$
sink:   var(1)![tainted].$
```

The subsequent analyzer evidence was:

```text
Total vulnerabilities: 1
Filter out 1 vulnerabilities without traces
```

Across all 39 reference-payload variants, BaseOnly created 40 pre-trace vulnerabilities and filtered all 40 during trace resolution. Consequently, these cases do not identify an incorrect forward BaseOnly operation.

## Original reproduction and verification

The complete differential run was:

```bash
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlySetterFuzzTest' \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyGetterFuzzTest' \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyMixedFuzzTest' \
  -x :opentaint-ir:go:buildGoServer --no-daemon --max-workers=1
```

Observed result: `118 tests completed, 118 failed`, with each failure occurring at the BaseOnly reachability assertion after its Tree assertion succeeded.

Temporary instrumentation logged the inputs and outputs of `collapse`, `read`, `concat`, and F2F edge insertion. It was removed after collecting the evidence; the report is the only durable diagnostic artifact.

## Fix obligations

1. Make `appendFinal` accept a field-qualified delta when the prefix is a broader whole-value wildcard. The result must cover `prefix.<field>.<delta-tail>` and must never be `null` for this refinement.
2. Track the getter trace-generation failure separately if trace resolution becomes part of the BaseOnly verification scope; it is not a forward-analysis regression.
