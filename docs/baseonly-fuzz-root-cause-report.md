# BaseOnlyField fuzz regression root-cause report

## Scope and result

The corpus contains 118 independently executed differential tests:

- 38 `BaseOnlySetterFuzzTest` cases;
- 39 `BaseOnlyGetterFuzzTest` cases;
- 41 `BaseOnlyMixedFuzzTest` cases.

For every case, Tree reaches the sink and BaseOnlyField does not. A combined run confirmed 118/118 BaseOnly assertion failures. The misses are forward-analysis failures: the fact is discarded before a sink fact exists, so trace resolution is not involved.

All 118 cases reduce to two BaseOnly operation defects:

| defect | affected cases | incorrect BaseOnly operation |
|---|---:|---|
| BO-1 | 79 (38 setter + 41 mixed) | `BaseOnlyAccessOps.appendFinal` rejects a field delta when the destination is a whole-value wildcard solely because their abstraction slots differ. |
| BO-2 | 39 getter | A field read preserves the internal collapsed marker, after which `MethodEdgesInitialToFinalBaseOnlyApSet.PerStatement.add` silently rejects the collapsed fact. |

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

## BO-2: collapsed getter fact is silently rejected by F2F storage

### Exact evidence

Getter analysis starts with an abstract receiver fact:

```text
<this>.*/{}                 packed=(-1,-1,ABSTRACT_MARK)
```

The following BaseOnly operations occur while analyzing a getter body:

```text
BaseOnlyAccessOps.collapse(<this>.*) = <this>.^
BaseOnlyAccessOps.read(<this>.^, Owner#id) = <this>.^
MethodEdgesInitialToFinalBaseOnlyApSet.PerStatement.add(final=<this>.^) = null
```

Captured evidence for `directGetter`:

```text
BO FINAL read in=<this>.^/{} accessor=BaseOnlyGetterFuzzSample$Owner#id out=<this>.^/{}
```

`BaseOnlyFinalFactAp.removeAbstraction` creates the collapsed marker via `BaseOnlyAccessOps.collapse` (`BaseOnlyAccessOps.kt:51-55`). `read` (`BaseOnlyAccessOps.kt:71-75`) deliberately keeps the marker for a structural accessor. The exact kill is then the `if (final.access.isCollapsed) return null` guard in `MethodEdgesInitialToFinalBaseOnlyApSet.PerStatement.add` (`MethodEdgesInitialToFinalBaseOnlyApSet.kt:69`). No getter F2F summary is stored, so no tainted return fact can be created at the caller.

Tree retains the equivalent path. The captured Tree sequence for `directGetter` was:

```text
source/caller:  var(1).[any]![base-only-getter-fuzz].$
field path:     var(1).id.[any]![base-only-getter-fuzz].$
getter return:  var(2).[any]![base-only-getter-fuzz].$
```

Expected BaseOnly behavior: the field read must produce a storable fact (either preserve enough state until rebasing restores abstraction, or materialize a field-qualified abstract fact), and edge insertion must return a non-null edge. Silently discarding the only overapproximating fact is unsound.

### Getter cases (39/39)

| test case | first killed getter/field read |
|---|---|
| `directGetter` | `Owner#getId`: `Owner#id` |
| `getterIntoLocal` | `Owner#getId`: `Owner#id` |
| `getterWithReassignment` | `Owner#getId`: `Owner#id` |
| `getterThroughIdentity` | `Owner#getId`: `Owner#id` |
| `getterThroughTwoCalls` | `Owner#getId`: `Owner#id` |
| `getterInCallee` | `extract` -> `Owner#getId`: `Owner#id` |
| `getterAndLocalInCallee` | `extractViaLocal` -> `Owner#getId`: `Owner#id` |
| `getterAfterReceiverAlias` | `Owner#getId`: `Owner#id` |
| `getterAfterTwoReceiverAliases` | `Owner#getId`: `Owner#id` |
| `getterInIfThen` | `Owner#getId`: `Owner#id` |
| `getterAfterIfAssignment` | `Owner#getId`: `Owner#id` |
| `getterInTernary` | `Owner#getId`: `Owner#id` |
| `getterAsTernaryArm` | `Owner#getId`: `Owner#id` |
| `getterInSwitch` | first `Owner#getMode`: `Owner#mode`; sink arm `Owner#getId`: `Owner#id` is independently killed |
| `getterInForLoop` | `Owner#getId`: `Owner#id` |
| `getterInWhileLoop` | `Owner#getId`: `Owner#id` |
| `getterInDoWhileLoop` | `Owner#getId`: `Owner#id` |
| `getterInTry` | `Owner#getId`: `Owner#id` |
| `getterInSynchronized` | `Owner#getId`: `Owner#id` |
| `nestedGetter` | first `Owner#getProfile`: `Owner#profile`; subsequent `Profile#getId`: `Profile#id` is independently affected |
| `nestedGetterViaLocal` | first `Owner#getProfile`: `Owner#profile`; then `Profile#getId`: `Profile#id` |
| `nestedGetterAndValueLocal` | first `Owner#getProfile`: `Owner#profile`; then `Profile#getId`: `Profile#id` |
| `nestedGetterThroughIdentity` | first `Owner#getProfile`: `Owner#profile`; then `Profile#getId`: `Profile#id` |
| `nestedPublicField` | `Owner#getProfile`: `Owner#profile`; the following `publicId` read never receives taint |
| `nestedFieldViaLocal` | `Owner#getProfile`: `Owner#profile`; the following `publicId` read never receives taint |
| `getterReturningFieldViaLocal` | `LocalGetterOwner#getId`: `LocalGetterOwner#id` |
| `getterReturningConditionalField` | `ConditionalGetterOwner#getId`: `ConditionalGetterOwner#id` (both reads) |
| `getterDelegatingToPrivateMethod` | `DelegatingOwner#getId` -> `readId`: `DelegatingOwner#id` |
| `inheritedGetter` | `BaseOwner#getId`: `BaseOwner#id` |
| `overriddenGetter` | `OverridingOwner#getId` -> `BaseOwner#getId`: `BaseOwner#id` |
| `getterFromInterfaceImplementation` | `InterfaceOwner#getId`: `InterfaceOwner#id` |
| `getterAfterReceiverIdentity` | after `self`, `Owner#getId`: `Owner#id` |
| `getterAfterTwoReceiverMethods` | after two `self` calls, `Owner#getId`: `Owner#id` |
| `getterFromArrayField` | `ArrayOwner#getFirstId`: first `ArrayOwner#ids` read; element read is also affected |
| `getterFromNestedArray` | `ArrayOwner#getIds`: `ArrayOwner#ids`; element read follows |
| `getterStoredInFreshBox` | `Owner#getId`: `Owner#id`, before construction |
| `getterStoredBySetter` | `Owner#getId`: `Owner#id`, before `Box#setValue` |
| `getterSelectedWithCleanValue` | `Owner#getId`: `Owner#id` |
| `twoGetterCandidates` | first `Owner#getMode`: `Owner#mode`; `Owner#id` and `Owner#backupId` arms are independently killed |

## Reproduction and verification

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
2. Do not discard a collapsed fact at F2F edge insertion when that fact represents a reachable field read. Convert it to a storable abstraction or defer collapse restoration until after the read/rebase operation.
3. Keep all 118 current tests as positive BaseOnly oracles. A correct fix makes all Tree and BaseOnly assertions pass without weakening the source or sink rules.
