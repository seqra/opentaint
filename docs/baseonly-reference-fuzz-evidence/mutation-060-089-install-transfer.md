# BaseOnly reference mutation/install/transfer evidence

## Scope and reproduction

Requested scope: `BaseOnlyReferenceMutationFuzzTest` indices 60..89 (30), both `BaseOnlyReferenceInstallFuzzTest` cases (2), and all `BaseOnlyReferenceTransferFuzzTest` cases (9): 41 total.

Command (from `core/`):

```text
JAVA_TOOL_OPTIONS='-Dopentaint.debug.ref41=true -Dopentaint.debug.mutation.tree=true' ./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyReferenceMutationFuzzTest' \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyReferenceInstallFuzzTest' \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyReferenceTransferFuzzTest' \
  -x :opentaint-ir:go:buildGoServer -x :opentaint-go-querylang:compileKotlin \
  --no-daemon --max-workers=1
```

The Mutation factory was temporarily sliced with `samples.drop(60)` and restored after capture. Result: 41 tests executed, 41 BaseOnly assertions failed, zero Tree assertions failed. The coordinated forward-stage run also reported exactly one Tree pre-trace vulnerability and zero BaseOnly pre-trace vulnerabilities for every row, so these are forward-analysis losses, not trace-resolution filtering.

Captured failing concatenations: Mutation 47 (some methods have additional identity/branch summary failures), Install 2, Transfer 10 (one additional abstract delta). Every required test has at least one taint-carrying failing concatenation.

## Common root cause and exact operation

All 41 losses are one BaseOnly operation: `BaseOnlyFinalFactAp.concat` calls `BaseOnlyAccessOps.appendFinal` (`BaseOnlyAccessOps.kt:101-109`). The destination summary has already committed one outer reference field, so the mapped prefix is `base.<outer>.*`, packed `(-1, outerFieldIdx, -2)` and `prefix.apSlot == 2`. The delta begins with another structural field (or array element), packed `(-1, innerFieldOrElementIdx, markIdx)` and `slotOfFirstAccessor(delta) == 1`. Line 103 rejects the valid wildcard substitution because `2 != 1`, returning `null`. `MethodCallSummaryHandler.handleSummary` consequently emits no successor.

Representative captured BaseOnly facts:

```text
Mutation: prefix=var(4).primary.*/{} packed=(-1,4,-2)
          delta=.payload![reference-mutation-taint].$ packed=(-1,0,2)
          out=null
Install:  prefix=var(3).cell.*/{} packed=(-1,4,-2)
          delta=.value![reference-install-taint].$ packed=(-1,0,2)
          out=null
Transfer: prefix=var(3).box.*/{} packed=(-1,4,-2)
          delta=.payload![reference-transfer-source].$ packed=(-1,0,2)
          out=null
Array:    prefix=var(3).values.*/{} packed=(-1,0,-2)
          delta=[*]![reference-transfer-source].$ packed=(-1,11,2)
          out=null
```

The corresponding Tree operation is `AccessTree.concatToLeafAbstractNodes`. Captured Tree comparisons:

```text
prefix=var(6).primary/* + delta=.payload!mark.$ -> var(6).primary.payload!mark.$
prefix=var(3).cell/*    + delta=.value!mark.$   -> var(3).cell.value!mark.$
prefix=var(3).box/*     + delta=.payload!mark.$ -> var(3).box.payload!mark.$
prefix=var(3).values/*  + delta=[*]!mark.$      -> var(3).values[*]!mark.$
```

Expected BaseOnly behavior is a non-null safe abstraction. Since BaseOnly has one structural field slot, it should retain the committed outer field and collapse the deeper marked descendant: `base.<outer>![mark].$` (or an equivalently broader marked descendant fact). For a whole-value identity prefix, it can retain the inner field exactly as `base.<inner>![mark].$`. Returning `null` is an under-approximation.

Cluster keys used below:

- **M(field)**: `Box.payload!mutationMark` enters wrapper `field`; Tree produces `wrapper.field.payload!mark`; BaseOnly applies `appendFinal(wrapper.field.*, .payload!mark)` and returns null; expected at least `wrapper.field!mark`.
- **I(cell)**: `Cell.value!installMark` enters `Envelope.cell`; Tree produces `envelope.cell.value!mark`; BaseOnly applies `appendFinal(envelope.cell.*, .value!mark)` and returns null; expected at least `envelope.cell!mark`.
- **R(box)**: `PayloadBox.payload!transferMark` enters `Envelope.box`; Tree produces `envelope.box.payload!mark`; BaseOnly applies `appendFinal(envelope.box.*, .payload!mark)` and returns null; expected at least `envelope.box!mark`.
- **A(values)**: marked array element enters `ArrayEnvelope.values`; Tree produces `envelope.values[*]!mark`; BaseOnly applies `appendFinal(envelope.values.*, [*]!mark)` and returns null; expected at least `envelope.values!mark`.

The Java call/install statement is where the callee field-write summary is applied. The associated JIR statement is the listed `this.<field> = arg(n)` (or equivalent setter assignment); the fact is present before this summary application and absent immediately after BaseOnly returns null.

## Explicit evidence rows

| # | Test | Java loss site | Callee IR / summary write | Fact comparison and operation |
|---:|---|---|---|---|
| 1 | `alternatePrimarySafeThenTaintedViaHelper` | Mutation sample:315, `installPrimary(value, box)` | helper :27 -> `setPrimary`; :582 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0 |
| 2 | `holderNullThenTainted` | :319, second `value.setBox(box)` | :547 `this.box = arg0` | **M(box)**; Tree 1, BaseOnly 0 |
| 3 | `holderTaintedNullThenTainted` | :323, first `value.setBox(box)` | :547 `this.box = arg0` | **M(box)**; Tree 1, BaseOnly 0; later overwrites do not restore the dropped successor |
| 4 | `quadEnvelopeFirstField` | :327, inner `new Quad(box, ...)` | :574 `this.first = arg0` | **M(first)**; Tree 1, BaseOnly 0; loss precedes `QuadEnvelope.quad` wrapping |
| 5 | `quadEnvelopeFourthField` | :331, inner `new Quad(..., box)` | :574 `this.fourth = arg3` | **M(fourth)**; Tree 1, BaseOnly 0 |
| 6 | `alternateEnvelopePrimaryField` | :335, inner `new AlternateHolder(box, ...)` | :581 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0 |
| 7 | `alternateEnvelopeSecondaryField` | :339, inner `new AlternateHolder(..., box)` | :581 `this.secondary = arg1` | **M(secondary)**; Tree 1, BaseOnly 0 |
| 8 | `alternateSetBothFirstArgument` | :343, `value.setBoth(box, ...)` | :584 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0 |
| 9 | `alternateSetBothSecondArgument` | :347, `value.setBoth(..., box)` | :584 `this.secondary = arg1` | **M(secondary)**; Tree 1, BaseOnly 0 |
| 10 | `keyedSetAllCenterArgument` | :351, `value.setAll(..., box, ...)` | :596 `this.center = arg1` | **M(center)**; Tree 1, BaseOnly 0 |
| 11 | `quadConstructorFirstWithNullPeers` | :355, `new Quad(box, null, null, null)` | :574 `this.first = arg0` | **M(first)**; Tree 1, BaseOnly 0 |
| 12 | `quadConstructorSecondWithNullPeers` | :359, `new Quad(null, box, null, null)` | :574 `this.second = arg1` | **M(second)**; Tree 1, BaseOnly 0 |
| 13 | `quadConstructorThirdWithNullPeers` | :363, `new Quad(null, null, box, null)` | :574 `this.third = arg2` | **M(third)**; Tree 1, BaseOnly 0 |
| 14 | `quadConstructorFourthWithNullPeers` | :367, `new Quad(null, null, null, box)` | :574 `this.fourth = arg3` | **M(fourth)**; Tree 1, BaseOnly 0 |
| 15 | `keyedConstructorLeftWithNullPeers` | :371, `new KeyedHolder(box, null, null)` | :592 `this.left = arg0` | **M(left)**; Tree 1, BaseOnly 0 |
| 16 | `keyedConstructorCenterWithNullPeers` | :375, `new KeyedHolder(null, box, null)` | :592 `this.center = arg1` | **M(center)**; Tree 1, BaseOnly 0 |
| 17 | `keyedConstructorRightWithNullPeers` | :379, `new KeyedHolder(null, null, box)` | :592 `this.right = arg2` | **M(right)**; Tree 1, BaseOnly 0 |
| 18 | `keyedEnvelopeLeftField` | :383, inner `new KeyedHolder(box, ...)` | :592 `this.left = arg0` | **M(left)**; Tree 1, BaseOnly 0; loss precedes envelope wrapping |
| 19 | `keyedEnvelopeCenterField` | :387, inner `new KeyedHolder(..., box, ...)` | :592 `this.center = arg1` | **M(center)**; Tree 1, BaseOnly 0 |
| 20 | `keyedEnvelopeRightField` | :391, inner `new KeyedHolder(..., box)` | :592 `this.right = arg2` | **M(right)**; Tree 1, BaseOnly 0 |
| 21 | `doubleAlternateEnvelopePrimaryField` | :395, innermost `new AlternateHolder(box, ...)` | :581 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0; first of three wrappers is the kill |
| 22 | `doubleAlternateEnvelopeSecondaryField` | :399, innermost `new AlternateHolder(..., box)` | :581 `this.secondary = arg1` | **M(secondary)**; Tree 1, BaseOnly 0 |
| 23 | `keyedOverwriteLeftSafeThenTainted` | :403, `value.setLeft(box)` | :593 `this.left = arg0` | **M(left)**; Tree 1, BaseOnly 0 |
| 24 | `keyedOverwriteCenterSafeThenTainted` | :407, `value.setCenter(box)` | :594 `this.center = arg0` | **M(center)**; Tree 1, BaseOnly 0 |
| 25 | `keyedOverwriteRightSafeThenTainted` | :411, `value.setRight(box)` | :595 `this.right = arg0` | **M(right)**; Tree 1, BaseOnly 0 |
| 26 | `alternateSetBothFirstWithNullPeer` | :415, `value.setBoth(box, null)` | :584 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0 |
| 27 | `alternateSetBothSecondWithNullPeer` | :419, `value.setBoth(null, box)` | :584 `this.secondary = arg1` | **M(secondary)**; Tree 1, BaseOnly 0 |
| 28 | `keyedFactoryLeftField` | :423, `makeKeyedLeft(box)` | helper :31 -> constructor :592 `this.left = arg0` | **M(left)**; Tree 1, BaseOnly 0 |
| 29 | `keyedFactoryCenterField` | :427, `makeKeyedCenter(box)` | helper :32 -> constructor :592 `this.center = arg1` | **M(center)**; Tree 1, BaseOnly 0 |
| 30 | `alternateConstructorPrimaryWithNullPeer` | :431, `new AlternateHolder(box, null)` | :581 `this.primary = arg0` | **M(primary)**; Tree 1, BaseOnly 0 |
| 31 | `constructorInstallThroughEnvelope` | Install sample:171, outer `new Envelope(new Cell(source()))` after `Cell.value` succeeds | :224 `this.cell = arg0`; inner value write :213 | **I(cell)**; Tree 1, BaseOnly 0 |
| 32 | `constructorInstallThroughTwoEnvelopes` | :176, inner `new Envelope(new Cell(source()))` | :224 `this.cell = arg0`; outer envelope is downstream | **I(cell)**; Tree 1, BaseOnly 0 |
| 33 | `nestedEnvelopeConstructors` | Transfer sample:20, outer `new Envelope(new PayloadBox(source()))` | :62 `this.box = arg0`; payload write :55 succeeds | **R(box)**; Tree 1, BaseOnly 0 |
| 34 | `tripleNestedConstructors` | :21, inner `new Envelope(new PayloadBox(source()))` | :62 `this.box = arg0`; `Outer.envelope` is downstream | **R(box)**; Tree 1, BaseOnly 0 |
| 35 | `envelopeFactory` | call :28; helper :10 `new Envelope(box)` | :62 `this.box = arg0` | **R(box)**; Tree 1, BaseOnly 0 |
| 36 | `envelopeFactoryFromValue` | call :29; helper :11 outer `new Envelope(new PayloadBox(value))` | :62 `this.box = arg0` after :55 payload succeeds | **R(box)**; Tree 1, BaseOnly 0 |
| 37 | `outerFactoryFromValue` | call :30; helper :12 inner `new Envelope(new PayloadBox(value))` | :62 `this.box = arg0`; outer write :68 is downstream | **R(box)**; Tree 1, BaseOnly 0 |
| 38 | `envelopeSetterAfterPayloadConstructor` | call :39; helper :15 `envelope.setBox(box)` | :63 `this.box = arg0` | **R(box)**; Tree 1, BaseOnly 0 |
| 39 | `envelopeSetterAfterPayloadSetter` | :40, `envelope.setBox(box)` | :63 `this.box = arg0` | **R(box)**; Tree 1, BaseOnly 0 |
| 40 | `fluentNestedEnvelope` | :44, `.withBox(new PayloadBox().withPayload(source()))` | :64 `this.box = arg0`, return `this` | **R(box)**; Tree 1, BaseOnly 0 |
| 41 | `referenceArrayWrapper` | :50, `new ArrayEnvelope(new String[]{source()})` | :79 `this.values = arg0` | **A(values)**; Tree 1, BaseOnly 0 |

## Conclusion

Every requested forward miss is caused by the same under-approximating `appendFinal` slot-alignment guard. The failure is not source matching, field-write propagation, sink matching, or trace resolution: the inner marked fact exists, Tree applies the wrapper summary and creates the nested successor, while BaseOnly receives the corresponding mapped prefix and delta but returns null before a vulnerability can be added.

All temporary BaseOnly logging and the Mutation slice were restored after the run. No committed corpus files remain modified or deleted by this investigation.
