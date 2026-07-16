# BaseOnlyReferenceMutationFuzz evidence: indices 30..59

## Reproduction

Diagnostic test: `MutationSlice30DiagTest` (temporary; removed after capture) ran the exact 30 methods with Tree followed by BaseOnlyField.

```bash
JAVA_TOOL_OPTIONS='-Dopentaint.debug.mutation=true -Dopentaint.debug.mutation.tree=true' \
  ./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.MutationSlice30DiagTest' \
  -x :opentaint-ir:go:buildGoServer --no-daemon --max-workers=1 \
  -Dkotlin.incremental=false
```

Captured evidence:

- `/tmp/mutation-slice30-tree.xml`: Tree fact concatenations and analyzer totals.
- `/tmp/mutation-slice30.xml`: BaseOnly summary/concat failures and analyzer totals.
- `/tmp/mutation-slice30-tree-run.log`, `/tmp/mutation-slice30-run.log`: Gradle output.

The run had 30 dynamic tests. All 30 Tree analyses logged `Total vulnerabilities: 1`; all 30 BaseOnlyField analyses logged `Total vulnerabilities: 0`. Each dynamic test therefore fails only its deliberate BaseOnly `assertReachable`. This is a forward-analysis loss before trace generation, not trace filtering. There are 43 observed BaseOnly null concats because constructors/factories with sibling fields yield more than one mapped summary fact.

No external methods occur on these paths: all source, setters, constructors, factories, field reads, getters, and sink methods are declared in `BaseOnlyReferenceMutationFuzzSample`. The rule source and sink both fire in Tree, and BaseOnly carries the source fact up to the in-project call summary, ruling out rule or approximation defects.

## Shared incorrect AP operation

For every row, BaseOnly reaches the transfer statement with this exact tainted input fact:

```text
current = var(1).payload![reference-mutation-taint].$/*
```

The setter/constructor/factory summary maps the destination field to an abstract prefix and derives the source object's inner-field suffix:

```text
mapped prefix = destination.<target>.*/{}
delta         = .payload![reference-mutation-taint].$
```

Symbolically, with `f(x)` the interned field index and `m` the mark index:

```text
prefix packed = (-1, f(target), ABSTRACT_MARK=-2), prefix.apSlot = 2
delta  packed = (-1, f(payload), m),             slotOfFirstAccessor(delta) = 1
```

`BaseOnlyFinalFactAp.concat` calls `BaseOnlyAccessOps.appendFinal`. The guard at `BaseOnlyAccessOps.kt:103` requires the slots to be equal and returns `null` because `2 != 1`. Consequently `MethodCallSummaryHandler` emits no mapped successor. The original `box.payload` fact may remain on the old object, but the destination wrapper receives no tainted fact and its later field/getter chain cannot reach the sink.

Tree applies the same summary successfully:

```text
prefix = destination.<target>/*
delta  = .payload![reference-mutation-taint].$
out    = destination.<target>.payload![reference-mutation-taint].$
```

BaseOnly cannot retain two structural fields, so the sound expected overapproximation is:

```text
expected = destination.<target>![reference-mutation-taint].$
packed   = (-1, f(target), m)
```

That is exactly the shape `fillSuffix(prefix.staticIdx, prefix.fieldIdx, suffix)` can produce. The slot-equality guard incorrectly prevents reaching it when an abstract suffix follows an already committed outer field.

## Per-test evidence

In every row, “before” is the observed `var(1).payload![reference-mutation-taint].$/*`; “Base after” is absent because `appendFinal` returned null; “expected” is the target field plus the semantic mark (the sound one-field abstraction). Variable numbers are the observed mapped destination locals.

| idx | method / Java line | first losing statement | observed mapped Base prefix | Tree after | Base actual / expected |
|---:|---|---|---|---|---|
| 30 | `alternateHolderPrimaryField` :195 | `holder.setPrimary(box)` | `var(4).primary.*/{}` | `var(4).primary.payload![mark].$` | `null` / `var(4).primary![mark].$` |
| 31 | `alternateHolderSecondaryField` :199 | `holder.setSecondary(box)` | `var(4).secondary.*/{}` | `var(4).secondary.payload![mark].$` | `null` / `var(4).secondary![mark].$` |
| 32 | `alternateConstructorPrimaryField` :203 | `new AlternateHolder(box, new Box())` | `var(5).primary.*/{}` (also root `*/{.secondary}`) | `var(5).primary.payload![mark].$` | `null` / `var(5).primary![mark].$` |
| 33 | `alternateConstructorSecondaryField` :207 | `new AlternateHolder(new Box(), box)` | `var(5).secondary.*/{}` | `var(5).secondary.payload![mark].$` | `null` / `var(5).secondary![mark].$` |
| 34 | `alternateOverwritePrimaryField` :211 | `holder.setPrimary(box)` | `var(6).primary.*/{}` | `var(6).primary.payload![mark].$` | `null` / `var(6).primary![mark].$` |
| 35 | `alternateOverwriteSecondaryField` :215 | `holder.setSecondary(box)` | `var(6).secondary.*/{}` | `var(6).secondary.payload![mark].$` | `null` / `var(6).secondary![mark].$` |
| 36 | `namedHolderSetBoxAndName` :219 | `holder.setBoxAndName(box, "safe")` | `var(4).box.*/{}` (also root `*/{.name}`) | `var(4).box.payload![mark].$` | `null` / `var(4).box![mark].$` |
| 37 | `namedHolderSetBoxAndNullName` :223 | `holder.setBoxAndName(box, null)` | `var(4).box.*/{}` (also root `*/{.name}`) | `var(4).box.payload![mark].$` | `null` / `var(4).box![mark].$` |
| 38 | `pairThenEnvelopeFirstField` :227 | `new Pair(box, new Box())` | `var(5).first.*/{}` (also root `*/{.second}`) | `var(5).first.payload![mark].$` | `null` / `var(5).first![mark].$` |
| 39 | `pairThenEnvelopeSecondField` :231 | `new Pair(new Box(), box)` | `var(5).second.*/{}` | `var(5).second.payload![mark].$` | `null` / `var(5).second![mark].$` |
| 40 | `quadConstructorFirstArgument` :235 | `new Quad(box, ...)` | `var(7).first.*/{}` (also root excluding second/third/fourth) | `var(7).first.payload![mark].$` | `null` / `var(7).first![mark].$` |
| 41 | `quadConstructorSecondArgument` :239 | `new Quad(..., box, ...)` | `var(7).second.*/{}` (also root excluding third/fourth) | `var(7).second.payload![mark].$` | `null` / `var(7).second![mark].$` |
| 42 | `quadConstructorThirdArgument` :243 | `new Quad(..., box, ...)` | `var(7).third.*/{}` (also root excluding fourth) | `var(7).third.payload![mark].$` | `null` / `var(7).third![mark].$` |
| 43 | `quadConstructorFourthArgument` :247 | `new Quad(..., box)` | `var(7).fourth.*/{}` | `var(7).fourth.payload![mark].$` | `null` / `var(7).fourth![mark].$` |
| 44 | `quadFactoryFirstArgument` :251 | `makeQuadFirst(box)` summary | `var(4).first.*/{}` (also root excluding siblings) | `var(4).first.payload![mark].$` | `null` / `var(4).first![mark].$` |
| 45 | `quadFactorySecondArgument` :255 | `makeQuadSecond(box)` summary | `var(4).second.*/{}` (also root excluding later siblings) | `var(4).second.payload![mark].$` | `null` / `var(4).second![mark].$` |
| 46 | `quadFactoryThirdArgument` :259 | `makeQuadThird(box)` summary | `var(4).third.*/{}` (also root excluding fourth) | `var(4).third.payload![mark].$` | `null` / `var(4).third![mark].$` |
| 47 | `quadFactoryFourthArgument` :263 | `makeQuadFourth(box)` summary | `var(4).fourth.*/{}` | `var(4).fourth.payload![mark].$` | `null` / `var(4).fourth![mark].$` |
| 48 | `keyedConstructorLeftField` :267 | `new KeyedHolder(box, ...)` | `var(6).left.*/{}` (also root excluding center/right) | `var(6).left.payload![mark].$` | `null` / `var(6).left![mark].$` |
| 49 | `keyedConstructorCenterField` :271 | `new KeyedHolder(..., box, ...)` | `var(6).center.*/{}` (also root excluding right) | `var(6).center.payload![mark].$` | `null` / `var(6).center![mark].$` |
| 50 | `keyedConstructorRightField` :275 | `new KeyedHolder(..., box)` | `var(6).right.*/{}` | `var(6).right.payload![mark].$` | `null` / `var(6).right![mark].$` |
| 51 | `keyedSetterLeftField` :279 | `value.setLeft(box)` | `var(4).left.*/{}` | `var(4).left.payload![mark].$` | `null` / `var(4).left![mark].$` |
| 52 | `keyedSetterCenterField` :283 | `value.setCenter(box)` | `var(4).center.*/{}` | `var(4).center.payload![mark].$` | `null` / `var(4).center![mark].$` |
| 53 | `keyedSetterRightField` :287 | `value.setRight(box)` | `var(4).right.*/{}` | `var(4).right.payload![mark].$` | `null` / `var(4).right![mark].$` |
| 54 | `alternatePrimaryViaHelper` :291 | `installPrimary(value, box)` summary | `var(4).primary.*/{}` | `var(4).primary.payload![mark].$` | `null` / `var(4).primary![mark].$` |
| 55 | `alternateSecondaryViaHelper` :295 | `installSecondary(value, box)` summary | `var(4).secondary.*/{}` | `var(4).secondary.payload![mark].$` | `null` / `var(4).secondary![mark].$` |
| 56 | `alternatePrimaryViaNestedHelper` :299 | `nestedInstallPrimary(value, box)` summary | `var(4).primary.*/{}` | `var(4).primary.payload![mark].$` | `null` / `var(4).primary![mark].$` |
| 57 | `alternatePrimaryViaFactory` :303 | `makeAlternatePrimary(box)` summary | `var(4).primary.*/{}` (also root `*/{.secondary}`) | `var(4).primary.payload![mark].$` | `null` / `var(4).primary![mark].$` |
| 58 | `alternatePrimaryNullThenTainted` :307 | second call, `value.setPrimary(box)` | `var(4).primary.*/{}` | `var(4).primary.payload![mark].$` | `null` / `var(4).primary![mark].$` |
| 59 | `alternateSecondaryNullThenTainted` :311 | second call, `value.setSecondary(box)` | `var(4).secondary.*/{}` | `var(4).secondary.payload![mark].$` | `null` / `var(4).secondary![mark].$` |

`[mark]` in the table abbreviates `[reference-mutation-taint]` only; all raw captures contain the full mark name.

## Classification

This is an engine/AP-algebra defect, not a missing library model or rule defect. The killing instructions are ordinary in-project constructors, setters, and their already-computed call summaries. Tree applies each summary and reaches the sink; BaseOnly computes the same semantic delta but rejects it solely in `BaseOnlyAccessOps.appendFinal` before adding the mapped successor.
