# BaseOnlyReferenceMutationFuzzTest: evidence for samples 0..29

## Scope and reproduction

Assigned corpus: the first 30 entries of `BaseOnlyReferenceMutationFuzzTest.samples`, from
`holderConstructorAfterTaint` through `holderOverwriteTaintedTwice`.

Reproduction command (the test factory was temporarily narrowed to `samples.take(30)` and was
restored after capture):

```text
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyReferenceMutationFuzzTest' \
  -x :opentaint-ir:go:buildGoServer --no-daemon --max-workers=1 --console=plain
```

Result: **30 tests completed, 30 failed**. Every dynamic test first completed its Tree
`assertReachable` and then failed at `AnalysisTest.kt:199`, the BaseOnlyField
`assertReachable`. Thus every assigned case reproduced Tree=1, BaseOnly=0.

Focused evidence command for sample 0:

```text
cd core
JAVA_TOOL_OPTIONS='-Dopentaint.debug.mutation=true' ./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyReferenceMutationFuzzTest' \
  -x :opentaint-ir:go:buildGoServer --no-daemon --max-workers=1 --console=plain
```

Temporary diagnostics logged `FinalFactAp.prependAccessor/readAccessor/delta/concat` and
`MethodCallSummaryHandler` summary composition. They were removed after capture.

## Shared forward-analysis kill

All 30 cases first establish the same fact successfully:

```text
Box-local.payload ![reference-mutation-taint].$
```

The next constructor/setter installs that already-tainted `Box` into an outer wrapper field.
Its method summary maps the destination to an abstract field prefix such as
`Holder-local.box.*`; the incoming argument contributes delta
`.payload![reference-mutation-taint].$`.

The exact failing operation is:

```text
BaseOnlyFinalFactAp.concat
  -> BaseOnlyAccessOps.appendFinal(prefix, suffix, fieldSensitive=true)
```

`appendFinal` rejects the composition at `BaseOnlyAccessOps.kt:103`:

```text
if (prefix.apSlot != slotOfFirstAccessor(suffix)) return null
```

For every row below:

```text
prefix = <destination outer field>.*
prefix.apSlot = 2                         // suffix abstraction slot
suffix = .payload![reference-mutation-taint].$
slotOfFirstAccessor(suffix) = 1           // field slot
actual = null
expected = <destination outer field>.payload![reference-mutation-taint].$
           (or a sound broader non-null BaseOnly representation)
```

The `null` is consumed by `MethodCallSummaryHandler.handleSummary`'s `mapNotNullTo`; no
destination fact is inserted. This is the first forward-analysis loss, before sink matching
or trace resolution.

Captured sample-0 comparison, immediately around the operation:

```text
Tree before:  current=var(1).payload![reference-mutation-taint].$
Tree summary: mapped=var(4).box/*
Tree delta:   .payload![reference-mutation-taint].$
Tree after:   var(4).box.payload![reference-mutation-taint].$

Base before:  current=var(1).payload![reference-mutation-taint].$/*
Base summary: mapped=var(4).box.*/{}
Base delta:   .payload![reference-mutation-taint].$
Base after:   null
```

Raw diagnostic line:

```text
MUT-BO-CONCAT prefix=var(4).box.*/{} delta=... out=null
MUT-SUMMARY current=var(1).payload![reference-mutation-taint].$/* mapped=var(4).box.*/{} ... out=null
```

## Per-sample evidence

All source line numbers refer to
`core/samples/src/main/java/test/samples/BaseOnlyReferenceMutationFuzzSample.java`.
“Before” is the tainted incoming Box fact `.payload!mark`; “Base after” is always `null` from
the exact `appendFinal` mismatch above. The row-specific prefix and expected Tree fact make
the operation evidence explicit for every test.

| idx | sample | first tainted install (entry/callee) | BaseOnly prefix + incoming suffix | Tree / expected after | Base after |
|---:|---|---|---|---|---|
| 0 | `holderConstructorAfterTaint` | entry line 75; `Holder(Box)` write line 545 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 1 | `namedHolderConstructorAfterTaint` | entry 79; `Holder(Box,String)` write 546 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 2 | `holderFactoryAfterTaint` | entry 83; factory 15 -> constructor write 545 | factory result `holder.box.*` + `.payload!mark` | result `holder.box.payload!mark` | `null` |
| 3 | `namedHolderFactoryAfterTaint` | entry 87; factory 16 -> constructor write 546 | factory result `holder.box.*` + `.payload!mark` | result `holder.box.payload!mark` | `null` |
| 4 | `envelopeConstructorAfterTaint` | entry 91; inner `Holder(Box)` write 545 (first kill) | inner holder `.box.*` + `.payload!mark` | `holder.box.payload!mark` (then `envelope.holder.box.payload!mark`) | `null` at inner install |
| 5 | `pairConstructorFirstArgument` | entry 95; `Pair` first-field write 559 | `pair.first.*` + `.payload!mark` | `pair.first.payload!mark` | `null` |
| 6 | `pairConstructorSecondArgument` | entry 99; `Pair` second-field write 559 | `pair.second.*` + `.payload!mark` | `pair.second.payload!mark` | `null` |
| 7 | `assignBoxThroughHolderSetter` | entry 103; `Holder.setBox` write 547 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 8 | `holderConstructorAliasArgument` | entry 107; alias helper 7 preserves input, constructor write 545 kills | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 9 | `holderConstructorLocalAlias` | entry 111; local alias preserves input, constructor write 545 kills | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 10 | `holderConstructorCastArgument` | entry 115; reference cast preserves input, constructor write 545 kills | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 11 | `holderConstructorNullMetadata` | entry 119; constructor write 546 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 12 | `holderConstructorIdentityMetadata` | entry 123; clean metadata identity is irrelevant; constructor write 546 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 13 | `tripleConstructorFirstArgument` | entry 127; `Triple.first` write 566 | `value.first.*` + `.payload!mark` | `value.first.payload!mark` | `null` |
| 14 | `tripleConstructorMiddleArgument` | entry 131; `Triple.second` write 566 | `value.second.*` + `.payload!mark` | `value.second.payload!mark` | `null` |
| 15 | `tripleConstructorLastArgument` | entry 135; `Triple.third` write 566 | `value.third.*` + `.payload!mark` | `value.third.payload!mark` | `null` |
| 16 | `tripleFactoryFirstArgument` | entry 139; factory 20 -> `Triple.first` write 566 | factory result `first.*` + `.payload!mark` | result `first.payload!mark` | `null` |
| 17 | `pairFactoryFirstArgument` | entry 143; factory 18 -> `Pair.first` write 559 | factory result `first.*` + `.payload!mark` | result `first.payload!mark` | `null` |
| 18 | `pairFactorySecondArgument` | entry 147; factory 19 -> `Pair.second` write 559 | factory result `second.*` + `.payload!mark` | result `second.payload!mark` | `null` |
| 19 | `holderFactoryAliasedArgument` | entry 151; factory 17, alias 7, constructor write 545 | factory result `box.*` + `.payload!mark` | result `box.payload!mark` | `null` |
| 20 | `holderFactoryCastArgument` | entry 155; cast preserves input, factory 15 -> write 545 | factory result `box.*` + `.payload!mark` | result `box.payload!mark` | `null` |
| 21 | `nestedHolderFactory` | entry 159; factory 15 -> `Holder.box` write 545 (first kill) | inner result `box.*` + `.payload!mark` | `holder.box.payload!mark` (then envelope nesting) | `null` at inner install |
| 22 | `doubleEnvelopeConstructor` | entry 163; inner `Holder.box` write 545 (first kill) | inner holder `box.*` + `.payload!mark` | `holder.box.payload!mark` (then two outer fields) | `null` at inner install |
| 23 | `envelopeWithMetadataConstructor` | entry 167; inner `Holder.box` write 545 (first kill) | inner holder `box.*` + `.payload!mark` | `holder.box.payload!mark` (then named envelope) | `null` at inner install |
| 24 | `holderSetterViaHelper` | entry 171; helper 25 -> `Holder.setBox` write 547 | helper receiver `box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 25 | `holderSetterWithMetadataViaHelper` | entry 175; helper 26 -> `setBoxAndName` box write 548 | helper receiver `box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 26 | `holderSetterAliasArgument` | entry 179; local alias preserves input; `setBox` write 547 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 27 | `holderSetterCastArgument` | entry 183; cast preserves input; `setBox` write 547 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 28 | `holderOverwriteSafeThenTainted` | entry 187; safe constructor has no taint; first tainted operation is `setBox`, write 547 | `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` | `null` |
| 29 | `holderOverwriteTaintedTwice` | entry 191; first and second `setBox`, write 547 | each application: `holder.box.*` + `.payload!mark` | `holder.box.payload!mark` after either write | `null` on both applications |

## Conclusion

This is one forward-analysis engine defect with 30 syntactic manifestations. It is not a
trace-resolution failure: BaseOnly loses the fact while applying the constructor/setter
summary because `appendFinal` returns `null`. Tree composes the two structural fields and
reaches the sink; BaseOnly must overapproximate that composition rather than reject it.

## Appendix: least-overapproximation algebra

The following algebra independently establishes the least-imprecise non-null BaseOnly result for the cross-slot composition diagnosed above.

## Least imprecise representable results

### A. Known field prefix plus field-leading marked suffix

```text
prefix = (S, Fo, *)       meaning base.Fo.*
suffix = (-, Fi, M)       meaning delta.Fi.!M.$

Tree exact concatenation = base.Fo.Fi.!M.$
BaseOnly expected        = (S, Fo, M) = base.Fo.!M.$
current                  = null
```

BaseOnly has only one field slot, so it cannot retain both `Fo` and `Fi`. Keeping the known
outer field and dropping the inner field is the least imprecise sound representation. It is
sound under the current read algebra: reading `Fo` yields `!M.$`; once the semantic mark is at
the head, `headRead` returns `KEEP` for every further structural read, including `Fi`.

This is also exactly what `fillSuffix(S,Fo,suffix)` computes today if the cross-slot guard is
not allowed to reject first: it retains `(S,Fo)` and takes terminal `M` from the suffix.

### B. Whole-object suffix hole plus field-leading marked suffix

```text
prefix = (-, -, *)        meaning base.*
suffix = (-, Fi, M)       meaning delta.Fi.!M.$

Tree exact concatenation = base.Fi.!M.$
BaseOnly expected        = (-, Fi, M) = base.Fi.!M.$
current                  = null
```

There is no earlier field competing for the sole field slot, so BaseOnly should retain the
suffix field. Returning mark-only `(-,-,M)` would also be sound but needlessly less precise;
the least overapproximation is the suffix itself. With a concrete static prefix `(S,-,*)`, the
corresponding representable result is `(S,Fi,M)`.

### C. Array-element-leading marked suffix

Element is structural and occupies the same packed slot as a field, so the same algebra
applies with `Fi := E`:

```text
known field prefix:
  (S, Fo, *) ++ (-, E, M)
  Tree exact = base.Fo[E].!M.$
  BaseOnly expected = (S, Fo, M)       // retain outer field, absorb element
  current = null

whole prefix:
  (-, -, *) ++ (-, E, M)
  Tree exact = base[E].!M.$
  BaseOnly expected = (-, E, M)        // retain element in free field slot
  current = null
```

For the first result, reading `Fo` yields mark-only and a subsequent element read keeps that
mark. For the second, reading `E` consumes the element and yields mark-only.
