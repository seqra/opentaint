# Supplemental metadata source proof

This package proves only the arithmetic and CFG-template facts needed to
interpret two old generated Spring scopes. It does not prove a demand-removal
predicate or import a newer NORMAL provider.

`SpringWebProject.ndMethodDispatch` emits one optional prepare call, five fixed
instructions, two instructions per selected-method branch, and two per saved
registry field. The boundary feature then appends entry, NORMAL exit and
exceptional exit. Thus the old entry index equals the raw body length.

The original root dispatcher has entry index 8. A recorded per-controller
dispatcher proves that at least one controller group exists. Therefore:

```text
6 + 2 * (N + R) = 8, N >= 1  =>  N = 1 and R = 0
```

The same source context supplies the registry to the child dispatcher. Its
old entry index is 11, so it has three branches:

```text
5 + 2 * (Nchild + 0) = 11  =>  Nchild = 3
```

When R=0, target names and branch order do not affect CFG edges. Every branch
has one call and one jump to cleanup. The source uses a switch; converting its
successors to a BitSet removes map-iteration order. Call targets can have
different transfer semantics. Only their generated dispatcher CFG geometry
is shared here.

The checked Python adapter requires the known generated class, method prefix,
Void descriptor, original entry indices, positive child witness and complete
input/source compatibility. It checks every fresh physical CFG edge against
the exact template. The generic deterministic-layout source argument and
native probe then apply to the full topology. Backward discovery ports keep
separate directed witnesses.

Run from `spec/lean`:

```sh
lake env lean proposals/redundant-demand-20261110/metadata/SpringLayout.lean
```

All seven theorems compile. The axioms are limited to `propext` and
`Quot.sound`; the template evaluations use none. There are no proof holes or
classical axioms. The Kotlin builder and frontend remain source-adapter
obligations; the formal model does not verify the complete JVM frontend.

Source correspondence and capture gates are in
[metadata-recapture.md](../../../../../docs/reports/data/redundant-demand-20261110/tools/metadata-recapture.md).
