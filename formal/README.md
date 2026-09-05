# `formal/` — the machine-checked half of the work

Lean 4, no mathlib, constructive by contract. `Opentaint/Support/Constructive.lean` defines
`#constructive`, which fails the build if a theorem reaches `Classical.choice`; every
load-bearing result goes through it. `lake build` type-checks the proofs, so a green build
with the gate intact *is* the soundness argument — there is nothing to re-run by hand.

```
cd formal && lake build && ./check-map.sh
```

## The mapping law

> **Lean path = source package path. Lean file = source file.** Lowercase each directory
> segment; keep the file name, in the target language's convention. Files with no
> counterpart live only in `Opentaint/Support/`.

```
Opentaint/Cli/Internal/Approximation/Resolve.lean  ->  cli/internal/approximation/resolve.go
Opentaint/Analyzer/Taint/RuleLoader.lean           ->  core/**/org/opentaint/analyzer/taint/RuleLoader.kt
```

`check-map.sh` enforces it, along with `MAP.md` freshness and the absence of `sorry`;
`LEGACY.txt` is the ratchet for files not yet re-homed and must shrink to empty. `MAP.md`
is **generated** by `gen-map.sh` — the index of what is proved about what — and must never
be hand-edited. Source files carrying a model name it in a `// Golden model:` comment, so
both directions are navigable.

The law exists because the alternative — one file per investigation, each with its own
types — produces models that constrain nothing but themselves.

## Method

Proof first, then the test the proof predicts, then the fix — and back to the proof when
the counterexample turns out to be in the model rather than the code.

**"Golden" means the design the invariants force**, not a transcription. Where production
differs, the model keeps the correct design and records the divergence as a theorem with a
counterexample: `shipped_loses_a_project` is a tree the shipped resolver drops a model
project on, and it sits next to `fixed_loses_nothing`, which says the guarded resolver
drops none, on any tree.

The abstraction is kept **sound within a stated scope** rather than made complete. The
example is `noClassLost`: a directory holding compiled classes next to a model project has
no correct classification at all, so the model names the condition (`unambiguous`), proves
the result under it, and the CLI reports the layouts that fall outside instead of guessing.

Where a statement of the concept and the implementation differ only in cost, both are
modelled and proved equal — `resolveFixed` against `resolveFused` (two subtree walks
against one), and always-compile against the stamped cache in `Stamp.lean`.
