# Star-operator deep-nesting matrix — characterization report

**Date:** 2026-07-20 · **Commit:** `062543192`

Records what the exhaustive `$*VAR` matrix (Sub-project A) proved about the engine, and the
one characterized gap parked green per the "characterize, don't fix" directive.

## What passes (both languages)

| Shape | Java | Go | Notes |
|---|---|---|---|
| Starred source → deep field read (5 deep) | ✅ `StarDeepSource` | ✅ `star_05` | Java needs `AnyAccessorEnabled` |
| Starred sanitizer clears deep field | ✅ `StarDeepSanitizer` | ✅ `star_06` | |
| Starred source through 5+ hop hide/expose chain | ✅ `StarInterproc` | ✅ `star_07` | Java needs `AnyAccessorEnabled` |
| Starred source + starred sink, nested extraction | ✅ `StarSourceAndSink` | ✅ `star_08` | |
| Starred source + starred sanitizer, deep | ✅ `StarSourceAndSanitizer` | — | |
| Starred sink observes field taint at **depth 1** | ✅ `StarSink` / `StarDeepSink.PositiveDepth1` | ✅ `star_01` | |

Every case is **load-bearing**: an ablation run stripping the `$*` from all six new Java rules
and all five new Go rules turned every corresponding positive into a false negative (and each
sanitizer negative into a false positive). Stars restored → all green again.

## The one characterized gap: starred sink vs. a concrete deep field (Java)

**Observable:** `sink($*Y)` observes a *concrete* field mark on the argument object only when the
mark sits **directly on that object** (depth 1). A mark stored on a **nested sub-object**
(depth ≥ 2, e.g. `o.f.v1 = src(); sink(o)`) is not observed. The cliff is at depth 2 (probed:
depth-1 positive fires, depth-2 and depth-5 do not).

**Parked as:** `taint.StarDeepSink.KnownFnDepth2` / `KnownFnDepth5` — inert classes not matched
by the harness `Positive`/`Negative` name filter, so they neither run nor assert. `PositiveDepth1`
stays a real positive; `NegativeCleanObject` a real negative.

**Why (mechanism, reasoned not fixed):** taint written to `o.f.v1` is tracked on the *sub-object*
`o.f`'s access path, not folded back onto an `o`-rooted access path. The sink's whole-object
any-field check (`evalContainsMarkOnAnyField` → `readAnyPosition`, which *is* recursive over a
single fact's accessor tree) therefore never sees it, because the mark lives on a different fact
base. Depth-1 works because `o.v0` is directly on the argument object. This is a heap/alias
folding limitation, not an any-field-evaluator depth limit.

**Language asymmetry:** Go does **not** exhibit this — `star_04 Positive_depth5` (taint 5 fields
deep, starred whole-object sink) passes. Go's engine folds/propagates the deep-field taint onto
the argument object (or its coarser any-accessor sink handling matches it). Java and Go diverge
here.

**Not contradicted by the passing cases:** `StarSourceAndSink` passes at a depth-2 extraction
because there the *source* is starred — it produces an abstract whole-object any-field taint that
unrolls *downward* to the extracted sub-object. That is the opposite direction from the sink gap,
which needs a concrete deep mark to fold *upward* to the object.

## Follow-up (not in scope here)

If the Java starred-sink deep gap is worth closing, the fix is in the JVM heap/field-store
modeling (fold nested-object field taint back onto the containing object's access path, or make
the sink any-field check consult sub-object facts), not in the querylang star threading. Bringing
Java to Go parity would flip `KnownFnDepth2`/`KnownFnDepth5` into real positives.
