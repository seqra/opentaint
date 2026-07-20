# Star-operator exhaustive tests + result-array hack removal — Design

**Branch:** `misonijnik/star-operator`
**Date:** 2026-07-20

Two independent sub-projects. Sub-project A (tests) is additive and safe; Sub-project B
(hack removal) is a behavior-changing engine edit gated on the OWASP trace count. Sequence
A → B; A merges independently of B's OWASP outcome.

---

## Sub-project A — exhaustive `$*VAR` star-operator test matrix (Java + Go)

### Goal

Stress the `$*VAR` any-field (whole-object) taint through:

- **deep field nesting** — taint hidden 5+ fields deep (`obj.a.b.c.d.e`),
- **deep interprocedural chains** — 5+ nested calls between source and sink,
- **alternation** — hide taint inside an object at one step, expose it a couple of steps
  later, re-wrap, expose again ("hide and make out taint inside objects"),
- both **directions** — hide source deep / expose at sink, and vice-versa; taint entering
  the object at the sink boundary; sanitizer clearing deep-field taint.

Covered star positions: source, sink, sanitizer, and the source+sink / source+sanitizer
combinations.

### Layout — few files, many cases

Extend the existing harnesses; do not invent new ones.

**Java** — new abstract sample classes under
`core/opentaint-java-querylang/samples/src/main/java/taint/`, each with a matching YAML under
`.../resources/taint/` (same base name, referenced via `@RuleSet`), wired into
`StarOperatorTest.kt`. The harness (`SampleBasedTest`) discovers nested classes by simple
name: `*Positive*` must report ≥1 vulnerability, `*Negative*` must report none. A negative
annotated `@IFDSFalsePositive` / `@TaintRuleFalsePositive` is downgraded to a skipped warning.

Planned files (each holds many nested Positive/Negative cases):

- `StarDeepSource.java` — `$*X = src()` taints a 5-deep field chain; unhide via nested field
  reads to a scalar sink. Needs `unrollStrategy = AnyAccessorEnabled` (mirrors existing
  `StarSource`). Removing the `*` must turn the positive into an FN (star is load-bearing).
- `StarDeepSink.java` — plain source taints a deep field; `sink($*Y)` observes it under the
  default `AnyAccessorDisabled`.
- `StarDeepSanitizer.java` — `clean($*C)` must clear deep-field taint; positive (no clean) vs
  negative (cleaned).
- `StarInterproc.java` — 5+ nested helper calls threading the object; taint written at call
  *k*, read at call *k+2* (alternation).
- `StarSourceAndSink.java`, `StarSourceAndSanitizer.java` — combined star positions.

**Go** — new dirs `core/opentaint-go-querylang/samples-go-massive/star_04_*` … following the
existing `star_01..03` pattern (one `rule.yaml` + one `sample.go`, top-level `Positive_*` /
`Negative_*` funcs, package `util`, import path `samples/<dir>`), wired into
`GoMassiveSampleTest.kt`. Same six shapes. Go always unrolls any-accessor (no per-test flag).

### Failure policy — characterize, don't fix

A case the engine cannot satisfy is **not** treated as a bug to fix in this sub-project.
Instead:

- Java: land it as a Negative marked `@IFDSFalsePositive` / `@TaintRuleFalsePositive` with a
  comment, or as a Positive documented as a known FN and excluded — whichever matches the
  actual gap — so the suite stays green.
- Go: keep it out of the asserted `Positive_*`/`Negative_*` set with a `// KNOWN GAP:` comment
  (Go harness has no skip annotation).
- Produce a written report of every characterized gap (shape, depth, direction, language) for
  separate triage.

The matrix becomes a living spec of what any-field depth actually supports.

### Run commands

```
cd core
./gradlew :opentaint-java-querylang:test --tests "org.opentaint.semgrep.StarOperatorTest"
./gradlew :opentaint-go-querylang:test --tests "org.opentaint.semgrep.GoMassiveSampleTest.star*"
```

---

## Sub-project B — remove the result-array hack

### The hack (three coupled pieces)

1. `MethodTaintConfigurationResolver.resolveArrayPosition` (config side) silently duplicates a
   source-action / `ContainsMark` / `ContainsMarkOnAnyField` position whose declared type
   `isArray` **or is exactly `java.lang.Object`** into `{pos, pos[*]}`.
2. `JIRMethodCallTaintUtil.arrayElementConditionReaders` (runtime side) lets element-only taint
   satisfy a whole-array sink condition; Go has a copy in `GoMethodCallTaintUtil.kt` (no type
   guard).
3. `PatternToActionListConverter.kt:180-193` deliberately **drops** `$X[...]` array indices,
   relying on (1)/(2) to recover the match (`// todo: dirty hack ... hackResultArray`).

### Change

1. **Keep the dirty hack, route it through star.** `PatternToActionListConverter`'s
   `ArrayAccess` branch stops relying on `resolveArrayPosition`; it **forces the metavar
   starred** (`IsMetavar.star = true`) so `$X[...]` compiles to any-field taint. Concrete index
   still ignored, now handled by the star/any-accessor machinery (which already unrolls
   `ElementAccessor`).
2. Delete `resolveArrayPosition` + its 4 call sites; collapse the now-identical
   `resolveWithArray` / `resolveNoArray` into one.
3. Delete `arrayElementConditionReaders` (JVM), the Go copy in `GoMethodCallTaintUtil.kt`, and
   the now-dead `callArgumentMayBeArray`. Keep `FinalFactReaderWithPrefix`.
4. **Out of scope:** `JIRMethodSequentFlowFunction.kt:554` weak-update hack stays.

### OWASP gate (non-negotiable)

- **Baseline before any change:** build `:projectAnalyzerJar` + autobuilder, run on
  `~/BenchmarkJava`, capture `TraceGenerationStats total` (expect **3619**) and the full
  `report-ifds.sarif` as golden.
- **After change:** re-run; `total` must equal **3619 exactly**; diff SARIF vs golden.
- Direct querylang dependents must stay green: `ExampleTest.\`test array example\``,
  `IssuesTest.\`issue 84\`` (recovered via the star routing).
- If `total ≠ 3619` or a true positive is lost: **report the delta and root cause and stop.**
  No poorly-designed patch — the user decides next.

### Known risk

`resolveArrayPosition` also fires implicitly for every `java.lang.Object`-typed source/condition
across `model/java/config/**` (634 `[*]` positions live in the model, mostly in `copy:` blocks
which are *not* routed through the hack, but implicit `Object`/`Object[]` duplication is). The
star routing only covers *pattern-derived* rules, not the model's implicit duplication, so the
trace count may shift. Measuring and reporting the delta is the deliverable if it does.
