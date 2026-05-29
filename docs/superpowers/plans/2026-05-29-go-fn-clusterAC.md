# Go FN Clusters A & C — reproduce + diagnose + propose Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Commit 7 reproducing tests for FN clusters A (source-shape matching) and C (dataflow engine), diagnose each to its responsible engine component, and produce a fix-proposal document for review. **No fixes are implemented.**

**Architecture:** Cluster A samples are full rule→reachability fixtures under `opentaint-go-querylang/samples-go/`; diagnosis inspects the produced `GoSerializedItem` first (rule-translation vs engine) then the full fact dump. Cluster C samples are `AnalysisTest` `001T/002F` fixtures under `core/samples`; diagnosis uses the full `printFactsAt` dump. The deliverable is a `test → description → fix proposal → post-fix behavior` doc.

**Tech Stack:** Kotlin, Go fixtures, the OpenTaint semgrep→Go query layer + IFDS engine.

---

## Preliminaries

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
export PATH="/home/sobol/local/bin:$PATH"
```
Tests use `-x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks`. Spec: `docs/superpowers/specs/2026-05-29-go-fn-clusterA-clusterC-design.md`.

Confirmed infra facts (do not re-derive):
- Cluster A harness `GoSampleBasedTest` (`core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt`): a sample is `samples-go/<Name>/` with `go.mod` (`module util`), exactly one `*.yaml` (mode: taint), and `*.go` in `package util` with top-level `Positive_*` (expect ≥1 vuln) / `Negative_*` (expect 0) funcs. Entry points = those funcs (any signature; a `*http.Request` param is fine). Register with `@Test fun name() = runSample("Name")`. A reproducing (failing) sample's test gets `@Disabled("Cluster A: <reason>")`.
- Cluster C harness `AnalysisTest` (`core/src/test/kotlin/org/opentaint/go/sast/dataflow/`): `001T`=`assertReachable`, `002F`=`assertNotReachable`, sources/sinks `test/util.Source`/`Sink`. Samples in `core/samples/src/main/go/`. Full fact dump via `EngineRoadmapDiagnosticTest`-style `printFactsAt`.
- `printFactsAt` writes `/tmp/go-engine-roadmap-facts/<entry>.txt`.

---

## Task 1: Cluster A reproducing samples (4)

**Files (create under `core/opentaint-go-querylang/samples-go/`):**
- `SourceUrlRawQuery/{go.mod,rule.yaml,sample.go}`
- `SourceHeaderMapIndex/{go.mod,rule.yaml,sample.go}`
- `SourceFormParse/{go.mod,rule.yaml,sample.go}`
- `SourceBeegoCtxInput/{go.mod,rule.yaml,sample.go}`
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt` (add 4 `@Test` methods)

Every `go.mod` is:
```
module util

go 1.21
```

- [ ] **Step 1: SourceUrlRawQuery sample**

`SourceUrlRawQuery/rule.yaml`:
```yaml
rules:
  - id: source-url-rawquery
    languages: [go]
    severity: WARNING
    message: "Taint from r.URL.RawQuery reaches Sink"
    mode: taint
    pattern-sources:
      - pattern: "$R.URL.RawQuery"
    pattern-sinks:
      - pattern: "util.Sink($X)"
```
`SourceUrlRawQuery/sample.go`:
```go
package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_rawquery(r *http.Request) {
	s := r.URL.RawQuery
	Sink(s)
}

func Negative_const(r *http.Request) {
	_ = r
	s := "safe"
	Sink(s)
}
```

- [ ] **Step 2: SourceHeaderMapIndex sample**

`SourceHeaderMapIndex/rule.yaml`:
```yaml
rules:
  - id: source-header-mapindex
    languages: [go]
    severity: WARNING
    message: "Taint from r.Header reaches Sink"
    mode: taint
    pattern-sources:
      - pattern: "$R.Header"
      - pattern: "$R.Header.Get($K)"
    pattern-sinks:
      - pattern: "util.Sink($X)"
```
`SourceHeaderMapIndex/sample.go`:
```go
package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_header_index(r *http.Request) {
	vals := r.Header["X-Test"]
	if len(vals) > 0 {
		Sink(vals[0])
	}
}

func Positive_header_get(r *http.Request) {
	Sink(r.Header.Get("X-Test"))
}

func Negative_const(r *http.Request) {
	_ = r
	Sink("safe")
}
```

- [ ] **Step 3: SourceFormParse sample**

`SourceFormParse/rule.yaml`:
```yaml
rules:
  - id: source-form-parse
    languages: [go]
    severity: WARNING
    message: "Taint from r.Form reaches Sink"
    mode: taint
    pattern-sources:
      - pattern: "$R.Form.Get($K)"
      - pattern: "$R.Form"
    pattern-sinks:
      - pattern: "util.Sink($X)"
```
`SourceFormParse/sample.go`:
```go
package util

import "net/http"

func Sink(s string) { _ = s }

func Positive_form_get(r *http.Request) {
	r.ParseForm()
	Sink(r.Form.Get("X-Test"))
}

func Positive_form_index(r *http.Request) {
	r.ParseForm()
	vals := r.Form["X-Test"]
	if len(vals) > 0 {
		Sink(vals[0])
	}
}

func Negative_const(r *http.Request) {
	_ = r
	Sink("safe")
}
```

- [ ] **Step 4: SourceBeegoCtxInput sample**

beego is an external dependency; the sample's `go.mod` must require it. To avoid network/module resolution complexity, model the beego Context.Input accessor with a LOCAL stand-in that has the same call shape (`c.Ctx.Input.Query(k)`), so the pattern-conversion of the `$X` accessor source is what's under test, not beego itself. `SourceBeegoCtxInput/rule.yaml`:
```yaml
rules:
  - id: source-beego-ctx-input
    languages: [go]
    severity: WARNING
    message: "Taint from Ctx.Input.Query reaches Sink"
    mode: taint
    pattern-sources:
      - pattern: "$X.Query($K)"
    pattern-sinks:
      - pattern: "util.Sink($X)"
```
`SourceBeegoCtxInput/sample.go`:
```go
package util

func Sink(s string) { _ = s }

type beegoInput struct{}

func (i *beegoInput) Query(k string) string { return "" }

type beegoContext struct{ Input *beegoInput }

type Controller struct{ Ctx *beegoContext }

func Positive_ctx_input(c *Controller) {
	Sink(c.Ctx.Input.Query("X-Test"))
}

func Negative_const(c *Controller) {
	_ = c
	Sink("safe")
}
```

- [ ] **Step 5: Register the 4 tests (disabled, since reproducing failures)**

In `GoSampleBasedTest.kt`, add near the other Go sample tests:
```kotlin
    @org.junit.jupiter.api.Disabled("Cluster A: r.URL.RawQuery source not matched — see fix proposal")
    @Test fun sourceUrlRawQuery() = runSample("SourceUrlRawQuery")

    @org.junit.jupiter.api.Disabled("Cluster A: r.Header map-index source not matched — see fix proposal")
    @Test fun sourceHeaderMapIndex() = runSample("SourceHeaderMapIndex")

    @org.junit.jupiter.api.Disabled("Cluster A: r.Form source not matched — see fix proposal")
    @Test fun sourceFormParse() = runSample("SourceFormParse")

    @org.junit.jupiter.api.Disabled("Cluster A: Ctx.Input.Query source not matched — see fix proposal")
    @Test fun sourceBeegoCtxInput() = runSample("SourceBeegoCtxInput")
```
(`Disabled` may already be imported; if so use the short form.)

- [ ] **Step 6: Confirm each reproduces (temporarily un-disable, run, see Positive fail)**

For each sample, temporarily remove its `@Disabled`, run, and confirm the `Positive_*` entry fails (`did not report any vulnerability`) — that is the reproduction. Negatives must pass. Then restore `@Disabled`.
```bash
./gradlew :opentaint-go-querylang:test --tests 'org.opentaint.semgrep.GoSampleBasedTest.sourceUrlRawQuery' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|did not report|reported vuln'
```
Expected: FAILED on the Positive entry (if it unexpectedly PASSES, the shape already works — record that and drop the sample from the FN set, noting it in the proposal doc). Repeat for the other three.

If a sample fails to BUILD (e.g. beego import, or the harness rejects a parameterized entrypoint), adjust per the spec fallbacks: for parameterized-entrypoint rejection use a package-level `var r *http.Request` read inside a no-arg `Positive_x`; the beego sample already uses a local stand-in. Record any such adjustment.

- [ ] **Step 7: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-go-querylang/samples-go/Source* \
  core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt
git commit -m "Cluster A: add 4 source-shape reproducing samples (disabled)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Cluster A diagnosis (GoSerializedItem first, then full facts)

**Files:**
- Create: `docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md` (start it; Cluster A sections)
- Possibly create a tiny throwaway test to dump the `GoSerializedItem` (see Step 1)

This task produces findings, not code. For EACH of the 4 Cluster A samples:

- [ ] **Step 1: Dump the produced GoSerializedItem**

The sample harness already converts via `GoSampleBasedTest.loadConfig(yamlFile)`:
```kotlin
val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
val rule = loader.loadRules().rulesWithMeta.first().first as TaintRuleFromSemgrep<GoSerializedItem>
return rule.toGoTaintConfiguration()   // current helper
```
Add a temporary test in `GoSampleBasedTest` (it has `samplesDir` + the imports) that does the same but inspects the SERIALIZED form via `toGoSerializedTaintConfig()` (the sibling of `toGoTaintConfiguration()`, both top-level extensions in `GoTaintRuleEmit.kt` — confirm the exact name there) and prints the serialized source rules (`GoNameMatcher`, `position`, `accessors`):
```kotlin
@Test fun dumpClusterASources() {
    for (name in listOf("SourceUrlRawQuery","SourceHeaderMapIndex","SourceFormParse","SourceBeegoCtxInput")) {
        val yamlFile = samplesDir.resolve(name).toFile()
            .listFiles { f -> f.extension == "yaml" }!!.single()
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        @Suppress("UNCHECKED_CAST")
        loader.loadRules().rulesWithMeta.forEach { (rule, _) ->
            val serialized = (rule as TaintRuleFromSemgrep<GoSerializedItem>).toGoSerializedTaintConfig()
            println("=== $name ===")
            println("source:      ${serialized.source}")
            println("passThrough: ${serialized.passThrough}")
        }
    }
}
```
Run it and capture the printed `GoSerializedItem` for each sample's source pattern:
```bash
./gradlew :opentaint-go-querylang:test --tests 'org.opentaint.semgrep.GoSampleBasedTest.dumpClusterASources' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -A3 '==='
```
If `toGoSerializedTaintConfig()` is not the exact name, find the serialized-config extension in `GoTaintRuleEmit.kt` (the spec references both `toGoSerializedTaintConfig()` and `toGoTaintConfiguration()`).

- [ ] **Step 2: Classify rule-translation vs engine, per the spec decision tree**

For each sample, decide:
- **Serialized source wrong/empty** for the shape (e.g. `$R.URL.RawQuery` did not produce a source rule at the field-read position/accessor, or `$R.Header` produced a whole-value source that can't match an element read) → **rule-translation issue**. Note the converter component (`GoLanguageStrategy` / `SemgrepGoPatternParser` / `GoTaintRuleEmit`).
- **Serialized source correct** but Positive still 0 → **engine matching/propagation issue**. Proceed to Step 3.

- [ ] **Step 3: Full fact dump for the engine-side cases**

For samples classified as engine-side, capture the full per-instruction facts for the `Positive_*` entry. The querylang harness doesn't expose `printFactsAt`; reuse the same engine query by adding a temporary diagnostic that runs `runAnalysis` and dumps `statementsWithFacts` (mirror `AnalysisTest.printFactsAt` against the querylang `program`/`config`/`entry`). Record where the source fact fails to appear or propagate (the field-read `x.Field` or map-index `x.Field[k]` instruction).

- [ ] **Step 4: Write the Cluster A sections of the proposal doc**

For each sample, write the four-part section (test case · description with the quoted `GoSerializedItem` + verdict + full fact dump · fix proposal labeled rule-translation|engine · post-fix behavior + FN recovery: 14/9/10/3). Commit the doc-in-progress:
```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md
git commit -m "Cluster A diagnosis + fix proposals (4 source shapes)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```
Remove any throwaway diagnostic test before committing (or keep it only if it's a clean, reusable dump helper — prefer removing).

---

## Task 3: Cluster C reproducing samples (3)

**Files:**
- Modify: `core/samples/src/main/go/closures.go` (add `closureCaptureReturn001T/002F` + the `makePrefixer`-style factory)
- Modify: `core/samples/src/main/go/struct_ops.go` (add `nestedStructConstructor001T/002F`)
- Modify: `core/samples/src/main/go/interface_dispatch.go` (add `interfaceLaundering001T/002F`)
- Create: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/ClusterCTest.kt`
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/EngineRoadmapDiagnosticTest.kt` (add 3 diag entries) — optional but recommended for the full-fact dump

- [ ] **Step 1: closureCaptureReturn sample**

Append to `core/samples/src/main/go/closures.go`:
```go
// ── Cluster C: factory returns a closure capturing tainted free var ──

func makeCapturingPrefixer(prefix string) func(string) string {
	return func(value string) string { return prefix + value }
}

func closureCaptureReturn001T() {
	data := util.Source()
	addPrefix := makeCapturingPrefixer(data)
	out := addPrefix("_suffix")
	util.Sink(out)
}

func closureCaptureReturn002F() {
	_ = util.Source()
	addPrefix := makeCapturingPrefixer("safe")
	out := addPrefix("_suffix")
	util.Sink(out)
}
```

- [ ] **Step 2: nestedStructConstructor sample**

Append to `core/samples/src/main/go/struct_ops.go`:
```go
// ── Cluster C: constructor builds a multi-level struct from tainted input ──

type CtorInner struct{ v string }
type CtorOuter struct{ inner CtorInner }

func NewCtorOuter(val string) CtorOuter {
	return CtorOuter{inner: CtorInner{v: val}}
}

func nestedStructConstructor001T() {
	data := util.Source()
	o := NewCtorOuter(data)
	util.Sink(o.inner.v)
}

func nestedStructConstructor002F() {
	data := util.Source()
	o := NewCtorOuter(data)
	_ = o
	util.Sink("safe")
}
```

- [ ] **Step 3: interfaceLaundering sample**

Append to `core/samples/src/main/go/interface_dispatch.go` (read the file first to reuse its existing interface/type naming style):
```go
// ── Cluster C: tainted value passed through an interface-typed method ──

type Launderer interface{ Transform(s string) string }

type identityLaunderer struct{}

func (identityLaunderer) Transform(s string) string { return s }

func interfaceLaundering001T() {
	data := util.Source()
	var l Launderer = identityLaunderer{}
	out := l.Transform(data)
	util.Sink(out)
}

func interfaceLaundering002F() {
	_ = util.Source()
	var l Launderer = identityLaunderer{}
	out := l.Transform("safe")
	util.Sink(out)
}
```

- [ ] **Step 4: Test class (disabled, reproducing)**

Create `core/src/test/kotlin/org/opentaint/go/sast/dataflow/ClusterCTest.kt`:
```kotlin
package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClusterCTest : AnalysisTest() {

    @Disabled("Cluster C: closure capture/higher-order not propagated — see fix proposal")
    @Test fun closureCaptureReturn001T() = assertReachable("test.closureCaptureReturn001T")
    @Test fun closureCaptureReturn002F() = assertNotReachable("test.closureCaptureReturn002F")

    @Disabled("Cluster C: nested-struct constructor return not propagated — see fix proposal")
    @Test fun nestedStructConstructor001T() = assertReachable("test.nestedStructConstructor001T")
    @Test fun nestedStructConstructor002F() = assertNotReachable("test.nestedStructConstructor002F")

    @Disabled("Cluster C: interface-method laundering not propagated — see fix proposal")
    @Test fun interfaceLaundering001T() = assertReachable("test.interfaceLaundering001T")
    @Test fun interfaceLaundering002F() = assertNotReachable("test.interfaceLaundering002F")
}
```

- [ ] **Step 5: Confirm each reproduces**

Temporarily un-disable each `001T`, run, confirm it FAILS ("Sink was not reached"); the `002F` must PASS.
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.ClusterCTest' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|Sink was'
```
Expected: each `001T` FAILS, each `002F` PASSES. If a `001T` unexpectedly PASSES (the shape already works), record it and drop from the FN set. Restore `@Disabled` on the `001T`s.

- [ ] **Step 6: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/samples/src/main/go/closures.go core/samples/src/main/go/struct_ops.go \
  core/samples/src/main/go/interface_dispatch.go \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/ClusterCTest.kt
git commit -m "Cluster C: add 3 dataflow reproducing samples (001T disabled)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: Cluster C diagnosis (full fact dump)

**Files:**
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/EngineRoadmapDiagnosticTest.kt` (add 3 `printFactsAt` entries; can be removed after capturing)
- Append: `docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md` (Cluster C sections)

- [ ] **Step 1: Capture the full fact dump for each 001T**

Add to `EngineRoadmapDiagnosticTest`:
```kotlin
    @Test fun diag_cC_closureCaptureReturn001T() = printFactsAt("test.closureCaptureReturn001T")
    @Test fun diag_cC_nestedStructConstructor001T() = printFactsAt("test.nestedStructConstructor001T")
    @Test fun diag_cC_interfaceLaundering001T() = printFactsAt("test.interfaceLaundering001T")
```
Run and read each dump:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EngineRoadmapDiagnosticTest.diag_cC_*' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
cat /tmp/go-engine-roadmap-facts/test_closureCaptureReturn001T.txt
cat /tmp/go-engine-roadmap-facts/test_nestedStructConstructor001T.txt
cat /tmp/go-engine-roadmap-facts/test_interfaceLaundering001T.txt
```

- [ ] **Step 2: Locate the death + responsible component, per sample**

From each full dump: record the source fact, intermediate carriers, last-tainted instruction, death point. Then inspect the responsible component:
- closure: `GoIRMakeClosureExpr` handling in `GoFlowFunctionUtils.exprToAccess` (it currently taints from `bindings.first()`) + the dynamic-call resolution for the returned closure in `GoCallResolver` / the call flow function. Determine whether the capture is lost at closure creation, at the factory return, or at the dynamic call.
- constructor: whether `NewCtorOuter` is summarized (return carries `result.inner.v`) — relate to Pattern 6 store-back and interproc return summaries.
- interface: whether `l.Transform(data)` resolves to `identityLaunderer.Transform` (devirtualization in `GoCallResolver`) and whether the arg→result flow applies.

- [ ] **Step 3: Write the Cluster C sections of the proposal doc**

Four-part section per sample (test case · description with full fact dump + responsible component file:line · fix proposal (engine; fact-generating) · post-fix behavior + FN recovery: ~41/4/3). Remove the temporary diag entries if they aren't worth keeping (the `EngineRoadmapDiagnosticTest` additions are cheap to keep — keep them, they're consistent with the existing diagnostic class). Commit:
```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/EngineRoadmapDiagnosticTest.kt
git commit -m "Cluster C diagnosis + fix proposals (3 dataflow shapes)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 5: Finalize the fix-proposal document

**Files:**
- Modify: `docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md`

- [ ] **Step 1: Add the summary + ranking**

Add a header (goal, link to triage + design spec, baseline) and a ranking table: each of the 7 samples → cluster, shape, root-cause kind (rule-translation | engine), responsible component, estimated FN recovery, risk. Order by FN recovery (closure ~41 first, then RawQuery 14, Form 10, Header 9, then 4/3/3).

- [ ] **Step 2: Consistency pass**

Verify every sample has all four parts, every `GoSerializedItem`/fact dump is the real captured output (not paraphrased), every "responsible component" cites a file:line, and the FN-recovery numbers sum consistently with the triage (35 for A, 58 for C). Note any sample that turned out to already work (dropped from the FN set) and any that split into multiple root causes.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md
git commit -m "Finalize Cluster A/C fix-proposal document

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Final review

Dispatch a review of the proposal doc + the 7 committed tests focused on: each test genuinely reproduces its FN (Positive/001T fails, Negative/002F passes); each diagnosis distinguishes rule-translation from engine (Cluster A) with the quoted `GoSerializedItem`; each fix proposal is concrete, fact-generating, and cites a real component; the doc is ready for the user to approve before implementation. Then stop and hand back to the user (implementation is a separate, post-approval round — do NOT proceed to finishing-a-development-branch).
