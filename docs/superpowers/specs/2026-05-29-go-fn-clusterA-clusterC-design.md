# Go FN clusters A & C — reproduce + diagnose + propose fixes

## Goal

Turn the two largest benchmark FN clusters from the triage (`docs/superpowers/specs/2026-05-28-go-fn-triage.md`) into a concrete, reviewable fix proposal. This round delivers: (1) committed reproducing tests — Cluster A in `opentaint-go-querylang`, Cluster C in `core/src/test` — left `@Disabled`/known-failing; (2) a diagnosis + fix-proposal document in the format `test case → description → fix proposal → post-fix behavior`. **No fixes are implemented this round.** The user reviews the proposals; implementation is a separate subagent-driven round, exactly as Patterns 1/2/5/6 were.

## Background

From the FN triage (115 FNs, baseline go-owasp 24.3% / go-sec 98.3%):

- **Cluster A — source-shape matching (35 FNs).** Source-read APIs that ARE in the rules' `pattern-sources` (`r.URL.RawQuery`, `r.Header[k]`, `r.Form`/`ParseForm`, `c.Ctx.Input`) produce no taint fact. Not a missing-source rule gap — a semgrep→Go source-pattern *matching* gap. This is a query-language/pattern-conversion problem, so its tests belong in `opentaint-go-querylang`.
- **Cluster C — dataflow engine FNs (58 FNs).** Taint enters the handler and dies internally. Re-classifying the triage's coarse "local-helper-return" bucket against the real sources shows it is dominated by **closure / higher-order** flows (the `makePrefixer(param)` factory-returns-closure shape — the deferred Patterns 9/10), plus nested-struct construction and interface-method laundering. These are engine dataflow problems, so their tests belong in `core/src/test` + `core/samples`.

## Sampling strategy

Sample by distinct root-cause shape, not per-FN (69 FNs → 7 canonical reproductions), each mapped to its FN count so fix priority is explicit.

### Cluster A samples — `core/opentaint-go-querylang/samples-go/<Name>/`

Infra: each sample dir has `go.mod`, one `rule.yaml` (mode: taint), and `*.go` with top-level `Positive_*` (expect ≥1 finding) / `Negative_*` (expect 0). Source introduced via the real HTTP shape; sink via a local `Sink`. Each rule's `pattern-sources` uses the actual benchmark source pattern under test; `pattern-sinks` = `Sink($X)`.

| Sample | Source shape under test | Pattern in rules | FNs |
|---|---|---|---|
| `SourceUrlRawQuery` | `s := r.URL.RawQuery` (string field read) | `$R.URL.RawQuery` | 14 |
| `SourceHeaderMapIndex` | `v := r.Header["K"]` then `v[0]` (index on tainted map field) | `$R.Header` / `$R.Header.Get($K)` | 9 |
| `SourceFormParse` | `r.ParseForm()`; `v := r.Form.Get("K")` and `r.Form["K"]` | `$R.Form`, `$R.Form.Get($K)`, `$C.ParseForm($PTR)` | 10 |
| `SourceBeegoCtxInput` | `c.Ctx.Input.Query("K")` / `c.Ctx.Input.*` | `$C.Input()` / beego `$X` accessors | 3 |

Entrypoint shape: prefer a top-level `func Positive_x(r *http.Request)` (the source pattern fires on the field-read expression irrespective of whether `r` is itself tainted). If the sample harness rejects parameterized entrypoints, fall back to a package-level `var r *http.Request` read inside a no-arg `Positive_x`. The first diagnosis step confirms which the harness accepts and the spec's implementation plan will pin it.

Each sample carries a `Negative_*` reading a constant/clean value through the same shape, to guard against an over-broad fix.

### Cluster C samples — `core/samples/src/main/go/` + paired tests in `core/src/test/kotlin/org/opentaint/go/sast/dataflow/`

Infra: `AnalysisTest` convention — `001T` (reach), `002F` (no-reach), `util.Source()/util.Sink()`. Diagnosis via the existing `printFactsAt`.

| Sample | Shape under test | FNs | Existing analog |
|---|---|---|---|
| `closureCaptureReturn001T/002F` | factory returns a closure capturing tainted free var; closure called later: `f := makePrefixer(data); out := f("x")` | ~41 | extends `ClosureTest.closureReturn`/`higherOrder` (`@Disabled`) |
| `nestedStructConstructor001T/002F` | helper/constructor builds a multi-level struct from tainted input and a field is read back: `o := NewBox(data); Sink(o.inner.v)` | 4 | extends Pattern 6 store-back + `nestedStructMod` |
| `interfaceLaundering001T/002F` | tainted value passed through an interface-typed method call: `var i I = impl{}; out := i.Transform(data)` | 3 | extends `InterfaceDispatchTest` |

sync/atomic (Pattern 3, passing), container/list (Pattern 2, fixed), range-iteration (`mapIter` `@Disabled`), plain type-switch (Pattern 5, fixed) are referenced, not re-sampled.

## Diagnosis method (per sample, during this round)

For every sample we record the engine's actual behavior and pinpoint the responsible component before proposing a fix. Two cross-cutting rules apply to all diagnosis:

- **Always dump the FULL fact set, not just the death point.** Use the complete per-instruction fact reachability (the `printFactsAt` / `--debug-fact-reachability-sarif` dump that walks every instruction, showing `∅` where a fact is absent), not only the last-tainted/first-missing pair. The death point is read off the full dump, but the surrounding facts (what survives, what the source produced, what intermediate temporaries carry) are needed to attribute the cause correctly — a fact dying at instruction N is often explained by what happened at N−3.
- **For rule-driven samples, inspect the produced `GoSerializedItem` BEFORE blaming the engine.** A `Positive_*` reporting 0 has two distinct causes that must be separated: (a) the semgrep→Go conversion produced a wrong/empty `GoSerializedItem` (rule-translation bug — fix in the converter/emit), or (b) the `GoSerializedItem` correctly represents the source but the engine doesn't match/propagate it (engine bug). Never propose an engine fix for what is actually a translation bug.

- **Cluster A:** First, run the rule through the conversion and inspect the resulting `GoSerializedItem` / `GoSerializedTaintConfig` (via `toGoSerializedTaintConfig()` / `toGoTaintConfiguration()` — the same path `GoRuleEmit`/`GoSampleBasedTest` use). Record what serialized source rule the pattern produced (its `GoNameMatcher`, position, accessors). Decide rule-translation vs engine:
  - If the `GoSerializedItem` is wrong or missing for the source shape (e.g. a field-read `$R.URL.RawQuery` doesn't translate to a serialized source at the right position/accessor) → **rule-translation issue**; inspect `GoLanguageStrategy`, the pattern parser (`SemgrepGoPatternParser`), and the emit (`GoTaintRuleEmit`/`GoStrategyAutomata`).
  - If the `GoSerializedItem` is correct but the `Positive_*` still reports 0 → **engine matching/propagation issue**; then take the full fact dump and locate where the source fact fails to be produced or propagated against the Go IR (field-read `x.Field`, map-index `x.Field[k]`).
- **Cluster C:** run `printFactsAt` on the `001T` entry point and read the FULL dump; record the source fact, every intermediate carrier, the last-tainted instruction and the death point. Inspect the responsible flow-function arm in `GoMethodSequentFlowFunction` / `GoMethodSequentPrecondition`, the call resolution in `GoCallResolver`, and (for closures) `GoIRMakeClosureExpr` handling + the dynamic-call summary path.

## Deliverable document format

`docs/superpowers/specs/2026-05-29-go-fn-clusterAC-fixproposals.md`, one section per sample:

1. **Test case** — the sample code + the test that reproduces the FN (file paths, function names).
2. **Description** — for Cluster A: the produced `GoSerializedItem` (quoted) and the rule-translation-vs-engine verdict; for both clusters: the verbatim FULL fact-reachability dump (all instructions, `∅` included) showing where the fact is missing, and the responsible component (file:line).
3. **Fix proposal** — the concrete change (which converter/emit, flow-arm, or resolver; what mechanism — fact-generating per the `FactTypeChecker` invariant). Sized and risk-rated. Explicitly labeled rule-translation fix vs engine fix.
4. **Post-fix behavior** — the expected full trace/finding after the fix; which `@Disabled` tests flip green; estimated FN recovery for that shape.

## Out of scope

- Implementing any fix (separate round after review).
- The smaller Cluster B (`append` propagator, sink-not-matched) and the residual triage buckets — addressed in a later round.
- Re-sampling shapes already fixed (Patterns 2/3/5) or already `@Disabled` with a known cause unless a Cluster A/C sample naturally subsumes them.

## Success criteria for this round

- 4 Cluster A + 3 Cluster C reproducing tests committed and confirmed failing (the FN reproduces in isolation).
- Each of the 7 samples has a diagnosed root cause naming the responsible engine component with a fact trace.
- The fix-proposal document covers all 7 in the required four-part format, ranked by FN recovery, ready for the user to approve before implementation.
