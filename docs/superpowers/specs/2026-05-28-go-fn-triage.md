# Go benchmark FN triage (2026-05-28)

Root-cause triage of every remaining false negative on the Go benchmarks, produced by the FN-investigation pipeline (`--entry-point` selection + `--debug-fact-reachability-sarif` + `benchmarks/fn_investigate.py`). Authoritative per-sample data: `benchmarks/fn-triage.jsonl` (115 rows). This document clusters those rows and ranks the next fix round. No fixes are implemented here.

Baseline at triage time (commit `ed791a59`): go-sec-code-mutated 98.3% (178/181), go-owasp-converted-mutated 24.3% (36/148).

## Method

For each FN (truth-fail URI absent from the report, per CWE) the driver runs the analyzer scoped to that file's handler entry point(s) and the single matching CWE rule, with per-statement fact reachability. It records: was a taint fact produced and attributed to the FN's own file (`sourceMatched`); did the scoped run emit a finding (`finding` — always false here, confirming the FNs reproduce in isolation); the last instruction still carrying taint (`lastTaintedInstr`); and any external method on the path lacking a propagator (`externalsOnPath`). Handler detection tries every `(http.ResponseWriter, *http.Request)` method (Get/Post/DoGet/DoPost/… not just ServeHTTP, non-ServeHTTP first since ServeHTTP is often a stub) plus beego no-arg controller methods.

**Caveat:** IFDS fact-death does not map cleanly to a single source line, and many flows cross into helper functions (`doSomething`, `NewNestedFields*`). The `engine-fn` sub-clustering below is therefore approximate — the robust signals are (a) `sourceMatched` true/false, (b) the exact `externalsOnPath` methods, and (c) the source-read API for the unmatched set. Per-sample death points are in the JSONL for follow-up.

## Coverage

115 FNs analyzed (112 owasp + 3 sec). All 115 ran; none errored.

| | count | meaning |
|---|---|---|
| reproduced (`sourceMatched=true`, no finding) | 80 | taint enters the handler, dies before the sink — the actual FN |
| `skip:entrypoint-unmatched` | 35 | no taint fact produced at any handler — the source read never becomes a fact |

Per-CWE: CWE-22 17 reproduced / 7 unmatched · CWE-78 13 / 8 · CWE-79 31 / 8 · CWE-89 19 / 12.

## Clusters (ranked by size × tractability)

### Cluster A — source not matched (35) — **largest, likely rule/querylang, high ROI**

These 35 produce no taint fact at all, yet their source-read APIs are already listed in every CWE rule's `pattern-sources`. So this is **not** a missing-source rule gap — it is a source-pattern *matching* gap: the semgrep→Go pattern conversion does not match these source shapes against the IR.

Source-read API in the unmatched handlers (a handler may use several):

| API in handler | count | rule has the pattern? | likely issue |
|---|---|---|---|
| `r.URL.RawQuery` | 14 | yes (`$R.URL.RawQuery`) | field-read of a string field not matched as a source |
| `r.Header[k]` / `r.Header` | 9 | yes (`$R.Header`, `.Get`, `.Values`) | whole-map source taints `r.Header` but the `r.Header["k"]` index read doesn't propagate the element (same map-element gap family as Pattern 2) |
| `r.ParseForm()` + `r.Form` | 8 | yes (`$R.Form`, `$C.ParseForm`) | `ParseForm` populates `r.Form`/`r.PostForm`; the subsequent form read isn't matched/propagated |
| `c.Ctx.Input...` (beego) | 3 | partial (`$C.Input()`) | beego `Ctx.Input.*` accessor shape not matched |
| `r.Cookie(k)` (in 2nd method) | 2 | yes (`$R.Cookie`) | source is in a non-ServeHTTP method; fact still not produced |
| `r.Form` direct | 2 | yes | as above |

Confirmed example (`benchmarkTest02034ijzke`): source is `r.Header["BenchmarkTest02034"]` — a map-index read on `r.Header`. The rule's `$R.Header` should taint the whole header map and the `[...]` read should yield the element, but no fact appears. This is the same whole-container→element propagation family as Pattern 2 (container/list), now for `http.Header` (a `map[string][]string`) and for `r.URL.RawQuery`/`r.Form` field reads.

**Next-round lane:** investigate the source-pattern→IR matching for field-read sources (`r.URL.RawQuery`) and map/Header element reads. Likely one or two matching/propagation fixes unlock a large fraction of 35. Highest leverage in the triage.

### Cluster B — missing library propagator (22) — **config, low risk**

`externalsOnPath` (method on the taint path with no propagator model), by frequency:

| method | count | note |
|---|---|---|
| `strings.Contains` | 6 | predicate; taint shouldn't die here — appears on path but likely not the killer (cleaner-style); verify before modelling |
| `len` | 5 | builtin; `len(tainted)` returns int — not a propagator (taint legitimately ends); likely noise |
| `os/exec.Command` | 4 | this is the **sink** for cmdinj; appearing here means the arg fact reached it but the sink/variant didn't fire — check sink pattern, not a propagator |
| `append` | 3 | `append(slice, tainted)` must propagate to the slice — genuine propagator candidate |
| `(net/http.ResponseWriter).Write` | 3 | XSS sink — same as exec.Command: arg reached, sink-match question |
| `(*container/list.List).Len` | 2 | container/list — Pattern 2 family (Len returns int; the element read is the real issue) |

**Reading:** only `append` is a clear missing-propagator. `strings.Contains`/`len`/`list.Len` return non-string scalars (taint legitimately stops). `os/exec.Command` and `ResponseWriter.Write` are **sinks** — their presence in `externalsOnPath` means the tainted value *reached the sink argument* but no finding was emitted, pointing at a **sink-matching gap** for specific call shapes, not a propagator gap. So Cluster B really splits into: `append` propagator (3) + a **sink-not-matched** sub-cluster (≈7: exec.Command, ResponseWriter.Write variants) worth its own look.

### Cluster C — engine FN, taint dies internally (58) — approximate sub-clustering

Among the 80 reproduced, the 58 without an external on the path. Death context (approximate — see caveat):

| sub-cluster | ~count | example | maps to |
|---|---|---|---|
| interprocedural helper flow (`doSomething(r,param)`, `NewNestedFields*`) | ~34 | `bar := doSomething(r, param)` then taint lost across the call | interproc summary / helper-return propagation |
| closures returned/called | 8 | `stringRet()`, `return func(...)` | deferred Pattern 9/10 (closures, higher-order) |
| `fmt.Sprintf`-adjacent | 6 | `fmt.Sprintf("ls %s", dir)` — but the real death is usually interface laundering just upstream | verify; likely interface-dispatch, not Sprintf |
| map/slice range | 5 | `for _, v := range r.URL.Query()` | range-iteration propagation (known `@Disabled` mapIter family) |
| pointer/heap via helper | 3 | `new(Test).doSomething(...)` | interproc + receiver |
| type-switch | 1 | `switch i.(type)` | Pattern 5 family (mostly fixed; residual) |

The dominant real sub-cluster is **interprocedural helper-return flow** (~34): the benchmark mutations wrap the tainted value in a call to a local helper (`doSomething`, `NewNestedFields2FromArray`, interface-laundering classes) and the taint is lost across that call. This is the same shape as the still-`@Disabled` `closureReturn`/`higherOrder` and the nested-struct families, plus genuine interprocedural-summary gaps for value-returning helpers.

## Next-round candidates (for a follow-up brainstorm)

Ranked by expected TP recovery × tractability:

1. **Cluster A — source-shape matching (35).** Investigate why `r.URL.RawQuery` (field read), `r.Header[k]` (map-element on a tainted map), and `r.Form`/`ParseForm` sources don't produce facts despite being in the rules. Largest single bucket; likely a small number of querylang/propagation fixes. Start here.
2. **Cluster C interproc-helper (~34).** The `doSomething`-style value-returning local helpers losing taint across the call. Build a focused sample set (mirror the FN shapes) and treat as the next engine pattern(s).
3. **Sink-not-matched sub-cluster (~7).** `os/exec.Command` / `ResponseWriter.Write` call shapes where the tainted arg reaches the sink but no finding fires — verify sink patterns.
4. **`append` propagator (3)** and **range-iteration (5)** — smaller, mostly known families.

Each becomes its own spec → plan → implementation cycle, gated by new regression samples mirroring the FN shapes and re-running this triage to measure movement.

## Residual / tooling notes

- The 35 `unmatched` are a *signal*, not a tooling failure: handler detection now tries all `(w,r)` methods + beego forms, and the source read is confirmed present in-handler — the engine simply produces no fact. (Before broadening handler detection, 39 FNs were mis-skipped; that tooling gap is fixed.)
- `finding=false` on all 80 reproduced confirms the scoped single-entry single-rule runs faithfully reproduce each FN.
- Re-run after any next-round fix: `python3 benchmarks/fn_investigate.py <bench>` then re-cluster `fn-triage.jsonl`.
