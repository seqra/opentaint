# Go FN-investigation pipeline — design

## Goal

Build a repeatable pipeline to investigate every false negative on the Go benchmarks: an analyzer entry-point selector, a fact-reachability SARIF export, and a batch script that runs the engine per-FN (one entry point, one rule) and collects where taint dies. Apply it to produce a complete root-cause-clustered triage of all current FNs. The next round of fixes is a separate follow-up; this spec delivers tooling + triage only.

## Background

After Patterns 1/2/5/6 (commit `ed791a59`), the benchmarks stand at go-sec-code-mutated 98.3% (178/181) and go-owasp-converted-mutated 24.3% (36/148). The remaining ~112 owasp + 3 sec FNs need per-sample root-cause analysis before the next fix round can be scoped. The seqra skills (`opentaint-issue-investigation`, `debug-rule-reachability`, `analyze-findings`) define the upstream Java pipeline for exactly this; the Go fork lacks the entry-point selector and the fact-reachability export those skills depend on.

## Architecture — three units + one output

### A. Entry-point selector (analyzer, production)

A new repeatable CLI flag selects which project functions are used as IFDS entry points, mirroring the Java `debug-run-on-entry-points "Class#method"` capability but keyed on Go function full names.

- **CLI flag:** `--entry-point <fullName>` (repeatable) on `AbstractAnalyzerRunner` (`core/src/main/kotlin/org/opentaint/jvm/sast/runner/AbstractAnalyzerRunner.kt`). Threaded through `ProjectAnalyzerRunner.analyzeGoProject` into a new field on the common analysis options.
- **Options:** add `entryPointFilter: List<String> = emptyList()` to the common options struct consumed by `GoProjectAnalysisOptions` (the same `options.common` object that already carries `ifdsAnalysisTimeout`, `trackExternalMethods`, etc.).
- **Filter:** `GoProjectAnalyzer.selectEntryPoints(cp)` (`core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt`) gains a final filter step. Current body:
  ```kotlin
  cp.packages.values
      .filter { it.isProject }
      .flatMap { it.functions }
      .filter { it.hasBody && !it.isSynthetic && it.parent == null }
  ```
  When `options.common.entryPointFilter` is non-empty, append `.filter { it.fullName in filterSet }`. Empty filter = today's behavior (all project entry points).
- **Diagnostics:** after filtering, log at INFO each requested name in the filter that matched zero functions, e.g. `"Entry-point filter: no project function named '<name>'"`. A typo or wrong-format name is then visible in the log rather than silently producing an empty run.

**Full-name format** is whatever `GoIRFunction.fullName` produces — for a free function `<importPath>.<Func>`, for a method `(*<importPath>.<Type>).<Method>` or `(<importPath>.<Type>).<Method>`. The exact module-path prefix is determined empirically during implementation by dumping `selectEntryPoints` names once on a benchmark model (see Testing). The batch script (unit C) derives names to match this exact format.

### B. Fact-reachability SARIF export (analyzer, production)

Ports the JVM `--debug-fact-reachability-sarif` capability to the Go analyzer using the existing non-instrumenting engine query.

- **Query:** add `GoTaintAnalyzer.statementsWithFacts(): Map<CommonInst, Set<FinalFactAp>>` (`core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt`), mirroring `JIRTaintAnalyzer.statementsWithFacts()` (`core/opentaint-jvm-sast-dataflow/.../JIRTaintAnalyzer.kt:262-276`): iterate `ifdsEngine.allUnits()`, `findUnitRunner(unit)`, `collectAllIntraProceduralFacts(map)`, then flatten the per-entry-point maps into one `inst → facts` map. This is the exact query path the test-side `AnalysisTest.printFactsAt` already validated. Confirm the engine member name in `GoTaintAnalyzer` (the analyzer holds the `TaintAnalysisUnitRunnerManager`; reuse it).
- **Generator:** new `GoDebugFactReachabilitySarifGenerator` (`core/src/main/kotlin/org/opentaint/go/sast/sarif/`), modelled on `DebugFactReachabilitySarifGenerator.kt:16-74`. One SARIF result per `(statement, fact)`; ruleId `s_<index>`; message = `fact.toString()`; location = `GoInstLocation.position` (file + line) resolved against the project source root, consistent with `GoSarifGenerator`.
- **Wiring:** the flag `--debug-fact-reachability-sarif` already exists on `AbstractAnalyzerRunner` and feeds `DebugOptions.factReachabilitySarif`. Thread `debugOptions` into `GoProjectAnalysisOptions`; in `GoProjectAnalyzer.analyze`, when the flag is set, after `analyzer.analyzeWithIfds(...)` call `analyzer.statementsWithFacts()` and write `debug-ifds-fact-reachability.sarif` into `resultDir` via the generator. Mirror `ProjectAnalyzer.kt:146-149` and `:213-223`. The filename matches the Java output so the `debug-rule-reachability` skill applies unchanged.

### C. Benchmark FN-investigation batch script (`benchmarks/`, investigation)

`benchmarks/fn_investigate.py` — drives A+B over the FN set of a benchmark and emits a machine-readable triage.

Per-run data flow:
```
compare.py(report.sarif, truth.sarif)  →  per-CWE FN file URIs
for each FN file:
  1. scan .go source → entry-point fullName(s)
       - method `func (b *T) ServeHTTP(w http.ResponseWriter, r *http.Request)` → (*<importPath>.T).ServeHTTP
       - top-level `func Name(w http.ResponseWriter, r *http.Request)`          → <importPath>.Name
       - beego method `func (c *T) Get()` / `Post()` / ...                       → (*<importPath>.T).Get
  2. CWE → single rule id:
       CWE-22 → go.security.go-path-traversal
       CWE-78 → go.security.go-command-injection
       CWE-79 → go.security.go-reflected-xss
       CWE-89 → go.security.go-sql-injection
  3. opentaint --experimental scan --project-model <bench>/.opentaint/project
        --entry-point <fullName> --rule-id <cwe-rule>
        --debug-fact-reachability-sarif --track-external-methods
        --analyzer-jar <…> --autobuilder-jar <…> --ruleset <bench>/rules
        -o <bench>/.opentaint/fn-runs/<sample>/report.sarif
  4. parse debug-ifds-fact-reachability.sarif + external-methods-without-rules.yaml →
       { file, cwe, entryPoint, sourceMatched, lastTaintedInstr, deathInstr,
         externalsOnPath[], finding }
→ fn-triage.jsonl  (one row per FN)
```

- **`--rule-id` to single rule:** the script passes one rule id so the fact-reachability SARIF stays small (the `debug-rule-reachability` skill's "single rule only" constraint). Implementation must confirm `--rule-id` threads to the Go semgrep-rule loader; if it doesn't filter the Go rules today, that wiring is a small addition folded into unit A's runner work.
- **`GOIR_SERVER_BINARY`** is exported by the script (as `scan.sh` does) so the analyzer finds the Go SSA server.
- **Signal extraction:** `sourceMatched` = at least one fact at the entry-point's source instruction; `deathInstr` = first instruction on the expected path with no fact after the last instruction that had one; `externalsOnPath` = intersection of `external-methods-without-rules.yaml` method names with the function/call names appearing in the fact-reachability trace.

### Investigation output (me, from `fn-triage.jsonl`)

Cluster FNs by root cause and write a Markdown triage report alongside the JSONL. Taxonomy — each FN gets exactly one primary category:

| Category | Mechanical signal | Fix lane (next round) |
|---|---|---|
| `missing-source` | `sourceMatched == false` | rule `pattern-sources` |
| `missing-sink` | source matched, taint reaches the sink instr but `finding == false` | rule `pattern-sinks` |
| `missing-propagator` | `externalsOnPath` non-empty | YAML passThrough / loader |
| `engine-fn` | source matched, no external on path, taint dies at a rule-irrelevant instruction | new engine pattern (like 1/2/5/6) |
| `unsupported-construct` | death at a known-hard IR shape (closure / dynamic dispatch / goroutine / interface method) | deferred patterns 7/9/10 or new |
| `not-reachable` | taint genuinely killed in-source (mutation neutralizes it) → mislabeled truth | none — note and exclude from the actionable denominator |

The `engine-fn` cluster is sub-grouped by the death-instruction IR kind so recurring gaps surface as candidate patterns. Report contents: per-sample table (file · cwe · entryPoint · category · death point) + clustered summary (category → count, with one representative sample and its trace per cluster). The clusters are handed to a follow-up brainstorm for the next fix round; no fixes are implemented in this spec.

## Error handling

- **Unrecognized handler signature** (scanner can't derive an entry-point name) → script records `skip:no-entrypoint` for that FN and continues; the residual skip set is listed in the report for manual inspection.
- **Analyzer exception on one FN run** → recorded as `error:analyzer` row with the exit code; batch continues to the next FN.
- **Entry-point name not found by the analyzer** (scanner produced a name that doesn't match `fullName`) → the analyzer logs the zero-match (unit A) and produces an empty run; the script detects the empty fact-reachability SARIF and records `skip:entrypoint-unmatched`, distinct from `skip:no-entrypoint`, so name-format mismatches are separable from signature-scan misses.

## Testing

- **A (entry-point filter):** a `GoProjectAnalyzer`/runner-level test that, given a filter naming exactly one known project function (a `samples-go` function or a benchmark fixture), analyzes only that function's entry point; and that an unknown name logs the zero-match and yields no entry points. First, dump `selectEntryPoints` names on a benchmark model to lock the exact `fullName` format the test and the script must use.
- **B (SARIF port):** a test that `statementsWithFacts()` is non-empty for a known-tainted sample and that `GoDebugFactReachabilitySarifGenerator` emits one result per fact; plus a CLI smoke test that `--debug-fact-reachability-sarif` on one benchmark FN writes `debug-ifds-fact-reachability.sarif`.
- **C (script):** run `fn_investigate.py` on a 3-FN slice (one expected `missing-propagator`, one `engine-fn`, one source-matched) and assert the `fn-triage.jsonl` rows carry the expected categories and a non-empty death point. Not a full-suite gate.

## Out of scope

- Implementing the next-round fixes the triage surfaces (separate brainstorm).
- Parallelizing the batch script (one analyzer invocation per FN is acceptable; optimize only if wall-clock becomes a blocker).
- Any change to the four shipped patterns or the benchmark rules.
