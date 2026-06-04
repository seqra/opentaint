export const meta = {
  name: 'go-engine-improvement-round',
  description: 'One benchmark-driven FN-fixing round on the Go taint engine: triage FNs per entry point, cluster into issues, repro+test+classify each, apply simple fixes (new rule / new approximation) or write an investigation report for hard ones, then synthesize a ranked round report with the recommended next fix.',
  whenToUse: 'Improving Go taint-engine recall on the go-sec-code / go-owasp benchmarks. Run one round, review the report and integrate the simple fixes, then re-invoke for the next round until only hard issues remain.',
  phases: [
    { title: 'Triage', detail: 'scan + compare (TP/FP) + per-entrypoint fn_investigate; categorize every FN' },
    { title: 'Cluster', detail: 'dedupe FNs into distinct issues so one agent handles one issue' },
    { title: 'Resolve', detail: 'per-issue worktree agent: minimal repro + route test + querylang/engine classify + apply-simple-fix-or-report' },
    { title: 'Synthesize', detail: 'round report: TP/FP, fixes applied, hard issues ranked by complexity, recommended next fix, stop-check' },
  ],
}

const REPO = '/drive-testcomp/opentaint-go-rules/opentaint'
const BENCHDIR = '/drive-testcomp/opentaint-go-rules/benchmarks'
const SERVER = REPO + '/core/opentaint-ir/go/go-ssa-server/go-ssa-server'
const PATHS = 'PATH=/home/sobol/local/bin:/usr/local/go/bin:$PATH PYTHON=python3.10'

const cfg = typeof args === 'string' ? (() => { try { return JSON.parse(args) } catch (e) { return {} } })() : (args || {})
const BENCH = cfg.bench || 'go-owasp-converted-mutated'
const LIMIT = cfg.limit || 8
const APPLY = cfg.applySimpleFixes !== false
const REUSE = !!cfg.reuseTriage
const REBENCH = !!cfg.rebenchAfterFix

const TRIAGE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['tpfpTable', 'totalFns', 'noRuleCwes', 'clusters'],
  properties: {
    tpfpTable: { type: 'string', description: 'verbatim compare.py per-CWE TP/FP/TP% table' },
    totalFns: { type: 'number', description: 'total covered-CWE FN rows triaged' },
    noRuleCwes: { type: 'array', items: { type: 'string' }, description: 'truth CWEs with no rule loaded' },
    clusters: {
      type: 'array',
      description: 'FNs already DEDUPED into distinct issues (one per root-cause signature). Keep this list to the distinct issues only (typically <=40) — do NOT emit one entry per FN file.',
      items: {
        type: 'object',
        additionalProperties: false,
        required: ['key', 'cwe', 'reason', 'count', 'representativeFile'],
        properties: {
          key: { type: 'string', description: 'stable cluster key, e.g. approx::strings.Index or prop::CWE-79::<deathShape>' },
          cwe: { type: 'string' },
          reason: { type: 'string', enum: ['source-not-matched', 'missing-approximation', 'propagation-failure'] },
          count: { type: 'number', description: 'number of FN files in this cluster' },
          representativeFile: { type: 'string' },
          topExternal: { type: 'string' },
          sourceApi: { type: 'string' },
          deathLine: { type: 'string' },
          entryPoint: { type: 'string' },
        },
      },
    },
  },
}

const RESOLVE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['key', 'route', 'classification', 'testPath', 'testPasses', 'isSimpleFix', 'applied', 'complexity', 'summary'],
  properties: {
    key: { type: 'string' },
    route: { type: 'string', enum: ['no-relevant-rule', 'missing-approximation', 'propagation-failure'] },
    classification: { type: 'string', enum: ['querylang', 'engine', 'approximation', 'rule-only', 'unresolved'] },
    testPath: { type: 'string' },
    testPasses: { type: 'boolean' },
    isSimpleFix: { type: 'boolean' },
    applied: { type: 'boolean' },
    reportPath: { type: 'string' },
    complexity: { type: 'string', enum: ['trivial', 'small', 'medium', 'large', 'pipeline-wide'] },
    javaAnalog: { type: 'boolean' },
    fixProposal: { type: 'string' },
    deathPointOrExternal: { type: 'string' },
    worktree: { type: 'string' },
    summary: { type: 'string' },
  },
}

const ROUND_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['summary', 'recommendedNextFix', 'stop'],
  properties: {
    summary: { type: 'string' },
    recommendedNextFix: { type: 'string' },
    stop: { type: 'boolean' },
  },
}

phase('Triage')
const reuseClause = REUSE
  ? "Reuse the existing triage: read '" + BENCHDIR + "/fn-triage.jsonl' (already produced for " + BENCH + "). Do NOT re-run fn_investigate.py."
  : "Run the per-entrypoint triage: 'cd " + BENCHDIR + " && GOIR_SERVER_BINARY=" + SERVER + " python3 fn_investigate.py " + BENCH + "' (single-entrypoint + single-rule + fact-reachability + external-methods; writes " + BENCHDIR + "/fn-triage.jsonl). May take 30-60 min."

const triagePrompt = [
  "You are the TRIAGE step of a Go taint-engine benchmark round. Read-only except for running the benchmark tooling. Bench: '" + BENCH + "' under '" + BENCHDIR + "/" + BENCH + "'.",
  "",
  "1. Current accuracy: 'cd " + BENCHDIR + " && ./compare.py " + BENCH + "/.opentaint/results/report.sarif " + BENCH + "/truth.sarif' and capture the per-CWE TP/FP/TP% table verbatim. If report.sarif is missing/stale, first run '" + PATHS + " ./scan.sh owasp' (for a go-owasp bench) then compare. CWE-22/78/79/89 are the only covered CWEs; the rest are no-relevant-rule.",
  "2. " + reuseClause,
  "3. Categorize every FN row from fn-triage.jsonl into exactly one reason (run this in Python, do not eyeball):",
  "   - 'source-not-matched' when status == 'skip:entrypoint-unmatched' (source read produced no taint fact).",
  "   - else 'missing-approximation' when externalsOnPath has a real propagator candidate: a method NOT in NOISE={len,cap,strings.Contains,strings.HasPrefix,strings.HasSuffix,strings.EqualFold,strings.Count,utf8.RuneCountInString} and NOT a known sink {os/exec.Command,(net/http.ResponseWriter).Write,os.Open,os.OpenFile,database/sql,http.ServeFile,net/http.ServeFile}; report it as topExternal.",
  "   - else 'propagation-failure' (sourceMatched true, taint dies internally).",
  "   Also capture per FN: cwe, sourceMatched, deathLine (lastTaintedInstr/deathInstr note), and the handler source-read API (sourceApi) when cheap to grep.",
  "4. DEDUPE the FNs into distinct issue CLUSTERS by root-cause signature (do this in Python; do NOT return one entry per FN file — that is too large). Cluster key: missing-approximation -> 'approx::<topExternal>'; source-not-matched -> 'source::<cwe>::<sourceApi>'; propagation-failure -> 'prop::<cwe>::<deathShape>' where deathShape is the deathLine or sourceApi. For each cluster emit one object: {key, cwe, reason, count (number of FN files), representativeFile (one member path), topExternal, sourceApi, deathLine}. Sort clusters by count descending. Typically <=40 clusters — keep it to the distinct issues, not the raw rows.",
  "5. List truth CWEs with NO rule loaded (noRuleCwes) by diffing " + BENCH + "/truth.sarif ruleIds against " + BENCHDIR + "/rules.",
  "",
  "Return the structured triage: tpfpTable, totalFns (raw FN row count), noRuleCwes, and clusters (the DEDUPED list, NOT raw fns). Your final message is the tool result.",
].join("\n")

const triage = await agent(triagePrompt, { schema: TRIAGE_SCHEMA, phase: 'Triage' })

log("Triage: " + triage.totalFns + " covered-CWE FNs; no-rule CWEs: " + (triage.noRuleCwes.join(', ') || 'none'))
log("TP/FP:\n" + triage.tpfpTable)

phase('Cluster')
const allClusters = (triage.clusters || []).map(c => ({
  key: c.key,
  reason: c.reason,
  cwe: c.cwe,
  members: new Array(Math.max(1, c.count || 1)).fill(c.representativeFile || ''),
  sample: { file: c.representativeFile, cwe: c.cwe, topExternal: c.topExternal, sourceApi: c.sourceApi, deathLine: c.deathLine },
})).sort((a, b) => b.members.length - a.members.length)
const issues = allClusters.slice(0, LIMIT)
log("Triage returned " + allClusters.length + " issue clusters; processing top " + issues.length + " (limit " + LIMIT + ").")

phase('Resolve')
const ROUTE_GUIDE = [
  "Go test conventions (follow exactly; NO comments in production Kotlin/Go source):",
  "- RULE test (routes no-relevant-rule / propagation-failure): create 'core/opentaint-go-querylang/samples-go/<Name>/' with go.mod (module util), one <rule>.yaml (mode: taint; pattern-sources/pattern-sinks mirroring " + BENCHDIR + "/rules/go/security/<cwe>.yaml), and <fixture>.go (package util; Positive_* must report, Negative_* must not). Add one line: @Test fun <name>() = runSample(\"<Name>\") in core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt. Run: (cd core && " + PATHS + " ./gradlew :opentaint-go-querylang:test --tests 'org.opentaint.semgrep.GoSampleBasedTest').",
  "- APPROXIMATION test (route missing-approximation), modelled on core/src/test/kotlin/org/opentaint/go/sast/dataflow/Pattern01StringsBuilderTest.kt: add a .go fixture under core/samples/src/main/go/ (package test, import test/util, funcs <name>001T positive / <name>002F negative) and a Pattern<NN><Name>Test : AnalysisTest() with override val commonPassRules = GoConfigLoader.getConfig()?.passThrough ?: emptyList() and assertReachable(\"test.<fn>\")/assertNotReachable. The FIX is a passThrough in core/opentaint-config/go-config/config/go-config/<pkg>.yaml (function{package,type?,name,receiver} + copy[{from,to}]; positions this|result|arg(N); modifiers as YAML list e.g. [arg(0), '[*]']). Run: (cd core && " + PATHS + " ./gradlew :test --tests 'org.opentaint.go.sast.dataflow.Pattern<NN><Name>Test').",
  "- ENGINE escalation (propagation-failure with a correct rule): add a test under core/src/test/kotlin/org/opentaint/go/sast/dataflow/ annotated with per-instruction fact reachability via AnalysisTest.printFactsAt(\"test.<fn>\") (driver EngineRoadmapDiagnosticTest) showing the death point (the first instruction line marked with the empty-set marker).",
  "- Querylang-vs-engine gate: if a rule test fails, load the YAML with SemgrepRuleLoader(listOf(GoLanguageStrategy())) then toGoSerializedTaintConfig()/toGoTaintConfiguration() and inspect emitted GoSerializedItems. Wrong names/positions/predicates => classification 'querylang'. Config correct but taint never reaches sink => 'engine'.",
].join("\n")

function resolvePrompt(issue) {
  const s = issue.sample
  const extra =
    (s.topExternal ? ", unmodeled method on path: '" + s.topExternal + "'" : "") +
    (s.sourceApi ? ", source API: '" + s.sourceApi + "'" : "") +
    (s.deathLine ? ", death: " + s.deathLine : "")
  const applyStep = APPLY
    ? "If this is a SIMPLE fix — a new/edited rule that makes the rule test pass, or a new approximation passThrough that makes the Pattern test pass — APPLY it and re-run the test until green. Commit your test + fix in the worktree (rationale in the message; end with the trailer 'Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>'). Set applied=true, isSimpleFix=true."
    : "Do NOT apply fixes this round (report-only). Set applied=false."
  const rebenchStep = REBENCH
    ? " If you applied a fix, rebuild the analyzer jar ((cd core && " + PATHS + " ./gradlew :projectAnalyzerJar)) and re-run the representative entry point with a scoped fn_investigate-style scan to confirm the bench FN is now reported."
    : ""
  return [
    "You are resolving ONE clustered benchmark FN issue for the Go taint engine, in your own git worktree off 'saloed/go-dev-tmp'. Be rigorous; prefer well-defined fixes over hacks; add NO comments to production Kotlin/Go source.",
    "",
    "ISSUE: key='" + issue.key + "' reason='" + issue.reason + "' cwe='" + issue.cwe + "' affecting " + issue.members.length + " benchmark file(s). Representative sample (in " + BENCHDIR + "/" + BENCH + "): '" + s.file + "'" + extra + ".",
    "",
    "STEPS:",
    "1. Read the representative sample file(s); cheaply confirm the FN shape. Read the matching rule " + BENCHDIR + "/rules/go/security/<cwe>.yaml.",
    "2. Extract a MINIMAL Go reproducer of just this shape.",
    "3. Add the route-appropriate test (conventions below) that reproduces the FN. Run it and confirm it FAILS first (red).",
    "4. Diagnose and classify via the querylang-vs-engine gate; set classification.",
    "5. " + applyStep,
    "5b. PRECISION GATE (mandatory for any new SINK or broad SOURCE rule edit): an isolated RED->GREEN repro is NOT sufficient. A new sink/source that matches a very common shape (e.g. '$W.Write', any '.Write', a bare field on every request) will inflate recall by one or two while flooding unrelated findings. Before declaring such a fix simple, re-scan the full bench ('cd " + BENCHDIR + " && " + PATHS + " ./scan.sh owasp' then './compare.py " + BENCH + "/.opentaint/results/report.sarif " + BENCH + "/truth.sarif') and compare the per-CWE 'rep' (reported-URI) and FP columns against the pre-fix numbers. If reported-URIs jump massively relative to the TP gained (e.g. +1 TP but +100s of new reports, or large cross-CWE bleed), the fix is a DIRTY HACK: REJECT it (revert the rule edit), set applied=false, isSimpleFix=false, classification='unresolved', and record in summary that it was rejected for precision. Only genuinely targeted source/sink shapes pass this gate. Prefer well-defined solutions over recall-at-any-cost.",
    "6. If NOT a simple fix (engine propagation/translation gap with no clean local fix, OR a rule fix rejected by the precision gate), write an investigation report to docs/superpowers/specs/2026-05-29-fn-<short-slug>.md (reproducer + exact test command + observed-vs-expected + death point from the fact dump + ruled-out causes + 1-3 sentence engine hypothesis); set isSimpleFix=false, applied=false, reportPath.",
    "7. Estimate complexity (trivial|small|medium|large|pipeline-wide) and whether a JVM analog exists to port (javaAnalog)." + rebenchStep,
    "",
    ROUTE_GUIDE,
    "",
    "Report the structured result including your worktree path. Your final message is the tool result, not a chat message.",
  ].join("\n")
}

const resolved = await pipeline(issues,
  (issue) => agent(resolvePrompt(issue), { schema: RESOLVE_SCHEMA, phase: 'Resolve', isolation: 'worktree', label: 'resolve:' + issue.key }),
)

const ok = resolved.filter(Boolean)
const applied = ok.filter(r => r.applied && r.testPasses)
const hard = ok.filter(r => !r.applied || !r.isSimpleFix)
log("Resolve: " + ok.length + " issues handled; " + applied.length + " simple fixes applied+green; " + hard.length + " hard/unapplied.")

phase('Synthesize')
const synthPrompt = [
  "You are the SYNTHESIZE step. Compile a concise ROUND REPORT for a Go taint-engine improvement round on bench '" + BENCH + "'.",
  "",
  "Current accuracy (TP/FP table):",
  triage.tpfpTable,
  "",
  "Covered-CWE FNs this round: " + triage.totalFns + ". No-relevant-rule CWEs (count-only): " + (triage.noRuleCwes.join(', ') || 'none') + ".",
  "",
  "Issues resolved (JSON):",
  JSON.stringify(ok, null, 1),
  "",
  "Produce: (1) a 4-8 line summary of the round (what moved, what is blocked); (2) the single RECOMMENDED NEXT FIX = the lowest-complexity hard issue with a Java analog or a localized fix (name it with its key and fixProposal); (3) stop = true ONLY if every remaining hard issue has javaAnalog=false AND complexity 'pipeline-wide'. Note for the operator that applied fixes live in per-issue worktrees and must be reviewed and integrated. Return the structured round report.",
].join("\n")

const round = await agent(synthPrompt, { schema: ROUND_SCHEMA, phase: 'Synthesize' })

return {
  bench: BENCH,
  tpfpTable: triage.tpfpTable,
  totalCoveredFns: triage.totalFns,
  noRuleCwes: triage.noRuleCwes,
  clusters: allClusters.length,
  processed: issues.length,
  appliedFixes: applied.map(r => ({ key: r.key, route: r.route, testPath: r.testPath, worktree: r.worktree, summary: r.summary })),
  hardIssues: hard.map(r => ({ key: r.key, route: r.route, classification: r.classification, complexity: r.complexity, javaAnalog: r.javaAnalog, reportPath: r.reportPath, fixProposal: r.fixProposal })),
  roundReport: round,
}
