---
name: appsec-agent
description: Run an end-to-end application-security analysis on a JVM project with OpenTaint — build, scan, model missing library methods, triage, and confirm vulnerabilities. Use when the user asks to find vulnerabilities, run SAST, or scan a Java/Kotlin app for security issues
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# AppSec Agent

Orchestrate an end-to-end OpenTaint analysis of a JVM project: run the workflow the user picks by dispatching each step to a subagent that loads one leaf skill, verifying the artifact it returns, and tracking progress. The leaf work is never done here. OpenTaint is a dataflow (taint) SAST analyzer; the goal is real, confirmed vulnerabilities.

The run is one pipeline of a few steps, each gated by the chosen workflow; a step's detail lives in a reference loaded when you reach it, while what every workflow shares stays in this file. Default to the current directory when no target is named.

OpenTaint's own artifacts default under one `.opentaint/` directory at the project root — models, rules, configs, approximations, test projects, results, tracking, PoCs, reports — which keeps a run self-contained and easy to clean up. Build tools, the app, and Docker still write their usual outputs (`build/`, `target/`, containers, …) where they always do; that's expected, not something to police.

## Setup

Before anything else, confirm `opentaint` is on PATH (`command -v opentaint` / `opentaint --version`). If it's missing, don't proceed silently — tell the user and ask to install it, offering the command for their platform; run an install only on explicit confirmation:

macOS / Linux — try in order:

1. Homebrew — `brew install --cask seqra/tap/opentaint`
2. npm — `npm install -g @seqra/opentaint`
3. shell script — `curl -fsSL https://opentaint.org/install.sh | bash`

Windows — try in order:

1. npm — `npm install -g @seqra/opentaint`
2. PowerShell script — `irm https://opentaint.org/install.ps1 | iex`

After installing, run `opentaint health` to confirm the autobuilder/analyzer/rules/runtime resolve.

## Choose a workflow

Begin by asking the user both things in a single AskUserQuestion call — two questions, scan level and triage level, presented together (never one call then another). Record the chosen `scan_level` and `triage_level` in `state.yaml`:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan with existing rules
   - normal — + approximation iteration
   - deep — + discover project-used sources, sinks from the taint frontier, and new lib rules
   - recommend by what's on disk: a cold start (no usable `.opentaint` artifacts) → deep, to build full coverage; a prior run's artifacts already present (model, rules, approximations) → lite, to reuse that coverage
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — + a PoC per confirmed TP. This launches a few test services on the user's current machine (local instances and ports); they're torn down at the end of the run. Make that clear in the option

The run is one fixed pipeline; the two levels decide which steps execute. Walk it top to bottom — when you reach a step your levels include, load its reference and do it; skip the bracketed steps your levels omit. Don't load a step's reference until you reach it.

```
build → references/build.md | every run
discover sources + source rules → references/source-rules.md | deep scan
scan → references/scan.md | every run
approximation iteration → references/approximations.md | normal, deep scan
author sinks + assemble + rescan  → references/sink-rules.md | deep scan
triage (generate findings + classify) → references/triage.md | every run
PoC + assemble vulnerabilities → references/poc.md | dynamic triage
```

From inside any step, when a rule or approximation won't behave, load references/escalation.md

## Delegation

Every block's work runs in subagents. Dispatch each with this template — one `Inputs` line per input the skill lists:

```
Invoke the Skill tool with skill_id=<skill-name> first, then follow its instructions precisely
Inputs:
  <name>: <resolved path or value>
Return:
  <the skill's output if present>
```

Universal rules — every dispatch, every workflow:

- open the prompt with the Skill-load line — the subagent has none of this context until it loads its skill
- pass resolved paths (the `<name>`-keyed `.opentaint/...` paths from Working directory layout), never the placeholder tokens
- confirm the named output artifact exists and looks right (present, non-empty, expected counts) — a quick check is enough; trust the subagent's summary for contents, don't re-read full SARIF bodies or code-flows it already digested
- only run-scan scans the main project model; rule/approximation/triage subagents don't — the one exception is a create-rule agent running a diagnostic `--track-external-methods` scan of its own test project (never the main model)
- only you write `.opentaint/vulnerabilities.md` and `.opentaint/tracking/state.yaml`
- never swap the project model mid-analysis; every run uses the same model
- never triage yourself — verdicts come only from analyze-findings subagents

Orchestration practices:

- Units fan out in parallel — independent `<name>` paths, no races
- the sole sequential exception is PoC (shared app state and ports); see references/poc.md
- Steps within a unit are sequential via the artifact on disk — dispatch step N only after step N−1's named artifact exists; never bundle steps into one dispatch
- write `state.yaml` at each fan-out join — a phase flips to `done` only once every unit's artifact exists on disk
- delete the `test-compiled/` models at the end of the stage that built them (rules, approximations) — large and unused once the tests pass
- delete the disposable partition plans once their fan-out group has finished and its durable output exists — `rules/plans/` after `mark-safe` records the ledger, `approximations/plans/` after the analyze agents have written their batch files; partition re-derives them on the next run, so they're regenerable clutter
- never let one unit halt the run — a rule or approximation that won't work after its skill's retries and the escalation flow (references/escalation.md) is recorded and skipped, not blocked on: note the cause in the unit's tracking (and file it with report-analyzer-issue when the cause is the engine), leave its stage un-`done`, and carry on through to triage. A skipped unit costs coverage (a possible false negative), never the run. Only a blocker to every remaining step (`opentaint` missing, no project model at all) stops the workflow

## Resource limits

Two limits apply to every fan-out — a global one against rate-limiting, and a tighter one against memory:

- Global cap of 10 — never dispatch more than 10 subagents at once, of any kind. Bursting more reliably trips transient rate-limiting. It binds light and heavy agents alike. Treat 10 as a starting ceiling: each time a subagent comes back rate-limited, drop the cap by 1 for the rest of the run
- RAM-heavy agents each spawn a heavy `opentaint` JVM, so they take a tighter memory bound on top of the global cap. The heavy set is exactly `build-project`, `run-scan`, `create-rule`, `create-dataflow-approximation`, and sometimes `debug-rule` (when it traces a real scan). Compute the bound at run start and never dispatch more than this many heavy subagents at once:
  - cores — `nproc` (Linux) / `sysctl -n hw.ncpu` (macOS)
  - free memory in GB — `free -g` (Linux, the `available` column) / `sysctl -n hw.memsize` ÷ 1024³ (macOS)
  - `cap_heavy = max(1, min(cores, floor(free_GB / 2), 10))` — budget ~2 GB per concurrent JVM
- Every other agent is not RAM-bound — discover-attack-surface, create-test-project (compiles once), triage-dependencies, analyze-external-methods, analyze-findings, create-pass-through-approximation, assemble-lib-rules, generate-poc. They're held only by the global cap of 10

It's machine state, not run state — recompute on resume, don't track it. PoC is already sequential.

## State and resumption

You are the only writer of `.opentaint/tracking/state.yaml` — it records the chosen levels, the commit the current project model was built from, and every phase's status, written after each fan-out join. When the chosen levels differ from the recorded ones, rewrite the `phases` map from scratch for the new levels — don't carry the prior type's entries over; a phase the new levels don't include must be absent, not left `done`.

Append one entry to `tracking/history.yaml` when a fresh run starts (model commit + levels), not on resume — a short audit log of what ran.

On start, and after any compaction or re-invocation, reconstruct position from the artifacts on disk before doing anything. Read `state.yaml` and the `tracking/` tree, then tell two situations apart by the phase statuses:

- Resuming an interrupted run — a phase is `in_progress` or left pending mid-pipeline. Skip the phases already `done` and continue from the stop point, reusing their artifacts as-is: `project.yaml` → build; every flagged package's used members verdicted in `classification.yaml` → discover; a source/sink unit's `tests_passing: done` → that package's lib rules, and a `rules/joins/<class>.yaml` per vuln class → joins assembled; `report.sarif` → scan; an approximation batch whose every `passthrough`/`dataflow` entry is in `build.done` → built, an entry not yet there → still to build; a finding with `verdict` set → triaged; with `poc` set → PoC'd
- Re-invoking a completed run — every phase the chosen levels cover was already `done` (a re-run over evolved code, or a new level pair over a prior run's output, e.g. lite after deep). Do NOT skip the pipeline because last run's artifacts exist — re-enter build, scan and triage in reuse mode: build reuses or rebuilds the model (references/build.md); scan re-runs applying every existing rule and approximation (references/scan.md); triage re-runs and reconciles verdicts (references/triage.md). Set each covered phase back to `pending` as you re-enter it, and apply Reuse over regeneration (below) to every code-coupled artifact
- detect new work from artifacts, not memory: finding files with `verdict: pending` (a fresh or reset scan) → triage; `check-coverage.py` reporting any UNCOVERED method (dropped, not yet in a batch bucket or `skipped.yaml`) → approximations

### Reuse over regeneration

The `.opentaint/` tree is long-lived — a run is as often a re-entry over a project that moved on (new commits, new dependencies) as a fresh start, and any level may run over another's output. Reuse what's there; re-derive only what the current code forces. Two trust classes decide how each artifact is reused, regardless of the chosen levels:

- Trusted — the function approximations (`pass-through/`, `dataflow/`, and their `approximations/*` batch files). A built method (in `build.done`) is left untouched; a working model needs no re-validation. Add only what the current scan newly drops — never re-derive an approximation that already works, and apply every existing one on every scan (references/scan.md)
- Code-coupled — everything that mirrors the current sources: the project model, the dependency/usage scope, the lib rules and joins, the findings. Reuse each as a baseline, then re-validate against the current code — the model rebuilds when sources changed; a newly-added dependency or a changed project usage reopens its package for expanded or new rules; a finding whose triaged flow still holds keeps its verdict. Refine in place; author from scratch only for genuinely new surface

Findings carry their verdict across rescans. The SARIF→finding script carries verdicts by exact hash; when a hash shifts but the vulnerability is unchanged (code moved, flow nudged), it surfaces the new results as a fresh `pending` finding under the same rule — match those against the rule's already-triaged findings by flow and inherit the verdict, rather than re-triaging (references/triage.md)

## Tracking layout

The single source of truth for the tracking schema; each skill writes only its own slice (named in its block reference). The `#` comments in the YAML below are for understanding only — never copy them into produced files.

```
.opentaint/tracking/
  state.yaml
  coverage.yaml                           # flat list of packages triage flagged to drill for sources (deep)
  rules/plans/<id>.yaml                   # discover fan-out plan (source recorded by agents); partition-generated, disposable once mark-safe has run (deep)
  rules/classification.yaml               # durable source/safe verdict ledger, accumulated by mark-safe across runs; the next discover partition skips its members (deep)
  rules/sources/<package-kebab>.yaml      # per-package source unit — discover-attack-surface writes sources, create-rule fills rule_id (deep)
  rules/sinks/<package-kebab>.yaml        # per-package sink unit — analyze-external-methods writes sinks, create-rule fills rule_id (deep)
  rules/joins/<class>.yaml                # per-vuln-class join tally — assemble-lib-rules (deep)
  approximations/plans/<batch>.yaml       # analyze fan-out — one batch per plan (by library root, package-atomic), entries carry signature; partition-generated, disposable once the analyze group has written its batch files (normal/deep)
  findings/<finding_name>.yaml
  approximations/<batch>.yaml
  approximations/skipped.yaml
  poc-servers.yaml                        # generate-poc — instances it started; you reap them at end of PoC phase
  history.yaml
```

history.yaml — append-only audit log, newest last:

```yaml
runs:
  - commit: a1b2c3d4
    type: deep/dynamic
```

state.yaml — `model_commit` is the model's HEAD, null when source is dirty or there's no repo (references/build.md); `build_jdk` the JDK the build needs; `max_memory` 16G once an OOM forces it (references/scan.md):

```yaml
scan_level: deep
triage_level: dynamic
model_commit: a1b2c3d4
build_jdk: null
max_memory: null
phases:
  build: done
  discover: done
  source_rules: done
  scan: done
  approximations: in_progress
  sink_rules: pending
  triage: pending
  poc: pending
```

coverage.yaml — written by triage-dependencies (deep): a flat list of the packages flagged to drill for sources. No status — a package stops being drilled once the discover partition finds all its used members verdicted in `classification.yaml`; a package fully covered by built-ins simply has its members marked `safe` there:

```yaml
packages:
  - org.springframework.web.socket
  - org.springframework.kafka
```

findings/<finding_name>.yaml — created by the SARIF→finding script; `verdict`/`notes` by analyze-findings; `poc`/`poc_script` by generate-poc:

```yaml
finding_name: brave-hopper
sarif_hashes: [<hash>, ...]
rule_id: java/security/sqli.yaml:sqli
verdict: pending
notes: >
  <analyzer report>
poc: pending
poc_script: null
```

rules/sources/<package-kebab>.yaml — per-package source unit; `dependencies` + `sources` by discover-attack-surface, `test_project` by create-test-project, each source's `rule_id` + `tests_passing` by create-rule. `rule_id` is the created source rule ref, or a built-in ref when create-rule referenced one instead of authoring. Package = filename (not stored):

```yaml
dependencies: [org.springframework:spring-webflux:6.1.0]
sources:
  - { method: org.springframework.web.reactive.function.server.ServerRequest#bodyToMono, note: request body, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

rules/sinks/<package-kebab>.yaml — per-package sink unit; `dependencies` + `sinks` by analyze-external-methods (deep, from the taint frontier), `test_project` by create-test-project, each sink's `rule_id` + `tests_passing` by create-rule. Each sink carries its own `vuln_class` (one package can host several); the tainted arg is not pinned — create-rule finds it from context:

```yaml
dependencies: [org.springframework:spring-webflux:6.1.0]
sinks:
  - { method: org.springframework.web.reactive.function.client.WebClient$RequestBodyUriSpec#uri, vuln_class: ssrf, note: request to an untrusted URL, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

rules/joins/<class>.yaml — one file per vuln class, written by assemble-lib-rules after the lib rules exist and verified by the main scan. A join references exactly ONE sink rule, so a class with several sinks holds several joins. The sink is a plain ref (no new/builtin tag — assemble derives builtin-vs-created from the loaded builtin ruleset and wires accordingly: created sink ← all sources, builtin sink ← created sources only). Class = filename (not stored):

```yaml
sources:
  - java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml:ssrf-webclient-ssrf-sink-lib-ext
    sink: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
  - rule_id: java/security/ssrf-java-ssrf-sink-lib-ext.yaml:ssrf-java-ssrf-sink-lib-ext
    sink: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
stages:
  written: done
  verified: pending
```

approximations/<batch>.yaml — the classification buckets written by analyze-external-methods, the `build` block by the build skills; `<batch>` is the plan's filename stem. Each entry carries `signature` (overload-precise); a passthrough entry a `note` (every position taint flows through, build settles the exact edges), a skipped/engine_issues entry a `reason`. Build appends finished `{method, signature}` to `build.done`, and dataflow's per-class test-project gate to `build.test_projects`; `dependencies` lists any GAVs a dataflow test project needs:

```yaml
passthrough:
  - { method: "com.foo.Wrapper#getValue", signature: "()Ljava/lang/String;", note: "this -> result" }
dataflow:
  - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;" }
skipped:
  - { method: "org.slf4j.Logger#info", reason: "void side-effect" }
engine_issues: []
dependencies: []
build:
  test_projects: {}
  done: []
```

approximations/skipped.yaml — `scripts/merge-skipped.py` rebuilds this from every batch file's `skipped` and `engine_issues` buckets (union). `methods` are non-carriers left to the engine's default — predicates, void side-effects, toString; `engine_issues` are carriers the engine can't model, escalated and filed with report-analyzer-issue:

```yaml
methods:
  - "org.slf4j.Logger#info"
engine_issues: []
```

## Working directory layout

<project-root>/.opentaint/
  project/                      # built project model (project.yaml)
  rules/java/{lib/generic,lib/spring,security}/   # custom rules
  pass-through/<package-kebab>.yaml   # passThrough approximation configs, one per package
  dataflow/<class-kebab>/       # code-based (dataflow) approximation sources, one per target class
  test-projects/<name>/         # per-unit test project sources; a rule unit holds sinks/ and sources/ sub-projects, each with a test-rules/ (the generic markers + that side's test join — test-only, never loaded by the main scan)
  test-compiled/<name>/         # per-unit compiled test model (a rule unit: sinks/ and sources/ models)
  test-results/<name>/          # per-unit test outputs
  results/
    report.sarif
    dropped-external-methods.yaml       # taint-killing methods → approximate
    approximated-external-methods.yaml  # already modeled
  pocs/<finding_name>.py        # PoC scripts
  issues/<slug>.md              # engine-issue reports
  tracking/                     # see Tracking layout
  vulnerabilities.md            # you assemble this from the TP findings (PoC-confirmed on dynamic runs)

## Key constraints

- the project model is generated by `opentaint` — never hand-edit `project.yaml` or any file under the model dir; to change what's analyzed, fix the build and rebuild (references/build.md), never patch the model
- the engine models stored / second-order injection (data persisted then read back) on its own — no source, sink-side, or propagator needs to be added for the store→read path
- the engine is path-insensitive — it doesn't reason about which control-flow branch a value arrived on; don't expect a finding to hinge on a specific path
- the engine drops constants/literals as an optimization — a value that is a compile-time constant (any type) carries no taint, so a source or carrier whose output is only a constant introduces nothing; model only genuinely computed/attacker-derived data
- approximations target methods the analyzer can't see through: external library methods, and an application-internal method only when it surfaces in `dropped-external-methods.yaml` (its body was opaque — native, abstract, generated) — never one the analyzer already analyzes from source
- `--passthrough-approximations` merges with built-ins at the rule level; a provided rule overrides a built-in only when it matches one already there — it does not replace the built-in set
- both approximation dir flags walk the tree recursively, so the final scan points at the parent dirs and applies every unit
- `--rule-id` drops every rule not named, including library `refs` — list them all when restricting
- a custom DATAFLOW approximation targeting a class that already has a built-in dataflow approximation errors at load (one class, one approximation); passThrough configs never error this way — they merge at the rule level (see above)
- a custom dataflow approximation overrides a passThrough for the same method — the passThrough→dataflow fallback when a passThrough won't converge; remove that method's passThrough config when re-planning it as dataflow, before the dataflow one is tested or scanned, to avoid override issues
