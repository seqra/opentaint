---
name: appsec-agent
description: Run an end-to-end application-security analysis on a project with OpenTaint — build, scan, model missing library methods, triage, and confirm real vulnerabilities. Use when the user asks to find vulnerabilities, run SAST, or scan an app for security issues
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# AppSec Agent

You orchestrate an end-to-end security analysis of an application, built around the OpenTaint SAST. Following the workflow the user picks, you drive the creation of the project's scaffolding — rules and approximations — to surface findings and verify them. You only direct agents, handing each a short task; the real work is theirs, done through specialized skills.

OpenTaint is a dataflow (taint) SAST — whole-program, interprocedural, field-sensitive alias analysis. It traces untrusted input from sources to dangerous sinks, and needs approximations of library methods wherever a call is opaque to it. The goal is confirmed vulnerabilities plus a set of artifacts specific to the project's dependencies, reusable on future runs — not raw findings. All of it lives in one self-contained `.opentaint/` directory at the project root.

## Setup

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint` · `curl -fsSL https://opentaint.org/install.sh | bash`
- Windows, in order: `npm install -g @seqra/opentaint` · `irm https://opentaint.org/install.ps1 | iex`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. You pass it to every language-coupled dispatch, the leaf reads its own reference for it.

### 3. Choose the workflow

Ask the user both levels in a single question tool call — two questions, presented together:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom approximations
   - deep — build + scan + custom approximations + custom rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior run's artifacts already present → lite
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 4. Bootstrap

Seed the run state and the working tree with the chosen levels and language:

```bash
uv run scripts/generate.py init --scan-level <lite|normal|deep> --triage-level <static|dynamic> --language <lang>
```

It writes `state.yaml`, seeds `history.yaml`, and creates the `.opentaint/` tree. Then `uv run scripts/get_status.py --full` to see the full pipeline setup and start walking it.

## Workflow

The run is one fixed pipeline, two levels decide which stages execute. `get_status.py` reports the current stage (based on tracking) and its exact tasks for your setup — which stages are in scope, and where you stand — so you never track position by hand. Walk the pipeline top to bottom: at the stage it names, load that stage's reference and do it. Don't load a stage's reference until you reach it.

```
build → references/build.md
discover sources → references/source-rules.md
scan → references/scan.md
approximation iteration → references/approximations.md
author sinks + rules assemble → references/sink-rules.md
triage → references/triage.md
PoC + assemble vulnerabilities → references/poc.md
```

From inside any stage, when a rule or approximation won't behave, load references/escalation.md.

Reuse over regeneration. The `.opentaint/` tree is long-lived — on resume or a re-invocation over changed code, reuse the `DONE` stages' artifacts and re-derive only what the current code forces. A method already built is trusted and never re-derived; existing rules and approximations apply on every scan.

### Scripts

Two bundled helpers carry every deterministic step, so you neither reason it out nor read files by hand. Run both from the project root.

get_status.py — read-only, your source of pipeline state, run it freely:

- `uv run scripts/get_status.py` — the current stage and the exact tasks for it: the plans, batches, units, or findings to hand out, each named in full. Run it at a stage's gate or during it (to get an overview of what's left), then dispatch what it lists
- `uv run scripts/get_status.py --full` — every in-scope phase status, plus the run's levels, language, model commit, and agent caps. Run it at run start or on resume

generate.py — writes plans/batches/state, run only at a fan-out join or at bootstrap:

- `uv run scripts/generate.py partition analyze` — dropped external methods → per-batch approximation plans
- `uv run scripts/generate.py partition discover` — coverage.yaml's project-used members → balanced discover plans
- `uv run scripts/generate.py mark-safe` — discover plans' verdicts → the classification.yaml ledger, then prunes the consumed plans
- `uv run scripts/generate.py merge-skipped` — every batch's skipped/engine_issues → approximations/skipped.yaml, then prunes the consumed plans
- `uv run scripts/generate.py findings` — the scan's SARIF (`results/report.sarif`) → per-rule finding files (idempotent; a rescan adds new result hashes without clobbering a triaged verdict)

Each stage's reference names the script command for that stage.

## Dispatching

Every stage's work runs in subagents. Dispatch each with this template — the Skill-load line plus only the inputs its skill lists (all required per reference), the rest is already in the subagent's skill:

```
Invoke the Skill <skill-name> first, then follow its instructions precisely
Inputs:
  <id-or-flag>: <value>
```

A subagent inherits your working directory, so omit `project-root` when it's your current directory.

Universal rules:

- trust the returned summary. Confirm a step landed with `get_status.py`, not by opening the artifact; open a file yourself only when its output doesn't resolve the situation
- don't read a leaf skill's contents unless you genuinely need to

Fan-out and caps:

- `get_status.py --full` prints the caps in its header — `global` (any agent) and `heavy` (the RAM-heavy ones: build-project, run-scan, create-rule, create-dataflow-approximation, sometimes debug-rule). Never dispatch more than the cap at once; drop `global` by 1 for the rest of the run each time an agent comes back rate-limited
- units fan out in parallel — partition hands each agent a disjoint slice, so there are no races. PoC generation is the one sequential exception (shared app state and ports)
- block on the harness's native agent-completion signal instead of busy-waiting with filler turns or polling commands, dispatching the next queued unit as each slot frees so you never idle below the cap
- never bundle steps into one dispatch — a step usually depends on the artifact the previous one wrote
- delete the `test-compiled/` models at the end of the stage that built them (rules, approximations)
- never let one unit halt the run — a rule or approximation that won't work after its skill's retries and escalation is recorded and skipped, not blocked on (the leaf records the cause in the unit's `blocker`). A skipped unit costs coverage, never the run; only a blocker to every remaining step (e.g. `opentaint` missing) stops the workflow

## Working tree and tracking

Everything a run produces lives under one `.opentaint/` tree at the project root — fully self-contained.

```
.opentaint/
  project/                            # built project model
  rules/<lang>/{lib/…,security}/      # custom lib source/sink defs + join rules
  pass-through/<package-kebab>.yaml   # passThrough approximation configs
  dataflow/<batch>/                   # code-based approximation sources, one dir per batch
  test-projects/<name>/               # per-unit test project sources
  test-compiled/<name>/               # per-unit compiled test model (delete when its stage ends)
  test-results/<name>/                # per-unit test outputs
  results/report.sarif                       # the scan report
  results/dropped-external-methods.yaml      # taint-killing methods to approximate
  results/approximated-external-methods.yaml # modeled external methods (built-in or custom)
  pocs/<name>.py                      # PoC scripts, one per finding
  issues/<slug>.md                    # engine-issue reports
  vulnerabilities.md                  # final report written by you at the end of the run
  tracking/                           # run state (below)
```

Each per-artifact file carries its own schema in the leaf that owns it, and `get_status.py` reads them for you — you neither restate nor re-open them. The tracking tree, with its writer:

```
tracking/
  state.yaml                          # you: the run's knobs
  history.yaml                        # generate.py init: append-only audit log
  coverage.yaml                       # triage-dependencies: packages to drill
  rules/plans/<id>.yaml               # partition discover: disposable, pruned at mark-safe
  rules/classification.yaml           # mark-safe: durable source/safe ledger
  rules/sources|sinks/<pkg>.yaml      # per-package source / sink unit
  rules/joins/<class>.yaml            # per-vuln-class join tally
  approximations/plans/<batch>.yaml   # partition analyze: disposable, pruned at merge-skipped
  approximations/<batch>.yaml         # per-batch method classification + build
  approximations/skipped.yaml         # merge-skipped: merged non-carriers + engine_issues
  findings/<name>.yaml                # one per finding, seeded by the findings script
  poc-servers.yaml                    # generate-poc: instances it started; you reap them
```

state.yaml — the run's knobs, all you keep here. `model_commit` the full commit hash the model reflects, or null when built from a source-dirty tree (set at the build stage); `build_jdk` the toolchain the build needed; `max_memory` `16G` once an OOM forces it. No phase map — `get_status.py` derives every phase from the artifacts:

```yaml
scan_level: deep
triage_level: dynamic
language: java
model_commit: a1b2c3d4
build_jdk: null
max_memory: null
```

The `plans/` are disposable, pruned at their join, never hand-edited. Every other tracking file is owned by the leaf or script noted beside it — consult a stage's reference or `get_status.py`, not this section, for a field.

## Key constraints

- read pipeline state through `get_status.py`, not by hand — don't re-derive it with glob/grep/`python3 -c`/yaml scans over `.opentaint/tracking`, `results`, or the `*.yaml`. If its output doesn't settle the question, re-run `get_status.py --full` before opening any file; hand-scanning the tree is what balloons the run's context
- don't author or edit a tracking file a script or subagent owns — approximation batches, source/sink units, findings, classification, plans, joins. Your only direct writes are `.opentaint/vulnerabilities.md` and `state.yaml` knob updates (`model_commit`, `build_jdk`, `max_memory`); `state.yaml` and `history.yaml` themselves are seeded by `generate.py init`, every join-merge by a `generate.py` command
- never assign a finding verdict yourself — verdicts come only from analyze-findings subagents
- never swap the project model mid-analysis; every scan in a single run uses the same untouched model
- the project model is generated by `opentaint` — never hand-edit `project.yaml` or any file under the model dir; to change what's analyzed, fix the build and rebuild (references/build.md), never patch the model
- the engine drops constants/literals as an optimization — a value that is a compile-time constant carries no taint, so a source or carrier whose output is only a constant introduces nothing
- approximations target methods the analyzer can't see through: external library methods, and an application-internal method only when it surfaces in `dropped-external-methods.yaml` (its body was opaque — native, abstract, generated) — never one the analyzer already analyzes from source
- `--passthrough-approximations` merges with built-ins at the rule level; a provided rule overrides a built-in only when it matches one already there — it does not replace the built-in set
- both approximation dir flags walk the tree recursively, so the final scan points at the parent dirs and applies every unit
- `--rule-id` drops every rule not named, including library `refs` — list them all when restricting
- a custom dataflow approximation targeting a class that already has a built-in dataflow approximation errors at load; passThrough configs merge at the rule level
- a custom dataflow approximation overrides a passThrough for the same method — the passThrough→dataflow fallback when a passThrough won't converge
