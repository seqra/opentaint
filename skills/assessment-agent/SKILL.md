---
name: assessment-agent
description: Assess a project for unknown vulnerabilities with OpenTaint, owning the long project build and scans and delegating each other pipeline stage. Use when the user asks to find vulnerabilities or scan an application for security issues, with no finding set supplied to reproduce
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Assessment Agent

Assess a project for vulnerabilities it was not already known to have. Keep the long project build and every full-project scan in this main session; delegate each bounded source, approximation, sink, triage, and PoC stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

This is the assessment pipeline — one of the two that share the OpenTaint machine and the `.opentaint/` tree. The other is `enactment-agent`'s, which reproduces a finding set the user supplies. They differ in where the source and sink rules come from: discovered from the project's dependency attack surface here, generalized from the supplied findings there. Everything downstream is shared, and `appsec-agent` is the entry point that picks between them.

This run is one *pass* over a tree that outlives it. The pass may follow an enactment pass, in which case its boundaries are already on disk as rules and this pass hunts with them; it may be followed by one; and it may run again on a later commit as a regression check. So leave the tree richer than you found it, and don't treat an artifact you didn't create as debris. If the tree carries a reference set from an enactment pass, your rescans change what it reproduces, and `get_status.py` keeps the cross-reference in scope so its coverage manifest stays true.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. The run produces confirmed vulnerabilities plus reusable project-specific rules and approximations under one self-contained `.opentaint/` directory at the project root.

## Setup

Skip only what `appsec-agent` already did when it handed off — the toolchain and nesting checks. Everything from step 3 on is this pipeline's own, including the bootstrap.

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves. When a repo carries build markers for more than one, ask the user which to analyze.

### 4. Choose the workflow

Ask the user for both knobs together:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom approximations
   - deep — build + scan + custom approximations + custom rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior run's artifacts already present → lite
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 5. Bootstrap

Seed the run state and the working tree with the chosen levels and language:

```bash
uv run <skill-dir>/scripts/generate.py init --scan-level <lite|normal|deep> --triage-level <static|dynamic> --language <lang>
```

It writes `state.yaml` with `mode: assessment`, appends this pass to `history.yaml`, and creates the `.opentaint/` tree.

Over a tree an earlier pass already built, it prints what carried over and keeps all of it — an enactment pass's boundary-derived rules, its approximations, and its verdicts are this pass's starting corpus, and `get_status.py` will report their phases `DONE` rather than redoing them.

## Workflow

The run is one fixed pipeline; the selected levels determine which phases are in scope. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
discover / source_rules     → stage subagent: sources
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
sink_rules                  → stage subagent: sinks, then MAIN: rescan
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref   (only if an enactment pass left a reference set)
```

`crossref` appears only when a previous enactment pass over this tree left a reference set. This pass's rescans changed what those supplied findings reproduce, so re-judging them and refreshing `.opentaint/enactment.md` is part of finishing — not optional cleanup.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/approximation; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed approximation, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.

## Dispatching

Dispatch exactly one stage-orchestrator subagent for each stage invocation:

```
Invoke the Skill orchestrate-stage first, then follow its instructions precisely
Inputs:
  stage: <sources|approx-round|sinks|triage|poc|crossref|escalation>
```

For a `deep` approximation round, also pass `sinks: true`. A subagent inherits the project-root working directory, so omit `project-root`.

Stage context:

- `sources` — discover dependency sources, author their rules, and wire the joins
- `approx-round` — classify and build one dropped-method frontier; use a fresh agent for each new frontier
- `sinks` — author classified sink rules and wire the joins
- `triage` — classify the latest findings and refresh the vulnerability report
- `crossref` — re-judge a reference set an earlier enactment pass left, and refresh its coverage manifest
- `poc` — reproduce confirmed findings and add the outcomes to the report
- `escalation` — repair or settle a stage artifact, or report a scan-wide no-SARIF failure

Keep each agent id until the next scan validates its artifacts. On a stage-owned error, resume that agent with `stage: escalation`, the exact error, and the artifact path/id. If its thread is unavailable, start a re-entrant `orchestrate-stage` agent with that diagnosis.

Dispatch each subagent fresh, don't fork context into it. Then wait for it natively, don't monitor or poll every minute. If the harness forces a wait timeout, set it to ~1h and re-wait when it returns.

## State and resumption

Use this ownership map to route work and scan errors:

```
.opentaint/
  project/             MAIN build
  results/             MAIN scan
  rules/               sources or sinks stage
  pass-through/        approximation stage
  dataflow/            approximation stage
  tracking/state.yaml  MAIN run knobs
  tracking/            stage agents, leaves, and join scripts otherwise
  vulnerabilities.md   triage / PoC stage
  issues/               escalation stage
```

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an enactment pass's boundary rules, reference set, and coverage manifest are as durable as your own.

`state.yaml` shape — `mode` is this pass's pipeline, not a property of the tree, so a later enactment pass simply rewrites it and keeps everything else:

```yaml
mode: assessment
scan_level: deep
triage_level: dynamic
language: java
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```

## Key constraints

- read pipeline state through `<skill-dir>/scripts/get_status.py`, not by hand — don't re-derive it with glob/grep/`python3 -c`/yaml scans over `.opentaint/tracking`, `results`, or the `*.yaml`, nor open finding/unit/SARIF files just to review progress. If its output doesn't settle the question, re-run it with `--full` before opening any file
- don't author or edit stage-owned artifacts or tracking; MAIN writes only `model_commit`, `build_jdk`, and `max_memory` in `state.yaml`
- keep one generated project model for the run; never hand-edit or replace it mid-analysis — fix the build and rebuild before starting a new run
