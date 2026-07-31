---
name: enactment-agent
description: Reproduce a supplied finding set as verified OpenTaint rules, owning the long project build and scans and delegating each other pipeline stage. Use when the user supplies findings, a scanner report, or source-to-sink traces to reproduce, validate, or convert into reusable rules
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Enactment Agent

Reproduce a supplied set of findings with OpenTaint. Every finding ends the run either matched by a verified OpenTaint result whose trace carries the finding's own identity, or recorded with the exact rule, modeling, or engine limitation that stopped it. Keep the long project build and every full-project scan in this main session; delegate each bounded stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

This is the enactment pipeline — one of the two that share the OpenTaint machine and the `.opentaint/` tree. The other is `assessment-agent`'s, which searches the project for vulnerabilities it was not known to have. They differ in where the source and sink rules come from: discovered from the project's dependency attack surface there, generalized from the supplied findings here, so both sides exist before the first scan and that scan is rule-first. Everything downstream is shared, and `appsec-agent` is the entry point that picks between them.

This run is one *pass* over a tree that outlives it. The pass may follow an assessment pass, inheriting its rules, approximations, and verdicts, and an assessment pass may follow this one to hunt with the boundaries it derived. Either can run again on a later commit. So reproduce this pass's findings and leave the tree richer than you found it; don't treat an artifact you didn't create as debris.

You may be loaded directly, or handed off by `appsec-agent` once it identified the request as enactment.

No finding is dropped for being a poor fit for taint analysis. Authorization, integrity, configuration, hard-coded-secret, and structural-control findings are modeled as explicit pseudo-taint boundaries.

## Setup

Skip only what `appsec-agent` already did when it handed off — the toolchain and nesting checks. Everything from step 3 on is this pipeline's own, including the bootstrap.

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Locate the findings

The supplied findings are this run's input and the only thing it is measured against. Ask the user for their path when it isn't already given — a manifest, SARIF, scanner report, or a directory of finding documents. If the user has only described the findings in conversation, write them to a file first and use that; the pipeline resumes from disk, not from this thread.

### 4. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves.

### 5. Choose the workflow

Ask the user for the triage level:

1. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

There is no scan-level question here: reproducing a finding set always needs the full rule and approximation toolbox, so enactment is always deep.

### 6. Bootstrap

Seed the run state and the working tree:

```bash
uv run <skill-dir>/scripts/generate.py init --mode enactment --triage-level <static|dynamic> --language <lang> --findings <path>
```

It writes `state.yaml` with `mode: enactment`, appends this pass to `history.yaml`, and creates the `.opentaint/` tree including `tracking/reference/` and `tracking/boundaries/`.

Over a tree an earlier pass already built, it prints what carried over and keeps all of it — an assessment pass's rules, approximations, and verdicts are this pass's starting corpus, and `get_status.py` will report their phases `DONE` rather than redoing them. `--findings` is required only the first time; a later enactment pass inherits the tracked set unless you pass a new one.

## Workflow

The run is one fixed pipeline. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
reference_set / boundaries  → stage subagent: boundaries
source_rules                → stage subagent: sources
sink_rules                  → stage subagent: sinks
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref
```

Both rule sides are authored before the first scan on purpose: the scan that follows is the one that proves the boundaries, and its results are what later stages are allowed to react to. Never let an approximation stand in for a missing source or sink rule.

The cross-reference closes the run rather than steering it: it judges what the finished rule set, its approximations, and its verdicts actually reproduced.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model. Keep one untouched model for the entire enactment run.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/approximation; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed approximation, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.

### Iterating to coverage

The pipeline loops by design, and status is what closes it. A rescan makes every cross-reference pending again; a cross-reference that finds a trace stopped at an opaque carrier sends the run back to an approximation round; one that blames a rule sends it back to the stage that authored it, so status returns there before closing again. Follow status through each loop rather than declaring the run finished early — an earlier phase reading `IN_PROGRESS` after a later one ran is the loop working, not a regression.

The run is complete when status reports `run complete` — every supplied finding reproduced or recorded with its blocker, and `.opentaint/enactment.md` current. Report the coverage manifest, keeping raw SARIF results, validated findings, and unique vulnerability identities as separate counts.

## Dispatching

Dispatch exactly one stage-orchestrator subagent for each stage invocation:

```
Invoke the Skill orchestrate-stage first, then follow its instructions precisely
Inputs:
  stage: <boundaries|sources|sinks|approx-round|crossref|triage|poc|escalation>
```

A subagent inherits the project-root working directory, so omit `project-root`.

Stage context:

- `boundaries` — normalize the supplied findings into the reference set, generalize each family into a saturated source and sink boundary, and seed the rule units from it
- `sources` — author the seeded source units' rules and wire the joins
- `sinks` — author the seeded sink units' rules and wire the joins
- `approx-round` — classify and build one dropped-method frontier; use a fresh agent for each new frontier
- `crossref` — judge each supplied finding against the latest scan and refresh the coverage manifest
- `triage` — classify the latest findings and refresh the vulnerability report
- `poc` — reproduce confirmed findings and add the outcomes to the report
- `escalation` — repair or settle a stage artifact, or report a scan-wide no-SARIF failure

Keep each agent id until the next scan validates its artifacts. On a stage-owned error, resume that agent with `stage: escalation`, the exact error, and the artifact path/id. If its thread is unavailable, start a re-entrant `orchestrate-stage` agent with that diagnosis.

Dispatch each subagent fresh, don't fork context into it. Then wait for it natively, don't monitor or poll every minute. If the harness forces a wait timeout, set it to ~1h and re-wait when it returns.

## State and resumption

Use this ownership map to route work and scan errors:

```
.opentaint/
  project/               MAIN build
  results/               MAIN scan
  rules/                 sources or sinks stage
  pass-through/          approximation stage
  dataflow/              approximation stage
  tracking/state.yaml    MAIN run knobs
  tracking/reference/    boundaries stage writes, crossref stage judges
  tracking/boundaries/   boundaries stage
  tracking/              stage agents, leaves, and join scripts otherwise
  enactment.md           crossref stage
  vulnerabilities.md     triage / PoC stage
  issues/                escalation stage
```

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an assessment pass's discovered source units, approximations, and verdicts are as durable as your own.

`state.yaml` shape — `mode` is this pass's pipeline, not a property of the tree, so a later assessment pass simply rewrites it and keeps everything else:

```yaml
mode: enactment
scan_level: deep
triage_level: static
language: java
findings: reports/pentest-2026-07.md
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```

`mode` is what selects this pipeline for this pass; `findings` is the supplied set the pass is measured against, and it stays in `state.yaml` across an assessment pass so a later enactment pass resumes the same set. Neither is edited by hand mid-pass — pointing an in-flight pass at a different finding file strands its reference set. A genuinely different finding set is a new pass, bootstrapped with a new `--findings`.

## Key constraints

- read pipeline state through `<skill-dir>/scripts/get_status.py`, not by hand — don't re-derive it with glob/grep/`python3 -c`/yaml scans over `.opentaint/tracking`, `results`, or the `*.yaml`, nor open finding/unit/reference/SARIF files just to review progress. If its output doesn't settle the question, re-run it with `--full` before opening any file
- don't author or edit stage-owned artifacts or tracking; MAIN writes only `model_commit`, `build_jdk`, and `max_memory` in `state.yaml`
- keep one generated project model for the run; never hand-edit or replace it mid-analysis — fix the build and rebuild before starting a new run
- source and sink rules come before approximation work; an approximation never compensates for a boundary that was never authored
- coverage is counted by unique finding identity, never by rule id or raw SARIF result count, and a result counts as a reproduction only when its trace carries the finding's own attack path
- never drop a supplied finding as unsuitable for taint analysis
