---
name: appsec-agent
description: Run an end-to-end OpenTaint application-security analysis in one of three modes — onboarding a project's dependency frontier, discovering vulnerabilities from the project, a diff, or a spec, or enacting a supplied finding set — owning the long project build and scans and delegating each other pipeline stage. Use when the user asks to find vulnerabilities, scan an application for security issues, reproduce or validate a supplied finding set, or continue an OpenTaint run
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# AppSec Agent

Run an end-to-end OpenTaint security analysis. Keep the long project build and every full-project scan in this main session; delegate each bounded intake, boundary, rule, approximation, triage, and PoC stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. A run produces confirmed vulnerabilities plus the project's own universal rules and the models behind them — the passThrough and dataflow approximations that carry taint through library code, which the pipeline's `approximations` phase builds. Everything lands under one self-contained `.opentaint/` directory at the project root.

This is the only entry point. It runs in one of three modes, which differ in what the run takes as its input — and therefore in where the universal rules come from — and in nothing else:

- **onboarding** — the external-method frontier: every dependency member the project's own code calls, taken as a trust boundary until a leaf verdicts it. Run once per project, to build the universal rule and model corpus the later passes inherit
- **discovery** — the project, a diff, or an informal spec of what changed or what matters; the code it names becomes the boundary evidence
- **enactment** — a finding set the user supplies: a report, pentest results, or source-to-sink traces, reproduced as verified rules

Whatever the input, intake groups it into families, the boundaries stage generalizes each family into one universal source and one universal sink, and everything downstream is the same pipeline in the same order.

## Modes

### What each mode takes in

- **onboarding** — no input beyond the project itself. The frontier sweep flags the dependencies that can carry untrusted data, partitions the members the project actually calls, and verdicts each one: a trust boundary, an effect, or neither. It is the widest intake there is, and its output — a classified frontier, universal rules for the stack, and the models behind them — is what makes every later pass cheap
- **discovery** — a diff, a spec, a ticket, or a sentence about what the project does and what would be bad. Ask for whatever the user has and record its path; with nothing supplied the scope is the whole project. Intake reads it, resolves it to code, and groups that code into families
- **enactment** — the supplied findings, as a manifest, SARIF, scanner report, or a directory of finding documents. Ask for the path when it isn't given. If the user only described the findings in conversation, write them to a file first and use that; the pipeline resumes from disk, not from this thread

### Onboarding runs once

The frontier sweep is the expensive pass, and its corpus is durable: the classification ledger, the universal rules, and the models stay on disk and apply to every scan afterwards, whichever mode ran it. So onboard a project once and then work in discovery or enactment. Bootstrap refuses a second onboarding pass over a tree that already had one and says so; a genuinely new dependency stack is a new tree.

### The modes compose

They are not alternatives, and picking one is not a commitment. One `.opentaint/` tree accumulates the artifacts of every pass over it, in any order and as many times as the project needs:

- **onboarding, then anything** — the natural start. A discovery or enactment pass over an onboarded tree finds most of its boundaries already ruled and modeled, and spends its work on what its own input names
- **enactment, then discovery** — reproduce the supplied report first, then hunt with the rules it produced. Boundaries derived from real findings are exactly the ones a discovery pass would otherwise have to argue for
- **discovery, then enactment** — assess the project, then measure a report against the corpus that pass built. What the report names but the scan missed is now a rule or modeling gap you can point at
- **any of them, again on a later commit** — the tree is long-lived. A new HEAD makes the model stale, so the pass rebuilds and rescans, and every rule, model, and verdict carries over. That's how a run becomes a regression check rather than a one-off

So `mode` in `state.yaml` is the intake of the *current pass*, not a property of the tree. Switching it is normal, needs no fresh tree, and strands nothing.

### Read what the tree already holds

If `.opentaint/tracking/state.yaml` exists, find out where the project stands before choosing:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints the current `mode`, the run's levels, the tracked finding set or spec if there is one, and — once the tree has more than one pass — the `passes:` chain. The phase lines say whether that pass is finished or mid-flight.

- mid-flight pass — resume it rather than starting a different one over the top of it
- finished pass, and the user wants more — that's a new pass, and the choice below applies again
- tell the user what's there either way, in one line: which pass, where it stands, what carried over

### Choose this pass

Decide from what the user brought, then confirm it with them before bootstrapping:

- **enactment** — they supplied findings and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **discovery** — no finding set to measure against; the goal is what the project is vulnerable to, in the whole project or in what a diff or spec names. "Find vulnerabilities", "scan this app", "did this PR introduce anything?"
- **onboarding** — the tree has never been onboarded and the user wants the project's own rule and model corpus built before anything is measured. Recommend it on a cold start when the run is not urgent; it is the pass that makes the others accurate

The signal for enactment is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is discovery.

When the user wants both — reproduce the report *and* find what it missed — say that it is two passes over one tree, recommend enactment first so the discovery pass inherits its boundaries, and run them one at a time. Never try to drive two modes in a single pass.

## Setup

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Choose the mode and locate its input

Pick `onboarding`, `discovery`, or `enactment` per Modes, confirm the choice with the user, and get the path its intake needs — the supplied findings for enactment, the diff or spec for discovery when there is one. Onboarding needs no input beyond the project.

### 4. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves. When a repo carries build markers for more than one, ask the user which to analyze.

### 5. Choose the workflow

Ask the user for the knobs this mode has, together:

1. Scan level — `lite` · `normal` · `deep`, **discovery mode only**
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom models
   - deep — build + scan + custom models + custom universal rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior pass's artifacts already present → lite
   - onboarding and enactment are always deep: sweeping the frontier and reproducing a finding set both need the full rule and model toolbox, so there is no level to ask for
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 6. Bootstrap

Seed the run state and the working tree:

```bash
uv run <skill-dir>/scripts/generate.py init --mode <onboarding|discovery|enactment> \
  --triage-level <static|dynamic> --language <lang> \
  [--scan-level <lite|normal|deep>] [--findings <path>] [--spec <path>]
```

`--scan-level` is discovery's; `--findings` is enactment's and required the first time; `--spec` is discovery's and optional. It writes `state.yaml`, appends this pass to `history.yaml`, and creates the `.opentaint/` tree — plus `tracking/reference/` in enactment mode.

Over a tree an earlier pass already built, it prints what carried over and keeps all of it — that pass's rules, models, boundary specs, and verdicts are this pass's starting corpus, and `get_status.py` will report their phases `DONE` rather than redoing them. It refuses a second onboarding pass over an already-onboarded tree.

## Workflow

The run is one fixed pipeline, the same in every mode; the mode decides what intake works from, and the selected levels decide which phases are in scope. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
intake                      → stage subagent: intake
boundaries                  → stage subagent: boundaries
source_rules                → stage subagent: sources
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
sink_rules                  → stage subagent: sinks, then MAIN: rescan
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref   (whenever the tree carries a reference set)
```

The spine is fixed — build, sources, scan, models, sinks, triage — and it is fixed for a reason. Both boundary sides are known before the first scan, because that scan is what proves them and names the taint frontier the model work then answers; the sink rules are authored against that frontier rather than guessed ahead of it. Never let a model stand in for a boundary that was never authored: an approximation carries taint through a carrier, it does not decide what is untrusted or what is dangerous.

`crossref` appears whenever the tree carries a reference set — the pass that supplied it need not be this one. This pass's rescans changed what those findings reproduce, so re-judging them and refreshing `.opentaint/enactment.md` is part of finishing, not optional cleanup.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model. Keep one untouched model for the whole pass.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/model; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed model, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.

### Iterating

The pipeline loops by design, and status is what closes it. A rescan makes every cross-reference pending again; a trace stopped at an opaque carrier sends the run back to a model round; a rule blamed for a miss goes back to the stage that authored it, so status returns there before closing again. Follow status through each loop rather than declaring the run finished early — an earlier phase reading `IN_PROGRESS` after a later one ran is the loop working, not a regression.

The run is complete when status reports `run complete`: `.opentaint/vulnerabilities.md` current, and — where the tree carries a reference set — every supplied finding either reproduced or recorded with the blocker that stopped it, in `.opentaint/enactment.md`. Report the outcome keeping raw SARIF results, validated findings, and unique vulnerability identities as separate counts.

## Dispatching

Dispatch exactly one stage-orchestrator subagent for each stage invocation:

```
Invoke the Skill orchestrate-stage first, then follow its instructions precisely
Inputs:
  stage: <intake|boundaries|sources|approx-round|sinks|triage|poc|crossref|escalation>
```

For a `deep` model round, also pass `sinks: true`. A subagent inherits the project-root working directory, so omit `project-root`.

Stage context:

- `intake` — turn this mode's input into the run's families: the swept frontier in onboarding, the diff or spec in discovery, the normalized reference set in enactment
- `boundaries` — generalize each family into one universal source and one universal sink, and seed the rule units from them
- `sources` — author the seeded source units' rules and wire the joins
- `approx-round` — classify and build one dropped-method frontier; use a fresh agent for each new frontier
- `sinks` — author the seeded sink units' rules and wire the joins
- `triage` — classify the latest findings and refresh the vulnerability report
- `crossref` — judge a reference set against the latest scan and refresh its coverage manifest
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
  tracking/scope.yaml    intake stage (onboarding, discovery)
  tracking/reference/    intake stage writes, crossref stage judges (enactment)
  tracking/boundaries/   boundaries stage
  tracking/              stage agents, leaves, and join scripts otherwise
  enactment.md           crossref stage
  vulnerabilities.md     triage / PoC stage
  issues/                escalation stage
```

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and models apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an onboarding pass's classification ledger, a discovery pass's boundary specs, and an enactment pass's reference set are all as durable as your own.

`state.yaml` shape — `mode` is this pass's intake, not a property of the tree, so a later pass in another mode simply rewrites it and keeps everything else:

```yaml
mode: enactment
scan_level: deep
triage_level: dynamic
language: java
findings: reports/pentest-2026-07.md
spec: null
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```

`findings` is the supplied set an enactment pass is measured against and `spec` is what a discovery pass was scoped by; both stay in `state.yaml` across passes in other modes, so a later pass in that mode resumes the same input. Neither is edited by hand mid-pass — pointing an in-flight pass at a different file strands the intake built from the old one. A genuinely different input is a new pass, bootstrapped with a new `--findings` or `--spec`.

## Key constraints

- read pipeline state through `<skill-dir>/scripts/get_status.py`, not by hand — don't re-derive it with glob/grep/`python3 -c`/yaml scans over `.opentaint/tracking`, `results`, or the `*.yaml`, nor open finding/unit/reference/SARIF files just to review progress. If its output doesn't settle the question, re-run it with `--full` before opening any file
- don't author or edit stage-owned artifacts or tracking; MAIN writes only `model_commit`, `build_jdk`, and `max_memory` in `state.yaml`
- keep one generated project model for the run; never hand-edit or replace it mid-analysis — fix the build and rebuild before starting a new run
- source and sink boundaries come before model work; a model never compensates for a boundary that was never authored
- run one mode per pass, and never switch `mode` mid-pass: the intake behind the current families would no longer be the one on disk
- where the tree carries a reference set, coverage is counted by unique finding identity, never by rule id or raw SARIF result count, and a result counts as a reproduction only when its trace carries the finding's own attack path
- never drop a supplied finding as unsuitable for taint analysis
