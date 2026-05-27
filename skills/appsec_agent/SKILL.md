---
name: appsec_agent
description: Run an end-to-end application-security analysis on a JVM project with OpenTaint — build, scan, model missing library methods, triage, and confirm vulnerabilities. Use when the user asks to find vulnerabilities, run SAST, or scan a Java/Kotlin app for security issues
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# AppSec Agent

Orchestrate an end-to-end OpenTaint analysis of a JVM project: run the workflow the user picks by dispatching each step to a subagent that loads one leaf skill, verifying the artifact it returns, and tracking progress. The leaf work is never done here. OpenTaint is a dataflow (taint) SAST analyzer; the goal is real, confirmed vulnerabilities.

The run is one pipeline of a few steps, each gated by the chosen workflow; a step's detail lives in a reference loaded when you reach it, while what every workflow shares stays in this file. Default to the current directory when no target is named.

Keep every artifact under one `.opentaint/` directory at the project root — models, rules, configs, approximations, test projects, results, tracking, PoCs, reports. Don't scatter files outside it.

## Setup

Run `opentaint dev rules-path` once to learn the built-in rules directory; built-ins always load, custom rules go under `.opentaint/rules`.

## Choose a workflow

Begin by asking the user which workflow to run — a single AskUserQuestion offering the presets only, each option's description giving its composition:

- fast — scan: lite, triage: static
- default — scan: normal, triage: static, suppress-FP: optional
- ultra — scan: deep, triage: dynamic, suppress-FP: on
- reproduce-vulnerability — anchored on a vulnerability the user asserts exists; deep scan + dynamic triage

The tool adds an Other choice; if the user takes it, ask for any custom steps — a custom combination of scan level (lite/normal/deep), triage level (static/dynamic), and suppress-FP (on/off). Record the resolved levels in `state.yaml`.

Levels, once chosen:

- scan — lite (build + scan with existing rules) · normal (+ approximation iteration) · deep (+ discover-attack-surface + new rules, fixed first)
- triage — static (classify from the model) · dynamic (+ a PoC per confirmed TP)
- suppress-FP — a post-triage stage that fixes confirmed false positives on rules you own

The run is one fixed pipeline; the levels decide which steps execute. Walk it top to bottom — when you reach a step your levels include, load its reference and do it; skip the bracketed steps your levels omit. Don't load a step's reference until you reach it.

```
build                                    → references/build.md           every level
[deep] discover + new rules              → references/discover-rules.md  deep
scan                                     → references/scan.md            every level
[normal/deep] approximation iteration    → references/approximations.md  normal, deep
triage (generate findings + classify)    → references/triage.md          every level
[suppress-FP]                            → references/suppress-fp.md     when suppress-FP is on
[dynamic] PoC + assemble vulnerabilities → references/poc.md             dynamic
```

Which steps each preset runs:

- fast — build, scan, triage
- default — build, scan, approximations, triage, [suppress-FP]
- ultra — build, discover-rules, scan, approximations, triage, suppress-FP, poc
- reproduce-vulnerability — references/reproduce-vulnerability.md walks the same steps anchored on the asserted vuln

From inside any step, when a rule or approximation won't behave, load references/escalation.md. Only the approximation iteration loops (it re-scans internally); new rules are fixed before it.

## Delegation

Every block's work runs in subagents. Dispatch each with this template:

```
Invoke the Skill tool with skill_id=<skill-name> first, then do the task.
Inputs:
  <name>: <resolved path or value>     # one line per input the skill lists
Return:
  <the skill's Output>, plus the exact command you ran to verify
Do not run `opentaint scan`. Do not write `.opentaint/vulnerabilities.md`.
```

Universal rules — every dispatch, every workflow:

- open the prompt with the Skill-load line — the subagent has none of this context until it loads its skill
- pass resolved paths (the `<name>`-keyed `.opentaint/...` paths from Working directory layout), never the placeholder tokens
- read the named output artifact yourself before continuing — a claim is not an artifact
- only the scan agent (run-scan) runs `opentaint scan`; no rule, approximation, or triage subagent scans
- only you write `.opentaint/vulnerabilities.md` and `.opentaint/tracking/state.yaml`
- never swap the project model mid-analysis; every run uses the same model
- never triage yourself — verdicts come only from analyze-findings subagents

Orchestration practices:

- one unit, one subagent — rules, approximation units, and finding files are independent (unique `<name>` paths), so dispatch them as a parallel fan-out, no races
- the sole sequential exception is PoC (shared app state and ports); see references/poc.md
- write `state.yaml` at each fan-out join — a phase flips to `done` only once every unit's artifact exists on disk

## State and resumption

You are the only writer of `.opentaint/tracking/state.yaml` — it records the chosen levels and every phase's status, written after each fan-out join.

On start, and after any compaction, reconstruct position from artifacts before doing anything — never replay a completed phase:

- read `state.yaml` and the `tracking/` tree
- skip any phase whose artifact exists: `project.yaml` → build; `report.sarif` → scan; a rule's `artifact` + `tests_passing: done` → that rule; an approximation unit's `artifact` (plus `tests_passing` for dataflow) → that unit; a finding with `verdict` set → triaged; with `poc` set → PoC'd
- detect new work from artifacts, not memory: finding files with `verdict: pending` (a fresh or reset scan) → triage; methods in `dropped-external-methods.yaml` not yet in any approximation unit → approximations

## Tracking layout

The single source of truth for the tracking schema; each skill writes only its own slice (named in its block reference).

```
.opentaint/tracking/
  state.yaml                              # you only — levels + phase status
  findings/<finding_name>.yaml            # one per logical finding (from the SARIF→finding script; split by triage)
  rules/<name>.yaml                       # one per rule
  approximations/<package>-passthrough.yaml   # simple from→to copies; write-only, scan-verified
  approximations/<package>-dataflow.yaml      # lambda/callback/async; tested on a test project
  approximations/skipped.yaml             # methods the engine asks for but that carry no taint
```

state.yaml:

```yaml
mode: ultra             # fast | default | ultra | reproduce-vulnerability | custom
scan_level: deep        # lite | normal | deep
triage_level: dynamic   # static | dynamic
suppress_fp: true
phases:                 # pending | in_progress | done
  build: done
  discover: done        # deep only
  rules: done           # deep only; fixed first
  scan: done
  approximations: in_progress  # normal/deep; iterative, rescans within
  triage: pending
  suppress_fp: pending  # after triage
  poc: pending          # dynamic triage
```

findings/<finding_name>.yaml — created by the SARIF→finding script; `verdict`/`notes` by analyze-findings; `poc`/`poc_script` by generate-poc:

```yaml
finding_name: brave-hopper
sarif_hashes: [<hash>, ...]
rule_id: java/security/sqli.yaml:sqli
verdict: pending        # pending | TP | FP
notes: >                # analyzer report, then triage and PoC notes
  <analyzer report>
poc: pending            # pending | confirmed | failed
poc_script: null        # path under .opentaint/pocs/ once generate-poc writes one
```

rules/<name>.yaml — created by discover-attack-surface (`description`); `test_project` by create-test-project; `tests_passing` + `rule_id` + `artifact` by create-rule:

```yaml
name: mybatis-sqli
rule_id: null           # filled on creation
artifact: null          # added once the rule file exists
finding: null           # finding_name; non-null only for suppress-FP
requirements: >
  CWE-89 SQLi via MyBatis ${} ; source @RequestParam orderBy ; sink ${} in SelectProvider
dependencies: [org.mybatis:mybatis:3.5.13]
stages:                 # pending | in_progress | done
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

approximations/<package>-<kind>.yaml — created by analyze-external-methods (`description` + `methods`); the stages differ by kind:

```yaml
package: com.foo
artifact: null          # added once the file exists
stages:
  description: done
  written: pending      # passthrough only (write-only, scan-verified)
  # test_project / tests_passing  # dataflow only (built and tested)
# dependencies: [...]   # dataflow only — the GAVs its test project needs
methods:
  - target: "com.foo.Wrapper#getValue"
    type: passthrough   # passthrough | dataflow (matches the file kind)
notes: >
  free-form
```

approximations/skipped.yaml:

```yaml
methods:                # engine asks to approximate these, but they carry no taint
  - "org.slf4j.Logger#info"
```

## Working directory layout

```
<project-root>/.opentaint/
  project/                      # built project model (project.yaml)
  rules/java/{lib/generic,lib/spring,security}/   # custom rules
  config/<name>.yaml            # passThrough approximation configs
  approximations/src/<name>/    # code-based (dataflow) approximation sources
  test-projects/<name>/         # per-unit test project sources
  test-compiled/<name>/         # per-unit compiled test model
  test-results/<name>/          # per-unit test outputs
  results/
    report.sarif
    dropped-external-methods.yaml       # taint-killing methods → approximate
    approximated-external-methods.yaml  # already modeled
  pocs/<finding_name>.py        # PoC scripts
  issues/<slug>.md              # engine-issue reports
  tracking/                     # see Tracking layout
  vulnerabilities.md            # you assemble this from confirmed findings
```

## Key constraints

- approximations apply only to external library methods — never an application-internal class
- `--passthrough-approximations` merges with built-ins at the rule level; a provided rule overrides a built-in only when it matches one already there — it does not replace the built-in set
- both approximation dir flags walk the tree recursively, so the final scan points at the parent dirs and applies every unit
- `--rule-id` drops every rule not named, including library `refs` — list them all when restricting
- a custom approximation targeting a class that already has a built-in one errors at load
