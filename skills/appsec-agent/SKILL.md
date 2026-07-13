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

Keep every artifact under one `.opentaint/` directory at the project root — models, rules, configs, approximations, test projects, results, tracking, PoCs, reports. Don't scatter files outside it.

## Setup

Before anything else, confirm `opentaint` is on PATH (`command -v opentaint` / `opentaint --version`). If it's missing, don't proceed silently — tell the user and ask to install it, offering the command for their platform; run an install only on explicit confirmation:

macOS / Linux — try in order:

1. Homebrew — `brew install --cask seqra/tap/opentaint`
2. npm — `npm install -g @seqra/opentaint`

Windows:

1. npm — `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm the autobuilder/analyzer/rules/runtime resolve.

## Choose a workflow

Begin by asking the user both things in a single AskUserQuestion call — two questions, scan level and triage level, presented together (never one call then another). Record the chosen `scan_level` and `triage_level` in `state.yaml`:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan with existing rules
   - normal — + approximation iteration
   - deep — + discover-attack-surface for project-used dependency members + new rules (fixed first)
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — + a PoC per confirmed TP. This launches a few test services on the user's current machine (local instances and ports); they're torn down at the end of the run. Make that clear in the option

The run is one fixed pipeline; the two levels decide which steps execute. Walk it top to bottom — when you reach a step your levels include, load its reference and do it; skip the bracketed steps your levels omit. Don't load a step's reference until you reach it.

```
build                                    → references/build.md           every run
[deep] discover project-used lib rules   → references/discover-rules.md  deep scan
scan                                     → references/scan.md            every run
[normal/deep] approximation iteration    → references/approximations.md  normal, deep scan
triage (generate findings + classify)    → references/triage.md          every run
[dynamic] PoC + assemble vulnerabilities → references/poc.md             dynamic triage
```

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
- only run-scan scans the main project model; rule/approximation/triage subagents don't — the one exception is a create-rule agent running a diagnostic `--track-external-methods` scan of its own test project (never the main model)
- only you write `.opentaint/vulnerabilities.md` and `.opentaint/tracking/state.yaml`
- never swap the project model mid-analysis; every run uses the same model
- never triage yourself — verdicts come only from analyze-findings subagents

Orchestration practices:

- Units fan out in parallel — independent `<name>` paths, no races
- the sole sequential exception is PoC (shared app state and ports); see references/poc.md
- Steps within a unit are sequential via the artifact on disk — dispatch step N only after step N−1's named artifact exists; never bundle steps into one dispatch
- write `state.yaml` at each fan-out join — a phase flips to `done` only once every unit's artifact exists on disk

## Resource limits

Two limits apply to every fan-out — a global one against rate-limiting, and a tighter one against memory:

- Global cap of 7 — never dispatch more than 7 subagents at once, of any kind. Bursting more reliably trips transient rate-limiting. It binds light and heavy agents alike. Treat 7 as a starting ceiling: each time a subagent comes back rate-limited, drop the cap by 1 for the rest of the run
- RAM-heavy agents each spawn a heavy `opentaint` JVM, so they take a tighter memory bound on top of the global cap. The heavy set is exactly `build-project`, `run-scan`, `create-rule`, `create-dataflow-approximation`, and sometimes `debug-rule` (when it traces a real scan). Compute the bound at run start and never dispatch more than this many heavy subagents at once:
  - cores — `nproc` (Linux) / `sysctl -n hw.ncpu` (macOS)
  - free memory in GB — `free -g` (Linux, the `available` column) / `sysctl -n hw.memsize` ÷ 1024³ (macOS)
  - `cap_heavy = max(1, min(cores, floor(free_GB / 2), 7))` — budget ~2 GB per concurrent JVM
- Every other agent is not RAM-bound — discover-attack-surface, create-test-project (compiles once), triage-dependencies, analyze-external-methods, analyze-findings, create-pass-through-approximation, assemble-lib-rules, generate-poc. They're held only by the global cap of 7

It's machine state, not run state — recompute on resume, don't track it. PoC is already sequential.

## State and resumption

You are the only writer of `.opentaint/tracking/state.yaml` — it records the chosen levels and every phase's status, written after each fan-out join.

On start, and after any compaction, reconstruct position from artifacts before doing anything — never replay a completed phase:

- read `state.yaml` and the `tracking/` tree
- skip any phase whose artifact exists: `project.yaml` → build; `coverage.yaml` with every entry `done` → discover; a lib unit's `tests_passing: done` → that package's lib rules, and a `rules/join/<class>.yaml` per vuln class → joins assembled; `report.sarif` → scan; an approximation unit's `artifact` (plus `tests_passing` for dataflow) → that unit; a finding with `verdict` set → triaged; with `poc` set → PoC'd
- detect new work from artifacts, not memory: finding files with `verdict: pending` (a fresh or reset scan) → triage; methods in `dropped-external-methods.yaml` not yet in any approximation unit → approximations

## Tracking layout

The single source of truth for the tracking schema; each skill writes only its own slice (named in its block reference). The `#` comments in the YAML below are for understanding only — never copy them into produced files.

```
.opentaint/tracking/
  state.yaml                              # you only — levels + phase status
  coverage.yaml                           # triage-dependencies seeds, discover-attack-surface flips — one entry per dependency package weighed (deep)
  usage/<package-kebab>.yaml              # discover-attack-surface writes project-used package members (deep)
  findings/<finding_name>.yaml            # one per logical finding (from the SARIF→finding script; split by triage)
  rules/lib/<package-kebab>.yaml          # per-package project-used rule plan — new source/sink lib rules (discover plans; create-* build + test vs the marker) (deep)
  rules/join/<class>.yaml                 # per-vuln-class security join (assemble-lib-rules writes; main scan verifies) (deep)
  approximations/<package-kebab>-passthrough.yaml   # simple from→to copies; write-only, scan-verified
  approximations/<package-kebab>-dataflow.yaml      # lambda/callback/async; tested on a test project
  approximations/skipped.yaml             # methods the engine asks for but that carry no taint
  poc-servers.yaml                        # generate-poc — instances it started; you reap them at end of PoC phase
```

state.yaml:

```yaml
scan_level: deep        # lite | normal | deep
triage_level: dynamic   # static | dynamic
phases:                 # pending | in_progress | done
  build: done
  discover: done        # deep only
  rules: done           # deep only; fixed first
  scan: done
  approximations: in_progress  # normal/deep; iterative, rescans within
  triage: pending
  poc: pending          # dynamic triage
```

coverage.yaml — seeded by triage-dependencies and flipped by discover-attack-surface (deep): one entry per dependency package weighed, so you can see which libraries were drilled and which were dismissed. A `pending` entry is a flagged library awaiting its depth pass; the rule plan lives in `rules/lib/<package-kebab>.yaml`, not here:

```yaml
packages:
  - package: org.springframework.web.reactive.function
    status: done          # pending (flagged, awaiting depth) | done (drilled or dismissed)
    notes: >
      free-form — what was found and why
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

rules/lib/<package-kebab>.yaml — per-package rule plan for project-used sources/sinks only; `description` fields + `sources`/`sinks` by discover-attack-surface, `test_project` by create-test-project, `tests_passing` + `rule_id`s + `artifact` by create-rule. `coverage: new` ⇒ write a pattern, `expand` ⇒ ref the built-in plus the missing used methods:

```yaml
package: org.springframework.web.reactive.function.client
dependencies: [org.springframework:spring-webflux:6.1.0]
builtin_coverage: partial   # partial | none
artifact: null              # create-rule
sources:
  - idea: ServerRequest body/params — untrusted request data
    coverage: new           # new | expand
    builtin: null
    rule_id: null
sinks:
  - vuln_class: ssrf
    idea: WebClient.post/put().uri($UNTRUSTED)
    coverage: expand
    builtin: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
    rule_id: null
stages:                 # pending | in_progress | done
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

rules/join/<class>.yaml — one file per vuln class, written by assemble-lib-rules after the lib rules exist and verified by the main scan. A join references exactly ONE sink rule, so a class with several sinks holds several joins — one entry under `joins:` per sink rule, each its own file/id:

```yaml
name: ssrf
sources:
  - ref: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - ref: java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml:ssrf-webclient-ssrf-sink-lib-ext
    artifact: .opentaint/rules/java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml
    sink: { new: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink }
  - rule_id: java/security/ssrf-java-ssrf-sink-lib-ext.yaml:ssrf-java-ssrf-sink-lib-ext
    artifact: .opentaint/rules/java/security/ssrf-java-ssrf-sink-lib-ext.yaml
    sink: { builtin: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink }
stages:                 # pending | in_progress | done
  written: done
  verified: pending
notes: >
  free-form
```

approximations/<package-kebab>-<kind>.yaml — created by analyze-external-methods (`description` + `methods`); `<package-kebab>` = the dotted package with `.` -> `-` (the YAML `package:` field keeps the real dotted name). The stages differ by kind:

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
  pass-through/<name>.yaml      # passThrough approximation configs
  dataflow/<name>/              # code-based (dataflow) approximation sources, per unit
  test-projects/<name>/         # per-unit test project sources; a rule unit holds sinks/ and sources/ sub-projects, each with a test-rules/ (the generic markers + that side's test join — test-only, never loaded by the main scan)
  test-compiled/<name>/         # per-unit compiled test model (a rule unit: sinks/ and sources/ models); delete once the unit's tests pass — large and unused after
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

- the engine models stored / second-order injection (data persisted then read back) on its own — no source, sink-side, or propagator needs to be added for the store→read path
- approximations apply only to external library methods — never an application-internal class
- `--passthrough-approximations` merges with built-ins at the rule level; a provided rule overrides a built-in only when it matches one already there — it does not replace the built-in set
- both approximation dir flags walk the tree recursively, so the final scan points at the parent dirs and applies every unit
- `--rule-id` drops every rule not named, including library `refs` — list them all when restricting
- a custom DATAFLOW approximation targeting a class that already has a built-in dataflow approximation errors at load (one class, one approximation); passThrough configs never error this way — they merge at the rule level (see above)
- a custom dataflow approximation overrides a passThrough for the same method — the passThrough→dataflow fallback when a passThrough won't converge; remove that method's passThrough config when re-planning it as dataflow, before the dataflow one is tested or scanned, to avoid override issues
