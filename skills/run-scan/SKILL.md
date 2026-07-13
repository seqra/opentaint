---
name: run-scan
description: Run an OpenTaint scan on project and produces the SARIF report. Use whenever the user asks to scan or re-scan a project
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Run Scan

Run an OpenTaint scan over the project model and collect its findings

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `rule-ids` (optional) — full rule IDs to restrict the scan to
- `max-memory` (optional) — a `--max-memory` value to run scan with. Default: unset (engine default `8G`)

## Workflow

### 1. Run the scan

Scan the pre-built model at `.opentaint/project`. Write the report to `.opentaint/results/report.sarif` and load both the built-in ruleset and the project's own rules under `.opentaint/rules`:

```bash
opentaint scan --project-model .opentaint/project \
  -o .opentaint/results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --track-external-methods
```

- `--rule-id <full-id>` — restrict to specific rules (repeatable, one per input rule ID); omit to run all loaded rules
- `--passthrough-approximations .opentaint/pass-through` — add when that directory exists: passThrough configs override built-ins at the rule level, a provided rule overriding a built-in only when it matches one
- `--dataflow-approximations .opentaint/dataflow` — add when that directory exists: code-based approximations (sources auto-compiled; pre-compiled `.class` dirs passed through as-is)

Leave `--timeout` at the engine default (900s) — don't shorten it, and don't kill the scan when it runs past: the CLI ends the analysis itself and writes whatever SARIF it has, so let it exit gracefully even if that runs a little over.

### 2. Retry once on out-of-memory

Start at the 8G default. Only after an out-of-memory failure, retry once with `--max-memory 16G` — never higher, more RAM won't improve results. One bump, no further. When the caller passed `max-memory`, run at it from the first attempt instead

### 3. Collect the report, or escalate

If a SARIF was produced — even alongside a timeout or OOM message — take it as-is and ignore the error, the results are already there. When the scan instead fails at config-load on a malformed approximation (e.g. an unexpected position modifier, a duplicate approximation class), it is not out-of-memory: don't retry at 16G — report the engine error and the offending file under `.opentaint/pass-through`/`.opentaint/dataflow` per Output, locating it from the error message (grep the artifacts for the reported symbol when the error doesn't name the file). Only when no valid SARIF comes out even at 16G is it a plain failure: report it per Output with the setup and don't retry beyond that one 16G attempt

## Output

Short and concise report of what was done

### Artifacts:

All three sit next to the report under `.opentaint/results/`:

- `.opentaint/results/report.sarif` — findings with code-flow traces
- `.opentaint/results/dropped-external-methods.yaml` — external methods where dataflow facts were killed for lack of a model
- `.opentaint/results/approximated-external-methods.yaml` — external methods already modeled

### Summary:

- finding count, and dropped-vs-approximated external-method counts
- whether memory was bumped to 16G
- if the scan failed at config-load on a malformed approximation: the engine error and the offending file under `.opentaint/pass-through` or `.opentaint/dataflow` (located from the error), so it can be fixed and rescanned — this is not an out-of-memory failure and 16G won't help
- if no SARIF came out even at 16G: that the scan is left failed, with the setup used (full scan command with ruleset, approximation dirs, model)

## Constraints

- Never hand-edit the project model to change scan results — this skill only reads it. If the model is wrong, rebuild it at the model stage rather than patching `project.yaml` or anything under it
