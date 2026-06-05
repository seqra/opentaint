---
name: run-scan
description: Run an OpenTaint scan on project and produces the SARIF report. Use whenever the user asks to scan or re-scan a project
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Run Scan

Run an OpenTaint scan over a project and collect results

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Target `<model-dir>` / `<project-src>` — pre-compiled model or source project directory. Default: model at `.opentaint/project`
- Ruleset `<rules-dir>` — Default: `builtin` plus `.opentaint/rules` if present
- Rule IDs `<full-id>` (optional) — full IDs to restrict the scan to, omit to run all loaded rules
- SARIF output `<report.sarif>` — Default: `.opentaint/results/report.sarif`
- PassThrough config `<config-dir>` (optional) — a passThrough YAML file or a directory of them. Default: `.opentaint/pass-through`
- Dataflow approximations directory `<approx-dir>` (optional) — Default: `.opentaint/dataflow`

## Workflow

Point at the code either way: a source project (CLI compiles it) as the positional `scan <project-src>`, or a pre-built model via `--project-model <model-dir>`. If project model provided prefer using it instead of source project

```bash
opentaint scan --project-model <model-dir> \
  -o <report.sarif> \
  --ruleset builtin --ruleset <rules-dir> \
  --track-external-methods
```

Append optional flags as needed:

- `--rule-id <full-id>` — restrict to specific rules (repeatable); omit to run all loaded rules
- `--passthrough-approximations <config-dir>` — apply passThrough configs from a YAML file or a directory of them (OVERRIDE: merged with built-ins at the rule level, a provided rule overrides a built-in only when it matches one; repeatable)
- `--dataflow-approximations <approx-dir>` — apply code-based approximations (Java sources, auto-compiled; or pre-compiled `.class` dirs, passed through as-is)

## Output

Three files, all next to the SARIF report:

1. `<report.sarif>` — findings with code-flow traces
2. `dropped-external-methods.yaml` — methods where dataflow facts were killed (no approximation model) → candidates to approximate; possible source of false negatives
3. `approximated-external-methods.yaml` — methods already modeled

## Key Flags

| Flag | Purpose |
|---|---|
| `--project-model` | Pre-compiled model directory (omit to scan a source project via the positional arg) |
| `--ruleset` | Rule directory (repeatable); `builtin` for built-ins |
| `--rule-id` | Restrict to specific full rule IDs (repeatable) |
| `--passthrough-approximations` | passThrough configs: a YAML file or directory of them (OVERRIDE, repeatable) |
| `--dataflow-approximations` | Directory of Java sources or compiled classes (repeatable) |
| `--track-external-methods` | Emit `dropped-external-methods.yaml` + `approximated-external-methods.yaml` next to the SARIF |
| `--timeout` | Analysis timeout (default 900s) |

## Gotchas

- Paths fall back to the `.opentaint/` layout when the caller omits them; the caller can override any of them
- Duplicate approximation targeting the same class as a built-in errors out
