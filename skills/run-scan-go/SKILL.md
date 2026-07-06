---
name: run-scan-go
description: Run an OpenTaint scan on a Go project and produce the SARIF report. Use whenever the user asks to scan or re-scan a Go (go.mod) project
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Run Scan (Go)

Run an OpenTaint scan over a Go project and collect results

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Target `<model-dir>` / `<project-src>` — a pre-built model directory or the Go source project directory. Default: model at `.opentaint/project`
- Ruleset `<rules-dir>` — Default: `builtin` plus `.opentaint/rules` if present
- Rule IDs `<full-id>` (optional) — full IDs to restrict the scan to, omit to run all loaded rules
- SARIF output `<report.sarif>` — Default: `.opentaint/results/report.sarif`
- PassThrough config `<config-dir>` (optional) — a passThrough YAML file or a directory of them. Default: `.opentaint/pass-through`

## Precondition

`go` must be on PATH — the analyzer compiles Go through the Go toolchain (go-ssa-server) at scan time and a Go-only project hard-fails without it. Check `command -v go` before scanning

## Workflow

Point at the code either way: a Go source project (the CLI compiles it) as the positional `scan <project-src>`, or a pre-built model via `--project-model <model-dir>` (a directory containing `project.yaml`, not the file). If a model is provided prefer it over re-compiling the source

```bash
opentaint scan --project-model <model-dir> \
  -o <report.sarif> \
  --ruleset builtin --ruleset <rules-dir> \
  --track-external-methods
```

Source-directory form (no pre-built model):

```bash
opentaint scan <project-src> \
  -o <report.sarif> \
  --ruleset builtin --ruleset <rules-dir> \
  --track-external-methods
```

Append optional flags as needed:

- `--rule-id <full-id>` — restrict to specific rules (repeatable); omit to run all loaded rules
- `--passthrough-models <config-dir>` — apply Go passThrough configs from a YAML file or a directory of them (OVERRIDE: merged with built-ins at the rule level, a provided rule overrides a built-in only when it matches one; repeatable). The built-in `go-config` set is bundled in the analyzer; this flag adds custom configs on top
- `--timeout <duration>` — maximum wall-clock analysis time (default 15m, same flag as the JVM scan)
- `--max-memory <size>` — maximum analyzer heap size (default 8G)

There is no `--java-models` for Go — Go has no dataflow approximations

## Output

Three files, all next to the SARIF report:

1. `<report.sarif>` — findings with code-flow traces
2. `dropped-external-methods.yaml` — methods where dataflow facts were killed (no model) → candidates to approximate with a Go passThrough; possible source of false negatives
3. `approximated-external-methods.yaml` — methods already modeled

## Key Flags

| Flag | Purpose |
|---|---|
| `--project-model` | Pre-built model directory containing `project.yaml` (omit to scan a source project via the positional arg) |
| `--ruleset` | Rule directory or YAML file (repeatable); `builtin` for built-ins |
| `--rule-id` | Restrict to specific full rule IDs (repeatable) |
| `--passthrough-models` | Go passThrough configs: a YAML file or directory of them (OVERRIDE, repeatable) |
| `--track-external-methods` | Emit `dropped-external-methods.yaml` + `approximated-external-methods.yaml` next to the SARIF |
| `--timeout` | Maximum wall-clock analysis time (default 15m) |
| `--max-memory` | Maximum analyzer heap size (default 8G) |

## Gotchas

- `go` not on PATH → a Go-only scan hard-fails; install the toolchain
- `--project-model` points at a directory (holding `project.yaml`), never at the `project.yaml` file itself
- Paths fall back to the `.opentaint/` layout when the caller omits them; the caller can override any of them
- No dataflow approximations and no `--java-models` flag for Go — don't pass one
- Failures: analyzer exit codes are forwarded (252 unhandled exception, 253 out of memory, 254 timeout, 255 project configuration error — documented in `opentaint scan --help`). On 253/254 the CLI prints a ready-to-run retry command with doubled `--max-memory`/`--timeout`; operational failures print the log-file path — read that log before diagnosing
