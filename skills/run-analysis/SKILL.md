---
name: run-analysis
description: Run an OpenTaint scan on a built project model and produce the SARIF report plus the taint-killing-method YAMLs used for iteration. Use whenever the user asks to scan or re-scan a project.
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.1"
---

# Skill: Run Analysis

Run OpenTaint analysis on the target project and collect results

## Prerequisites

- Project built (build-project skill) — model at `.opentaint/project/`
- Rules created and tested (create-rule, test-rule skills) — at `.opentaint/rules/`
- Optionally: YAML config (create-yaml-config skill) at `.opentaint/config/` and/or approximations (create-approximation skill) at `.opentaint/approximations/`

## Procedure

### Basic analysis

The `--rule-id` flag requires the **full rule ID** in the format `<ruleSetRelativePath>.yaml:<id>`. Example: for a rule file at `.opentaint/rules/java/security/my-vuln.yaml` with `id: my-vulnerability`, the full ID is `java/security/my-vuln.yaml:my-vulnerability`.

Pass the pre-compiled project model via `--project-model`. The positional `scan <path>` argument is reserved for source projects that the CLI will compile itself.

```bash
opentaint scan --project-model .opentaint/project \
  -o .opentaint/results/report.sarif \
  --ruleset builtin \
  --ruleset .opentaint/rules \
  --rule-id java/security/my-vuln.yaml:my-vulnerability \
  --track-external-methods
```

### With custom passThrough config

`--approximations-config` is repeatable; every occurrence is OVERRIDE-merged.

```bash
opentaint scan --project-model .opentaint/project \
  -o .opentaint/results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --rule-id java/security/my-vuln.yaml:my-vulnerability \
  --approximations-config .opentaint/config/custom-propagators.yaml \
  --track-external-methods
```

### With code-based approximations

Point `--dataflow-approximations` at a directory of Java sources. The CLI auto-compiles `.java` files into a temp directory and forwards that to the analyzer.

```bash
opentaint scan --project-model .opentaint/project \
  -o .opentaint/results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --rule-id java/security/my-vuln.yaml:my-vulnerability \
  --dataflow-approximations .opentaint/approximations/src \
  --track-external-methods
```

### View results

```bash
opentaint summary .opentaint/results/report.sarif --show-findings
```

## Outputs

Three files to collect — all next to the SARIF report:

1. **`.opentaint/results/report.sarif`** — Vulnerability findings with code flow traces
2. **`.opentaint/results/external-methods-without-rules.yaml`** — Methods where no pass-through rules fired (**dataflow facts killed here — these cause false negatives**)
3. **`.opentaint/results/external-methods-with-rules.yaml`** — Methods where pass-through rules were applied (already modeled, typically no action needed)

The `--track-external-methods` flag is a boolean. Filenames and location are fixed: the two YAMLs are written into the same directory as the SARIF file, using the names above.

## Key Flags

| Flag | Purpose |
|------|---------|
| `--project-model` | Pre-compiled project model directory (contains `project.yaml`) |
| `--ruleset` | Rule directory (repeatable). Use `builtin` for built-in rules |
| `--rule-id` | Enable only specific rules by full ID `<path>.yaml:<id>` (repeatable) |
| `--approximations-config` | YAML passThrough config (repeatable; all files merged, combined result replaces the entire built-in passThrough list) |
| `--dataflow-approximations` | Directory of Java sources or compiled class files (repeatable) |
| `--track-external-methods` | Emit `external-methods-{without,with}-rules.yaml` next to the SARIF |
| `--severity` | Filter by severity (note, warning, error) |
| `--timeout` | Analysis timeout (default 900s) |

## Notes

- For a pre-compiled model, always use `--project-model <dir>`. The positional argument is only for source projects that will be compiled by the CLI.
- `--rule-id` drops every rule whose full ID is not in the filter, **including library rules referenced via join-mode `refs`**. List every rule you want active explicitly.
- `--approximations-config` is repeatable; all supplied files are merged into one combined config, which then replaces the **entire** built-in passThrough list. If you pass any `--approximations-config`, no built-in passThrough entry is active — your files must cover everything you need.
- `--dataflow-approximations` accepts a directory. `.java` files are auto-compiled by the CLI; already-compiled `.class` directories are passed through as-is.
- Duplicate approximation targeting the same class as a built-in will cause an error.
