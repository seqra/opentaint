---
name: debug-rule-reachability
description: Produce a fact-reachability SARIF for one OpenTaint rule to see exactly where its dataflow facts get killed. Use when a rule passes its tests but still misses (or spuriously fires) on the real project.
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.1"
---

# Skill: Debug Rule Reachability

Generate a fact reachability SARIF report to debug why a specific rule does (or doesn't) reach certain taint sinks

## Prerequisites

- Project model available — path provided by caller (`.opentaint/project/` from main pipeline, `.opentaint/test-compiled/` when called from `opentaint-issue-investigation`)
- Rule created and tested (create-rule, test-rule skills)

## ⚠️ CRITICAL: Single Rule Only

This command targets exactly ONE rule. Running fact reachability across multiple rules would produce an enormously huge SARIF report that is effectively unusable; the dedicated `opentaint dev debug-fact-reachability` command takes a single rule ID as its required argument.

## Procedure

### Run the debug command

`opentaint dev debug-fact-reachability` is a separate command (not a flag on `scan`). It takes the full rule ID as its first positional argument and the source path (or a pre-compiled model via `--project-model`) as the second.

```bash
opentaint dev debug-fact-reachability \
  java/security/my-vuln.yaml:my-vulnerability \
  --project-model .opentaint/project \
  -o .opentaint/results/fact-reachability.sarif \
  --ruleset builtin --ruleset .opentaint/rules
```

The rule ID requires the **full rule ID** in the format `<ruleSetRelativePath>:<shortId>`. Example: for a rule file at `.opentaint/rules/java/security/my-vuln.yaml` with `id: my-vulnerability`, the full ID is `java/security/my-vuln.yaml:my-vulnerability`.

### View results

```bash
opentaint summary .opentaint/results/fact-reachability.sarif --show-findings
```

## Key Flags

| Flag/Arg | Purpose |
|------|---------|
| `<rule-id>` (positional) | **Exactly one** full rule ID (`<path>.yaml:<id>`) — required |
| `--project-model` | Pre-compiled project model directory (skip recompilation) |
| `-o` | Path to the main SARIF output file |
| `--ruleset` | Rule directory (repeatable). Use `builtin` for built-in rules |
| `--timeout` | Analysis timeout (default 15m) |

## Outputs

The fact reachability report is **not** the main SARIF file specified by `-o`. The analyzer writes it as a **separate file** named `debug-ifds-fact-reachability.sarif` in the same output directory as the main report.

For example, with `-o .opentaint/results/fact-reachability.sarif`:

- **`.opentaint/results/fact-reachability.sarif`** — Main vulnerability findings for the single rule
- **`.opentaint/results/debug-ifds-fact-reachability.sarif`** — Debug fact reachability report

Always check the output directory (`-o` parent) for this file.

## Notes

- This is a debug-only command intended for troubleshooting rule coverage
- Pre-compiled project models are passed via `--project-model <dir>`; otherwise the second positional argument is a source-path that the CLI will compile
- The command implicitly restricts the run to the one rule given as the positional argument; library rules referenced via join-mode `refs` are still resolved as needed
