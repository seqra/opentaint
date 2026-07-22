---
name: report-analyzer-issue
description: Write a self-contained OpenTaint engine-issue report from an analysis diagnosis or a full-scan failure. Use when an engine-side issue needs a report
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Report Analyzer Issue

Turn a suspected engine-level problem into a self-contained `.opentaint/issues/<slug>.md` report. It runs no analysis of its own — it only writes the report from what the caller supplies. Two kinds:

- an `analysis` issue — a suspected engine-level taint-propagation problem the caller couldn't resolve with a rule or a model (the analyzer's result looks wrong)
- a `resource` issue — a full-project scan that produced no SARIF after its allowed retry, memory bound, or timeout backstop; no taint diagnosis, just the setup that triggered it so the engine team can reproduce

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `diagnosis` (required for `analysis`) — the caller's brief engine-level cause: roughly where taint appears to die and why. A short hand-off, not a proven trace
- `artifact` (required for `analysis`) — the rule or approximation the issue concerns: a rule's full id and ruleset, or the approximation's target method(s)
- `name` (optional, `analysis`) — the test-project name the artifact was traced on; its tree is `.opentaint/test-projects/<name>` and model `.opentaint/test-compiled/<name>`, cited so the engine team can reproduce
- `setup` (required for `resource`) — what was running when the scan failed without SARIF: the ruleset(s), approximation dirs, project model, final memory bound, timeout/backstop outcome, scan log, and commit hash (`git rev-parse HEAD`)

## Workflow

### 1. Gate

The inputs pick the kind: a `diagnosis` (+ `artifact`) is an `analysis` issue, a `setup` is a `resource` issue.

For an `analysis` issue, write from the caller's brief cause as supplied — don't verify, reproduce, or run anything yourself. This is a first-pass approximate hand-off to the engine team, not a proven diagnosis; whatever the caller gives is enough to write the report.

For a `resource` issue, the gate is simpler: the caller confirms the full-project scan completed its allowed retry/backstop without producing valid SARIF. No taint diagnosis is required — write the report from the setup.

### 2. Write the report

Write `.opentaint/issues/<slug>.md` — the self-contained deliverable, `<slug>` a short kebab-case symptom name. Open with a fixed header so the engine team can triage at a glance, then free-form detail below it.

Header (both kinds):

- Type — `analysis` or `resource`
- Setup — the exact command that reproduces it: the `opentaint test rule …` / `test approximation run` for `analysis`, or the failed `opentaint scan` for `resource`, each with its model, rulesets, and approximation dirs (plus final memory and timeout/backstop outcome for `resource`)
- Run logs — the run's log files, by path: for `analysis`, any debug log or fact-reachability SARIF the caller cited, if present; for `resource`, the scan's output log
- Minimal repro — the smallest set of files/folders that demonstrates it: for `analysis`, the test project `.opentaint/test-projects/<name>` if one was named; for `resource`, the project model, rulesets, and approximation dirs in play (with their rough size). A Go passThrough has no test project — cite the scan evidence instead: the config under test, the modeled method now absent from `dropped-external-methods.yaml` (and present in `approximated-external-methods.yaml`), the flow still missing from the scan SARIF, and a minimal standalone Go module wiring the modeled call between a real source and sink
- TL;DR — 2–3 sentences: the symptom, and for `analysis` where taint appears to die and what the engine should do instead

Below the header, free-form — whatever makes the case, at least:

- `analysis` — the `artifact` under test (rule id + ruleset, or approximation target method(s)); the caller's brief cause; observed vs expected and any fact-reachability trace, if the caller supplied them; a 1–3 sentence hypothesis of what the engine does wrong (a hypothesis, not a fix)
- `resource` — the model's rough size (classes/modules if known) and the commit hash (`git rev-parse HEAD`) it was built from

Keep it tight: the header plus about one screen of body.

## Output

### Artifacts

- `.opentaint/issues/<slug>.md` — the self-contained issue report (the deliverable)

### Summary

- the kind (`analysis` / `resource`) and the one-line symptom; for an `analysis` issue, where taint appears to die
