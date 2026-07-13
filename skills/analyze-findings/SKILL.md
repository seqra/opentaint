---
name: analyze-findings
description: Triage OpenTaint findings — split a rule's results into distinct vulnerabilities and classify each true positive or false positive. Use when scan findings need a TP/FP verdict
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Analyze Findings

A finding file bundles all of one rule's results. Read each result's code flow, split the bundle into distinct vulnerabilities, and give each a TP/FP verdict on its own evidence

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Findings to triage `<findings>` — the finding tracking file(s); each bundles all of one rule's SARIF results in `sarif_hashes` 
- SARIF report `<report.sarif>` — the raw scan output holding the code-flow traces. Default: `.opentaint/results/report.sarif`

## Workflow

### 1. One result at a time — STOP checklist

For each hash in the bundle, before any verdict:

- found its SARIF result via `sarif_hashes` and read the raw `codeFlows[]`
- walk every step, source → hops → sink, confirming it's the same tainted value end to end
- judging each result on its own trace — no verdict shared across results just because they share the rule

### 2. Split the bundle into logical findings

The results in the file all fired one rule, but may be several different vulnerabilities. Keep results that are the same vulnerability (same sink, same essential flow) together as one finding; move genuinely distinct ones (different sink, or a different flow) into their own finding file with a new `finding_name` and their `sarif_hashes`

### 3. Classify and record

Verdict each logical finding from its flow:

- TP — the source is attacker-controlled, the sink is genuinely dangerous with that input, and nothing sanitizes it in between
- FP — a sanitizer/validator neutralizes it, the source isn't actually attacker-controlled (config, constant, server-set), the sink is safe for this input (parameterized, escaped), or the path is infeasible. Record which one

Set `verdict` and append the reasoning to `notes`, below the analyzer report already seeded there

## Output

- Each logical finding in its own file with `verdict` set and the rationale in `notes`
- A brief summary to the caller: one line per finding — name, verdict, one-clause reason

## Tracking

Editing an existing finding touches only `verdict` and `notes`. A split also creates a new finding file — give it the full shape, copying `rule_id` from the bundle and moving over the results' `sarif_hashes` and their analyzer report:

```yaml
finding_name: <new-slug>              # a fresh docker-like name for the split-off vuln
sarif_hashes: [<moved hash>, ...]     # hashes matching this logical vulnerability
rule_id: java/security/sqli.yaml:sqli # same rule as the bundle it came from
verdict: TP                           # pending | TP | FP
notes: >
  <analyzer report for these results — moved from the bundle>
  triage: @RequestParam orderBy is attacker-controlled; reaches ${} in SelectProvider unsanitized → TP
poc: pending
poc_script: null
```

## Gotchas

- Bulk verdicts are the most common triage error — many results under one shared rationale with the traces unread. One trace, one judgment
- A rule's bundle is not one finding — split distinct vulnerabilities apart, but keep true duplicates (same sink and flow) together as one finding with multiple `sarif_hashes`
