---
name: report-analyzer-issue
description: Write an OpenTaint engine-issue report from a confirmed diagnosis, optionally opening a GitHub issue. Use when engine-side issue got confirmed and requires report
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Report Analyzer Issue

Turn a confirmed engine-level diagnosis into a self-contained `.opentaint/issues/<slug>.md` report, and optionally a GitHub issue. It only writes the report from the diagnosis, the test project, and the rule or approximation it concerns — it runs no analysis of its own

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Diagnosis `<diagnosis>` — debug-rule's engine-level conclusion: where taint dies (`file:line` + instruction), the fact-reachability trace up to the last reachable fact, and observed vs expected verdict
- Test project `<test-project>` / `<test-compiled>` — the project the artifact was tested on and debug-rule traced, already built by create-test-project. Default: `.opentaint/test-projects/<name>` / `.opentaint/test-compiled/<name>`
- Artifact `<artifact>` — the rule or approximation the issue concerns: a rule's full id and ruleset, or the approximation's target method(s)
- Issue file `<issue-file>` — where to write the report. Default: `.opentaint/issues/<slug>.md`; `<slug>` is a short kebab-case symptom name (a filename — no spaces or hashes)
- Open a GitHub issue `<open-issue>` (optional) — whether to also file at github.com/seqra/opentaint; the main agent decides and passes this. Default: no

## Workflow

### 1. Gate — require an engine diagnosis

File a report only for an engine issue debug-rule already confirmed. The diagnosis must establish all three; if any is missing, return to the caller and ask for debugging first — don't verify or run anything yourself:

- not a rule fix — the rule's patterns are correct; debug-rule ruled out tightening or broadening it
- not a missing model — no method on the source→sink path remains in `dropped-external-methods.yaml`
- it is the engine — taint is dropped at an instruction the engine should propagate through

### 2. Write the report

Write `<issue-file>` — this file is the deliverable; never return the diagnosis as chat text only. Assemble from the inputs:

- Test project — `<test-project>` path, the test command (`test rule run` / `test approximation run`), and the failing `test-result.json` snippet (e.g. a `@PositiveRuleSample` stuck at `falseNegative`)
- Rule / approximation — the `<artifact>`: a rule's full id and ruleset, or the approximation's target method(s)
- Observed vs expected — e.g. expected a finding at `Sink.java:42`; observed none
- Where the dataflow dies — `file:line` and the instruction, quoted up to the last reachable fact
- Ruled-out causes — the three gate points
- Hypothesis — 1–3 sentences on what the engine is likely doing wrong there; a hypothesis, not a fix

Keep it to about one screen plus the test project

### 3. File on GitHub (only if asked)

When `<open-issue>` is set, file the same content to the fixed repo:

```bash
gh issue create --repo seqra/opentaint \
  --title "<slug>: <one-line symptom>" \
  --body-file <issue-file>
```

## Output

- The written `<issue-file>` (always), and the issue URL if one was filed
