### 1. Reconcile before judging

A finding whose `notes` open with a `reconcile` line is a rescan result under a rule whose other findings are already triaged — most often the same vulnerability with a shifted hash, not a new one. Before judging it fresh, read the rule's already-triaged finding files and compare flows (source → sink, same essential path): if one matches, move this finding's `sarif_hashes` into that finding, drop this file, and let the inherited verdict stand — don't re-judge a flow already triaged. Only when no triaged finding matches do you treat it as new and continue below.

### 2. One result at a time — STOP checklist

For each hash in the bundle, before any verdict, read its raw result from `.opentaint/results/report.sarif`:

- find its SARIF result via `sarif_hashes` — each entry is the leading 16 chars of that result's `vulnerabilitySourceSinkHash`/`vulnerabilityWithTraceHash` fingerprint, so match it against the result's `fingerprints`/`partialFingerprints` — then read the raw `codeFlows[]`
- walk every step, source → hops → sink, confirming it's the same tainted value end to end; confirm the flow against the application source (the built project's own sources under `.opentaint/project/sources/`) and dependency code, not the trace text alone
- judge each result on its own trace — no verdict shared across results just because they share the rule

### 3. Split the bundle into logical findings

The results in the file all fired one rule, but may be several different vulnerabilities. Keep results that are the same vulnerability (same sink, same essential flow) together as one finding; move genuinely distinct ones into their own finding file with a new name and their `sarif_hashes` (per Tracking).

### 4. Classify and record

Verdict each logical finding from its flow:

- TP — the source is attacker-controlled, the sink is genuinely dangerous with that input, and nothing sanitizes it in between
- FP — a sanitizer/validator neutralizes it, the source isn't actually attacker-controlled (config, constant, server-set), the sink is safe for this input (parameterized, escaped), or the path is infeasible. Record which one

Set `verdict` and append the reasoning to `notes`, below the analyzer report already seeded there (per Tracking).
