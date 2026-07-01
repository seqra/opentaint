# Triage

On a normal/deep run, finish the approximation loop first — triage only once every dropped method is classified (references/approximations.md), not merely once the SARIF stops changing.

A zero-finding scan is not automatically a clean project. On a normal/deep run, when rules load and run cleanly but nothing fires, suspect a broken flow before accepting the result — taint that dies before reaching any sink yields zero findings just as a genuinely clean project does. The usual causes are an over-eager skip entry or a method still dropped on a source→sink path. A flat zero across every rule — including the non-dataflow ones — instead points at scope: the project model's `--package` roots missed application code (often packages that differ from the source layout), so the app was analyzed as a library and nothing fires; confirm `project.yaml`'s `packages` cover the roots the app's classes declare and rebuild if not. Check these, then trace where taint dies with debug-rule (references/escalation.md). Conclude the project is clean only once the flows are confirmed intact, or the cause is found and genuinely cannot be fixed.

## Generate finding files

Run this skill's bundled `scripts/sarif-to-findings.py` over `.opentaint/results/report.sarif` (`python3 <this skill's directory>/scripts/sarif-to-findings.py .opentaint/results/report.sarif -o .opentaint/tracking/findings` — the script lives in the skill directory, not the project; the project-relative paths are arguments). It writes one `tracking/findings/<finding_name>.yaml` per rule and is idempotent — a rescan adds new result hashes to an untriaged finding and resets it to `pending`, while leaving triaged verdicts intact. This is a deterministic script with no context cost, so run it yourself, not via a subagent.

When every finding for a rule is already triaged but the rescan brings new hashes, the script can't merge them without clobbering a verdict, so it writes them as a fresh `pending` finding whose `notes` open with a `reconcile` line (its summary reports a `to reconcile` count). These are the hash-shift cases — the same vulnerability with a nudged hash, or a genuinely new one. Hand each such finding to its analyze-findings subagent to reconcile against the rule's triaged findings by flow: same vulnerability → it merges the hashes into that finding and inherits the verdict; genuinely new → it triages it normally.

## Classify — never in main

Fan out analyze-findings, one subagent per finding file (the rule bundle is the bucket). Inputs: `<findings>` = the finding file, report `.opentaint/results/report.sarif`. The agent reads each result's `codeFlows[]`, splits the bundle into distinct logical findings, and sets `verdict` + `notes` on each. Return: one line per logical finding (name, verdict, one-clause reason). Assign no verdicts yourself.

## Assemble the report

Refresh `.opentaint/vulnerabilities.md` yourself, so every run — static included — ends with a report on the current verdicts, not only dynamic ones. Rewrite it from the current `verdict: TP` findings: one entry each — `finding_name`, rule / vuln class, the source→sink location, and the one-clause rationale from `notes`. Each run reflects only the current state: drop findings now resolved, update changed ones; if no TP remains, say so rather than leaving a stale file.

A static run can't reproduce anything, so its current TPs are analysis-only. Don't discard a prior dynamic run's evidence: list any finding still carrying `poc: confirmed` under a separate "Previously PoC-confirmed (not re-verified on current code)" section, since a static run can't tell whether it still holds.

On a dynamic run the PoC phase refreshes this again and collapses back to one current-state view (references/poc.md). Set `phases.triage: done` once it's written.
