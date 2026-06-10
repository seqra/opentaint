# Triage

The scan must be stable first.

## Generate finding files

Run this skill's bundled `scripts/sarif-to-findings.py` over `.opentaint/results/report.sarif` (`python3 <this skill's directory>/scripts/sarif-to-findings.py .opentaint/results/report.sarif -o .opentaint/tracking/findings` — the script lives in the skill directory, not the project; the project-relative paths are arguments). It writes one `tracking/findings/<finding_name>.yaml` per rule and is idempotent — a rescan adds new result hashes and resets changed findings to `pending`. This is a deterministic script with no context cost, so run it yourself, not via a subagent.

## Classify — never in main

Fan out analyze-findings, one subagent per finding file (the rule bundle is the bucket). Inputs: `<findings>` = the finding file, report `.opentaint/results/report.sarif`. The agent reads each result's `codeFlows[]`, splits the bundle into distinct logical findings, and sets `verdict` + `notes` on each. Return: one line per logical finding (name, verdict, one-clause reason). Assign no verdicts yourself. Set `phases.triage: done`.
