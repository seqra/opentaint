# Scan

Runs the built model to produce `results/report.sarif` and `results/dropped-external-methods.yaml` (the frontier the approximation loop models). Re-invoked for every rescan a later stage triggers.
Gate: `get_status.py` reports `scan` `DONE` once a `results/report.sarif` newer than the model exists; otherwise (no SARIF, or a rebuild left it stale) it lists `dispatch run-scan`.

### 1. Dispatch run-scan

Inputs:
- `project-root`
- `max-memory` — `state.yaml.max_memory`, only when it's set

Expect back — the SARIF and `dropped-external-methods.yaml` on disk: `get_status` then reads them. Record `max_memory` (`16G`) in `state.yaml` if run-scan reports it bumped memory, and pass it to every later run-scan.

Existing approximations apply on every scan at any level — the level gates whether new approximations are generated, not whether existing ones apply, so a lite rescan still sees a prior run's coverage.

Run `uv run scripts/get_status.py` to confirm `scan` `DONE`.

## Gotchas

- A scan that produced a SARIF — even alongside a timeout or OOM message — is done. Only when no valid SARIF comes out even at the highest memory bound is it a real failure: stop the workflow and dispatch report-analyzer-issue with the setup run-scan reports
- A config-load failure on a malformed approximation is not a scan failure, and 16G won't help — run-scan names the offending file; route it through escalation (references/escalation.md) to fix that file and rescan
- When triage or a rescan surfaces a created rule the scan couldn't load, a join that should fire but didn't, or an own rule that false-positives, route it through escalation (references/escalation.md) and rescan before continuing
