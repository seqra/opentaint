# Scan

The scan step, run in every workflow (and once per rescan the approximation iteration triggers). Dispatch via the scan agent per the Delegate template in SKILL.md.

Delegate run-scan. Inputs: model-dir `.opentaint/project`, ruleset `builtin` + `.opentaint/rules`, report `.opentaint/results/report.sarif`; on normal/deep also config-dir `.opentaint/config` and approx-dir `.opentaint/approximations/src` (both dir flags walk the tree recursively, so the parents apply every unit). Require a concise return — finding counts per rule, the methods still in `dropped-external-methods.yaml` that sit on a source→sink path, and any config load/parse errors — not the SARIF body. The files persist on disk for the next steps. Set `phases.scan: done`.
