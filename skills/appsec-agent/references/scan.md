# Scan

Delegate run-scan. Inputs: model-dir `.opentaint/project`, ruleset `builtin` + `.opentaint/rules`, report `.opentaint/results/report.sarif`; on normal/deep also config-dir `.opentaint/pass-through` and approx-dir `.opentaint/dataflow` (both dir flags walk the tree recursively, so the parents apply every unit). Require a concise return — finding counts per rule, the methods still in `dropped-external-methods.yaml` that sit on a source→sink path, and any config load/parse errors — not the SARIF body. The files persist on disk for the next steps. Set `phases.scan: done`.

On deep runs, if the scan flags an issue with a created rule — a rule that failed to load/parse, a join that should fire but didn't, or an own rule that false-positives — dispatch create-rule to fix that rule (references/discover-rules.md), then rescan before continuing.
