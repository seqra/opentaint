# Scan

Delegate run-scan. Inputs: model-dir `.opentaint/project`, ruleset `builtin` + `.opentaint/rules`, report `.opentaint/results/report.sarif`; plus config-dir `.opentaint/pass-through` and approx-dir `.opentaint/dataflow` whenever those dirs exist — apply every existing approximation on every scan, any level (the level gates whether new approximations are *generated*, not whether existing ones are *applied*; a lite rescan must still see a prior deep run's coverage). Both dir flags walk the tree recursively, so the parents apply every unit. Keep the return concise — finding counts per rule and any config load/parse errors, never the SARIF body; the files persist on disk for the next steps.

Normal/deep runs iterate approximations: pass `--track-external-methods` so `dropped-external-methods.yaml` is emitted, and have the agent report that it was written, plus — on a verify rescan — any method it modeled that's still listed and any config load error. A lite run has no approximation work — omit `--track-external-methods`; the SARIF and finding counts are all triage needs.

On a deep run, this first scan carries the new source rules wired to the built-in sinks; it drives the taint frontier that the approximation loop and sink discovery consume.

Pass `<max-memory>` when `state.yaml`'s `max_memory` is set. If a subagent reports it only succeeded after retrying at `--max-memory 16G`, record `max_memory: 16G` and pass it to every later run-scan subagent so they start there.

A scan that produced a SARIF — even with a timeout or OOM message — is done; take it as-is. Only when no valid SARIF comes out even at 16G: stop the workflow (nothing to triage) and document it — dispatch report-analyzer-issue with the setup (ruleset, approximation dirs, model, the 16G reached) and commit hash.

Set `phases.scan: done`.

On deep runs, if the scan flags an issue with a created rule — a rule that failed to load/parse, a join that should fire but didn't, or an own rule that false-positives — dispatch create-rule with `<fix-target>` = that rule to fix it, then rescan before continuing.
