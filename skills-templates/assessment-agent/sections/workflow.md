The run is one fixed pipeline; the selected levels determine which phases are in scope. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
discover / source_rules     → stage subagent: sources
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
sink_rules                  → stage subagent: sinks, then MAIN: rescan
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref   (only if an enactment pass left a reference set)
```

`crossref` appears only when a previous enactment pass over this tree left a reference set. This pass's rescans changed what those supplied findings reproduce, so re-judging them and refreshing `.opentaint/enactment.md` is part of finishing — not optional cleanup.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/approximation; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed approximation, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.
