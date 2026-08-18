The run is one fixed pipeline, the same in every mode; the mode decides what intake works from, and the selected levels decide which phases are in scope. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
intake                      → stage subagent: intake
boundaries                  → stage subagent: boundaries
source_rules                → stage subagent: sources
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
sink_rules                  → stage subagent: sinks, then MAIN: rescan
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref   (whenever the tree carries a reference set)
```

The spine is fixed — build, sources, scan, models, sinks, triage — and it is fixed for a reason. Both boundary sides are known before the first scan, because that scan is what proves them and names the taint frontier the model work then answers; the sink rules are authored against that frontier rather than guessed ahead of it. Never let a model stand in for a boundary that was never authored: an approximation carries taint through a carrier, it does not decide what is untrusted or what is dangerous.

`crossref` appears whenever the tree carries a reference set — the pass that supplied it need not be this one. This pass's rescans changed what those findings reproduce, so re-judging them and refreshing `.opentaint/enactment.md` is part of finishing, not optional cleanup.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model. Keep one untouched model for the whole pass.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/model; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed model, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.

### Iterating

The pipeline loops by design, and status is what closes it. A rescan makes every cross-reference pending again; a trace stopped at an opaque carrier sends the run back to a model round; a rule blamed for a miss goes back to the stage that authored it, so status returns there before closing again. Follow status through each loop rather than declaring the run finished early — an earlier phase reading `IN_PROGRESS` after a later one ran is the loop working, not a regression.

The run is complete when status reports `run complete`: `.opentaint/vulnerabilities.md` current, and — where the tree carries a reference set — every supplied finding either reproduced or recorded with the blocker that stopped it, in `.opentaint/enactment.md`. Report the outcome keeping raw SARIF results, validated findings, and unique vulnerability identities as separate counts.
