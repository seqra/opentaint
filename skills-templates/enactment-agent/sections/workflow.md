The run is one fixed pipeline. Use `uv run <skill-dir>/scripts/get_status.py` to choose the next action:

```
build                       → MAIN: build
reference_set / boundaries  → stage subagent: boundaries
source_rules                → stage subagent: sources
sink_rules                  → stage subagent: sinks
scan                        → MAIN: scan
approximations              → stage subagent: approx-round, then MAIN: rescan; repeat
triage                      → stage subagent: triage
poc                         → stage subagent: poc
crossref                    → stage subagent: crossref
```

Both rule sides are authored before the first scan on purpose: the scan that follows is the one that proves the boundaries, and its results are what later stages are allowed to react to. Never let an approximation stand in for a missing source or sink rule.

The cross-reference closes the run rather than steering it: it judges what the finished rule set, its approximations, and its verdicts actually reproduced.

### Build in MAIN

When status reports `build`, load and follow the `build-project` skill in this main session. Run its long build command through the harness's main-session background-command facility and wait for its completion event.

Record the returned `build_jdk` in `.opentaint/tracking/state.yaml`. Record `model_commit` as the full HEAD only when no source file is uncommitted, otherwise set it to null. Build non-convergence blocks the run because no later phase can proceed without the model. Keep one untouched model for the entire enactment run.

### Scan in MAIN

When status reports `scan`, or a stage returns with a rescan pending, load and follow the `run-scan` skill in this main session. Start the scan with the harness's main-session background-command facility, keep the engine's self-timeout, add a 1200-second outer backstop, and wait for the process completion event.

A valid `.opentaint/results/report.sarif` means the scan completed, including exit 254 after an engine timeout. Record `max_memory: 16G` when the scan had to bump memory and reuse it on later scans. If no SARIF exists after the allowed retry/backstop, follow the repair path below for a malformed rule/approximation; otherwise dispatch `orchestrate-stage` with `stage: escalation` and the scan `setup` to write the scan-wide resource issue, then stop.

When a scan or later stage reports a malformed approximation, unloadable created rule, ineffective join, or a created rule's false positive/negative, route the exact diagnosis and artifact path/id to the responsible stage agent per Dispatching, then scan again in MAIN.

After every build, scan, or stage return, run `uv run <skill-dir>/scripts/get_status.py` once to choose the next action. Use `--full` at run start, on resume, or when the brief output does not settle the question.

### Iterating to coverage

The pipeline loops by design, and status is what closes it. A rescan makes every cross-reference pending again; a cross-reference that finds a trace stopped at an opaque carrier sends the run back to an approximation round; one that blames a rule sends it back to the stage that authored it, so status returns there before closing again. Follow status through each loop rather than declaring the run finished early — an earlier phase reading `IN_PROGRESS` after a later one ran is the loop working, not a regression.

The run is complete when status reports `run complete` — every supplied finding reproduced or recorded with its blocker, and `.opentaint/enactment.md` current. Report the coverage manifest, keeping raw SARIF results, validated findings, and unique vulnerability identities as separate counts.
