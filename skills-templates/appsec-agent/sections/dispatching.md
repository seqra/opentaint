Every stage's work runs in subagents. Dispatch each with this template — the Skill-load line plus only the inputs its skill lists (all required per reference), the rest is already in the subagent's skill:

```
Invoke the Skill <skill-name> first, then follow its instructions precisely
Inputs:
  <id-or-flag>: <value>
```

A subagent inherits your working directory, so omit `project-root` when it's your current directory.

Universal rules:

- trust the returned summary. Confirm a step landed with `get_status.py`, not by opening the artifact; open a file yourself only when its output doesn't resolve the situation
- don't read a leaf skill's contents unless you genuinely need to

Fan-out and caps:

- `get_status.py --full` prints the caps in its header — `global` (any agent) and `heavy` (the RAM-heavy ones: build-project, run-scan, create-rule, create-dataflow-approximation, sometimes debug-rule). Never dispatch more than the cap at once; drop `global` by 1 for the rest of the run each time an agent comes back rate-limited
- units fan out in parallel — partition hands each agent a disjoint slice, so there are no races. PoC generation is the one sequential exception (shared app state and ports)
- block on the harness's native agent-completion signal instead of busy-waiting with filler turns or polling commands, dispatching the next queued unit as each slot frees so you never idle below the cap
- never bundle steps into one dispatch — a step usually depends on the artifact the previous one wrote
- delete the `test-compiled/` models at the end of the stage that built them (rules, approximations)
- never let one unit halt the run — a rule or approximation that won't work after its skill's retries and escalation is recorded and skipped, not blocked on (the leaf records the cause in the unit's `blocker`). A skipped unit costs coverage, never the run; only a blocker to every remaining step (e.g. `opentaint` missing) stops the workflow
