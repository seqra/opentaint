Every step's work runs in subagents. Dispatch each with this template — one `Inputs` line per input the skill lists, resolved to a value:

```
Invoke the Skill tool with skill=<skill-name> first, then follow its instructions precisely
Inputs:
  project-root: <path, or . for the current directory>
  language: <target language>          # every skill except triage-dependencies / run-scan / debug-rule / analyze-findings / report-analyzer-issue
  <id-or-flag>: <value>                # the unit / batch / plan / side / type / fix-target / sinks the step's reference names
Return:
  <the skill's Output>
```

Universal rules — every dispatch, every workflow:

- open the prompt with the Skill-load line — the subagent has none of this context until it loads its skill
- pass only what the skill lists: `project-root`, `language`, and the small identifier or flag the reference names. The leaf resolves its own `.opentaint/...` paths — never hand it a model/tracking/rules/test path
- when the skill is language-coupled, name the reference to read on dispatch — "target language <lang>; read references/<lang>.md first" (build-project recorded the language)
- trust the returned summary. Confirm a step landed with `verify.py`, not by opening the artifact — it reports presence, counts and completeness across the tree (Scripts). Read a file yourself only on an integrity flag or an escalation
- only run-scan scans the main project model; rule/approximation/triage subagents don't — the one exception is a create-rule agent running its own diagnostic scan of its test project (never the main model)
- only you write `.opentaint/vulnerabilities.md`, `.opentaint/tracking/state.yaml`, and `.opentaint/tracking/history.yaml`
- never swap the project model mid-analysis; every run uses the same model
- never triage yourself — verdicts come only from analyze-findings subagents

Orchestration practices:

- Units fan out in parallel — partition hands each agent a disjoint slice (its own unit/batch/plan), so there are no races. Cap per Resource limits
- the sole sequential exception is PoC (shared app state and ports); see references/poc.md
- steps within a unit are sequential via the artifact on disk — dispatch step N only after step N−1's named artifact exists; never bundle steps into one dispatch
- one batch file has several writers across stages (analyze → create-test-project → the build skills): sequence them, never fan two writers onto one batch at once
- at each join run the join's `generate.py` command (Scripts) — it aggregates the agents' slices and prunes the consumed plans — then update `state.yaml`
- delete the `test-compiled/` models at the end of the stage that built them (rules, approximations) — large and unused once the tests pass
- never let one unit halt the run — a rule or approximation that won't work after its skill's retries and the escalation flow (references/escalation.md) is recorded and skipped, not blocked on. The leaf marks the cause (a `blocker` on the unit, or the method in the batch's `engine_issues`; filed with report-analyzer-issue when the cause is the engine); you carry on to triage. A skipped unit costs coverage (a possible false negative), never the run — `verify.py` keeps it visible in integrity so it isn't silently lost. Only a blocker to every remaining step (`opentaint` missing, no project model at all) stops the workflow
