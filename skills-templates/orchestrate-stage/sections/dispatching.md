Launch leaf subagents from the project root. They inherit that working directory, so omit `project-root`. One dispatch loads exactly one leaf skill and performs only that skill's task. Follow this template when dispatching subagent:

```
Invoke the Skill <skill-name> first, then follow its instructions precisely
Inputs:
  <id-or-flag>: <value>
```

Pass `language` from `get_status.py --full` to every language-coupled leaf.

Universal rules:

- trust the returned summary; open an artifact only when the summary does not resolve the result
- don't read a leaf skill's contents unless genuinely needed
- never bundle multiple steps into one dispatch
- when a rule or approximation does not converge after its leaf's retries, load `<skill-dir>/references/escalation.md`, settle that item, and continue. Only a blocker shared by every remaining item stops the stage

Fan-out and caps:

- `get_status.py --full` prints `global` and `heavy` caps; the heavy leaves in these stages are `create-rule` and `create-dataflow-approximation`. Never exceed either cap; reduce `global` by 1 for the rest of the stage when a leaf is rate-limited
- fan out independent units and dispatch the next queued unit as each slot frees
- block on native agent completion. Never use Monitor, a background command, or resume-polling to wait inside this agent
