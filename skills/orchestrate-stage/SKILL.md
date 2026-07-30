---
name: orchestrate-stage
description: Run one stage of the OpenTaint pipeline by coordinating leaf subagents and deterministic joins. Use when a separate OpenTaint pipeline stage needs to be executed
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Run one stage

Complete one bounded stage of the OpenTaint security workflow. Dispatch its independent work to leaf subagents within the resource caps and run the deterministic plan/join scripts its reference names. All durable state lives under the project's `.opentaint/` tree.

## Workflow

Match the stage keyword to its reference and read it fully:

```
sources      → <skill-dir>/references/sources.md
approx-round → <skill-dir>/references/approx-round.md
sinks        → <skill-dir>/references/sinks.md
triage       → <skill-dir>/references/triage.md
poc          → <skill-dir>/references/poc.md
escalation   → <skill-dir>/references/escalation.md
boundaries   → <skill-dir>/references/boundaries.md   (enactment mode)
crossref     → <skill-dir>/references/crossref.md     (enactment mode)
```

Run the bundled script to get the setup overview before proceeding to the reference's instructions:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Use `uv run <skill-dir>/scripts/get_status.py` at a stage gate or join, or when an updated list of remaining work is needed. It is the read-only view of the current stage.

Finish with one concise summary: counts completed and terminal items with one-line causes. Never paste file contents.

## Dispatching

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

## Key constraints

- don't author or edit tracking state owned by a script or leaf; write directly only where the selected reference explicitly assigns it
- read pipeline state through `get_status.py`, not by hand — don't re-derive it with glob/grep/`python3 -c`/YAML scans over `.opentaint/tracking`, `results`, or the `*.yaml`. If its output doesn't settle the question, re-run `get_status.py --full` before opening any file; hand-scanning the tree balloons the run's context
