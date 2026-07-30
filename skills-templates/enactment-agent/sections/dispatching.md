Dispatch exactly one stage-orchestrator subagent for each stage invocation:

```
Invoke the Skill orchestrate-stage first, then follow its instructions precisely
Inputs:
  stage: <boundaries|sources|sinks|approx-round|crossref|triage|poc|escalation>
```

A subagent inherits the project-root working directory, so omit `project-root`.

Stage context:

- `boundaries` — normalize the supplied findings into the reference set, generalize each family into a saturated source and sink boundary, and seed the rule units from it
- `sources` — author the seeded source units' rules and wire the joins
- `sinks` — author the seeded sink units' rules and wire the joins
- `approx-round` — classify and build one dropped-method frontier; use a fresh agent for each new frontier
- `crossref` — judge each supplied finding against the latest scan and refresh the coverage manifest
- `triage` — classify the latest findings and refresh the vulnerability report
- `poc` — reproduce confirmed findings and add the outcomes to the report
- `escalation` — repair or settle a stage artifact, or report a scan-wide no-SARIF failure

Keep each agent id until the next scan validates its artifacts. On a stage-owned error, resume that agent with `stage: escalation`, the exact error, and the artifact path/id. If its thread is unavailable, start a re-entrant `orchestrate-stage` agent with that diagnosis.

Dispatch each subagent fresh, don't fork context into it. Then wait for it natively, don't monitor or poll every minute. If the harness forces a wait timeout, set it to ~1h and re-wait when it returns.
