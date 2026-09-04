Dispatch exactly one stage-orchestrator subagent for each stage invocation:

```
Invoke the Skill orchestrate-stage first, then follow its instructions precisely
Inputs:
  stage: <intake|boundaries|sources|approx-round|sinks|triage|poc|crossref|escalation>
```

For a `deep` model round, also pass `sinks: true`. A subagent inherits the project-root working directory, so omit `project-root`.

Stage context:

- `intake` — turn this mode's input into the run's families: the swept frontier in onboarding, the diff or spec in discovery, the normalized reference set in enactment
- `boundaries` — generalize each family into one universal source and one universal sink, and seed the rule units from them
- `sources` — author the seeded source units' rules and wire the joins
- `approx-round` — classify and build one dropped-method frontier; use a fresh agent for each new frontier
- `sinks` — author the seeded sink units' rules and wire the joins
- `triage` — classify the latest findings and refresh the vulnerability report
- `crossref` — judge a reference set against the latest scan and refresh its coverage manifest
- `poc` — reproduce confirmed findings and add the outcomes to the report
- `escalation` — repair or settle a stage artifact, or report a scan-wide no-SARIF failure

Keep each agent id until the next scan validates its artifacts. On a stage-owned error, resume that agent with `stage: escalation`, the exact error, and the artifact path/id. If its thread is unavailable, start a re-entrant `orchestrate-stage` agent with that diagnosis.

Dispatch each subagent fresh, don't fork context into it. Then wait for it natively, don't monitor or poll every minute. If the harness forces a wait timeout, set it to ~1h and re-wait when it returns.
