Use this ownership map to route work and scan errors:

```
.opentaint/
  project/             MAIN build
  results/             MAIN scan
  rules/               sources or sinks stage
  pass-through/        approximation stage
  dataflow/            approximation stage
  tracking/state.yaml  MAIN run knobs
  tracking/            stage agents, leaves, and join scripts otherwise
  vulnerabilities.md   triage / PoC stage
  issues/               escalation stage
```

The tree is long-lived. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan.

`state.yaml` shape:

```yaml
scan_level: deep
triage_level: dynamic
language: <language>
model_commit: 0123456789abcdef0123456789abcdef01234567
max_memory: null
```

The selected `build-project` language reference may define additional build fields; preserve them on resume and pass them back as `build-hints`.
