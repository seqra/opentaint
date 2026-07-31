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

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an enactment pass's boundary rules, reference set, and coverage manifest are as durable as your own.

`state.yaml` shape — `mode` is this pass's pipeline, not a property of the tree, so a later enactment pass simply rewrites it and keeps everything else:

```yaml
mode: assessment
scan_level: deep
triage_level: dynamic
language: java
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```
