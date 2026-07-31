Use this ownership map to route work and scan errors:

```
.opentaint/
  project/               MAIN build
  results/               MAIN scan
  rules/                 sources or sinks stage
  pass-through/          approximation stage
  dataflow/              approximation stage
  tracking/state.yaml    MAIN run knobs
  tracking/reference/    boundaries stage writes, crossref stage judges
  tracking/boundaries/   boundaries stage
  tracking/              stage agents, leaves, and join scripts otherwise
  enactment.md           crossref stage
  vulnerabilities.md     triage / PoC stage
  issues/                escalation stage
```

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an assessment pass's discovered source units, approximations, and verdicts are as durable as your own.

`state.yaml` shape — `mode` is this pass's pipeline, not a property of the tree, so a later assessment pass simply rewrites it and keeps everything else:

```yaml
mode: enactment
scan_level: deep
triage_level: static
language: java
findings: reports/pentest-2026-07.md
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```

`mode` is what selects this pipeline for this pass; `findings` is the supplied set the pass is measured against, and it stays in `state.yaml` across an assessment pass so a later enactment pass resumes the same set. Neither is edited by hand mid-pass — pointing an in-flight pass at a different finding file strands its reference set. A genuinely different finding set is a new pass, bootstrapped with a new `--findings`.
