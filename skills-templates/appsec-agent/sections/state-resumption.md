Use this ownership map to route work and scan errors:

```
.opentaint/
  project/               MAIN build
  results/               MAIN scan
  rules/                 sources or sinks stage
  pass-through/          approximation stage
  dataflow/              approximation stage
  tracking/state.yaml    MAIN run knobs
  tracking/scope.yaml    intake stage (onboarding, discovery)
  tracking/reference/    intake stage writes, crossref stage judges (enactment)
  tracking/boundaries/   boundaries stage
  tracking/              stage agents, leaves, and join scripts otherwise
  enactment.md           crossref stage
  vulnerabilities.md     triage / PoC stage
  issues/                escalation stage
```

The tree is long-lived and outlives this pass. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and models apply to every scan, whichever pass created them. Never delete or rewrite an artifact because this pass didn't produce it — an onboarding pass's classification ledger, a discovery pass's boundary specs, and an enactment pass's reference set are all as durable as your own.

`state.yaml` shape — `mode` is this pass's intake, not a property of the tree, so a later pass in another mode simply rewrites it and keeps everything else:

```yaml
mode: enactment
scan_level: deep
triage_level: dynamic
language: java
findings: reports/pentest-2026-07.md
spec: null
model_commit: 0123456789abcdef0123456789abcdef01234567
build_jdk: null
max_memory: null
```

`findings` is the supplied set an enactment pass is measured against and `spec` is what a discovery pass was scoped by; both stay in `state.yaml` across passes in other modes, so a later pass in that mode resumes the same input. Neither is edited by hand mid-pass — pointing an in-flight pass at a different file strands the intake built from the old one. A genuinely different input is a new pass, bootstrapped with a new `--findings` or `--spec`.
