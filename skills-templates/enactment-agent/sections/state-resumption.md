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

The tree is long-lived. On resume, reuse `DONE` artifacts; `get_status.py` derives the next phase from disk. Existing rules and approximations apply to every scan.

`state.yaml` shape:

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

`mode` is what selects this pipeline; `findings` is the supplied set the whole run is measured against. Both are written at bootstrap and never edited afterwards — pointing an in-flight run at a different finding file strands its reference set.
