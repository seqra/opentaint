The tracking tree. Each per-artifact file carries its own schema in the leaf that owns it, and `verify.py` reads them for you — you neither restate nor re-open them. What is written out below is only what you or your scripts own.

```
.opentaint/tracking/
  state.yaml                              # you: the run's knobs (schema below)
  history.yaml                            # you: append-only audit log
  coverage.yaml                           # triage-dependencies: packages to drill for sources (deep)
  rules/plans/<id>.yaml                   # script partition discover: disposable, pruned at mark-safe (deep)
  rules/classification.yaml               # script mark-safe: durable source/safe ledger (deep)
  rules/sources/<package-kebab>.yaml      # per-package source unit (deep)
  rules/sinks/<package-kebab>.yaml        # per-package sink unit (deep)
  rules/joins/<class>.yaml                # per-vuln-class join tally (deep)
  approximations/plans/<batch>.yaml       # script partition analyze: disposable, pruned at merge-skipped (normal/deep)
  approximations/<batch>.yaml             # per-batch method classification + build (normal/deep)
  approximations/skipped.yaml             # script merge-skipped: merged non-carriers + engine_issues
  findings/<name>.yaml                    # one per finding, seeded by the findings script
  poc-servers.yaml                        # generate-poc: instances it started; you reap them (dynamic)
```

state.yaml — the run's knobs, all you keep here. `model_commit` is HEAD when the model is current, null when built from a modified tree (references/build.md); `build_jdk` the toolchain the build needed; `max_memory` `16G` once an OOM forces it (references/scan.md). No phase map — `verify.py` derives phases from the artifacts:

```yaml
scan_level: deep
triage_level: dynamic
language: java
model_commit: a1b2c3d4
build_jdk: null
max_memory: null
```

history.yaml — append-only, newest last:

```yaml
runs:
  - commit: a1b2c3d4
    type: deep/dynamic
```

classification.yaml — the durable ledger `mark-safe` accumulates across runs; `source` and `safe` entries are method+signature strings, so an overloaded member stays distinct and the next discover partition skips only the exact overloads already verdicted:

```yaml
source:
  - org.springframework.web.socket.TextMessage#getPayload()Ljava/lang/String;
safe:
  - org.springframework.web.socket.WebSocketSession#getId()Ljava/lang/String;
```

skipped.yaml — `merge-skipped` rebuilds this from every batch's `skipped`/`engine_issues` (union), each entry keeping its `signature`. `methods` are non-carriers left to the engine default; `engine_issues` are carriers the engine can't model, filed with report-analyzer-issue:

```yaml
methods:
  - { method: org.slf4j.Logger#info, signature: "(Ljava/lang/String;)V" }
engine_issues: []
```

The `plans/<id>.yaml` are script-generated and pruned at their join — disposable, never durable state, never hand-edited. The seven per-artifact files above them are owned by the leaves and scripts noted beside each; their schemas live with those owners, so consult a step's reference or `verify.py`, not this section, for a field.
