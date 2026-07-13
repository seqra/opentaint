Everything a run produces lives under one `.opentaint/` tree at the project root — fully self-contained.

```
.opentaint/
  project/                            # built project model
  rules/<lang>/{lib/…,security}/      # custom lib source/sink defs + join rules
  pass-through/<package-kebab>.yaml   # passThrough approximation configs
  dataflow/<batch>/                   # code-based approximation sources, one dir per batch
  test-projects/<name>/               # per-unit test project sources
  test-compiled/<name>/               # per-unit compiled test model (delete when its stage ends)
  test-results/<name>/                # per-unit test outputs
  results/report.sarif                       # the scan report
  results/dropped-external-methods.yaml      # taint-killing methods to approximate
  results/approximated-external-methods.yaml # modeled external methods (built-in or custom)
  pocs/<name>.py                      # PoC scripts, one per finding
  issues/<slug>.md                    # engine-issue reports
  vulnerabilities.md                  # final report written by you at the end of the run
  tracking/                           # run state (below)
```

Each per-artifact file carries its own schema in the leaf that owns it, and `get_status.py` reads them for you — you neither restate nor re-open them. The tracking tree, with its writer:

```
tracking/
  state.yaml                          # you: the run's knobs
  history.yaml                        # generate.py init: append-only audit log
  coverage.yaml                       # triage-dependencies: packages to drill
  rules/plans/<id>.yaml               # partition discover: disposable, pruned at mark-safe
  rules/classification.yaml           # mark-safe: durable source/safe ledger
  rules/sources|sinks/<pkg>.yaml      # per-package source / sink unit
  rules/joins/<class>.yaml            # per-vuln-class join tally
  approximations/plans/<batch>.yaml   # partition analyze: disposable, pruned at merge-skipped
  approximations/<batch>.yaml         # per-batch method classification + build
  approximations/skipped.yaml         # merge-skipped: merged non-carriers + engine_issues
  findings/<name>.yaml                # one per finding, seeded by the findings script
  poc-servers.yaml                    # generate-poc: instances it started; you reap them
```

state.yaml — the run's knobs, all you keep here. `model_commit` the full commit hash the model reflects, or null when built from a source-dirty tree (set at the build stage); `build_jdk` the toolchain the build needed; `max_memory` `16G` once an OOM forces it. No phase map — `get_status.py` derives every phase from the artifacts:

```yaml
scan_level: deep
triage_level: dynamic
language: java
model_commit: a1b2c3d4
build_jdk: null
max_memory: null
```

The `plans/` are disposable, pruned at their join, never hand-edited. Every other tracking file is owned by the leaf or script noted beside it — consult a stage's reference or `get_status.py`, not this section, for a field.
