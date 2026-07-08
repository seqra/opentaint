<project-root>/.opentaint/
  project/                      # built project model (project.yaml)
  rules/<lang>/{lib/…,security}/   # custom rules — lib source/sink defs + security join rules
  pass-through/<package-kebab>.yaml   # passThrough approximation configs, one per package
  dataflow/<batch>/             # code-based (dataflow) approximation sources, one dir per batch
  test-projects/<name>/         # per-unit test project sources; a rule unit holds sinks/ and sources/ sub-projects, each with a test-rules/ (the generic markers + that side's test join — test-only, never loaded by the main scan)
  test-compiled/<name>/         # per-unit compiled test model (a rule unit: sinks/ and sources/ models)
  test-results/<name>/          # per-unit test outputs
  results/
    report.sarif
    dropped-external-methods.yaml       # taint-killing methods → approximate
    approximated-external-methods.yaml  # already modeled
  pocs/<name>.py                # PoC scripts, one per finding
  issues/<slug>.md              # engine-issue reports
  tracking/                     # see Tracking layout
  vulnerabilities.md            # you assemble this from the TP findings (PoC-confirmed on dynamic runs)
