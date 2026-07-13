### Artifacts

- the custom library rule file(s) under `.opentaint/rules`
- `.opentaint/tracking/rules/<side>/<unit>.yaml` — the unit's entries updated (per Tracking)

### Summary

- the lib rule ids (created or referenced), a one-line test summary for the side, and the exact `test rule run` command used
- if blocked at step 5: `stages.tests_passing` left pending, and the cause —
  - a dropped library method on the failing sample's flow → the methods that need a model, to be approximated before a re-dispatch
  - nothing dropped and no clear rule cause → non-convergence, for the orchestrator to intervene
