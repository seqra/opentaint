# Escalation block

When a rule or approximation won't behave after its skill's own retries, diagnose before re-authoring blindly. These skills write no tracking state.

1. debug-rule — Inputs: `project-root`, `rule` (the `<path>#<id>` whose sample routes taint through the code under test; for an approximation, the rule whose sample routes through the modeled method), `model` (the model where the behavior shows — the unit's test model, or `.opentaint/project` for the main scan). It traces where taint dies and returns a diagnosis: rule defect, missing/wrong library model, or engine issue.

2. Route by cause:
   - rule defect → create-rule with `side` + `unit` of the affected unit and `fix-target` = the flagged `<path>#<id>` plus the FP/FN to correct (references/source-rules.md / references/sink-rules.md)
   - missing/wrong library model → the relevant create-*-approximation to add or override the method. A passThrough that won't converge is re-planned as dataflow: remove its passThrough config, then create-test-project (`type: dataflow`) → create-dataflow-approximation (references/approximations.md)
   - engine issue → step 3

3. report-analyzer-issue — Inputs: `project-root`, `diagnosis` (debug-rule's conclusion), `artifact` (the rule's full id, or the approximation's target method(s)), and `name` (the test project it was traced on). It writes `.opentaint/issues/<slug>.md`. Then move the method to the batch's `engine_issues` and carry on — a skipped carrier costs coverage, not the run.
