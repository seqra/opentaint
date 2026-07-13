# Escalation block

These skills write no tracking files.

1. debug-rule — Inputs: the `<full-id>` to trace (for an approximation, the rule whose sample routes taint through the modeled method), the `<model-dir>` and `<results-dir>` of the run that showed the problem, `<dropped-file>`, and the approximation dirs if the flow depends on them. Returns a diagnosis: rule fix, missing library model, or engine issue
2. Route by cause: a rule cause goes back to create-rule (references/discover-rules.md); a model cause back to the relevant create-*-approximation agent (references/approximations.md) — either to add a missing unit, or to override a built-in that debug-rule shows isn't propagating (you write the override tracking unit for the specific method, since analyze-external-methods didn't produce one); an engine cause goes to step 3
3. report-analyzer-issue — Inputs: the `<diagnosis>`, the existing `<test-project>` / `<test-compiled>`, the `<artifact>` (rule full id, or the approximation's target methods), and `<open-issue>` (you decide whether to also file at github.com/seqra/opentaint). It writes `.opentaint/issues/<slug>.md`
