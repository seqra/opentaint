# Skill: Report Analyzer Issue

Turn a suspected engine-level problem into a self-contained `.opentaint/issues/<slug>.md` report. It runs no analysis of its own — it only writes the report from what the caller supplies. Two kinds:

- an `analysis` issue — a suspected engine-level taint-propagation problem the caller couldn't resolve with a rule or a model (the analyzer's result looks wrong)
- a `resource` issue — a full-project scan that produced no SARIF after its allowed retry, memory bound, or timeout backstop; no taint diagnosis, just the setup that triggered it so the engine team can reproduce
