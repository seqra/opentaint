# Skill: Report Analyzer Issue

Turn a confirmed engine-level problem into a self-contained `.opentaint/issues/<slug>.md` report. It runs no analysis of its own — it only writes the report from what the caller supplies. Two kinds:

- an `analysis` issue — a confirmed engine-level taint-propagation diagnosis (the analyzer's result is wrong)
- a `resource` issue — a scan that ran out of memory even at `--max-memory 16G` (the analyzer can't finish); no taint diagnosis, just the setup that triggered it so the engine team can reproduce
