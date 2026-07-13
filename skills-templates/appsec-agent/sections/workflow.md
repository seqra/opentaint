The run is one fixed pipeline, two levels decide which stages execute. `get_status.py` reports the current stage (based on tracking) and its exact tasks for your setup — which stages are in scope, and where you stand — so you never track position by hand. Walk the pipeline top to bottom: at the stage it names, load that stage's reference and do it. Don't load a stage's reference until you reach it.

```
build → references/build.md
discover sources → references/source-rules.md
scan → references/scan.md
approximation iteration → references/approximations.md
author sinks + rules assemble → references/sink-rules.md
triage → references/triage.md
PoC + assemble vulnerabilities → references/poc.md
```

From inside any stage, when a rule or approximation won't behave, load references/escalation.md.

Reuse over regeneration. The `.opentaint/` tree is long-lived — on resume or a re-invocation over changed code, reuse the `DONE` stages' artifacts and re-derive only what the current code forces. A method already built is trusted and never re-derived; existing rules and approximations apply on every scan.

### Scripts

Two bundled helpers carry every deterministic step, so you neither reason it out nor read files by hand. Run both from the project root.

get_status.py — read-only, your source of pipeline state, run it freely:

- `uv run scripts/get_status.py` — the current stage and the exact tasks for it: the plans, batches, units, or findings to hand out, each named in full. Run it at a stage's gate or during it (to get an overview of what's left), then dispatch what it lists
- `uv run scripts/get_status.py --full` — every in-scope phase status, plus the run's levels, language, model commit, and agent caps. Run it at run start or on resume

generate.py — writes plans/batches/state, run only at a fan-out join or at bootstrap:

- `uv run scripts/generate.py partition analyze` — dropped external methods → per-batch approximation plans
- `uv run scripts/generate.py partition discover` — coverage.yaml's project-used members → balanced discover plans
- `uv run scripts/generate.py mark-safe` — discover plans' verdicts → the classification.yaml ledger, then prunes the consumed plans
- `uv run scripts/generate.py merge-skipped` — every batch's skipped/engine_issues → approximations/skipped.yaml, then prunes the consumed plans
- `uv run scripts/generate.py findings` — the scan's SARIF (`results/report.sarif`) → per-rule finding files (idempotent; a rescan adds new result hashes without clobbering a triaged verdict)

Each stage's reference names the script command for that stage.
