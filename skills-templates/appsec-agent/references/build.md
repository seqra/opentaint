# Build

Produces the whole-program project model every later stage analyzes, nothing runs without it.
Gate: `get_status.py` reports `build` `DONE` when the model is current; otherwise `IN_PROGRESS` — no model yet, or `model stale` when HEAD moved past `model_commit`.

### 1. Dispatch build-project

Inputs:
- `project-root`
- `build-hints` (optional) — a required toolchain or build approach you already know; never hint module scope, the skill widens it itself

Expect back — the built model, plus `build_jdk` from its summary recorded to `state.yaml` (reused for later compiling subagents).

### 2. Record `model_commit`

Run `git status`, then set `state.yaml.model_commit` yourself. When no source files are uncommitted — a clean tree, or dirty only from non-source changes (modules toggled, config/infra), whose model still reflects that commit's source — record the full HEAD hash. When any source file is uncommitted, record null, so the next run rebuilds rather than falsely reusing this model.

Run `uv run scripts/get_status.py` to confirm `build` `DONE`.

## Gotchas

- Non-convergence (build-project reports the build still pending after its retries) blocks the whole run — surface it to the user; nothing downstream runs without a model
