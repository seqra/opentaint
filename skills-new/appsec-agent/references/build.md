# Build

`verify.py status` reports this phase: `done` when the model is current, `stale` when HEAD moved past `model_commit`, `pending` when there's no model. On `done`, skip the phase — no subagent. Otherwise build.

Determine the target language first (from the project's build files — Maven/Gradle → java, `go.mod` → go, …), record it in `state.yaml.language`, and name it on this dispatch and every later one.

Dispatch build-project. Inputs: `project-root`, `language`, and `build-hints` when you know a required toolchain, modules/profiles, or build approach. It builds `.opentaint/project` and returns how it built, the build toolchain, and (multi-module) the module count.

Record from its summary:

- `build_jdk` — when the build needed a specific toolchain the caller didn't supply; feed it to every later compiling subagent (create-test-project)
- `model_commit` — `git rev-parse HEAD` when the tree carries no uncommitted source changes, else null (so next run rebuilds rather than falsely reusing). If build-project only re-enabled disabled modules to widen coverage — a config edit, not a source change — the model still represents HEAD, so record HEAD anyway

`verify.py status` confirms `build: done`. Non-convergence (build-project reports it left the build pending after its retries) is a blocker to the whole run — surface it to the user; nothing downstream runs without a model.
