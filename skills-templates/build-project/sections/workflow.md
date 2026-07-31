### 1. Reset the output

Delete any existing `.opentaint/project` first, so files from an old model can't bleed into the new one

### 2. Identify the build

Determine how the project builds — its build tool, or whether it ships pre-compiled artifacts

### 3. Enable all modules

Re-enable every module the project disables so their code lands in the model, then build with them included. Enabling a disabled module is a config edit, not a source change, so the model still represents the current commit. If a specific module cannot be made to compile after reasonable effort, exclude only that one. Report which modules were enabled and which (if any) were excluded.

### 4. Autobuilder — the primary path

```bash
opentaint compile <project-root> -o .opentaint/project
```

`opentaint compile` runs the project's real build, so it resolves the full dependency graph and the actual module reactor automatically — no hand-listing of dependencies or scope. Set the build toolchain the project needs first. Use this path almost always.

Feedback loop: a failure here is almost always a fixable build problem, not grounds to leave this path — and the autobuilder's wrapper message is terse, so don't judge fixability from it. Reproduce the project's own build directly to surface the real error, fix it, then re-run `opentaint compile`.

### 5. Manual build + `opentaint project` — last resort

Only when the project's own build cannot be made to pass at all, build the artifacts by hand, then create the model from them with `opentaint project`, restricting analysis to project code. It's required to show the analyzer which code belongs to the project and which to third-party packages. Take the scope roots from what the code actually declares, not the build config or the folder layout. Verify final list of methods carefully, it's very important to list ALL third-party packages.

### 6. Verify

`.opentaint/project/project.yaml` exists, non-empty, and its module/scope entries cover every root the project's own code declares. For a multi-module project, confirm the expected module count is present. Make sure, that dependencies at `.opentaint/project/dependencies` resolved and downloaded correctly.

### 7. Escalate

When the build won't converge after ~3 fixes → report non-convergence and leave the build stage pending, for the orchestrator to intervene.
