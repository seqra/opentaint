# Build

`model_commit` is yours alone — the subagent never sees it; you decide reuse from it before dispatching.

If `git rev-parse HEAD` matches `model_commit`, the source tree is clean (`git status --porcelain -uno` empty — this ignores untracked/generated paths, so only uncommitted changes to tracked files count), and `.opentaint/project/project.yaml` is present — the model is current. Set `phases.build: done` and skip the phase. No subagent, no double-check.

Otherwise delegate build-project. Inputs: `<project-root>`, `build_jdk` if known, any build constraints. Confirm `project.yaml` exists, is non-empty, and for a multi-module project covers the expected module count.

When the subagent returns a fresh model, record `model_commit` so the next run can reuse it: `git rev-parse HEAD` on a clean source tree, or null when it's dirty (a tree with uncommitted source changes can't be tagged by commit, so the fast path won't falsely fire next run). If the build needed a specific JDK the caller didn't supply, record it in `build_jdk`. Set `phases.build: done`

If build-project re-enabled disabled modules to cover the whole app, the tree is dirty only from that config edit, not a source change — the model still represents HEAD, so record `model_commit` as HEAD anyway.
