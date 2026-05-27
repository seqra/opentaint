# Build

The build step, run in every workflow. Dispatch per the Delegate template in SKILL.md; write only the slice named here.

Delegate build-project. Inputs: `<project-root>`, model-out `.opentaint/project`, any build constraints (Java version, submodules, `--package` filters). Verify `.opentaint/project/project.yaml` exists, is non-empty, and — for a multi-module project — covers the expected module count, not just that the file is present. Set `phases.build: done`.
