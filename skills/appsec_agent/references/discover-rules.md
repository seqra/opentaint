# Discover + new rules

The deep-scan step that maps the attack surface and writes the rules to cover it, run after build and before the scan (deep, and the reproduce-vulnerability workflow). New rules are fixed here, before any approximation iteration. Dispatch per the Delegate template in SKILL.md.

## Discover attack surface

Delegate discover-attack-surface. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It walks a fixed checklist of attack areas into `tracking/coverage.yaml` and creates one `tracking/rules/<name>.yaml` per gap (`description` stage + a short requirements + dependencies), returning the areas covered and one line per rule. Don't ask for the full analysis back. Set `phases.discover: done` once every area in `coverage.yaml` is `done`.

## Rules

Fan out the rule units (one subagent each); per unit a two-step loop:

1. create-test-project — Inputs: spec = the rule's `requirements`, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the tracking file. Sets `test_project: done`
2. create-rule — Inputs: requirements (the tracking file), test-compiled `.opentaint/test-compiled/<name>`, rules-dir `.opentaint/rules`, `<tracking-file>`. Iterates `opentaint dev test-rules` until every sample passes; sets `tests_passing: done`, `rule_id`, `artifact`

If create-rule can't converge after repeated attempts, load references/escalation.md. Set `phases.rules: done` once every rule's `tests_passing` is done.
