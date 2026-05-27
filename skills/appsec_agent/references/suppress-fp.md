# Suppress-FP block

Load this when the workflow has suppress-FP on, after triage. It fixes confirmed false positives on rules you own or can override, so a rule edit can't silently drop a real finding. Dispatch per the Delegate template in SKILL.md.

For each confirmed FP on an own/overridable rule, one at a time:

1. create-test-project — pin the confirmed TPs as `@PositiveRuleSample` and add the FP as `@NegativeRuleSample`, recompile. Inputs: the FP and TP traces as `<spec>`, the rule's `<tracking-file>`, test-project / test-compiled `.opentaint/test-{projects,compiled}/<name>`
2. create-rule — refine only the rule until the negative stops firing and every positive still passes. Inputs: the rule `<tracking-file>`, test-compiled `.opentaint/test-compiled/<name>`, rules-dir `.opentaint/rules`
3. re-scan (references/scan.md), then regenerate finding files and retriage the affected findings (references/triage.md)

Loop until the FP is gone and the TPs stay. An FP from a built-in rule you can't override is recorded in the finding's `notes`, not suppressed. Set `phases.suppress_fp: done`.
