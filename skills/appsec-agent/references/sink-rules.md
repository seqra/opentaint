# Author sinks + assemble + rescan

The approximation loop classified every source-reached external method and recorded the dangerous ones as possible sinks in per-package sink units `tracking/rules/sinks/<package-kebab>.yaml`. Those are the sinks the project's untrusted data can actually reach. Now author the sink rules, join them to every source, and rescan to surface the findings.

## Sink lib rules

Fan out per package that has pending sinks:

1. create-test-project — Inputs: `<spec>` = the unit's sinks, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/sinks/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the unit, `build_jdk` if set. Scaffolds the `sinks/` marker project, writes the marker samples, compiles it. Sets `test_project: done`
2. create-rule — Inputs: `<tracking-file>` `.opentaint/tracking/rules/sinks/<name>.yaml` (the unit — both spec and where results are recorded), test-compiled `.opentaint/test-compiled/<name>`, test-project `.opentaint/test-projects/<name>`, rules-dir `.opentaint/rules`. Writes the package's sink lib rules + the `sinks` test join against the marker, and iterates until every sample passes; sets `tests_passing: done` and each sink's `rule_id`. If a sample drops a library method on its flow, route it through the approximation loop (references/approximations.md), then re-dispatch with the approximation dirs `.opentaint/pass-through` / `.opentaint/dataflow`

## Assemble the full joins

Delegate assemble-lib-rules (Inputs: source-units `.opentaint/tracking/rules/sources`, sink-units `.opentaint/tracking/rules/sinks`, rules-dir, tracking-dir). With the sinks now created it writes the remaining joins — every source (built-in + created) × each created sink — as `.opentaint/rules/java/security/<class>-<sink>-lib-ext.yaml`, extending the `tracking/rules/joins/<class>.yaml` tally.

## Final rescan

Re-run the scan (references/scan.md) so the new sink rules and joins produce findings — this rescan's SARIF is what triage reads. Set `phases.sink_rules: done` once it's in place.
