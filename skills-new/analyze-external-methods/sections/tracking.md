### Batch classification

{% include "shared/tracking/approximations-batch.md" %}

This skill writes `passthrough`/`dataflow`/`skipped` and `dependencies`; leave `engine_issues` and the `build` block to the build stage.

### Sink units (only when `sinks` is set)

{% include "shared/tracking/sink-unit.md" %}

This skill fills `dependencies` and one `sinks` entry per sink it found — `{ method, signature, vuln_class, note, rule_id: null }`, `signature` the method's JVM descriptor from the plan so overloads stay distinct, `vuln_class` per entry, `note` a few words on the danger. Leave `rule_id: null` and the `stages` for the rule-authoring stage. One unit per package; the partition keeps a whole package in one batch, so you are its only writer. Where a package already has a unit from a prior round, add to it rather than rewriting.
