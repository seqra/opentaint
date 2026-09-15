### Batch classification

{% include "shared/tracking/approximations-batch.md" %}

This skill writes `passthrough`/`dataflow`/`skipped` and `dependencies`; leave the `build` block and `engine_issues` alone — they are filled later in the approximation stage.

### Sink units (only when `sinks` is set)

{% include "shared/tracking/sink-unit.md" %}

The partition keeps a whole package in one batch, so populate only the units your plan owns. Leave `rule_id: null` and the `stages` for rule authoring. If a package already has a unit from a prior round, merge new methods into the matching tag group rather than rewriting it.
