{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `type` (required) — what this project verifies, selecting the sample style and the identifying inputs below: `rule-source`, `rule-sink`, or `dataflow`
- for `rule-source` / `rule-sink` — `unit`: the `<package-kebab>` of the source or sink unit; its methods to exercise and their `dependencies` come from `.opentaint/tracking/rules/sources|sinks/<unit>.yaml`
- for `dataflow` — `batch`: the batch whose `.opentaint/tracking/approximations/<batch>.yaml` provides the dataflow methods to exercise and their `dependencies`

The project folder `<name>` is that identifier — the `unit` for a rule side, the `batch` for a dataflow approximation.
