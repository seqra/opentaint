{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `plan` (required) — path to this agent's batch plan `.opentaint/tracking/approximations/plans/<batch>.yaml`: the dropped methods to classify
- `sinks` (optional) — a flag whether to classify sinks per step 2 or not
