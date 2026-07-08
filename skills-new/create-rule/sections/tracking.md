This skill writes only each unit entry's `rule_id` and its `stages.tests_passing`, once the lib rules exist and every sample on the side passes. `rule_id` is the created lib rule's ref, or a built-in ref when you referenced a built-in instead of authoring one. Don't add a top-level `artifact` — the path is derivable from `rule_id`. A blocked unit stays `tests_passing: pending`.

{% include "shared/tracking/source-unit.md" %}

{% include "shared/tracking/sink-unit.md" %}
