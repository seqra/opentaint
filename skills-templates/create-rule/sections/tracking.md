This skill writes each unit entry's implementing `rule_id` and the unit's `stages.tests_passing`. `rule_id` is a `<relative-yaml-path>#<id>` locator for either the custom lib rule created for that entry or an existing built-in lib rule proven to cover it. Preserve the source unit's top-level `tag` and every sink `groups[].tag`, those tags are the authoring contract. A blocked unit stays `tests_passing: pending`.

{% include "shared/tracking/source-unit.md" %}

{% include "shared/tracking/sink-unit.md" %}
