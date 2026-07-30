{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `findings` (required) — path to the supplied finding manifest or report the reference set was normalized from
- `finding-ids` (required) — the reference finding ids assigned to this family. Their normalized files are `.opentaint/tracking/reference/<id>.yaml`
- `family` (required) — kebab-case name of the family; also the name of its spec and of the rule units seeded from it
