{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `family` (required) — kebab-case name of the family; also the name of its spec and of the rule units seeded from it
- `evidence` (required) — the ids assigned to this family. Reference finding ids when the pass has a reference set, whose normalized files are `.opentaint/tracking/reference/<id>.yaml`; otherwise the members or code areas `.opentaint/tracking/scope.yaml` recorded for the family
- `findings` (optional) — path to the supplied finding manifest or report the reference set was normalized from, when there is one. Read it for detail a normalized file doesn't carry
