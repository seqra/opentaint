{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `side` (required) — `sources` or `sinks`; the unit's side. It selects the unit file, the sample style, and the test sub-project
- `unit` (required) — the `<package-kebab>` identifying the unit. Its spec and tracking are in `.opentaint/tracking/rules/<side>/<unit>.yaml`; its test project is `.opentaint/test-projects/<unit>/<side>` and its compiled model `.opentaint/test-compiled/<unit>/<side>`
- `fix-target` (optional) — a created rule `<path>#<id>` the main scan flagged, plus the false positive or false negative to correct. When set, narrow or broaden that one rule instead of authoring from the unit
