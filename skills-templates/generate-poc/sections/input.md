{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `finding` (required) — the TP finding to reproduce, `.opentaint/tracking/findings/<name>.yaml`
- `base-url` (optional) — the app's base URL when it is already running; otherwise build and start it
