{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
- `findings` (required) — the finding file(s) to triage, each `.opentaint/tracking/findings/<name>.yaml` bundling one rule's SARIF results in `sarif_hashes`
