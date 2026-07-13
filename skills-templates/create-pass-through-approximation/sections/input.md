{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
{% include "shared/inputs/language.md" %}
- `batch` (required) — the batch id; its `passthrough` entries live in `.opentaint/tracking/approximations/<batch>.yaml`, and you append the ones you build to that file's `build.done`
- `methods` (optional) — a specific `{ method, signature }` subset to (re)work instead of the whole passthrough bucket, when the caller needs only those
