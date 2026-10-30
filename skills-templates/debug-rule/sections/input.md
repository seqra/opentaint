{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
- `rule` (required) — the one rule whose sample or flow routes taint through the code under test, as `<ruleSetRelativePath>.yaml:<shortId>`. For a model, the rule whose sample routes taint through the modeled method
- `model` (required) — the project model where the behavior shows up, or the Go test project directory
