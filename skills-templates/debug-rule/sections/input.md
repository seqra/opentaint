{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
- `rule` (required) — the one rule whose sample or flow routes taint through the code under test, as `<ruleSetRelativePath>.yaml:<shortId>`. For an approximation, the rule whose sample routes taint through the approximated method
- `model` (required) — the project model where the behavior shows up
