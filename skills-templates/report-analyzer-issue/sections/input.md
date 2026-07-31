{% include "shared/inputs-preamble.md" %}

{% include "shared/inputs/project-root.md" %}
- `diagnosis` (required for `analysis`) — the caller's brief engine-level cause: roughly where taint appears to die and why. A short hand-off, not a proven trace
- `artifact` (required for `analysis`) — the rule or approximation the issue concerns: a rule's full id and ruleset, or the approximation's target method(s)
- `name` (optional, `analysis`) — the test-project name the artifact was traced on; its tree is `.opentaint/test-projects/<name>` and model `.opentaint/test-compiled/<name>`, cited so the engine team can reproduce
- `setup` (required for `resource`) — what was running when the scan failed without SARIF: the ruleset(s), approximation dirs, project model, final memory bound, timeout/backstop outcome, scan log, and commit hash (`git rev-parse HEAD`)
