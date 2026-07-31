{% include "shared/engine/facts.md" %}

- Library rules MUST have `options.lib: true` and `severity: NOTE`
- The test joins (`mode: join`) MUST have `metadata.cwe` and `metadata.short-description`
- Metavariable names must match across `refs` and `on` clauses, or the join won't connect. Bind the tainted value to one consistent metavariable in every lib source/sink rule
- The `rule` path in `refs` is relative to its ruleset root — a marker ref resolves under the test project's marker rules, a lib ref under the scanned rules tree
- Rule IDs must be globally unique
- The custom lib rules go in the scanned rules tree; the test joins go only in the test project's marker rules
- Never scan the main project model
- Never try to edit the test project
