{% include "shared/tracking/source-unit.md" %}

This skill sets `tag: untrusted-data-source`, fills `dependencies`, and adds one `{ method, signature, note, rule_id }` entry per source. Copy `method` + `signature` from the plan, explain why the data is untrusted in `note`, and leave `rule_id: null` and the stages for rule authoring.

The plan `.opentaint/tracking/rules/plans/<id>.yaml` — read your members from its `scopes` map, record the sources you find under a top-level `source` list; the join then ledgers `source` + `safe` (members − source), keyed by the exact method and signature so distinct callable variants stay separate. It is regenerable and disposable, not durable state:

```yaml
id: lib-001
scopes:
  <package-kebab>:
    - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
    - { method: "<qualified-member-b>", signature: "<language-signature-b>" }
source:
  - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
```

`source: null` is the generated plan's unprocessed sentinel. On completion, replace it with the exact sources found, or `source: []` when there are none; `mark-safe` leaves a null plan for re-dispatch instead of incorrectly classifying all its members as safe. Every member listed as a source must also appear in its source unit.
