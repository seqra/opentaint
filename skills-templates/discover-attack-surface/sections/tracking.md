{% include "shared/tracking/source-unit.md" %}

This skill fills `dependencies` (the package's dependency identifier) and one `sources` entry per source it found — `{ method, signature, note, rule_id }` with `method` + `signature` copied from the plan and `note` a few words on why the data is untrusted; leave `rule_id: null` and the `stages` for the rule-authoring stage. One unit per package the plan touched.

The plan `.opentaint/tracking/rules/plans/<id>.yaml` — read your members from its `scopes` map, record the sources you find under a top-level `source` list; the join then ledgers `source` + `safe` (members − source), keyed per method+signature so an overload stays distinct. It is regenerable and disposable, not durable state:

```yaml
id: lib-001
scopes:
  <package-kebab>:
    - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;" }
    - { method: org.springframework.web.socket.WebSocketSession#getId, signature: "()Ljava/lang/String;" }
source:
  - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;" }
```
