`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from. `groups` partitions the package's dangerous operations by reusable sink tag; each group is `{ tag, sinks }`, and each sink is `{ method, signature, note, rule_id }`. The tag belongs to the group, never to an individual method: one rule may cover several methods and several rules may extend the same vulnerability family. `method` and `signature` use the exact language-specific identifiers from the plan. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
groups:
  - tag: path-traversal-sink
    sinks:
      - { method: "<qualified-member>", signature: "<language-signature>", note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```
