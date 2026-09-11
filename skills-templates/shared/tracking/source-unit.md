`.opentaint/tracking/rules/sources/<package-kebab>.yaml` — one source unit per package (a dependency can span several packages), the file named for that package with `.` → `-`. `tag` is always the reusable `untrusted-data-source` group. `dependencies` names the dependency the package comes from, `sources` each an entry point `{ method, signature, note, rule_id }` (`method` and `signature` use the exact language-specific identifiers from the plan), `stages` tracks the unit through rule authoring, and a `blocker` string is added under it when the unit can't be made to pass. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
tag: untrusted-data-source
sources:
  - { method: "<qualified-member>", signature: "<language-signature>", note: untrusted message payload, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```
