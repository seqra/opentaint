`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sinks` each a dangerous operation reached by the taint frontier `{ method, signature, vuln_class, note, rule_id }` — `signature` the member's JVM descriptor so overloads stay distinct, always quoted (array types contain `[`, which is invalid unquoted in a flow mapping), `vuln_class` per entry since one package can host several, `note` a few words on the danger, the tainted argument left unpinned. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - cn.hutool:hutool-core:5.8.20
sinks:
  - { method: cn.hutool.core.io.FileUtil#writeBytes, signature: "([BLjava/lang/String;)Ljava/io/File;", vuln_class: path-traversal, note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```
