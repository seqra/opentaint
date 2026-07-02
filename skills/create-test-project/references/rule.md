# Rule test project

## Samples

The fixed counterpart is always the generic `Taint` marker (scaffolded by `test rule init`), never a real source/sink — so types fit cast-free and the sample only exercises the rule under test.

- **positive** — a minimal flow that must flag, with real sink/source signatures and no extra hops:
  - **sink** under test → `<Type> t = test.Taint.source(); pkg.theSink(t);` — declare the local as the sink argument's type; the generic `source()` infers it, no cast
  - **source** under test → `var v = pkg.theSource(); test.Taint.sink(v);` — `sink` takes `Object`, so any type fits
  One positive per new sink (in `sinks/`) and per new source (in `sources/`); the sub-project's `rule-test.yaml` names its test join as the `rule-id` (`java/security/<name>-sinks.yaml#<name>-sinks` / `<name>-sources`, `<name>` = the package-kebab)
- **negative** — the safe (sanitized or parameterized) variant of the same, which must not flag. Keep it realistic, not stripped to constants

The samples are plain methods; their expected verdicts live in a `rule-test.yaml` at the sub-project source root, listing each sample by its JVM binary class name (nested classes use `$`), optionally `#<methodName>` to target a single method:

```java
package test;

import java.sql.Connection;
import java.sql.Statement;

// sinks/ sub-project — a SQL sink fed by the generic marker source
public class SqlSinkTest {
    private Connection db;

    public void vulnerable() throws Exception {
        String input = test.Taint.source();          // generic marker: infers String, no cast
        Statement stmt = db.createStatement();
        stmt.executeQuery("SELECT * FROM users WHERE id = " + input);
    }

    public void safe() throws Exception {
        String input = test.Taint.source();
        var pstmt = db.prepareStatement("SELECT * FROM users WHERE id = ?");
        pstmt.setString(1, input);
        pstmt.executeQuery();
    }
}
```

```yaml
# sinks/rule-test.yaml
tests:
  - rule-id: java/security/jdbc-sinks.yaml#jdbc-sinks
    positive:
      - test.SqlSinkTest#vulnerable
    negative:
      - test.SqlSinkTest#safe
```

## Spring-entry flows

If the flow only fires through a Spring entry point (controller → bean → sink), a plain method sample will be a `falseNegative`. Use the multi-module Spring layout — read `spring-multimodule.md` and follow it
