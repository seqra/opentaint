# Rule test project

## Samples

The fixed counterpart is always the generic `Taint` marker (scaffolded by `test rule init`), never a real source/sink — so types fit cast-free and the sample only exercises the rule under test.

- `@PositiveRuleSample` — a minimal flow that must flag, with real sink/source signatures and no extra hops:
  - **sink** under test → `<Type> t = test.Taint.source(); pkg.theSink(t);` — declare the local as the sink argument's type; the generic `source()` infers it, no cast
  - **source** under test → `var v = pkg.theSource(); test.Taint.sink(v);` — `sink` takes `Object`, so any type fits
  One positive per new sink (in `sinks/`) and per new source (in `sources/`); `value`/`id` point at that sub-project's test join (`<name>-sinks` / `<name>-sources`, `<name>` = the package-kebab)
- `@NegativeRuleSample` — the safe (sanitized or parameterized) variant of the same, which must not flag. Keep it realistic, not stripped to constants

```java
package test;

import org.opentaint.sast.test.util.PositiveRuleSample;
import org.opentaint.sast.test.util.NegativeRuleSample;
import java.sql.Connection;
import java.sql.Statement;

// sinks/ sub-project — a SQL sink fed by the generic marker source
public class SqlSinkTest {
    private Connection db;

    @PositiveRuleSample(value = "java/security/jdbc-sinks.yaml", id = "jdbc-sinks")
    public void vulnerable() throws Exception {
        String input = test.Taint.source();          // generic marker: infers String, no cast
        Statement stmt = db.createStatement();
        stmt.executeQuery("SELECT * FROM users WHERE id = " + input);
    }

    @NegativeRuleSample(value = "java/security/jdbc-sinks.yaml", id = "jdbc-sinks")
    public void safe() throws Exception {
        String input = test.Taint.source();
        var pstmt = db.prepareStatement("SELECT * FROM users WHERE id = ?");
        pstmt.setString(1, input);
        pstmt.executeQuery();
    }
}
```

## Spring-entry flows

If the flow only fires through a Spring entry point (controller → bean → sink), a plain method sample will be a `falseNegative`. Use the multi-module Spring layout — read `spring-multimodule.md` and follow it
