# create-test-project — Java rule test project

Language reference for a `rule-source` / `rule-sink` type, keyed to the body's steps. The fixed counterpart is always the generic `Taint` marker, never a real source/sink — so types fit cast-free and the sample exercises only the rule under test.

## Workflow

### 1. Scaffold the project

`rule-source` → `opentaint test rule init <project> --sources-only`; `rule-sink` → `--sinks-only`. Each scaffolds that one sub-project under `.opentaint/test-projects/<name>` with `Taint.java` (the generic `source()` / `sink()`) and the generic marker lib rules in its `test-rules/`. You are handed one side per invocation, build only that side. Pass each coordinate from the unit's `dependencies` as a `--dependency`, taking its exact version from the app's dependency management (`.opentaint/project/sources/**/pom.xml`) verbatim — including timestamped snapshots — not a guess:

```bash
# source side
opentaint test rule init .opentaint/test-projects/<name> --sources-only \
  --dependency "org.springframework:spring-webflux:6.1.0"
# sink side
opentaint test rule init .opentaint/test-projects/<name> --sinks-only \
  --dependency "org.mybatis:mybatis:3.5.13"
```

### 2. Write the samples

Each unit entry already records the method's `signature` (its JVM descriptor) — the overload the sample must match, don't disassemble the jar. To shape a faithful call, look at how the method is actually used in the project. Write the samples under the sub-project's `src/main/java/test/`:

- positive sample — a minimal flow that must flag, with the real sink/source signature and no extra hops:
  - **sink** under test → `<Type> t = test.Taint.source(); pkg.theSink(t);` — declare the local as the sink argument's type; the generic `source()` infers it, no cast
  - **source** under test → `var v = pkg.theSource(); test.Taint.sink(v);` — `sink` takes `Object`, so any type fits
  One positive per new sink (in `sinks/`) and per new source (in `sources/`)
- negative sample — the safe (sanitized or parameterized) variant of the same, which must not flag. Keep it realistic — prefer the library's real sanitizer or validation call when the source makes one visible — not stripped to constants

The samples are plain methods; their verdicts live in a `rule-test.yaml` (below), not on the method.

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

Register the verdicts — write `rule-test.yaml` at the sub-project source root (`sinks/rule-test.yaml` or `sources/rule-test.yaml`), under the sub-project's test-join `rule-id`: `java/security/<name>-sinks.yaml#<name>-sinks` for sink samples, `<name>-sources` for source samples (`<name>` = the package-kebab). The `<path>#<id>` is the rule path relative to the test-rules root plus its short id, not the full `--rule-id` used by `opentaint scan`. List each sample by `test.<Class>#<method>`:

```yaml
tests:
  - rule-id: java/security/jdbc-sinks.yaml#jdbc-sinks
    positive:
      - test.SqlSinkTest#vulnerable
    negative:
      - test.SqlSinkTest#safe
```

The class part is a JVM binary name — a nested class joins with `$` (`test.Outer$Inner#method`); a bare `test.<Class>` with no `#method` targets every method in the class.

Spring-entry flows — if the flow only fires through a Spring entry point (controller → bean → sink), a plain method sample will be a `falseNegative`. Run the sample in Spring app mode: read `references/java-spring-multimodule.md` and follow it.

## Constraints

- The scaffold defaults to Java 8. A sample using a library that needs Java 17/21 (Spring 7, spring-data 4, Lucene 10, Jackson 3) must bump `source/targetCompatibility` and set `release` on the running JDK — a Gradle `toolchain{}` block fails here (only JDK 21 is locatable, with no download repo)
- Diagnose a compile failure with `gradle compileJava --console=plain` in the sub-project — no gradlew is generated
