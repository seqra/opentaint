# discover-attack-surface — Java / JVM

## Workflow

### 1. Settle built-in coverage

Built-in java source rules live under `java/lib/{generic,spring}/` within the `opentaint health --rules` root — grep there for the member's simple class or method name (a rule is a semgrep-like pattern, not indexed by full FQN+signature), then read the matched rule file to confirm it covers the member. The project's own custom rules are under `.opentaint/rules/java`

### 2. Classify the plan's members

- Each plan member is `{ method, signature }` — an `owner.Class#method` ref and its JVM descriptor, copy both into the source tracking unit
- Confirm the class lives in the resolved jar under `.opentaint/project/dependencies` with `unzip -l <jar> | grep <class-as-path>` — this locates it but lists only class paths, not signatures. Read a method's signatures with `javap -p -s -classpath <jar> <fully.qualified.Class>`; for readable source prefer the source jar or a decompiler

### 3. Write the source units

- `dependencies` is the package's Maven GAV, `group:artifact:version` (e.g. `io.vertx:vertx-core:4.5.26`).
