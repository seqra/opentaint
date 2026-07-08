# build-project — Java / JVM specific instructions

## Workflow

### 2. Identify the build

- `build.gradle` / `build.gradle.kts` → Gradle
- `pom.xml` → Maven
- a shipped JAR/WAR with no buildable sources → classpath mode (step 4)

### 3. Autobuilder

Set `JAVA_HOME` to the JDK the build needs before running `opentaint compile`: the `build-hints` JDK if the orchestrator supplied one, else the version the project declares

Reproduce the project's own build directly to surface the real error the autobuilder's terse wrapper hides:

Prefer the `./gradlew` / `./mvnw` wrapper when present:

```bash
./gradlew build -x test     # Gradle
mvn package -DskipTests     # Maven
```

Fix the build, then re-run `opentaint compile`. If the build needed a JDK the caller didn't supply, return it so the orchestrator reuses it for other compiling subagents.

### 4. Manual build + `opentaint project`

Build the artifacts by hand, then model them. Always pass `--package` to restrict analysis to project code. One `--package` per declared root, and cover all of them, since an omitted root is dropped from the model.

```bash
opentaint project \
  --output .opentaint/project \
  --source-root <project-root> \
  --classpath <app.jar> \
  --package <root.one> --package <root.two>
```

Multi-module: repeat `--classpath` and `--package` per module.

### 5. Verify

`project.yaml`'s package/module roots cover every root the app's classes declare (the `--package` roots on the manual path)

## Constraints

- The build JDK (via `JAVA_HOME`) is separate from the analyzer runtime (Java 21+) — never point the analyzer at the build JDK
- If building by hand pass `--package` on every `opentaint project` invocation; scope roots come from declared packages

## Gotchas

- Modules disabled (commented out in `settings.gradle` / the parent `pom.xml`'s `<modules>`, or behind an inactive profile) → re-enable all of them and rebuild, so their app code lands in the model. The build is still the project's real build, so the model still represents the current commit, return this info to analyzer
- Compilation errors → check the autobuilder log, fix the build, retry; if it truly can't be fixed, fall back to the manual `opentaint project` path
- Missing dependencies → initialize submodules `git submodule update --init`
