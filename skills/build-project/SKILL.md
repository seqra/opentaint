---
name: build-project
description: Build a Java/Kotlin project for opentaint analysis and produce a project.yaml model. Use whenever an opentaint scan needs a project model and `opentaint compile` may need help
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Build Project

Build a target project into an opentaint project model. The model is this skill's only output

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the project to build. Default: current directory
- Model output directory `<model-out>` — where to write the model. Default: `.opentaint/project`
- Build constraints (optional) — required Java version, submodules to initialize, `--package` filters for `opentaint project`
- Build JDK `<build-jdk>` (optional) — the JDK this project's build needs, set via `JAVA_HOME`. Separate from the analyzer runtime (Java 21+)

## Workflow

### 1. Determine project type

- `build.gradle` / `build.gradle.kts` → Gradle
- `pom.xml` → Maven
- pre-compiled JAR/WAR → classpath mode

Start by deleting any existing `<model-out>` first, so files from an old model can't bleed into the new one.

### 2a. Gradle/Maven — autobuilder (almost always this path)

```bash
opentaint compile <project-root> -o <model-out>
```

`opentaint compile` runs the project's real build, so it resolves the full dependency graph and the actual module reactor automatically — no hand-listing of dependencies or package scope. `opentaint project` (2b) does none of that, so reach for it only when there is genuinely no way to make the autobuilder compile the project.

Set `JAVA_HOME` to the JDK the build needs before compiling — `<build-jdk>` if given, else the version the project declares (Gradle toolchain / `sourceCompatibility`, Maven `maven.compiler.release`). If you find a required JDK that wasn't handed to you, return it so the orchestrator reuses it for other compiling subagents.

A failure here is almost always a fixable build problem, not grounds to switch to 2b — and the autobuilder's wrapper message is terse, so don't judge fixability from it. Reproduce the project's own build directly (`./gradlew build -x test` or `mvn package -DskipTests`) to surface the real error, fix it, then re-run `opentaint compile`. Try this before concluding the autobuilder can't build the project.

### 2b. Manual build + `opentaint project` — last resort only

Only when the project's own build cannot be made to pass at all (so the autobuilder can't either). Build manually, then create the model from the artifacts. Always pass `--package` to restrict analysis to project code — without it the analyzer walks third-party libraries and hangs. Take the roots from the packages the classes actually declare, not the Gradle `group` or the source-folder layout — forked or vendored code often declares packages that differ from its directory. Pass one `--package` per declared root and cover all of them; an omitted root is left out of the model

```bash
./gradlew build -x test     # Gradle
mvn package -DskipTests     # Maven

opentaint project \
  --output <model-out> \
  --source-root <project-root> \
  --classpath <app.jar> \
  --package <root.one> --package <root.two>
```

Multi-module: repeat `--classpath` and `--package` per module

### 3. Verify

`<model-out>/project.yaml` exists, is non-empty, and its `packages` list includes every root the project's classes declare

## Output

The project model directory containing `project.yaml` (default `.opentaint/project`, or the caller's path). Report that path back. If the build required a specific JDK, report it too, for the orchestrator to reuse

## Gotchas

- Modules disabled (commented out in `settings.gradle` / the parent `pom.xml`'s `<modules>`, or behind an inactive profile) → re-enable all of them and rebuild, so their app code lands in the model instead of surfacing later as dropped external methods. Enabling modules widens coverage; the build is still the project's real build, so the model still represents the current commit
- Analysis hangs → `--package` was omitted in `opentaint project`; the analyzer is processing third-party libraries. Re-run with `--package`
- Build tool not found → use the wrapper (`./gradlew`, `./mvnw`) or install the tool
- Compilation errors → check the autobuilder log, fix the build, retry; if it can't be fixed, fall back to 2b
- Java version mismatch → set `JAVA_HOME` to the version the project's build needs (opentaint runs its analyzer under Java 21+ separately)
- Missing dependencies → initialize submodules (`git submodule update --init`)
