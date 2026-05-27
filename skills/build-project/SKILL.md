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

## Workflow

### 1. Determine project type

- `build.gradle` / `build.gradle.kts` → Gradle
- `pom.xml` → Maven
- pre-compiled JAR/WAR → classpath mode
- existing `project.yaml` → already built, reuse it

### 2a. Gradle/Maven — autobuilder

```bash
opentaint compile <project-root> -o <model-out>
```

### 2b. Autobuilder fails — manual build + `opentaint project`

Build manually, then create the model from the artifacts. Always pass `--package` to restrict analysis to project code — without it the analyzer walks third-party libraries and hangs

```bash
./gradlew build -x test     # Gradle
mvn package -DskipTests     # Maven

opentaint project \
  --output <model-out> \
  --source-root <project-root> \
  --classpath <app.jar> \
  --package <com.example.app>
```

Multi-module: repeat `--classpath` and `--package` per module

### 3. Verify

`<model-out>/project.yaml` exists and is non-empty

## Output

The project model directory containing `project.yaml` (default `.opentaint/project`, or the caller's path). Report that path back

## Gotchas

- Analysis hangs → `--package` was omitted in `opentaint project`; the analyzer is processing third-party libraries. Re-run with `--package`
- Build tool not found → use the wrapper (`./gradlew`, `./mvnw`) or install the tool
- Compilation errors → check the autobuilder log, fix the build, retry; if it can't be fixed, fall back to 2b
- Java version mismatch → set `JAVA_HOME` to the version the project needs (opentaint itself needs Java 21+)
- Missing dependencies → initialize submodules (`git submodule update --init`)
