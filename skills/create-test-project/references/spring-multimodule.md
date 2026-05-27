# Spring multi-module test projects

Load this when a plain method-level sample returns `falseNegative` because the flow only fires through a Spring entry point (controller → bean → sink). Some rules only trigger inside a full Spring MVC entry-point graph — a `@PositiveRuleSample` on a bare method won't trigger them, because the tainted data must flow from a discovered `@Controller`.

For these rules, create one dedicated Gradle sub-project per sample. Each sub-project is a complete, minimal Spring application containing exactly one `@PositiveRuleSample` or `@NegativeRuleSample`. Split positive and negative cases into separate sub-projects, e.g. `xss-spring-test-positive` and `xss-spring-test-negative`.

## How detection works

`TestProjectAnalyzer` computes a `testSetName` per module as `module.moduleSourceRoot.relativeTo(project.sourceRoot)`, with `/` replaced by `-` (see `core/src/main/kotlin/org/opentaint/jvm/sast/project/TestProjectAnalyzer.kt`). If the name starts with `spring-app-tests`, the module is treated as a Spring test set:

- All sample annotations in the module are collected as usual
- Each sample is wrapped in a `SpringTestSample` that uses the Spring dispatcher method as the analysis entry point instead of the annotated method itself
- Taint therefore originates from real `@Controller` request parameters and must reach the annotated sink method through normal Spring wiring

Consequence: the annotated method is only a marker for which rule to run and the expected verdict. The actual vulnerable/safe flow must be reachable from a controller in the same module. Keep each module to a single annotation so the verdict is unambiguous.

## Project layout

Multi-module Gradle build where every `spring-app-tests/<name>` directory is its own sub-project:

```
<test-project>/
├── settings.gradle.kts
├── build.gradle.kts
└── spring-app-tests/
    ├── xss-spring-test-positive/
    │   ├── build.gradle.kts
    │   └── src/main/java/test/
    │       ├── VulnerableController.java    // @Controller with the tainted flow
    │       └── VulnerableSink.java          // carries the single @PositiveRuleSample
    └── xss-spring-test-negative/
        ├── build.gradle.kts
        └── src/main/java/test/
            ├── SafeController.java
            └── SafeSink.java                // carries the single @NegativeRuleSample
```

`settings.gradle.kts` should auto-discover every `spring-app-tests/*/build.gradle.kts` so adding a case only needs a new directory. See `rules/test/settings.gradle.kts` in the OpenTaint repo for a reference implementation.

## Required dependencies

Each Spring sub-project needs at least:

- `compileOnly` on `opentaint-sast-test-util` (the sample annotations)
- `org.springframework:spring-webmvc` and `spring-context` (so `@Controller` is recognized)
- Any libraries the sample itself uses (servlet-api, JDBC, etc.)

## Compile

```bash
opentaint compile <test-project> -o <test-compiled>
```

Each `spring-app-tests/<name>` sub-project becomes an independent test set and appears as its own entry in `test-result.json`.

## Common pitfalls

- No `@Controller` in the module → `TestProjectAnalyzer` logs `No spring entry point found` and the sample is analyzed without Spring context, usually a false negative. Always include a controller that reaches the sink
- More than one annotation per module → results become ambiguous; keep it to one sample per sub-project
- Module path not starting with `spring-app-tests` → `isSpringAppTestSet()` returns false and the sample runs as a regular method-level test, so Spring flows won't trigger
