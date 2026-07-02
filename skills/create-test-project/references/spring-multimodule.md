# Spring app-mode test samples

Load this when a plain method-level sample returns `falseNegative` because the flow only fires through a Spring entry point (controller → bean → sink). Some rules only trigger inside a full Spring MVC entry-point graph — a positive sample analyzed as a bare method won't trigger them, because the tainted data must flow from a discovered `@Controller`.

For these rules, run the sample in **Spring app mode**. A `rule-test.yaml` sample entry can be either a plain string (default mode — the sample method is the analysis entry point) or an object with an explicit `mode`:

```yaml
tests:
  - rule-id: java/security/xss.yaml#xss-in-spring-app
    positive:
      - entrypoint: test.VulnerableSink#vulnerable
        mode: spring-app
    negative:
      - entrypoint: test.SafeSink#safe
        mode: spring-app
```

## How detection works

`mode: spring-app` (see `core/src/main/kotlin/org/opentaint/jvm/sast/project/TestProjectAnalyzer.kt`):

- The analysis entry points become the project's Spring web dispatch entry points (`springWebProjectContext.springWebProjectEntryPoints()`) instead of the sample method itself
- Taint therefore originates from real `@Controller` request parameters and must reach the sink through normal Spring wiring
- The sample's `entrypoint` (class, optionally `#method`) is only a marker: it selects which rule to run and records the expected verdict. The actual vulnerable/safe flow must be reachable from a controller in the compiled project

`mode: default` (or a bare string entry) runs the sample method directly as the entry point, as usual.

## Project layout

Put one Spring sample per project so the verdict is unambiguous — a `@Controller` that reaches the sink, plus the marker class named in `entrypoint`:

```
<test-project>/
├── settings.gradle.kts
├── build.gradle.kts
├── rule-test.yaml                        // entries with mode: spring-app
└── src/main/java/test/
    ├── VulnerableController.java          // @Controller with the tainted flow
    └── VulnerableSink.java                // holds the marker method named in entrypoint
```

`rule-test.yaml` lives at the project source root (`<projectSourceRoot>/rule-test.yaml`). Split positive and negative Spring cases into separate projects when a single controller graph cannot host both unambiguously.

## Required dependencies

Each Spring project needs at least:

- `org.springframework:spring-webmvc` and `spring-context` (so `@Controller` is recognized)
- Any libraries the sample itself uses (servlet-api, JDBC, etc.)

## Compile

```bash
opentaint compile <test-project> -o <test-compiled>
```

## Common pitfalls

- No `@Controller` reachable → `TestProjectAnalyzer` finds no Spring entry points and the `mode: spring-app` sample is skipped (logged). Always include a controller that reaches the sink
- Using a bare string (default mode) for a flow that only fires via Spring → false negative; switch that entry to `mode: spring-app`
- More than one ambiguous sample per controller graph → keep positive and negative in separate projects
