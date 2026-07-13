# create-test-project — Java Spring app-mode samples

Load this when a plain method-level `rule` sample returns `falseNegative` because the flow only fires through a Spring entry point (controller → bean → sink): the tainted data must flow from a discovered `@Controller`, so a sample analyzed as a bare method won't trigger the rule. Run such a sample in Spring app mode instead.

## Workflow

Spring app mode is selected per sample in `rule-test.yaml` — an entry is either a bare string (default: the method itself is the analysis entry point) or an object with `mode: spring-app`:

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

With `mode: spring-app` the analysis entry points become the project's Spring web dispatch entry points instead of the sample method: taint originates from real `@Controller` request parameters and must reach the sink through normal Spring wiring. The `entrypoint` (class, optionally `#method`) is only a marker — it selects which rule to run and records the expected verdict; the actual vulnerable/safe flow must be reachable from a controller in the compiled project.

Put one Spring sample per project so the verdict is unambiguous — a `@Controller` that reaches the sink, plus the marker class named in `entrypoint`, with `rule-test.yaml` at the project source root:

```
.opentaint/test-projects/<name>/
├── settings.gradle.kts
├── build.gradle.kts
├── rule-test.yaml
└── src/main/java/test/
    ├── VulnerableController.java    // @Controller with the tainted flow
    └── VulnerableSink.java          // holds the marker method named in entrypoint
```

Split positive and negative Spring cases into separate projects when a single controller graph can't host both unambiguously. Each project needs `org.springframework:spring-webmvc` and `spring-context` so `@Controller` is recognized, plus any library the sample itself uses.

## Gotchas

- No `@Controller` reachable in the project → no Spring entry point is found and the `mode: spring-app` sample is skipped (logged). Always include a controller that reaches the sink.
- A bare-string (default-mode) entry for a flow that only fires via Spring → false negative; give it `mode: spring-app`.
