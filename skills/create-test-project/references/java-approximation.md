# create-test-project — Java approximation test project

Language reference for a `dataflow` type, keyed to the body's steps.

## Workflow

### 1. Scaffold the project

`opentaint test approximation init <project>` scaffolds the Gradle build plus generic object-capable `Taint.java` markers and `approximation-rule.yaml`. The harness contains four independent rules: plain/plain, plain/starred, starred/plain, and starred/starred source/sink scope. Pass each lib as a `--dependency` at its exact version from the app's dependency management (`.opentaint/project/sources/**/pom.xml`) verbatim — including timestamped snapshots — not a guess: this Gradle build is the approximation's own compile environment, so it must recompile from these pins even after the main project drops that dependency.

```bash
opentaint test approximation init .opentaint/test-projects/<name> \
  --dependency "io.projectreactor:reactor-core:3.8.5"
```

### 2. Write the samples

Write one sample per method in the batch's `dataflow` bucket, across all its classes. Each `dataflow` entry records the method's `signature` (JVM descriptor) — reuse it so your sample matches. Look at how the method is actually called in the project to shape the sample and pick the receiver type. Each sample is a plain public method under `src/main/java/test/` — you don't author a rule; the scaffold's fixed `approximation-rule.yaml` is what the harness applies. The sample routes `Taint.source()` through the approximated method into `Taint.sink(...)`. The generic markers infer the real boundary types, including objects, arrays, and containers.

Classify every sample under all four rules. Each rule changes only the source and sink fact scope:

| Source scope | Sink scope | Rule id |
|---|---|---|
| base only | base only | `approximation-rule-plain-source-plain-sink` |
| base only | base or nested field | `approximation-rule-plain-source-starred-sink` |
| base plus nested fields | base only | `approximation-rule-starred-source-plain-sink` |
| base plus nested fields | base or nested field | `approximation-rule-starred-source-starred-sink` |

For each rule, put the sample in exactly one of `positive` or `negative`; omission is not allowed. Derive the four verdicts from the real method's propagation. Don't default them all to positive and don't remove a negative because the approximation is too broad. The matrix makes scope bugs observable: a method that carries only a nested input field into a nested output field can be negative for the first three rules and positive only for starred/starred.

Mark each method's test-project status (per Tracking): `done` once its sample is in the project. If no sample can be written for a method, exclude it, mark it `failed`, and note it in the summary — don't let one unmodelable method block the rest.

Positive sample — route `Taint.source()` through the approximated method into `Taint.sink(...)`, one per method being approximated. Declare the source variable as the method's real input type; `Taint.source()` is generic, so don't cast a tainted string into an unrelated type.

```java
package test;

import java.util.HashMap;
import java.util.Map;

public class ApproximationSamples {

    public void taintReachesSink() {
        String tainted = Taint.source();
        Map<String, String> cache = new HashMap<>();
        String routed = cache.computeIfAbsent(tainted, k -> k);   // the approximated method
        Taint.sink(routed);
    }
}
```

Add deliberate negative samples wherever the method has a non-propagating argument, field, key/value slot, receiver, result, or callback path. The analyzer is field-sensitive: taint set on one field must not surface from another. These negatives force a precise approximation instead of one that taints the whole object. Even a positive flow sample will usually have negative verdicts in its four-rule scope matrix; keep separate behavioral negatives when they exercise a different non-flow path.

```java
    public void taintStaysInItsField() {
        UserBean bean = new UserBean();
        bean.setName(Taint.source());    // taint stored in the `name` field
        Taint.sink(bean.getEmail());     // a different field — must stay clean
    }
```

Register the verdicts in `rule-test.yaml` at the test-project root (next to `build.gradle.kts`). Repeat every sample once under each rule, in that rule's `positive` or `negative` list. This hypothetical nested-field-only flow is positive only when both boundaries are starred:

```yaml
tests:
  - rule-id: approximation-rule.yaml#approximation-rule-plain-source-plain-sink
    negative:
      - test.ApproximationSamples#nestedFieldFlowsThrough
  - rule-id: approximation-rule.yaml#approximation-rule-plain-source-starred-sink
    negative:
      - test.ApproximationSamples#nestedFieldFlowsThrough
  - rule-id: approximation-rule.yaml#approximation-rule-starred-source-plain-sink
    negative:
      - test.ApproximationSamples#nestedFieldFlowsThrough
  - rule-id: approximation-rule.yaml#approximation-rule-starred-source-starred-sink
    positive:
      - test.ApproximationSamples#nestedFieldFlowsThrough
```

Note — a sample's receiver type fixes the dropped method's fully-qualified name, and the later approximation targets that exact class, so mirror the real call's receiver type. The same call off an interface-typed receiver (`Map<String,String> m`, e.g. a parameter) resolves to `java.util.Map#computeIfAbsent`, off a concrete one (`new HashMap<>()`) to `java.util.HashMap#computeIfAbsent` — match whichever the real flow uses.

When the approximated method hands the data to a callback instead of returning it, put the sink inside the callback body: `obj.method(c -> Taint.sink(tainted))`. Don't stash the value in a captured local or array and sink it after the call.

## Constraints

- The scaffold defaults to Java 8. A sample using a library that needs Java 17/21 must bump `source/targetCompatibility` and set `release` on the running JDK
- Diagnose a compile failure with `gradle compileJava --console=plain` in the sub-project — no gradlew is generated
