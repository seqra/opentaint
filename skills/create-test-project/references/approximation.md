# Dataflow approximation test project

## How it tests

`opentaint test approximation run` applies one fixed source → sink rule automatically — you do not author or pass a rule. That rule matches a fixed pair, `test.Taint.source()` and `test.Taint.sink(...)`, provided by the `Taint` helper scaffolded into the project. Your samples route taint from `Taint.source()` through the method being approximated into `Taint.sink(...)`. Granularity is per sample (`className#methodName`), so the one fixed rule covers every sample — a broken approximation only flips its own sample

`opentaint test approximation init <dir>` scaffolds the Gradle build, `Taint.java`, and the `approximation-rule.yaml` reference — you add only the samples (under `src/main/java/test/`)

## Positive sample

Put samples under `src/main/java/test/`, each a public method annotated with the fixed rule. A positive sends `Taint.source()` through the approximated method into `Taint.sink(...)`; it stays a `falseNegative` until the approximation propagates the taint, then flips to `success`. One positive per method being approximated

```java
package test;

import org.opentaint.sast.test.util.PositiveRuleSample;

import java.util.HashMap;
import java.util.Map;

public class ApproximationSamples {

    @PositiveRuleSample(value = "approximation-rule.yaml", id = "approximation-rule")
    public void taintReachesSink() {
        String tainted = Taint.source();
        Map<String, String> cache = new HashMap<>();
        String routed = cache.computeIfAbsent(tainted, k -> k);   // the approximated method
        Taint.sink(routed);
    }
}
```

## Negative sample — only for shared state

Add a `@NegativeRuleSample` only when the method holds state that taint must not cross — a container, cache, registry, or builder where you store under one key/field and read from another. Write a negative that stores tainted data under one variable and reads a different one; with a correct model the read stays clean, so the sample must not fire. For plain propagation (argument → result, or a value through a callback) the positive alone proves the model — skip the negative

```java
    @NegativeRuleSample(value = "approximation-rule.yaml", id = "approximation-rule")
    public void taintDoesNotCrossKeys() {
        Map<String, String> cache = new HashMap<>();
        cache.put("k1", Taint.source());   // taint stored under one key
        Taint.sink(cache.get("k2"));       // a different key — must stay clean
    }
```

A negative that fires (`falsePositive` in `test-result.json`) means the model is over-broad — it taints a read it shouldn't. Narrow the approximation until the negative stays non-firing while the positive still passes

## Notes

- `value`/`id` always reference the fixed rule: `approximation-rule.yaml` / `approximation-rule`. `test approximation run` applies its own bundled copy, so the project's `approximation-rule.yaml` is only a reference — what matters is that samples call `test.Taint.source()` / `test.Taint.sink(...)`
- the sample's receiver type fixes the dropped method's fully-qualified name, and the approximation must `@Approximate` that exact class — so mirror the real call's receiver type. An interface-typed receiver (`Map<String,String> m`, e.g. a method parameter) drops `java.util.Map#computeIfAbsent`; a concrete `Map<String,String> cache = new HashMap<>()` drops `java.util.HashMap#computeIfAbsent`. The `new HashMap<>()` form above is just one case — match whichever the real flow uses
