---
name: create-dataflow-approximation
description: Model a library method's taint propagation as code-based dataflow approximation and refine it against a test project until the sample passes. Use for a dropped external method whose propagation a passThrough copy cannot express
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Dataflow Approximation

Write a code-based approximation for a library method whose taint propagation depends on lambdas, callbacks, or async chains, then test it against the prepared test project and fix until the approximation sample passes

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Methods to model `<methods>` — the target method(s) and how taint flows through them, from the tracking file's `methods` (all `type: dataflow`)
- Tracking file `<tracking-file>` — the dataflow approximation unit (`<package-kebab>-dataflow`, e.g. `reactor-core-publisher-dataflow`). Default: `.opentaint/tracking/approximations/<name>.yaml`
- Approximation sources `<approx-src>` — this package's own directory for the `.java` approximation files. Default: `.opentaint/dataflow/<name>`
- Compiled test project `<test-compiled>` — the per-package compiled model to test against. Default: `.opentaint/test-compiled/<name>`

## Workflow

### 1. Write the approximation source

Create Java files in `<approx-src>`. Target the EXACT class named in `dropped-external-methods.yaml` — `@Approximate` matches only that class (unlike passThrough's `overrides: true`), and the dropped FQN reflects how the analyzer resolved the call: an interface-typed receiver (`Map m = ...; m.computeIfAbsent(...)`) drops `java.util.Map#computeIfAbsent`; a concrete one (`new HashMap<>()`) drops `java.util.HashMap#computeIfAbsent`. Don't substitute a supertype or subtype. Model the real propagation — never leave the body empty (it silently drops taint); when unsure how taint flows through the method, read the library source rather than guessing:

```java
package com.example.approximations;

import org.opentaint.ir.approximation.annotation.Approximate;
import org.opentaint.jvm.dataflow.approximations.ArgumentTypeContext;
import org.opentaint.jvm.dataflow.approximations.OpentaintNdUtil;

import java.util.function.Function;

@Approximate(com.example.lib.ReactiveProcessor.class)
public class ReactiveProcessor {

    // Model: taint on this flows through the function to the result
    public Object transform(@ArgumentTypeContext Function fn) throws Throwable {
        com.example.lib.ReactiveProcessor self =
            (com.example.lib.ReactiveProcessor) (Object) this;
        if (OpentaintNdUtil.nextBool()) return null;
        Object input = self.getValue();
        return fn.apply(input);
    }

    // Model: taint on this flows to the consumer argument
    public void subscribe(@ArgumentTypeContext java.util.function.Consumer consumer) {
        com.example.lib.ReactiveProcessor self =
            (com.example.lib.ReactiveProcessor) (Object) this;
        if (OpentaintNdUtil.nextBool()) {
            consumer.accept(self.getValue());
        }
    }
}
```

Wrapper-returning operators (a `Mono`/`Flux`, `Optional`, `Stream`, a builder — anything where the taint stays inside a container): declare the real concrete return type, not `Object`; in the `nextBool()` branch `return self`, not `null`; and extract → apply → re-wrap so a downstream extractor (`block`, `get`, …) can pull the tainted value back out:

```java
@Approximate(reactor.core.publisher.Mono.class)
public class Mono {
    public reactor.core.publisher.Mono map(@ArgumentTypeContext Function fn) throws Throwable {
        reactor.core.publisher.Mono self = (reactor.core.publisher.Mono) (Object) this;
        if (OpentaintNdUtil.nextBool()) return self;
        Object up = self.block();                                  // extract upstream element
        return reactor.core.publisher.Mono.justOrEmpty(fn.apply(up)); // apply mapper, re-wrap
    }
}
```

### 2. Test against the test project

Run `test approximation run` over `<test-compiled>` applying only this package's sources (`<approx-src>`); iterate the source until the sample passes:

```bash
opentaint test approximation run <test-compiled> \
  -o .opentaint/test-results/<name> \
  --dataflow-approximations <approx-src>
```

`test approximation run` applies its own bundled fixed source→sink rule automatically — you don't author or pass one. The CLI auto-compiles the `.java` sources against the analyzer JAR (for `@Approximate`, `OpentaintNdUtil`, `ArgumentTypeContext`) and the project's dependencies; if compilation fails it reports the errors and aborts before the tests. The sample that routes taint through the method is a `falseNegative` until the model propagates it. Read `.opentaint/test-results/<name>/test-result.json`:

- still `falseNegative` → the `@Approximate(...)` target class or a method signature doesn't match what the analyzer sees, or the body doesn't route taint from the real source to the modeled result/argument; diagnose the mismatch, don't rationalize a non-result. Most common: target-class mismatch with the dropped FQN — re-target the exact dropped class and match the cast (`(java.util.HashMap) (Object) this`)
- `falsePositive` (a negative sample fired) → the model is over-broad: it taints a read it shouldn't, e.g. data fetched under a different key/field than it was stored under. Narrow the propagation until the negative stays non-firing while the positive passes

### 3. When the sample won't pass after a couple of fixes

After ~2 fix attempts without a clearer cause — `@Approximate` target matches the dropped FQN, the body propagates from the modeled source slot to the result/argument, but the sample is still `falseNegative` — don't keep guessing. Leave `tests_passing: pending` and report non-convergence to the caller; the orchestrator escalates to debug-rule for a fact-reachability trace through the approximation point

## Key patterns

| Pattern | Usage |
|---|---|
| `@Approximate(TargetClass.class)` | Link the approximation to its target class. Must be on the compile classpath (a project dependency or a JDK type) |
| `(TargetClass) (Object) this` | Cast to reach the real object's methods |
| `@ArgumentTypeContext` | On lambda / functional-interface parameters |
| `OpentaintNdUtil.nextBool()` | Non-deterministic branch — the analyzer considers both paths |

## Output

- The approximation source(s) under `<approx-src>`
- Tracking updated: `artifact` and `stages.tests_passing` (per Tracking)
- Report the source path, a one-line test summary, and the exact `test approximation run` command used

## Tracking

In `<tracking-file>`, once the source exists and its sample passes:

```yaml
artifact: .opentaint/dataflow/<name>/com/example/approximations/ReactiveProcessor.java
stages:
  tests_passing: done
```

Do not touch other stages or fields

## Constraints

- Also the passThrough fallback — when a passThrough for a method won't converge, the orchestrator re-plans it here; target the same dropped class and the dataflow approximation overrides the passThrough (the orchestrator removes the stale passThrough config before this one is tested)
- Java 8 source compatibility
- Put the `@Approximate` classes in a neutral package (e.g. `com.example.approximations`) — never the target library's own package. Inside the library's package every bare FQN resolves to your approximation's non-generic class instead of the real type, breaking compilation wholesale
- Model every method and overload the unit lists, not only the shapes you happen to have a sample for — an under-covered unit silently drops taint through the overloads you skipped
- One approximation class per target class — a strict bijection enforced at load (duplicates throw `IllegalArgumentException`). Built-in dataflow approximations are first-priority and presumed correct; you cannot override them — see Troubleshooting if debug-rule traces a kill to one
- Method signatures must match the target class methods exactly
- Don't unpack or grep the analyzer JAR for built-in models or signatures — its internals aren't a stable API; go through the CLI

## Troubleshooting

When debug-rule traces a taint kill to an external method, walk this in order:

1. Confirm the method has a built-in — `approximated-external-methods.yaml` lists it (if you didn't pass an approximation to the scan, the listing is the bundled set)
2. Confirm from the debug-rule trace that taint dies at exactly that method
3. Classify the gap:
   - fits a from→to copy → write a passthrough override (built-in passthroughs are overrideable by design)
   - truly needs dataflow shape (lambdas/callbacks/async) → engine issue; built-in dataflows aren't locally overrideable — report it upstream
