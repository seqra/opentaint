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
- Tracking file `<tracking-file>` — the dataflow approximation unit (`<package>-dataflow`). Default: `.opentaint/tracking/approximations/<name>.yaml`
- Approximation sources `<approx-src>` — this package's own directory for the `.java` approximation files. Default: `.opentaint/approximations/src/<name>`
- Compiled test project `<test-compiled>` — the per-package compiled model to test against. Default: `.opentaint/test-compiled/<name>`

## Workflow

### 1. Write the approximation source

Create Java files in `<approx-src>`. Target the EXACT class named in `dropped-external-methods.yaml` (the unit's `methods[].target`), whatever it is. `@Approximate` matches only that one class — unlike passThrough's `overrides: true`, it is not propagated to other types in the hierarchy — and the dropped FQN already reflects how the analyzer resolved the call: an interface-typed receiver (`Map<String,String> m = ...; m.computeIfAbsent(...)`) drops `java.util.Map#computeIfAbsent` → target `java.util.Map`; a concrete receiver (`new HashMap<>()`) drops `java.util.HashMap#computeIfAbsent` → target `java.util.HashMap`. Don't substitute a supertype or a subtype for what the dropped file names. Model the real propagation — never leave the body empty, an empty body silently drops the taint; in doubt about how taint flows through the method (which callback or argument carries it), read the library's source rather than guessing:

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

Wrapper-returning operators (a `Mono`/`Flux`, `Optional`, `Stream`, a builder — anything where the taint stays inside a container): three things matter beyond the plain case above. Declare the real concrete return type, not `Object` (the IFDS summary won't propagate otherwise); in the `nextBool()` branch `return self`, not `null` (returning `null` discards the container's taint on that path); and extract → apply → re-wrap so a downstream extractor (`block`, `get`, …) can pull the tainted value back out:

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

Run `test-approximations` over `<test-compiled>` applying only this package's sources (`<approx-src>`); iterate the source until the sample passes:

```bash
opentaint dev test-approximations <test-compiled> \
  -o .opentaint/test-results/<name> \
  --dataflow-approximations <approx-src>
```

test-approximations applies its own bundled fixed source→sink rule automatically — you don't author or pass one (there is no `--ruleset` flag); other packages' approximation sources are merged only at the final scan, not here. The CLI auto-compiles the `.java` sources against the analyzer JAR (for `@Approximate`, `OpentaintNdUtil`, `ArgumentTypeContext`) and the project's dependencies; if compilation fails it reports the errors and aborts before the tests. The sample that routes taint through the method is a `falseNegative` until the model propagates it. Read `.opentaint/test-results/<name>/test-result.json`:

- still `falseNegative` → the `@Approximate(...)` target class or a method signature doesn't match what the analyzer sees, or the body doesn't route taint from the real source to the modeled result/argument; diagnose the mismatch, don't rationalize a non-result. Most common: the target class doesn't equal the FQN in `dropped-external-methods.yaml` — you wrote a supertype/subtype (e.g. `java.util.Map` when the dropped file says `java.util.HashMap#computeIfAbsent`, or vice-versa). Re-target the exact dropped class and match the cast (`(java.util.HashMap) (Object) this`)
- `falsePositive` (a negative sample fired) → the model is over-broad: it taints a read it shouldn't, e.g. data fetched under a different key/field than it was stored under. Narrow the propagation until the negative stays non-firing while the positive passes (negatives exist only for shared-state methods — see create-test-project/references/approximation.md)

## Key patterns

| Pattern | Usage |
|---|---|
| `@Approximate(TargetClass.class)` | Link the approximation to its target class — the EXACT class `dropped-external-methods.yaml` names (interface or concrete, as the analyzer resolved it); matches only that class, not propagated to other types in the hierarchy. Must be on the compile classpath (a project dependency or a JDK type) |
| `(TargetClass) (Object) this` | Cast to reach the real object's methods |
| `@ArgumentTypeContext` | On lambda / functional-interface parameters |
| `OpentaintNdUtil.nextBool()` | Non-deterministic branch — the analyzer considers both paths |

## Output

- The approximation source(s) under `<approx-src>`
- Tracking updated: `artifact` and `stages.tests_passing` (per Tracking)
- Report the source path, a one-line test summary, and the exact `test-approximations` command used

## Tracking

In `<tracking-file>`, once the source exists and its sample passes:

```yaml
artifact: .opentaint/approximations/src/<name>/com/example/approximations/ReactiveProcessor.java
stages:
  tests_passing: done
```

Do not touch other stages or fields

## Constraints

- Java 8 source compatibility
- One approximation class per target class (strict bijection); never target a class that already has a built-in approximation — it errors at load with `IllegalArgumentException`
- Method signatures must match the target class methods exactly
