# Dataflow approximations

A dataflow approximation is a small Java implementation that substitutes for an unavailable external method during analysis. Its body exposes relevant calls and value movement to the analyzer. Use it when propagation crosses a callback, lambda, functional interface, coroutine continuation, stream operator, future stage, or another behavior that cannot be expressed as positional copies.

Code-based dataflow approximations are a JVM facility. Go library propagation currently uses its pass-through configuration format and the Go analyzer's native inter-procedural analysis.

For direct argument/receiver/result/state copies, prefer a [pass-through model](passthrough-models.md).

The built-in implementations are ordinary Java sources under [`model/java/dataflow`](../model/java/dataflow/src/main/java/). Representative models include [`Optional`](../model/java/dataflow/src/main/java/org/opentaint/jvm/dataflow/approximations/stdlib/Optional.java), [`Stream`](../model/java/dataflow/src/main/java/org/opentaint/jvm/dataflow/approximations/stdlib/Stream.java), [`CompletableFuture`](../model/java/dataflow/src/main/java/org/opentaint/jvm/dataflow/approximations/stdlib/CompletableFuture.java), executor models, and Kotlin coroutine [`Builders`](../model/java/dataflow/src/main/java/org/opentaint/jvm/dataflow/approximations/kotlin/Builders.java). These are the reference behavior behind the recipes in this guide.

## What an approximation should preserve

An approximation is a security semantics model, not a reimplementation of the library. It should preserve every relevant path by which data can:

- enter a callback argument;
- leave a callback return value;
- remain inside or leave a wrapper;
- reach a consumer or runnable;
- combine with another async/container value;
- flow through success, empty, alternate, or exceptional branches when relevant.

Keep control flow minimal. Do not perform network, file, process, clock, or other real side effects. The model is analyzed, not executed as a library replacement.

## Minimal model

```java
package com.example.approximations;

import java.util.function.Function;
import org.opentaint.ir.approximation.annotation.Approximate;
import org.opentaint.jvm.dataflow.approximations.ArgumentTypeContext;

@Approximate(com.example.lib.Box.class)
public class Box {
    public Object map(@ArgumentTypeContext Function mapper) {
        com.example.lib.Box self =
            (com.example.lib.Box) (Object) this;
        Object input = self.get();
        return mapper.apply(input);
    }
}
```

The approximation class may have any neutral package, but the annotation target and method signature must identify the real API. The double cast accesses the real receiver from the substitute body.

## Matching constraints

### Target the exact analyzed class

`@Approximate` matches one class, not its full hierarchy. Use the declaring/receiver class reported in `dropped-external-methods.yaml`.

```java
@Approximate(java.util.Map.class)      // for a Map-typed receiver
@Approximate(java.util.HashMap.class)  // for a HashMap-resolved receiver
```

These are different targets. Mirror the real sample's receiver type when testing.

`@ApproximateByName` exists for built-in cases whose target cannot be referenced normally, such as generated Kotlin facade classes. Prefer typed `@Approximate(Target.class)` for custom models because it gives compile-time validation.

### Match the real method descriptor

Preserve:

- method name, including generated names such as `$default` when required;
- static versus instance dispatch;
- parameter count and erased JVM parameter types;
- return type;
- overloads that can occur in the supported library versions;
- checked exceptions where the model body needs them.

Generics may be erased in the signature, but a concrete wrapper return type still matters for downstream calls. Do not use `Object` merely to make compilation easier when the real method returns `Optional`, `Stream`, `Mono`, `Future`, or a builder.

One approximation class may model many methods of one target class. Each target class may have only one approximation class in a run. A second custom model for the same target, or a custom model colliding with a built-in dataflow approximation, is logged and rejected during indexing; the already registered mapping remains. Never rely on classpath order to choose between them.

## Callback parameters

Annotate every functional-interface parameter that the model invokes:

```java
public Object transform(@ArgumentTypeContext Function fn) {
    return fn.apply(readInput());
}
```

`@ArgumentTypeContext` preserves the call-site functional type context needed to analyze lambdas and method references. It is not necessary on ordinary values that the model only copies or passes through without invoking.

## Modeling patterns

### Value through a mapper

```java
public java.util.Optional map(@ArgumentTypeContext Function mapper) {
    java.util.Optional self =
        (java.util.Optional) (Object) this;
    if (self.isPresent()) {
        Object mapped = mapper.apply(self.get());
        return java.util.Optional.ofNullable(mapped);
    }
    return java.util.Optional.empty();
}
```

Extract the wrapped value, invoke the mapper, and re-wrap the mapper result. Returning the original receiver would miss transformations introduced inside the callback.

### Flat map

```java
public java.util.Optional flatMap(@ArgumentTypeContext Function mapper) {
    java.util.Optional self =
        (java.util.Optional) (Object) this;
    if (self.isPresent()) {
        return (java.util.Optional) mapper.apply(self.get());
    }
    return java.util.Optional.empty();
}
```

Do not wrap an already wrapped callback result.

### Consumer or terminal callback

```java
public void forEach(@ArgumentTypeContext java.util.function.Consumer action) {
    java.util.stream.Stream self =
        (java.util.stream.Stream) (Object) this;
    java.util.Iterator it = self.iterator();
    if (it.hasNext()) {
        action.accept(it.next());
    }
}
```

One representative element is enough to expose the flow; iterating the entire abstract collection adds analysis cost without adding a new taint relationship.

### Supplier into async wrapper

```java
public static java.util.concurrent.CompletableFuture supplyAsync(
        @ArgumentTypeContext java.util.function.Supplier supplier) {
    Object value = supplier.get();
    return java.util.concurrent.CompletableFuture.completedFuture(value);
}
```

Invoke the supplier and return a real wrapper carrying its result so later stages and extractors remain connected.

### Async transform

```java
public java.util.concurrent.CompletableFuture thenApply(
        @ArgumentTypeContext java.util.function.Function fn) throws Throwable {
    java.util.concurrent.CompletableFuture self =
        (java.util.concurrent.CompletableFuture) (Object) this;
    Object mapped = fn.apply(self.get());
    return java.util.concurrent.CompletableFuture.completedFuture(mapped);
}
```

Executor arguments normally affect scheduling, not value propagation. Preserve them in the signature but do not invent taint edges from an executor to the result.

### Combining two wrapped values

```java
public java.util.concurrent.CompletableFuture thenCombine(
        java.util.concurrent.CompletionStage other,
        @ArgumentTypeContext java.util.function.BiFunction fn) throws Throwable {
    java.util.concurrent.CompletableFuture self =
        (java.util.concurrent.CompletableFuture) (Object) this;
    java.util.concurrent.CompletableFuture rhs =
        (java.util.concurrent.CompletableFuture) other;
    Object value = fn.apply(self.get(), rhs.get());
    return java.util.concurrent.CompletableFuture.completedFuture(value);
}
```

Feed every value that the real callback can observe. Omitting one side creates a direction-specific false negative.

### Runnable or callback with side effects

```java
public void execute(@ArgumentTypeContext Runnable command) {
    command.run();
}
```

The callback body may write tainted data to fields or sinks even if the modeled method returns no value.

### Alternative paths

Use `OpentaintNdUtil.nextBool()` when the analyzer must consider a path that may or may not execute, especially for async scheduling, empty wrappers, or alternate completion:

```java
import org.opentaint.jvm.dataflow.approximations.OpentaintNdUtil;

public java.util.concurrent.CompletableFuture completeAsync(
        @ArgumentTypeContext java.util.function.Supplier supplier) {
    java.util.concurrent.CompletableFuture self =
        (java.util.concurrent.CompletableFuture) (Object) this;
    if (OpentaintNdUtil.nextBool()) {
        return self;
    }
    self.complete(supplier.get());
    return self;
}
```

Keep a wrapper-preserving branch when downstream calls need a non-null receiver. A branch that returns only `null` can accidentally terminate the path the model is meant to expose.

## Kotlin and coroutine APIs

Approximation sources are Java 8-compatible even when they target Kotlin. Match compiled JVM signatures, including facade classes, `Continuation` parameters, `FunctionN` interfaces, and `$default` bridges when those are the calls the analyzer resolves.

A coroutine builder typically invokes its `Function2` body and, for value-producing builders, stores the result in a real `Deferred`-like wrapper. Do not model only the source-level Kotlin signature; inspect the dropped JVM method and test the compiled call shape.

## Project layout and compilation

Put custom sources in a directory dedicated to one library unit:

```text
.opentaint/dataflow/example/
└── com/example/approximations/Box.java
```

Use a neutral package such as `com.example.approximations`, not the target library's package. Defining a non-generic approximation class beside the real generic class can shadow imports and break compilation.

The CLI compiles Java sources supplied through `--dataflow-approximations` against the analyzer and the project model's dependencies.

## Testing

Scaffold and compile a dedicated approximation project:

```bash
opentaint test approximation init \
  .opentaint/test-projects/example-dataflow \
  --dependency com.example:example-lib:1.2.3

opentaint compile .opentaint/test-projects/example-dataflow \
  -o .opentaint/test-compiled/example-dataflow
```

Each positive routes the fixed marker through exactly one behavior:

```java
package test;

public class BoxSamples {
    public void mapCarriesTaint() {
        String input = Taint.source();
        com.example.lib.Box box = com.example.lib.Box.of(input);
        Object output = box.map(x -> x.toString().trim());
        Taint.sink(output);
    }
}
```

```yaml
tests:
  - rule-id: approximation-rule.yaml#approximation-rule
    positive:
      - test.BoxSamples#mapCarriesTaint
```

Run only the approximation sources for that unit:

```bash
opentaint test approximation run \
  .opentaint/test-compiled/example-dataflow \
  --dataflow-approximations .opentaint/dataflow/example \
  -o .opentaint/test-results/example-dataflow
```

The command supplies its own fixed rule automatically — a built-in `Taint.source()`-to-`Taint.sink(...)` harness reported under the id `approximation-rule.yaml#approximation-rule` — so you never write that rule file yourself. A positive remains in `falseNegative` until the model exposes the path.

Add negatives when state must remain separated—for example, different keys, fields, channels, or alternate values. A `falsePositive` means the model introduced a propagation path the real API does not have.

Test at least:

- every modeled method and overload;
- every callback input and return direction;
- empty and non-empty wrapper behavior where it changes flow;
- sync and async variants;
- combining operators from both operands;
- terminal consumers and extractors;
- generated Kotlin bridge methods that occur in real bytecode;
- state-separation negatives for containers, registries, caches, and builders.

## Applying and debugging

```bash
opentaint scan \
  --project-model .opentaint/project \
  --ruleset builtin \
  --dataflow-approximations .opentaint/dataflow/example \
  --track-external-methods \
  -o .opentaint/results/report.sarif
```

If the sample still fails:

1. compare the dropped FQN with the `@Approximate` target;
2. compare the real JVM descriptor with the model method;
3. confirm every invoked functional parameter has `@ArgumentTypeContext`;
4. walk the body from wrapped input to callback and from callback result to returned wrapper;
5. confirm the model is loaded and does not collide with another target model;
6. run rule reachability with the same `--dataflow-approximations` directory and inspect `debug-ifds-fact-reachability.sarif`.

A successfully installed dataflow approximation makes the call analyzable, while pass-through rules are applied to unresolved calls. A pass-through for that same method therefore does not supplement the approximation. Remove the stale pass-through once behavior is modeled in code. Built-in dataflow approximations cannot currently be replaced locally because the target-class mapping is one-to-one; report a missing or incorrect built-in behavior upstream.

## Review checklist

- The behavior truly needs callback or control-flow modeling.
- The annotation targets the exact class resolved in the dropped-method report.
- Method descriptors, staticness, return types, overloads, and generated bridges match.
- Every invoked functional parameter has `@ArgumentTypeContext`.
- Mapper inputs enter callbacks and callback results re-enter the correct wrapper.
- Consumers and runnables are actually invoked.
- Combining methods include every relevant operand.
- Alternative branches preserve downstream reachability without inventing impossible flows.
- The source is Java 8-compatible and in a neutral package.
- Positives cover all modeled methods; precision-sensitive state has negatives.
- No second model targets the same class.
