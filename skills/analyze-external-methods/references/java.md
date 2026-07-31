# analyze-external-methods — Java / JVM

## Workflow

### 1. Classify propagation

An application-internal dropped method sits in the project's own sources under the project root — read it directly. For a library method, prefer the dependency's source jar; when only bytecode is available, the resolved jars sit under `.opentaint/project/dependencies` — locate the class with `unzip -l <jar> | grep <class-as-path>` (dotted class with `.` → `/`) and disassemble it with `javap -c -p -classpath <jar> <fully.qualified.ClassName>`, or decompile it for readable source.

passthrough examples — the data is copied from one position to another:
- `StringBuilder`/`StringBuffer#append`, `String` transforms (`concat`, `substring`, `replace`, `format`, `getBytes`)
- collection / map `add`/`put`/`get`/`iterator`/`toArray`, `Stream#collect`, wrapper boxing, `parse`/`valueOf` conversions that keep the data
- external key-value stores — a `set`/`put` paired with a `get` carries the value across the round trip; model both ends

dataflow examples — the data moves through a function/lambda/callback parameter or an async chain:
- `java.util.Optional#map`, `#flatMap`
- `java.util.stream.Stream#map`, `#flatMap`, `#forEach`
- `java.util.concurrent.CompletableFuture#thenApply`, `#thenCompose`, `#thenCombine`, `#supplyAsync`; `CompletionStage#thenApply`; `ExecutorService#submit`
- reactive/async libraries — Reactor `Mono`/`Flux#map`/`#flatMap`, RxJava `Observable#map`, or an event-handler registration that later invokes the handler with tainted data

skipped examples — the method carries the data nowhere:
- predicates and inspectors returning a boolean or number — `Object#equals`, `Class#isInstance`, `hashCode`, `compareTo`, `size`/`length`, and string tests like hutool `CharSequenceUtil#contains`/`#startWith`/`#isEmpty`/`#isBlank`/`#isNumeric`
- number conversions that collapse the data — `Integer#parseInt`, `#intValue`, `#valueOf`
- `toString` — always skip any `toString()` method on any class, never model it
- synthetic lambda constructors — a `…$jIR_lambda$…#<init>` name is engine-internal capture machinery, never a carrier

`signature` — the method's JVM descriptor, e.g. `(Ljava/lang/String;)Ljava/lang/String;`, copied from the plan. Put it on every entry so overloads stay distinct.
