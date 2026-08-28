# Whole-project prescan and initialization fact propagation

- **Status:** design proposal
- **Languages:** JVM and Go
- **Scope:** prescan only; the full scan and its externally selected entry points remain unchanged

## 1. Summary

The prescan currently starts from the same externally visible entry points as the full scan. It therefore misses facts created in code that is semantically executed before, or independently of, those entry points: JVM class initializers and constructors, Go package initialization, private helpers, and functions reached only through a dynamically stored callable.

This design changes the prescan in three ways:

1. Start every executable project method/function in the prescan, including private declarations and JVM/Go initialization code.
2. Whenever the prescan produces a zero-to-fact (`Z2F`) summary whose final access path has `AccessPathBase.ClassStatic`, submit that fact as an initial fact to every method/function in the project prescan scope.
3. On the JVM, whenever a constructor produces a receiver-rooted `Z2F` summary, seed that fact into every receiver-bearing method declared by the same class.

The broad roots are only a discovery mechanism. They must not become full-scan roots and must not make unreachable private code reportable. Seed eligibility is based on zero-derived summaries, while target installation deliberately reuses the ordinary initial-fact path and therefore participates in the target as an `F2F` premise.

For Go, package `init` functions are included in the broad scope, and their global facts use rule 2. Go has no language-level constructor. Functions named `NewT`, `newT`, or similar are ordinary factories and are not treated as constructors by name.

## 2. Motivation and failure mode

A representative Go program has this shape:

```go
var client = buildClient() // executed by package initialization

func EntryPoint() {
    client.Do() // dynamic target depends on the value stored above
}
```

The current staged analysis starts the prescan from `EntryPoint`. Package initialization is not a call-reachable predecessor of that function, so the prescan never learns the callable or concrete type stored in `client`. The full scan then starts with an incomplete dynamic-call-resolution index and cannot resolve `client.Do()`.

The JVM equivalent is a lambda, implementation object, or tainted field stored by `<clinit>` or `<init>` and consumed by a method which has no call-graph path back to that initializer.

Ordinary interprocedural propagation cannot repair this. It follows calls from callers to callees, while initialization state has to flow in the other direction:

```text
initializer or constructor
          |
          | discovered Z2F state
          v
unrelated consumer method --> dynamic call/type/rule discovery
```

## 3. Goals

The feature must:

- make prescan discovery independent of public/exported entry-point selection;
- include JVM `<clinit>`, JVM constructors and instance-initializer code compiled into them, and Go package initialization;
- make unconditional global/static facts visible in every project method/function;
- make unconditional JVM constructor receiver state visible in methods of the same declaration class;
- work across analysis units/packages and regardless of discovery order;
- pass the complete qualifying `FinalFactAp` into each target's normal initial-fact handling;
- converge under repeated and cyclic propagation;
- preserve phase isolation: only information intentionally retained by the language analysis manager, such as relevant rule IDs and dynamic-call-resolution knowledge, crosses into the full scan.

## 4. Non-goals

This proposal does not:

- broaden the full scan's selected entry points;
- start every dependency or standard-library method as a prescan root;
- model JVM class-loading order or Go package initialization order precisely;
- infer Go constructors from names, return types, or coding conventions;
- make constructor state flow to subclasses or overriding methods in the first version;
- implement Go global aliasing in `GoLocalAliasAnalysis`;
- turn `F2F` or N-dimensional summaries into global initial state;
- persist prescan-propagated facts into the full-scan summary store.

The analysis is a may-analysis. When several constructors can initialize the same class differently, their receiver facts are unioned. The design does not attempt path- or constructor-choice correlation.

## 5. Terminology and semantic contract

### 5.1 Project prescan scope

The **project prescan scope** is the finite catalog of project-owned executable methods/functions that are started from zero during prescan. “All methods/functions” means all executable project declarations, not all declarations on the classpath/program.

Call-reachable dependency approximations can still be analyzed through normal call handling. They are not independently started and are not broadcast targets.

### 5.2 Initialization seed

A prescan **initialization seed** is a `FinalFactAp` selected from an accepted `ZeroToFact` summary and submitted to another method through `submitExternalInitialFact`:

```text
input fact premise -> target-entry fact
```

The target's method-start flow and initial-fact abstraction are intentionally applied. The resulting target edge is therefore `FactToFact`, rather than a copied `ZeroToFact` edge.

This reuses established runner accounting, method-start transformation, exclusion/refinement handling, and initial-fact deduplication. It does not make target summaries transitively qualify as new `Z2F` seeds; the coordinator continues to classify only genuinely accepted `ZeroToFact` summaries.

### 5.3 Exact fact preservation

The coordinator passes the whole `FinalFactAp` to the normal initial-fact API, including:

- its accessors;
- type-information accessors;
- taint marks and values;
- exclusions/refinement state;
- the identity in `ClassStaticAccessor`.

Only facts whose base and source method qualify are propagated. The coordinator does not strip suffixes or generalize facts merely for fan-out. Normal method-start transformation and initial-fact abstraction may still refine the fact when it is installed in the target.

The singleton `ClassStatic` base is not the identity of a particular field/global. For example:

```text
JVM: ClassStatic / ClassStaticAccessor(class) / FieldAccessor(field) / ...
Go:  ClassStatic / ClassStaticAccessor(global full name) / ...
```

The accessor chain must therefore remain intact.

## 6. Prescan scope

### 6.1 JVM

Include every project-owned `JIRMethod` with an executable body, regardless of visibility or staticness:

- public, protected, package-private, and private methods;
- static and instance methods;
- constructors (`<init>`);
- class initializers (`<clinit>`);
- concrete default/private interface methods;
- project-generated bridge, anonymous-class, and lambda methods when the IR exposes an executable body.

Exclude:

- abstract and native methods;
- declarations without an executable CFG/body;
- dependency/runtime methods that are not project-owned.

This must not reuse `allAnalyzableMethods()` unchanged: that helper currently excludes `<clinit>` and does not express the complete body/ownership contract above.

### 6.2 Go

For every `GoIRPackage` with `isProject == true`, include every distinct `GoIRFunction` with `hasBody == true`, regardless of:

- export status;
- whether it is a top-level function or receiver method;
- whether it is private/unexported;
- `parent` (nested/anonymous functions);
- `isSynthetic`, provided it has executable project IR.

Explicitly include `GoIRPackage.initFunction` and deduplicate it against `package.functions` by function identity. Exclude dependency/standard-library packages and bodyless declarations.

Starting a closure with `EmptyMethodContext` cannot supply its captured values. That is acceptable for conservative prescan discovery; context-specific closure activations remain possible through normal call resolution, and the seed coordinator replays applicable global seeds to those activations.

### 6.3 Full-scan roots and debug selection

Production project analysis should pass two separate lists:

```text
analysisEntryPoints  = existing public/framework/debug-selected roots
prescanRoots         = all executable project methods/functions
```

Only `analysisEntryPoints` are used by the full scan, vulnerability confirmation, and trace entry-point validation.

A debug selector continues to restrict the full scan, but does not silently restrict the production prescan. Low-level tests and specialized callers can use a compatibility overload whose prescan roots default to their supplied entry points, or can pass an explicit prescan scope. This prevents every unit test from unexpectedly becoming a whole-program test while giving production the required behavior.

## 7. Propagation rules

The language mapping is:

| Producer | Eligible fact | Targets |
|---|---|---|
| JVM `<clinit>` or any other analyzed method | `Z2F ClassStatic` | every project prescan method |
| JVM `<init>` | `Z2F ClassStatic` | every project prescan method |
| JVM `<init>` | `Z2F This` | receiver-bearing methods declared by the exact same class |
| Go package initialization or any other analyzed function | `Z2F ClassStatic` | every project prescan function |
| Go `NewT`-style factory | no special category | normal call propagation only; rule A still applies if it writes a global |

### 7.1 Rule A: static/global facts

When a newly canonicalized method summary contains:

```text
Edge.ZeroToFact(finalFact.base == AccessPathBase.ClassStatic)
```

register the exact `finalFact` as a global prescan seed and submit it as an initial fact to every activated entry point whose method is in the project prescan scope.

This rule is language-neutral:

- a JVM static-field fact is visible to every project method;
- a Go global fact is visible to every project function;
- the producer and consumer may be in different analysis units/packages;
- the producer may be a project method or a normally analyzed dependency/approximation, but targets remain limited to project scope.

Facts rooted at `Constant`, `Argument`, `Return`, `This`, or `LocalVar` do not qualify for this rule.

### 7.2 Rule B: JVM constructor receiver facts

When a newly canonicalized summary satisfies all of the following:

```text
edge is Edge.ZeroToFact
source method is JIRMethod with isConstructor == true
edge.finalFact.base == AccessPathBase.This
source class is project-owned and indexed in the prescan scope
```

register the exact fact under the constructor's declaration class. Submit it as an initial fact to every executable receiver-bearing method declared by that exact class:

- instance methods;
- constructors, including other overloads.

Do not deliver receiver facts to static methods or `<clinit>`, because `This` is not a valid base there. The fact needs no rebase: constructor `This` and instance-method `This` denote the receiver at their respective method boundaries.

Static facts emitted by a constructor use rule A. Constructor facts rooted at arguments, constants, return, exception, or locals are not class initialization state and are not broadcast.

Java and Kotlin instance initializer blocks compile into `<init>` bodies and are covered by this rule. Constructor delegation also works naturally: a `this(...)` or `super(...)` call maps receiver facts back to the calling constructor before its summary is produced.

The initial version uses exact declaration-class ownership, as requested. A superclass constructor fact is therefore not directly seeded into methods declared only by a subclass. Extending the target set through the class hierarchy is a separate precision/soundness decision and should be measured independently.

### 7.3 Go initialization semantics

Go has package initialization but no language-level instance constructor:

- package `init` and compiler-composed package initialization functions are included as prescan roots;
- their writes to package globals produce `ClassStatic` facts and are distributed by rule A;
- `func NewT(...) *T` is an ordinary function, even when idiomatic, and receives no special owner fan-out;
- naming a function `init` does not create receiver/class semantics.

A Go package `init` function has no meaningful receiver-rooted exit state. Any surviving initialization state relevant outside the function should be global/static and is already handled by rule A. Consequently there is no Go counterpart to rule B in this version.

If future IR metadata provides an explicit, sound “initializer for receiver type T” relation, it can implement the same owner-seed policy. Name or return-type heuristics are not sufficient.

## 8. Proposed architecture

### 8.1 Separate analysis entry points from prescan roots

Introduce an analysis-scope value at the SAST driver boundary:

```kotlin
data class AnalysisScope<M>(
    val analysisEntryPoints: List<M>,
    val prescanRoots: List<M>,
)
```

`ProjectAnalyzer` already owns project-boundary and entry-point selection. It should build both lists and pass them to `TaintAnalyzer`. This is preferable to making the generic IFDS engine enumerate language classpaths.

`TaintAnalyzer.analyzeStaged` then creates two `MethodWithContext` lists:

```text
prescan:  prescanRoots + EmptyMethodContext
full:     analysisEntryPoints + EmptyMethodContext
```

The current full-scan, confirmation, and trace code continues to use only `analysisEntryPoints`.

### 8.2 Language policy

Provide a small prescan propagation policy with language-specific ownership knowledge:

```kotlin
interface PrescanPropagationPolicy<M> {
    fun initializerOwner(method: M): InitializerOwner?
    fun acceptsReceiverSeed(method: M, owner: InitializerOwner): Boolean
}
```

The JVM policy recognizes project constructors and exact enclosing classes. The Go policy returns no instance initializer owner. Static/global classification stays in the common core because it is represented by the common `ClassStatic` base.

The policy is evaluated only for methods in the prepared catalog; it must not perform classpath scans from worker threads.

### 8.3 Phase-local seed coordinator

Add a `PrescanSeedCoordinator` owned by `TaintAnalysisUnitRunnerManager`. It exists only while `Phase.Prescan` is active and holds:

```text
scopeMethods                 set of project prescan methods
globalSeeds                  append-only canonical fact log
ownerSeeds[owner]            append-only canonical receiver-fact log
globalVersion[entryPoint]    replay cursor per activated entry point
ownerVersion[entryPoint]     replay cursor for its owner
```

The coordinator has two inputs:

1. **A canonical summary delta.** Newly stored `Z2F` summaries are classified into global or owner seeds.
2. **An activated method entry point.** Applicable previously discovered seeds are replayed to it.

These two inputs make behavior independent of scheduling order:

- producer first: the seed is logged, then replayed when a consumer activates;
- consumer first: it receives the seed when the producer later publishes it;
- a dynamic context activates later: it receives the current seed snapshot on activation.

All roots are known before worker execution, but entry-point activation is still event-driven because methods can have multiple/contextual entry points and runners operate concurrently.

### 8.4 Observe canonical summary deltas

Do not observe the raw list passed to `AnalysisUnitRunnerManager.newSummaryEdges`. Summary storage can canonicalize, subsume, or discard an edge. Propagation must observe the delta that `SummaryEdgeStorageWithSubscribers` actually accepted.

The preferred change is for `SummaryEdgeStorageWithSubscribers.addEdges` (and the wrapping `MethodSummariesUnitStorage.addSummaryEdges`) to return or publish its `addedEdges` canonical delta. `AnalysisUnitRunnerManager` stores the edges first and forwards only that delta to the prescan coordinator.

This location also covers summaries loaded from persistent storage, because `MethodAnalyzer.loadSummariesFromRunner` republishes loaded summaries through `runner.addNewSummaryEdges`.

### 8.5 Deliver seeds through the existing initial-fact event

Route every delivered seed through the existing runner API:

```text
submitExternalInitialFact(methodEntryPoint, finalFact)
```

Handling obtains or creates the target `MethodAnalyzer` and calls its existing `addInitialFact` API. This retains existing enqueue/process accounting, cancellation, method-start handling, and per-unit runner routing, so analysis completion cannot race ahead of fan-out work.

Each fact is an ordinary counted runner event. Batching can be added later if initial-fact events gain a batch form.

### 8.6 Activation hook

When `TaintAnalysisUnitRunner` resolves a `MethodWithContext` into one or more `MethodEntryPoint`s, it should notify the coordinator before or immediately after adding the initial zero fact. The coordinator then schedules the seed snapshot for that exact entry point.

The order between the ordinary zero start and replayed seeds is not semantically significant because edge processing is monotone. Both events must be counted before global quiescence is declared.

## 9. Algorithm

At prescan start:

```text
catalog = build project prescan method/owner index
coordinator.reset(catalog, current prescan AP manager)
submit every prescan root from Zero
```

On entry-point activation:

```text
if method not in project prescan scope: return
mark entry point active
deliver globalSeeds since globalVersion[entryPoint]
if entry point accepts receiver facts:
    deliver ownerSeeds[owner] since ownerVersion[entryPoint]
advance cursors atomically
```

On accepted summary delta:

```text
for each ZeroToFact edge:
    if final base is ClassStatic:
        if exact/canonical seed is new:
            append to globalSeeds
            deliver to all active in-scope entry points

    if source is a JVM constructor and final base is This:
        owner = exact declaration class
        if exact/canonical seed is new for owner:
            append to ownerSeeds[owner]
            deliver to all active receiver-bearing entry points of owner
```

Before full scan:

```text
disable and clear coordinator
select FullScan
reset AP manager and IFDS storages as today
start analysisEntryPoints only
```

## 10. Concurrency, deduplication, and termination

The coordinator is shared by concurrently running analysis units. Its state updates must be linearizable. A simple implementation can synchronize classification/version updates, collect deliveries while holding the lock, release the lock, and enqueue runner events afterward. It must never call into a runner while holding the coordinator lock.

Required invariants:

1. Each exact canonical global fact enters `globalSeeds` at most once.
2. Each exact canonical constructor receiver fact enters its owner log at most once.
3. Each activated method entry point consumes each applicable log position at most once.
4. A seed discovered concurrently with activation is delivered by either the activation snapshot or the new-seed fan-out, never missed; duplicate scheduling is acceptable only if the target edge store removes it.
5. Propagated facts enter targets as `F2F` edges and therefore do not re-enter the coordinator merely because they were broadcast.
6. Repeated qualifying source summaries are rejected by canonical summary storage or the corresponding seed registry.

Use AP-manager-compatible/canonical fact storage rather than relying on object identity. If a later, more general fact subsumes an earlier narrow fact, it is a new seed and is propagated. Already delivered narrow facts are not retracted; this is conservative and matches the monotone IFDS analysis.

The append-log plus per-entry-point cursor representation avoids a separate `Set<(target, fact)>` with explicit Cartesian-product metadata. The target analyzers still necessarily process the applicable facts.

Termination follows from the existing finite/capped access-path domain plus the two monotone seed registries. The feature must not introduce a retry loop or re-enqueue an existing seed merely because another method summarized it.

## 11. Phase isolation and retained knowledge

`resetApManager` currently clears method facts, summary storages, subscribers, vulnerabilities, and work queues between phases while retaining the language analysis-manager/context objects. That is the intended boundary:

- prescan facts and synthetic broad-root reachability are discarded;
- the full scan starts only from externally selected entry points;
- relevant rule IDs and learned lambda/closure call-resolution values remain available;
- phase-specific subscribers/caches are reset and reattached in the full scan.

The coordinator must be explicitly disabled before the full-scan reset. Full-scan summaries must never trigger global or constructor fan-out.

Persisted prescan summaries are treated like newly discovered summaries after canonical insertion. No coordinator state itself is serialized, because facts are tied to the prescan AP manager and can be reconstructed from summaries/analysis.

## 12. Precision and performance

Starting the complete project scope and broadcasting every global seed increases prescan work. The correctness contract must not be weakened by a silent method limit or fan-out cap.

It also intentionally over-approximates discovery. Starting a private function from zero can make an unconditional write in that otherwise unreachable function appear as a global seed. That may add dynamic-call candidates or relevant rules, but it cannot by itself create a final finding: the full scan discards prescan facts, starts from the original external entry points, and must re-establish the complete source-to-sink flow. This separation is a required safety property, not merely a performance optimization.

Initial mitigations:

- deduplicate the method catalog and canonical seeds before scheduling;
- use append-only logs and replay cursors instead of pair sets;
- batch deliveries per target/unit;
- do not independently start dependencies;
- propagate only `Z2F`, only `ClassStatic` globally, and only constructor `This` within an owner;
- retain the existing cheap prescan AP manager and timeout policy.

Add phase metrics:

```text
prescan.scope.methods
prescan.scope.units
prescan.seeds.global
prescan.seeds.constructor
prescan.seed.deliveries.global
prescan.seed.deliveries.constructor
prescan.seed.duplicates
prescan.seed.replayed_entrypoints
```

Log the largest fan-out facts/owners and distinguish scope-start events from propagation events. These measurements are required before changing timeout allocation.

If the current prescan timeout expires, the existing staged-analysis behavior may continue with partial learned knowledge, but status/logging must clearly say that the prescan and its seed closure were incomplete. This design does not claim completeness after a timeout.

## 13. Test plan

### 13.1 Scope selection

JVM tests:

- private, package-private, protected, and public executable methods are roots;
- static methods, constructors, and `<clinit>` are roots;
- concrete interface/default methods and anonymous project methods are included;
- abstract/native/bodyless and dependency methods are excluded;
- debug-selected full scan still receives only the selected entry point.

Go tests:

- exported and unexported top-level functions are roots;
- value/pointer receiver methods are roots;
- package `init` is a root;
- nested/anonymous and executable synthetic project functions are included;
- bodyless, dependency, and standard-library functions are excluded;
- duplicates between `functions` and `initFunction` are removed.

### 13.2 Static/global propagation

Common/core tests:

- an accepted `ClassStatic` `Z2F` edge is submitted through ordinary initial-fact handling in every target;
- the complete accessor/mark/type-info structure is preserved;
- non-static bases and non-`Z2F` summaries do not fan out;
- cross-unit targets receive the fact;
- producer-before-consumer and consumer-before-producer schedules have identical results;
- a newly activated contextual entry point receives prior seeds;
- repeated summaries do not create repeated fan-out;
- loaded summaries use the same path.

Language end-to-end tests:

- Go package initialization stores a closure/interface implementation in a global and an otherwise unrelated entry point resolves and calls it;
- JVM `<clinit>` stores a lambda/implementation in a static field and an unrelated method resolves and calls it;
- producer and consumer in different packages still work.

### 13.3 JVM constructor propagation

- a private constructor initializes a receiver field with a callable/type and an instance method resolves it;
- overloaded constructors contribute a may-union of receiver facts;
- constructor delegation preserves the receiver fact;
- only methods declared by the exact same class receive it;
- static methods and `<clinit>` do not receive a `This` fact;
- constructor `Argument`, `Constant`, and static facts are respectively ignored by rule B or handled only by rule A;
- a `Z2F This` fact produced by a non-constructor method is not owner-broadcast.

### 13.4 Go negative semantics

- a `NewT` factory is not treated as a constructor solely because of its name or return type;
- the same factory works when invoked by package initialization and stored in a global, through rule A;
- receiver-local state is propagated only by ordinary calls, not owner fan-out.

### 13.5 Phase and reporting isolation

- an unreachable private prescan root can contribute dynamic-resolution/rule-selection knowledge but cannot itself produce a final reported vulnerability;
- broad prescan roots are absent from full-scan root and trace-entry sets;
- coordinator state/facts do not survive `resetApManager`;
- the feature is inactive in a direct full-scan-only/core analysis;
- cancellation waits for counted fan-out events and timeout status is reported correctly.

## 14. Acceptance criteria

The implementation is complete when:

1. JVM and Go production analyzers enumerate the scope described in section 6.
2. The full scan and vulnerability confirmation still use only the pre-existing external entry points.
3. Static/global `Z2F` facts reach all project prescan methods/functions across units through normal initial-fact handling.
4. JVM constructor `This` `Z2F` facts reach receiver-bearing methods of the exact declaration class.
5. Go package-init global callable/type information repairs the motivating dynamic-call regression without a Go constructor heuristic.
6. Propagated facts use existing `F2F` initial-fact semantics and still contribute prescan dynamic-resolution and rule-selection knowledge.
7. Order, duplicate, cycle, reset, loaded-summary, and cancellation tests pass.
8. Scope/fan-out telemetry is available for performance evaluation.

## 15. Expected implementation areas

The exact names can change during implementation, but the responsibility boundaries should remain:

- `ProjectAnalyzer`, `JirProjectAnalyzer`, `GoProjectAnalyzer`: construct external entry points and whole-project prescan roots separately.
- `TaintAnalyzer`: start the two phases with different root lists and enable/disable the phase-local coordinator.
- `TaintAnalysisUnitRunnerManager`: own the coordinator and route cross-unit seed deliveries.
- `TaintAnalysisUnitRunner`: report entry-point activation and process existing initial-fact events.
- `MethodAnalyzer`: process delivered seeds through its existing initial-fact operation.
- `SummaryEdgeStorageWithSubscribers` / `MethodSummariesUnitStorage`: expose the accepted canonical summary delta.
- JVM policy code: classify constructors and exact declaration-class receiver targets.
- Go policy code: provide no instance-constructor classification; package initialization relies on static/global propagation.

This keeps language-specific declaration semantics out of the common IFDS storage while keeping static-base propagation, event accounting, deduplication, and phase isolation common to both analyzers.
