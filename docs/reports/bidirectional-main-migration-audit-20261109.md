# Main analyzer changes relevant to the bidirectional core

9 November 2026. Status: source audit complete. Migration has not started.

The shared base is `f945f92c5`. Current remote main is `54ad708fe`.
Main has 14 commits after the base. The principal migration work is in the
rule compiler, rule binding, JVM adapter and model loader. Main also changes
the legacy analysis engine. Those changes do not replace the bidirectional
core's iteration, demand or loop algorithms.

**Major semantic changes are present.** In particular, explicit whole-object
rule positions replace implicit array and Spring expansion; sanitizer scope
changes; model transfer relations change; default getter behavior changes;
and the legacy engine gains limits and a precision-losing unfold filter.
This document identifies those changes separately from API and build changes.
It does not authorize their implementation in the new core.

Latest reached iteration: **not applicable**. This task reads source and Git
history. It does not run an analysis or make a new performance claim.

## 1. Exact comparison

| Role | Revision |
| --- | --- |
| Bidirectional branch inspected | `6a4349628c92828acc1aefa383166d4084a0203d` |
| Shared main base | `f945f92c5ae554ff4f5fc7696ee5a269210478bb` |
| Current remote main | `54ad708fe1c4f551956d3d572866de1534415fa1` |
| Local `main`, not used as the target | `ce24bbbb9` |

`git merge-base --all HEAD origin/main` returns one commit: `f945f92c5`.
That commit is an ancestor of both revisions. It is the October 1 main change
“Handle sequent instructions via summaries.” Thus, method-boundary and
method-exit normalization changes before it are already in the base.

The remote tip was checked with:

```bash
git ls-remote https://github.com/seqra/opentaint.git refs/heads/main
```

The returned SHA equals the target above. The local `main` branch is older
than the shared base and must not define this comparison. SSH access failed;
the public HTTPS check succeeded. No checkout, merge or source change was
needed.

The [audit data](data/bidirectional-main-migration-audit-20261109.json) contains
all 601 changed-file records, the 14 commits, file blob IDs at all three
revisions, current-branch status, and a detailed Java model comparison.
Use the immutable target SHA in all commands. Later movement of `main`
does not change this audit.

```bash
git log --reverse --oneline f945f92c5..54ad708fe
git diff --name-status -M f945f92c5 54ad708fe
git diff f945f92c5 54ad708fe -- core model rules
```

## 2. Complete commit inventory

The links identify the exact upstream changes. Sections 4–12 explain their
effect on the new core.

| Commit | Change | Relevance |
| --- | --- | --- |
| [5d96c047c](https://github.com/seqra/opentaint/commit/5d96c047ce176fc65e3481790fe9aecfd539a647), #340 | Add `$*` star operator | Java/Go grammar, generated rules, binding and action APIs; array and Spring behavior |
| [e07c76050](https://github.com/seqra/opentaint/commit/e07c76050dc5418dc6d7b7031e7e678d91d15c5d), #314 | Use stars in bundled rules | The new rule compiler and new rule files must move together |
| [e67576682](https://github.com/seqra/opentaint/commit/e67576682107efa677f5b82ec0a1f615be550db3), #315 | More precise Java models | Field identities and transfer relations change; OWASP reference count changes |
| [91d95b3d8](https://github.com/seqra/opentaint/commit/91d95b3d8b39c7d22de815087762a015e1228743), #322 | Any-field cleanup | Rule-position API cleanup, sanitizer focus, default getter slot, mark-unfold routing and filtering |
| [96ede134b](https://github.com/seqra/opentaint/commit/96ede134b9722aa06784d043d814a7b17e5c4dbd), #356 | Fix default getter fallback | Apply fallback only when no pass rule exists; use the same condition in trace reconstruction |
| [c624add27](https://github.com/seqra/opentaint/commit/c624add27b8743e3f82267b14d971bed46ddb2d6), #419 | Hard field limits | Shared AP interfaces, legacy scheduling, CLI/options and trace depth |
| [c86a5fbd6](https://github.com/seqra/opentaint/commit/c86a5fbd60f7bcef212c5ecde0bddecc8cb56ada), #403 | CLI analyzer version pin | Packaging only; does not change the source-run core |
| [a62c4710c](https://github.com/seqra/opentaint/commit/a62c4710cc0167f7879b188f9a2eefbef4dd684a), #377 | Isolated Java model modules | Gradle model discovery, resource aggregation and external-model API JAR |
| [197fa95c8](https://github.com/seqra/opentaint/commit/197fa95c8bcf9d8c9f70648274496e1f6862ec54), #378 | Move built-in model libraries | Independent dependency classpaths; model module build files |
| [344a9f466](https://github.com/seqra/opentaint/commit/344a9f4666995caacdebfd7c5a103cd8c14eece6), #380 | Model build/test CLI workflow | External Java model compilation, dependencies, scaffolding and tests |
| [98f319bd0](https://github.com/seqra/opentaint/commit/98f319bd0bc880f06e32d2dcb953f3348c04b43c), #387 | Go model support | Go IR/protocol and project integration; shared repository build compatibility |
| [4ab629048](https://github.com/seqra/opentaint/commit/4ab629048cbcd9723ab74a150ee83206a95eed02), #381 | New Java model addressing and Go models | Java `opentaint.` class prefix; Go default models/configuration and tests |
| [b6a3a7e70](https://github.com/seqra/opentaint/commit/b6a3a7e70f4ae23113890f167029ac7ff17f21c4), #382 | Rename CLI approximations to models | User-facing commands, options and compatibility aliases |
| [54ad708fe](https://github.com/seqra/opentaint/commit/54ad708fe1c4f551956d3d572866de1534415fa1), #384 | Rename documentation and skills | Terminology and model-authoring instructions; no new core algorithm |

## 3. Coverage and current-branch state

The 601 file changes comprise 296 under `core`, 107 under `model`, 42 under
`rules`, 35 under `cli`, and 121 in documentation, skills and CI. Renames count
as one file change. The inventory includes tests and generated documentation;
these counts are not production-source counts.

The main changes are largely absent from this branch. The six changed rule
contract files, the Java grammar, model loader, all 82 changed Java model YAML
files and all 24 changed bundled rule YAML files still have their base blobs.
Two changed Java compiler files have branch-specific edits:
`AutomataToTaintRuleConversion.kt` and `TaintRuleProcessing.kt`. Their local
edits must survive the upstream compiler migration.

Across the full inventory, 533 destination paths have their base state;
68 are branch-specific or moved. For an upstream-added path, “base state” can
mean that the path does not exist here. These are literal blob comparisons,
not proofs that behavior is equal or that an upstream change was ported.

The following sections distinguish three actions:

- **Integrate:** use the current main API, rule compiler, loader or data.
- **Adapt:** translate that contract in the JVM bidirectional adapter.
- **Keep separate:** retain a legacy-engine change for the legacy engine;
  do not infer that its algorithm belongs in the new core.

## 4. Rule syntax and position semantics

### 4.1 Explicit `$*X` whole-object rules — major semantic change

Before, Java metavariables had no star bit. Some object/array behavior was
added by runtime type checks or by Spring-specific rewrites.

Main adds `$*X` to Java and Go patterns. In Java, the AST carries the bit in
`Metavar`, `TypedMetavar`, `StarMetavarName` and `IsMetavar`. Parsing supports
expression, declaration and formal-parameter positions. Rewriters and
generated-source paths preserve the bit. Unsupported uses, such as starred
method names, remain errors; this is not a wildcard on arbitrary identifiers.

The rule compiler emits the following value/descendant operations:

```text
source at $*X:       assign at X AND assign after AnyField at X
check at $*X:        ContainsMark(X,T) OR ContainsMarkOnAnyField(X,T)
sanitizer at $*X:    emit value and descendant clean actions
```

The source's two actions are both required. A starred check is an OR, not an
ND conjunction. A rule star is **not** the AP core's correlated STAR tail.
It describes the reach of a rule position. The adapter must translate that
reach into the core's existing source/check/clean operations.

Main also makes `$X[...]` use a starred metavariable in Java conversion.
The concrete array index is not modeled by this pattern path.

Integrate the full compiler change. Adapting only the parser would leave
generated sources, state marks, sanitizers and negated patterns inconsistent.

Evidence: `JavaLexer.g4`, `JavaParser.g4`, `SemgrepJavaPatternParser.kt`,
`PatternToActionListConverter.kt`, `AutomataToTaintRuleConversion.kt`,
`TaintRuleProcessing.kt` in [#340](https://github.com/seqra/opentaint/commit/5d96c047ce176fc65e3481790fe9aecfd539a647).

### 4.2 Star-aware equality and negation

Main keeps starred and plain metavariable unification contexts separate.
The formula simplifier uses the implication `X => X*` at one position:

```text
X AND X*       = X
X AND NOT X*   = false
X* AND NOT X   can be field-only; do not remove it
```

Generated-edge elimination and metavar replacement preserve the star bit.
This prevents a positive descendant match from incorrectly removing a
plain-value exclusion. Integrate these changes with the grammar; they are
part of rule meaning, not optional compiler speed improvements.

Evidence: `UnifyMetavars.kt`, `MethodFormulaSimplifier.kt`,
`GeneratedEdgeElimination.kt`, and `StarPatternNot*Test` in #340/#322.

### 4.3 Action positions replace AnyField in ordinary positions

Main removes `PositionAccessor.AnyFieldAccessor`. A normal `Position` contains
only concrete field/element accessors. Action positions now use:

```kotlin
sealed interface ActionPosition {
    data class Exact(val position: Position) : ActionPosition
    data class AnyAccessorAfter(val position: Position) : ActionPosition
}
```

`AssignMark`, `CopyMark`, `CopyAllMarks`, `RemoveMark` and `RemoveAllMarks`
use these wrappers. `RemoveMark` and its serialized form no longer carry a
separate `reach` field. Main derives selected-clean reach from the wrapper.
`TaintCleanReach` still exists in the common evaluator; it is not deleted
from the entire repository.

Serialized `PositionModifier.AnyField` remains supported. The helper
`beforeFirstAnyField()` splits the position at its **first** AnyField. It
keeps the concrete prefix and drops modifiers after that marker. Binding then
produces `AnyAccessorAfter(prefix)` for actions, or
`ContainsMarkOnAnyField(prefix,T)` for conditions. Ordinary position binding
throws if an unresolved AnyField reaches it.

This differs from the branch's current rejection of accessors after AnyField.
It is an observable input-normalization change and must be explicit in the
migration design.

Adapt these consumers together:

- `JIRRuleForms`: action/source/pass/clean lowering and position validation.
- `JIRCallPlanBuilder`: action position lists and generated return cleaners.
- `JVMRuleSpecialization` and mark ownership/selection code: inspect the new
  wrappers without changing executable/metadata selection policy.
- String concat and Spring rule providers: wrap generated positions.
- Tests and any code that constructs `AssignMark`, `CopyAllMarks` or cleaners.

The new core currently rejects AnyField pass premises and below-only
`RemoveAllMarks`. Main's API can represent such positions. Compilation
compatibility alone does not decide whether to extend that core contract.
List these cases in the migration design instead of silently weakening the
existing validator.

Evidence: `Position.kt`, `TaintAction.kt`, `SerializedAction.kt`,
`SerializedPosition.kt`, `MethodTaintConfigurationResolver.kt`, `TaintEvaluator.kt`.

## 5. Arrays, cleaners and rule redefinition

### 5.1 Remove implicit array expansion — major semantic change

The base resolver expanded some assignments and checks for array-typed
positions. Sink evaluation could add a second reader for an array element.

Main removes `resolveArrayPosition`, the JVM array-condition reader patch,
`callArgumentMayBeArray` and its related helpers. Actions and conditions use
the positions specified by the new rule compiler. Thus:

```text
plain X:     check/assign the specified value
starred X:   explicit value plus descendant handling
```

The bidirectional adapter has its own array widening in `JIRRuleForms`, with
array callbacks from call/boundary plan construction. Updating the shared
resolver does not remove that widening. Audit it explicitly so that the new
rules do not retain the old implicit behavior through another path.

### 5.2 Sanitizer focus — major semantic change

Main changes `TaintCleanCompositionStrategy` to use `focus-metavariable`.
For an accessor sanitizer:

```java
safe = request.getRequestURI(); // sanitizer focuses on safe
sink(request.getParameter("url"));
```

The receiver is a matching constraint. The generated clean must not clean
`request` because `safe` was sanitized. A pass-through sanitizer focused on
an argument still cleans that argument in the entering call flow; Result
alone does not exist at that stage. A focus-free sanitizer retains wider
matched-position behavior. Starred clean arms use the same base as the
corresponding plain clean arm.

Integrate the compiler fix. Preserve the new core's selected-clean transfer
and protection rules when lowering the resulting actions.

### 5.3 Remove the hidden String byte clean

The base JVM clean evaluator additionally cleaned
`java.lang.String#<string-bytes>#byte[]` when it cleaned a String value.
Main removes this type-specific second action and the evaluator's
`PositionTypeResolver` dependency. Explicit rule reach now controls cleaning.

The new core independently retains `JIRRuleForms.stringBytes()` and adds a
second cleaner. A merge of the shared evaluator cannot remove that behavior.
This is a required adapter review point with a semantic effect, not just a
constructor-signature update.

### 5.4 Rule redefinition and alias-model extraction

Main's `JIRMethodCallRuleBasedSummaryRewriter` stores `Set<ActionPosition>`
and makes reset cleaners with the same wrapper. Do not strip the wrapper
while rebuilding the new core's return rewriter: that loses clean reach.

`JIRLocalAliasAnalysis` also uses the wrapper. Exact positions can map to
`ExternalObject`; `AnyAccessorAfter` cannot. Main deliberately does not turn
a whole-object taint operation into a concrete alias assignment. The alias
engine itself is not rewritten in this range. Its updated regression uses
the new action type.

Evidence: `AccessorSanitizerScopeTest`, `TaintCleanCompositionStrategy.kt`,
`TaintEvaluator.kt`, `JIRMethodCallRuleBasedSummaryRewriter.kt`,
`JIRLocalAliasAnalysis.kt` in #322.

## 6. Spring integration

Main removes two provider rewrites:

1. Controller entry sources no longer receive an extra AnyField assignment
   based on the Java argument type. Starred source rules express that reach.
   The old Kotlin `Continuation` exclusion moves into the source rule regex.
2. Controller exit checks are no longer rewritten from plain ContainsMark to
   ContainsMarkOnAnyField. Starred return rules express that reach.

Controller exit rules still run on controllers. Main keeps the
`initialFacts = null` bypass when asking the base exit provider for these
rules. Its comment identifies stored/second-order flows, for example a POST
writing repository data and a GET returning it. Removing the widening helper
must not remove that bypass. Main also explicitly skips generated Spring
methods in the exit sink provider.

Repository SAVE/FIND/Optional/Iterable transfers retain their structure but
use `ActionPosition.Exact` wrappers. Cleanup actions also use wrappers.

The branch's `SpringRuleProvider` additionally implements bidirectional rule
views, selection and action-specialization metadata. Its cleanup uses the
branch's complete predefined-summary mechanism. Preserve those branch-owned
features; do not replace the file wholesale with main's simpler provider.

Evidence: `SpringRuleProvider.kt`, `rules/ruleset/java/lib/spring/` in #340/#314.

## 7. Bundled Java rules and model configuration

### 7.1 Rules must move with the compiler

Main changes 24 bundled rule YAML files: 20 Java and 4 Go. The Java changes
cover generic code/command/log/path/response/SMTP/SSRF/redirect/XSS sinks,
servlet and Spring sources, JDBC sinks, CRLF, crypto, configuration control
and insecure-design rules. The audit data lists every path.

These are not all mechanical star insertions. Principal changes include:

- Servlet/Spring whole-object inputs and selected returned values become
  starred; uploaded-file collections are tainted at the parsed result.
- Spring XSS/response/redirect and generic sinks/cleaners explicitly select
  value or descendant reach. XSS gains an object-to-string propagator and
  additional safe content types.
- Trust-boundary sources bind typed request call results, exclude
  `getSession`, and star the result. Separate focused sinks check attribute
  names and values in `setAttribute`/`putValue`.
- Test sources, expectations and the rules manifest change with the rules.

A findings comparison against the old branch can therefore change because
the input rules changed, even if the core transfer is preserved. Record the
rule revision separately from the core revision.

### 7.2 Java model field identities — major semantic change

Main changes 82 Java configuration YAML files. It replaces generic
`<rule-storage>` carrier slots with named slots. Examples:

```text
CharSequence.<rule-storage>  -> CharSequence.content
Collection.<rule-storage>    -> Collection.elements
File.<rule-storage>          -> File.path
```

Some owners split one old carrier into distinct properties. Examples include
QName components, cookie path/domain, naming objects and formatter state.
The exact owner, name and field type are part of the AP key. This is a change
in modeled flow and precision, not a cosmetic field rename.

Main's `TaintAnalyzer.unrollStrategy` also stops excluding the literal field
name `<rule-storage>`. Every `FieldAccessor` becomes eligible there. The
bidirectional abstraction has its own policy; do not copy a legacy unfold
switch into it without checking that policy.

### 7.3 Additional model transfer corrections

The audit data includes a comparison that applies only unambiguous carrier
renames and then retains every remaining changed rule object. Nineteen files
still differ under that comparison. Two ambiguous rename families are left
visible rather than guessed. This is a review aid; raw blob IDs remain the
authority.

| Model family | Principal change beyond a uniform carrier rename |
| --- | --- |
| Jackson 2.20.1 | `ObjectMapper.readValue` and `ObjectBuffer.completeAndClearBuffer` transfers |
| JSF | SelectItem value and SelectItemGroup item-array transfers |
| JSON-P | JsonArrayBuilder add overload rules are consolidated/changed |
| Servlet | Cookie path and domain use separate state |
| SnakeYAML | Add `Yaml.dump` flow |
| IO | Reader output flows to the supplied character array, including elements; File constructors and StringWriter transfer change |
| Java lang | Object.toString, String.format and String.join transfer changes |
| URI/NIO file | URI constructor and FileSystem.getPath transfers change |
| NIO buffers | Add Buffer.flip and typed-buffer toString transfers |
| Security | CodeSource certificate and signer state/transfers are separated |
| Text | Replace broad formatter getters/setters with named-property rules; add specific DecimalFormat, DateFormatSymbols and DecimalFormatSymbols coverage |
| Collections | Add Properties.store flow through writer content |
| Naming/directory | Separate name, class-name, bound-object and attributes; change SearchResult and Reference transfers |
| LDAP | Separate control IDs/encoded values, RDN components and SortKey properties; resolve each exact field key from the data |
| Script | ScriptContext attribute/bindings state changes; exact rename mapping is not uniform |
| RowSet | CachedRowSet table name and JoinRowSet rowset transfers |
| XML namespace | QName namespace/local-part/prefix are distinct rather than one broad carrier |

These changes affect both forward and backward runs because the new core
builds its reversible plans from model rules. Field paths also affect field
limits, C2 admission, C5 budgets, relation subsumption and loop growth tests.
Reuse the designed core mechanisms; test the new model inputs against them.

## 8. Default getter behavior

There are two separate changes.

First, main's default getter reads a synthetic field on the declaring class:

```text
base: this.* -> result.*
main: this.<get-default>.* -> result.*
      plus result.[*] transfer for array/Object return types
```

The model still requires a nonstatic `get...` method and an enabled class.
The synthetic field can add a concrete AP field compared with the old model.

Second, #356 permits fallback only when the explicit pass-rule list is empty.
It does not use “no pass result for this offered fact” as the test. In the
intermediate main version, the test was `passThroughFacts.isNone`; #356 fixes
that and makes trace reconstruction use the same empty-rule condition.

The branch's `JIRCallPlanBuilder.passRules()` currently appends default getter
rules to explicit rules. Thus, merging only `JIRMethodGetDefault` would still
miss the fallback-policy correction. Adapt plan construction and test an
explicit rule that produces no output for one input: that input must not
silently activate the fallback.

Evidence: `JIRMethodGetDefault.kt`, `JIRMethodCallFlowFunction.kt`,
`JIRMethodCallPrecondition.kt` in #322/#356.

## 9. Legacy mark unfolding and source conditions

### 9.1 Changed legacy request pipeline

Main adds `MarkUnfoldDemand` to each JVM/Go `MethodAnalysisContext` and gives
`TaintMarkFieldUnfoldRequest` a suffix. The side-effect handler can handle an
answer at a FactToFact stage, retain/propagate an unanswered request, and
carry the selected suffix while climbing callers. Handling is no longer
limited to a ZeroToFact answer.

The per-method filter records contributed accessors under:

```text
(asking MethodEntryPoint, request base, requested mark) -> accessor set
```

It suppresses repeated refinement contributions. It does **not** key the
question by the complete refined field path. An empty fresh-accessor result
does not consume the request; the request can continue to a caller.

**This filter changes precision.** The source comment explicitly says that
`arg0.*` and `arg0.x.*` are conflated and that a flow needing `arg0.x.y` can be
lost. It cuts a repeated-unfold pattern such as erased container fields or
`CharSequence.content`. Do not describe it as a purely technical cache.

The bidirectional core has its own request/demand mechanism. Keep this
legacy handler and its new API wiring for the legacy lane. No evidence in
this audit requires adding the filter to the bidirectional lane.

### 9.2 Conditional sources now request hidden marks

Main passes `markAfterAnyFieldResolver` to source-rule evaluation. The old
common call path explicitly passed null on the assumption that sources did
not need marks hidden after AnyAccessor. Main removes that assumption.

`TaintFactAwareConditionEvaluator` also caches any-field mark evaluations per
position/mark, like its ordinary mark cache. It records the evaluated facts
on a hit and invokes the resolver on a miss.

Reuse the **requirement** that mark-dependent source conditions can request
refinement. Verify it in the new core's existing predicate/request path.
Do not route its rules through the old side-effect request machinery.

Evidence: `MarkUnfoldDemand.kt`,
`MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt`, `TaintUtil.kt`,
`TaintFactAwareConditionEvaluator.kt` and `MarkUnfoldDemandTest` in #322.

## 10. Legacy field limits and trace reconstruction

### 10.1 New shared interfaces

Main adds:

```kotlin
FactAp.exceedsFieldLimit(limit: Int): Boolean
FinalFactAp.splitFieldLimit(limit: Int): FieldLimitSplit
// FieldLimitSplit(within, rest)
```

Field-depth counting includes `FieldAccessor`, `ElementAccessor` and
`AnyAccessor`; it excludes marks, class markers, value and type accessors.
Tree paths/nodes cache field counts. AccessTree can split a mixed packet
into within-limit and over-limit paths. Graph/cactus final facts currently
fall back to accepting or delaying the complete packet; they do not have a
precise path split.

### 10.2 Changed legacy scheduler — keep separate

The base delayed selected FactToFact initials/summaries using total AP depth
and a larger output allowance. Main starts legacy deepening at field depth 1
instead of 3. It checks initials, sequential edges and summaries for ZeroToFact,
FactToFact and ND cases. Over-limit conclusion parts are delayed; over-limit
premises delay the edge. A configured hard cap drops the remaining parts
instead of delaying them forever.

The new option is `--iteration-limit`, wired through `CommonAnalysisOptions`,
`TaintAnalyzerOptions`, the runner manager and analyzer storage. It accepts 0
and is unlimited by default. This is **not** the new core's run count or its
`1,1,2,3,...` field-limit schedule. Do not map these meanings by name alone.
Decide and document what the legacy option means when the new core is selected.

The new core has demand-relative restriction and its own AP field counting.
Keep these policies. The shared legacy API additions are a build/integration
requirement, not a reason to replace C2/C5 with `splitFieldLimit`.

### 10.3 Trace search — observable search-policy change

`MethodTraceResolver` receives the analyzer's current depth. It delays deep
predecessors, increases the depth when needed, and drops delayed work after
a start is found. Reconstruction of a specific start waits for that required
start, rather than accepting the first different start. This changes search
work and can change which trace alternatives are returned.

The bidirectional lane uses its own report/Target trace path, including
`JIRBidiAnalysis`. Check each actual consumer before transferring this legacy
search policy. Source and sink locations and required report identities remain
the migration validation target; exact incidental path order is separate.

Evidence: #419, `MethodAnalyzer.kt`, `FactAp.kt`, `AccessTree.kt`,
`AccessGraphFinalFactAp.kt`, `AccessCactus.kt`, `MethodTraceResolver.kt`,
`FieldLimitTest`, `IterationLimitAnalysisTest`.

## 11. Java code models, IR and packaging

### 11.1 Independent modules

Before, `model/java/dataflow` was one module with one compilation classpath.
Main discovers child directories with `build.gradle.kts`. The current modules
are `core`, `stdlib` and `kotlin`, each built with its own dependencies.
The support module supplies `OpentaintNdUtil` and `ArgumentTypeContext`.
The convention plugin keeps Java 8 model bytecode compatibility.

Resources from all modules still go to `opentaint-dataflow-approximations/`.
Duplicate class paths fail the build. An empty discovered module set also
fails rather than shipping an analyzer without built-in models.

An additional `opentaint-approximations-api.jar` resource contains annotations
and support types for external model compilation. The internal module,
package and resource names still use “approximations” in places. The user-facing
rename to “models” does not rename all these ABI/resource identifiers.

Integrate settings, convention plugin, module source moves and resource
assembly together. Verify runtime model resources, not only Kotlin compilation.

### 11.2 Prefix-addressed Java models

Main's IR approximation loader recognizes, for example:

```text
opentaint.java.util.Optional -> java.util.Optional
```

It retains annotation-addressed models. Explicit mappings take precedence
over prefix-derived mappings. Annotation values are read by name, and the
indexer validates conflicting addresses. Built-in stdlib and Kotlin model
classes move to the prefix-addressed packages. Tests cover legacy annotations,
Java classes and Kotlin naming cases.

There is no new bidirectional flow algorithm here. The core must see the
modeled CFG through the normal IR/call resolver. Do not add another model
substitution layer inside the method analyzer.

### 11.3 Preserve the existing model bodies

The support sources are byte-exact moves. Other Java model files change their
package, imports, class names or addressing annotations. Their existing
callback bodies remain. In particular, `runBlocking$default`, Thread's Runnable
paths and executor/stream/future callbacks are already in the base; they are
not new algorithms in this range. Verify that the new loader still exposes
these bodies to prescan after the package/address changes.

Evidence: #377/#378/#381, `ApproximationModules.kt`,
`dataflow-approximation-module.gradle.kts`, `Approximations.kt`,
`model/java/dataflow/{core,stdlib,kotlin}` and `ApproximationsTest`.

## 12. Go, CLI and validation changes

### 12.1 Go compatibility; no new Go bidirectional core

The new core remains JVM-only. A repository migration must still compile and
preserve the existing Go lane because configuration and analysis interfaces
are shared. Main changes the following:

- Go star parsing/emission and action-position wrappers follow the explicit
  position contract. Separate serialized any-accessor assign/check types are
  removed. Named element/field positions remain.
- Go pass action resolution includes an element source for applicable
  variadic argument indexes. Call signatures now carry those indexes.
  The old sink-side slice-element reader patch is removed.
- Go positions gain ClassStatic resolution for generated/global rule state.
- Go contexts implement the new legacy unfold-demand API.
- The IR protocol carries model directories and model programs, plus generic
  origin/type-argument data. Kotlin installs model lookup/transformers before
  package lookup and specializes model bodies for generic calls/closures.
- Go model methods can form package analysis units even when the original
  target package is not project code. Default and external model paths are
  passed by ordinary and rule-test analyzers.
- Built-in MCP and GitHub MCP model modules/configuration add callback flows.
  The runner adds `--go-models` and `--disable-default-go-models`.

Keep the Go client, generated protocol, server, model loader and project
options compatible. This does not require translating the JVM bidirectional
algorithm to Go. The Go server's required Go version was already 1.26.0 in
the shared base; this range does not introduce that requirement.

### 12.2 CLI and model authoring

The CLI gains source compilation/test/scaffolding for external model projects,
dependency handling and related tests. Later commits rename user-facing
approximation commands/options to models and retain deprecated forms where
implemented. The bundled analyzer pin changes to
`analyzer/2026.10.26.c624add`; the autobuilder pin does not change in this range.

These changes do not select or alter the bidirectional engine. Local validation
must continue to run Gradle tasks with an explicit bidirectional selection.
Do not validate a source migration by running the CLI's pinned older analyzer.

### 12.3 Test/reference changes

Main changes the OWASP workflow reference from **4112 to 2633 traces** with
the model-precision commit. This is an upstream expectation change, not proof
that the new core should produce exactly that count. Preserve per-location
quality comparison and record the rules/models used.

Principal upstream regression families to carry into migration validation:

| Contract | Upstream tests or fixtures |
| --- | --- |
| Star syntax, generated actions and source LHS | `StarOperatorParseTest`, `StarOperatorRuleGenTest`, `StarOperatorTest`, serialized round-trip tests |
| Negated/field-only star checks | `StarPatternNotCoincidenceTest`, `StarPatternNotFieldOnlyTest` |
| Sanitizer receiver/focus scope | `AccessorSanitizerScopeTest` |
| Array/plain-value separation and calls | `AnyFieldInterproceduralAnalysisTest`, `AnyFieldPrimitiveAnalysisTest`, `AnyFieldInterproceduralSample` |
| Named model fields and positive/negative flows | `Phase3BeanIsolationTest`, `Phase3ConfigCoverageTest`, `Phase3RuleStorageFixesTest`, `Phase3StarSourceGetterTest` and related Phase3 suites |
| Legacy field cap and AP splitting | `FieldLimitTest`, `IterationLimitAnalysisTest`, `IterationLimitSample` |
| Legacy repeated unfold | `MarkUnfoldDemandTest` |
| Alias extraction API | `DSUAliasAnalysisInvalidateOuterHeapAliasesTest` |
| Model loading/addressing | `ApproximationsTest`; Go `ModelTests`, `McpModelTest`, unit-resolver and workspace tests |
| End-to-end rules | Updated `rules/test/rule-test.yaml` and rule samples |

Several upstream tests use the legacy test runner. Their presence does not
prove that the bidirectional lane executes them. The
[runner validation report](bidirectional-rule-runner-validation-20261109.md)
records the current engine-selection checks and two convergence failures.
That report also records existing root-test compilation failures. Those are
separate from this source audit; no test success is claimed here.

## 13. Migration boundaries and removal review

| Area | Use from main | Preserve/adapt from this branch | Redundant old behavior to review for removal |
| --- | --- | --- | --- |
| Rule compiler | Star-aware parse, unification, generation and focus handling | Executable rule reduction, stable generated-rule/action identities and metadata selection | Old scalar-only metavar assumptions |
| Rule binding | ActionPosition and first-AnyField normalization | Bidirectional rule views and per-method specialization | PositionAccessor.AnyFieldAccessor, old array expansion and serialized cleaner reach |
| JVM rule forms | New wrapper access and explicit rule reach | Existing source/pass/clean micro-edges, protection, FULL/GROUP policy and unsupported-rule diagnostics | Independent implicit array widening and hidden String-byte cleaning, once the replacement contract is tested |
| Spring | Explicit-star rules, controller exit bypass, generated-method exclusion | Controller annotations, selection metadata, complete predefined cleanup summaries | `taintObjectFields`, `unfoldSpringExitObject`, their private rewriters/type helpers |
| Default get | Named slot and empty-explicit-rule fallback | Existing reversible call-plan stages | Unconditional append of fallback pass rules |
| Aliases | Wrapper-aware external assignments | Existing call/field alias processing and designed identity policy | Ordinary-position AnyField alias case |
| Models/build | Current YAML, independent Java modules and prefix loader | Normal IR/prescan/call entry into model bodies | Single model-module build and old moved source paths |
| Shared legacy APIs | New AP depth methods and context/handler signatures | Bidi AP managers, demand-relative C2/C5 and loop algorithm | Only stale call sites; the legacy engine itself remains supported |
| Requests | Legacy handler for legacy engine | Existing new-core requests and static pools | No new-core replacement is implied by MarkUnfoldDemand |
| CLI/Go | Current compatible workflow/protocol and existing Go engine | Explicit Java bidirectional selection and current rule runner | Stale external-model documentation/paths where renamed upstream |

The current default FULL mode, known GROUP limitations, no-ANY-premise policy,
FLOW companion emission, literal protected/unprotected memberships, transitive
subsumption, Targets, demand-only handoff, loop-boundary ownership/liveness and
predefined-summary completeness are branch-owned contracts. None of the 14
commits implements a replacement for these mechanisms.

In particular, do not import any of the following as an incidental merge fix:

- The legacy precision-losing unfold filter into new-core request processing.
- The legacy hard-drop field cap or its limit-zero meaning into C2/C5.
- Legacy implicit array behavior alongside the explicit starred rules.
- A normal-only controller exit restriction that removes stored flows.
- Main's simpler rule/provider objects at the cost of branch selection,
  action identities or predefined summaries.

## 14. Work order and verification for the later migration

1. Pin these revisions and retain the current native/example results. Resolve
   shared API compilation together with JVM/Go action-wrapper consumers.
2. Integrate the complete star-aware compiler, binding and matching rules.
   Reconcile branch edits in the two compiler files. Validate generated
   positions before changing core lowering.
3. Adapt JVM forms, return rewriters, aliases and providers. Test explicit
   array reach, selected-clean scope, String cleanup, Spring controller exits
   and default-get suppression. Mark every accepted semantic change in the
   implementation proposal.
4. Integrate Java model data, module packaging and prefix loading as a
   separately attributable change. Verify model CFG/callback visibility and
   inspect generated runtime resources. Keep Go/protocol compatibility green.
5. Run native new-core examples, the actual bidirectional Java rules suite,
   and the selected project validation through Gradle. Compare findings,
   locations, timeout/OOM status and latest reached/completed iteration.
   Report compiler/rule/model changes separately from algorithm regressions.

This audit is complete for the pinned range. It does not prove that these
changes are compatible with the new core. The remaining design decisions
are the explicit-rule contract for currently rejected action shapes and the
meaning of the new legacy `iterationLimit` option in bidirectional mode.
Those decisions belong in the migration specification before implementation.
