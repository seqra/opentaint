# Bidirectional core after the main rebase

9 November 2026. Status: proposed post-rebase contract. No rebase or analyzer
implementation is part of this specification task. Use ASD-STE100 Simplified
Technical English.

The pipeline is:

```text
current bidirectional branch
    -> rebase onto the pinned actual main
    -> apply this specification to the bidirectional adapter
    -> validate the resulting analyzer
```

Latest reached iteration: not applicable to this source/specification task.
The examples below describe local run behavior; they are not project results.

## 1. Versions, authority and semantic scope

| Role | Exact revision or document |
| --- | --- |
| Branch before migration | `14b8ac8354bfc824080e790c7d71f6cfae0f401a` |
| Shared old-main base | `f945f92c5ae554ff4f5fc7696ee5a269210478bb` |
| Rebase target | `54ad708fe1c4f551956d3d572866de1534415fa1` |
| Source comparison | [Main migration audit](../docs/reports/bidirectional-main-migration-audit-20261109.md) |
| Existing core contract | [Subsumption, initial emission and demand intersection](edge-subsumption-initial-emission-demand-intersection.md), including its selected gap resolutions |
| Method/rule execution | [Interpreter](interpreter.md), with the existing later selected overrides |
| Proof authority | [Proof guide](proof-guide.md) and [migration proof map](main-migration-proofs.md) |

The branch's `core` tree at `14b8ac835` equals that at the audit's inspected
`6a4349628` revision. The target was checked against remote main on 9 November.
If the target moves, audit the additional commits before applying this spec.

This spec overrides existing documents only at the rule/compiler, provider,
adapter and option seams listed below. It does not redefine the AP algebra.
The rebase must retain main's source changes and the branch's core changes.
A conflict resolution that compiles but loses either contract is invalid.

### 1.1 Selected changes

| ID | Kind | Before migration | Required result |
| --- | --- | --- | --- |
| M1 | Major semantic change | Some array/object reach is implicit | Rule positions alone select value or whole-object reach; no automatic array or Spring widening |
| M2 | API plus input-normalization change | AnyField can be an ordinary position accessor; malformed trailing accessors reject | Use main's ActionPosition wrappers and first-AnyField normalization |
| M3 | Major semantic change | Accessor sanitizers can clean a nonfocused receiver; String cleaning has an implicit byte-field step | Use main's focused sanitizer generation and explicit clean positions; remove the implicit String-byte step |
| M4 | Major semantic change | Spring provider widens entry/exit rules | Starred rules supply reach; retain controller exit applicability and branch-owned cleanup summaries |
| M5 | Major semantic change | Default getter rules are appended to explicit pass rules | Read main's named `<get-default>` field; add fallback only if the prepared explicit pass-rule list is empty |
| M6 | Imported semantic inputs | Old bundled rules, model field names and model addressing | Use main's rules/models/IR loader and model packaging through existing core entry points |
| M7 | API adaptation | Actions and helper constructors use ordinary Position and an explicit selected-clean reach | Lower the new wrappers to existing core operations; retain core-generated reset scope and identities |
| M8 | Explicit option policy | No upstream `iterationLimit` option | In bidirectional mode ignore an explicitly supplied value and emit one diagnostic; preserve the current schedule |

M1–M6 can change findings. They are not technical optimizations or a claim
of equivalence to old rule/model inputs. M2 changes acceptance of serialized
positions after the first AnyField, as specified in section 3.

The user selected these restrictions for this migration:

- Keep rejection of an AnyField pass input and below-only RemoveAllMarks.
- Ignore `--iteration-limit` with a diagnostic in bidirectional mode.

### 1.2 Mechanisms which must remain unchanged

Keep the four AP tails, counted-field rules, FULL default and alternating
field schedule `1,1,2,3,...`. Keep current GROUP mode and its known issues;
this migration does not make GROUP an acceptance substitute for FULL.

Keep C2 initial emission, paired C5 restriction, FLOW companion emission,
no-ANY-owned-premise invariant, summary normalization, same-flag subsumption,
separate protected/plain memberships, and opposite-direction inside policy.
A pass never creates protection. Keep selected partial-cleaner survivor
handling, field overwrite handling and the existing exclusions/layers.

Keep complete ND condition evaluation and the existing run-1 contributor
policy. A rule-position star does not turn AND into OR. Keep rule selection,
executable mark reduction, metadata reset selection and stable action ordinals.

Keep static pools, writer registration at micro-edges, static summary policy,
run-1-to-run-2 demand lookup, Targets, report identities, source permissions,
loop decomposition/restriction, own-ZERO loop bypass, boundary liveness,
ordinary calls, persisted-summary-first replay and the stopping rule.

Keep complete predefined summaries and their analyzer/boundary-rule bypass.
Keep alias transfer, enum alias filtering and type filtering, except for the
wrapper extraction and removed array helper described here.
`trackFactsReachAnalysisEnd` remains empty in the new core.

Do not introduce GroundingSupport, per-input writer grounding, a new tail,
a legacy mark-unfold filter or a discarded-fact archive.

## 2. Responsibility after the rebase

Main supplies the grammar, star-aware rule compiler, serialized rules,
MethodTaintConfigurationResolver, ActionPosition API, model YAML, model
modules, model addressing, shared legacy API changes and Go support.
Do not implement a second copy of those features inside the new core.

The post-rebase work changes the JVM bidirectional adapter and branch-owned
provider integration. It also resolves shared constructor/API conflicts.
The legacy engine and Go retain main's implementations. There is no Go
bidirectional-core migration in this spec.

```text
main rule compiler / model loader
    -> existing provider selection and executable mark reduction
    -> main method binding, with stable branch rule/action labels
    -> canonical rule descriptors
    -> existing core primitives and reversible method forms
    -> unchanged analysis, storage, demand and reporting pipeline
```

Perform validation of the complete bound rule before publishing a form.
A rejected rule contributes no partial actions or static operations. Retain
the existing diagnostics and frozen occurrence-order policy.

## 3. Canonical rule positions

An ordinary Position contains a base and concrete field/element accessors.
It contains no AnyField. The rule adapter uses this temporary descriptor:

```text
RulePosition = (base, concretePath, anyAfter)

describe(ActionPosition.Exact(p))            = (base(p), path(p), false)
describe(ActionPosition.AnyAccessorAfter(p)) = (base(p), path(p), true)
describe(ContainsMark(p,T))                  = (base(p), path(p), false)
describe(ContainsMarkOnAnyField(p,T))         = (base(p), path(p), true)
```

`anyAfter` is compiler/adapter reach. It is not an AP tail or a stored fact
flag. Do not attach it to a MethodEdgeStore key, demand row or report.
`ActionPosition.Exact` also does not mean “emit AP EXACT for every action”:
source, pass and clean have different operations below.

Use main's `beforeFirstAnyField()` while binding serialized positions:

| Serialized position | Canonical descriptor |
| --- | --- |
| `p` | `(p, [], false)` |
| `p.f` | `(p, [f], false)` |
| `p.[*]` | `(p, [element], false)` |
| `p.f.AnyField` | `(p, [f], true)` |
| `p.f.AnyField.g` | `(p, [f], true)` |
| `p.AnyField.AnyField` | `(p, [], true)` |

The last two rows deliberately use main's first-marker rule. Do not rebuild
the discarded suffix, count AnyField as a concrete field, or reject it again
in a second ordinary-position parser. Concrete paths before the marker and
their base/type information remain unchanged.

Retain static grammar and class validation. In particular, AnyField class
source targets, class pass endpoints and invalid static anchors still reject
under the existing core rules. A condition pattern with ANY is permitted;
it is not an emitted analyzer initial or an owned ANY premise.

## 4. Conditions and explicit reach

Compile each bound source/sink condition with the existing predicate builder.
Preserve the signed normalization and existing negative-literal approximation
order. Use the provider's explicit exact/any-field atoms. Remove the array
callback and array-element alternatives from `JIRRulePredicates` and all its
callers. Do not infer rule reach from a parameter or return type.

Main's compiler supplies the meaning of `$*X`:

```text
plain check:    CM(X,T)
starred check:  CM(X,T) OR CMAny(X,T)
conjunction:    CM(X,T) AND CM(Y,U) keeps both required inputs
```

Use the existing normal predicate representation; do not expand DNF cubes.
Any-field source conditions must use the same existing mark-request path as
any-field sink conditions. Do not call the legacy side-effect unfold handler.

Main's star-aware unifier/simplifier must survive the rebase. At the same
position, plain X implies starred X. Thus `X AND X*` reduces to X;
`X AND NOT X*` is false; `X* AND NOT X` can describe a field-only case.
These compiler identities precede the core's existing approximation policy.

## 5. Actions and generated reset operations

Use the following lowering table. Each operation then uses the existing
mark mode, type checks, field limit, layer, request and protection policy.

| Bound action | Core operation |
| --- | --- |
| AssignMark(T, Exact(p)) | Existing exact source target `p.$/T` |
| AssignMark(T, AnyAccessorAfter(p)) | Existing uniform source target `p.MUST/T` |
| CopyAllMarks(Exact(p), Exact(q)) | Existing correlated FLOW `p.* -> q.*` |
| CopyAllMarks(Exact(p), AnyAccessorAfter(q)) | Existing MAY pass output `p.* -> q.ANY` |
| CopyMark(T, Exact(p), Exact(q)) | Existing selected-mark pass operation |
| CopyMark(T, Exact(p), AnyAccessorAfter(q)) | Existing selected-mark pass operation with MAY output |
| Copy with AnyAccessorAfter input | Reject the whole rule, as before |
| RemoveMark(T, Exact(p)) | Existing selected exact clean at p |
| RemoveMark(T, AnyAccessorAfter(p)) | Existing selected below-p clean |
| RemoveAllMarks(Exact(p)) | Existing whole-position kill at and below p |
| RemoveAllMarks(AnyAccessorAfter(p)) | Reject the whole rule, as before |

A uniform source and a MAY pass are different even when they have the same
prefix. The backward form uses the existing source/pass distinction and
MUST-to-MAY rules. Do not emit MUST backward, use MAY as an initial, or make
a static source NORMAL merely because its action is Exact.

A starred Semgrep propagator is not automatically an AnyField pass input.
Validate the actual bound action/condition after main's rule compilation;
mark-dependent generated source rules use their existing source path.

For `$*X`, the compiler supplies both source actions. Preserve their ordered
occurrence/action identities. Existing fact canonicalization may remove
redundant output memberships; the compiler must not renumber surviving
actions by their packed output.

### 5.1 Cleaner scope

Use main's focus-aware sanitizer generation. Without by-side-effect behavior,
an accessor sanitizer focused on its returned value must not clean its
receiver. A sanitizer focused on a passed argument retains its entering-call
argument clean. A focus-free sanitizer keeps main's matched-position policy.
Explicit by-side-effect actions remain explicit actions; do not erase them
because another variable is focused.

Remove the hidden String `<string-bytes>` clean from `JIRRuleForms`. Cleaning
an exact String position cleans the specified value. Descendants are cleaned
only by the explicit below/whole-position operation. Retain ordinary field
cleaner lowering, its typed temporary, selected survivor protection and
run-1 DEMAND behavior. Do not replace these with main's legacy clean engine.

### 5.2 Source-definition resets are not selected cleaners

Preserve the branch's existing return rewriter. Its generated reset is part
of user-rule redefinition; it is not the configured selected cleaner action.

```text
source-definition target Exact(p):       existing exact reset
source-definition target AnyAfter(p):    existing at-and-below reset
cleaner-definition position Exact(p):    existing exact reset
cleaner-definition position AnyAfter(p): existing below reset
```

Lower these generated resets directly with the existing core clean reach.
Do not encode the at-and-below reset as one RemoveMark(AnyAfter(p)): that
would retain p itself. Do not restore a removed public `reach` field or
change the meaning of ordinary AnyAfter cleaners to repair this case.
No new core primitive or support label is required.

Keep `ActionRole.RETURN_REWRITER`, original reset-mark ordinals and metadata
selection. Delete only the String-byte substep; do not renumber other actions
or remove metadata guards. A false executable rule is not permission to
rewrite metadata conditions using the executable mark set.

## 6. Selection, identity, caches and aliases

Keep executable-only mark reduction, its fixed point, and separate metadata
action reduction. Do not enumerate specialized rules to build a new mark
table. Preserve `SpecializedRules`, original conditions, original action
ordinals, top-level group ownership and source/sink identities when rebasing
the compiler/provider files.

For one bound input rule list, conversion to wrappers must preserve order,
duplicates, selected action ordinals and semantic payloads. A rebuild of one
form owner must produce the same logical forms. New main rule/compiler input
can legitimately change those lists; cross-revision ordinal equality is not
required.

Review equality/hashCode in every changed data class. Include meaningful
Exact/AnyAfter distinctions. Do not add cache handles, managed-reference
identity or transient compiler statistics to logical fact/edge/report keys.
Keep protected and plain memberships independent and delivered independently.
A pass preserves the incoming flag and never creates a protected result.

Model alias extraction follows main: Exact positions can form concrete alias
assignments; AnyAfter positions cannot. Keep the existing alias engine,
input alias closure, enum filtering and summary application policy.

Reuse the existing FormOwner generation and cache lifecycle. New rule/model
configuration requires new forms. Do not reuse in-memory or serialized
analysis records across the old/new configuration as if the field/rule keys
were compatible. This does not change persistence across ordinary iterations
of one migrated analysis.

## 7. Spring and default getters

### 7.1 Spring

Remove `taintObjectFields`, `unfoldSpringExitObject` and their private
ContainsMark/type helpers. Main's starred source/exit rules supply reach.
Use main's source regex for Continuation exclusion; do not keep a second
type-driven expansion/exclusion in the provider.

Retain controller annotation checks and the `initialFacts = null` bypass
when asking the base provider for controller exit sinks. A NORMAL conditional
F2F controller summary can still trigger a controller exit rule. Do not impose
a ZERO-only witness requirement or move the rule to a generated dispatcher.
Skip generated Spring method boundary rules as main does. The existing
complete predefined-summary bypass also remains in force.

Wrap repository SAVE/FIND/Iterable/Optional action positions. Keep their
existing direction, virtual field keys and transfers. Preserve the branch's
predefined registry-cleanup summary; do not restore the old cleanup cleaner
or generated static save/restore assignments from a rebase conflict.

### 7.2 Default getter selection

Use main's `JIRMethodGetDefault` rule body. It reads the declaring class's
`<get-default>` field and retains its existing scalar/array result actions.
Do not substitute a receiver-root identity for that named input.

The fallback decision is made once while building the call plan:

```text
explicit = query executable pass rules for the call's named method
prepared = rewrite call conditions and remove statically false rows

if prepared is empty:
    selected = defaultGetModel.defaultPropagationRules(method)
else:
    selected = prepared

validate and lower selected using the existing pass stage
```

Use the existing fact-independent method-form query. “Empty” means no
prepared explicit rule. It does not mean no output for the currently offered
fact, no relevant output base, or no successfully validated rule. A present
unsupported rule still receives its normal rejection diagnostic; it must
not silently enable fallback. Static-false rows do not block fallback.

Keep the existing default-get enable/disable and method eligibility checks.
Use this same frozen plan for forward interpretation, backward forms and
trace reconstruction. Do not apply one fallback policy during analysis and
another during reporting.

## 8. Main inputs and legacy boundaries

Use main's bundled rules and model configuration as one compatible input set.
Named virtual fields remain ordinary field identities, with their owner and
type. Do not translate `content`, `elements`, `path`, property-specific fields
or `<get-default>` back to `<rule-storage>`. Do not add a blanket identity to
compensate for more precise models.

Keep main's isolated Java model modules, duplicate/empty-module build checks,
API resource and prefix-addressed model loader. Model bodies enter the new
core through the existing IR/call resolver. Analyze the modeled CFG; do not
also apply a second adapter-generated substitute for the same body.
New model classes and callbacks must be visible during prescan before forms
and call targets are frozen.

Shared `FactAp` depth/split APIs and MethodAnalysisContext additions remain
available for main's legacy JVM/Go engine. Satisfy their shared signatures.
Do not apply their legacy deferred-edge scheduler, hard-drop cap,
MarkUnfoldDemand or legacy trace-search policy to the new core.

In bidirectional mode:

```text
if options.iterationLimit is specified:
    emit one configuration diagnostic:
      "--iteration-limit is ignored by the bidirectional engine;
       the bidirectional field-limit schedule is used"

use the existing configured bidirectional schedule
```

Emit once per analyzer invocation, not once per method or run. Values 0, 1
and larger values have the same lack of effect on that schedule. In legacy
mode the option retains main's behavior. Existing separate bidirectional
schedule controls retain their meaning.

Keep main's Go client/server/protocol and model support compatible. Go uses
its existing engine. Keep `TestProjectAnalyzer` honoring the Java
`--ifds-bidirectional` flag; do not lose the runner fix during the rebase.

## 9. Removed or unused entities

The final rebased tree must not retain duplicate old/new paths for these:

- Ordinary `PositionAccessor.AnyFieldAccessor` and its conversion branches.
- Serialized/JVM selected-clean `reach` property and constructors using it.
  The common evaluator/core clean-reach types remain.
- Old resolver array expansion and sink array-reader patch helpers.
- `mayBeArray`/`callArgumentMayBeArray` wiring in new-core predicates/forms.
- `JIRRuleForms.stringBytes()` and its implicit clean operation.
- Spring object-source and exit-check widening helpers and Continuation hack.
- Unconditional appending of default getter rules to explicit pass rules.
- Old single-module Java model settings and moved duplicate model sources.

Retain RulePosition.anyAfter, explicit element positions, CMAny atoms,
selected below cleaners, source-definition reset reach, model API resources,
branch selection metadata, generated-step identities, complete predefined
summaries, legacy engine support and the existing optional GROUP mode.
None is made unused by deleting the ordinary AnyField position accessor.

## 10. Principal examples and required observations

Facts below use FULL mode. `N` means NORMAL and `D` means DEMAND.
Transfer templates are shown before ordinary limits and C5. A concrete rule
template is not an admitted analyzer premise. Existing C2 owns admission.

### E01: an array type must not add a hidden sink input

```java
void check(Object[] a) {
    // Offered at the call: a.[*].$/T, N. No a.$/T.
    sink(a);  // plain CM(arg0,T): no hit
    sinkStar(a); // CM(arg0,T) OR CMAny(arg0,T): hit
}
```

The old implicit element reader can make both hit. The migrated core must
hit only the starred check. Explicit `CM(arg0.[*],T)` still hits. This applies
to source and method-boundary position binding too.

### E02: a whole-object source remains uniform, a pass remains MAY

```java
void check() {
    Object x = sourceStar(); // compiler: Exact(ret) and AnyAfter(ret)
    // Source templates: ZERO -> x.$/T and ZERO -> x.MUST/T.
    sinkT(x.f);              // explicit starred source supplies this field
}
```

`CopyAllMarks(Exact(p),AnyAfter(q))` instead gives a MAY output. It must not
assert uniform taint on every q field. Backward lowering retains this
distinction. Main's first-marker normalization maps `p.f.AnyField.g` to
AnyAfter(p.f), with no invented concrete g in the descriptor.

### E03: a conjunction still needs both positions

```java
void check(Box p, Box q) {
    // Offered: p.f.$/T, N. No U anywhere under q.
    guarded(p,q); // CMAny(p,T) AND CMAny(q,U): not satisfied
}
```

A star adds alternatives within its one check. It cannot satisfy the other
conjunct or authorize a ZERO-premise source. Retain the current ND/contributor
and layer rules after complete guard evaluation.

### E04: accessor focus and pass-through sanitizer

```java
void check(Request request, Object p) {
    // request.MUST/T, N.
    Object safe = request.getRequestURI(); // sanitizer focuses on safe
    sinkT(request.getParameter("url"));   // receiver remains tainted

    Object cleaned = sanitize(p); // focus p: retain entering-argument clean
    sinkT(cleaned);               // use existing clean/pass semantics
}
```

The accessor sanitizer must not emit a receiver clean merely because its
pattern names request. Explicit by-side-effect behavior and focus-free rules
keep their main-defined policies.

### E05: exact String cleaning has no hidden byte-field action

```java
void check(String s) {
    // Model facts: s.$/T and s.<string-bytes>.$/T, N.
    cleanValueOnly(s); // RemoveMark(T,Exact(s))
    // Keep the byte-field fact. Remove the exact value fact.
}
```

An explicit starred clean supplies the below action separately. A source
definition targeting AnyAfter(s) still uses the existing whole-region reset
when main's rule-redefinition stage requests that reset.

### E06: getter fallback cannot bypass an explicit model

```java
Object getValue(Box p) { /* external modeled method */ }
```

For a prepared explicit `p.left.* -> ret.*`, an offered `p.right.$/T` produces
no return through that pass rule. It must not activate default fallback.
Without an explicit prepared pass rule, the eligible default reads the named
`this.<get-default>` slot. A rewritten-false explicit row does not block it.

### E07: controller exit rules still handle stored flows

```java
@PostMapping void save(Request request) { repository.save(request.value()); }
@GetMapping Object load() { return repository.find(); }
```

For a controller initial `repository.content.*/T`, the normal read can give
`repository.content.*/T -> ret.*/T`. The annotation-selected starred exit sink
must still be evaluated on that conditional result. Do not require ZERO.
The generated registry cleanup retains its complete predefined summary.

### E08: named model properties remain distinct

```java
Cookie c = new Cookie("name", "value");
c.setPath(sourceT()); // named path slot receives T
sinkT(c.getDomain()); // domain is a different slot; no carrier alias is added
```

The same principle applies to QName parts, formatter properties and model
container content. Fields are not renamed back to one generic carrier.

### E09: source requests, statics and loop ownership stay in their pipeline

```java
Object guarded(Box p) { // CMAny(p,T) assigns U to ret.$
    return null;
}
void main() {
    C.f = sourceT();
    while (again()) sinkT(C.f);
}
```

The first rule can request T through the existing new-core request path.
For the second program, the executed write supplies the existing static pool;
run-1 static conclusions remain D; the sink Target goes to the existing
nearest boundary. No main legacy unfold state or method-level loop shortcut
is added. Later demands keep the existing static/Target handoff rules.

### E10: wrappers preserve support and logical identity

For one pass input edge with layer D, E, mx and H=false, wrapper conversion
must not yield N, clear exclusions or set H=true. With H=true it retains that
membership. Same-geometry plain/protected rows remain two memberships.
Rebuilding the same owner's form keeps its original rule/action IDs.

### E11: the legacy option does not change bidirectional field depth

With FULL and the normal schedule, `--iteration-limit 0` still starts run-1
at limit 1 and run-2 at limit 1. It emits one ignored-option diagnostic.
The same holds for another explicitly supplied cap. The legacy lane retains
its actual cap behavior.

## 11. Proof and validation gates

The [proof map](main-migration-proofs.md) states the constructive component
proofs, counterexamples and implementation obligations. Its Lean model
checks position normalization, Boolean predicate translation, source/pass
target distinction, source identity, support framing, clean/reset scope,
fallback selection and option isolation.

These are scoped adapter proofs. They do not prove a Java parser, model IR
loader, Kotlin implementation or whole-analyzer convergence. Reuse the
existing AP proofs only where their primitive inputs and contracts are kept.
Re-run the existing full-mode Conductor MUST, cleaner, ZERO-loop and
plain/protected regressions with the migrated adapter.

For implementation, use TDD at each seam: create the failing regression,
then adapt the seam, then run its focused tests. Validate source/entry/exit,
call, static-field source, metadata-reset and cached rebuild paths. Confirm
that rejected rules publish no partial form. Check forward and backward
forms from the same forward definition.

Then run native core/JVM suites and actual Java bidirectional rules tests
through Gradle. Verify real driver events and successful analyzer status;
matching test-result counts after a timeout do not pass validation. Keep Go
compatibility tests on its current engine. Use the new main rule/model inputs
and record their revisions.

Adapt stale test API call sites while retaining their behavioral assertions.
Do not delete a failing fixture or relax its expected result as a compilation
fix. Inventory rejected bound rules under the new inputs. If a required
rule needs a shape outside the retained scope, report the concrete bound
rule and obtain a scope decision before extending transfer semantics.

Run OWASP and the selected Stirling-PDF, Conductor and Thingsboard settings
from the current validation procedure. Record finding identities, locations,
time/OOM status, latest reached and completed run, field schedule and input
rules/models. Do not substitute main's changed OWASP count for a bidirectional
quality comparison. Separate intended rule/model changes from adapter losses.
Current documented convergence failures remain visible; migration does not
silently waive or fix them.

All behavior decisions raised by this migration audit have a rule in this
spec. No further FN-producing counterexample is currently known for these
adapter rules in the stated model. Native correspondence and project
acceptance remain uncompleted until the post-rebase implementation is tested.
