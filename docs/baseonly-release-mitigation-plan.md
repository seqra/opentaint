# BaseOnly release mitigation plan

## Goal

Bring every BaseOnly access-path and summary-storage operation to verdict **(1): perfect design and implementation**.

An operation reaches verdict (1) only when all of the following are true:

1. Its contract is part of one authoritative, self-contained specification.
2. The contract states its relationship to the equivalent Tree operation.
3. The contract follows from the BaseOnly abstract domain rather than a list of examples.
4. Its implementation calls the shared domain primitives named by the specification.
5. Unit laws, bounded exhaustive tests, and Tree differential tests cover the contract.
6. There is no known forward, trace-resolution, serialization, concurrency, or performance counterexample.

Passing the current test suite alone is not verdict (1). Updating a golden file to match an unexplained behavior is not mitigation.

## Scope

This plan covers only:

- `access/baseonly` access representation and operations;
- BaseOnly initial/final facts and deltas;
- BaseOnly exclusions, filtering, abstraction, serialization, and rendering;
- BaseOnly fact sets, summary stores, subscriptions, and side-effect-requirement stores.

Tree and Automata implementations are read-only references. Generic IFDS code changes are permitted only if an interface contract cannot otherwise be expressed, and require a separate review.

## Specification authority and Tree conformance

The specifications must have this precedence:

1. The public `FactAp`/storage interface semantics, made explicit from the confirmed Tree behavior.
2. The BaseOnly abstraction relation described by `project` and `concretize` below.
3. The packed BaseOnly representation.

Representation convenience must never override levels 1 or 2.

For a Tree access value `T`, let `project(T)` be its canonical BaseOnly abstraction. For an access value `A`, let `concretize(A)` be the set of concrete paths denoted by it. The fundamental release invariant is:

```text
concretize(T) ⊆ concretize(project(T))
```

For every public operation `op`, the corresponding result must be sound:

```text
concretize(opTree(T, ...)) ⊆ concretize(opBaseOnly(project(T), ...))
```

This has concrete consequences:

- if Tree returns a fact/delta, BaseOnly must not return `null` or an empty result solely because it cannot retain Tree's precision;
- if Tree says a containment/prefix relation holds, BaseOnly must also accept the projected relation;
- BaseOnly may return additional facts, matches, and reads only when they belong to the documented overapproximation;
- equality remains exact representation/domain equality and must not be replaced by overlap;
- exclusions and type filters may remove only paths that Tree would also remove.

### Accessor-view semantics inherited from Tree

The accessor views are deliberately not interchangeable:

- `getStartAccessors()` enumerates outgoing access edges. BaseOnly exposes its implicit structural self-loop as `AnyAccessor`, without storing it in the field slot.
- `getAllAccessors()` enumerates concrete accessors occurring in the represented paths and deliberately excludes `AnyAccessor`, matching Tree's `collectAccessorsTo` behavior.
- `startsWithAccessor(a)` and `readAccessor(a)` must agree for every accessor: a successful start has a non-null read and vice versa.
- `getStartAccessors()` must be sufficient for generic readers to discover every symbolic branch. It need not enumerate every concrete accessor accepted through an `AnyAccessor` edge.
- Type-info group access is a two-step logical path and must have the same start/read/all-accessor behavior as Tree after projection.

These rules must be captured explicitly in the conformance specification and tests. In particular, BaseOnly must not derive both views from raw packed slots.

## Required specification set

Before semantic implementation changes, add three normative documents:

1. `baseonly-access-domain-spec.md`
   - accessor alphabet and path grammar;
   - valid canonical BaseOnly states;
   - `project` and `concretize`;
   - abstraction ordering;
   - construction, observation, matching, delta, concat, filtering, and serialization laws.
2. `baseonly-tree-conformance.md`
   - one row for every public operation;
   - exact Tree behavior;
   - permitted BaseOnly widening;
   - forbidden BaseOnly loss;
   - executable differential property.
3. `baseonly-storage-spec.md`
   - logical keys and subsumption;
   - exclusion merge algebra;
   - delta/subscription semantics;
   - ownership and concurrency model;
   - normalized-alias behavior.

The existing example-based documents and golden files become evidence and regression fixtures, not normative specifications.

## Phase 0: establish the release gate and verdict ledger

Create a checked-in ledger with one row per operation listed below and these columns:

```text
operation | spec section | Tree relation | shared primitive | implementation | law tests | differential tests | verdict
```

Initially no row is verdict (1). A row can change to (1) only in the same change that provides all its evidence.

Record the current focused baseline. At the time of this plan, 141 BaseOnly tests run and six fail:

1. Stirling semantic sink split is rejected by exclusion handling.
2. suffix-AP concat accepts a cross-kind delta contrary to its current test.
3. suffix-AP `appendFinal` accepts a field-leading delta contrary to its current test.
4. one delta/concat golden file disagrees with current behavior.
5. logical type-info size is expected as 3 but implemented as 1.
6. type-info serialization writes an accessor count inconsistent with the encoded sequence.

Do not repair items 2–4 by choosing either current behavior or the old golden. First derive the expected outcome from `project`, `concretize`, and Tree differential behavior.

Exit criteria:

- the ledger contains every operation and storage listed in this plan;
- each row points to a proposed normative section and a Tree comparison;
- CI runs the focused BaseOnly suite even while some tests remain quarantined as known blockers.

## Phase 1: specify the BaseOnly abstract domain

### 1.1 Canonical representation

Specify, without referring to bit positions:

- which static accessor is retained;
- which structural accessor is retained when a path contains several fields/elements;
- how `AnyAccessor` changes the retained information;
- which semantic terminal is retained;
- whether the final accessor is explicit or implied after semantic terminals;
- the meaning and legal position of one abstraction marker;
- the exact meaning and lifecycle of a collapsed marker;
- whether type-info group/type is one encoded atom or two logical accesses;
- invalid combinations and how they are rejected.

The retained structural accessor must be chosen once for `build`, `prepend`, `append`, `appendFinal`, delta concat, abstraction, and deserialization. Based on normal path composition, the proposed rule is the **outermost still-representable structural accessor**: preserve an existing prefix field; take a suffix field only when the prefix has none. This rule must be confirmed against Tree projection before implementation.

Raw packed values must not be constructible outside a validated codec. Define the bit width and maximum interned-index range, including the static slot's current 16-bit limit.

### 1.2 Shared semantic primitives

Specify these primitives first; all higher operations must be equations over them:

- `canonicalize(path or components) -> Access`
- `concretize(access) -> PathLanguage` (a test/reference operation, not necessarily production materialization)
- `consume(access, accessor) -> Access?`
- `covers(pattern, fact) -> Boolean` (directional language inclusion)
- `mayOverlap(left, right) -> Boolean` (symmetric non-empty intersection)
- `residual(pattern, fact) -> set<Delta>`
- `graft(prefix, delta, typeChecker) -> Access?`
- `logicalAccessors(access) -> logical graph/view`
- `exclusionAllows(access/delta, exclusions) -> Boolean`

Do not use one compatibility predicate for both `covers` and `mayOverlap`. In particular, the current missing-field wildcard relation is non-transitive and cannot be called containment.

### 1.3 Algebraic laws

The normative spec must include at least these laws:

- canonicalization is idempotent;
- projection is monotone: adding concrete paths cannot make the abstraction denote fewer paths;
- `consume` agrees with `startsWithAccessor` and `readAccessor`;
- start/all accessor views follow the Tree conventions above;
- `covers` is reflexive and transitive;
- `mayOverlap` is reflexive and symmetric;
- equality implies mutual coverage, but overlap does not imply equality;
- `residual(P, F)` is empty exactly when `P` cannot match `F`;
- for every residual `D`, `graft(P, D)` covers `F`;
- an empty delta is the identity for concat;
- delta concat is associative after canonicalization;
- `clearAccessor` removes exactly the represented branch, or returns a documented sound widening when exact removal is unrepresentable;
- serialization round-trips every valid canonical state;
- render/parse diagnostics uniquely expose static-, field-, and suffix-position abstraction.

### 1.4 Tree differential semantics

For each law, generate a corresponding Tree path/tree and compare the projected result. The conformance matrix must cover:

- construction and prepend;
- read/start/start-view/all-view;
- clear and exclusion;
- containment, equality, and overlap;
- final delta and concat;
- initial split-delta and concat;
- abstraction, collapse, restoration, and rebasing;
- type filtering;
- serialization-visible logical structure.

Exit criteria:

- all valid states have one unambiguous denotation;
- every operation has an equation over shared primitives;
- every permitted Tree divergence is explicitly a widening;
- no operation contract is defined only by a table of special cases.

## Phase 2: build executable reference and differential tests

Implement a slow, test-only reference domain using explicit path languages or bounded symbolic paths. It must not reuse BaseOnly production operations.

Generate:

- all valid canonical BaseOnly states over a small accessor alphabet;
- invalid packed states for validator tests;
- Tree paths up to a bounded depth, including static, two distinct fields, element, Any, semantic mark, type-info group/type, final, and abstraction;
- exclusion sets: empty, concrete single/multiple, and universe where legal;
- primitive/reference type-checker outcomes.

Test layers:

1. **Representation laws:** codec, validity, canonicalization, logical enumeration.
2. **Operation laws:** exhaustive combinations for the algebra in phase 1.
3. **Tree differential laws:** project Tree operands, apply both operations, and assert language inclusion.
4. **Metamorphic laws:** equivalent construction routes produce the same canonical result.
5. **Regression samples:** Stirling and all retained dataflow reproductions.

The existing pin/golden tests remain only if each expected row is generated from or cross-checked against the reference model. Otherwise replace them with property tests.

Exit criteria:

- every ledger row has a failing-or-passing executable contract before its production rewrite;
- every current e2e root-cause sample maps to a named domain law;
- test failures distinguish “spec unresolved” from “implementation violates spec.”

## Phase 3: replace access operations with the shared algebra

### 3.1 Representation and construction

Rewrite these through the single canonicalizer:

- pack/unpack and validity checking;
- `build`;
- `abstractAt`;
- `prepend`;
- `append`;
- `appendFinal`;
- deserialization construction;
- summary normalization/projection.

Remove slot-specific fall-throughs such as accepting every `abstractAt` slot other than 0/1 as slot 2. Invalid states fail at the boundary; production operations return only canonical states.

### 3.2 Logical observation

Implement one logical transition/view component and derive:

- `read`;
- `startsWith`;
- `getStartAccessors`;
- `getAllAccessors`;
- `headOrNull`/first logical accessor;
- `size` and `depth`;
- `isAbstract`;
- filtering and rendering.

Preserve the Tree asymmetry: Any belongs in the start-edge view but not the all-concrete-accessors view. Count logical type-info group/type/final structure, not occupied packed slots.

### 3.3 Relations and composition

Replace `fieldsCompatible`, `containsAccess`, `matchPrefix`, `splitConcreteInitial`, and special branches in `splitDelta` with the named relations:

- fact containment and summary subsumption use directional `covers`;
- summary candidate indexing uses `mayOverlap`;
- delta creation uses `residual`;
- all concat/append paths use `graft` followed by `canonicalize`;
- exact equality uses canonical equality.

No split or concat branch may inspect an AP slot merely to select a hand-coded outcome. Slot inspection is confined to the primitive interpreter/canonicalizer.

### 3.4 Abstraction lifecycle

Define and implement one state machine for:

- `abstractOnly`;
- most-abstract initial/final facts;
- collapse;
- restore/remove abstraction;
- initial and final rebase;
- stable/transient abstraction boundaries;
- rendering and serialization.

Either give `COLLAPSED_MARK` a complete denotation and transition table or remove it. Initial and final rebase must preserve the same abstraction meaning.

Exit criteria:

- `BaseOnlyAccessOps` is a thin implementation of the named primitives;
- no duplicated construction, prefix matching, or accessor traversal remains;
- all representation, law, and Tree differential tests pass;
- the six focused-suite blockers are resolved by spec-backed behavior.

## Phase 4: align facts, deltas, exclusions, and type filtering

Rewrite wrappers as direct delegation to the shared access algebra:

- `BaseOnlyInitialFactAp`;
- `BaseOnlyFinalFactAp`;
- empty/node initial deltas;
- empty/node final deltas;
- initial-fact abstraction;
- manager factories and views.

Required corrections:

- final `delta` checks the base before matching, as Tree does;
- final `concat` applies `FactTypeChecker` and cannot recreate primitive/incompatible facts;
- every delta's `isAbstract` reflects any legal abstraction, not only suffix abstraction;
- `splitDelta` and `delta` use the same residual definition in opposite workflows;
- exclusions are checked through one semantic-head operation, including Any and type-info group;
- Universe handling is explicit for every call site;
- factory methods cannot manufacture invalid or manager-incompatible facts;
- equality/hash either include the manager or document and assert the manager-scoped invariant.

Tree differential tests must include boxed/primitive drop rules separately from AP loss so intentional primitive behavior cannot mask a forward regression.

Exit criteria:

- every fact/delta operation has verdict (1) in the ledger;
- Stirling and all trace-resolution dataflow tests pass in both Tree and BaseOnly;
- no production operation relies on rendering or packed-slot shape to infer semantics.

## Phase 5: redesign storage around explicit keys and SWMR publication

### 5.1 Concurrency contract

Document and enforce ownership by storage type:

- summary stores and side-effect requirements: one writer, multiple concurrent readers, eventually consistent;
- fact sets and final-fact lists: single-threaded;
- subscription registries: analysis-thread-owned unless a call site proves otherwise.

Use the confirmed Tree/Automata publication approach for SWMR structures: a writer may mutate/replace internal tables, while readers traverse a safely published table snapshot. Do not add concurrent structures to single-thread fact sets.

Every value must be fully initialized before publication. A newly published identity-summary layer must never be transiently observable with `Universe` exclusion if that value was not committed.

### 5.2 Shared storage primitives

Introduce/reuse:

- one `BaseOnlyInitialAccessIndex<V>` driven by `mayOverlap` for candidate selection;
- one authoritative `covers` check after candidate selection;
- one exclusion merge/delta accumulator with explicit union/intersection semantics;
- one initialized-before-publication SWMR value holder;
- one subscription candidate collector whose result covers every Tree-selected registration;
- one direct `isCollapsed` guard at each BaseOnly storage boundary that can receive a transient final fact.

### 5.3 Storage-by-storage migration

Apply the shared primitives to:

- intraprocedural Z2F exact set;
- intraprocedural ordinary F2F set;
- intraprocedural ND set;
- final-fact list;
- method Z2F summary storage;
- method non-identity F2F storage;
- method identity F2F storage;
- normalized F2F lookup;
- method ND summary storage;
- fact-side-effect summaries;
- side-effect requirements;
- Z2F/F2F/ND subscriptions.

Specific requirements:

- coalesce repeated updates for one logical F2F key within a batch before emitting one exclusion delta;
- identity-summary insertion must perform the same subsumption in every bucket, including the `NO_ACCESSOR` bucket, and prune across all buckets;
- readers must never observe partially initialized exclusion state;
- fact-side-effect and side-effect-requirement lookup must filter by access compatibility, not only base;
- Z2F, F2F, and ND subscriptions must preserve their logical endpoint/base partitions and return a
  candidate superset for either `emptyDeltaRequired` mode;
- subscriptions may broadcast within the selected registration group because the BaseOnly
  projection cannot soundly partition all represented Tree residuals; downstream residual
  processing is authoritative.

### 5.4 Normalized summaries

Do not maintain a second mutable summary store containing copied normalized edges. A normalized edge is a query-time alias/projection of one primary edge:

- the primary edge is the only source of truth;
- the alias participates in backward lookup when required;
- exclusions are read from the primary edge;
- the alias emits no independent delta and owns no subscription state;
- lookup deduplicates primary and normalized views by logical edge identity;
- an explicit one-way analyzer lifecycle transition enables the conservative trace-query view only
  after forward analysis has finished; each query snapshots that phase once at entry;
- trace-query lookup may scan primary records and emit primary/alias candidates beyond the ordinary
  forward-pattern bucket because backward containment/residual processing is authoritative.

This implements the earlier decision to drop delta behavior from normalized storage and prevents duplicated finals and divergent exclusion state.

### 5.5 Storage verification

For every SWMR store, add deterministic concurrency tests that force:

- read during first insertion;
- read during rehash/table replacement;
- read during exclusion narrowing;
- repeated same-key updates in one batch;
- subsumption in both insertion orders;
- normalized and primary lookup overlap;
- subscription installation before and after insertion.

Compare emitted logical edge sets and deltas against a synchronized reference map. Eventual consistency permits a reader to see an older complete snapshot; it does not permit impossible, partially initialized, or duplicate logical states.

Exit criteria:

- every storage row has an explicit ownership/publication contract;
- logical results match the synchronized reference model;
- Thread Sanitizer/stress-style runs show no mutation/iteration failure;
- allocation and lookup benchmarks show no normalized-edge duplication or base-wide broadcast.

## Phase 6: serialization and compatibility

Define a compact serialized payload from the logical BaseOnly state, not `size` plus an unrelated accessor iterator. It has no BaseOnly magic, header, or version field.

The format must encode:

- base;
- canonical static/structural/semantic components;
- abstraction kind/position or its representation-independent equivalent;
- collapsed state, if retained;
- terminal/final semantics;
- type-info group/type structure;
- exclusions.

Deserializer flow is `decode -> validate -> canonicalize -> construct`. Reject corrupt/unknown states. Add round trips for every generated valid state and compatibility fixtures for any format already persisted outside tests.

Exit criteria:

- exhaustive valid-state round trips pass;
- malformed states fail predictably;
- a serialized fact has the same Tree-relative denotation after restore;
- serializer and renderer use the shared logical view.

## Phase 7: integration, e2e, and performance release gates

Run gates in this order:

1. BaseOnly representation and law tests.
2. BaseOnly storage reference/concurrency tests.
3. Full `core/src/test` JVM and Go dataflow tests.
4. Both querylang suites.
5. Retained BaseOnly fuzz/dataflow regressions with path sampling enabled.
6. Full Tree-versus-BaseOnly e2e corpus with identical analyzer settings.

Correctness gates:

- zero Tree finding missing from a complete BaseOnly analysis, except an individually approved and documented domain limitation;
- zero vulnerability filtered only because BaseOnly cannot resolve a Tree-resolvable trace;
- zero analyzer-status regression, OOM, or timeout attributable to BaseOnly;
- BaseOnly-only findings are sampled to confirm they follow from intended widening;
- code-flow comparison is made only when path sampling settings are identical.

Performance gates:

- record summary counts, candidate edges visited, accepted edges, subscription fan-out, trace lookups, allocations, scan time, and peak memory;
- compare identical commits/configuration against Tree and against the previous BaseOnly baseline;
- no project may regress to incomplete/OOM/timeout;
- any material scan-time or peak-memory regression must be explained by counters and either fixed or explicitly waived before release;
- BaseOnly's aggregate summary lookup and memory costs must demonstrate the intended advantage, not merely equal finding counts.

Keep the e2e artifact/report generator as a release job so later changes cannot silently reintroduce misses or path-sampling configuration differences.

Exit criteria:

- all test layers pass;
- every ledger row is verdict (1);
- all e2e projects with complete Tree results also complete in BaseOnly;
- correctness and performance reports are attached to the release commit.

## Operation-to-phase checklist

| Operation family | Required shared definition | Tree comparison | Mitigation phase |
|---|---|---|---|
| packing, validity, factories | canonical state | Tree path projection | 1, 3 |
| build, prepend, append, appendFinal | `canonicalize` + `graft` | projected construction result is covered | 1–3 |
| read, startsWith, head/tail | `consume` | every Tree read survives projection | 1–3 |
| start accessors | logical outgoing-edge view | includes Tree Any edge/virtual BaseOnly Any branch | 1–3 |
| all accessors | logical concrete-accessor view | excludes Any as Tree does | 1–3 |
| size, depth, abstract status | logical graph | same metric definition after projection | 1–3 |
| clear | branch subtraction/widening rule | cannot erase unrelated Tree paths | 1–3 |
| contains | `covers` | Tree true implies BaseOnly true | 1–3 |
| summary candidate match | `mayOverlap` then `covers` | candidate superset, authoritative same relation | 1–5 |
| equality | canonical equality | exact projected-state equality | 1–4 |
| final delta/concat | `residual` + `graft` | Tree result is covered | 1–4 |
| initial split/concat | `residual` + `graft` | Tree reconstruction is covered | 1–4 |
| exclusions | `exclusionAllows` | removes no Tree-allowed branch | 1, 4 |
| type filtering | logical traversal + checker | preserves Tree-compatible reference paths | 1, 4 |
| collapse/restore/remove/abstractOnly | abstraction state machine | denotation preserved or widened as specified | 1, 3–4 |
| rebase | base substitution; restore only the documented transient remove/rebase state | same Tree operation plus BaseOnly lifecycle completion | 1, 4 |
| rendering | logical view | diagnostic distinction for every state | 3 |
| serialization | logical state codec | denotation round trip | 2, 6 |
| initial access index | `mayOverlap` | same candidate class as Tree filter | 2, 5 |
| Z2F/F2F/ND stores | exact key + merge algebra | same logical summaries, BaseOnly widening allowed | 2, 5 |
| identity F2F subsumption | `covers` | same containment intent as Tree | 2, 5 |
| normalized lookup | projection alias | enables Tree-resolvable backward edge | 2, 5 |
| FactSE/requirements | index + exclusion merge | no base-wide false broadcast/loss | 2, 5 |
| subscriptions | conservative candidate collector | covers Tree selection; downstream residual is authoritative | 2, 5 |

## Required code sharing

The final implementation must have one production implementation for each of these concepts:

1. canonical projection/construction;
2. logical accessor transition and views;
3. directional coverage;
4. symmetric overlap;
5. residual creation;
6. delta graft/concat;
7. exclusion compatibility;
8. abstraction lifecycle;
9. transient collapsed-state rejection;
10. initial-access indexing;
11. exclusion merge and per-key delta emission;
12. subscription matching;
13. initialized SWMR publication.

Callers may wrap results in initial/final fact types, but must not reimplement these decisions.

## Change sequencing

Use small, reviewable changes in this dependency order:

1. normative specs, conformance matrix, and verdict ledger;
2. independent reference model and failing law/differential tests;
3. validated representation and canonicalizer;
4. logical access views and Tree accessor-view conformance;
5. coverage/overlap/residual/graft algebra;
6. fact, delta, exclusion, type, and abstraction wrappers;
7. storage indexes and matching without concurrency changes;
8. SWMR publication and exclusion-delta coalescing;
9. normalized alias removal from mutable/delta storage;
10. subscription and side-effect filtering;
11. serializer migration;
12. full suites, e2e correctness, and performance verification.

Each change must update the ledger. Do not combine a semantic change with a performance rewrite unless the reference tests prove the logical edge set before and after.

## Final release definition

BaseOnly is ready only when the ledger contains no verdict (2) or (3), no unresolved golden expectation, and no undocumented Tree difference. At that point the implementation is not merely regression-free: every behavior is derived from a minimal abstract-domain specification, every public operation is sound with respect to Tree, every shared concept has one implementation, and every storage meets its stated ownership and publication contract.
