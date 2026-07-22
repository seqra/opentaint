# BaseOnly access-domain specification

Status: **normative** for the BaseOnly release mitigation.

This document defines the BaseOnly access domain independently of its packed
representation. Production code, tests, serialization, and summary storage must
implement this document. Existing BaseOnly behavior and golden files are not
authoritative when they disagree with it.

The Tree domain is the behavioral reference for the public `FactAp` interfaces.
The precise conformance obligations are in
[`baseonly-tree-conformance.md`](baseonly-tree-conformance.md).

## 1. Goal and soundness boundary

BaseOnly is a finite abstraction of Tree access paths and access trees. It may
merge Tree states and therefore report more flows, but it must not lose a Tree
flow merely because the packed form cannot retain Tree's precision.

Let `Paths(X)` be the set of logical accessor paths accepted by a Tree or
BaseOnly value `X`. Let `project(X)` return a finite set of canonical BaseOnly
values (normally one; more are allowed when a Tree contains incompatible
branches). The fundamental invariant is:

```text
Paths(X) ⊆ ⋃ { Paths(A) | A ∈ project(X) }
```

For every public operation `op`, every Tree result must be represented by a
BaseOnly result:

```text
⋃ Paths(opTree(X, ...)) ⊆ ⋃ Paths(opBaseOnly(project(X), ...))
```

Here an absent result, `null`, an empty result list, or a rejected summary has an
empty path set. Consequently, inability to represent a precise Tree result
requires widening; it never permits rejection. Base mismatch, a Tree-equivalent
exclusion, and a Tree-equivalent type incompatibility remain valid reasons to
reject.

`project` is manager-relative because field-sensitive and field-insensitive
managers have different canonical states.

## 2. Accessor alphabet and valid logical paths

The accessor alphabet is partitioned as follows:

| Category | Members | Symbol |
|---|---|---|
| static | `ClassStaticAccessor` | `S` |
| structural | `FieldAccessor`, `ElementAccessor` | `H` |
| implicit structural loop | `AnyAccessor` | `?` |
| taint semantic | `TaintMarkAccessor` | `M` |
| value semantic | `ValueAccessor` | `V` |
| type semantic | `TypeInfoAccessor`, optionally preceded by `TypeInfoGroupAccessor` | `T`, `G T` |
| terminal | `FinalAccessor` | `$` |

A well-formed concrete path has this grammar:

```text
path       ::= static? structural* terminal
static     ::= S
structural ::= H
terminal   ::= $
             | M $
             | V M $
             | T $
             | G T $
```

`AnyAccessor` is a Tree graph edge, not a concrete accessor in a path. BaseOnly
never stores it. A missing structural slot before a semantic or suffix-abstract
terminal implicitly denotes its universal structural self-loop. This deliberately
overapproximates a Tree `AnyAccessor` whose configured unroll strategy is narrower.
`T $` is the residual after consuming `G` from `G T $` and is also a
valid direct semantic path. `TypeInfoGroupAccessor` is a real logical step even
when BaseOnly stores the following type as one compact terminal component.

Malformed orderings are rejected at public construction boundaries. A
projection of an otherwise valid Tree graph that cannot be expressed exactly is
widened at the earliest lost position.

## 3. Canonical BaseOnly state

A canonical access is the logical tuple:

```text
(static, structural, terminal, valueAccessorState, abstraction)
```

where:

- `static` is absent or one concrete `S`;
- `structural` is absent or the **outermost** concrete `H` after `static`;
- `terminal` is absent, `$`, a concrete taint mark `M`, or a concrete type `T`;
- `valueAccessorState` is `Normal` or `Value`. `Value` means that a taint-mark
  suffix is preceded by `ValueAccessor`. For a type suffix, the same encoded state
  reconstructs its analogous `TypeInfoGroupAccessor` prefix. Every
  non-semantic state uses `Normal`;
- `abstraction` is absent or an abstract node at exactly one of the three
  positions `STATIC`, `STRUCTURAL`, or `SUFFIX`.

The suffix atom stores the concrete semantic accessor and the state records
whether its category wrapper occurs immediately before it. Let `W(M) = V` and
`W(T) = G`. For a semantic accessor `X`, the denotation is:

```text
TerminalPath(X, Normal) = X $
TerminalPath(X, Value)  = W(X) X $
```

One packed access denotes one terminal path. A union containing both paths is
represented by two facts and is never encoded as a third state. This distinction
prevents `M $` from being confused with `V M $`, and a type residual `T $` from
being confused with `G T $`.

The implicit `$` belongs to every alternative. Public reads, accessor views,
clear, exclusions, filtering, relations, residuals, concat, storage,
serialization, and rendering operate on this logical alternative set. No
operation may recreate a wrapper state that was removed, except by retaining a
separate fact carrying that state.

### 3.1 Retention rule

Construction and composition always retain:

1. the first (outermost) static accessor;
2. in field-sensitive mode, the first (outermost) concrete structural accessor;
   in field-insensitive mode, no structural field slot;
3. the first well-formed semantic terminal and whether its parsed path is direct
   or wrapper-prefixed.

A second distinct static is invalid. Later structural accessors are not allowed
to replace the retained outermost accessor. In field-insensitive mode no
concrete structural identity is retained. An explicit Tree `Any` is projected
to the same absent structural slot in either mode. Every semantic root has the
implicit structural self-loop.

When incompatible projected branches differ in an ordinary retained component,
`canonicalJoin` retains their common canonical prefix and places abstraction at
the first position where they differ. When they differ only in
`valueAccessorState`, it returns both facts. Collection interfaces keep this
minimal covering set and never manufacture a union state.

When structural information is discarded:

- a discarded or explicit structural branch is represented by an absent field
  slot and the implicit structural loop;
- `V M $` projects to `(M, Value)` and `G T $` projects to `(T, Value)`;
  the wrapper is not added to a direct terminal;
- an abstract suffix state already widens by its implicit structural-`Any`
  transition;
- an exact `$` terminal cannot express a discarded structural step and therefore
  widens to an abstract suffix at the last exact prefix;
- if the lost step precedes the retained structural accessor or static accessor,
  widening moves to the corresponding earlier abstraction position.

This rule applies identically to `build`, `prepend`, `append`, final concat,
initial concat, Tree projection, deserialization, and summary normalization.

### 3.2 Abstract positions

An abstract marker represents Tree's abstract-node acceptance at one category
boundary:

- `STATIC`: no prefix is committed;
- `STRUCTURAL`: the optional concrete static prefix is committed;
- `SUFFIX`: the optional concrete static and structural prefix is committed.

`SUFFIX` and semantic terminal states have an implicit structural-`Any`
self-loop. `AnyAccessor` is never an explicit stored graph edge. Earlier abstract
positions are refinement boundaries and do not fabricate a public outgoing
edge.

An abstraction marker terminates the canonical tuple. Components after it must
be absent. There is at most one abstraction marker.

### 3.3 Canonical validity

The following are valid:

```text
STATIC abstract:       (*, -, -, STATIC)
STRUCTURAL abstract:   (S?, *, -, STRUCTURAL)
SUFFIX abstract:       (S?, H?, -, SUFFIX)
exact value:           (S?, H?, $, none)
semantic value:        (S?, H?, X, Normal | Value, none)
```

Here `X` is a concrete taint mark or type. `Normal` and `Value` denote
`TerminalPath(X, state)` above. Only semantic values may use `Value`; every
abstract, empty, exact-`$`, and transient state uses `Normal`.

The internal empty access is valid only as an intermediate or empty delta. A
fact must never contain it.

The following are invalid:

- multiple abstraction markers;
- a component following an abstraction marker;
- a static accessor outside the static component;
- `AnyAccessor` in any packed slot (it is implicit and has no stored slot);
- `TypeInfoGroupAccessor` without a following type;
- `ValueAccessor` without a following taint mark;
- a `Value` state on a non-semantic suffix;
- a semantic terminal without its logical `$`;
- more than one semantic terminal;
- a nonempty exact prefix with neither a terminal nor an abstraction;
- an accessor index that does not belong to the slot category;
- an index outside the codec's documented range.

`COLLAPSED_MARK` is not a stable domain state. It has no standalone
Tree denotation and is forbidden in deltas, storage, initial facts, and
serialization. One transient operational state is reserved for
flow-function recursion:
`COLLAPSED` in the suffix slot. It means that suffix abstraction was temporarily
removed while the concrete prefix is processed. It may exist only in a final
fact returned by `removeAbstraction`; it is restored to suffix abstraction by
`rebase`. Storage, initial facts, deltas, and serialization reject it.

### 3.4 Packed codec

The current packed `Long` reserves 16 bits for the static component, 24 bits for
the structural component, and 24 bits for the suffix word. The suffix word is
split into a **23-bit biased accessor value** and a one-bit value-accessor-state
flag. With bias `3`, the suffix accessor range is `-3..8_388_604` inclusive.
`Normal` and `Value` use flag values `0` and `1`. Static and structural retain
their existing 16-bit and 24-bit
biased ranges. These widths are implementation limits, not domain semantics.

Reducing the suffix accessor payload from 24 to 23 bits is a format invariant:
construction, raw packing, deserialization, and interner-to-slot conversion must
reject an out-of-range suffix rather than truncate its high bits into the
state flag. The state bit is zero for every non-semantic suffix.

Raw packing and unpacking are codec-internal. The codec must validate category,
range, uniqueness, ordering, and canonical form. Deserialization is:

```text
decode -> validate -> canonicalize -> construct
```

No public or storage API may accept an arbitrary packed `Long` as a valid fact.

## 4. Logical graph and accessor views

Every operation in this section is derived from one logical graph view.

Concrete static components form ordinary single edges. A retained concrete
structural component denotes that edge followed by zero or more projected-away
structural edges before the terminal; after consuming it, the implicit
`AnyAccessor` loop is exposed when a semantic terminal remains. A missing
structural slot before a semantic or suffix-abstract state forms the same loop
and admits its suffix alternatives at zero length. A semantic terminal expands to exactly the
single path selected by `valueAccessorState`; it does not gain the other path
implicitly. A `SUFFIX` abstract state exposes the
implicit `AnyAccessor` self-loop required by its widening.

### 4.1 `consume`, `readAccessor`, and `startsWithAccessor`

`consume(A, a)` follows the logical outgoing edge `a` and returns the canonical
residual state. It returns no result if no such edge exists.

```text
startsWithAccessor(a) == (consume(A, a) exists)
readAccessor(a)       == consume(A, a), wrapped with the same base/exclusions
```

Reading a concrete prefix removes that prefix and may expose the implicit
structural residual. Reading a concrete structural accessor through the implicit
Any self-loop of a semantic or suffix-abstract state returns the same state.
Reading a semantic accessor advances each matching
logical alternative:

- `(X, Normal)` reads `X` to `$` and does not read `W(X)`;
- `(X, Value)` reads `W(X)` to `(X, Normal)` and does not read `X` at the
  wrapper root;

The residual after a wrapper read is always `Normal`; the wrapper has already
been consumed. The same rules apply when the terminal is admitted at zero length
through implicit Any.

`AnyAccessor` is never stored. A missing structural slot before a semantic or
suffix-abstract terminal denotes the implicit Any self-loop and accepts every
concrete structural read without enumerating fields.

### 4.2 `getStartAccessors`

This returns the set of logical outgoing edge labels at the current node. It
includes `AnyAccessor` whenever the compact state has the implicit structural
self-loop. It does not expand that loop into concrete fields.

For a root semantic `(X, state)`, the start set is:

```text
Normal -> { AnyAccessor, X }
Value  -> { AnyAccessor, W(X) }
```

Thus a compact semantic root exposes both its terminal alternative and its
implicit structural loop. A suffix-abstract root returns `{AnyAccessor}`; its
suffix alternatives are
readable through the zero-length wildcard but are not additional raw root-edge
labels.

### 4.3 `getAllAccessors`

This returns all **concrete logical accessors** occurring anywhere in the
represented graph. As in Tree's `collectAccessorsTo`, it deliberately excludes
`AnyAccessor`, even though `getStartAccessors` exposes it. For a semantic
terminal it always includes `X` and `$`; it includes `W(X)` exactly when the
state is `Value`. It must not report `ValueAccessor` or
`TypeInfoGroupAccessor` when the state is `Normal`.

The two accessor views are intentionally asymmetric and must not share a raw
slot iterator.

### 4.4 Head, size, depth, and abstract status

- `headOrNull` and `firstAccessorOrNull` follow the one path selected by the
  access's value-accessor state. A set containing both alternatives is handled
  by iterating its two facts; no individual access has two semantic heads.
- `size` counts occupied concrete packed slots. Static, field, and suffix each
  contribute at most one; abstract markers, missing slots, implicit Any, and a
  logical value/type wrapper do not contribute. Therefore `0 <= size <= 3`.
- `depth` equals this compact size. It is a bounded retention metric, not an
  attempt to reproduce Tree's node count, logical wrapper depth, or Any-cycle
  sentinel.
- `isAbstract` is true exactly when the logical graph contains abstract-node
  acceptance. Delta emptiness is independent of abstractness.

These metrics intentionally describe the compact representation. Semantic
operations must not use them as logical-path lengths.

## 5. Canonical construction

### 5.1 `canonicalize` and `build`

`canonicalize(sequence, fieldSensitive)` parses a well-formed logical accessor
sequence, applies the retention/widening rule in section 3.1, validates the
result, and returns its unique canonical state. It is idempotent.

`build(accessors, isAbstract)` is a compatibility entry point for
`canonicalize`. `isAbstract` adds abstract-node acceptance after the supplied
sequence; it does not silently reorder malformed input. A sequence ending in a
semantic accessor expands its implied `$` only when that convention is explicit
at the caller boundary; the canonical state always records the same terminal
meaning.

Construction assigns the value-accessor state from the parsed sequence:

```text
M [$]   -> (M, Normal)       V M [$] -> (M, Value)
T [$]   -> (T, Normal)       G T [$] -> (T, Value)
```

The wrapper must be followed by the corresponding semantic category. A lone
`V` or `G`, `G M`, `V T`, multiple semantics, or anything after `$` is invalid.
`build` returns one access and therefore one of the two states.

### 5.2 `abstractAt`

`abstractAt(prefix, position)` canonicalizes the exact prefix followed by an
abstract node at one of the validated `STATIC`, `STRUCTURAL`, or `SUFFIX`
positions (currently encoded as `0..2`). A prefix component at or after the
abstract position is invalid.

### 5.3 `prependAccessor`

`prepend(A, a)` is:

```text
canonicalize([a] + logicalPaths(A))
```

for every represented path, joined by the least canonical widening if required.
It obeys the outermost-retention rule in the **composed** path: a prepended
structural accessor becomes the new outermost structural accessor, while a
structural accessor appended at an abstraction cannot replace the already-known
outer prefix. Impossible Tree prepends remain impossible; representational loss widens.

`TypeInfoGroupAccessor` is accepted only before an already compact type suffix
and changes that terminal to `Value`. `ValueAccessor` is accepted only before
an already compact taint-mark suffix and likewise changes it to `Value`. This
models prepending the wrapper to the unwrapped residual; it does not merge paths.
A standalone or category-mismatched wrapper is rejected.

### 5.4 `graft`, append, and concat

`graft(prefix, suffix, typeChecker?)` substitutes each abstract accepting leaf
of `prefix` with `suffix`, like Tree concat, and canonicalizes the union.

- empty delta is the identity;
- a nonempty suffix with a static accessor can be grafted only at a position
  where Tree allows that static accessor;
- incompatible paths are rejected only when Tree/type checking rejects them;
- discarded precision causes widening: when two structural steps compete for
  the one retained field slot, keep the earlier known step and preserve an
  incoming semantic terminal behind its implicit structural-Any tail; if the
  suffix ends only in exact `$`, widen to suffix abstraction because no terminal
  can represent the discarded step;
- initial-delta concat uses the same graft without a type checker;
- final-delta concat uses the supplied `FactTypeChecker` and must not recreate a
  Tree-rejected or primitive-incompatible path.

`append` and `appendFinal` are implementation wrappers around `graft`; they do
not have independent slot-case semantics.

## 6. Relations

Three different relations are required.

### 6.1 Exact equality

Canonical access equality means equal canonical logical paths, including equal
value-accessor state. `Normal` and `Value` are unequal. Fact equality
also requires equal base and exclusions. Initial/final cross-kind `equalTo`
compares their logical projected graphs under the Tree cross-kind definition;
it is not overlap.

### 6.2 Directional coverage

```text
covers(pattern, fact) iff Paths(fact) ⊆ Paths(pattern)
```

Coverage is reflexive and transitive. It is used by authoritative storage
subsumption and canonical joins. A missing structural slot before `M` includes
the implicit Any loop, so compact `M.$` covers both its zero-length path and
`f.M.$`. A suffix-abstract pattern likewise covers concrete structural
continuations through its implicit Any loop.

For equal semantic accessor `X`, value-accessor states must be equal:

```text
Normal covers Normal only
Value covers Value only
```

Different semantic accessors never cover one another. `containsProjected` uses
the same value-accessor-state direction after its separate structural-slot compatibility
check.

Base and exclusions are not part of access-only coverage. Public final-to-initial
fact containment first requires base equality, then uses the
projection-aware `containsProjected` relation: corresponding concrete slots must
agree, abstraction covers descendants, and a missing structural slot is compatible
with a retained structural slot because either side may be the projection of the
same longer Tree path. This symmetric slot compatibility is intentionally broader
than `covers`; it is required by trace entry matching and is not storage subsumption.
Exclusions do not change that query. Public **initial
fact** `contains` projects Tree's exact `AccessPath.contains`: base remains
exact, while access equality widens to a zero-residual prefix match and
exclusions are ignored. These widenings are required because distinct Tree paths
and their path-local exclusion state may collapse to one canonical BaseOnly
access. Storage subsumption that needs broader directional coverage still calls
`covers` explicitly.

### 6.3 Symmetric overlap

```text
mayOverlap(a, b) iff Paths(a) ∩ Paths(b) ≠ ∅
```

Overlap is reflexive and symmetric, but need not be transitive. It is used only
for candidate indexing and never as containment. Candidate indexes may return a
superset of overlapping values, provided an authoritative relation is applied
afterward.

For equal semantic accessor `X`, two accesses overlap only when their
value-accessor states are equal.

The test-reference `canonicalJoin` returns the minimal fact set covering both denotations. If its
operands have the same prefix and semantic accessor but different
value-accessor states, the result contains both operands. A join must not
discard either path or change its wrapper state. If prefixes or semantic
accessors differ, the ordinary earliest-difference abstraction rule applies and
may produce one widened access.

The symmetric “missing field is compatible” predicate implements only
`containsProjected`; it must not implement `covers`.

## 7. Residuals, delta, and split-delta

`residual(pattern, fact)` returns the canonical suffix deltas needed to
reconstruct the paths of `fact` matched by `pattern`. It is defined by logical
graph quotient, not AP-slot cases.

For every returned delta `D`:

```text
Paths(fact matched by pattern) ⊆ Paths(graft(pattern, D))
```

The result is empty exactly when there is no match. It contains the empty delta
when the match includes identity. It may contain both empty and nonempty deltas,
as Tree final delta does for a node having abstract acceptance plus concrete
children.

Residuals preserve the value-accessor state of every unmatched terminal path. A
wrapper residual is `(X, Value)` before its wrapper is consumed and
`(X, Normal)` after it is consumed. When a collection contains both paths, each
is processed independently. Residual computation must not merge them merely
because they share the same compact suffix accessor.

### 7.1 Final `delta`

`final.delta(initial)` first requires equal bases. It computes the quotient of
the final logical graph by the initial linear pattern, applies the initial
exclusions to the residual's logical first branches, and projects every
surviving Tree delta.

If the residual starts at a compact semantic terminal, exclusions are applied
to that fact's root path before the delta is returned. Excluding `X` removes an
`Normal` fact; excluding `W(X)` removes a `Value` fact. A collection retains
the other fact independently.

### 7.2 Initial `splitDelta`

`initial.splitDelta(finalPattern)` first requires equal bases. It finds the
longest Tree-valid matched initial prefix and returns `(matchedInitial, delta)`
pairs whose concat covers the original initial. Exclusions on the final pattern
filter the first logical branches of the delta. No behavior may depend on a
hand-written pair of abstraction slots.

Matched initial accesses and returned deltas retain value-accessor state. In
particular, a split of `W(X) X $` cannot return a direct-root delta until the
wrapper belongs to the matched prefix.

### 7.3 Delta concat

Initial delta concat is logical path concatenation followed by canonicalization.
Empty is a two-sided identity. Concat is associative after canonicalization.
Final deltas are grafted through final-fact concat.

Composition copies the semantic terminal and value-accessor state from the operand that
contributes that terminal. Grafting or appending a wrapped suffix stays wrapped;
an unwrapped suffix stays unwrapped. When alternative operands with the same semantic
accessor are joined, concat delegates to `canonicalJoin`, which returns both
facts. Concat itself never changes `Normal` to `Value` merely because the
wrapper is representationally compact.

## 8. Exclusions and clear

An exclusion set filters outgoing **logical branches at the point where the
interface applies it**:

- `Empty` allows all branches;
- `Concrete(E)` removes branches whose concrete logical edge is in `E`;
- excluding `TypeInfoGroupAccessor` excludes every type-info group branch;
- excluding a concrete `TypeInfoAccessor` excludes that type branch only;
- `Universe` removes all branches and is legal only at interfaces that explicitly
  accept it; otherwise it is rejected as an invariant violation.

At a root compact semantic terminal, an exclusion may remove the zero-length
terminal branch, but the same terminal remains reachable after the implicit Any
loop. Exact subtraction is not representable, so BaseOnly retains the compact
cover. All delta, split, abstraction, side-effect, and storage code follows this
same conservative rule.

`clearAccessor(a)` subtracts every represented root branch labeled `a`. If exact
subtraction is representable, it is returned. If all paths are removed, it
returns `null`. If subtraction is not representable, the operation returns the
least canonical **overapproximation of the surviving paths**. Such a widening
may retain a cleared path as a false positive, but it must never remove an
unrelated surviving Tree path. Clearing `AnyAccessor` removes the Any branch
itself, not every concrete structural branch.

For a root compact semantic terminal, clearing a terminal label leaves the
compact state unchanged: the zero-length branch is removed, while the same
terminal remains reachable after the implicit Any loop. This is the least
representable cover of the survivors.

## 9. Type filtering

`FactApFilter` traverses every edge of the logical graph, including implicit
group/type/final steps and the implicit Any loop. Compatibility filtering follows Tree's
different rule: it consults an accessor only when that edge's child has direct
abstract acceptance. Ancestor edges that merely lead eventually to an abstract
descendant, and wholly concrete paths, are retained without consulting the
compatibility checker. The filters are applied per fact as in Tree. If
BaseOnly merges accepted and rejected paths, it keeps a sound projection of the
accepted branches; it must not reject the whole fact merely because one
represented branch is rejected.

For a semantic suffix, `FactApFilter` evaluates the one complete path selected
by its value-accessor state: `X $` for `Normal` or `W(X) X $` for `Value`.
It returns the same state when that path survives and `null` otherwise. A set
containing both paths invokes the filter independently for each fact.

Tree's `FactCompatibilityFilter` is narrower than `FactApFilter`: it checks only
an edge whose surviving child is abstract, and removes that child's abstract
acceptance when the edge is incompatible. It never rejects an exact path merely
because one of its concrete accessors is incompatible. In a canonical BaseOnly
fact, only the last committed accessor immediately before the single abstract
position is therefore checked; a root abstraction has no such concrete edge.

`FinalFactAp.concat(typeChecker, delta)` performs the same branch-wise check
during graft. `InitialFactAp.compatibilityFilter` is built from the logical
accessor sequence/graph, not the packed slots.

## 10. Abstraction lifecycle and rebasing

- `mostAbstractInitialAp(base)` is the projection of Tree's null initial access.
- `mostAbstractFinalAp(base)` is the projection of Tree's abstract root.
- `abstractOnly()` preserves an existing static- or field-position abstraction.
  Other facts become suffix-position abstract. This is the restored historical
  BaseOnly behavior; a single precise representation of Tree's abstract root is
  still unspecified.
- `removeAbstraction()` suppresses the current abstract acceptance for the duration
  of one flow-function step. A suffix-position abstraction, including the
  most-abstract final fact, becomes the transient `COLLAPSED` state. Field-position
  abstraction is projected to the later suffix abstraction when the compact
  domain cannot express a terminating concrete prefix. Suffix abstraction after
  a concrete prefix also becomes the transient `COLLAPSED` state.
- `rebase(newBase)` changes the base and completes that operational lifecycle by
  restoring `COLLAPSED` to suffix abstraction. For stable facts it changes
  only the base.
- `exclude` and `replaceExclusions` change only exclusions.

Initial-fact abstraction constructs the same refinement ladder as Tree after
projection. It uses `FactTypeChecker` and `AnyAccessorUnrollStrategy`, emits no
mixed concrete-initial/abstract-final identity edge, and deduplicates canonical
logical pairs. Its behavior is specified by Tree projection rather than by a
fixed three-slot case table.

## 11. Fact and manager factories

Every factory validates canonical form. All BaseOnly values in one analysis are
assumed to use the same manager/interner.

- `createFinalAp(base, exclusions)` creates the exact `$` final fact.
- `createFinalInitialAp(base, exclusions)` creates the exact `$` initial fact.
- facts cannot wrap the internal empty access;
- deltas may wrap empty only through the dedicated empty-delta singleton;
- equality and hashing use base, packed access, and exclusions only; manager
  identity is intentionally absent under the single-manager invariant.

## 12. Serialization and diagnostics

The serialized payload encodes the logical state:

- base and exclusions;
- optional static and structural accessor identities;
- terminal kind and logical semantic accessor identities;
- value-accessor state (`Normal` or `Value`);
- abstraction kind/position.

It does not encode `size` followed by a differently-sized iterator. Every valid
canonical fact round-trips to exact canonical equality. Invalid, unknown, empty
fact, out-of-range, and noncanonical states fail predictably.

The codec writes the three tagged logical slots followed by one value-accessor-state
byte. It has no BaseOnly magic, header, or version field. Accessor identities are
resolved through the serialization context and the current 23-bit suffix range
is enforced rather than truncated.

Rendering is unambiguous and representation-independent. It distinguishes
abstract positions, implicit Any, concrete terminal kinds, value-accessor state,
and every retained prefix. `Normal` and `Value` must render distinctly.
Rendering and parsing are diagnostic only and are never used to infer semantics.

## 13. Required shared primitives

The target production architecture has exactly one implementation of each
decision below. The operation ledger identifies the decisions that have not yet
been consolidated; declaring the primitive here is a requirement, not evidence
that delegation is already complete.

```text
canonicalize       logical sequence/graph -> canonical access set
canonicalJoin      two accesses -> minimal covering access set
logicalGraph       canonical access -> logical graph/view
terminalPath       semantic accessor x value-accessor state -> one path
consume            access x accessor -> residual access?
covers             directional language inclusion
containsProjected  projected final-to-initial trace/fact compatibility
mayOverlap         symmetric nonempty intersection
residual           pattern x fact -> delta set
graft              prefix x delta x optional type checker -> access set
exclusionAllows    logical branch x exclusion -> boolean
removeBranches     logical graph x predicate -> canonical graph set
```

Facts and deltas may wrap these results but must not reimplement their decisions.

## 14. Algebraic laws

All laws apply to valid canonical states from the analysis's single manager.

1. `canonicalize(canonicalize(A)) == canonicalize(A)`.
2. Projection is sound and monotone under Tree graph inclusion.
3. Metamorphic construction routes (`build`, repeated prepend, graft) have the
   same canonical projection when they describe the same logical graph.
4. `startsWith(A,a) == (consume(A,a) != null)`.
5. `readAccessor` is `consume` with base/exclusions preserved.
6. `getStartAccessors` is exactly the logical root-edge set, including Any.
7. `getAllAccessors` is the logical transitive concrete-accessor set, excluding
   Any.
8. `covers` is reflexive and transitive.
9. `mayOverlap` is reflexive and symmetric.
10. Equality implies mutual coverage; overlap implies neither equality nor
    coverage.
11. `residual(P,F)` is empty iff `P` cannot match `F`.
12. Every residual reconstructs a cover of its matched fact through `graft`.
13. Empty delta is a two-sided concat identity.
14. Delta concat is associative after canonicalization.
15. Prepend and consume form a left inverse whenever Tree prepend is exact.
16. Clear never removes an unrelated Tree survivor; when exact subtraction is
    unrepresentable its result is the least canonical cover of the survivors.
17. Exclusion filtering is monotone: adding exclusions cannot add paths.
18. Type filtering never removes a Tree-compatible path.
19. Rebase changes only base.
20. Serialization round-trips every valid stable state and rejects the
    transient collapsed state.
21. `Normal` and `Value` are distinct states. Joining them returns two facts;
    neither state covers or overlaps the other.
22. Reading a wrapper from `Value` produces `Normal`; reading the semantic
    accessor succeeds only from `Normal`.
23. Clear, exclusion, and filtering preserve a cover of every surviving
    terminal alternative; implicit-Any subtraction may conservatively retain
    the original compact state.
24. Residual and concat preserve value-accessor state; an explicit join retains
    differing states as separate facts.

Release verdict (1) requires a bounded exhaustive test and a Tree differential
counterpart for each applicable law. The operation ledger is authoritative for
current coverage; a behavior example is not a substitute for these laws.
