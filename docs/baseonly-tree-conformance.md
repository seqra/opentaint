# BaseOnly conformance to Tree

Status: **normative** for the BaseOnly release mitigation.

This document defines how every BaseOnly access-domain operation is compared
with Tree. The domain itself is defined in
[`baseonly-access-domain-spec.md`](baseonly-access-domain-spec.md).

## 1. Comparison model

The release target is a small, independent logical-graph reference model that
does not call BaseOnly production operations to compute expected values. The
current differential suite is bounded and uses Tree values plus observable
BaseOnly reads; it is useful regression evidence, but it is not yet that
independent projector. The operation ledger records this open evidence gate.

For a Tree value `T`, `project(T)` is the minimal canonical BaseOnly antichain
whose union covers every Tree path. A Tree may project to multiple BaseOnly
values when its branches have incompatible static or semantic terminals; forcing
those branches into one packed value is not permitted to lose either branch.
The test-reference `canonicalJoin` therefore returns a fact set. It may return one widened access
for an ordinary retained-component difference, but it returns two accesses when
the only difference is value-accessor state.

Results are compared by denotation, not packed equality:

```text
treeCovered(treeResults, baseResults) :=
    ⋃ Paths(treeResults) ⊆ ⋃ Paths(baseResults)
```

The default differential assertion is `treeCovered`. Exact equality is required
only where the table below says **exact**. BaseOnly-only paths are permitted only
when they follow from the documented projection/widening rule.

Every differential fixture uses the same:

- base and exclusions;
- accessor identities;
- field-sensitivity mode;
- `AnyAccessorUnrollStrategy`;
- `FactTypeChecker` outcome.

Base mismatch and type/exclusion rejection are tested independently so an
intentional primitive drop cannot hide access-path loss.

## 2. Tree behavior that BaseOnly inherits

The following Tree behaviors are interface contracts:

- `AccessTree.getStartAccessors()` returns the root edge labels and therefore
  includes `AnyAccessor` when the root has an Any edge.
- `AccessTree.getAllAccessors()` calls `collectAccessorsTo`, which deliberately
  ignores `AnyAccessor` while recursively collecting concrete accessors and `$`.
- Tree `startsWithAccessor` and `readAccessor` query the same logical edge;
  successful start implies a non-null read.
- Tree initial access paths are linear; Tree final access trees may branch.
- Tree final `delta` checks the base, consumes the initial path, applies initial
  exclusions to the remainder, and may return both empty and nonempty deltas.
- Tree final concat grafts at abstract leaves and applies the supplied type
  checker.
- Tree initial `splitDelta` finds a matched prefix and a remainder; concat
  reconstructs it.
- Tree `clearAccessor` subtracts a root branch rather than reading/promoting it.
- Tree filters operate branch-wise on the logical tree.
- Tree rebase changes only the base.
- Tree exact equality is not containment and is not overlap.

BaseOnly never stores an Any field slot. An explicit or forgotten Tree
structural edge projects to the implicit structural self-loop of a semantic or
suffix-abstract state. The accessor views remain asymmetric: start accessors
expose Any, while all accessors do not.

Tree distinguishes the semantic paths `M $` and `T $` from paths having a
category wrapper, `V M $` and `G T $`. BaseOnly preserves that distinction with
the value-accessor state:

```text
Normal = the normal suffix path
Value  = the value suffix path through ValueAccessor
```

A Tree union containing both paths projects to two BaseOnly facts. There is no
packed state representing their union.

## 3. Operation conformance matrix

“Projected Tree result” below means the independent `project` operation from the
reference model.

| Operation | Tree contract | Permitted BaseOnly widening | Forbidden BaseOnly behavior | Differential property |
|---|---|---|---|---|
| codec pack/unpack | Tree has no packed equivalent | none; codec is representation-only | accept invalid category/order/range or change logical state | logical state before/after codec is exact |
| validate | Tree values are structurally valid | none | allow a packed state with no Tree-relative denotation | every accepted state builds the reference graph; every generated invalid state is rejected |
| `project`/`canonicalize` | preserves the Tree graph | discard later structural precision per the outermost rule | omit a Tree path or replace the outermost structural with an inner one | `Paths(T) ⊆ Paths(project(T))`; idempotent |
| `build` | repeated Tree construction in sequence order | canonical projection only | reorder malformed paths, conflate `Normal` with `Value`, silently lose a path | ordinary input projects to `Normal`; a `ValueAccessor`-prefixed taint mark projects to `Value`; malformed wrapper pairs are rejected |
| `abstractAt` | construct prefix ending at abstract node | canonical prefix projection | unchecked position; retain components after abstract node | exact projected Tree graph |
| `prependAccessor` | `AccessNode.addParent` / linear `AccessNode` parent | field truncation to an absent slot with implicit Any | replace an outer field with an inner field; return less than Tree | projected Tree prepend is covered |
| `consume` / `readAccessor` | `getChild` (final) or exact head read (initial) | universal reads enabled by implicit Any and by a retained field's projected structural tail | fail a Tree-successful read; allow a `Normal` terminal to read `ValueAccessor` or a `Value` root to skip it | every Tree read result projects into BaseOnly read results; reading `ValueAccessor` returns a `Normal` residual |
| `startsWithAccessor` | Tree edge membership (`contains` for final; exact head for initial) | true for an implicit-Any-covered structural read | false when corresponding BaseOnly read succeeds, or true with null read | exact agreement with BaseOnly `consume`; Tree true implies BaseOnly true after projection |
| `getStartAccessors` | root edge labels, including Any | implicit Any only | omit Tree/projected Any; enumerate every possible concrete field instead of Any | `Normal -> {Any,X}`, `Value -> {Any,W(X)}` after the common prefix |
| `getAllAccessors` | recursive concrete collection; **Any excluded** | concrete accessors retained by logical expansion | include Any; omit the wrapper for `Value`; invent one for `Normal`; omit semantic/final | exact set of projected logical concrete labels for each state |
| head/first | first logical concrete/edge accessor | absence when only virtual Any/abstract remains | expose type before group for `Value`, or group before type for `Normal` | exact projected logical view for each fact; collections iterate each fact |
| `size` | final Tree `countNodes`; initial Tree linear node count | BaseOnly intentionally uses a different bounded retention metric | exceed three or count virtual/wrapper nodes inconsistently | exact occupied concrete-slot count in `[0,3]` |
| `depth` | final Tree `maxDepth`; initial Tree path length | BaseOnly intentionally aliases its bounded packed size and omits Tree's Any-cycle sentinel | use it as a semantic path length | exact equality with BaseOnly packed size |
| `isAbstract` | current logical node has abstract acceptance | none beyond projected abstraction | report a later abstraction before its concrete prefix is consumed; call every empty delta concrete | exact against projected current node |
| `clearAccessor` | remove matching root branch | least canonical cover of surviving branches; an implicit Any continuation can require retaining the compact state | remove an unrelated surviving branch | every projected Tree survivor is covered; 39 mutation traces pin the root-terminal case |
| exact equality | equal logical initial/final shape under Tree's method | none | use overlap/compatibility; ignore base at fact level | exact on projected canonical graph/base/exclusions as applicable |
| access `covers` | Tree final `AccessNode.contains` intent, generalized for canonical storage keys | projected directional language inclusion | symmetric missing-field compatibility; claim `Normal` covers `Value` or vice versa | Tree containment true implies BaseOnly coverage; state equality and coverage laws hold |
| final fact `contains(initial)` | Tree `AccessNode.contains` after equal base check; exclusions ignored | projection-aware missing-structural compatibility; one manager is assumed | cross-base true; using this symmetric relation as storage subsumption | every Tree-true pair remains true after projection; split-delta is aligned with the same projected match |
| initial fact `contains(initial)` | Tree `AccessPath.contains` is exact fact equality | zero-residual access-prefix match after lossy canonical projection; base remains exact and path-local exclusions are ignored; one manager is assumed | use arbitrary overlap or nonempty residual; cross-base match | every projected Tree-equal pair matches; widening is limited to zero-residual access and exclusion erasure |
| `mayOverlap` | candidate relation inferred from nonempty Tree intersection | false positives allowed in index only | false negative candidate; use as final containment | every Tree-overlapping pair is a candidate; symmetry law |
| `delta` (final) | consume initial path, check `$`, filter remainder exclusions; empty/nonempty branches | project residual trees, possibly returning multiple facts | skip base check; change value-accessor state; drop one fact because another state shares its suffix | every Tree delta is covered with state reflecting the unmatched path |
| final `concat` | `concatToLeafAbstractNodes(typeChecker, delta)` | canonical projection after graft | ignore checker; recreate primitive/incompatible path; change value-accessor state without a different input fact | every Tree concat result is covered; the terminal-contributing operand's state is preserved |
| `splitDelta` (initial) | match against final tree, filter remainder, return matched prefix + delta | projected matched prefix/residual | AP-slot special case that loses reconstructability; lose wrapper position or value-accessor state; ignore base/exclusion | every Tree pair has a covering BaseOnly pair and concat covers original initial |
| initial/delta `concat` | linear node concat | canonical projection | non-associative result after canonicalization; change value-accessor state; cross-kind slot rejection not made by Tree | projected Tree concat is covered; identity/associativity and state-preservation laws |
| exclusions | Tree filters exact outgoing logical branches | projection of surviving branches; implicit Any subtraction may retain the compact cover | treat `Universe` as Empty; drop a surviving branch; mishandle group/type | projected Tree filtered graph is covered |
| compatibility filter | Tree checks exactly an edge whose child has direct abstract acceptance; ancestors and wholly concrete paths bypass the checker | compatibility cover when paths merged | check every path edge or every ancestor of an abstract leaf; omit the direct predecessor | every Tree concrete path and every Tree-compatible abstract path survives projected filter |
| final fact filter | Tree `filterAccessNode`, branch-wise | retain a sound projection per fact | reuse filter state across facts or change their value-accessor states | evaluate each complete path independently and return exactly the surviving facts |
| `abstractOnly` | Tree abstract root with same base/exclusions | BaseOnly currently preserves an existing static/field abstraction position | silently collapse distinct positions before a root representation is specified | restored slot-preserving behavior is pinned; Tree-root equivalence remains open |
| `removeAbstraction` | remove abstract acceptance, keep concrete branches; null if empty | later-AP widening or an explicit transient collapsed suffix until rebase | persist the transient marker; lose a concrete prefix | projected Tree survivors remain covered through the flow-function lifecycle |
| `rebase` | base substitution; in the remove/rebase flow lifecycle it restores suppressed abstract acceptance | transient collapsed restoration only | alter any stable access or exclusions | stable access/exclusions exact; transient access restored; base replaced |
| `exclude` / `replaceExclusions` | exclusion-set update only | none | alter access/base | access/base exact; exclusion algebra exact |
| most-abstract factories | Tree null initial / abstract-root final | their canonical projections | choose a state that does not cover reference | exact projected logical graph |
| final factories | Tree exact `$` initial/final | none | manufacture empty/open/abstract state | exact projected `$` graph |
| initial-fact abstraction | Tree refinement ladder, Any unroll, type checks | deduplicate/merge projected pairs | ignore checker/unroll, omit Tree pair, emit mixed identity | every Tree pair is covered; no mixed concrete/abstract identity |
| render | Tree printer exposes graph distinctions | compact notation | hide AP position, virtual Any, or value-accessor state so distinct states print identically | generated canonical states have unambiguous renderings |
| serialize | Tree serializer round-trips its logical value | compact BaseOnly payload | lose value-accessor state; truncate a suffix outside the 23-bit range; add a BaseOnly magic/header/version | every canonical value round-trips exactly |

## 4. Required combined scenarios

Single-operation tests are insufficient. The differential suite must include
these compositions because storage and trace resolution consume them as units.

### 4.1 Prepend, start, read

For every generated Tree value `T` and accessor `a` for which prepend succeeds:

```text
B = project(prependTree(T, a))
assert a in getStartAccessors(B) or a is represented through a documented Any edge
assert startsWith(B, a)
assert read(B, a) covers project(T)
```

Include two distinct fields and verify the first/outermost field remains the
retained concrete field.

### 4.2 Delta and concat

For every Tree final `F`, initial `I`, and Tree delta `D ∈ F.delta(I)`:

```text
BD ∈ projectDelta(D)
BF ∈ project(F)
BI ∈ project(I)
concat(BI, BD) covers the matched initial reconstruction
concat(BF-prefix, BD, checker) covers Tree concat when non-null
```

Include identity plus nonempty residual, abstraction at each position, a field
followed by a semantic mark, type group/type, exclusions, and primitive rejection.

### 4.3 Split-delta and concat

For every pair returned by Tree `I.splitDelta(P)`:

```text
(matched, delta) = projected BaseOnly pair
concat(matched, delta) covers project(I)
```

Exercise `Tree initial = f.g.M.$` against patterns abstract at root, after `f`,
and before `M`. This scenario forbids special-case slot alignment that cannot
reconstruct the original path.

### 4.4 Clear, start, all-accessors

For every root accessor `a`:

- if Tree clear removes the only branch, BaseOnly returns null;
- otherwise every Tree survivor is covered;
- `a` is absent from the resulting start set when exactly removable;
- an Any root edge is present in start accessors before clear but absent from all
  accessors both before and after clear.

### 4.5 Filter and concat

Graft a delta that contains one compatible reference branch and one incompatible
or primitive branch. BaseOnly keeps a cover of the compatible Tree branch and
does not recreate the rejected branch as an exact fact.

### 4.6 Serialize and operate

Round-trip every canonical operand, then repeat prepend/read, delta/concat,
clear, coverage, and filtering. Results before and after serialization are exact
canonical equals.

### 4.7 Rebase and abstraction lifecycle

For each abstraction position:

```text
!A.isCollapsed implies rebase(A).access == A.access
removeAbstraction(abstractOnly(A)).rebase(A.base) == abstractOnly(A)
```

For generated projected trees with both abstract and concrete branches,
`removeAbstraction` retains a cover of every concrete Tree branch. Because the
compact representation cannot encode a concrete prefix with no accepting
terminal, it may move abstraction to the suffix or return the transient
collapsed state. `rebase` completes that lifecycle; no storage
or serializer accepts the transient state.

### 4.8 Compact value-accessor state

Run the same operation chain for `M $`, `V M $`, `T $`, `G T $`, and for the
two-fact unions of each pair:

```text
build -> getStart/getAll -> read -> clear -> exclude -> filter
      -> delta/splitDelta -> concat -> serialize -> repeat
```

For each semantic accessor `X`, assert:

- exact construction yields `Normal` for `X $` and `Value` for `W(X) X $`;
- joining the two yields two facts, independent of insertion order;
- reading `W(X)` from `Value` yields `Normal`;
- clearing or excluding a zero-length terminal root retains a sound compact
  cover when the same terminal survives behind implicit Any;
- residual and concat preserve the surviving state;
- serialization preserves both states exactly without a BaseOnly header.

## 5. Differential generator

The bounded generator must include:

- two bases;
- two statics;
- two fields plus element;
- Any with an unroll strategy that both accepts and rejects selected fields; BaseOnly's
  implicit universal Any must remain a superset in both cases;
- two taint marks, Value, Final;
- TypeInfoGroup plus two types;
- `Normal` and `Value` states, plus their two-fact union, for every
  generated taint mark and type;
- Tree paths to depth at least five;
- Tree branching at root and below a field;
- abstract acceptance at root and internal nodes;
- empty, concrete, and Universe exclusions where the API permits them;
- field-sensitive and field-insensitive BaseOnly managers;
- always-compatible and selectively-incompatible type checkers.

Generate valid Tree values directly. Generate invalid BaseOnly codec states
separately; do not use invalid values as differential operands.

For each operation, compare the union of result denotations. When BaseOnly emits
extra paths, assert that each extra follows from one named widening rule:

1. later structural truncation;
2. field-insensitive structural erasure;
3. implicit structural Any before a semantic or suffix-abstract state;
4. branch join into a canonical cover;
5. separate facts retained when joining `Normal` and `Value` states.

No catch-all “BaseOnly is approximate” waiver is permitted.

## 6. Release verdict for an operation

An operation is conformant only when all are true:

1. its production code delegates to the shared primitive named in the access
   spec;
2. its algebraic laws pass bounded exhaustive tests;
3. its differential property and relevant combined scenarios pass against Tree;
4. all BaseOnly-only results are attributed to a named widening rule;
5. no retained dataflow regression contradicts the result.

Until then its release verdict is not “perfect design and implementation,” even
if example and golden tests pass.
