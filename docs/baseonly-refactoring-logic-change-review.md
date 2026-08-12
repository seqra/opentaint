# BaseOnly refactoring logic-change review

## Scope

This review covers the production-code diff from `fef4d51c7` to `52805bebe`.
Tests and specification documents are used as evidence but are not themselves
counted as runtime logic changes.

## `abstractOnly()` is not justified as written

- Related operations: `BaseOnlyFinalFactAp#abstractOnly`,
  `BaseOnlyApManager#mostAbstractFinalAp`, `AccessTree#abstractOnly`.

The change was intended to mirror Tree, where `abstractOnly()` returns the
abstract root, and to make every result equal to `mostAbstractFinalAp()`.

However, the old and new BaseOnly values are observably different:

- Old:
  - `(ABSTRACT, -, -)` stayed static-position abstract.
  - `(-, ABSTRACT, -)` stayed field-position abstract.
  - Concrete or suffix-abstract facts became `(-, -, ABSTRACT)`.
- New: every fact becomes `(-, -, ABSTRACT)`.

BaseOnly operations distinguish those abstraction positions. For example, the
current tests assert that suffix abstraction accepts structural reads through
implicit Any, while static and field abstraction do not. Therefore this is not
merely canonicalization.

Verdict: reject this change as-is. The intended "Tree abstract root" needs a
precise BaseOnly representation first; reverting to the old implementation also
would not completely solve that specification problem.

Resolution: reverted to the pre-refactoring slot-preserving implementation.
The representation question remains open and is not hidden by claiming that all
three abstraction positions are equivalent.

## Access-path logic changes

### 1. Value-wrapper state

- Related operations: `BaseOnlyAccessKt#packBaseOnlyAccess`,
  `BaseOnlyAccessOps#build`, `BaseOnlyAccessOps#prepend`,
  `BaseOnlyAccessOps#read`.

- Old behavior: `M.$` and `Value.M.$`, or `T.$` and `TypeGroup.T.$`, collapsed
  to the same packed value.
- New behavior: `Normal` and `Value` are distinct states stored in one suffix
  bit.
- Motivation: prevent loss of primitive-value/type-wrapper position during
  reads, residuals, storage, and trace resolution.
- Verdict: keep.

### 2. Suffix range

- Related operations: `BaseOnlyAccessKt#packBaseOnlyAccess`,
  `BaseOnlyAccessKt#rawBaseOnlySuffixSlot`,
  `BaseOnlyAccessKt#packBaseOnlyAccessFromRawSuffix`.

- Old behavior: the suffix used all 24 bits.
- New behavior: the suffix index uses 23 bits; one bit stores wrapper state.
- Motivation: support the value-wrapper state without enlarging the packed
  `Long`.
- Cost: the maximum suffix index is halved.
- Verdict: keep only together with change 1.

### 3. Any is forbidden in the field slot

- Related operation: `BaseOnlyAccessKt#packBaseOnlyAccess`.

- Old behavior: raw packing could store `AnyAccessor` as a field.
- New behavior: packing rejects it; Any remains implicit.
- Motivation: enforce the intended BaseOnly representation.
- Verdict: keep.

### 4. Canonical-value validation

- Related operations: `BaseOnlyAccessOps#requireCanonical`,
  `BaseOnlyFinalFactAp#<init>`, `BaseOnlyInitialFactAp#<init>`.

- Old behavior: fact constructors checked only that the access was nonempty.
- New behavior: constructors validate slot kinds, abstraction placement,
  wrapper state, terminal structure, and collapsed-state usage.
- Motivation: reject malformed packed values at their creation boundary.
- Verdict: keep.

### 5. Build grammar

- Related operations: `BaseOnlyAccessOps#build`,
  `BaseOnlyAccessOps#validateBuildGrammar`.

- Old behavior: malformed ordering was silently projected; later static
  accessors overwrote earlier ones.
- New behavior: invalid order, repeated statics, accessors after a terminal,
  and incomplete wrappers are rejected.
- Motivation: prevent construction history from silently changing meaning.
- Verdict: keep.

### 6. Structural projection

- Related operation: `BaseOnlyAccessOps#build`.

- Old behavior: `build()` retained the last/innermost field.
- New behavior: it retains the first/outermost field.
- Motivation: the retained outer field plus implicit Any covers the discarded
  inner path; retaining only the inner field can lose the outer prefix.
- Verdict: keep.

### 7. Size and depth

- Related operations: `BaseOnlyFinalFactAp#getSize`,
  `BaseOnlyFinalFactAp#getDepth`, `BaseOnlyInitialFactAp#getSize`,
  `BaseOnlyInitialFactAp#getDepth`, `BaseOnlyAccessKt#getSize`.

- Old behavior: counted occupied packed slots.
- New behavior: counts enumerated logical accessors; final facts additionally
  count abstraction.
- Intended motivation: approximate Tree node/path metrics more closely.
- Problem: taint `ValueAccessor` is still omitted from `size`, while the
  analogous type-group wrapper is counted. `size` and `depth` therefore remain
  inconsistent across equivalent wrapper forms.
- Verdict: reject. We should keep size <= 3. It is important.
- Resolution: reverted. `size` and `depth` count occupied concrete packed slots,
  so both remain bounded by three.

### 8. Start/all accessor views

- Related operations: `BaseOnlyAccessViewKt#startAccessors`,
  `BaseOnlyAccessViewKt#allAccessors`.

- Old behavior: used a single packed head; type suffixes always exposed
  `TypeInfoGroup`; suffix abstraction did not expose implicit Any consistently.
- New behavior: start accessors include implicit Any where applicable and
  respect wrapper state; all accessors exclude implicit Any.
- Motivation: match Tree's `getStartAccessors`/`getAllAccessors` distinction.
- Verdict: keep.

### 9. Prepend

- Related operation: `BaseOnlyAccessOps#prepend`.

- Old behavior: type group was ignored, `ValueAccessor` could replace the
  semantic suffix, and a second static silently replaced the first.
- New behavior: wrappers set wrapper state, a second static is rejected, Any is
  a no-op, and a prepended structural accessor becomes the retained outer field.
- Motivation: preserve path order and wrapper identity.
- Verdict: keep.

### 10. Read and `startsWith`

- Related operations: `BaseOnlyAccessOps#read`,
  `BaseOnlyAccessOps#startsWith`, `BaseOnlyAccessOps#headRead`.

- Old behavior: reading Any consumed a concrete field; a direct semantic
  accessor could consume a wrapped suffix; type group was effectively an
  idempotent read.
- New behavior: concrete fields require exact reads, implicit Any loops only
  after the concrete slot is absent, and wrapped terminals require consuming
  their wrapper first.
- Motivation: model logical edges rather than packed-slot compatibility.
- Verdict: keep.

### 11. Clear

- Related operation: `BaseOnlyAccessOps#clear`.

- Old behavior: Any could clear a concrete field, and clearing a root semantic
  terminal removed the entire fact.
- New behavior: clearing is exact; a root semantic/suffix-abstract fact is
  retained when its implicit Any continuation still represents surviving paths.
- Motivation: avoid underapproximating branch subtraction that BaseOnly cannot
  express exactly.
- Verdict: rewrite. IF we have static/field -> do nothing, if field and static are both -1 -> clear entire fact. The reason is that in the latter case startsWith([any]) returns true
- Resolution: rejected after end-to-end validation. With path sampling enabled,
  this rule made 39 previously reachable mutation traces fail; every failure
  disappeared when the denotational clear was restored. A root semantic fact's
  implicit Any loop represents surviving paths after one direct branch is
  cleared, so deleting the entire compact fact is an underapproximation.

### 12. General append

- Related operations: `BaseOnlyAccessOps#append`,
  `BaseOnlyAccessOps#combineTerminal`.

- Old behavior: suffix structural slots could replace the prefix field, and
  composition after a concrete terminal was handled through slot merging.
- New behavior: empty is identity, a concrete terminal stops composition,
  abstract prefixes use grafting, and the outer prefix field is retained.
- Motivation: follow logical path concatenation order.
- Verdict: keep.

### 13. Final graft/concat

- Related operations: `BaseOnlyAccessOps#appendFinal`,
  `BaseOnlyAccessOps#graftAtAbstraction`.

- Old behavior: rejected suffixes whose first accessor was not in an expected
  packed slot.
- New behavior: rejects only a structurally impossible second static; otherwise
  it absorbs unrepresentable structural steps and preserves semantic terminals.
- Motivation: representation loss should cause widening rather than a false
  negative.
- Verdict: keep as intentional overapproximation.

### 14. Coverage versus overlap

- Related operations: `BaseOnlyAccessOps#covers`,
  `BaseOnlyAccessOps#mayOverlap`, `BaseOnlyAccessOps#containsAccess`,
  `BaseOnlyAccessOps#equalToInitial`.

- Old behavior: the same broad containment-style checks were reused for prefix
  matching and storage lookup.
- New behavior: separates directional `covers`, symmetric `mayOverlap`,
  projected final containment, and exact/zero-residual initial matching.
- Motivation: storage candidacy is not the same operation as subsumption or
  final-to-initial containment.
- Verdict: keep.

### 15. Wrapper-aware relations

- Related operations: `BaseOnlyAccessOps#covers`,
  `BaseOnlyAccessOps#mayOverlap`, `BaseOnlyAccessOps#containsAccess`,
  `BaseOnlyAccessOps#equalToInitial`.

- Old behavior: wrapper position was erased.
- New behavior: containment, equality, coverage, and overlap require matching
  `Normal`/`Value` state for semantic terminals.
- Motivation: direct and wrapped primitive/type facts are different paths.
- Verdict: keep.

### 16. `canonicalJoin`

- Related operation: `BaseOnlyAccessOps#canonicalJoin`.

- Old behavior: no shared join operation existed.
- New behavior: the same semantic suffix with different wrapper states returns
  two facts; other differences widen at the earliest representable position.
- Motivation: avoid inventing a third "both" state.
- Caveat: this helper currently has no production caller.
- Verdict: move to base-only test utils.
- Resolution: removed from production and retained as a test-only reference
  helper.

### 17. Prefix match and residual

- Related operations: `BaseOnlyAccessOps#matchPrefix`,
  `BaseOnlyAccessOps#splitConcreteInitial`,
  `BaseOnlyAccessOps#splitDelta`, `BaseOnlyAccessOps#dropCorePrefix`.

- Old behavior: matching required exact pre-abstraction slots.
- New behavior: a missing structural slot can cover a concrete field when the
  pattern has an implicit Any continuation; residuals preserve wrapper state.
- Motivation: keep projected root-terminal and field-terminal paths
  reconstructable.
- Verdict: keep.

### 18. Split-delta exclusion boundary

- Related operation: `BaseOnlyAccessOps#splitDelta`.

- Old behavior: exclusions were always applied to the packed residual head.
- New behavior: exclusions are not applied when field compatibility matched
  across an erased structural boundary.
- Motivation: the exclusion belongs after the known field, not at a projected
  root residual.
- Verdict: review carefully. This is a narrow semantic exception, although it
  addresses a demonstrated trace miss.

### 19. Exclusion application

- Related operations: `BaseOnlyApManager#applyExclusions`,
  `BaseOnlyFinalFactAp#delta`, `BaseOnlyAccessOps#splitDelta`.

- Old behavior: `Universe` was effectively treated like no exclusion; a
  matching packed head removed the whole suffix.
- New behavior: `Universe` removes the result, while an implicit-Any terminal
  may be retained as a sound cover.
- Motivation: implement correct exclusion algebra without dropping surviving
  projected branches.
- Verdict: keep. Use kotlin `when` to pattern match exclusions
- Resolution: retained and rewritten with exhaustive Kotlin `when` matching.

### 20. Fact filtering

- Related operations: `BaseOnlyFinalFactAp#filterFact`,
  `BaseOnlyFinalFactAp#filterAccess`,
  `BaseOnlyFinalFactAp#pathAccepted`.

- Old behavior: filters traversed packed/enumerated accessors and could
  synthesize the wrong type wrapper.
- New behavior: filters traverse the complete logical path selected by wrapper
  state.
- Motivation: filter direct and wrapped terminals independently.
- Verdict: keep.

### 21. Compatibility filtering

- Related operation: `BaseOnlyFinalFactAp#filterFact`.

- Old behavior: checked every concrete accessor in the fact.
- New behavior: concrete facts bypass compatibility checking; abstract facts
  check only the direct predecessor of abstract acceptance.
- Motivation: match Tree's abstract-child compatibility filter.
- Verdict: keep.

### 22. Final delta

- Related operations: `BaseOnlyFinalFactAp#delta`,
  `BaseOnlyAccessOps#matchPrefix`, `BaseOnlyApManager#applyExclusions`.

- Old behavior: did not check base equality and used the old head-only
  exclusion test.
- New behavior: rejects different bases, preserves wrapper state, and applies
  the new exclusion operation.
- Motivation: match the Tree delta contract.
- Verdict: keep.

### 23. Checked final concat

- Related operations: `BaseOnlyFinalFactAp#concat`,
  `BaseOnlyFinalFactAp#filterDelta`, `BaseOnlyAccessOps#appendFinal`.

- Old behavior: ignored the supplied `FactTypeChecker`.
- New behavior: filters the delta using the receiver prefix before grafting.
- Motivation: prevent incompatible or primitive flows that Tree rejects.
- Verdict: keep.

### 24. Delta abstraction status

- Related operations: `BaseOnlyNodeFinalDelta#isAbstract`,
  `BaseOnlyNodeInitialDelta#isAbstract`.

- Old behavior: only suffix-position abstraction made a delta abstract.
- New behavior: abstraction in any slot makes it abstract once no concrete
  prefix remains before it.
- Motivation: `isAbstract` describes abstract acceptance at the current logical
  node, independently of the packed slot holding that node.
- Verdict: keep.

### 25. Initial-fact abstraction

- Related operations:
  `BaseOnlyInitialFactAbstraction#addAbstractedInitialFact`,
  `BaseOnlyInitialFactAbstraction#registerNewInitialFact`,
  `BaseOnlyInitialFactAbstraction#abstractOneBranch`.

- Old behavior: refinement ignored wrapper edges and could emit direct facts
  for wrapped terminals.
- New behavior: wrapper accessors participate in refinement and exact emitted
  facts preserve wrapper state.
- Motivation: avoid merging distinct Tree paths during abstraction.
- Verdict: keep.

### 26. Serialization

- Related operations: `BaseOnlySerializer#writeFact`,
  `BaseOnlySerializer#readFact`, `BaseOnlySerializer#writeSlot`,
  `BaseOnlySerializer#readSlot`.

- Old behavior: serialized an accessor sequence plus one abstract flag, losing
  abstraction position and wrapper state.
- New behavior: serializes three tagged slots and wrapper state exactly.
- Motivation: exact round-trip of canonical BaseOnly values.
- Cost: incompatible with the old serialized format and intentionally has no
  version/header.
- Verdict: keep.

## Storage logic changes

### 27. Initial-access index identity

- Related operations: `BaseOnlyInitialAccessIndex#getOrCreate`,
  `BaseOnlyInitialAccessIndex#collectAll`,
  `BaseOnlyInitialAccessIndex#collectCandidates`.

- Old behavior: suffix index alone was the leaf key.
- New behavior: raw suffix plus wrapper state is the key.
- Motivation: prevent direct and wrapped facts from sharing storage.
- Verdict: keep.

### 28. Candidate-only indexing

- Related operations: `BaseOnlyInitialAccessIndex#collectCandidates`,
  `BaseOnlyInitialAccessIndexKt#baseOnlySummaryInitialMatches`.

- Old behavior: the index performed its own containment filtering.
- New behavior: it returns conservative candidates; callers apply
  `mayOverlap`.
- Motivation: use one authoritative semantic predicate across summaries and
  side effects.
- Verdict: keep.

### 29. F2F summary exclusion aggregation

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.MergingStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#add`.

- Old behavior: each exact final stored its own exclusions and repeated finals
  merged by union.
- New behavior: every non-identity final for one initial shares one exclusion
  intersection; identity repetitions also intersect.
- Motivation: Tree merges alternative final branches into one tree and
  intersects their exclusions.
- Verdict: keep.

### 30. F2F batch deltas

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.MergingStorage#getAndResetDelta`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#getAndResetDelta`.

- Old behavior: one batch could emit intermediate exclusion states repeatedly.
- New behavior: each edge is merged directly into persistent storage; changed
  aggregate keys are coalesced in writer-local delta state and drained after the
  batch. All finals are re-emitted when the aggregate exclusion changes.
- Motivation: emit only final batch deltas without duplicating merge semantics
  in temporary maps.
- Verdict: keep.

### 31. Identity-summary storage

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#collectAll`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#collectContainedBy`.

- Old behavior before the rewrite: a hierarchical trie suppressed concrete
  children beneath abstract entries by replacing the child value with `null`
  while retaining the map key.
- New behavior: the hierarchical trie and null tombstones are restored. It is
  adapted only where the current representation requires it: suffix leaves use
  the raw suffix slot so Normal and Value remain distinct, while abstraction
  tests use the decoded semantic accessor.
- Motivation: retain Tree-compatible same-slot subsumption without temporary
  active flags or a flat identity index.
- Verdict: reject. Motivation looks incorrect, need detailed investigation. 
- Resolution: Tree's identity trie does not suppress
  arbitrary packed-compatible facts. An abstract node suppresses only a concrete
  child in the same logical slot, and only when the node exclusion does not
  exclude that child accessor. The map key is retained with a null value, so the
  concurrent-read-safe table shape is not changed by removal. `NO_ACCESSOR`
  advances to a later packed slot and therefore is not such a child. BaseOnly
  implements exactly this rule while keeping `Normal` and `Value` suffix leaves
  distinct. Tests cover both insertion orders, excluded children, cross-slot
  records, and both suffix states.

### 32. Normalized summary aliases

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage#collectSummariesTo`,
  `MethodInitialToFinalBaseOnlyApSummariesStorageKt#normalizeSummaryInitialAccess`.

- Old behavior: aliases were written into a second mutable summary storage.
- New behavior: only primary edges are stored; normalized aliases are generated
  as read-only trace-time views.
- Motivation: aliases cannot diverge, own exclusions, or emit forward deltas.
- Verdict: rewrite. We don't need to add such edges at all. We can reconstruct them from the added ones during `collectSummariesTo`
- Resolution: implemented. Only primary summaries are stored; aliases are
  reconstructed and deduplicated in `collectSummariesTo` and never emit deltas.

### 33. Trace-mode summary query

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage#collectSummariesTo`,
  `BaseOnlyApManager#normalizedEdgesEnabled`.

- Old behavior: queried primary and normalized stores using the requested
  pattern.
- New behavior: trace mode scans all primaries, creates primary/alias views, and
  relies on downstream trace matching.
- Motivation: an alias may match even when its primary lies outside the packed
  candidate bucket.
- Cost: potentially substantial trace-resolution workload.
- Verdict: keep for correctness, but measure performance.

### 34. Summary publication

- Related operations:
  `MethodInitialToFinalBaseOnlyApSummariesStorage.MergingStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.MergingStorage#collectAll`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage.Entry#intersect`.

- Old behavior: nested mutable trie state could expose partially initialized
  leaves to concurrent readers.
- New behavior: uses append-only concurrent-read-safe indexes/sets and volatile
  complete exclusion values.
- Motivation: satisfy single-writer/multiple-reader eventual consistency.
- Verdict: postpone. Add it to the list of known concurrency issues
- Resolution: postponed. The remaining SWMR proof and stress-test gaps are
  recorded in `baseonly-storage-spec.md`; no concurrency guarantee is inferred
  for fact sets, which are single-thread-owned.

### 35. Intraprocedural F2F final aggregation

- Related operations:
  `MethodEdgesInitialToFinalBaseOnlyApSet.Storage#add`,
  `MethodEdgesInitialToFinalBaseOnlyApSet.PerStatement#add`,
  `MethodEdgesInitialToFinalBaseOnlyApSet.PerStatement.Entry#add`.

- Old behavior: exclusions were stored per exact final and filtered according
  to the initial abstraction slot.
- New behavior: all finals for one initial/statement share one unioned
  exclusion, matching Tree steady-state storage.
- Intended motivation: Tree stores one merged final tree and one exclusion
  value.
- Problem: `add()` returns only one final. If the shared exclusion changes,
  previously stored finals also change but are not re-emitted.
- Verdict: keep. We should re-emmit all finals on exclusion change
- Resolution: implemented by changing `MethodEdgesInitialToFinalApSet#add` to
  return a list of changed edges. When the shared exclusion changes, BaseOnly
  now returns every stored final with the new exclusion; a new final without an
  exclusion change still returns only that final. `MethodAnalyzerEdges#add`
  publishes the complete returned list. Tree and Cactus return their single
  merged fact, while Automata also re-emits its complete stored final set.

### 36. Removal of intraprocedural normalized alias lookup

- Related operation:
  `MethodEdgesInitialToFinalBaseOnlyApSet.Storage#filter`.

- Old behavior: exact-initial lookup had a trace-mode fallback from a suffix-AP
  initial to a field-AP key.
- New behavior: intraprocedural storage uses only exact primary keys;
  normalization exists only in summary queries.
- Motivation: normalized aliases are trace-summary views, not forward fact-set
  identities.
- Verdict: validate. Set SKIP_PATH_SAMPLING=false and rerun tests. 
- Resolution: validation failed without the fallback and passed after it was
  restored. The missing lookup broke all six identity trace fuzz cases, two
  value-transfer cases, the constructor trace-shape case, and the nested-factory
  reachability case. Intraprocedural storage still stores only primary keys; in
  trace mode, lookup maps the suffix-abstract alias back to its field-abstract
  primary.

### 37. ND edge initial exclusions

- Related operation: `MethodEdgesNDInitialToFinalBaseOnlyApSet#add`.

- Old behavior: insertion retained supplied exclusions, while exact lookup
  normalized its query to `Universe`.
- New behavior: insertion also replaces initial exclusions with `Universe`.
- Motivation: insertion and lookup use the same logical ND key.
- Verdict: keep.

### 38. Side-effect requirement batching

- Related operations: `BaseOnlySideEffectRequirementApStorage#add`,
  `BaseOnlySideEffectRequirementApStorage.RequirementStorage#mergeAdd`,
  `BaseOnlySideEffectRequirementApStorage.RequirementStorage#getAndResetDelta`.

- Old behavior: duplicate requirements in one batch were merged incrementally.
- New behavior: requirements with the same base/access are first coalesced with
  exclusion union and publish one committed delta.
- Motivation: deterministic, idempotent batch behavior.
- Verdict: reject. I didn't get the reason
- Resolution: reverted to incremental insertion and delta publication.

### 39. Side-effect requirement filtering

- Related operations: `BaseOnlySideEffectRequirementApStorage#filterTo`,
  `BaseOnlySideEffectRequirementApStorage.RequirementStorage#filterTo`.

- Old behavior: `filterTo` returned every requirement with the same base.
- New behavior: returns only accesses that `mayOverlap` the queried final fact.
- Motivation: match Tree's `filterContains` behavior and remove a large
  broadcast.
- Verdict: keep, conditional on `mayOverlap` correctness.

### 40. Fact-side-effect summary filtering

- Related operation:
  `FactSESummariesBaseOnlyStorage.SEStorage#collectSummariesTo`.

- Old behavior: used the old bidirectional-containment expression inside the
  index.
- New behavior: uses the candidate index followed by authoritative
  `mayOverlap`.
- Motivation: share the same query contract as F2F summaries and Tree
  `filterContains`.
- Verdict: keep.

### 41. ND subscription identity

- Related operations:
  `MethodBaseOnlyAccessPathSubscription.NDSub#add`,
  `MethodBaseOnlyAccessPathSubscription.NDSub#find`.

- Old behavior: the generic interner keyed initial facts by base/access and
  could conflate facts differing only by exclusions.
- New behavior: keys the exact canonical set of `InitialFactAp` values and its
  exit set.
- Motivation: preserve the full registered caller-initial identity.
- Verdict: reject. According to the spec ND edge exclusion is always Universe
- Resolution: restored the generic ND subscription storage and normalize every
  registered initial exclusion to `Universe` before interning.

### 42. Collapsed-value insertion

- Related operations: `BaseOnlyFinalFactList#add`,
  `MethodEdgesInitialToFinalBaseOnlyApSet.Storage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.MergingStorage#add`,
  `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#add`.

- Old behavior: transient collapsed finals could enter final lists or some
  stores.
- New behavior: final lists, intraprocedural F2F, and summary stores reject them
  before mutation.
- Motivation: collapsed state belongs only to the
  `removeAbstraction`/`rebase` transition.
- Verdict: keep.

### 43. Summary phase visibility

- Related operations: `BaseOnlyApManager#enableNormalizedEdges`,
  `BaseOnlyApManager#normalizedEdgesEnabled`.

- Old behavior: the normalized-edge phase was a plain Boolean.
- New behavior: it is a volatile one-way `Forward -> TraceResolution` phase.
- Motivation: concurrent readers reliably observe the transition.
- Verdict: keep.

## Changes with no runtime logic effect

- Manager identity is not part of fact or delta equality/hash before or after
  this refactoring.
- No common/non-BaseOnly production module changed.
- Z2F/final summary algorithms were not changed.
- Changes in `BaseOnlyApAccess`, some delta braces, and simple iteration rewrites
  are formatting or structural only.

## Mitigation summary

- `BaseOnlyFinalFactAp#abstractOnly` and the `size`/`depth` rewrite were
  reverted as requested.
- `BaseOnlyAccessOps#clear` retains its denotational implementation because the
  proposed whole-fact deletion caused 39 reproducible path-resolution misses.
- `MethodInitialToFinalBaseOnlyApSummariesStorage.IdEdgeStorage#add` now follows
  Tree's same-slot, exclusion-aware identity suppression rule.
- `MethodEdgesInitialToFinalBaseOnlyApSet.Storage#filter` retains the normalized
  trace lookup required by the path-sampling tests.
- Intraprocedural F2F steady-state aggregation and delta publication now both
  re-emit the complete changed final language through the list-valued
  `MethodEdgesInitialToFinalApSet#add` contract.
- SWMR publication proof and deterministic concurrency schedules remain the
  postponed storage issue documented in `baseonly-storage-spec.md`.

The split-delta erased-boundary exception still requires explicit approval
because it is a narrow semantic special case. Trace-mode full scanning remains
correctness-motivated and requires performance validation.
