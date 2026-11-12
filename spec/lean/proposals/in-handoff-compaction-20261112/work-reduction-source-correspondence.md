# Source correspondence for C2, loop trials and disabled diagnostics

12 November 2026. Specification audit, not an implementation. The selected
revision is `fabf6247f24ade8e5b91be86be8df7749279101f`. The combined
[specification](../../../in-handoff-edge-compaction.md) changes no runtime
source. Full source hashes and the actual Lean check are in
[work-reduction-receipt.json](work-reduction-receipt.json).

## 1. Empty strict-descendant C2 families

The relevant sources are under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

| Source and member | Correspondence |
| --- | --- |
| `ap/RestrictedInitialPolicy.kt`: `emit` | Equal paths return earlier. The next branch handles demand ancestors. The final strict-descendant branch requires actual ANY or ANY_TAINT. STAR/EXACT cannot enter it. |
| `emitAdmission`, `emitAdmissions` | Failed primary returns before either FLOW companion. The empty-family proof includes all emitted commands, not only the primary. |
| `store/FrozenDemandTrie.kt`: `visitCountedNativeOrder` | Walk ancestor nodes along the raw path, then DFS from the same node. The proposed filter removes only strict descendants for INITIAL_C2/STAR or EXACT. Profile filtering and terminal ordinal order remain intact. |
| `store/DemandStore.kt`: `initials` | The first local visitor calls `offer`; the second run-2 visitor calls `requireFamily`. Completion/carry/control paths are separate. |
| `store/DemandResultCoverage.kt`: `InitialDemandResults` | Empty `emitAdmissions` changes neither keys, missing families nor materialized initials. Omitting an otherwise-recorded rejected `(entry,actual)` pair cannot change a later immutable-policy result. |

The branch uses path prefix, not counted depth. Static CLASS accessors do not
invalidate it. Marks, E, field limits and static grammar add guards; none
bypasses the tail requirement. Run-2 local walks are covered; their separate
transitive completion is not pruned. OUTPUT_C5 and precision witnesses stay
unchanged. The earlier
[nine-law audit](../main-migration-work-reduction-20261109/source-proof.md)
has the complete branch analysis and reconstructed run-8 work counts.

## 2. Structural descriptor round trip

`ap/ApManager.kt` stores initials under
`InitialKey(base,path,tail,intern(E),mark)`. `initial(Pattern)` interns the
same accessor list into the same manager. `ap/Premise.kt` reconstructs
`Pattern(PathFact(base,pathArray,tail,mark),E)` in `InitialAp.toPattern`.
Neither function changes tail, mark, field exclusions or path contents.
`ap/AdmittedInitial.kt` stores layer separately. Thus, for legal emitted
patterns, decoding the materialized command preserves the exact structural
descriptor used by the loop comparison.

Materialization does allocate IDs. Skipping losing trial materialization can
change those IDs. They are not semantic descriptor fields, sink IDs or full
mark identities. Native correspondence tests must compare decoded keys and
complete premise membership, rather than requiring equal allocation IDs.
Do not add proof/descriptor metadata to existing runtime data-class keys.

## 3. Negative loop witness and unchanged fallback

| Source and member | Correspondence |
| --- | --- |
| `engine/LoopOutputRestriction.kt`: `restrictWithCertificate`, `restrictScalar` | Existing run-1/Reach/non-growing bypasses, complete baseline, empty-baseline drop, prefix order, full equality and raw fallback remain. The first-budget certificate is still disabled. |
| `engine/LoopConsumerObservation.kt`: `observe` | Adjacent, enclosing, repeat and labelled components are all frozen into the result. Virtual saved replay suppresses actual mark-request effects. Keep its data/Target checks. |
| `LoopOutputRestriction.kt`: `LoopObservedFacts` | A LinkedHashSet adds full pattern/layer/H members. No later subsumption or OR-upgrade removes an extra membership. |
| `engine/MethodBlockRuntime.kt`: `observe` | The native adjacent/repeat scope maps, physical entries, `keepLocalConclusion(...,count=false)` filter and emission layer define the probe descriptors. Use these views directly; do not reconstruct approximate routes. |
| `engine/LoopQueryScratch.kt`: `LoopAdmissionBundle` | Adjacent/repeat queries feed both aggregate and labelled projections. Reuse completed descriptor families in this same bundle; do not run C2 again on fallback. |
| `LoopQueryScratch` | An existing complete cached C2 answer may be decoded. Partial early-aborted results must not enter that cache. |

The earlier audit pinned 12 runtime sources. Eleven hashes still match.
`MethodBlockRuntime.kt` differs only by forwarding
`reachedSinkReportIds` from the root owner at the block adapter. Its observer,
routing, liveness and C2 code is unchanged. This difference is recorded in
the new receipt; it was not treated as hash parity.

The new Lean proof requires `local descriptors ⊆ complete observation`.
The native bridge is precisely the original labelled-admission projection
after native liveness. Unknown views and run-2 transitive queries fall back.
The round-trip proof is a generic component whose native premise is audited
above; it is not a formal model of Java ConcurrentHashMap or interning.

## 4. Disabled unresolved-call archive

| Source | Current ownership and selected change |
| --- | --- |
| `engine/RunMethodCallServices.kt` | `observed` is allocated for every run-1 owner. Its only behavioral use is `observeUnresolved`, where full input growth gates a callback. `freeze` releases it. Semantic transfer does not read it. Initialize null and allocate only after the enabled observer, unresolved stage and TAINT guards. |
| `engine/SharedObjects.kt` | Currently casts the interpreter to `UnresolvedCallObserver`. Return that same object only when its stable capability is enabled. |
| `interp/UnresolvedCallObserver.kt` | One abstract callback. Add a default-true capability; existing generic observers keep their old behavior and identity. |
| JVM `interp/JIRInterpreter.kt` | `reached` returns immediately when `externalMethodTracker` is null. This is the exact inert-disabled case. Expose `enabled = tracker != null`. |
| `ap/ifds/taint/ExternalMethodTracker.kt` | Enabled callbacks aggregate method/signature, position, pass-rule state and callback counts. Do not change this class or enabled archive deduplication. |

The diagnostic archive has no consumer which can admit a fact, answer a
mark request, apply a summary, report a sink or seed a later iteration.
`AddedFactAccumulator` also has independent semantic owners; keep the class
and those instances. This is an ownership audit, not a proof that arbitrary
observers are inert. Only a declared disabled capability can skip a callback.

The Lean diagnostic model uses one stable enabled flag for a finite trace.
Its archive key is opaque; the enabled transition is literally shared.
The semantic-state product theorem requires that transfer does not read
the diagnostic component. The private-field audit supplies that bridge.
It does not prove equivalence for a dynamically toggled observer.

## 5. Checks actually run

- `WorkReduction.lean`: 23 constructive claims; audit permits only `propext`
  and `Quot.sound`. First failed parser attempts are retained separately.
- `NativeWorkReduction.java`: 182 assertions on the pinned dataflow JAR.
  It checks empty-E strict-descendant families, ordered stream equality,
  native descriptor interning and positive MAY/MUST child controls. It uses
  opaque concrete mark IDs without a catalog lookup, as the earlier native
  operator controls did. It does not model rule declaration ownership.
- The first Java compile failed because the manager needed a MarkTable
  wrapper; its failure receipt is retained. The corrected compile/run pass.
- No analyzer iteration, project scan, production rewrite or Gradle suite
  was run. These controls do not exercise a future modified native trie,
  streaming loop adapter or observer capability. The spec lists those
  required implementation tests explicitly.
