# Reverse-MUST overlap: transient native adapter

5 November 2026. Selected implementation design, no Kotlin implementation.
This is a supplement to the explicit CURRENT/SAVED_DIRECT/OPPOSITE matcher.
The pure region law belongs to Canonical.lean. This adapter retains the exact
native inverse output and layer. It does not define a new demotion policy.

## Verified native bridge

A bounded native AP probe runs on the unmodified52f dataflow jar:

```text
old P = arg0.prefixA.prefixB.MUST/FLOW / E{oldInputExcludedI}
old G = ret.MUST/FLOW / E{storedExcludedH}, mx{U}, NORMAL
reader mode = BACKWARD; old producer = FORWARD
actual = ret.STAR/FLOW / E{actualExcludedG}, mx{T}, NORMAL
G != H

old view = ret.STAR/FLOW / E{H} -> P.ANY/FLOW / E{}, DEMAND
old native Summary selector: no match
project same-path actual STAR flag to E{G,H}: old selector matches
existing native applyRecordLeaf + compiled edge: P.ANY/FLOW, DEMAND,
  E{}, mx{T,U}; no mark requests
```

The probe also applies the native compiled edge to the unprojected actual;
its output is identical. This rules out a second hidden rejection in that
closed FLOW cell. The proposed adapter still uses projected match+apply,
not a bypass of the native selector.

Four concrete cases also PASS. For old P.EXACT/T -> ret.MUST/T, the native
inverse remains P.EXACT/T with demand=false: NORMAL actual gives NORMAL,
DEMAND actual gives DEMAND. For old P.MUST/T -> ret.MUST/T, the native inverse
remains P.ANY/T, DEMAND for both actual layers. In all four cases the actual
STAR/T has protection, the original incomparable-E selector rejects, the
projected selector and native application pass, and protection survives.
Do not narrow the selected overlap correction to FLOW-only while pruning
concrete MUST relations, and do not force these concrete outputs to DEMAND.

The separate MAY/MUST FLOW controls in the probe are native application
comparisons, not permission to broaden their selector. Only the actual STAR
same-path overlap cell is added by this adapter.

## Preserve provenance before it is erased

`ap/Reference.kt:80` has `RecordLeafView(premise,result)`. The special MUST
constructor at90–113 loses some old tails and old input E by design. Do not
infer MUST provenance from result ANY, read-premise STAR or nonempty E.

Refactor the constructor internally to return a transient wrapper:

```kotlin
enum class NativeReadKind { GENERIC, FLOW_MUST_CONSTRUCTOR, CONCRETE_MUST_CONSTRUCTOR }
enum class OverlapCapability { NONE, MUST_CONCLUSION }

// Ordinary class: no automatic equality over compiler/source metadata.
class NativeReverseRead internal constructor(
    val geometry: RecordLeafView,
    val kind: NativeReadKind,
    val source: NativeReadSource, // immutable old P, old scalar G, producer direction
) {
    val overlapCapability: OverlapCapability get() =
        if (kind != GENERIC && source.conclusion.fact.tail == ANY_TAINT)
            MUST_CONCLUSION else NONE
    fun semanticKey() = NativeReadKey(geometry, overlapCapability)
}

data class NativeReadSource(
    val producer: Direction,
    val premise: Pattern,
    val conclusion: Conclusion,
)
data class NativeReadKey(val geometry: RecordLeafView, val capability: OverlapCapability)
```

`FLOW_MUST_CONSTRUCTOR` is produced only by the accepted first branch of
`mustRecordReadView`. `CONCRETE_MUST_CONSTRUCTOR` is produced only by its accepted concrete
branch. `GENERIC` is produced by the existing generic revEdge fallback.
Construct source and kind in the same branch as the view, not by repeating
an approximate tail test at a caller. Keep the public geometry-only
`reverseRecordLeaf` reference function as `typedRead?.geometry` if needed.
No new persisted AP field or Record identity/equality is required.

New overlap authority is narrower than recognition of a MUST constructor:
require an old normal MUST CONCLUSION. The special FLOW constructor also
accepts old P.MUST -> G.STAR. That reader retains LEGACY eligibility and must
not inherit the added overlap branch merely from its constructor family.
Two equal view geometries can therefore have different overlap capabilities;
`semanticKey` must distinguish those capabilities.

Old input E, output E, complete marks/mx, old direction and raw scalar geometry
remain available in `source`. The existing inverse can still deliberately
forget old input E in its result. Do not restore that E or rewrite output
headers. Physical ports stay on the owning Record and its direction-aware
scopeIn/exitIn functions; do not turn them into AP fields.

## Match legacy plus one projected AT contribution

The helper below returns at most two invocation-local packets per read.
Native legacy output is first. A new projected STAR packet is second.
This preserves the entire old stream before the new selected overlap effect.
Never project the whole packed actual or its exact/MAY/MUST memberships.

```kotlin
fun matchReversePackets(actual, read, mode): List<Facts> {
    require(read.source.producer != mode.direction)
    val old = ops.matchSummary(actual, read.geometry.premise, mode, OPPOSITE)

    if (read.overlapCapability != MUST_CONCLUSION || read.geometry.premise.tail != STAR)
        return listOfNotNull(old)

    // Ordinary STAR at the SAME read path only. All native old ancestry,
    // below and non-STAR checks retain their existing behavior.
    val starAt = samePathStarMemberships(actual, read.geometry.premise.path)
        ?: return listOfNotNull(old)
    val aE = actual.exclusion
    val rE = read.geometry.premise.exclusion
    if (aE.isSubsetOf(rE) || rE.isSubsetOf(aE))
        return listOfNotNull(old) // old AT/applicable already handles this flag

    val projected = starAt.withExclusion(aE.union(rE))
    val extra = ops.matchSummary(projected, read.geometry.premise, mode, OPPOSITE)
    return listOfNotNull(old, extra)
}
```

`samePathStarMemberships` is a complete membership operation:

- For FlowTree with tail STAR: look up the read-premise path and keep its
  complete Flow flag, actual layer and full mx. Build only that path/flag.
- For TaintTree with anyTail STAR: keep ALL `.any` marks at that exact node;
  omit its `.exact` marks, which remain on the legacy path. Keep the complete
  selected protection mask with `retainProtection(actual, projected)`.
- For Reach, EXACT, MAY, MUST or a missing STAR flag: return null.

The predicate is per scalar header/profile; do not compare a first mark,
forget mx or convert a mixed exact/nonexact packet wholesale. The projection
is an ephemeral matching packet. It is not an admitted initial, standing
input update, summary, demand, persisted row or source permission.

For same-path actual STAR and a STAR read premise, old eligibility uses the
E subset tests in either direction (`applicable` or `inside`). If both fail,
the old STAR AT contribution is absent. The new E-union packet is the
intersection region and contains the shared anchor. The existing native
query succeeds via `Ereader subset Eprojected`. The full native mark gate and
protection selection still execute. The pure region law does not replace them.

For a plain FLOW-MUST-conclusion read with FlowTree STAR actual, all positions can emit
the same constant P.ANY/FLOW result. A later proved specialization could skip
extra when any legacy contribution already gives that complete result. Do
not rely on that shortcut in the general implementation: a concrete packet
may have a legacy match for U and a new projected STAR/T at the same time.
Fallback-only-when-legacy-empty would lose T/protection there.

## Reuse existing application and effect handling

For each selected packet, call the existing native application with the exact
view, original complete caller P and protected-result flag:

```kotlin
for (packet in matchReversePackets(actual, read, mode)) {
    ops.applyRecordLeaf(packet, read.geometry, protected, mode,
        existingCollector(original, ...), original = original)
}
```

No new summaryEdge, custom mark transformer, blanket layer change or source
callback is needed. The original `view.result` controls the result layer.
The same ordinary global field cap, post-S storage, complete original,
cycle/protection logic, source-to-Reach discharge and Target handler run.
A ZERO source inverse may still produce Reach/Target; do not suppress that
case by an assumed DATA-output-base shortcut.

At physical calls, `PersistedSummaryReplay` can call the shared helper and
pass each selected packet to the existing already-matched `applyRecordView`.
At local boundaries and in pure observers, `LocalRelationApplication` calls
the same helper and applies all packets. Do not match a projected packet a
second time with a generic/current role. Classification and loop gating use
the STORED read geometry, never the transient projected E header.

## Selection and dedup migration

- Add typed construction at `Record.reverseOne` and
  `RecordOutputPosition.forEachReversedAt` in store/RecordStore.kt. Both full
  and positional readers must use the same trusted MUST constructor.
- Add or migrate typed callbacks in `SavedRecordSelection`. Its record-first,
  submitted-leaf and native-position order stays unchanged.
- `PersistedSummaryReplay.seenViews` changes its key explicitly from geometry
  to `NativeReadKey(geometry,overlapCapability)`. Keep its false-to-true protection upgrade
  rule exactly. A rejected generic read must not suppress a later MUST read
  with different eligibility.
- The per-record positional `SavedRecordSelection` seen set likewise uses
  `(NativeReadKey,protected)`, retaining old iteration order.
- Scope and physical exit are fixed by each owning query/record. If an index
  shares keys across those contexts, include owner/scope/exit in that key;
  do not broaden an invocation-local dedup key silently.
- Retain full `source` metadata for guard validation but do not add raw Record
  object identity or unused source fields to semantic equality by default.
  The overlap capability plus complete geometry determines eligibility;
  old input E intentionally forgotten by the native inverse is not restored.

Candidate PathTrie/position queries already enumerate comparable real paths;
the added AT case needs no broader scan, synthetic field or port alias.
Persistent summaries/Targets/normal contributors retain their existing keys.
NativeRecord source headers and source kind are read-only for this invocation.

## Native gates still required before implementation acceptance

The current seven standalone AP controls verify the bridge, not the complete
packed/actor integration. Add native tests for:

1. A packet with a legacy-matching mark/position and a different newly
   projected STAR mark: both results and protection must survive.
2. A full multi-mark STAR node, protected and unprotected memberships, both
   concrete and FLOW MUST provenance, both actual layers.
3. A generic read with otherwise similar geometry must not gain overlap;
   matching dedup must retain distinct semantic read kinds.
4. Same-path comparable E keeps the old result without duplicate overlap
   lane; excluded strict descendant, disjoint branches, MAY/MUST unchanged.
5. Direct/current roles cannot invoke the adapter. NormalResult from concrete
   EXACT-to-MUST remains NORMAL only when the native applied layer is NORMAL.
6. Physical/local/pure-observer consistency, exact ports, full parent ND,
   Source->Reach/Target and real call suffix continuation ordering.

No full native AP, Kotlin, whole-engine soundness, termination or report
invariance theorem is claimed by the region model or these finite probes.
