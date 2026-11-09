# Local C2 pruning and a first-extra-admission witness

Runtime source: `9b21b3716`; current migration checkout: `03cf52fa9` plus report-only work. This is a read-only design audit. No analyzer runtime was changed. All Conductor geometry below is from the **run-8** snapshot, field limit 7; the campaign reached run-8 and completed/accepted run-7.

## 1. Skip impossible descendant visits in C2

Candidate change: reduce candidate enumeration only. Accepted initial families, their order, AP fields, marks, exclusions, layers, protection, source/sink behavior, paired C5 and handoff stay unchanged. Rejected-candidate and trie-work diagnostic counts can decrease.

`RestrictedInitialPolicy.emit` lines53–63 permits a demand strictly below the actual path only when the **actual tail is ANY or ANY_TAINT (MUST)**. STAR and EXACT actuals return null in that case. The earlier same-path and demand-ancestor branches cannot apply: a strict descendant is not equal to the actual and cannot also be its ancestor. This argument uses path-list prefix order, not counted field length, so uncounted static class accessors do not create an exception.

`emitAdmission` then returns null. `emitAdmissions` lines73–74 returns the empty list before either companion is considered. In particular, it does not create a FLOW companion or an EXACT/FLOW prefix companion after a failed primary.

Keep the existing ancestor walk, same-node values, compatible-mark profile test and ordinal order. Prune only the strict descendant subtree, and only for `INITIAL_C2` with actual STAR/EXACT:

```text
visitCandidates(actual, kind, visit):
    node = roots[actual.base]
    if node is absent: return

    for accessor in actual.path:
        visitValuesInExistingProfileAndOrdinalOrder(node, actual, kind, visit)
        node = node.child(accessor)
        if node is absent: return

    if kind == INITIAL_C2 and actual.tail in {STAR, EXACT}:
        visitValuesInExistingProfileAndOrdinalOrder(node, actual, kind, visit)
        return                         // Strict descendants cannot emit a family.

    existingDepthFirstVisit(node, actual, kind, visit)

rejectBudgetOnExtraAdmission(candidate, completeBaseline):
    if not supportedFrozenLocalDataView(candidate): return UNKNOWN
    for actual scoped/family-labelled consumer view V of this candidate:
        if not existingBoundaryLivenessAllows(V, candidate): continue
        stream V's local C2 candidates in the existing order:
            for emission in policy.emitAdmissions(demand, candidate, candidate.layer):
                key = (V.scope, V.family, emission.pattern, emission.layer)
                if key is absent from completeBaseline's same labelled family:
                    return REJECT_THIS_BUDGET   // Before ap.initial() or saved replay.
    return UNKNOWN                     // Run the complete observer; never accept here.
```

The actual Kotlin predicate may use `!actual.fact.tail.isAny`, because `Tail.isAny` is exactly ANY or ANY_TAINT. Keep the explicit `kind == INITIAL_C2` guard.

### Complete source-case review

- **Marks and groups:** the strict-descendant tail guard does not depend on mark kind, group membership or concrete mark equality. Existing mark-profile compatibility stays unchanged. Well-formed interned mark IDs are part of the native input domain.
- **Exclusions:** demand-exclusion normalization and actual exclusions can reject additional matches; they cannot permit a STAR/EXACT actual to enter the strict-descendant branch. No exclusion is dropped or rewritten by this optimization.
- **Layers and companions:** primary failure prevents all emissions for either input layer. Same-path and ancestor cases, including the run-2 requested-STAR case and its FLOW companion, remain visited.
- **Budgets, directions and static anchors:** these are additional guards, not ways around the tail test. The rule holds in both directions and all restricted runs. Run-1 has no DemandStore C2 lookup and is unaffected.
- **ZERO and Target:** `DemandStore.initials` handles Reach/ZERO through control pairs before using this trie. Target has no AP path. DATA entries from control rows do enter the same trie and use the same emitter, so the proof covers them.
- **Scopes and ND:** each method/block entry retains its existing physical scope and exit union. The lookup does not change an ND premise or its execution join.
- **Run-2 static completion:** both local C2 trie walks are safe to prune, including the `requireFamily` walk. An empty primary adds no `keys`, `initials` or `missing` memberships. The direct/static carry/transitive lookup code remains unchanged. The query-local `offered` set can omit rejected pairs without changing a later emission: the same immutable actual/policy pair still rejects. Diagnostics can vary.
- **C5 and precision witnesses:** keep OUTPUT_C5 traversal and `precisionCursors` unchanged. This proof authorizes neither a C5 subtree cut nor a longest-demand certificate.
- **Visitor contract:** arbitrary callback enumeration is observably different because rejected candidates are omitted. The proven boundary is the two production C2 visitors (`offer` and `requireFamily`), not an arbitrary visitor with unrelated side effects. Valid input semantics are preserved; corrupt-input exception timing is not a selected contract.

### Why ANY and MUST must still descend

Assume matching full T, empty exclusions and enough field budget:

| Demand | Actual | Native start | Why pruning would lose it |
|---|---|---|---|
| `a.f.$/T` | `a.[any]/T`, DEMAND | `a.f.$/T`, DEMAND | A MAY suffix can be f. |
| `a.f.$/T` | `a.[any-taint]/T`, NORMAL | `a.f.$/T`, NORMAL | Uniform taint includes f. |
| `a.f.[any]/T` | `a.[any]/T`, DEMAND | `a.f.*/T`, DEMAND plus FLOW companion | This is a real descendant initial family. |

A MUST actual that excludes f does not satisfy the first-field f demand. That per-field rejection does not justify pruning other descendant branches.

### Exact captured Conductor work bounds

The reconstruction deduplicates entry patterns exactly as `DemandStore.Builder.index` does. It reconciles **all 242 native `entryCount` values**: 83,646 paired DATA rows correspond to **11,250 unique C2 entry terminals**. All control entries in this snapshot are Target, so they add no DATA terminal. A paired-row count must not be reported as a trie-terminal count.

These are synthetic base-root STAR/FLOW probes against the actual frozen tries, not measured query frequencies:

| Consumer index | Base | Nodes before→after | Mark profiles before→after | Compatible terminals before→after |
|---|---|---:|---:|---:|
| `ParametersUtils.replace`, scope(2,40), key52269309 | local3 | 4,665→1 | 4,686→3 | 4,666→2 |
| Same signature/scope, key102472271 | local3 | 3,821→1 | 3,840→3 | 3,822→2 |
| `ParametersUtils.replaceList`, scope(2,34), key102495197 | local2 | 295→1 | 339→3 | 296→2 |

Thus the first probe avoids 4,664 compatible emitter calls which can only reject, plus the corresponding node/profile work. The per-query bound changes from ancestor+subtree visits to ancestor+same-node visits for STAR/EXACT. No elapsed-time or whole-run speedup follows without the actual query distribution. Complete per-base cases are in the [captured trie work data](../../../../docs/reports/data/bidirectional-main-migration-c2-trie-work.json).

## 2. Reject one prefix budget on the first extra descriptor

This is a separate negative test. It does not restore the disabled whole-family/range certificate.

The complete observation has independent adjacent, enclosing, repeat and labelled membership sets. `InitialDemandResults` adds exact `(pattern,layer)` keys. `LoopObservedFacts` adds exact `(pattern,layer,protection)` members. It performs no OR upgrade, layer replacement, subsumption deletion or later removal. Enclosing data also retains scope, exit and complete original; targets are separate exact set members. Consequently, an element outside the frozen baseline cannot disappear when more query results are added.

If a **real admission** in one candidate family is absent from that same complete baseline family, the full candidate observation cannot equal the baseline. Stop only this candidate budget, before interning its initial and before enclosing saved replay. The remaining consumer families cannot cancel the extra element. This does not require a certificate covering any other budget.

Required guards:

1. Use the complete already computed baseline. A partial baseline is insufficient.
2. Compare the full descriptor: native base and accessor chain, tail, concrete/full mark or FLOW exclusion, field exclusion, layer, exact consumer scope, and ADJACENT/REPEAT label. Admission starts do not add protection. An enclosing-data witness would additionally need its original, exit, layer and exact protection membership.
3. Use the native `emitAdmissions` family, including both companion rules. A demanded path or ANY cursor witness alone is not an emitted initial.
4. Apply the same boundary liveness filter and actual consumer-view routing as the observer. Do not invent labels when a view does not export them.
5. Keep this fast path local on run-3 and later. Run-2 shared/static completion and unsupported adapters use the current full observer.
6. If no extra witness is found, run the full observer/fallback. There may be missing baseline members or different enclosing results. A completed descriptor family may be retained for the fallback to avoid a repeated lookup, but this is an implementation option, not permission to accept the cut.
7. If exact result union is changed later to remove/upgrade memberships, re-prove this monotonicity contract.

### Concrete first witness from captured Conductor demands

Use scope(2,40), key52269309, local3 and the actual FLOW demand rows at paths `[]`, `[MapValue]`, `[MapValue,Iterable.Element]` and `[MapValue,MapValue]`. There is a root ANY and a root STAR demand; the other listed demands are ANY.

Construct the well-formed native C2 raw probe:

```text
raw: local3.MapValue.Iterable.Element.*/FLOW, NORMAL

Complete C2 raw family (all FLOW,NORMAL):
    local3.$
    local3.MapValue.*
    local3.MapValue.$
    local3.MapValue.Iterable.Element.*

Budget-1 candidate:
    local3.MapValue.[any]/FLOW, DEMAND

One actual descendant demand:
    local3.MapValue.MapValue.[any]/FLOW

Its emitted start:
    local3.MapValue.MapValue.*/FLOW, NORMAL
```

That last start is outside the four-member baseline family. It rejects the budget immediately. The complete candidate C2 family has **466** distinct starts; producing them all is unnecessary once the extra witness is found. The candidate also lacks baseline `local3.MapValue.$/FLOW`, which illustrates why absence of an extra witness must not accept a budget.

This is an executable C2 probe reconstructed from captured native demands. It is not evidence that this exact raw value was sampled during a live loop trial, nor a complete baseline LoopObservation: other families remain opaque. Its witnessed admission is sufficient to reject any candidate whose complete baseline contains the stated local family for that view.

The root STAR/FLOW work probe in the previous table has two starts, but depth zero has no proper loop prefix cut. Do not use that two-terminal/root example as a complete deep-loop baseline.

## 3. Verification and implementation gates

`C2Descendants.lean` checks nine constructive local laws: STAR/EXACT rejection, no companion without a primary, ordered output equivalence after empty-family filtering, removed node work, and persistence of an explicit extra witness under later union. It uses no Classical.choice or excluded-middle axiom. Some generic list/equality laws use Lean's `propext`; no whole native AP/trie/driver equivalence is claimed. Native branch correspondence and all adapters are audited above. The [axiom log](axioms.txt) records every checked theorem's axioms.

No Gradle build, analyzer run or core edit was performed for this note. Before implementation, add focused native checks for STAR/EXACT versus ANY/MUST, same-path and ancestor order, concrete/Flow companions, exclusions and group matching, DATA controls, ZERO, both directions and run-2 static fallback. For the negative witness, test a late extra companion, equal projections with different scope/family/layer, both protection memberships in enclosing data, and a no-extra-but-missing-member case which must fall back.
