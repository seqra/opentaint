# AP, stores and IR interpreter — implementation proposal

Status: implementation proposal for phase 1 of [bidirectional-task.md](../bidirectional-task.md). It implements the
two parts of the AP spec: [`ap.md`](ap.md) (Part I: the access path and its stores) and
[`interpreter.md`](interpreter.md) (Part II: the IR interpreter for the JVM). The specs are normative. This document
does not change them. [`analyzer-impl.md`](analyzer-impl.md) (phase 2) calls the facade `ApOps` (§5), the stores
(§7), the `Interpreter` and its forms (§23, §25). JVM only.

Language: ASD-STE100 Simplified Technical English. Code first.

Numbering: Part I uses §0 to §8, Part II uses §20 to §34. In the text and in the package maps, a qualified name
(`ap.md` §4.1) names a spec section, and a bare number names a section of this document. In a Kotlin comment, a bare
`§` number names a section of the spec that the part implements (`ap.md` in Part I, `interpreter.md` in Part II), and
`Part I §n` or `Part II §n` names a section of this document. A rule id (`S7`, `W2`, `T1`, `I3`, `AC3`, `O1`, `P4`)
names the rule of the spec that defines it. Two specs have `A` ids: a bare `A1` to `A6` is a rule of
`interpreter.md` §2.5, and an assumption of `analyzer-core.md` §0.1 is always qualified (`analyzer-core.md` A4). The
`D` ids of Part II are the deviations of `interpreter.md` §6. The ids `DD`, `K` and `SI` are ids of this document.

Paths of today's code: the design decisions and Part I give them relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/`, unless they start with `core/`.
Part II uses the prefixes `DF/`, `JVM/` and `BWD/` (see the scope of Part II). `path:n` is line `n` of that file; a bare
`:n` is line `n` of the file that the row or the comment names.

Each part ends with its test plan (§8, §33). §34 lists the spec issues and the deviations from today's code.

## Design decisions

The sections below cite these decisions by their id.

| Id | Decision | Reason | Code |
|---|---|---|---|
| DD1 | MODULES AND PACKAGES. The new code is in the Gradle modules of today's core, in new packages: `org.opentaint.dataflow.bidi.ap`, `bidi.store` and `bidi.interp` in `core/opentaint-dataflow-core/opentaint-dataflow`, and `org.opentaint.dataflow.jvm.bidi.interp` in `core/opentaint-dataflow-core/opentaint-jvm-dataflow`. `analyzer-impl.md` §1 adds `bidi.engine`, `bidi.driver` and `jvm.bidi`. | The new code uses many `internal` declarations and utilities of these modules. The old core stays in the same modules, because the prescan runs it. | §1, §20 |
| DD2 | REFERENCE FORMS AND TREES. The spec forms are per path (`Pattern`, `PathEdge`, `Conclusion`). The code groups the paths into trees (`EdgeTree`, `ap.md` §7). The per-path forms stay in `Reference.kt` as the reference forms. | The tests compare each tree operation with its reference form. | §6, §8 |
| DD3 | THE EDGE DELTA. A propagated item is `(premise: PremiseKey, node: CommonInst, tree: EdgeTree)`. The layer is `tree.layer` (`analyzer-core.md` §4.3). There is no `Edge` class (`ZeroToFact`, `FactToFact`, `NDFactToFact`). | The premise key gives the kind of the edge (`PremiseKey.nonZeroCount`). | §3.4 |
| DD4 | ADDED FACTS ARE TREES PER LINK KEY. After the binding and the cleaners, a caller fact tree is one `EdgeTree` in callee coordinates. Its leaves are the added facts. `AddedFactStore` keeps one merged tree per (caller reference, link layer, base, exclusion, mark exclusion). `add` returns the delta: the new leaves are the new links. A `Link` (the spec form) is one leaf with its `CallerRef`. The same tree is the added-fact part of a subscription. | Today a subscription keeps caller fact trees too (`MethodTreeAccessPathSubscription`). The replay and the delivery read the satisfying part of a tree with one function, `ApOps.satisfying` (P4 of `analyzer-core.md` §5.3). | §5.4, §7.5 |
| DD5 | INTERNING. `ApManager` interns `PathNode`, `InitialAp`, `PremiseKey`, `MarkSet`, `ExclusionSet`, `LeafMarks` and `Payload`, so equality is identity where a store key needs it. Each store hash-conses its `FactNode`s with its own interner (`ApManager.newNodeInterner()`). `FactNode` and `EdgeTree` equality is structural, with an identity fast path. | A shared node table needs a lock and keeps the trees of a run alive. A callee publication tree meets a caller subscription tree of another store, so equality must not use identity alone. | §4.5, §5.1 |
| DD6 | A PATH ELEMENT IS `AccessorIdx` (an `Int`, `ap/ifds/access/util/AccessorInterner.kt:17`). A path is `List<AccessorIdx>` in the reference forms and `IntArray` or `PathNode` in the tree code. `isClass` is `AccessorIdx.isStaticAccessor()`. Part II converts a JIR `Accessor` with `manager.accessors.index(a)`. | `ap.md` §3.4 says that the sets hold `AccessorIdx`. | §3.1, §6 |
| DD7 | `TaintMark` is `@JvmInline value class TaintMark(val id: Int)` in `bidi.ap`, with `MarkTable` (`manager.marks.mark(name)`, `manager.marks.name(m)`). The zero mark is `TaintMark.ZERO`. The JVM glue maps a rule mark to it by its name. | The JVM `TaintMark` is in `configuration-rules-jvm`. `opentaint-dataflow` does not see it: its `build.gradle.kts` has `configuration-rules-common` only. | §3.1 |
| DD8 | THE ZERO BASE is `AccessPathBase.Zero` (GENERALIZE of `ap/ifds/Accessors.kt:5`). | `ap.md` §1, §2.4. The old core never makes it, so its behaviour does not change. | §2, §3.4 |
| DD9 | `TypeFilter(may, markPolicy)` is a class in `bidi.ap`. `ApOps.filter` applies `may` to the path, then the mark policy to the concrete marks of the leaves at the root path. `TypeFilter.and` is the conjunction of two filters on one base. The backward run applies no filter and no policy. | `interpreter.md` §5.1 applies the mark policy "after the filter", to the same facts. Part II builds `may` with today's `JIRFactTypeChecker`. | §5.5, §26.2 |
| DD10 | THE WITNESS REPRESENTATION. `VulnerabilityStore` keeps one entry per (vulnerability key, run, witness shape). Its fact trees are the union of the triggering parts of every witness with that shape. | The confirmation reads only the shape (the premise set and the layer of each sink edge), and each sink edge stays a leaf. So the merge loses nothing (§7.12). | §7.12 |
| DD11 | FORMS PER METHOD KEY. `JIRMethodForms` caches the call plans and the entry rules per method key. `JIRMethodEntry` caches the statement summaries and the exit rules per method. | The callees of a call and the start filter read the context of the key. `analyzer-core.md` §4.8 caches per method (spec issue SI16). | §31.2 |

---

## Part I — The access path and its stores

Scope: the AP with all its stores (`ap.md` §2 to §9) and the test plan of `ap.md` §13. The code is in the module
`core/opentaint-dataflow-core/opentaint-dataflow`, in the new packages `org.opentaint.dataflow.bidi.ap` and
`org.opentaint.dataflow.bidi.store` (DD1). The behaviour of the old core does not change (the prescan runs it).

## 0. Conventions and additions to the AP interface

### 0.1 Conventions

| # | Convention | Reason |
|---|---|---|
| K1 | A path element is `AccessorIdx` (DD6). `isClass` is `AccessorIdx.isStaticAccessor()`. A counted accessor is a field or an element accessor (`isCounted`, §3.1). | `ap.md` §1, §3.4. |
| K2 | A mark is the value class `TaintMark` of `bidi.ap` (DD7). | The JVM `TaintMark` is not visible in `opentaint-dataflow`. |
| K3 | The zero base is `AccessPathBase.Zero` (DD8). Each exhaustive `when` over `AccessPathBase` gets a `Zero` branch (§2). | `ap.md` §1, §2.4. |
| K4 | `MethodKey` is `typealias MethodKey = MethodEntryPoint` (REUSE, `ap/ifds/MethodWithContext.kt:24`). | `ap.md` §1 and `analyzer-core.md` §1 define the method key as the `MethodEntryPoint` of the method (context and forward entry statement). |
| K5 | A RUN store has one writer (the runner of its method, `analyzer-core.md` O1). It has no lock. `ApManager`, `ApOps` and `VulnerabilityStore` are thread-safe. §7.1 gives the table. | `analyzer-core.md` §2. |

### 0.2 Additions to the AP interface

`ap.md` gives the operations of `ap.md` §4, §6.2 to §6.5 and §9.1, and the stores of `ap.md` §8. Part I adds these
members. `analyzer-impl.md` and Part II call them.

| What | Why | Code |
|---|---|---|
| `ApOps.satisfying(a, j, mode, record = false)` | The part of an added-fact tree whose facts satisfy the premise `j`. The replay and the delivery use this one function (P4 of `analyzer-core.md` §5.3, DD4). | §5.4 |
| `ApOps.applyCombination(parts, g, mode, out)` | A summary with several premises on one full combination (`ap.md` §4.6, event E6). | §5.4 |
| `ApOps.matchLiteral(c, lit, mode, out): LiteralMatch?` | The input of one conjunction literal and the layers of its contribution (`ap.md` §4.6). `ConjunctionStore.add` takes it. | §5.8 |
| `ApOps.without(c, part)`, `ApOps.targetTree(target, layer)` | The exact removal of a part of a tree: the global-state rule and the entry marks (`interpreter.md` §4.7 steps 3 and 4), and the identity split of a summary delta (`analyzer-impl.md` §4.6). A one-leaf tree for a conjunction target or an end fact. | §5.8 |
| `ApOps.zero(layer)` | The end facts apply to the zero fact in the layer of the sink edge (`interpreter.md` §4.1). | §5.9 |
| `ApOps.policy(added)` | `ap.md` §6.2 on a tree: one initial fact per added tree. | §5.9 |
| `ApOps.requestAction(i, kind, a, caller): RequestAction` | The AP rule of one (request, link) pair (`ap.md` §4.5, §4.10 items 2 to 4). The analyzer makes the pairs (`analyzer-core.md` §4.6). | §5.10 |
| `ApOps.leaves(t)` | The per-path view of a tree. The links of `AddedFactStore` and the tests read it. | §5.11 |
| `ApMode`, `ApOut`, `CollectingOut`, `SinkCheck` | The constants of a run that the operations read; the receiver of the result groups and of the requests; the result of a sink check (`ap.md` §4.9). | §3.2, §5.2, §5.8 |
| `ExclusionSet.of(a: AccessorIdx)` | The exclusion `{a}` of one keep edge (`interpreter.md` §2.1 `strongKeep`). | §3.2 |
| `InitialAp.manager` (internal) | `Record.reversedAt` interns the reversed premise. | §3.4, §7.8 |
| `ApManager.newNodeInterner()` | One `FactNode` interner per store (DD5). | §4.5, §5.1 |
| `MethodEdgeStore.add` with a zero conclusion per premise key; `edgesAt` | The backward edge `{jb} → zero` of a reversed source (`ap.md` §9.2 SOURCE HITS). The queries of the trace resolution (phase 5). | §7.3 |
| `InitialFactStore.supported` | The premise sets that are supported jointly (`ap.md` §4.9 condition 3). The driver fills it at the barrier. | §7.4 |
| `AddedFactStore`: the key (caller reference, link layer, base, exclusion, mark exclusion), `add` returns the delta, `overlapping(base, path)`, `links()` | Two trees with other exclusions never merge (T3). The request join of `ap.md` §8.8 and the support at the barrier read the links. | §7.5 |
| `DemandStore.Builder`; the implicit zero demand of `near` | The driver builds the store before the run (`analyzer-core.md` A4). Every method key has the zero demand (`analyzer-core.md` §4.4). | §7.7 |
| `RecordStore` (an interface), `PersistentRecordStore`, `view()`, `persist(direction, summaries)`, `Record.reversedAt(a)` | A run reads the store through a read-only view (`analyzer-core.md` A4). The driver persists the records at a barrier (R1). A reader in the other direction reads the reversed records (R3). | §7.8 |
| `ConjunctionStore.add(rule, statement, arity, literal, input)`, `Input`, `Combination`, `ndJoin<S>(NdKey)`, `NdSummaryJoin` | The literal inputs and the E6 join (`ap.md` §8.9, `analyzer-core.md` §5.4). The type parameter `S` keeps `bidi.store` independent of `bidi.engine`. | §7.10 |
| `SourceHitStore.entries()` | The driver reads the source hits at the barrier. | §7.11 |
| `VulnerabilityKey.rule: CommonTaintConfigurationSink`, `SinkEdge(premise, layer, facts)`, `SinkWitness.endFacts`, `ConcurrentVulnerabilityStore` | The key reuses the rule object of every run. The witness merge (DD10). | §7.12 |
| `Cleaner(base, path, reach, mark)`, `CleanReach`, `ConjunctiveEdge(literals: List<Pattern>, target)`, `revEdge` | The primitives that Part II builds and reverses (§22.1). | §5.8, §6 |

---

## 1. Package map

```
core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/
├ ap/ifds/Accessors.kt              GENERALIZE: + AccessPathBase.Zero (DD8)
├ ap/ifds/AccessPathBaseStorage.kt  GENERALIZE: `Zero -> error(...)` in `getOrCreate`/`find` (the zero tree never goes there, §7.3)
└ bidi/
  ├ ap/
  │ ├ Facts.kt             Direction, Layer, Tail, ApMode, TaintMark, MarkSet, MarkSlot, ExclusionSet (§3.2)
  │ ├ AccessorTable.kt     AccessorTable, MarkTable: id <-> value, no ConcurrentReadSafe map (§3.1)
  │ ├ PathNode.kt          PathNode: the interned accessor chain of a premise (§3.3)
  │ ├ InitialAp.kt         InitialAp, PremiseKey, the zero fact (§3.4)
  │ ├ Payload.kt           LeafMarks, Payload (§4.1)
  │ ├ FactNode.kt          FactNode: the trie node, boundedDepth (§4.1, §4.5)
  │ ├ FactNodeOps.kt       the node algebra: T1 merge, T4 delta, T5 fold, maps and splits (§4.2, §4.4)
  │ ├ FactNodeInterner.kt  T6 hash-consing, one per store (§4.5)
  │ ├ EdgeTree.kt          EdgeTree and its canonical form (§4.1)
  │ ├ TreeGroup.kt         merge rules T1, T2, T2', T3, the delta T4, subsumption of ap.md §8.1 (§4.3)
  │ ├ ApManager.kt         the interners and the factories (§5.1)
  │ ├ ApOut.kt             ApOut, Results (the result groups), CollectingOut (§5.2)
  │ ├ ApOps.kt             the facade of the AP operations (§5)
  │ ├ Concat.kt            CompiledEdge, the tree delta-concat of ap.md §7.3 (§5.3)
  │ ├ Summary.kt           satisfying, applySummary (§5.4)
  │ ├ Clean.kt             the cleaner on a tree (§5.6)
  │ ├ Limit.kt             the field limit on a tree (§5.7)
  │ ├ Demand.kt            startFact, policy, emit, restrict (§5.9)
  │ ├ Primitives.kt        Cleaner, CleanReach, TypeFilter, MarkPolicy, ConjunctiveEdge, SinkCheck, LiteralMatch, RequestAction
  │ └ Reference.kt         the per-path forms of ap.md §3.4, §4.1, §6.3, §6.4 and of §6 (DD2)
  └ store/
    ├ PathTrie.kt          the path index of ap.md §8 (§7.2)
    ├ MethodEdgeStore.kt   ap.md §8.1 (§7.3)
    ├ InitialFactStore.kt  ap.md §8.2 (§7.4)
    ├ AddedFactStore.kt    ap.md §8.3; CallerRef, Link (§7.5)
    ├ RunSummaryStore.kt   ap.md §8.5 (§7.6)
    ├ DemandStore.kt       ap.md §8.6; DemandStore.Builder (§7.7)
    ├ RecordStore.kt       ap.md §8.7; Record, RecordStore, PersistentRecordStore (§7.8)
    ├ RequestStore.kt      ap.md §8.8; RequestKind (§7.9)
    ├ ConjunctionStore.kt  ap.md §8.9; NdSummaryJoin (§7.10)
    ├ SourceHitStore.kt    ap.md §8.11 (§7.11)
    └ VulnerabilityStore.kt ap.md §8.10; VulnerabilityKey, SinkEdge, SinkWitness (§7.12)
```

---

## 2. Reuse map

The kinds of reuse (both parts):

* REUSE: import today's class and call it as it is.
* GENERALIZE: make today's class generic (a type parameter, an extracted interface), so that the old core and the new
  core both use it. The behaviour of the old core does not change (the prescan runs it).
* ADAPT: copy the algorithm into a new class and change it. The row says what changes.
* PORT: copy a class of the branch `origin/saloed/backward-main` into a new class.
* SPLIT: divide today's class into new classes.
* REPLACE: a new class does the work; the new core does not use today's class.
* REMOVE, NOT USED: the new core does not use today's class, and no new class does its work.

| Today (path:line) | Kind | New |
|---|---|---|
| `AccessPathBase` (`ap/ifds/Accessors.kt:5`) | GENERALIZE | `+ data object Zero`. Each exhaustive `when` over `AccessPathBase` gets `Zero -> error("zero base")`: `ap/ifds/AccessPathBaseStorage.kt`, `ap/ifds/serialization/AccessPathBaseSerializer.kt`, `core/opentaint-dataflow-core/opentaint-jvm-dataflow/.../JIRCallPositionResolver.kt`, `.../JIRMethodCallFactMapper.kt`, `core/src/main/kotlin/.../sarif/TraceMessageBuilder.kt`, `.../spring/SpringRuleProvider.kt` (a `when` with `else` does not change). The old core never makes `Zero`, so its behaviour does not change. |
| `Accessor` and its classes (`ap/ifds/Accessors.kt:66`) | REUSE | the values of `AccessorTable`; `TypeFilter` reads them |
| `AccessorIdx`, the bit layout and its tests (`ap/ifds/access/util/AccessorInterner.kt:17`, `:94-137`) | REUSE | path elements; `isFieldAccessor`, `ELEMENT_ACCESSOR_IDX` (counted), `isStaticAccessor` (class) |
| `AccessorInterner.AccessorStorage` (`ap/ifds/access/util/AccessorInterner.kt:20-38`) on `ConcurrentReadSafeObject2IntMap` | ADAPT | `AccessorTable`, `MarkTable`: `ConcurrentHashMap` and a volatile copy-on-write array (§3.1) |
| `ConcurrentReadSafeObject2IntMap`, `ConcurrentReadSafeInt2ObjectMap` (`src/main/java/.../util/`) | REPLACE | not used by the new core (§3.1) |
| `ExclusionSet` (`ap/ifds/ExclusionSet.kt:6`) | REPLACE | `bidi.ap.ExclusionSet`: no `Universe`, `IntArray` of `AccessorIdx` |
| `AccessPath.AccessNode` (`ap/ifds/access/tree/AccessPath.kt:261`) | ADAPT | `PathNode`: interned, no manager field, no `addParent` collapse (`:316`, `limitFieldAccess` `:375`, `limitElementAccess` `:354`) |
| `AccessPath` (`ap/ifds/access/tree/AccessPath.kt:27`) | REPLACE | `InitialAp` |
| `AccessTree.AccessNode` (`ap/ifds/access/tree/AccessTree.kt:261`) | ADAPT | `FactNode`: a `Payload` instead of `isAbstract`/`isFinal`/`deepAccessorExclusion`; no `[any]` edge, no `$` child |
| `mergeAdd`, `mergeAddDelta`, `mergeNodeLoop`, `pushSharedChildPairs`, `mergeAccessorsRaw`, `transformAccessors`, `removeSingleAccessor`, `trimModifiedAccessors` (`AccessTree.kt:815`, `:854`, `:912`, `:1005`, `:1388`, `:1671`, `:1638`, `:1712`) | ADAPT | `FactNodeOps.kt` (§4.2): the payload union and the payload delta replace the flags; the parameter `foldToAny` of `mergeAdd`/`mergeAddDelta` (`:815`, `:854`) and `trimAnyCoveredAndPushChildren` (`:965`) go |
| `TreeApManager.create`, `createElementAndField` (`AccessTree.kt:1784`, `:1806`) | ADAPT | `ApManager.node`: one shared leaf node per payload |
| `annotateAbstractNodes(cache)` (`AccessTree.kt:735`) | ADAPT | the identity memo of every node map (`mapPayloads`) |
| `filterAccessNode(FactApFilter)` (`AccessTree.kt:1031`) | ADAPT | `ApOps.filter` (§5.5): no `[any]` edge, no `FinalAccessor` check |
| `concatToLeafAbstractNodes` (`AccessTree.kt:1114`, `:1281`) | ADAPT | `graft` in `applySummary` (§5.4): no type filter, no element limit, no deep exclusion |
| `filterStartsWith` (`AccessTree.kt:1329`) | ADAPT | the run-1 part of `satisfying` (§5.4) |
| `internNodes` (`AccessTree.kt:1125`), `AccessTreeInterner` (`ap/ifds/access/tree/AccessTreeInterner.kt:8`) | ADAPT | `FactNodeInterner` (§4.5) |
| `TreeSetWithCompression.internIfRequired`, `AccessTreeSoftInterner` (`ap/ifds/access/tree/TreeSetWithCompression.kt:14`, `AccessTreeSoftInterner.kt:7`) | ADAPT | the intern policy of `TreeGroup` |
| `boundedDepthRaw`, `FieldLimiter.limit` (branch `saloed/any-field-limit`, `ap/ifds/access/tree/AccessTree.kt:298`, `:722`) | ADAPT | `FactNode.boundedDepth`, `ApOps.limit` (§5.7): no `[any]` edge to keep |
| `TreeApManager.isCounted` (branch, `ap/ifds/access/tree/TreeApManager.kt:79`) | ADAPT | `AccessorIdx.isCounted()`: field or element, no unroll strategy (`ap.md` §1) |
| `TreeFieldLimitCheck` (branch) | ADAPT | the test `FieldLimitTest` (§8) checks W3 on random trees |
| `TreeApManager` (`ap/ifds/access/tree/TreeApManager.kt:34`), `ap/ifds/access/ApManager.kt` | REPLACE | `bidi.ap.ApManager` (§5.1) |
| `AnyAccessorUnrollStrategy`, `AccessTreeAnySuffixMatcher`, `DeepAccessorExclusion` (`ap/ifds/access/DeepAccessorExclusion.kt:6`), `TreeInitialFactAbstraction`, mark/`$`/`[any]` accessors in paths | REPLACE | the `[any]` tail, the mark exclusion `*∖X`, the policy and the emission (§5.9; `ap.md` §6.2, §6.3, §7.6) |
| `AccessBasedStorage` (`ap/ifds/access/tree/AccessBasedStorage.kt:12`) | ADAPT | `PathTrie` (§7.2): keyed by `IntArray`, plain fastutil maps, `lookupPrefixes`/`lookupExtensions`/`around` |
| `AccessPathBaseStorage`, `MethodAnalyzerEdges.EdgeStorage` (`ap/ifds/AccessPathBaseStorage.kt:5`, `ap/ifds/MethodAnalyzerEdges.kt:240`) | REUSE (+ the `Zero` error branch) | the base level of `MethodEdgeStore`; the zero edges are in bit sets (§7.3) |
| `MethodAnalyzerEdges` (`ap/ifds/MethodAnalyzerEdges.kt:13`): `SameInitialZeroFactEdges` (`:150`), `instructionStorageIdx` (`:272`) | REUSE the structure | `MethodEdgeStore` (§7.3) |
| `EdgeNonUniverseExclusionMergingStorage` (`ap/ifds/access/tree/MethodEdgesInitialToFinalTreeApSet.kt:75`) | REPLACE | `TreeGroup` (the union of `:95` is forbidden by T3) |
| `MethodInitialToFinalApSummaries` (`ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt:13`) | REPLACE | `RunSummaryStore` (the union of `:271` is forbidden by T3) |
| `MethodTreeAccessPathSubscription`, `AccessTreeIndex` (`ap/ifds/access/tree/MethodTreeAccessPathSubscription.kt:22`, `:199`) | REPLACE | `PathTrie` (the delivery-side miss of `analyzer-core.md` Appendix A P4 goes) |
| `FactTypeChecker.FactApFilter`, `FilterResult` (`ap/ifds/FactTypeChecker.kt:27`, `:12`) | REUSE | `TypeFilter.may` (§5.5) |
| `TaintSinkTracker` rule assumptions and vulnerability nodes (`ap/ifds/taint/TaintSinkTracker.kt:15`) | REPLACE | `ConjunctionStore`, `VulnerabilityStore` (§7.10, §7.12) |
| `Edge` (`ZeroToZero`, `ZeroToFact`, `FactToFact`, `NDFactToFact`) | REPLACE | `PremiseKey` + `Layer` (DD3) |
| `Cancellation` (`util/Cancellation.kt:5`) | REUSE | `ApManager.cancellation.checkpoint()` in long walks |
| `LanguageManager.getInstIndex`, `getMaxInstIndex` (`ap/ifds/LanguageManager.kt:9`) | REUSE | the statement index of `MethodEdgeStore` |
| `CommonTaintConfigurationSink` (`configuration-rules-common`) | REUSE | `VulnerabilityKey.rule` |

---

## 3. The fact model (`ap.md` §2, §3.4, §7.1)

### 3.1 Accessors and marks

```kotlin
package org.opentaint.dataflow.bidi.ap

/** AccessorIdx <-> Accessor. ADAPT of AccessorInterner (ap/ifds/access/util/AccessorInterner.kt:19): the same index layout (REUSE of
 *  its companion, :94-137), a new storage. Today AccessorStorage.index reads a ConcurrentReadSafeObject2IntMap without a lock
 *  (:24-26). Its getInt re-reads non-volatile fields in a `while (true)` loop (ConcurrentReadSafeObject2IntMap.java:27-33).
 *  The JIT can hoist the reads, and the loop then never ends (analyzer-core.md Appendix A). AccessorTable uses a
 *  ConcurrentHashMap for value -> id and a volatile copy-on-write array for id -> value. A read has no retry loop. */
class AccessorTable {
    internal class Storage<T : Any> {
        private val ids = ConcurrentHashMap<T, Int>()
        @Volatile private var values: Array<Any?> = arrayOfNulls(64)
        private var size = 0                                                      // guarded by `this`

        fun index(v: T): Int = ids[v] ?: synchronized(this) {
            ids[v] ?: run {
                val i = size++
                val arr = if (i < values.size) values else values.copyOf(2 * values.size)
                arr[i] = v
                values = arr                                                      // the volatile write publishes arr[i]
                ids[v] = i                                                        // a reader gets i only after the publication
                i
            }
        }

        @Suppress("UNCHECKED_CAST")
        fun value(i: Int): T = values[i] as T                                     // one volatile read
    }

    private val fields = Storage<Accessor>()
    private val statics = Storage<Accessor>()
    private val types = Storage<Accessor>()

    fun index(a: Accessor): AccessorIdx = when (a) {
        is FieldAccessor -> setAccessorKind(fields.index(a), FIELD_KIND, BASIC_KIND_BITS)
        is ClassStaticAccessor -> setAccessorKind(statics.index(a), STATIC_KIND, BASIC_KIND_BITS)
        is TypeInfoAccessor -> setAccessorKind(types.index(a), TYPES_KIND, TYPES_OR_MARKER_KIND_BITS)
        ElementAccessor -> ELEMENT_ACCESSOR_IDX
        ValueAccessor -> VALUE_ACCESSOR_IDX
        TypeInfoGroupAccessor -> TYPE_INFO_GROUP_ACCESSOR_IDX
        is TaintMarkAccessor, FinalAccessor, AnyAccessor -> error("W5: $a is not an accessor of a path")
    }

    fun accessor(i: AccessorIdx): Accessor = when {                              // the decode of AccessorInterner.accessor (:70-92)
        i.isFieldAccessor() -> fields.value(i.getAccessorIdx(BASIC_KIND_BITS))
        i.isStaticAccessor() -> statics.value(i.getAccessorIdx(BASIC_KIND_BITS))
        i.isTypeInfoAccessor() -> types.value(i.getAccessorIdx(TYPES_OR_MARKER_KIND_BITS))
        i == ELEMENT_ACCESSOR_IDX -> ElementAccessor
        i == VALUE_ACCESSOR_IDX -> ValueAccessor
        i == TYPE_INFO_GROUP_ACCESSOR_IDX -> TypeInfoGroupAccessor
        else -> error("not a path accessor: $i")
    }
}

/** ap.md §1: a counted accessor is a field or an element accessor. The class accessor `<C>` is not counted. */
fun AccessorIdx.isCounted(): Boolean = isFieldAccessor() || this == ELEMENT_ACCESSOR_IDX

/** ap.md §4.1 `rootOrClass`: the class accessor `<C>` (`ClassStaticAccessor`). */
fun AccessorIdx.isClass(): Boolean = isStaticAccessor()

/** DD7: a concrete mark. The id is the index of its name in MarkTable. */
@JvmInline
value class TaintMark(val id: Int) {
    companion object { val ZERO = TaintMark(0) }                                 // ap.md §2.4: the zero mark; no rule names it
}

class MarkTable {
    private val names = AccessorTable.Storage<String>().also { check(it.index("<zero>") == 0) }
    fun mark(name: String): TaintMark = TaintMark(names.index(name))            // the JVM glue: marks.mark(jvmMark.name)
    fun name(m: TaintMark): String = names.value(m.id)
}
```

### 3.2 Tails, layers, marks, exclusions

```kotlin
enum class Direction { FORWARD, BACKWARD }                                        // ap.md §8.7
enum class Layer { NORMAL, DEMAND }                                               // ap.md §2.2
enum class Tail { STAR, ANY, EXACT }                                              // ap.md §2.1: `*`, `[any]`, `$`

/** The constants of one run that the AP operations read (ap.md §4.1, §4.4, §6.1). */
class ApMode(val run1: Boolean, val direction: Direction, val fieldLimit: Int) {
    val restricted: Boolean get() = !run1
    init { require(!run1 || (direction == Direction.FORWARD && fieldLimit >= 1)) }   // run 1 is forward; S12 (d): L >= 1
}

/** ap.md §3.4: the X of `*∖X`. Canonical: sorted ids, no duplicates. ApManager interns it (T6), so equal sets are mostly the
 *  same object; equals also compares the content, so a reference form can make a set without the manager. */
class MarkSet(@JvmField val ids: IntArray) {
    private val hash = ids.contentHashCode()
    val isEmpty: Boolean get() = ids.isEmpty()
    operator fun contains(m: TaintMark): Boolean = ids.binarySearch(m.id) >= 0
    fun isSubsetOf(o: MarkSet): Boolean = this === o || sortedSubset(ids, o.ids)
    operator fun plus(o: MarkSet): MarkSet = if (o.isSubsetOf(this)) this else MarkSet(sortedUnion(ids, o.ids))
    operator fun plus(m: TaintMark): MarkSet = if (m in this) this else MarkSet(sortedUnion(ids, intArrayOf(m.id)))
    operator fun minus(o: MarkSet): MarkSet = MarkSet(ids.filter { it !in o.ids }.toIntArray())   // canonical stays canonical
    fun intersect(o: MarkSet): MarkSet = MarkSet(ids.filter { o.ids.binarySearch(it) >= 0 }.toIntArray())
    override fun equals(other: Any?) = this === other || (other is MarkSet && hash == other.hash && ids.contentEquals(other.ids))
    override fun hashCode() = hash
    companion object { val EMPTY = MarkSet(IntArray(0)) }
}

/** ap.md §3.4. `*` is Star(MarkSet.EMPTY). A premise has `*` or a concrete mark (§2.2). */
sealed interface MarkSlot {
    data class Star(val excluded: MarkSet) : MarkSlot                            // `*` or `*∖X`
    data class Concrete(val mark: TaintMark) : MarkSlot                           // `T`; the zero mark is concrete
    companion object { val STAR = Star(MarkSet.EMPTY) }
}

/** ap.md §3.4: the exclusion E. No Universe (§1, S8). Concrete is never empty. REPLACE of ap/ifds/ExclusionSet.kt. */
sealed interface ExclusionSet {
    fun admits(first: AccessorIdx): Boolean                                       // r = [first, ...]: the first accessor is not in E
    fun admits(r: List<AccessorIdx>): Boolean = r.isEmpty() || admits(r[0])
    fun union(o: ExclusionSet): ExclusionSet                                      // along one derivation only (§3.3)
    fun intersect(o: ExclusionSet): ExclusionSet                                  // merge rule 2 (§3.3)
    fun isSubsetOf(o: ExclusionSet): Boolean

    data object Empty : ExclusionSet {
        override fun admits(first: AccessorIdx) = true
        override fun union(o: ExclusionSet) = o
        override fun intersect(o: ExclusionSet) = Empty
        override fun isSubsetOf(o: ExclusionSet) = true
    }

    class Concrete internal constructor(@JvmField val ids: IntArray) : ExclusionSet {   // sorted AccessorIdx
        private val hash = ids.contentHashCode()
        override fun admits(first: AccessorIdx) = ids.binarySearch(first) < 0
        override fun union(o: ExclusionSet) = if (o is Concrete) of(sortedUnion(ids, o.ids)) else this
        override fun intersect(o: ExclusionSet) = if (o is Concrete) of(ids.filter { o.ids.binarySearch(it) >= 0 }.toIntArray()) else Empty
        override fun isSubsetOf(o: ExclusionSet) = o is Concrete && sortedSubset(ids, o.ids)
        override fun equals(other: Any?) = this === other || (other is Concrete && hash == other.hash && ids.contentEquals(other.ids))
        override fun hashCode() = hash
    }

    companion object {
        /** The only factories: an empty set is Empty (ap.md §3.4). ApManager.intern makes it the shared object. */
        fun of(ids: IntArray): ExclusionSet = if (ids.isEmpty()) Empty else Concrete(ids.sortedDistinct())
        /** `{a}`: the exclusion of one keep edge (interpreter.md §2.1 `strongKeep`). */
        fun of(a: AccessorIdx): ExclusionSet = Concrete(intArrayOf(a))
    }
}
```

### 3.3 `PathNode`

```kotlin
/** ap.md §7.1: the concrete path of a premise, a position or a demand chain, linked from the root. No `[any]`, `$` or mark
 *  accessor (W4, W5). ADAPT of AccessPath.AccessNode (ap/ifds/access/tree/AccessPath.kt:261): the same (accessor, next) cell with a
 *  cached hash and size. Changes: no `manager` field; ApManager.path interns every node, so equality is identity; no
 *  `addParent`. The old `addParent` (:316) collapses a repeated field (`limitFieldAccess`, :375) and long element chains
 *  (`limitElementAccess`, :354). These are depth bounds; the field limit must be the only one (ap.md §4.4). */
class PathNode internal constructor(@JvmField val accessor: AccessorIdx, @JvmField val next: PathNode?) {
    @JvmField val size: Int = 1 + (next?.size ?: 0)
    @JvmField val counted: Int = (if (accessor.isCounted()) 1 else 0) + (next?.counted ?: 0)  // W3 checks
    private val hash: Int = accessor + 17 * (next?.hashCode() ?: 0)

    /** Shallow: `next` is interned. The interner of ApManager uses it; after interning it is identity. */
    override fun equals(other: Any?) = this === other || (other is PathNode && accessor == other.accessor && next === other.next)
    override fun hashCode() = hash

    fun toIntArray(): IntArray = IntArray(size).also { var n: PathNode? = this; var i = 0; while (n != null) { it[i++] = n.accessor; n = n.next } }
    fun toList(): List<AccessorIdx> = toIntArray().asList()
}
```

### 3.4 `InitialAp`, `PremiseKey`, the zero fact

```kotlin
/** ap.md §7.1: the premise. ApManager.initial interns it: equality is identity (DD5). */
class InitialAp internal constructor(
    val base: AccessPathBase,
    val path: PathNode?,
    val tail: Tail,
    val exclusion: ExclusionSet,                  // Empty unless STAR; a restricted run can emit a `*/E` demand exclusion (§6.3)
    val mark: MarkSlot,                           // `*` or `T`, never `*∖X` (§2.2)
    @JvmField val id: Int,                        // the intern order: the sort key of PremiseKey
    @JvmField internal val manager: ApManager,    // Record.reversedAt (Part I §7.8) interns the reversed premise
) {
    init {
        check(mark !is MarkSlot.Star || mark.excluded.isEmpty)
        check(tail == Tail.STAR || exclusion == ExclusionSet.Empty)
    }
    @JvmField val pathArray: IntArray = path?.toIntArray() ?: EMPTY_PATH
    val isZero: Boolean get() = base == AccessPathBase.Zero
    fun toPattern(): Pattern = Pattern(PathFact(base, pathArray.asList(), tail, mark), exclusion)
}

/** ap.md §7.1, §4.6: the premise SET. Interned: equal sets are the same object. Sorted by id, no duplicates, never empty. */
class PremiseKey internal constructor(val initials: List<InitialAp>) {
    val single: InitialAp? get() = initials.singleOrNull()
    val isZero: Boolean get() = initials.size == 1 && initials[0].isZero
    /** §4.6: 0 = zero-to-fact edge, 1 = fact-to-fact edge, >= 2 = ND edge (DD3). */
    val nonZeroCount: Int get() = initials.count { !it.isZero }
}

// In ApManager (Part I §5.1):
//   val zero: InitialAp = initial(AccessPathBase.Zero, null, Tail.EXACT, ExclusionSet.Empty, MarkSlot.Concrete(TaintMark.ZERO))
//   val zeroPremise: PremiseKey = premiseKey(listOf(zero))
//   val zeroTree: EdgeTree = tree(Zero, Empty, EMPTY, demand = false, leaf(Payload(exact = {zeroMark})))      // ap.md §2.4
```

---

## 4. Trees (`ap.md` §7.2, §7.5, §8.1)

### 4.1 `LeafMarks`, `Payload`, `FactNode`, `EdgeTree`

```kotlin
/** ap.md §7.2. `star`: a leaf with the abstract mark `*∖X` of its tree. Interned by ApManager (T6): the factory returns
 *  EMPTY and STAR for an empty concrete set, so these two are the only objects with that content. */
class LeafMarks internal constructor(@JvmField val star: Boolean, @JvmField val concrete: MarkSet) {
    val isEmpty: Boolean get() = !star && concrete.isEmpty
    companion object {
        @JvmField val EMPTY = LeafMarks(false, MarkSet.EMPTY)
        @JvmField val STAR = LeafMarks(true, MarkSet.EMPTY)                    // one abstract-mark leaf, no concrete mark
    }
}

/** ap.md §7.2. Interned (T6): ONE empty payload, Payload.EMPTY (ApManager.payload returns it). FactNode equality and its
 *  hash read payloads by identity, so the factories must never make a second empty payload. */
class Payload internal constructor(@JvmField val star: Boolean, @JvmField val any: LeafMarks, @JvmField val exact: LeafMarks) {
    val isEmpty: Boolean get() = !star && any.isEmpty && exact.isEmpty
    val hasAbstractMark: Boolean get() = star || any.star || exact.star
    companion object { @JvmField val EMPTY = Payload(false, LeafMarks.EMPTY, LeafMarks.EMPTY) }
}

/** ap.md §7.2. ADAPT of AccessTree.AccessNode (ap/ifds/access/tree/AccessTree.kt:261). Immutable. */
class FactNode internal constructor(
    @JvmField val payload: Payload,
    @JvmField val accessors: IntArray?,          // sorted AccessorIdx, as today
    @JvmField val children: Array<FactNode>?,
    @JvmField val interned: Boolean,
) {
    @JvmField val hash: Long                     // structural (AccessTree.kt:281), with the child accessor
    @JvmField val boundedDepth: Short            // max counted accessors on a path below (Part I §4.5); not in the hash
    @JvmField val hasStar: Boolean               // a `*` leaf at or below: W2 checks, lostCorr
    @JvmField val hasAny: Boolean                // an `[any]` leaf at or below: the W6 split
    @JvmField val hasAbstractMark: Boolean       // a `*∖X` leaf at or below: N2, the sink check
    @JvmField val size: Long                     // nodes, shared subtrees counted again (AccessTree.kt:316-322): the intern policy
    @JvmField internal var allMarks: LeafMarks? = null   // lazy fold of every leaf mark; a benign race (immutable value)

    init {
        var h = System.identityHashCode(payload).toLong()
        var depth = 0
        var star = payload.star; var any = !payload.any.isEmpty; var abs = payload.hasAbstractMark
        var count = 1L
        if (children != null) for (i in children.indices) {
            val c = children[i]
            count += c.size
            h += (c.hash * 31 + accessors!![i]) shl 5
            val d = c.boundedDepth + if (accessors[i].isCounted()) 1 else 0
            if (d > depth) depth = d
            star = star || c.hasStar; any = any || c.hasAny; abs = abs || c.hasAbstractMark
        }
        hash = h
        boundedDepth = minOf(depth, Short.MAX_VALUE.toInt()).toShort()   // saturating, as branch any-field-limit AccessTree.kt:366
        hasStar = star; hasAny = any; hasAbstractMark = abs; size = count
    }

    val isEmpty: Boolean get() = payload.isEmpty && accessors == null
    fun child(a: AccessorIdx): FactNode? =                                // getNodeByAccessor (AccessTree.kt:385)
        accessors?.binarySearch(a)?.let { if (it >= 0) children!![it] else null }
    override fun hashCode() = hash.toInt()
    override fun equals(other: Any?): Boolean =                            // AccessNode.equals (:326) with payload identity
        this === other || (other is FactNode && hash == other.hash && payload === other.payload &&
            accessors.contentEquals(other.accessors) && children.contentEquals(other.children))
}

/** ap.md §7.2: one edge group. ApManager.tree makes the canonical form:
 *  N1 (W1) no `*` leaf => exclusion = Empty;  N2 no abstract-mark leaf => markExclusion = EMPTY;
 *  W2 demand => no `*` leaf;  W6 normal => no `[any]` leaf;  the root and every subtree are not empty. */
class EdgeTree internal constructor(
    val base: AccessPathBase,
    val exclusion: ExclusionSet,
    val markExclusion: MarkSet,
    val demand: Boolean,
    val root: FactNode,
) {
    val layer: Layer get() = if (demand) Layer.DEMAND else Layer.NORMAL
    internal fun withRoot(r: FactNode): EdgeTree = EdgeTree(base, exclusion, markExclusion, demand, r)

    /** Value equality (structural root, Part I §4.5). The analyzer compares trees by value: the edge-delta deduplication
     *  (the unchanged set of one Work event; EdgeDelta is a data class), the deduplication of ConjunctionStore.Input
     *  (Part I §7.10), and the split of a summary delta into its identity part and its effect part (`summaryParts` of
     *  analyzer-impl.md §4.6: by the tree key and ApOps.without). */
    override fun equals(other: Any?): Boolean = this === other || (other is EdgeTree && demand == other.demand &&
        base == other.base && exclusion == other.exclusion && markExclusion == other.markExclusion && root == other.root)
    override fun hashCode(): Int = ((root.hashCode() * 31 + base.hashCode()) * 31 + exclusion.hashCode()) * 31 +
        markExclusion.hashCode() * 2 + (if (demand) 1 else 0)
}
```

A normal tree holds `*` and `$` leaves; a demand tree holds `[any]` and `$` leaves (W2, W6). One tree holds abstract marks
or concrete marks, not both: a `*` premise has only abstract conclusions (S7), a concrete premise only concrete ones
(`Coverage.edge_conc`). `checkSink` (§5.8) asserts it.

### 4.2 T1 merge and T4 delta

`mergeAdd` and `mergeAddDelta` keep the iterative pair loop of today. Only the step changes:

```kotlin
// FactNodeOps.kt. ADAPT of AccessNode.mergeAddDeltaStep (AccessTree.kt:859). `mergeNodeLoop` (:912) and `mergeAccessorsRaw`
// (:1388) are copied as they are. The parameter `foldToAny` (:815, :854) and `trimAnyCoveredAndPushChildren` (:965) go
// (no `[any]` edge): the loop always calls `pushSharedChildPairs` (:1005).
internal fun ApManager.mergeAddDeltaStep(
    a: FactNode, b: FactNode, results: Object2ObjectOpenHashMap<NodePair, Pair<FactNode, FactNode?>>,
): Pair<FactNode, FactNode?> {
    val payload = union(a.payload, b.payload)                 // was: isAbstract ||, isFinal ||, intersectDeepExclusion
    val payloadDelta = minus(b.payload, a.payload)            // was: isAbstractDelta, isFinalDelta, deltaDeepExclusion
    val deltaAccessors = IntArrayList()
    val deltaNodes = ArrayList<FactNode>()
    val merged = mergeAccessors(a, b.accessors, b.children,
        onOtherNode = { acc, n -> deltaAccessors.add(acc); deltaNodes.add(n) }) { acc, x, y ->
        val (node, delta) = results.getComputedResult(NodePair(x, y))
        if (delta != null) { deltaAccessors.add(acc); deltaNodes.add(delta) }
        node
    }
    if (payload === a.payload && merged == null) return a to null
    val delta = node(payloadDelta, deltaAccessors.toIntArray(), deltaNodes.toTypedArray()).takeIf { !it.isEmpty }
    return node(payload, merged?.first ?: a.accessors, merged?.second ?: a.children) to delta
}

internal fun ApManager.union(p: Payload, q: Payload): Payload =           // interned: union(p, p) === p
    payload(p.star || q.star, leafMarks(p.any.star || q.any.star, p.any.concrete + q.any.concrete),
            leafMarks(p.exact.star || q.exact.star, p.exact.concrete + q.exact.concrete))

internal fun ApManager.minus(p: Payload, q: Payload): Payload =           // the leaves of p that q does not have
    payload(p.star && !q.star, leafMarks(p.any.star && !q.any.star, p.any.concrete - q.any.concrete),
            leafMarks(p.exact.star && !q.exact.star, p.exact.concrete - q.exact.concrete))
```

T1 (`Tree.rule1_mem`): two trees with the same key merge by `mergeAdd`. T4: `mergeAddDelta` returns the new part only.

### 4.3 T2, T2', T3 and the subsumption of `ap.md` §8.1: `TreeGroup`

`TreeGroup` holds the trees of one (statement, premise key, base) in both layers. `MethodEdgeStore`, `RunSummaryStore`
and `RecordStore` use it.

```kotlin
/** ap.md §7.2 T1–T5 and §8.1. Single writer. REPLACE of EdgeNonUniverseExclusionMergingStorage
 *  (ap/ifds/access/tree/MethodEdgesInitialToFinalTreeApSet.kt:75): it unions exclusions across edges (:95), which T3 forbids
 *  (Subsume.union_loses_pairs). */
class TreeGroup(private val m: ApManager, private val interner: FactNodeInterner) {
    private val trees = arrayOf(ArrayList<EdgeTree>(1), ArrayList<EdgeTree>(1))          // NORMAL, DEMAND: T3, no merge across layers

    fun trees(): Sequence<EdgeTree> = trees[0].asSequence() + trees[1].asSequence()

    /** Returns the delta (T4) or null if `t` adds nothing. */
    fun add(t: EdgeTree): EdgeTree? {
        val list = trees[t.layer.ordinal]
        val i = list.indexOfFirst { it.exclusion == t.exclusion && it.markExclusion == t.markExclusion }
        if (i >= 0) {                                                                     // T1: the same key
            // §8.1 FIRST, against every tree of the layer, the same-key tree included: a leaf that the stored tree has, or
            // that one of its `[any]` leaves absorbed (T5), is not new. Without this, an absorbed leaf is a delta on every
            // arrival, and a loop never empties the worklist.
            val rest = m.subtractSubsumed(t, list, skip = -1) ?: return null
            val (merged, delta) = m.mergeAddDelta(list[i].root, rest.root)
            val d = delta ?: return null
            val kept = if (t.demand) m.foldUnderAny(merged) ?: merged else merged          // T5 on the stored tree (Part I §4.4)
            list[i] = list[i].withRoot(interner.internIfRequired(kept))                   // the policy of Part I §4.5
            return m.tree(t.base, t.exclusion, t.markExclusion, t.demand, d)              // canonical: the delta can have no `*` leaf
        }
        val k = list.indexOfFirst { it.root == t.root &&                                  // EQUAL content (Tree.rule2_den)
            (it.markExclusion == t.markExclusion || it.exclusion == t.exclusion) }
        if (k >= 0) {                                                                     // T2 / T2': intersect, never union
            val s = list[k]
            val merged = m.tree(t.base, s.exclusion.intersect(t.exclusion), s.markExclusion.intersect(t.markExclusion), t.demand, s.root)
            if (merged.exclusion == s.exclusion && merged.markExclusion == s.markExclusion) return null   // s already covers t
            list.removeAt(k)
            return add(merged)                         // T4 exception: the WHOLE merged tree (or its delta to a tree with that key)
        }
        val fresh = m.subtractSubsumed(t, list, skip = -1) ?: return null                // §8.1
        list += fresh.withRoot(interner.internIfRequired(fresh.root))
        return fresh
    }
}

/** ap.md §8.1 (Subsume.subsumesB, markSubsB): the part of `t` that no other tree of the same premise key, layer and base
 *  subsumes. `[any]` at p subsumes every leaf at or below p; `*/Es` subsumes `*/En` at p if Es ⊆ En; `$` subsumes `$` at p;
 *  marks: the same concrete mark, or `*∖Xs` over `*∖Xn` with Xs ⊆ Xn. One layer only: a demand leaf never drops a normal one. */
internal fun ApManager.subtractSubsumed(t: EdgeTree, others: List<EdgeTree>, skip: Int): EdgeTree? {
    var root: FactNode = t.root
    for ((i, s) in others.withIndex()) {
        if (i == skip) continue
        root = subtract(root, s.root, LeafMarks.EMPTY, starOk = s.exclusion.isSubsetOf(t.exclusion),
            markOk = s.markExclusion.isSubsetOf(t.markExclusion)) ?: return null
    }
    return if (root === t.root) t else tree(t.base, t.exclusion, t.markExclusion, t.demand, root)
}

private fun ApManager.subtract(n: FactNode, s: FactNode?, anyAbove: LeafMarks, starOk: Boolean, markOk: Boolean): FactNode? {
    val any = if (s == null) anyAbove else unionMarks(anyAbove, s.payload.any)        // the `[any]` leaves of s at or above n
    if (s == null && any.isEmpty) return n                                           // nothing subsumes below: share
    val pl = n.payload
    val kept = payload(
        star = pl.star && !(s?.payload?.star == true && starOk && markOk),
        any = minusSubsumed(pl.any, any, markOk),
        exact = minusSubsumed(minusSubsumed(pl.exact, s?.payload?.exact, markOk), any, markOk))
    return mapChildren(n, kept) { a, c -> subtract(c, s?.child(a), any, starOk, markOk) }   // null when empty
}

private fun ApManager.minusSubsumed(ms: LeafMarks, by: LeafMarks?, markOk: Boolean): LeafMarks =
    if (by == null) ms else leafMarks(ms.star && !(by.star && markOk), ms.concrete - by.concrete)
```

The subscriptions and the links do not use subsumption (`analyzer-core.md` §5.3): `AddedFactStore` and `RequestStore`
deduplicate exactly (§7.5, §7.9).

### 4.4 T5: the fold under `[any]`

```kotlin
/** T5 (ap.md §7.2): inside ONE demand tree, an `[any]` leaf with the mark m at p absorbs every leaf with the mark m strictly
 *  below p. The denotation does not change (argued, ap.md §11.2). TreeGroup applies it to the STORED tree after the delta is
 *  computed, so a fold never hides a new leaf from the delta. */
internal fun ApManager.foldUnderAny(n: FactNode, above: LeafMarks = LeafMarks.EMPTY): FactNode? {
    if (above.isEmpty && !n.hasAny) return n
    val pl = n.payload
    val kept = payload(pl.star, minusSubsumed(pl.any, above, true), minusSubsumed(pl.exact, above, true))
    val below = unionMarks(above, pl.any)
    return mapChildren(n, kept) { _, c -> foldUnderAny(c, below) }
}
```

### 4.5 T6 interning and `boundedDepth`

```kotlin
/** T6, ap.md §7.5: bottom-up hash-consing. ADAPT of AccessTreeInterner (ap/ifds/access/tree/AccessTreeInterner.kt:8) and of
 *  AccessNode.internNodes (AccessTree.kt:1125): the strategy compares the payload by identity (payloads are interned by
 *  the one ApManager), the accessors by content and the children by identity. Not thread-safe: one per store
 *  (owner-local, Part I §7.1; DD5). */
class FactNodeInterner {
    private val table = Long2ObjectOpenHashMap<Object2ObjectOpenCustomHashMap<FactNode, FactNode>>()
    private var operationsBeforeIntern = INTERN_RATE

    /** A node with `interned = true` (this store or another one made it) stays as it is: the loop of :1130-1172. */
    fun intern(n: FactNode): FactNode = if (n.interned) n else internBottomUp(n, IdentityHashMap())

    /** The policy of TreeSetWithCompression (ap/ifds/access/tree/TreeSetWithCompression.kt:14-29): a large tree at once,
     *  else one tree in INTERN_RATE adds when it is not small. TreeGroup calls it on every stored tree. */
    fun internIfRequired(n: FactNode): FactNode = when {
        n.size >= SIZE_TO_FORCE_INTERN -> intern(n)
        --operationsBeforeIntern > 0 || n.size < MIN_SIZE_TO_INTERN -> n
        else -> { operationsBeforeIntern = INTERN_RATE; intern(n) }
    }

    companion object { const val MIN_SIZE_TO_INTERN = 100L; const val SIZE_TO_FORCE_INTERN = 100_000L; const val INTERN_RATE = 100 }
}
```

`FactNode.size` (§4.1) is the node count with shared subtrees counted again, as `AccessNode.size` (`AccessTree.kt:316-322`).

EQUALITY ACROSS INTERNERS (DD5). Each store has its own interner, so two equal nodes of two stores can be two
objects. A callee publication tree (from the callee `RunSummaryStore`) meets a caller subscription tree (from the
caller `AddedFactStore`) in `satisfying`, `applySummary` and the `TreeGroup` of the caller. So no operation reads
identity as equality. `FactNode.equals` and `hashCode` (§4.1) are structural:

```kotlin
// FactNode (Part I §4.1): identity is only a fast path.
override fun equals(other: Any?): Boolean =
    this === other ||                                                   // the fast path: the same interner, or a shared subtree
    (other is FactNode && hash == other.hash &&                          // a structural hash: equal for equal content in any store
     payload === other.payload &&                                        // payloads are interned by the ONE ApManager: identity is exact
     accessors.contentEquals(other.accessors) &&
     children.contentEquals(other.children))                            // recursive equals: the same rule one level down
```

| Place | Why it is correct with two interners |
|---|---|
| `FactNode.hash` | it reads the payload by its identity hash (one `ApManager` interns every payload, §5.1) and the children by their structural hash: the same value for equal content in every store |
| `FactNodeInterner` | it compares children by identity, which is exact inside one interner (bottom-up: equal children are one object there). A node that another store interned stays as it is: it is immutable and equality is structural, so this is correct; it only is not shared with the equal nodes of this store |
| `mergeNodeLoop` | identity pairs (`NodePair`) are only a memo and `a === b` only a shortcut: two equal nodes of two stores take the full merge, with the same result |
| T2 (§4.3), `minusNode` (§5.8), `EdgeTree.equals` (§4.1) | they use `==`, so they also work for a tree that another store made |

`boundedDepth` is the number of counted accessors on the longest path below a node (§4.1). It is part of the node and not
of the hash (`ap.md` §7.5). `limit` reads it: a tree with `root.boundedDepth <= L` needs no walk (O(1) check, §5.7).

---

## 5. `ApManager` and `ApOps` (`ap.md` §4, §6.3–§6.5, §7.3, §7.4, §9.1)

### 5.1 `ApManager`

```kotlin
/** The interners and the factories of the AP. One per analysis (analyzer-core.md §2). Thread-safe (O4): every shared table is
 *  a ConcurrentHashMap (lock-free reads that are correct under the JMM) or the copy-on-write arrays of Part I §3.1. No
 *  ConcurrentReadSafe map. FactNode hash-consing is owner-local (Part I §4.5, DD5), so no FactNode table is shared, and no
 *  run leaks its trees into the next run. */
class ApManager(val cancellation: Cancellation) {
    val accessors = AccessorTable()
    val marks = MarkTable()

    private val markSets = ConcurrentHashMap<MarkSet, MarkSet>()
    private val exclusions = ConcurrentHashMap<ExclusionSet, ExclusionSet>()
    private val paths = ConcurrentHashMap<PathNode, PathNode>()
    private val initials = ConcurrentHashMap<InitialKey, InitialAp>()
    private val premises = ConcurrentHashMap<List<InitialAp>, PremiseKey>()
    private val leafMarkTable = ConcurrentHashMap<LeafMarksKey, LeafMarks>()
    private val payloads = ConcurrentHashMap<PayloadKey, Payload>()
    private val leaves = ConcurrentHashMap<Payload, FactNode>()                  // one shared leaf node per payload (AccessTree.kt:1806)
    private val nextId = AtomicInteger()

    fun intern(s: MarkSet): MarkSet = if (s.isEmpty) MarkSet.EMPTY else markSets.putIfAbsent(s, s) ?: s
    fun intern(e: ExclusionSet): ExclusionSet = if (e == ExclusionSet.Empty) e else exclusions.putIfAbsent(e, e) ?: e
    fun path(a: AccessorIdx, next: PathNode?): PathNode = PathNode(a, next).let { paths.putIfAbsent(it, it) ?: it }
    fun path(p: List<AccessorIdx>): PathNode? = p.foldRight(null as PathNode?) { a, n -> path(a, n) }
    fun path(p: IntArray): PathNode? = p.foldRight(null as PathNode?) { a, n -> path(a, n) }

    /** §4.10: a position is the path cut to at most two accessors (`[<C>, f]` or `[<C>]`). */
    fun position(p: IntArray): PathNode = checkNotNull(path(p.copyOf(minOf(2, p.size))))

    fun initial(base: AccessPathBase, path: PathNode?, tail: Tail, exclusion: ExclusionSet, mark: MarkSlot): InitialAp =
        initials.computeIfAbsent(InitialKey(base, path, tail, intern(exclusion), mark)) { k ->
            InitialAp(k.base, k.path, k.tail, k.exclusion, k.mark, nextId.getAndIncrement(), this)
        }
    fun initial(p: Pattern): InitialAp = initial(p.fact.base, path(p.fact.path), p.fact.tail, p.exclusion, p.fact.mark)

    fun premiseKey(members: Collection<InitialAp>): PremiseKey {
        val sorted = members.distinct().sortedBy { it.id }
        check(sorted.isNotEmpty())
        return premises.computeIfAbsent(sorted, ::PremiseKey)
    }

    val zero: InitialAp = initial(AccessPathBase.Zero, null, Tail.EXACT, ExclusionSet.Empty, MarkSlot.Concrete(TaintMark.ZERO))
    val zeroPremise: PremiseKey = premiseKey(listOf(zero))
    val zeroTree: EdgeTree = tree(AccessPathBase.Zero, ExclusionSet.Empty, MarkSet.EMPTY, false,
        leaf(payload(exact = leafMarks(false, markSetOf(TaintMark.ZERO)))))
    val zeroTreeDemand: EdgeTree = tree(AccessPathBase.Zero, ExclusionSet.Empty, MarkSet.EMPTY, true, zeroTree.root)

    /** T6: the shared empties come back as themselves, so identity is exact for every payload and leaf-mark value. */
    fun leafMarks(star: Boolean, concrete: MarkSet): LeafMarks = when {
        concrete.isEmpty -> if (star) LeafMarks.STAR else LeafMarks.EMPTY
        else -> leafMarkTable.computeIfAbsent(LeafMarksKey(star, intern(concrete))) { LeafMarks(it.star, it.concrete) }
    }
    fun payload(star: Boolean = false, any: LeafMarks = LeafMarks.EMPTY, exact: LeafMarks = LeafMarks.EMPTY): Payload =
        if (!star && any === LeafMarks.EMPTY && exact === LeafMarks.EMPTY) Payload.EMPTY
        else payloads.computeIfAbsent(PayloadKey(star, any, exact)) { Payload(it.star, it.any, it.exact) }   // `any`, `exact` interned: identity keys
    fun leaf(p: Payload): FactNode = leaves.computeIfAbsent(p) { FactNode(it, null, null, interned = true) }

    /** ADAPT of TreeApManager.create (AccessTree.kt:1784): the shared leaf when there is no child. */
    fun node(p: Payload, accessors: IntArray?, children: Array<FactNode>?): FactNode =
        if (accessors == null || accessors.isEmpty()) leaf(p) else FactNode(p, accessors, children, interned = false)

    /** `path ++ n`: n under the accessors of `path` (Tree.prependPath). */
    fun prepend(path: PathNode?, n: FactNode): FactNode =
        path?.toIntArray()?.foldRight(n) { a, acc -> node(Payload.EMPTY, intArrayOf(a), arrayOf(acc)) } ?: n

    /** The canonical form of Part I §4.1. Every tree that leaves an operation goes through here. */
    fun tree(base: AccessPathBase, exclusion: ExclusionSet, mx: MarkSet, demand: Boolean, root: FactNode): EdgeTree {
        check(!root.isEmpty)
        check(!demand || !root.hasStar) { "W2" }
        check(demand || !root.hasAny) { "W6" }
        return EdgeTree(base, if (root.hasStar) intern(exclusion) else ExclusionSet.Empty,
            if (root.hasAbstractMark) intern(mx) else MarkSet.EMPTY, demand, root)
    }

    fun newNodeInterner(): FactNodeInterner = FactNodeInterner()
}
```

The other node functions of `FactNodeOps.kt` are extension functions on `ApManager`. Each returns `null` for an empty
node, and each map has an identity memo for one call (as `annotateAbstractNodes`, `AccessTree.kt:735`):

| Function | Result |
|---|---|
| `mergeAdd`, `mergeAddDelta` | T1, T4 (§4.2) |
| `foldUnderAny(n)` | T5 (§4.4) |
| `mapChildren(n, payload, f)` | `n` with a new payload and each child `c` at `a` replaced by `f(a, c)` (ADAPT of `transformAccessors`, `AccessTree.kt:1461`) |
| `replaceChild(n, payload, a, c)` | `n` with a new payload and the child at `a` replaced by `c` |
| `mapPayloads(n, f)` | every payload of the subtree replaced by `f(payload)` |
| `retainChildren(n, pred)` | a node with the empty payload and only the children whose accessor `pred` accepts |
| `foldMarks(n, pred, starTails)` | every leaf mark of the payload of `n` and of the accepted children, `*` leaves only if `starTails`; the full fold is cached in `FactNode.allMarks` |
| `onlyMark(n, t)`, `onlyMarksOf(slot, n)` | the leaves with the concrete mark `t` (`onlyMarksOf(Star, n) = n`; `markSub` of `ap.md` §3.4) |
| `onlyAny(n)`, `splitAny(n)`, `starToAny(n)` | the `[any]` leaves; (without them, them); every `*` flag as `any.star` (W2) |
| `minusNode(n, k)`, `coveredBy(n, lit)` | the leaves of `n` not in `k`; the leaves of `n` that the literal covers (`coversB`) |
| `chain(path, payloads)` | one payload per depth on one path, no other child |
| `forEachLeaf(n, prefix, f)`, `forEachLeafPosition(n, f)` | `f(path, tail, marks)` per leaf kind; `f(path)` per node with a leaf |
| `leafKinds(g)`, `graft(g, kind, r)` | the (tail, mark) kinds of the leaves of g; §5.4 |
| `markSetOf(t)`, `unionMarks`, `withStar(ms, b)`, `payloadOf(tail, ms)` | small interned values, through `leafMarks`/`payload`, so the shared empties `LeafMarks.EMPTY`, `LeafMarks.STAR`, `Payload.EMPTY` come back as themselves |
| `treeOf(fact, exclusion, demand)` | a one-leaf tree of a `PathFact`, through `tree` (W2, W6 applied) |
| `class LeafKind(val tail: Tail, val mark: MarkSlot) { fun occursIn(p: Payload): Boolean }` | one (tail, mark) kind of leaf of a summary tree (`applySummary`, §5.4); `occursIn`: the payload has a leaf of this tail with this mark (`Star` = the abstract flag of that tail) |
| `fun IntArray.startsWith(p: IntArray): Boolean` | `p` is a prefix (the `startsWith` of `ap.md` §3.4 on arrays) |
| `fun IntArray.sortedDistinct(): IntArray`, `fun sortedUnion(a: IntArray, b: IntArray): IntArray`, `fun sortedSubset(a: IntArray, b: IntArray): Boolean` (in `Facts.kt`) | the canonical sets of §3.2: sort and drop duplicates; a merge walk of two sorted arrays; every element of `a` is in `b` |

### 5.2 `ApOut` and the result groups

```kotlin
/** Receives the results of one operation on one input tree. Requests exist only in run 1. */
interface ApOut {
    fun result(tree: EdgeTree)                    // one result group: its own layer, exclusion, mark exclusion
    fun markRequest(mark: TaintMark)              // ap.md §4.5, on the premise of the input edge
    fun positionRequest(position: PathNode)       // ap.md §4.10 item 1, the path cut to <= 2 accessors
}

/** ap.md §7.3 steps 5 to 7: the results of one operation, one FactNode per (layer, exclusion, mark exclusion). */
internal class Results(private val m: ApManager, private val base: AccessPathBase) {
    private data class Key(val demand: Boolean, val exclusion: ExclusionSet, val mx: MarkSet)
    private val groups = LinkedHashMap<Key, FactNode>(4)

    /** The key is canonical at once (N1, N2 of Part I §4.1), so one operation emits one tree per canonical key. */
    fun add(demand: Boolean, exclusion: ExclusionSet, mx: MarkSet, node: FactNode) {
        val k = Key(demand,
            if (demand || !node.hasStar) ExclusionSet.Empty else exclusion,      // a demand tree has no `*` leaf (W2); W1
            if (node.hasAbstractMark) mx else MarkSet.EMPTY)                     // N2
        groups[k] = groups[k]?.let { m.mergeAdd(it, node) } ?: node
    }

    fun flush(out: ApOut) {
        for (k in groups.keys.filter { !it.demand }) {                         // W6: an `[any]` leaf leaves the normal layer
            val (plain, any) = m.splitAny(groups.getValue(k))
            if (plain == null) groups.remove(k) else groups[k] = plain
            if (any != null) add(true, ExclusionSet.Empty, k.mx, any)
        }
        for ((k, n) in groups)                                                  // W2: a demand `*` leaf becomes `[any]`
            out.result(m.tree(base, k.exclusion, k.mx, k.demand, if (k.demand) m.starToAny(n) else n))
        groups.clear()
    }
}

/** An ApOut that keeps everything: tests, graft (Part I §5.4), the barrier. */
class CollectingOut : ApOut {
    val trees = ArrayList<EdgeTree>(); val markRequests = ArrayList<TaintMark>(); val positionRequests = ArrayList<PathNode>()
    override fun result(tree: EdgeTree) { trees += tree }
    override fun markRequest(mark: TaintMark) { markRequests += mark }
    override fun positionRequest(position: PathNode) { positionRequests += position }
}
```

### 5.3 The facade and `applyEdge` (`ap.md` §4.1, §4.2 step 4, §7.3)

```kotlin
/** The facade of the AP operations. Stateless: every memo is local to one call, so one instance serves every thread. */
class ApOps(val manager: ApManager) {
    private val m get() = manager

    fun applyEdge(c: EdgeTree, premise: PremiseKey, e: PathEdge, statementEdge: Boolean, mode: ApMode, out: ApOut) {
        val ce = e.compiled ?: m.compile(e).also { e.compiled = it }                 // §7.5: the identity cache of the edge
        concat(c, ce, edgeDemand = false, staticAt = staticIdentityDepth(c, premise, ce, statementEdge, mode), mode, out)
    }
    // Part I §5.4: satisfying, applySummary, applyCombination.   Part I §5.5: filter.   Part I §5.6: clean.
    // Part I §5.7: limit.   Part I §5.8: checkSink, without, matchLiteral, targetTree.
    // Part I §5.9: zero, startFact, policy, emit, restrict.   Part I §5.10: requestAction.   Part I §5.11: reverse, leaves.
}
```

§5.4 to §5.11 write each operation as `fun ApOps.x(...)` to show its file. In the code each one is a member of `ApOps`
with the same signature. The member calls the internal helper of its file (`ConcatStep`, `CleanWalk`, `Limiter`).

```kotlin

/** A PathEdge in the form that the tree walk reads. PathEdge caches it (`@JvmField internal var compiled`, Part I §6): a benign race,
 *  because CompiledEdge is immutable with final fields (JLS §17.5). Part II makes the PathEdges once per statement and keeps
 *  them in the method context cache, so the cache hits. */
internal fun ApManager.compile(e: PathEdge) = CompiledEdge(
    e.from.base, e.from.path.toIntArray(), e.from.tail, e.from.mark,
    e.to.base, path(e.to.path), e.to.tail, e.to.mark, intern(e.exclusion))

internal class CompiledEdge(
    @JvmField val fromBase: AccessPathBase, @JvmField val fromPath: IntArray, @JvmField val fromTail: Tail, @JvmField val fromMark: MarkSlot,
    @JvmField val toBase: AccessPathBase, @JvmField val toPath: PathNode?, @JvmField val toTail: Tail, @JvmField val toMark: MarkSlot,
    @JvmField val exclusion: ExclusionSet,              // the ONE exclusion of the edge (§2.2)
) {
    init {                                              // §4.1 preconditions; a bug of the interpreter or the analyzer
        check(fromMark !is MarkSlot.Star || fromMark.excluded.isEmpty)                        // S7
        check(fromTail != Tail.EXACT || fromMark is MarkSlot.Concrete)                        // S8
        check(fromTail != Tail.EXACT || toTail != Tail.STAR)                                  // S8
    }
}

/** ap.md §4.1 static exception, §4.10 item 1. The depth of the `*` leaf of an identity static `*` edge `(S, q, */E0, *) -> c`
 *  at `q = []` or `q = [<C>]`, when a statement micro edge reads strictly below q in run 1; else -1. The walk tests
 *  condition 4 (`Ec admits r`). */
private fun staticIdentityDepth(c: EdgeTree, premise: PremiseKey, ce: CompiledEdge, statementEdge: Boolean, mode: ApMode): Int {
    if (!mode.run1 || !statementEdge || c.demand || c.base != STATIC || ce.fromBase != STATIC) return -1
    val i = premise.single ?: return -1
    if (i.base != STATIC || i.tail != Tail.STAR || i.mark != MarkSlot.STAR) return -1
    val q = i.pathArray
    if (!(q.isEmpty() || (q.size == 1 && q[0].isClass()))) return -1                          // rootOrClass(q)
    if (ce.fromPath.size <= q.size || !ce.fromPath.startsWith(q)) return -1                    // case `above`
    return q.size
}
```

The tree delta-concat. One function serves a micro edge (`applyEdge`) and a summary leaf kind (`applySummary`, §5.4):

```kotlin
/** ap.md §7.3 steps 1 to 5 and 7 on all paths of `c` at once. Step 6 (the field limit) is not here (§4.1): the caller
 *  calls limit at the cut points of §4.4. Cost: |from.path| + 1 nodes for the walk, U for the transform (Tree.walkSteps_le). */
internal fun ApOps.concat(c: EdgeTree, ce: CompiledEdge, edgeDemand: Boolean, staticAt: Int, mode: ApMode, out: ApOut) {
    if (c.base != ce.fromBase) return                                                       // §4.1 step 1
    val k = ConcatStep(manager, c, ce, edgeDemand, mode, out)
    var node = c.root
    for (d in ce.fromPath.indices) {                                                        // §7.3 step 1: proper prefixes, case `above`
        val r0 = ce.fromPath[d]                                                             // the first accessor of the rest r
        val pl = node.payload
        var star = pl.star && c.exclusion.admits(r0)                                        // Tree.cS: `*/Ec` admits r
        if (star && d == staticAt) { out.positionRequest(manager.position(ce.fromPath)); star = false }   // §4.10 item 1
        k.gate(manager.leafMarks(pl.any.star || star, pl.any.concrete))?.let {               // `[any]`: always; `$`: no overlap
            k.results.add(true, ExclusionSet.Empty, k.mx, k.leafAtTarget(k.aboveTail, it))   // `[any]` (or `$`), demand layer
        }
        node = node.child(r0) ?: return k.results.flush(out)
    }
    k.below(node)                                                                           // §7.3 steps 2 to 5 on the subtree U
    k.results.flush(out)
}

internal class ConcatStep(private val m: ApManager, private val c: EdgeTree, private val ce: CompiledEdge,
                          edgeDemand: Boolean, private val mode: ApMode, private val out: ApOut) {
    val results = Results(m, ce.toBase)
    private val layer = c.demand || edgeDemand                                              // §4.1 step 6: the layer of c or of the summary
    val mx: MarkSet = when (val tm = ce.toMark) {                                           // §4.1 step 5: `*∖Y` adds Y
        is MarkSlot.Star -> m.intern(c.markExclusion + tm.excluded)
        is MarkSlot.Concrete -> MarkSet.EMPTY
    }
    val aboveTail = if (ce.toTail == Tail.EXACT) Tail.EXACT else Tail.ANY                   // case `above`: `$` or `[any]`
    private val admitsRest = { a: AccessorIdx -> ce.fromTail != Tail.EXACT && ce.exclusion.admits(a) }  // the premise admits r ≠ []

    /** §4.1 step 3, case `below`, on U. */
    fun below(u: FactNode) {
        val pl = u.payload
        when (ce.toTail) {
            Tail.STAR -> {
                m.retainChildren(u, admitsRest)?.let { kids ->                              // r ≠ []: `to.path ++ r`, c.tail with Ec
                    gateTree(kids)?.let { results.add(layer, c.exclusion, mx, m.prepend(ce.toPath, it)) }
                }
                if (pl.star) gate(LeafMarks.STAR)?.let {                                        // r = [], `*`: `*/(Ec ∪ E)`
                    results.add(layer, c.exclusion.union(ce.exclusion), mx, m.prepend(ce.toPath, m.leaf(starPayload(it))))
                }
                gate(pl.exact)?.let { results.add(layer, c.exclusion, mx, leafAtTarget(Tail.EXACT, it)) }   // r = [], `$`
                gate(pl.any)?.let { results.add(true, ExclusionSet.Empty, mx, leafAtTarget(Tail.ANY, it)) } // r = [], `[any]`: W6
            }
            Tail.ANY ->                                                                     // fold U into one `[any]` payload (W6)
                gate(m.foldMarks(u, admitsRest, starTails = true))?.let {
                    results.add(true, ExclusionSet.Empty, mx, leafAtTarget(Tail.ANY, it))
                }
            Tail.EXACT -> {                                                                 // fold U into one `$` payload
                val rootLost = pl.star && c.exclusion.union(ce.exclusion) != ExclusionSet.Empty   // lostCorr, r = []
                val deepStar = m.retainChildren(u, admitsRest)?.hasStar == true
                val deepLost = deepStar && c.exclusion != ExclusionSet.Empty                       // lostCorr, r ≠ []
                val other = m.foldMarks(u, admitsRest, starTails = false)                          // `[any]` and `$` leaves: never lost
                val starKept = (pl.star && !rootLost) || (deepStar && !deepLost)
                gate(m.withStar(other, starKept))?.let { results.add(layer, ExclusionSet.Empty, mx, leafAtTarget(Tail.EXACT, it)) }
                if (rootLost || deepLost) gate(LeafMarks.STAR)?.let {
                    results.add(true, ExclusionSet.Empty, mx, leafAtTarget(Tail.EXACT, it))
                }
            }
        }
    }

    /** §4.1 steps 4 and 5 on the marks of one leaf kind (Lean markGate, markComp). `star` is the mark `*∖Xc` of c. */
    fun gate(ms: LeafMarks): LeafMarks? {
        if (ms.isEmpty) return null
        var star = ms.star
        var conc = ms.concrete
        val pm = ce.fromMark
        if (pm is MarkSlot.Concrete) {                                                       // step 4: the mark gate
            if (star && pm.mark !in c.markExclusion) {                                       // `*`, or `*∖X` with T ∉ X
                check(mode.run1) { "a restricted run is concrete (ap.md §6.3)" }
                out.markRequest(pm.mark)
            }
            star = false
            conc = if (pm.mark in conc) m.markSetOf(pm.mark) else return null               // T' ≠ T, or T ∈ X: empty
        }
        return when (val tm = ce.toMark) {                                                   // step 5: the result mark
            is MarkSlot.Concrete -> m.leafMarks(false, m.markSetOf(tm.mark))
            is MarkSlot.Star -> m.leafMarks(star, conc - tm.excluded).takeIf { !it.isEmpty } // a concrete mark in Y: no fact
        }
    }

    /** gate on every leaf of a subtree. A concrete result of a `*` leaf becomes an `[any]` leaf (W2). */
    private fun gateTree(n: FactNode): FactNode? =
        if (ce.fromMark == MarkSlot.STAR && ce.toMark == MarkSlot.STAR) n                     // `*` -> `*`: no copy (the common case)
        else m.mapPayloads(n) { pl ->
            val s = if (pl.star) gate(LeafMarks.STAR) else null
            m.payload(star = s?.star == true,
                any = m.unionMarks(gate(pl.any) ?: LeafMarks.EMPTY, m.leafMarks(false, s?.concrete ?: MarkSet.EMPTY)),
                exact = gate(pl.exact) ?: LeafMarks.EMPTY)
        }

    private fun starPayload(it: LeafMarks) = m.payload(star = it.star, any = m.leafMarks(false, it.concrete))   // W2
    fun leafAtTarget(tail: Tail, ms: LeafMarks): FactNode = m.prepend(ce.toPath, m.leaf(when (tail) {
        Tail.ANY -> m.payload(any = ms); Tail.EXACT -> m.payload(exact = ms); Tail.STAR -> starPayload(ms)
    }))
}
```

`Tree.applyTreeE_mem`, `applyTreeE_den` prove this walk for a `*`-to-`*` edge with the mark `*` on both sides. The mark
gate, the static exception and the other target tails are the per-path rows of §4.1 applied per payload. The test
`EdgeTreeEquivalenceTest` (§8) compares every case with the reference `concat` (`ap.md` §4.1).

### 5.4 `satisfying`, `applySummary`, `applyCombination` (`ap.md` §4.3, §4.6; DD4)

```kotlin
/** The part of the added-fact tree `a` whose facts satisfy `j`: `applicable` (run 1), `inside` (restricted), both (a
 *  record, §8.7 R4). ONE function for the replay and the delivery (analyzer-core.md P4). */
fun ApOps.satisfying(a: EdgeTree, j: InitialAp, mode: ApMode, record: Boolean = false): EdgeTree? {
    if (a.base != j.base) return null
    val below = if (record || mode.run1) applicablePart(a, j) else null
    val above = if (record || mode.restricted) insidePart(a, j) else null
    val n = when { below == null -> above; above == null -> below; else -> manager.mergeAdd(below, above) } ?: return null
    return manager.tree(a.base, a.exclusion, a.markExclusion, a.demand, n)
}

/** applicable(j, leaf) (ap.md §3.4): j covers the leaf, and an `[any]` premise needs an `[any]` fact. ADAPT of
 *  AccessNode.filterStartsWith (AccessTree.kt:1329): walk j.path, take the subtree, rebuild the chain. */
private fun ApOps.applicablePart(a: EdgeTree, j: InitialAp): FactNode? {
    val m = manager
    var u = a.root
    for (acc in j.pathArray) u = u.child(acc) ?: return null
    val pl = u.payload
    val at = when (j.tail) {                                                    // r = []: tailSub(j, leaf)
        Tail.STAR -> m.payload(star = pl.star && j.exclusion.isSubsetOf(a.exclusion),
                               any = if (j.exclusion == ExclusionSet.Empty) pl.any else LeafMarks.EMPTY, exact = pl.exact)
        Tail.EXACT -> m.payload(exact = pl.exact)
        Tail.ANY -> m.payload(any = pl.any)
    }
    val kids = when (j.tail) {                                                  // r ≠ []: j.tail admits r
        Tail.STAR -> m.retainChildren(u) { j.exclusion.admits(it) }
        Tail.EXACT -> null
        Tail.ANY -> m.retainChildren(u) { true }?.let(m::onlyAny)
    }
    val n = m.node(at, kids?.accessors, kids?.children).takeIf { !it.isEmpty }
        ?.let { m.onlyMarksOf(j.mark, it) } ?: return null                     // markSub(j.mark, leaf.mark)
    return m.prepend(j.path, n)
}

/** inside(j, leaf) (ap.md §3.4, Lean satI): j lies inside the leaf as locations, and the marks of the leaf are a subset of the
 *  marks of j. Such a leaf is at or above j.path: only the payloads on the path are kept. */
private fun ApOps.insidePart(a: EdgeTree, j: InitialAp): FactNode? {
    val m = manager
    val p = j.pathArray
    val spine = arrayOfNulls<Payload>(p.size + 1)
    var u: FactNode? = a.root
    for (d in 0..p.size) {
        val n = u ?: break
        val pl = n.payload
        spine[d] = if (d < p.size) m.payload(star = pl.star && a.exclusion.admits(p[d]), any = pl.any)   // above j: the tail admits r
        else m.payload(                                                                                   // at j: tailSub(leaf, j)
            star = pl.star && when (j.tail) {
                Tail.EXACT -> true
                Tail.STAR -> a.exclusion.isSubsetOf(j.exclusion)
                Tail.ANY -> a.exclusion == ExclusionSet.Empty
            },
            any = pl.any,
            exact = if (j.tail == Tail.EXACT) pl.exact else LeafMarks.EMPTY)
        u = if (d < p.size) n.child(p[d]) else null
    }
    return m.chain(p, spine)?.let { m.onlyMarksOf(j.mark, it) }
}

/** ap.md §4.3: concat(a, j -> g, edgeDemand = g.demand) on every leaf of g. Precondition: a = satisfying(...).
 *  The leaves of one kind (tail, mark) differ only by their path. So one concat with `to.path = []` gives the result of every
 *  such leaf, and graft puts it at each path. ADAPT of concatToLeafAbstractNodes (AccessTree.kt:1281), which puts a caller
 *  delta under every abstract node of a summary. */
fun ApOps.applySummary(a: EdgeTree, j: InitialAp, g: EdgeTree, mode: ApMode, out: ApOut) {
    for (kind in manager.leafKinds(g)) {                       // (STAR, *∖Xg); (ANY | EXACT, *∖Xg or one concrete mark)
        val e = CompiledEdge(j.base, j.pathArray, j.tail, j.mark, g.base, toPath = null, kind.tail, kind.mark,
            exclusion = if (kind.tail == Tail.STAR) j.exclusion.union(g.exclusion) else j.exclusion)   // §2.2: ONE exclusion
        val one = CollectingOut()
        concat(a, e, edgeDemand = g.demand, staticAt = -1, mode, one)
        check(one.markRequests.isEmpty())                      // a summary application never requests (Coverage.summary_step)
        for (r in one.trees)
            out.result(manager.tree(r.base, r.exclusion, r.markExclusion, r.demand, manager.graft(g.root, kind, r.root)!!))
    }
}

/** `r` at every node of g that has a leaf of `kind`; no other leaf of g. Every kind of leafKinds(g) occurs, so the result is
 *  not empty. An identity memo over g keeps shared subtrees of g shared. */
internal fun ApManager.graft(g: FactNode, kind: LeafKind, r: FactNode, memo: IdentityHashMap<FactNode, FactNode?> = IdentityHashMap()): FactNode? {
    if (memo.containsKey(g)) return memo[g]
    val here = if (kind.occursIn(g.payload)) r else null
    val kids = mapChildren(g, Payload.EMPTY) { _, c -> graft(c, kind, r, memo) }
    return (if (here == null) kids else if (kids == null) here else mergeAdd(here, kids)).also { memo[g] = it }
}
```

Event E6 applies a summary with several premises to one full combination (`ap.md` §4.6 "at a call", `ap.md` §4.3; Lean
`ND.DN.ndBind`). The caller keeps the combination (`analyzer-core.md` §5.4). For each member `jm`, it gives the
satisfying part of the added fact of its link: `satisfying(a, jm, mode)` on the link tree. The `demand` bit of the link
tree IS the layer of the added fact on that link (§7.5: `add` asserts `linkLayer == added.layer`). So the link layer
enters through `part.demand`, and the same `applySummary` of E2 and E4 gives the layer of each member.

```kotlin
/** One full combination: `parts[m]` = (the satisfying part for member m, the member jm). The conclusion g has no `*` tail
 *  and concrete marks (W7), so every member application gives the leaves of g (an uncorrelated target puts the result at
 *  to.path with the tail and the mark of the target, §4.1 step 3); only its LAYER differs. The result is in the demand
 *  layer if g is, if one part is demand on its link, or if one application moves it there (case `above`). Several
 *  premise sets: the analyzer gives the result the union of the premise sets of the caller edges (§4.6). The caller binds
 *  it back and applies the field limit (§5.3 step 5). */
fun ApOps.applyCombination(parts: List<Pair<EdgeTree, InitialAp>>, g: EdgeTree, mode: ApMode, out: ApOut) {
    check(parts.size >= 2 && !g.root.hasStar && !g.root.hasAbstractMark)       // W7
    var normal = !g.demand                                                       // a choice of leaves with every member normal
    var demand = g.demand                                                        // a choice with one member in the demand layer
    for ((part, j) in parts) {
        val one = CollectingOut()
        applySummary(part, j, g, mode, one)                                      // edgeDemand = g.demand; layer of c = part.demand
        check(one.markRequests.isEmpty())                                        // satisfying: the gate passes (C4)
        if (one.trees.isEmpty()) return                                          // not a full combination
        normal = normal && one.trees.any { !it.demand }
        demand = demand || one.trees.any { it.demand }
    }
    if (normal) out.result(manager.tree(g.base, ExclusionSet.Empty, MarkSet.EMPTY, demand = false, g.root))
    if (demand) out.result(manager.tree(g.base, ExclusionSet.Empty, MarkSet.EMPTY, demand = true, g.root))   // W6 holds: no `*`
}
```

### 5.5 `filter` and the mark policy (`ap.md` §4.8, `interpreter.md` §5.1)

```kotlin
/** The mark policy of interpreter.md §5.1 (`markPolicyKeeps`): it reads a concrete mark on the value of the base itself.
 *  It is NOT a may-predicate: it reads the mark, not the path, and it can drop a real flow (outside ap.md S5; gap G6).
 *  Part II builds it for a primitive or boxed static type: `MarkPolicy { isPrimitiveTracking(it) }`. */
fun interface MarkPolicy { fun keeps(mark: TaintMark): Boolean }

/** ap.md §4.8: the primitive `filter(b, may)`; `may` is prefix-closed (S5). The base is the key of
 *  StatementSummary.typeFilters (and resultFilters, Part II §23.2). Part II builds `may` with JIRFactTypeChecker (REUSE of
 *  its FactApFilter). `markPolicy` is the policy of the same static type, or null (DD9). */
class TypeFilter(val may: FactTypeChecker.FactApFilter, val markPolicy: MarkPolicy? = null) {
    /** interpreter.md §5.1: two filters on one base are a conjunction. */
    fun and(o: TypeFilter): TypeFilter = TypeFilter(AndFilter(may, o.may), when {
        markPolicy == null -> o.markPolicy
        o.markPolicy == null -> markPolicy
        else -> MarkPolicy { markPolicy.keeps(it) && o.markPolicy.keeps(it) }
    })

    private class AndFilter(val a: FactTypeChecker.FactApFilter, val b: FactTypeChecker.FactApFilter) : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FactTypeChecker.FilterResult {
            val x = a.check(accessor)
            val y = b.check(accessor)
            return when {
                x === FactTypeChecker.FilterResult.Reject || y === FactTypeChecker.FilterResult.Reject -> FactTypeChecker.FilterResult.Reject
                x === FactTypeChecker.FilterResult.Accept -> y                                   // Accept and r: r
                y === FactTypeChecker.FilterResult.Accept -> x
                else -> FactTypeChecker.FilterResult.FilterNext(                               // both FilterNext: the conjunction below
                    AndFilter((x as FactTypeChecker.FilterResult.FilterNext).filter, (y as FactTypeChecker.FilterResult.FilterNext).filter))
            }
        }
    }
}

/** ap.md §4.8: `filter(b, may)`, then the mark policy (interpreter.md §5.1: "after the filter", on the same facts).
 *  The path filter checks the concrete path only; it keeps the `*`, `[any]` and `$` tails whole. ADAPT of
 *  AccessNode.filterAccessNode(FactApFilter) (AccessTree.kt:1031): no `[any]` edge, no FinalAccessor check. A filter never
 *  rejects the empty path, so S11 (d) holds on the zero base. The backward run calls neither (analyzer-core.md §3). */
fun ApOps.filter(c: EdgeTree, f: TypeFilter): EdgeTree? {
    var root = filterNode(c.root, f.may) ?: return null
    f.markPolicy?.let { p -> root = markPolicyAtRoot(root, p) ?: return null }
    return if (root === c.root) c else manager.tree(c.base, c.exclusion, c.markExclusion, c.demand, root)
}

private fun ApOps.filterNode(n: FactNode, may: FactTypeChecker.FactApFilter): FactNode? =
    manager.mapChildren(n, n.payload) { a, child ->
        when (val r = may.check(manager.accessors.accessor(a))) {
            FactTypeChecker.FilterResult.Accept -> child                         // the whole subtree (prefix-closed, S5)
            FactTypeChecker.FilterResult.Reject -> null
            is FactTypeChecker.FilterResult.FilterNext -> filterNode(child, r.filter)
        }
    }

/** interpreter.md §5.1 `markPolicyKeeps(t, f)`: true unless `f.path` is empty and `f.mark` is a concrete mark that the
 *  policy rejects. So only the concrete marks of the leaves at the ROOT path can go, for every tail (`$`, `[any]`); a `*`
 *  leaf has an abstract mark (W2) and stays; a deeper leaf stays. Payloads are interned, so "no change" is `===`. */
private fun ApOps.markPolicyAtRoot(n: FactNode, p: MarkPolicy): FactNode? {
    val m = manager
    val pl = n.payload
    fun keep(ms: LeafMarks): LeafMarks =
        m.leafMarks(ms.star, MarkSet(ms.concrete.ids.filter { p.keeps(TaintMark(it)) }.toIntArray()))
    val kept = m.payload(pl.star, keep(pl.any), keep(pl.exact))
    if (kept === pl) return n
    return m.node(kept, n.accessors, n.children).takeIf { !it.isEmpty }
}
```

### 5.6 `clean` (`ap.md` §4.7)

```kotlin
/** ap.md §4.7 on one tree. Only the spine of `x.p` is rebuilt; a node off the spine is `disjoint` and stays shared. */
fun ApOps.clean(c: EdgeTree, premise: PremiseKey, cl: Cleaner, mode: ApMode, out: ApOut) {
    if (c.base != cl.base) { out.result(c); return }                                   // another base: disjoint
    check(mode.run1 || !c.root.hasAbstractMark)                                       // restricted: concrete (RExact.DR_concrete)
    val w = CleanWalk(manager, c, cl, mode, out)
    w.walk(c.root, 0)?.let { w.results.add(c.demand, c.exclusion, c.markExclusion, it) }   // the kept part keeps the key of c
    w.results.flush(out)
}

internal class CleanWalk(private val m: ApManager, private val c: EdgeTree, private val cl: Cleaner,
                         private val mode: ApMode, private val out: ApOut) {
    val results = Results(m, c.base)
    private val p = cl.pathArray
    private val cleanedMx = cl.mark?.let { m.intern(c.markExclusion + it) }          // `*∖(X ∪ {T})`
    private var requested = false

    /** The kept part of `n` at depth d of the spine. The other leaves go to their result groups. */
    fun walk(n: FactNode, d: Int): FactNode? {
        val pl = n.payload
        if (d < p.size) {                                                              // c strictly above x.p (table rows 5 to 7)
            val starPos = if (c.exclusion.admits(p[d])) Pos.PART else Pos.DISJOINT
            val kept = m.payload(star = pl.star && row(LeafMarks.STAR, Tail.STAR, starPos, d).star,
                                 any = row(pl.any, Tail.ANY, Pos.PART, d), exact = pl.exact)
            return m.replaceChild(n, kept, p[d], n.child(p[d])?.let { walk(it, d + 1) })
        }
        val wide = if (cl.reach == CleanReach.AT_AND_BELOW) Pos.INSIDE else Pos.PART  // at x.p, tail `*` or `[any]` (row 4)
        val exactPos = if (cl.reach == CleanReach.BELOW) Pos.DISJOINT else Pos.INSIDE // at x.p, tail `$` (row 3)
        val kept = m.payload(star = pl.star && row(LeafMarks.STAR, Tail.STAR, wide, d).star,
                             any = row(pl.any, Tail.ANY, wide, d), exact = row(pl.exact, Tail.EXACT, exactPos, d))
        if (cl.reach == CleanReach.EXACT) return m.node(kept, n.accessors, n.children).takeIf { !it.isEmpty }   // below: disjoint
        val (keptKids, cleaned) = splitInside(m.retainChildren(n) { true })           // below x.p: inside (row 2)
        cleaned?.let { results.add(c.demand, c.exclusion, cleanedMx!!, m.prepend(cl.path, it)) }
        return m.node(kept, keptKids?.accessors, keptKids?.children).takeIf { !it.isEmpty }
    }

    /** The result table of §4.7 for the marks of one leaf kind at depth d (d < |p|: above; d = |p|: at). Returns the marks that
     *  stay in c; moves the others. */
    private fun row(ms: LeafMarks, tail: Tail, pos: Pos, d: Int): LeafMarks {
        if (pos == Pos.DISJOINT || ms.isEmpty) return ms
        val t = cl.mark
        val cleanedConc = if (t == null) ms.concrete else ms.concrete.intersect(m.markSetOf(t))
        if (!cleanedConc.isEmpty && pos == Pos.PART) concPart(cleanedConc, tail, d)    // `T` cleaned in part; inside: dropped
        if (ms.star) when {
            t != null -> {                                                             // `*∖X` -> `*∖(X ∪ {T})`, the same layer
                results.add(c.demand, c.exclusion, cleanedMx!!, leafAt(d, tail, LeafMarks.STAR))
                if (pos == Pos.PART && t !in c.markExclusion && !requested) {          // §11.2: no request for T ∈ X
                    check(mode.run1); out.markRequest(t); requested = true
                }
            }
            pos == Pos.PART -> results.add(true, ExclusionSet.Empty, c.markExclusion, leafAt(d, tail, LeafMarks.STAR))  // all marks: demand, W2
            else -> Unit                                                               // all marks, inside: dropped
        }
        return m.leafMarks(false, ms.concrete - cleanedConc)                           // `T'` that the cleaner does not clean stays
    }

    /** concPart (Lean): an `[any]` fact at x.p under a `below` cleaner keeps only `(x, p, $, T)` in the layer of c; any other
     *  part goes to the demand layer. */
    private fun concPart(marks: MarkSet, tail: Tail, d: Int) =
        if (tail == Tail.ANY && cl.reach == CleanReach.BELOW && d == p.size)
            results.add(c.demand, ExclusionSet.Empty, MarkSet.EMPTY, leafAt(d, Tail.EXACT, m.leafMarks(false, marks)))
        else results.add(true, ExclusionSet.Empty, MarkSet.EMPTY, leafAt(d, tail, m.leafMarks(false, marks)))

    /** Every leaf strictly below x.p is `inside` (reach below or atAndBelow). Returns (kept, abstract leaves for `*∖(X ∪ {T})`).
     *  Path-free, so an identity memo is valid. */
    private fun splitInside(n: FactNode?): Pair<FactNode?, FactNode?>   // abstract leaves: moved (one mark) or dropped (all marks);
                                                                        // concrete cleaned marks: dropped; other marks: kept
    private fun leafAt(d: Int, tail: Tail, ms: LeafMarks): FactNode = m.prepend(m.path(p.copyOf(d)), m.leaf(m.payloadOf(tail, ms)))
}
```

### 5.7 `limit` (`ap.md` §4.4)

```kotlin
/** ap.md §4.4. A path with more than L counted accessors is cut before the (L+1)-th one; the tail becomes `[any]`, the
 *  exclusion Empty, the mark stays (also `*∖X`), the layer becomes demand. ADAPT of FieldLimiter.limit (branch
 *  saloed/any-field-limit, AccessTree.kt:722): the same budget walk over the nodes with boundedDepth > budget, with a memo per
 *  budget; no `[any]` edge to keep, so the cut part is a separate demand tree. */
fun ApOps.limit(c: EdgeTree, fieldLimit: Int, out: ApOut) {
    if (c.root.boundedDepth <= fieldLimit) { out.result(c); return }                  // the O(1) check (Part I §4.5)
    val (kept, cut) = Limiter(manager).keep(c.root, fieldLimit)
    kept?.let { out.result(manager.tree(c.base, c.exclusion, c.markExclusion, c.demand, it)) }
    cut?.let { out.result(manager.tree(c.base, ExclusionSet.Empty, c.markExclusion, demand = true, it)) }
}

private class Limiter(private val m: ApManager) {
    private val memo = Int2ObjectOpenHashMap<IdentityHashMap<FactNode, Pair<FactNode?, FactNode?>>>()

    /** (the paths within the budget, the `[any]` leaves at the cut points); both rooted at n, so the memo is path-free. */
    fun keep(n: FactNode, budget: Int): Pair<FactNode?, FactNode?> {
        if (n.boundedDepth <= budget) return n to null
        memo.getOrPut(budget, ::IdentityHashMap)[n]?.let { return it }
        m.cancellation.checkpoint()
        var cutHere = LeafMarks.EMPTY                                                  // the marks of the cut subtrees at this node
        val keptKids = IntArrayList(); val keptNodes = ArrayList<FactNode>()
        val cutKids = IntArrayList(); val cutNodes = ArrayList<FactNode>()
        n.accessors?.forEachIndexed { i, a ->
            val child = n.children!![i]
            if (a.isCounted() && budget == 0) { cutHere = m.unionMarks(cutHere, m.foldMarks(child, { true }, starTails = true)); return@forEachIndexed }
            val (k, ct) = keep(child, if (a.isCounted()) budget - 1 else budget)        // uncounted accessors stay in the prefix
            k?.let { keptKids.add(a); keptNodes.add(it) }
            ct?.let { cutKids.add(a); cutNodes.add(it) }
        }
        val kept = m.node(n.payload, keptKids.toIntArray(), keptNodes.toTypedArray()).takeIf { !it.isEmpty }
        val cut = m.node(m.payload(any = cutHere), cutKids.toIntArray(), cutNodes.toTypedArray()).takeIf { !it.isEmpty }
        return (kept to cut).also { memo[budget]!![n] = it }
    }
}
```

`L = 0` cuts every first counted accessor: the cut leaf is `[any]` at the root path, as `ap.md` §4.4 says.

### 5.8 `checkSink`, `without`, `matchLiteral`, `targetTree` (`ap.md` §4.6, §4.9)

```kotlin
sealed interface SinkCheck {                                    // ap.md §4.9
    data object None : SinkCheck
    class Triggered(val facts: EdgeTree) : SinkCheck            // the part of the input that triggers
    class Request(val mark: TaintMark) : SinkCheck              // run 1 only
}

fun ApOps.checkSink(c: EdgeTree, s: Pattern, mode: ApMode): SinkCheck {
    val t = (s.fact.mark as MarkSlot.Concrete).mark                                  // a sink pattern has a concrete mark
    if (c.base != s.fact.base) return SinkCheck.None
    val hit = overlapPart(c, s) ?: return SinkCheck.None                             // overlap, marks ignored (§3.2)
    val request = hit.hasAbstractMark && t !in c.markExclusion                       // `*`, or `*∖X` with T ∉ X
    val triggered = manager.onlyMark(hit, t)                                         // f.mark = T
    check(!(request && triggered != null))                                           // Part I §4.1: one tree is abstract or concrete
    return when {
        triggered != null -> SinkCheck.Triggered(manager.tree(c.base, ExclusionSet.Empty, MarkSet.EMPTY, c.demand, triggered))
        request -> { check(mode.run1); SinkCheck.Request(t) }                         // the analyzer asserts i.mark abstract (below)
        else -> SinkCheck.None                                                       // T' ≠ T, or T ∈ X
    }
}

/** The leaves of `c` that are not in `part` (same path, tail and mark). `part` is a part of `c`, for example the
 *  `SinkCheck.Triggered.facts` of an exit sink: the global-state rule (interpreter.md §4.7 step 3) drops only the facts
 *  on S on which the sink triggered. null: nothing is left. */
fun ApOps.without(c: EdgeTree, part: EdgeTree): EdgeTree? {
    if (c.base != part.base) return c
    val n = manager.minusNode(c.root, part.root) ?: return null
    return if (n === c.root) c else manager.tree(c.base, c.exclusion, c.markExclusion, c.demand, n)
}

/** FactNodeOps.kt: the leaves of n not in k, walked along k only (a subtree of n off k is shared). */
internal fun ApManager.minusNode(n: FactNode, k: FactNode): FactNode? {
    if (n == k) return null                                                       // structural (Part I §4.5): nothing is left
    val kept = minus(n.payload, k.payload)                                        // Part I §4.2: the leaves of n that k does not have
    return mapChildren(n, kept) { a, c ->                                         // null: the child is removed completely
        val kc = k.child(a)
        if (kc == null) c else minusNode(c, kc)
    }
}

// ap.md §4.9: on a request, "i.mark is abstract too ... the implementation asserts it". checkSink has no premise
// parameter, so the analyzer asserts it on its request path (Coverage.edge_conc): on SinkCheck.Request it calls `raise`
// and `addRequest` (analyzer-impl.md §4.9, §4.3, §4.2), and RequestStore.add (Part I §7.9) checks that the premise has
// the mark `*`.

/** The leaves of c that overlap `s` (Lean overlapB per leaf). Above s.path: a `*` leaf whose exclusion admits the rest, every
 *  `[any]` leaf; at s.path: every leaf; below: every leaf if s has the `[any]` tail. Rebuilt on the path. */
internal fun ApOps.overlapPart(c: EdgeTree, s: Pattern): FactNode?

/** ap.md §4.6: `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)`. Each literal has a concrete mark (S9) and the tail `$` or
 *  `[any]`; the target has a concrete mark and no `*` tail (W7, S10). Part II reverses it into one PathEdge per literal,
 *  `reverse(PathEdge(lit.fact, target, Empty))` (ap.md §9.2). */
class ConjunctiveEdge(val literals: List<Pattern>, val target: PathFact) {
    init {
        check(literals.size >= 2)
        check(literals.all { it.fact.mark is MarkSlot.Concrete && it.fact.tail != Tail.STAR })
        check(target.mark is MarkSlot.Concrete && target.tail != Tail.STAR)
    }
}

/** ap.md §4.6: the leaves of c that overlap the literal and pass its mark gate, split by `coversB lit leaf`. Raises the
 *  request Tj for an abstract leaf (rule reqConj, run 1). null: no input for this literal. The analyzer gives the result to
 *  ConjunctionStore.add (Part I §7.10); a conjunctive sink uses checkSink per literal instead (ap.md §4.9). */
fun ApOps.matchLiteral(c: EdgeTree, lit: Pattern, mode: ApMode, out: ApOut): LiteralMatch? {
    val t = (lit.fact.mark as MarkSlot.Concrete).mark                                 // S9
    val hit = overlapPart(c, lit) ?: return null
    if (hit.hasAbstractMark && t !in c.markExclusion) { check(mode.run1); out.markRequest(t) }
    val tLeaves = manager.onlyMark(hit, t) ?: return null
    val covered = manager.coveredBy(tLeaves, lit)          // `$` lit: the `$` leaves at ρ; `[any]` lit: the leaves at or below ρ
    val uncovered = if (covered == null) tLeaves else manager.minusNode(tLeaves, covered)   // null: covered completely (ND.Example.c3_normal)
    return LiteralMatch(normal = covered != null && !c.demand, demand = c.demand || uncovered != null)
}

/** The layers of the contribution of one input to a conjunction (ap.md §4.6, ND.conjLayer). Both can be true. */
class LiteralMatch(val normal: Boolean, val demand: Boolean)

/** A conjunction result `z.π.t(T)` (ap.md §4.6) or an end fact `P.$ (T)` (interpreter.md §4.1): a one-leaf tree. */
fun ApOps.targetTree(target: PathFact, layer: Layer): EdgeTree {
    check(target.mark is MarkSlot.Concrete && target.tail != Tail.STAR)               // W7
    return manager.treeOf(target, ExclusionSet.Empty, demand = layer == Layer.DEMAND)
}

/** A one-leaf tree. `[any]` goes to the demand layer (W6); `*` with a concrete mark or in the demand layer becomes `[any]` (W2). */
internal fun ApManager.treeOf(f: PathFact, exclusion: ExclusionSet, demand: Boolean): EdgeTree {
    val c = normalize(f, exclusion, demand)                                           // ap.md §4.1 step 6 (Reference.kt)
    val ms = when (val mk = c.fact.mark) {
        is MarkSlot.Star -> leafMarks(true, MarkSet.EMPTY)
        is MarkSlot.Concrete -> leafMarks(false, markSetOf(mk.mark))
    }
    val mx = (c.fact.mark as? MarkSlot.Star)?.excluded ?: MarkSet.EMPTY
    return tree(c.fact.base, c.exclusion, mx, c.demand, prepend(path(c.fact.path), leaf(payloadOf(c.fact.tail, ms))))
}
```

### 5.9 `zero`, `startFact`, `policy`, `emit`, `restrict` (`ap.md` §2.4, §6.2–§6.5, §7.4)

```kotlin
/** The zero fact `(zero, [], $, {}, zeroMark)` as a tree in the given layer (ap.md §2.4). The END FACTS of a sink apply
 *  `zero.$ (zeroMark) -> P.$ (T)` to the zero fact "in the layer of the sink edge" (interpreter.md §4.1), so a demand
 *  sink edge needs a demand zero tree. Both share one root, so MethodEdgeStore keeps them in its zero bit sets (Part I §7.3). */
fun ApOps.zero(layer: Layer): EdgeTree =
    if (layer == Layer.NORMAL) manager.zeroTree else manager.zeroTreeDemand     // ApManager: tree(Zero, Empty, EMPTY, true, zeroTree.root)

/** ap.md §6.5 (Lean startFact). */
fun ApOps.startFact(i: InitialAp): EdgeTree {
    val m = manager
    fun one(demand: Boolean, pl: Payload) = m.tree(i.base, i.exclusion, MarkSet.EMPTY, demand, m.prepend(i.path, m.leaf(pl)))
    val marks = when (val mk = i.mark) {
        is MarkSlot.Star -> m.leafMarks(true, MarkSet.EMPTY)
        is MarkSlot.Concrete -> m.leafMarks(false, m.markSetOf(mk.mark))
    }
    return when (i.tail) {
        Tail.STAR -> if (i.mark is MarkSlot.Star) one(false, m.payload(star = true))   // identity, normal; also a position answer
                     else one(true, m.payload(any = marks))                            // `*` with T: `[any]`, demand (W2)
        Tail.ANY -> one(true, m.payload(any = marks))
        Tail.EXACT -> one(false, m.payload(exact = marks))                             // also the zero fact
    }
}

/** ap.md §6.2 (Lean policy1): the zero fact for the zero fact, else `(x, [], *, {}, *)`. One per added tree (one base). */
fun ApOps.policy(added: EdgeTree): InitialAp =
    if (added.base == AccessPathBase.Zero) manager.zero
    else manager.initial(added.base, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)

/** ap.md §6.3: `a ∩ D-c` for every leaf a of `added`, with the mark of a. One initial fact per distinct result (no sharing). */
fun ApOps.emit(d: DemandPattern, added: EdgeTree): List<InitialAp> {
    val m = manager
    val dc = d.entry
    if (dc.fact.base != added.base) return emptyList()
    check(!added.root.hasAbstractMark)                                     // C3: the run is concrete (RCore.emitM_not_full_any)
    val p = m.path(dc.fact.path); val pa = dc.fact.path.toIntArray()
    val res = LinkedHashSet<InitialAp>()
    fun marks(ms: LeafMarks) = ms.concrete.ids.asSequence().map(::TaintMark)
        .filter { dc.fact.mark !is MarkSlot.Concrete || (dc.fact.mark as MarkSlot.Concrete).mark == it }   // markMatchB: `*∖X` counts as `*`
    fun add(path: PathNode?, tail: Tail, excl: ExclusionSet, t: TaintMark) { res += m.initial(added.base, path, tail, excl, MarkSlot.Concrete(t)) }
    var n = added.root
    for (k in pa.indices) {                                                // above: the tail of a admits r; only `[any]` does
        for (t in marks(n.payload.any)) add(p, dc.fact.tail, dc.exclusion, t)       // the demand chain and tail
        n = n.child(pa[k]) ?: return res.toList()
    }
    for (t in marks(n.payload.any)) add(p, dc.fact.tail, dc.exclusion, t)  // at: meet([any], t) = t
    for (t in marks(n.payload.exact)) add(p, Tail.EXACT, ExclusionSet.Empty, t)    // at: meet($, t) = $
    n.accessors?.forEachIndexed { i, a ->                                  // below: a itself if the tail of D-c admits r
        if (dc.tailAdmits(listOf(a))) m.forEachLeaf(n.children!![i], prefix = pa + a) { path, tail, ms ->
            for (t in marks(ms)) add(m.path(path), tail, ExclusionSet.Empty, t)
        }
    }
    return res.toList()
}

/** ap.md §6.4 on a whole tree (§7.4, RStore.restrictTree). Cost |D-p.path| + 1 + width; kept subtrees are shared. */
fun ApOps.restrict(j: InitialAp, g: EdgeTree, d: DemandPattern): EdgeTree? {
    val m = manager
    val dp = d.exit ?: return null                                         // the demand does not reach the exit
    if (!overlap(j.toPattern(), d.entry)) return null                      // the premise: all of j or nothing
    if (g.base != dp.fact.base) return null
    check(!g.root.hasStar)                                                 // a restricted run has no `*` leaf
    val pa = dp.fact.path.toIntArray()
    var moved = LeafMarks.EMPTY                                            // the `[any]` marks above D-p.path
    var n: FactNode = g.root
    for (a in pa) {                                                        // step 1: proper prefixes; `$` and off-chain children go
        moved = m.unionMarks(moved, n.payload.any)
        n = n.child(a) ?: return moved.takeIf { !it.isEmpty }?.let { tree(g, m.prepend(m.path(pa), m.leaf(m.payloadOf(movedTail(dp), it)))) }
    }
    val pl = m.union(n.payload, m.payloadOf(movedTail(dp), moved))         // step 2: keep the payload, add the moved marks
    val kids = m.retainChildren(n) { dp.tailAdmits(listOf(it)) }           // `[any]`: all; `*/E`: E admits; `$`: none
    return tree(g, m.prepend(m.path(pa), m.node(pl, kids?.accessors, kids?.children)))
}
private fun movedTail(dp: Pattern) = if (dp.fact.tail == Tail.EXACT) Tail.EXACT else Tail.ANY
private fun ApOps.tree(g: EdgeTree, root: FactNode) = manager.tree(g.base, g.exclusion, g.markExclusion, g.demand, root)  // the layer and mark of g
```

### 5.10 `requestAction` (`ap.md` §4.5, §4.10 items 2 to 4)

The analyzer joins a request with a link (`analyzer-core.md` §4.6). The AP rule of the pair is here:

```kotlin
sealed interface RequestAction {
    class Answer(val initial: InitialAp) : RequestAction                             // a new initial fact of this method
    class Climb(val premise: InitialAp, val request: RequestKind) : RequestAction    // RequestIn to the caller, on its premise
    data object None : RequestAction
}

/** One (request, link) pair. `a` is one leaf of the added fact of the link; it overlaps the request (RequestStore,
 *  AddedFactStore give only such pairs). */
fun ApOps.requestAction(i: InitialAp, kind: RequestKind, a: Pattern, caller: CallerRef): RequestAction {
    check(i.tail == Tail.STAR && i.exclusion == ExclusionSet.Empty && i.mark == MarkSlot.STAR)   // §4.5: a policy fact or a position answer
    val m = manager
    return when (kind) {
        is RequestKind.Mark -> when (val am = a.fact.mark) {
            is MarkSlot.Concrete ->
                if (am.mark == kind.mark) RequestAction.Answer(m.initial(answer(i.toPattern(), a, kind.mark)))   // `answer`, Part I §6
                else RequestAction.None                                                // T' ≠ T
            is MarkSlot.Star ->
                if (kind.mark in am.excluded) RequestAction.None                       // `*∖X` with T ∈ X: does not climb
                else RequestAction.Climb(checkNotNull(caller.premise.single), kind)    // Lean climbsB; an ND caller edge is concrete (W7)
        }
        is RequestKind.Position -> when {
            a.fact.path.startsWith(kind.path.toList()) ->                               // item 2: at or below p
                RequestAction.Answer(m.initial(STATIC, kind.path, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR))
            caller.premise.single?.base == STATIC -> RequestAction.Climb(caller.premise.single!!, kind)   // item 3: above p
            else -> RequestAction.None
        }
    }
}
```

### 5.11 `reverse`, `leaves` (`ap.md` §9.1)

```kotlin
/** ap.md §9.1: null if the edge is not mark-reversible. Part II uses it for every micro edge (StatementSummary.reversed);
 *  Record.reversedAt uses it per conclusion leaf (Part I §7.8). */
fun ApOps.reverse(e: PathEdge): PathEdge? = revEdge(e)                              // Part I §6

/** The per-path view: one Pattern per leaf and mark. A `*` leaf has the tree exclusion; every abstract mark is
 *  `*∖X` with the mark exclusion of the tree. The tests read every tree result through it. */
fun ApOps.leaves(t: EdgeTree): Sequence<Pattern> {
    val out = ArrayList<Pattern>()
    val abstractMark = MarkSlot.Star(t.markExclusion)
    manager.forEachLeaf(t.root, EMPTY_PATH) { path, tail, ms ->
        val p = path.asList()
        val excl = if (tail == Tail.STAR) t.exclusion else ExclusionSet.Empty
        if (ms.star) out += Pattern(PathFact(t.base, p, tail, abstractMark), excl)
        for (id in ms.concrete.ids) out += Pattern(PathFact(t.base, p, tail, MarkSlot.Concrete(TaintMark(id))), excl)
    }
    return out.asSequence()
}
```

---

## 6. The reference forms (`Reference.kt`)

`Reference.kt` holds the Kotlin of the spec as the spec gives it (DD2): `ap.md` §3.4 (from `startsWith`, `STATIC` and
`PathFact` to `inside`; `Tail`, `MarkSet`, `ExclusionSet` and `MarkSlot` are in `Facts.kt`, §3.2), `ap.md` §4.1
(`PathEdge` to `normalize`), `ap.md` §6.3 (`meet`, `emit`, `satisfies`) and `ap.md` §6.4 (`restrict`). The `Accessor`
of the spec is `AccessorIdx` (DD6), so `rootOrClass` calls `q[0].isClass()` (a function here, a property in `ap.md`
§4.1). The tests compare every tree operation with these forms. `PathEdge` has one addition: the cache of §5.3.

```kotlin
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet) {
    @JvmField internal var compiled: CompiledEdge? = null                   // not in equals/hashCode (not a constructor property)
}
```

The forms that `ap.md` does not give in Kotlin (from the Lean definitions in `Basic.lean` and `Subsume.lean`):

```kotlin
/** ap.md §6.5 (Lean startFact). */
fun startFact(i: Pattern): Conclusion = when (i.fact.tail) {
    Tail.STAR -> if (i.fact.mark is MarkSlot.Star) Conclusion(i.fact, i.exclusion, demand = false)
                 else Conclusion(i.fact.copy(tail = Tail.ANY), ExclusionSet.Empty, demand = true)          // W2
    Tail.ANY -> Conclusion(i.fact, ExclusionSet.Empty, demand = true)
    Tail.EXACT -> Conclusion(i.fact, ExclusionSet.Empty, demand = false)
}

/** ap.md §4.4 (Lean cutPath, limitF). */
fun limit(c: Conclusion, fieldLimit: Int): Conclusion {
    var n = 0
    for ((k, a) in c.fact.path.withIndex())
        if (a.isCounted() && ++n > fieldLimit)
            return Conclusion(c.fact.copy(path = c.fact.path.take(k), tail = Tail.ANY), ExclusionSet.Empty, demand = true)
    return c
}

// Primitives.kt (not a reference form; listed here because cleanPos reads it)
enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }

/** ap.md §4.7 (Lean Cleaner). `mark == null`: every mark. Part II builds it (interpreter.md §5.2). */
class Cleaner(val base: AccessPathBase, val path: PathNode?, val reach: CleanReach, val mark: TaintMark?) {
    init { check(base != AccessPathBase.Zero) }                             // S11 (d): no cleaner on the zero base
    @JvmField internal val pathArray: IntArray = path?.toIntArray() ?: EMPTY_PATH
}

enum class Pos { INSIDE, DISJOINT, PART }

/** ap.md §4.7 (Lean cleanPos). */
fun cleanPos(cl: Cleaner, c: PathFact, exclusion: ExclusionSet): Pos {
    if (c.base != cl.base) return Pos.DISJOINT
    val p = cl.path?.toList().orEmpty()
    val q = c.path
    return when {
        q.size > p.size && q.startsWith(p) -> if (cl.reach == CleanReach.EXACT) Pos.DISJOINT else Pos.INSIDE
        q == p -> when {
            cl.reach == CleanReach.AT_AND_BELOW -> Pos.INSIDE
            c.tail == Tail.EXACT -> if (cl.reach == CleanReach.EXACT) Pos.INSIDE else Pos.DISJOINT
            else -> Pos.PART
        }
        p.startsWith(q) -> when (c.tail) {
            Tail.EXACT -> Pos.DISJOINT
            Tail.STAR -> if (exclusion.admits(p.drop(q.size))) Pos.PART else Pos.DISJOINT
            Tail.ANY -> Pos.PART
        }
        else -> Pos.DISJOINT
    }
}

class CleanOut(val facts: List<Conclusion>, val request: TaintMark?)

/** ap.md §4.7 (Lean cleanRes, addEx, concPart), with the §11.2 difference: no request for T ∈ X. */
fun cleanRes(cl: Cleaner, c: Conclusion): CleanOut {
    val pos = cleanPos(cl, c.fact, c.exclusion)
    if (pos == Pos.DISJOINT) return CleanOut(listOf(c), null)
    return when (val mk = c.fact.mark) {
        is MarkSlot.Concrete ->
            if (cl.mark != null && cl.mark != mk.mark) CleanOut(listOf(c), null)                  // T' not cleaned
            else if (pos == Pos.INSIDE) CleanOut(emptyList(), null)
            else CleanOut(listOf(concPart(cl, c)), null)
        is MarkSlot.Star -> {
            val t = cl.mark
            if (t == null) CleanOut(if (pos == Pos.INSIDE) emptyList() else listOf(normalize(c.fact, c.exclusion, demand = true)), null)
            else CleanOut(listOf(c.copy(fact = c.fact.copy(mark = MarkSlot.Star(mk.excluded + t)))),
                          if (pos == Pos.PART && t !in mk.excluded) t else null)
        }
    }
}

fun concPart(cl: Cleaner, c: Conclusion): Conclusion =
    if (c.fact.tail == Tail.ANY && cl.reach == CleanReach.BELOW && c.fact.path == cl.path?.toList().orEmpty())
        c.copy(fact = c.fact.copy(tail = Tail.EXACT))                       // in the layer of c
    else c.copy(demand = true)

sealed interface CheckResult { data object None : CheckResult; data object Triggered : CheckResult; data class Request(val mark: TaintMark) : CheckResult }

/** ap.md §4.9 (Lean `check`; renamed: `check` is the Kotlin assert), with the §11.2 difference: the effective-mark case is
 *  asserted away. */
fun sinkCheck(i: Pattern, f: Conclusion, s: Pattern): CheckResult {
    val t = (s.fact.mark as MarkSlot.Concrete).mark
    if (!overlap(Pattern(f.fact, f.exclusion), s)) return CheckResult.None
    return when (val mk = f.fact.mark) {
        is MarkSlot.Concrete -> if (mk.mark == t) CheckResult.Triggered else CheckResult.None
        is MarkSlot.Star -> if (t in mk.excluded) CheckResult.None
                            else { check(i.fact.mark is MarkSlot.Star); CheckResult.Request(t) }
    }
}

/** ap.md §4.5 chain answer (Lean answerInit) and §4.10 item 4 (Lean Statics.SCtx.ansInit). Precondition: a overlaps i, a.mark = t. */
fun answer(i: Pattern, a: Pattern, t: TaintMark): Pattern = when {
    i.fact.base == STATIC && a.fact.path.startsWith(i.fact.path) ->          // a at or below a static premise: a itself
        Pattern(a.fact.copy(mark = MarkSlot.Concrete(t)), a.exclusion)
    a.fact.tail == Tail.EXACT && a.fact.path == i.fact.path ->
        Pattern(PathFact(i.fact.base, i.fact.path, Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)
    else -> Pattern(i.fact.copy(mark = MarkSlot.Concrete(t)), i.exclusion)   // the request chain and kind, mark t
}

/** ap.md §6.2 (Lean policy1). */
fun policy(a: Pattern): Pattern =
    if (a.fact.base == AccessPathBase.Zero) a
    else Pattern(PathFact(a.fact.base, emptyList(), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)

/** ap.md §9.1 (Lean revEdge, revKinds, MarkRev). null: not mark-reversible. */
fun revEdge(e: PathEdge): PathEdge? {
    val fAbstract = e.to.mark is MarkSlot.Star
    if (!fAbstract && e.from.mark !is MarkSlot.Concrete) return null       // no_rev_of_star_conc
    val (pt, ct) = revTails(e.from.tail, e.to.tail)
    val pm = if (fAbstract) e.from.mark else e.to.mark                     // the new premise never has `*∖X`
    val cm = if (fAbstract) e.to.mark else e.from.mark
    val excl = if (pt == Tail.STAR || ct == Tail.STAR) e.exclusion else ExclusionSet.Empty   // the exclusion goes to the new conclusion (W1)
    return PathEdge(PathFact(e.to.base, e.to.path, pt, pm), PathFact(e.from.base, e.from.path, ct, cm), excl)
}

fun revTails(i: Tail, f: Tail): Pair<Tail, Tail> = when (i) {             // the table of §9.1
    Tail.STAR -> when (f) { Tail.STAR -> Tail.STAR to Tail.STAR; Tail.EXACT -> Tail.EXACT to Tail.ANY; Tail.ANY -> Tail.ANY to Tail.ANY }
    Tail.ANY -> when (f) { Tail.STAR -> Tail.STAR to Tail.STAR; Tail.EXACT -> Tail.EXACT to Tail.ANY; Tail.ANY -> Tail.ANY to Tail.ANY }
    Tail.EXACT -> when (f) { Tail.STAR -> Tail.EXACT to Tail.EXACT; Tail.EXACT -> Tail.EXACT to Tail.EXACT; Tail.ANY -> Tail.ANY to Tail.EXACT }
}

/** ap.md §8.1 (Subsume.subsumesB, markSubsB): s subsumes n inside one layer. */
fun subsumes(s: Conclusion, n: Conclusion): Boolean {
    if (s.fact.base != n.fact.base || s.demand != n.demand || !markSubsumes(s.fact.mark, n.fact.mark)) return false
    return when (s.fact.tail) {
        Tail.ANY -> n.fact.path.startsWith(s.fact.path)
        Tail.STAR -> n.fact.tail == Tail.STAR && s.fact.path == n.fact.path && s.exclusion.isSubsetOf(n.exclusion)
        Tail.EXACT -> n.fact.tail == Tail.EXACT && s.fact.path == n.fact.path
    }
}
fun markSubsumes(s: MarkSlot, n: MarkSlot): Boolean = when (s) {
    is MarkSlot.Concrete -> n == s
    is MarkSlot.Star -> n is MarkSlot.Star && s.excluded.isSubsetOf(n.excluded)
}
```

The test sources add the denotation `den(i, f)(l0, l1)` of `ap.md` §3.2 and a statement transfer (`transfer` of `Basic.lean`:
the union of `concat` over the micro edges, an untouched base unchanged, then `limit`) for the vector tests (§8).

---

## 7. The stores (`ap.md` §8)

### 7.1 Ownership and concurrency (`analyzer-core.md` §2, O1–O5)

| Store | Lifetime | Writer | Readers | Concurrency |
|---|---|---|---|---|
| `MethodEdgeStore`, `InitialFactStore`, `AddedFactStore`, `RequestStore`, `ConjunctionStore` | RUN | the runner of the method (O1) | the same runner; the driver at the barrier (O5) | none: single writer; the join of the runners (`analyzer-core.md` §6.3) orders the barrier reads |
| `RunSummaryStore`, `SourceHitStore` | HAND-OFF | the runner of the method (O1) | the driver at the barrier | as above |
| `DemandStore` | RUN, read-only | the driver, before the run (`Builder.build`) | any runner (`analyzer-core.md` A4) | immutable after `build`; the start of the run publishes it |
| `RecordStore` | PERSISTENT | the driver, at a barrier (`persist`) | any runner, through `view()` (`analyzer-core.md` A4) | written only when no runner is alive; `view()` rejects writes |
| `VulnerabilityStore` | PERSISTENT | any runner (O4) | the driver at the barrier | nested `ConcurrentHashMap`s; `merge` is atomic per (key, shape) (§7.12) |
| `PathTrie` | inside a store | the owner of the store | the owner | none; `SummaryStorage` (`analyzer-impl.md` §5.2) guards its trie with its lock (P3) |
| `ApManager`, `ApOps` | analysis | any | any | `ConcurrentHashMap`; `ApOps` is stateless (§5.3) |

### 7.2 `PathTrie` (`ap.md` §8 PATH TRIES)

```kotlin
package org.opentaint.dataflow.bidi.store

/** Entries keyed by `base :: path`. ADAPT of AccessBasedStorage (ap/ifds/access/tree/AccessBasedStorage.kt:12): the same child walk
 *  (`getOrCreateNode` :19, `find` :34, `allNodes` :76), keyed by IntArray instead of the old AccessPath.AccessNode, and plain
 *  fastutil maps instead of ConcurrentReadSafeInt2ObjectMap. Single writer. Store.lean proves each lookup equals its list
 *  filter (`lookupPrefixes_equiv`, `lookupExtensions_equiv`, `mem_around_indexBy`). */
class PathTrie<V : Any> {
    private class Node<V : Any> {
        val values = ArrayList<V>(1)
        var children: Int2ObjectOpenHashMap<Node<V>>? = null
        fun child(a: Int): Node<V>? = children?.get(a)
        fun getOrCreate(a: Int): Node<V> = (children ?: Int2ObjectOpenHashMap<Node<V>>().also { children = it }).getOrPut(a) { Node() }
    }
    private val roots = HashMap<AccessPathBase, Node<V>>(4)

    fun add(base: AccessPathBase, path: IntArray, value: V) { node(base, path).values += value }

    /** The value once per position (a linear test: a node holds few values). */
    fun addIfAbsent(base: AccessPathBase, path: IntArray, value: V) { val n = node(base, path); if (value !in n.values) n.values += value }

    private fun node(base: AccessPathBase, path: IntArray): Node<V> {
        var n = roots.getOrPut(base) { Node() }
        for (a in path) n = n.getOrCreate(a)
        return n
    }

    /** The entries at or above `path` (also at `path`). Cost: |path| + 1 nodes (Store.prefHits_le). */
    fun lookupPrefixes(base: AccessPathBase, path: IntArray): MutableList<V> {
        val out = ArrayList<V>()
        var n = roots[base] ?: return out
        out += n.values
        for (a in path) { n = n.child(a) ?: return out; out += n.values }
        return out
    }

    /** The entries at or below `path` (also at `path`). */
    fun lookupExtensions(base: AccessPathBase, path: IntArray): List<V> =
        ArrayList<V>().also { out -> find(base, path)?.let { collect(it, out, self = true) } }

    /** lookupPrefixes ++ the entries strictly below: each entry once (Store.around). It is also the `near` of ap.md §8.6
     *  (RStore.nearBy_iff_around). Cost: walk + Σ|rel| (RStore.near_query_cost); a radix trie would give walk + count. */
    fun around(base: AccessPathBase, path: IntArray): List<V> =
        lookupPrefixes(base, path).also { out -> find(base, path)?.let { collect(it, out, self = false) } }

    fun all(): Sequence<V> = roots.values.asSequence().flatMap { r -> ArrayList<V>().also { collect(r, it, self = true) } }

    private fun find(base: AccessPathBase, path: IntArray): Node<V>? {
        var n = roots[base] ?: return null
        for (a in path) n = n.child(a) ?: return null
        return n
    }
    private fun collect(n: Node<V>, out: MutableList<V>, self: Boolean) {   // iterative, as allNodes (:76)
        val stack = ArrayDeque<Node<V>>()
        if (self) out += n.values
        n.children?.values?.let(stack::addAll)
        while (stack.isNotEmpty()) { val x = stack.removeLast(); out += x.values; x.children?.values?.let(stack::addAll) }
    }
}
```

### 7.3 `MethodEdgeStore` (`ap.md` §8.1)

```kotlin
/** ap.md §8.1. Key (statement, premise key, layer, base, exclusion, mark exclusion) -> EdgeTree. REUSE of the structure of
 *  MethodAnalyzerEdges (ap/ifds/MethodAnalyzerEdges.kt:13): the zero edges in a BitSet per statement, here one per premise
 *  key and layer (SameInitialZeroFactEdges, :150), the conclusion base in an EdgeStorage (:240), the statement as its instruction index
 *  (instructionStorageIdx, :272). The layer, the exclusion and the mark exclusion are inside TreeGroup (Part I §4.3). */
class MethodEdgeStore(private val m: ApManager, private val method: MethodKey, private val lm: LanguageManager) {
    private val size = lm.getMaxInstIndex(method.method) + 1
    private val zeroEdges = Reference2ObjectOpenHashMap<PremiseKey, Array<BitSet>>()             // premise -> [NORMAL, DEMAND]
    private val byBase = object : MethodAnalyzerEdges.EdgeStorage<Reference2ObjectOpenHashMap<PremiseKey, Array<TreeGroup?>>>(method.statement) {
        override fun createStorage() = Reference2ObjectOpenHashMap<PremiseKey, Array<TreeGroup?>>()  // premise keys are interned
    }
    private val interner = m.newNodeInterner()

    /** Returns the delta (T4) or null (`analyzer-core.md` §4.3). */
    fun add(node: CommonInst, premise: PremiseKey, t: EdgeTree): EdgeTree? {
        val idx = lm.getInstIndex(node)
        if (t.base == AccessPathBase.Zero) {                         // only the zero fact lives on the zero base (§2.4)
            check(t.root === m.zeroTree.root)                        // premise {zero}, or {jb} in a backward run: the reversed
                                                                     // source `x.p.$ (T) -> zero.$ (zeroMark)` (ap.md §9.2 SOURCE HITS)
            val bits = zeroEdges.getOrPut(premise) { arrayOf(BitSet(size), BitSet(size)) }[t.layer.ordinal]
            if (bits[idx]) return null
            bits.set(idx)
            return t
        }
        val groups = byBase.getOrCreate(t.base).getOrPut(premise) { arrayOfNulls(size) }
        val g = groups[idx] ?: TreeGroup(m, interner).also { groups[idx] = it }
        return g.add(t)
    }

    /** §8.1: the queries of the trace resolution (phase 5). The store of the last forward run stays for it. Both read the
     *  zero bit sets too (a set bit is the zero tree of that premise key and layer). */
    fun edgesAt(node: CommonInst, premise: PremiseKey? = null): Sequence<Pair<PremiseKey, EdgeTree>>
    fun edgesAt(node: CommonInst, pattern: Pattern): Sequence<Pair<PremiseKey, EdgeTree>>   // trees with a leaf that overlaps it
}
```

The unchanged propagation of `analyzer-core.md` §4.3 skips the store, as today (`ap.md` §8.1).

### 7.4 `InitialFactStore` (`ap.md` §8.2)

```kotlin
class InitialFactStore {
    private val initials = ReferenceOpenHashSet<InitialAp>()            // interned: identity
    /** The premise SETS that are supported jointly (§4.9 condition 3). The analyzer fills it at the barrier
     *  (analyzer-core.md §7.5). */
    val supported = ReferenceOpenHashSet<PremiseKey>()
    fun add(i: InitialAp): Boolean = initials.add(i)                    // also deduplicates the answers of §8.8
    fun all(): Collection<InitialAp> = initials
}
```

### 7.5 `AddedFactStore`, `CallerRef`, `Link` (`ap.md` §8.3; DD4)

```kotlin
/** E-2 of analyzer-core.md §5.1: the caller side of a link. */
data class CallerRef(val caller: MethodKey, val premise: PremiseKey, val callerLayer: Layer, val call: CommonInst)

/** ap.md §8.3, the spec form: one leaf of an added tree with its caller reference and its layer on the link. */
data class Link(val addedFact: Pattern, val linkLayer: Layer, val caller: CallerRef)

/** ap.md §8.3. The added facts of one caller reference are ONE tree per (link layer, base, exclusion, mark exclusion): the
 *  leaves of the tree are the added facts (DD4). The key holds the exclusion and the mark exclusion, because two trees
 *  with different ones never merge (T3).
 *  EXACT DEDUPLICATION (analyzer-core.md §5.3, E-3): the only merge is the T1 union of leaves (mergeAddDelta, Part I §4.2,
 *  with no `[any]` fold). A leaf that the tree of its key has (same path, tail, mark) is dropped, nothing else: no T5 absorption,
 *  no subsumption (no TreeGroup, foldUnderAny, subtractSubsumed). Reason: `applicable` is not monotone in the added fact
 *  (a fact above j does not satisfy j), so a subsumed leaf can satisfy a premise that the subsuming leaf does not; dropping
 *  it loses a link, an answer or a summary application. The analyzer reuses this store to merge its subscription trees.
 *  Exact per key: a `$` or `[any]` leaf that comes once in a tree with a `*` leaf (key E) and once in a tree with none
 *  (key Empty, N1) is a new link twice. That is a duplicate, which E-3 permits; nothing is lost. */
class AddedFactStore(private val m: ApManager) {
    private data class Key(val ref: CallerRef, val linkLayer: Layer, val base: AccessPathBase, val exclusion: ExclusionSet, val mx: MarkSet)
    private val trees = Object2ObjectOpenHashMap<Key, EdgeTree>()
    private val index = PathTrie<Key>()                                   // one entry per new leaf position (§8.8 overlap queries)

    /** Event E1/E2: returns the delta (the new links) or null. */
    fun add(ref: CallerRef, linkLayer: Layer, added: EdgeTree): EdgeTree? {
        check(linkLayer == added.layer)                                    // the layer of the added fact on the link (§8.3)
        val key = Key(ref, linkLayer, added.base, added.exclusion, added.markExclusion)
        val old = trees[key]
        val delta = if (old == null) added.also { trees[key] = it }
        else {
            val (merged, d) = m.mergeAddDelta(old.root, added.root)
            trees[key] = old.withRoot(merged)
            m.tree(added.base, added.exclusion, added.markExclusion, added.demand, d ?: return null)
        }
        m.forEachLeafPosition(delta.root) { path -> index.addIfAbsent(added.base, path, key) }   // a key once per position
        return delta
    }

    /** §8.3, §8.8: the links whose added fact overlaps `(base, path, *, {}, *)` (a request premise or a position, §4.5). */
    fun overlapping(base: AccessPathBase, path: PathNode?): Sequence<Link> {
        val q = Pattern(PathFact(base, path?.toList().orEmpty(), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)
        val p = path?.toIntArray() ?: EMPTY_PATH
        return index.around(base, p).distinct().asSequence().flatMap { key -> links(key) }.filter { overlap(it.addedFact, q) }
    }

    fun links(): Sequence<Link> = trees.keys.asSequence().flatMap { links(it) }      // the support at the barrier (analyzer-core.md §7.5)
    private fun links(k: Key) = ApOps(m).leaves(trees.getValue(k)).map { Link(it, k.linkLayer, k.ref) }
}
```

The analyzer computes the satisfying part of a stored tree with `ApOps.satisfying` (P4); `satisfying` reads the tree, not
the per-leaf links.

### 7.6 `RunSummaryStore` (`ap.md` §8.5)

```kotlin
/** ap.md §8.5. Key (premise key, layer) -> the exit trees, BEFORE the restriction (analyzer-core.md §4.6). HAND-OFF.
 *  REPLACE of MethodInitialToFinalApSummaries (ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt:13), which unions the
 *  exclusions of different summaries (:271). */
class RunSummaryStore(private val m: ApManager) {
    private val groups = Reference2ObjectOpenHashMap<PremiseKey, HashMap<AccessPathBase, TreeGroup>>()
    private val interner = m.newNodeInterner()

    fun add(premise: PremiseKey, g: EdgeTree): EdgeTree? =
        groups.getOrPut(premise, ::HashMap).getOrPut(g.base) { TreeGroup(m, interner) }.add(g)

    fun all(): Sequence<Pair<PremiseKey, EdgeTree>> =
        groups.asSequence().flatMap { (p, byBase) -> byBase.values.asSequence().flatMap { it.trees() }.map { p to it } }
}
```

### 7.7 `DemandStore` (`ap.md` §8.6)

```kotlin
/** ap.md §8.6. RUN, read-only. The driver builds it from the hand-off of ap.md §9.2 (analyzer-core.md §7.3, §7.4). */
class DemandStore private constructor(
    private val byMethod: Map<MethodKey, PathTrie<DemandPattern>>,      // keyed by `base :: D-c.path`
    private val zeroDemand: DemandPattern,                              // (zero, none) of EVERY method key (§9.2, analyzer-core.md §4.4)
) {
    /** `near(q)`: the emission query (§6.3) for an added fact, the restriction query (§6.4) for a premise.
     *  RStore.near_equiv, emit_complete_M, restrict_complete_U. On the zero base it also gives the implicit zero demand.
     *  A stored zero-base pattern can have an exit pattern: `(D-c = zero, D-p = jb)` from a backward summary that reached a
     *  source (§9.2 item 3); it restricts the zero-premise summaries of the method. */
    fun near(method: MethodKey, base: AccessPathBase, path: PathNode?): List<DemandPattern> {
        val stored = byMethod[method]?.around(base, path?.toIntArray() ?: EMPTY_PATH).orEmpty()
        return if (base == AccessPathBase.Zero) stored + zeroDemand else stored
    }

    class Builder(private val m: ApManager) {
        private val byMethod = HashMap<MethodKey, PathTrie<DemandPattern>>()
        private val seen = HashSet<Pair<MethodKey, DemandPattern>>()
        private val zeroDemand = DemandPattern(m.zero.toPattern(), null)
        fun add(method: MethodKey, d: DemandPattern) {
            if (d == zeroDemand || !seen.add(method to d)) return           // the zero demand is implicit
            byMethod.getOrPut(method, ::PathTrie).add(d.entry.fact.base, d.entry.fact.path.toIntArray(), d)
        }
        fun build(): DemandStore = DemandStore(byMethod, zeroDemand)
    }
}
```

### 7.8 `RecordStore`, `Record` (`ap.md` §8.7)

```kotlin
/** ap.md §8.7: a normal summary edge with ONE premise (R1), in the orientation in which it was derived. A record is one
 *  delta of the conclusion; the union of the records of one premise is the persisted conclusion. */
class Record(val method: MethodKey, val direction: Direction, val premise: InitialAp, val conclusion: EdgeTree) {
    /** R3, §9.1: the reversal of each conclusion leaf near `a` (byExit returned this record for `a`), if mark-reversible.
     *  The reversed record has the reversed leaf as its premise and the reversed premise as its one-leaf conclusion. */
    fun reversedAt(a: Pattern): Sequence<Record> {
        val m = premise.manager
        val p = premise.toPattern()
        return ApOps(m).leaves(conclusion)
            .filter { it.fact.path.startsWith(a.fact.path) || a.fact.path.startsWith(it.fact.path) }   // the leaves that byExit found
            .mapNotNull { leaf ->
                val rev = revEdge(PathEdge(p.fact, leaf.fact, p.exclusion.union(leaf.exclusion))) ?: return@mapNotNull null
                Record(method, if (direction == Direction.FORWARD) Direction.BACKWARD else Direction.FORWARD,   // read in the other direction (R3)
                    m.initial(Pattern(rev.from, ExclusionSet.Empty)),        // the new premise has the Empty exclusion (§9.1)
                    m.treeOf(rev.to, rev.exclusion, demand = false))         // a one-leaf conclusion; a record is normal (R1)
            }
    }
}

/** ap.md §8.7. PERSISTENT, direction-neutral. */
interface RecordStore {
    fun add(record: Record)
    /** R2: candidates for an added fact `a` of a link, in the direction of the record: `around(base :: a.path)`. The reader
     *  tests `applicable || inside` (analyzer-core.md `recordApplies`). */
    fun byEntry(method: MethodKey, addedFact: Pattern): Sequence<Record>
    /** R2, R3: candidates for a reader in the other direction (PipelineStore.record_lookup). */
    fun byExit(method: MethodKey, fact: Pattern): Sequence<Record>
    /** A read-only view for a run (analyzer-core.md A4): add and persist throw. */
    fun view(): RecordStore
    /** R1, at a barrier. */
    fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>)
}

/** Written only at a barrier (no runner is alive); read by every runner of the next run through view(). */
class PersistentRecordStore(private val m: ApManager) : RecordStore {
    private val entry = HashMap<MethodKey, PathTrie<Record>>()          // R2: base :: premise path
    private val exit = HashMap<MethodKey, PathTrie<Record>>()           // R2: base :: leaf path, one entry per leaf
    private val merged = HashMap<Triple<MethodKey, Direction, InitialAp>, HashMap<AccessPathBase, TreeGroup>>()
    private val interner = m.newNodeInterner()

    override fun add(record: Record) {
        entry.getOrPut(record.method, ::PathTrie).add(record.premise.base, record.premise.pathArray, record)
        m.forEachLeafPosition(record.conclusion.root) { p -> exit.getOrPut(record.method, ::PathTrie).add(record.conclusion.base, p, record) }
    }

    override fun byEntry(method: MethodKey, addedFact: Pattern): Sequence<Record> =
        entry[method]?.around(addedFact.fact.base, addedFact.fact.path.toIntArray())?.asSequence().orEmpty()

    override fun byExit(method: MethodKey, fact: Pattern): Sequence<Record> =
        exit[method]?.around(fact.fact.base, fact.fact.path.toIntArray())?.asSequence()?.distinct().orEmpty()

    override fun view(): RecordStore = object : RecordStore by this {
        override fun add(record: Record) = error("read-only during a run (analyzer-core.md A4)")
        override fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>) = error("read-only")
        override fun view(): RecordStore = this
    }

    /** A delta per premise: TreeGroup (Part I §4.3) merges the same record of several runs, so a record never repeats. */
    override fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>) {
        for ((method, store) in summaries) for ((premise, g) in store.all()) {
            if (g.demand) continue                                       // normal only
            val j = premise.single ?: continue                           // ONE member; an ND or {zero, i} edge is never a record
            if (direction == Direction.BACKWARD && j.isZero) continue    // a zero-premise backward edge is never persisted
            val delta = merged.getOrPut(Triple(method, direction, j), ::HashMap)
                .getOrPut(g.base) { TreeGroup(m, interner) }.add(g) ?: continue
            add(Record(method, direction, j, delta))
        }
    }
}
```

### 7.9 `RequestStore`, `RequestKind` (`ap.md` §8.8)

```kotlin
/** A request of run 1 (ap.md §4.5, §4.10). */
sealed interface RequestKind {
    data class Mark(val mark: TaintMark) : RequestKind
    data class Position(val path: PathNode) : RequestKind               // a static position, cut to <= 2 accessors
}

/** ap.md §8.8. RUN 1 only. A mark request is keyed by `base :: i.path`, a position request by `S :: p`. */
class RequestStore {
    private val seen = HashSet<Pair<InitialAp, RequestKind>>()
    private val index = PathTrie<Pair<InitialAp, RequestKind>>()

    fun add(premise: InitialAp, kind: RequestKind): Boolean {
        check(premise.tail == Tail.STAR && premise.exclusion == ExclusionSet.Empty && premise.mark == MarkSlot.STAR)   // §4.5
        if (!seen.add(premise to kind)) return false                     // exact deduplication (E-3)
        when (kind) {
            is RequestKind.Mark -> index.add(premise.base, premise.pathArray, premise to kind)
            is RequestKind.Position -> index.add(STATIC, kind.path.toIntArray(), premise to kind)
        }
        return true
    }

    /** Event E2: every standing request that overlaps the added fact `a` (Store `standing_complete`). */
    fun overlapping(a: Pattern): Sequence<Pair<InitialAp, RequestKind>> =
        index.around(a.fact.base, a.fact.path.toIntArray()).asSequence().filter { (i, k) ->
            overlap(a, when (k) {
                is RequestKind.Mark -> i.toPattern()
                is RequestKind.Position -> Pattern(PathFact(STATIC, k.path.toList(), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)
            })
        }
}
```

Event E5/E7 (a new request) reads `AddedFactStore.overlapping(base, path)`; event E2 (a new link) reads
`RequestStore.overlapping(leaf)` for each new leaf. `ApOps.requestAction` (§5.10) gives the action of each pair.

### 7.10 `ConjunctionStore` (`ap.md` §8.9, `analyzer-core.md` §5.4)

```kotlin
/** ap.md §8.9. RUN. REPLACE of the rule assumptions of TaintSinkTracker (ap/ifds/taint/TaintSinkTracker.kt:173-240): the same "the
 *  last input sees every earlier input" join, per method, with premise SETS and layers. */
class ConjunctionStore(private val m: ApManager) {
    /** One input of a literal: its premise set and the layer of its contribution (§4.6: LiteralMatch), and for a conjunctive
     *  sink the triggered facts (§4.9: SinkCheck.Triggered). */
    data class Input(val premise: PremiseKey, val layer: Layer, val facts: EdgeTree? = null)
    class Combination(val premise: PremiseKey, val layer: Layer, val inputs: List<Input>)

    private val slots = HashMap<Pair<Any, CommonInst>, Array<LinkedHashSet<Input>>>()

    /** `rule`: a ConjunctiveEdge or a conjunctive SinkRule (interpreter.md §5.3). Returns the NEW full combinations. */
    fun add(rule: Any, statement: CommonInst, arity: Int, literal: Int, input: Input): List<Combination> {
        val slot = slots.getOrPut(rule to statement) { Array(arity) { LinkedHashSet() } }
        if (!slot[literal].add(input)) return emptyList()
        val out = ArrayList<Combination>()
        fun product(k: Int, acc: List<Input>) {                          // one input per literal, every combination
            if (k == arity) { out += combine(acc); return }
            if (k == literal) product(k + 1, acc + input) else for (x in slot[k]) product(k + 1, acc + x)
        }
        product(0, emptyList())
        return out
    }

    private fun combine(inputs: List<Input>) = Combination(
        m.premiseKey(inputs.flatMap { it.premise.initials }),          // the union; the zero fact is a member like every other
        if (inputs.any { it.layer == Layer.DEMAND }) Layer.DEMAND else Layer.NORMAL, inputs)

    /** analyzer-core.md §5.4 (E6): one join per (callee, premise key, layer of the publication, call statement). `S` is the
     *  link type of the analyzer (its Subscription), so this package does not depend on bidi.engine. */
    data class NdKey(val callee: MethodKey, val premise: PremiseKey, val layer: Layer, val call: CommonInst)
    private val joins = HashMap<NdKey, NdSummaryJoin<*>>()
    @Suppress("UNCHECKED_CAST")
    fun <S : Any> ndJoin(key: NdKey): NdSummaryJoin<S> =
        joins.getOrPut(key) { NdSummaryJoin<S>(m, key.premise.initials.size) } as NdSummaryJoin<S>
}

class NdSummaryJoin<S : Any>(m: ApManager, private val arity: Int) {
    private val conclusion = TreeGroup(m, m.newNodeInterner())             // the merged conclusion that has arrived so far
    private val byIndex = Array(arity) { LinkedHashSet<S>() }

    /** A subscription that satisfies member `index` (it goes under EVERY index that it satisfies): the new full combinations,
     *  each with the whole stored conclusion. */
    fun addSubscription(index: Int, s: S): List<Pair<List<S>, EdgeTree>> {
        if (!byIndex[index].add(s)) return emptyList()
        return combinations(fixed = index, value = s).flatMap { c -> conclusion.trees().map { c to it } }
    }

    /** A new conclusion delta: every full combination with the delta (the key holds no conclusion, so every order works). */
    fun addConclusion(g: EdgeTree): List<Pair<List<S>, EdgeTree>> {
        val delta = conclusion.add(g) ?: return emptyList()
        return combinations(fixed = -1, value = null).map { it to delta }
    }

    private fun combinations(fixed: Int, value: S?): List<List<S>>   // the cartesian product of byIndex, index `fixed` = value
}
```

### 7.11 `SourceHitStore` (`ap.md` §8.11)

```kotlin
/** ap.md §8.11. HAND-OFF of a backward run; owner: the backward RunMethodAnalyzer (O1). The forward form of a micro edge is a
 *  data class (PathEdge), equal in every run (interpreter.md I5). */
class SourceHitStore {
    private val hits = HashSet<Triple<MethodKey, CommonInst, PathEdge>>()
    fun add(method: MethodKey, statement: CommonInst, forward: PathEdge): Boolean = hits.add(Triple(method, statement, forward))
    /** The driver reads the hits at the barrier (O5) and makes the source seeds of the next forward run (§9.2). */
    fun entries(): Sequence<Triple<MethodKey, CommonInst, PathEdge>> = hits.asSequence()
}
```

### 7.12 `VulnerabilityStore` (`ap.md` §8.10)

```kotlin
typealias RuleId = CommonTaintConfigurationSink                        // REUSE: the same rule object in every run

/** ap.md §8.10: the key; the same key in two runs is the same vulnerability. */
data class VulnerabilityKey(val rule: RuleId, val method: MethodKey, val statement: CommonInst)

/** ap.md §4.9: a sink edge. `facts` is the triggered part of the conclusion tree (SinkCheck.Triggered), not one leaf. */
class SinkEdge(val premise: PremiseKey, val layer: Layer, val facts: EdgeTree)

/** One sink edge, or the sink edge set of a conjunctive sink; confirmed as a whole (analyzer-core.md §7.5). */
class SinkWitness(val edges: List<SinkEdge>, val run: Int, val endFacts: List<PathFact> = emptyList()) {
    @Volatile var confirmed: Boolean = false                           // set only at a barrier
}

interface VulnerabilityStore {
    fun add(key: VulnerabilityKey, witness: SinkWitness)
    fun witnessesOf(run: Int): Sequence<Pair<VulnerabilityKey, SinkWitness>>
}

/** PERSISTENT; any runner adds (O4). WITNESS MERGE (DD10): one entry per (key, run, shape); its fact trees are the union
 *  of the triggering parts of every witness with that shape. */
class ConcurrentVulnerabilityStore(private val m: ApManager) : VulnerabilityStore {
    /** The SHAPE of a witness: its run and, per literal, the premise set and the layer of its sink edge. */
    private data class Shape(val run: Int, val edges: List<Pair<PremiseKey, Layer>>)

    private val byKey = ConcurrentHashMap<VulnerabilityKey, ConcurrentHashMap<Shape, SinkWitness>>()

    override fun add(key: VulnerabilityKey, witness: SinkWitness) {
        val shape = Shape(witness.run, witness.edges.map { it.premise to it.layer })
        byKey.computeIfAbsent(key) { ConcurrentHashMap() }.merge(shape, witness, ::union)     // atomic per (key, shape)
    }

    /** Edge k of the result: the same premise set and layer; the facts are the union (T1) of the two triggering parts. Both
     *  parts have the same tree key: the base of literal k, the layer, concrete marks (so Empty and EMPTY, Part I §5.8). */
    private fun union(a: SinkWitness, b: SinkWitness): SinkWitness = SinkWitness(
        a.edges.zip(b.edges) { x, y -> SinkEdge(x.premise, x.layer, x.facts.withRoot(m.mergeAdd(x.facts.root, y.facts.root))) },
        a.run, (a.endFacts + b.endFacts).distinct())

    override fun witnessesOf(run: Int) = byKey.entries.asSequence()
        .flatMap { (k, byShape) -> byShape.values.asSequence().filter { it.run == run }.map { k to it } }
}
```

`analyzer-core.md` §4.7 says "it never merges two witnesses into one". This merge (DD10) is not that merge:

* The forbidden merge is LOSSY. Today `TaintVulnerability.mergeAdd` (`ap/ifds/taint/TaintSinkTracker.kt:27`) can drop a
  witness: an `Unconditional` node replaces a `Fact` node (`:50`), a `Fact` node with another trigger position is ignored
  (`:62`), and a `Fact` node replaces a `WithRequirement` node (`:79`). The premise sets of the dropped witness are lost.
* This merge joins only witnesses of the SAME shape: per literal, the same premise set and the same layer. The
  confirmation of `ap.md` §4.9 reads only these: condition 1 (the layer of each sink edge), condition 2 (each member of
  the premise set is zero or exact concrete) and condition 3 (the premise set is supported jointly). So the merged entry
  is confirmed exactly when each of its witnesses is confirmed. `analyzer-core.md` §7.5 step 2 gives the same answer.
* Each sink fact stays a leaf of the union tree. So the trace resolution (phase 5) can find each sink edge again.
* A conjunctive sink: the union of `(a1, b1)` and `(a2, b2)` also denotes `(a1, b2)`. That combination is a witness
  too: `a1` and `b2` are stored inputs of their literals at that statement, and `ConjunctionStore.add` (§7.10) gives
  every combination of the stored inputs.
* The run is part of the shape. So a witness of one run never merges with a witness of another run
  (`RunResult.hasDemandVulnerability`, `analyzer-core.md` §10, reads the witnesses of one run).
* The merge only makes the number of entries per key smaller: one entry per shape, not one per delta that triggers the
  sink.

The driver builds the report of `ap.md` §8.10 (state, pattern, end facts, run) at the barrier (`analyzer-impl.md` §7.6).

---

## 8. Test plan (`ap.md` §13)

Tests are in `core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ap/` and
`.../bidi/store/`, with `kotlin.test` as today (`ap/ifds/access/tree/AnyFieldMarkExclusionTest.kt`). Write each test
class before its code, in this order. Each row names the Lean theorem or `example` that it mirrors.

| # | Test class | Checks (`ap.md` §13 item) | Lean |
|---|---|---|---|
| 1 | `FactModelTest` | `MarkSet`/`ExclusionSet` canonical form, no empty `Concrete`; `PathNode`, `InitialAp`, `PremiseKey` interning gives identity; `AccessorTable` decodes as `AccessorInternerTest`; `payload() === Payload.EMPTY`, `leafMarks(true, MarkSet.EMPTY) === LeafMarks.STAR`; `FactNode` and `EdgeTree` equality across two interners (DD5) | — |
| 2 | `ApManagerConcurrencyTest` | 8 threads intern the same accessors, marks, paths and premises: one object each, no hang (a timeout fails the test) | — |
| 3 | `ReferenceDenotationTest` | `covers`, `overlap`, `applicable`, `inside`, `cleanPos` against `den` (`ap.md` §3.2) on a bounded universe with a fresh accessor and a fresh mark (item 2) | `coversB_sound`, `overlapB_of_common`, `cleanPos_inside_sound`, `cleanPos_disjoint_sound` |
| 4 | `ApplyEdgeVectorsTest` | every `example` of `Cases.lean` and `RestrictedCases.lean`, on the reference forms AND on `ApOps`; W6 vectors assert the demand layer (item 1) | `Cases.lean`, `RestrictedCases.lean` |
| 5 | `EdgeTreeEquivalenceTest` | random trees and edges (every tail and mark row, static exception, `*∖X`): the union of `ApOps.applyEdge` trees, read by `leaves`, equals the per-leaf `concat`, layer and mark exclusion included; the same for `restrict` (item 2) | `Tree.applyTreeE_mem`, `applyTreeE_den`, `applyTreeE_grouped_key`, `RStore.restrictTreeE_mem_U` |
| 6 | `MergeRulesTest` | T1; T2 and T2' only for equal content; the delta of T2 is the whole tree; no union across trees; T4 deltas union to the tree; a leaf below a stored `[any]` of the same mark gives null, also on its second arrival (the termination guard of T5) (item 8) | `Tree.rule1_mem`, `rule2_den`, `rule2_mark`, `Subsume.merge_inter`, `union_loses_pairs` |
| 7 | `SubsumptionTest` | `TreeGroup.add` drops exactly what `subsumes` (§6) drops; never across layers | `Subsume.subsumes_sound`, `recordSubsumesLB_layer` |
| 8 | `LayerRulesTest`, `MarkRulesTest` | items 3 and 4: the cut, W6, W2, demand in -> demand out; every row of the mark gate and of `compose`; the `check` preconditions fail | `Invariant.final_star_legal`, `applyEdge_demand_monotone`, `markComp_sound` |
| 9 | `FieldLimitTest` | `limit` equals the per-leaf `limit` (§6); `boundedDepth` equals a recount (the check of `TreeFieldLimitCheck`); W3 | `limitF_sound` |
| 10 | `CleanerTest` | every row of the two tables of `ap.md` §4.7; the split; no request for T ∈ X; the all-marks cleaner (item 5) | `CleanCases` in `Cases.lean`, `Core.cleanRes_sound`, `Exact.cleanRes_exact` |
| 11 | `TypeFilterTest` | accepted path passes with a `*` tail; rejected path drops; `FilterNext`; `and` is the conjunction; the mark policy drops a rejected concrete mark at the root path only, after the path filter (item 6; `interpreter.md` §5.1) | `Core.filt_keeps` (path part; the policy is gap G6, no theorem) |
| 12 | `SinkCheckTest` | the `check` vectors; `*∖X` with T ∈ X; the static premise; `without(c, Triggered.facts)` has no leaf of the triggered part and keeps every other leaf | `check_sound`, `check_request_star` |
| 13 | `EmissionTest`, `RestrictionTest` | every row of `ap.md` §6.3 and §6.4; two insertion orders; programs 1 and 2 (items 11, 12) | `RCore.emitM_inter`, `emitM_complete`, `RCases.p1_found_M`, `p2_found_M` |
| 14 | `RequestActionTest` | answer, climb, nothing; the chain answer; `ap.md` §4.10 items 2–4 (item 9) | `answerInit_covers`, `Statics.CexClean.shallow_misses` |
| 15 | `ReversalTest` | every row of `ap.md` §9.1 that occurs for a record, with `*∖X`; converse results on one concrete pair (item 15) | `Reverse.revEdge_exact`, `rev_starEx_exact` |
| 16 | `PathTrieTest` | `lookupPrefixes`, `lookupExtensions`, `around` equal their list filters on random keys (item 14) | `Store.lookupPrefixes_equiv`, `lookupExtensions_equiv`, `mem_around_indexBy` |
| 17 | `AddedFactStoreTest`, `RequestStoreTest`, `DemandStoreTest`, `RecordStoreTest`, `ConjunctionStoreTest`, `VulnerabilityStoreTest` | each index against its list filter; a new caller edge of an existing added fact is a new link (the example of `ap.md` §4.5); a backward edge `{jb} → zero` is stored and its repeat gives null (`MethodEdgeStoreTest`); a fully covered literal input is normal only (`matchLiteral`); E6 in two orders; the witness merge keeps every shape apart and every sink leaf, and the confirmation of a merged entry equals that of its witnesses (DD10) (items 7, 14) | `standing_complete`, `RStore.near_equiv`, `PipelineStore.record_lookup`, `ND.Example.c3_normal`, `NDConfirmed.CexSites.cex_sites` |

Example 1 — `ApplyEdgeVectorsTest`, the vector `a = b.f` on `(b, ., */{h}, *)` (`Cases.lean:64`, `ap.md` §4.2 table row 2):

```kotlin
package org.opentaint.dataflow.bidi.ap

class ApplyEdgeVectorsTest {
    private val m = ApManager(Cancellation())
    private val ops = ApOps(m)
    private val f = m.accessors.index(FieldAccessor("C", "f", "C"))
    private val h = m.accessors.index(FieldAccessor("C", "h", "C"))
    private val a = AccessPathBase.LocalVar(11)
    private val b = AccessPathBase.LocalVar(12)
    private val run1 = ApMode(run1 = true, Direction.FORWARD, fieldLimit = 8)

    private fun pf(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = MarkSlot.STAR) = PathFact(base, path, tail, mark)

    /** `a = b.f` with the keep edge of the read base (Cases.lean `loadF'`). */
    private val loadF = listOf(
        PathEdge(pf(b, emptyList(), Tail.STAR), pf(b, emptyList(), Tail.STAR), ExclusionSet.Empty),
        PathEdge(pf(b, listOf(f), Tail.STAR), pf(a, emptyList(), Tail.STAR), ExclusionSet.Empty))

    @Test
    fun `read of an abstract fact gives an any fact in the demand layer`() {
        val e1 = ExclusionSet.of(intArrayOf(h))
        val c = Conclusion(pf(b, emptyList(), Tail.STAR), e1, demand = false)
        val expected = Conclusion(pf(a, emptyList(), Tail.ANY), ExclusionSet.Empty, demand = true)

        // the reference form (ap.md §4.1)
        val ref = loadF.map { concat(c, it) }.filterIsInstance<EdgeOutcome.Fact>().map { it.conclusion }.filter { it.fact.base == a }
        assertEquals(listOf(expected), ref)

        // the tree form (ap.md §7.3): the same fact, the same layer, no request (Cases.lean:74)
        val premise = m.premiseKey(listOf(m.initial(b, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)))
        val tree = m.tree(b, e1, MarkSet.EMPTY, demand = false, m.leaf(m.payload(star = true)))
        val out = CollectingOut()
        for (e in loadF) ops.applyEdge(tree, premise, e, statementEdge = true, run1, out)
        val onA = out.trees.filter { it.base == a }
        assertEquals(listOf(Layer.DEMAND), onA.map { it.layer })
        assertEquals(listOf(Pattern(expected.fact, ExclusionSet.Empty)), onA.flatMap { ops.leaves(it).toList() })
        assertTrue(out.markRequests.isEmpty() && out.positionRequests.isEmpty())
    }
}
```

Example 2 — `EdgeTreeEquivalenceTest`, the property that makes the tree form safe (`Tree.applyTreeE_mem` and its
extension to the mark gate):

```kotlin
class EdgeTreeEquivalenceTest {
    private val gen = RandomFacts(seed = 42, accessors = 3, marks = 2, maxDepth = 3)   // a fresh accessor and mark are outside

    @Test
    fun `tree concat equals the per-leaf reference concat`() = repeat(10_000) {
        val (tree, premise) = gen.edgeTree()                      // a canonical EdgeTree with W1, W2, W6, N2
        val edge = gen.pathEdge()                                 // S7, S8 hold; every tail and mark
        val mode = gen.mode()                                     // run 1 or restricted (then only concrete trees)
        val treeOut = CollectingOut()
        gen.ops.applyEdge(tree, premise, edge, statementEdge = true, mode, treeOut)

        val refOut = gen.leavesAsConclusions(tree).map { concat(it, edge, staticIdentity = gen.isStaticIdentity(tree, premise, it), restricted = mode.restricted) }
        assertEquals(refOut.facts().toSet(), treeOut.trees.flatMap { gen.asConclusions(it) }.toSet())         // fact, layer, exclusion
        assertEquals(refOut.markRequests().toSet(), treeOut.markRequests.toSet())
        assertEquals(refOut.positionRequests().toSet(), treeOut.positionRequests.map { it.toList() }.toSet())
    }
}
```

After the unit tests pass, the analysis tests of `ap.md` §13 item 16 run through phase 3 (`analyzer-impl.md` §8.1).

---

## Part II — The IR interpreter (JVM)

Scope: `interpreter.md` behind the `Interpreter` interface of `analyzer-core.md` §4.9: the common forms and their
reversal (`org.opentaint.dataflow.bidi.interp`), and the JIR interpreter (`org.opentaint.dataflow.jvm.bidi.interp`)
(DD1). §2 gives the kinds of reuse.

Path prefixes in Part II:

* `DF/` = `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/`
* `JVM/` = `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/`
* `BWD/` = `JVM/backward/` on `origin/saloed/backward-main`

## 20. Package map

```
opentaint-dataflow  (language-neutral)
  org.opentaint.dataflow.bidi.interp
    Interpreter.kt        Interpreter, ExitNode, UnresolvedCallObserver          (analyzer-core.md §4.9)
    MicroEdges.kt         MicroEdge, keepEdge, strongKeep, starEdge, ZERO_FACT, ZERO_KEEP, ZERO_PATTERN
    StatementSummary.kt   StatementSummary + reversed()
    Rules.kt              SinkRule, RuleStatement + reversed(), ExitRules + reversed(), CleanStep
    CallPlan.kt           CallPoint, StageKind, Origin, Guard, CallStage + reversed(), CallPlan + reversed()
    MicroEdgeBuilder.kt   MicroEdgeBuilder (ADAPT of StatementSummaryBuilder)
    Forms.kt              FormsCache, MethodForms, DirectedForms        (analyzer-core.md §4.8, §4.9 direction table)
    FormsReference.kt     FormsReference: the per-path application of the forms (test oracle)
opentaint-jvm-dataflow
  org.opentaint.dataflow.jvm.bidi.interp
    JIRInterpreter.kt         JIRInterpreter : Interpreter
    JIRStatementForms.kt      statement summaries of non-call statements (ADAPT of JIRStatementSummary)
    JIRTypeFilters.kt         Part I's TypeFilter made from JIRFactTypeChecker (interpreter.md §5.1)
    JIRRuleForms.kt           rules -> micro edges, conjunctions, sink rules, cleaners; RulePos; RuleErrors
    JIRCallPlanBuilder.kt     the forward call plan (interpreter.md §3, §4.5, §4.6)
    JIRBoundaryForms.kt       entry rules, exit rules, exit nodes (interpreter.md §4.3, §4.7)
    JIRExitWiredGraph.kt      the exit wiring (PORT of BWD/JIRBackwardExitWiringGraph.kt)
    JIRMethodEntry.kt         JIRMethodEntry (per method), JIRMethodForms : MethodForms (per method key), JIRMethodEntries,
                              PrescanLambdas (analyzer-core.md §4.8, §9)
```

`JIRMethodContextCache` (`analyzer-impl.md` §3.4) holds one `JIRMethodEntries` and gives, per method key, its
`JIRMethodForms` (§31.2).

## 21. Reuse map

| Today | Kind | New |
|---|---|---|
| `DF/ap/ifds/summary/StatementSummaryBuilder.kt:12-143` | ADAPT | `MicroEdgeBuilder`: `PathEdge`s; a read keeps the whole base (`interpreter.md` D1, D2); no `to == null` edge; no `keepAliasPropagationEdges`; operand and result filters apart; `buildReversed` (:30-46) becomes `StatementSummary.reversed` |
| `DF/ap/ifds/summary/StatementSummary.kt` | REPLACE | `bidi.interp.StatementSummary` (the old class stays for the prescan) |
| `DF/ap/ifds/analysis/MethodSequentFlowFunction.kt:41-78` (`transfer`) | REPLACE | `ApOps.applyEdge` in the core; `FormsReference.statement` is its reference |
| `DF/graph/BackwardGraphs.kt:40-45` (`reversed`) | REUSE | the backward method graph |
| `DF/graph/MethodInstGraph.kt:25-46` (`build`) | REUSE | the compact graphs of `JIRMethodEntry` |
| `BWD/JIRBackwardExitWiringGraph.kt:10-63` | PORT | `JIRExitWiredGraph`; the wired node list is made once (today: on each `predecessors` call, :46-50) |
| `JVM/analysis/JIRStatementSummary.kt:24-117` | ADAPT | `JIRStatementForms`: the lhs filter is a result filter; a static field ref adds no filter on `S`; the read sources (`interpreter.md` §4.4) join the summary; no `buildReversed` |
| `JVM/analysis/JIRMethodSequentFlowFunction.kt` | ADAPT parts, REPLACE rest | exit sources and sinks (:136-226) -> `JIRBoundaryForms.exitRules`; the global-state drop (:186-188) -> `ExitRules.globalStateDrop`; the entry-mark drop (:300-305) -> `ExitRules.entryMarks`; read sources (:228-269) -> `JIRRuleForms.readSources`; type-info facts (:45-52) not used (prescan only) |
| `JVM/analysis/JIRMethodCallFlowFunction.kt` | ADAPT the order, REPLACE the evaluation | `JIRCallPlanBuilder`: sinks (:221-233), sources (:235-251), cleaners (:146-196), constructor (:213-216), unresolved (:253-339), aliases (:350-363) become stages |
| `JVM/analysis/JIRMethodStartFlowFunction.kt` | ADAPT | `JIRBoundaryForms.entryRules`: `locationClass` (:64-84) copied; entry sinks (:86-127); entry sources (:35-48) |
| `JVM/analysis/JIRMethodCallResolver.kt:159-211` | ADAPT | `JIRCallPlanBuilder.resolve`: no tracker subscription, no lambda event; the lambdas are the prescan values |
| `JVM/JIRCallResolver.kt:90-246` | GENERALIZE | `resolve(call, location, context: JIRCallResolutionContext)`; `JIRMethodAnalysisContext` implements the new interface (§28.4) |
| `JVM/analysis/JIRMethodCallRuleBasedSummaryRewriter.kt:54-88` | ADAPT | `JIRCallPlanBuilder.rewriterCleaners` |
| `JVM/analysis/JIRMethodCallSummaryHandler.kt` | REPLACE | aliases (:40-69, :98-101) -> stage `ALIASES` + `Guard.MemoryEffect`; rewriter (:71-79) -> stage `Rewrite`; exit mapping -> stage `BIND_BACK` |
| `JVM/analysis/JIRMethodSummaryEdgeProcessor.kt:15-25` | REMOVE | `interpreter.md` D14 |
| `JVM/analysis/JIRMethodAnalysisContext.kt` | SPLIT | per method -> `JIRMethodEntry`; caches (:41-76) -> `FormsCache`; `lambdaCallResolution` (:39) -> `PrescanLambdas`; `taintMarksAssignedOnMethodEnter` (:37) -> `ExitRules.entryMarks` |
| `JVM/analysis/JIRAnalysisManager.kt` | GENERALIZE | add `prescanLambdas()` over `contexts` (:76); `factTypeChecker`, `params` REUSE; ADAPT: `JIRMethodEntry.aliasAnalysis` copies the constructor call (:129-135), the old one stays (the prescan runs it) |
| `JVM/analysis/JIRAliasUtil.kt` | REUSE + GENERALIZE | REUSE `forEachAliasPathAtStatement` (:61-72), `apAccessor` (:77-81); add `aliasesPersistedThroughCall` (PORT of `BWD/../analysis/JIRAliasUtil.kt:31-35`); `forEachAliasAfterCallStatement` (:25-35) calls it |
| `JVM/JIRMethodCallFactMapper.kt` | ADAPT | `bindIn` (:210-242), `bindBack` (:141-205); `factIsRelevantToMethodCall` (:247-278) -> `CallPlan.touched` |
| `JVM/JIRFactTypeChecker.kt` | REUSE + GENERALIZE | REUSE `AccessorFilter` (:75-155) as `TypeFilter.may`; GENERALIZE: a public `localFilter(type)` gives it (today it is private); the mark policy moves to `TypeFilter.markPolicy` |
| `JVM/JIRLocalAliasAnalysis.kt` | REUSE | one per method in `JIRMethodEntry` |
| `JVM/JIRLocalVariableReachability.kt:27-31` | REUSE | `isLive` |
| `JVM/JIRLambdaTracker.kt` | REUSE | the source of the prescan values |
| `JVM/MethodFlowFunctionUtils.kt:37-73` | REUSE | `mkAccess`, `accessPathBase` |
| `JVM/JIRMarkAwareConditionRewriter.kt:18-52` | REUSE | the primary constructor (statement, alias analysis) |
| `JVM/taint/JIRBasicAtomEvaluator.kt` | REUSE | through the rewriter |
| `JVM/JIRCallPositionResolver.kt:35,51,77` | REUSE | `CallPositionToJIRValueResolver`, `CalleePositionToJIRValueResolver`, `JIRMethodPositionBaseTypeResolver` |
| `JVM/taint/TaintEvaluator.kt` | REUSE + ADAPT | REUSE `resolveBaseAp`, `resolveAp`, `toApAccessor` (:73-107); ADAPT the `<string-bytes>` rule (:43-61) |
| `JVM/taint/PrimitiveTaintExt.kt` | REUSE | `PRIMITIVE_TRACKING_ENABLED_MODE` in `isPrimitiveTracking` |
| `JVM/taint/TaintRulesProvider.kt` | REUSE | the REDUCED rule set (after `selectRules(relevantRuleIds)`) |
| `JVM/taint/JIRTaintAnalysisContext.kt` | REPLACE | direct `TaintRulesProvider` queries with the same rewriter (:107-122, :170-186); `handlePhase` (:188-194) not used |
| `JVM/taint/JIRSequentTaintUtil.kt`, `JVM/taint/JIRMethodCallTaintUtil.kt`, `DF/taint/TaintUtil.kt` | REPLACE | static forms + `ConjunctionStore` (Part I); the assumptions (`TaintUtil.kt:167-256`) go |
| `JVM/TaintConfigUtils.kt` | REPLACE | `applyPassThrough`, `applyCleaner` evaluate on a fact; the forms are static |
| `DF/taint/RuleConditionRewriter.kt:8-14`, `DF/taint/TaintMarkAwareConditionExpr.kt:48-50,110-123` | REUSE | `rewrite`, `removeTrueLiterals`, `explodeToDNF` |
| `DF/taint/PositionAccess.kt` | REUSE | `accessors()`, `base()` |
| `JVM/analysis/JIRMethodGetDefault.kt:37-51` | REUSE | the default getter rules |
| `JVM/analysis/JIRMethodEntrypointResolver.kt:11-16` | REUSE | the callee method keys |
| `DF/ap/ifds/taint/ExternalMethodTracker` | REUSE | through `UnresolvedCallObserver` (§28.5): the core calls it when an added fact reaches an unresolved callee, as today per fact (`JIRMethodCallFlowFunction.kt:285-295`) |
| `DF/util/SoftReferenceManager.kt` | NOT USED | the forms stay strongly held: their objects are keys of the run stores (§31.2) |

## 22. Names from Part I and additions to `analyzer-core.md` §4.9

### 22.1 Names from Part I

Part II uses these names of Part I with the signatures of the Part I section.

| Name | Part I | Use in Part II |
|---|---|---|
| `AccessorIdx` (`Int`), `ApManager.accessors.index(a: Accessor)`, `accessors.accessor(i)` | §3.1 (DD6) | every path element; the JIR builders convert a JIR `Accessor` with `manager.accessors.index(a)` |
| `TaintMark(id)` (value class), `TaintMark.ZERO`, `ApManager.marks.mark(name)`, `marks.name(m)` | §3.1 (DD7) | the rule marks; the zero mark; `isPrimitiveTracking` |
| `AccessPathBase.Zero` | §2, §3.4 (DD8) | the zero base |
| `Tail`, `MarkSlot` (`MarkSlot.STAR`, `Star`, `Concrete`), `MarkSet`, `ExclusionSet` (`of(ids)`, `of(a: AccessorIdx)`), `Direction` | §3.2 | the forms |
| `PathNode`, `ApManager.path(p: List<AccessorIdx>): PathNode?` | §3.3, §5.1 | the path of a `Cleaner` |
| `ApManager`, `MethodKey` | §5.1, §0.1 (K4) | the builders; the forms |
| `TypeFilter(may: FactTypeChecker.FactApFilter, markPolicy: MarkPolicy? = null)`, `fun interface MarkPolicy { fun keeps(mark: TaintMark): Boolean }`, `TypeFilter.and` | §5.5 (DD9) | `StatementSummary.typeFilters`, `resultFilters` |
| `ConjunctiveEdge(literals: List<Pattern>, target: PathFact)` | §5.8 | the conjunctive sources and pass rules |
| `PathFact(base, path: List<AccessorIdx>, tail, mark)`, `Pattern(fact, exclusion)`, `PathEdge(from, to, exclusion)`, `Conclusion`, `EdgeOutcome`, `concat` | §6 (DD2) | the micro edges; `FormsReference` |
| `revEdge(e: PathEdge): PathEdge?` | §6 | every `reversed()` |
| `Cleaner(base, path: PathNode?, reach: CleanReach, mark: TaintMark?)`, `enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }` | §6 | `CleanStep.Clean`, the summary rewriter |

### 22.2 Additions to the interface of `analyzer-core.md` §4.9

`analyzer-core.md` §4.9 gives the interpreter interface. Part II adds these members. `analyzer-impl.md` calls them.

| What | Why | Code |
|---|---|---|
| `StatementSummary.resultFilters` (default empty) | `interpreter.md` §2.1 step 5 and the binding-back filters of `interpreter.md` §3.1 act on the results. One map per base cannot hold the operand filter and the result filter of one base (`x = x.f`; `o.m(this)`). | §23.2 |
| `CallStage.Edges.kind: StageKind`, with the member `StageKind.statementEdges` | The core must find the sources stage (the source seeds and the source hits), the statement micro edges (the static exception of `ap.md` §4.10 item 1) and the `Origin` of a fact. | §23.5 |
| `Origin`; the `Guard` members `SinkTriggered(sink)` and `MemoryEffect` (`admits(origin)`) | `analyzer-core.md` §4.9 names `Guard` but does not define it. The alias guard needs the origin of a fact (`interpreter.md` §3.8 AC3, AC4). | §23.5 |
| `SinkRule(rule, patterns, endFacts)`, with `unconditional`, `conjunctive`, `seedPatterns()` | `analyzer-core.md` §4.9 names `SinkRule` but does not define it. | §23.4 |
| `ExitRules.entryMarkParts(base)` | The core removes the entry marks of `interpreter.md` §4.7 step 4 exactly, with `ApOps.without`. | §23.4 |
| `MicroEdge.isSource`, `MicroEdge.isIdentity`, `StatementSummary.edgesOf`, `CallPlan.stagesFrom` | The source-seed places (`analyzer-core.md` §4.7), the alias guard (AC4), the edges of one base, the stages from one point. | §23.1, §23.2, §23.6 |
| the stage `AFTER → BEFORE` of kind `PASS_OVER` in `CallPlan.reversed()` | The identity edge `b.* → b.*` of an alias base (`analyzer-core.md` §4.5, `interpreter.md` A5). The step table of `analyzer-core.md` §4.5 has no such stage (spec issue SI9). | §23.6 |
| `FormsCache`, `MethodForms`, `DirectedForms` | The forms cache of `analyzer-core.md` §4.8 and the direction table of `analyzer-core.md` §4.9. `analyzer-impl.md` §3.4 uses them. | §23.7 |
| `UnresolvedCallObserver` (`reached(call, position, plan)`); `JIRInterpreter` implements it | The external method tracker records the taint that reaches an unresolved callee, as today. | §28.5 |

---

## 23. The common forms (`bidi.interp`)

Implements `analyzer-core.md` §4.9, `ap.md` §9.1, §9.2, `interpreter.md` §4.9.

### 23.1 Interpreter and micro edges

```kotlin
package org.opentaint.dataflow.bidi.interp

/** analyzer-core.md §4.9, unchanged. The interpreter gives FORWARD forms only. */
interface Interpreter {
    fun entryNode(method: MethodKey): CommonInst
    fun exitNodes(method: MethodKey): List<ExitNode>
    fun entryRules(method: MethodKey): RuleStatement
    fun exitRules(method: MethodKey, exit: CommonInst): ExitRules
    fun statementSummary(method: MethodKey, statement: CommonInst): StatementSummary
    fun callPlan(caller: MethodKey, statement: CommonInst, call: CommonCallExpr): CallPlan
    fun isLive(method: MethodKey, base: AccessPathBase, statement: CommonInst): Boolean
    fun isSummaryBase(base: AccessPathBase): Boolean
}

class ExitNode(val node: CommonInst, val exceptional: Boolean)

/** THE SOURCE-SEED PLACES (analyzer-core.md §4.7). The core applies the source-seed filter (forward restricted run) and
 *  records the source hits (backward run) ONLY on an `isSource` edge of: a statement summary, `RuleStatement.summary`
 *  (entry and exit rules), and a `StageKind.SOURCES` stage. NEVER on `RuleStatement.endFacts`, `SinkRule.endFacts` or a
 *  `StageKind.END_FACTS` stage: an end fact has the shape `zero -> P.$ (T)` of a source, but it applies as usual. */
class MicroEdge(val edge: PathEdge, val forward: PathEdge) {
    /** analyzer-core.md §4.7: a SOURCE goes from the zero fact to another base (forward form). */
    val isSource: Boolean get() = forward.from.base == AccessPathBase.Zero && forward.to.base != AccessPathBase.Zero
    /** interpreter.md §3.8 AC4: `x.p.* -> x.p.*` with no exclusion. */
    val isIdentity: Boolean get() = edge.from == edge.to && edge.exclusion == ExclusionSet.Empty
    companion object { fun of(e: PathEdge) = MicroEdge(e, e) }
}

val ZERO_FACT: PathFact = PathFact(AccessPathBase.Zero, emptyList(), Tail.EXACT, MarkSlot.Concrete(TaintMark.ZERO))   // DD8, DD7
val ZERO_PATTERN: Pattern = Pattern(ZERO_FACT, ExclusionSet.Empty)
/** interpreter.md I11 (d): the keep edge `zero.$ (zeroMark) -> zero.$ (zeroMark)`. */
val ZERO_KEEP: PathEdge = PathEdge(ZERO_FACT, ZERO_FACT, ExclusionSet.Empty)

// DD6: a path element is an AccessorIdx.
fun starSide(b: AccessPathBase, p: List<AccessorIdx> = emptyList()) = PathFact(b, p, Tail.STAR, MarkSlot.STAR)
/** interpreter.md §2.1 `keepEdge`. */
fun keepEdge(b: AccessPathBase, p: List<AccessorIdx> = emptyList(), e: ExclusionSet = ExclusionSet.Empty) =
    PathEdge(starSide(b, p), starSide(b, p), e)
/** interpreter.md §2.1 `strongKeep`: one keep edge per proper prefix, the next accessor excluded (I3). */
fun strongKeep(b: AccessPathBase, path: List<AccessorIdx>): List<PathEdge> =
    path.indices.map { k -> keepEdge(b, path.take(k), ExclusionSet.of(path[k])) }                        // ExclusionSet.of(a): Part I §3.2
/** A move, a binding or an alias edge `x.p.* -> y.q.*` (I4: `*` tail, mark `*`). */
fun starEdge(from: AccessPathBase, fp: List<AccessorIdx>, to: AccessPathBase, tp: List<AccessorIdx>) =
    PathEdge(starSide(from, fp), starSide(to, tp), ExclusionSet.Empty)
```

### 23.2 Statement summary and its reversal

`typeFilters` are the OPERAND filters (on the input, `interpreter.md` §2.1 step 3). `resultFilters` are the LHS and
binding-back filters (on the results, step 5). One map cannot hold both (§22.2): in `x = x.f`, and in `o.m(this)`, where
the callee base `this` and the caller base `this` differ.

```kotlin
class StatementSummary(
    val touched: Set<AccessPathBase>,
    val edges: List<MicroEdge>,
    val conjunctions: List<ConjunctiveEdge>,
    val typeFilters: Map<AccessPathBase, TypeFilter>,
    val resultFilters: Map<AccessPathBase, TypeFilter> = emptyMap(),          // an addition (Part II §22.2)
) {
    private val byBase: Map<AccessPathBase, List<MicroEdge>> = edges.groupBy { it.edge.from.base }
    fun edgesOf(b: AccessPathBase): List<MicroEdge> = byBase[b].orEmpty()

    /** ap.md §9.1, §9.2; interpreter.md §4.9 STATEMENTS; Lean `Reverse.Stmt.rev`. */
    fun reversed(): StatementSummary {
        val targets = LinkedHashSet<AccessPathBase>()
        edges.mapTo(targets) { it.edge.to.base }
        conjunctions.mapTo(targets) { it.target.base }
        val rev = ArrayList<MicroEdge>()
        for (e in edges) rev += MicroEdge(revOrFail(e.edge), e.forward)
        for (c in conjunctions) for (lit in c.literals) {                                  // an OR of the requirements
            val fwd = PathEdge(lit.fact, c.target, ExclusionSet.Empty)                    // a literal is a Pattern (Part I §5.8)
            rev += MicroEdge(revOrFail(fwd), fwd)
        }
        for (b in targets) if (b !in touched) rev += MicroEdge.of(keepEdge(b))            // A5, Lean `idEdge`
        return StatementSummary(touched + targets, rev, emptyList(), emptyMap())         // no filter (§5.1 last rows)
    }

    /** The identity edges of `bases`, added to this summary (touched too). */
    fun withIdentities(bases: Collection<AccessPathBase>): StatementSummary =
        if (bases.isEmpty()) this
        else StatementSummary(touched + bases, edges + bases.map { MicroEdge.of(keepEdge(it)) }, conjunctions,
            typeFilters, resultFilters)

    companion object {
        val EMPTY = StatementSummary(emptySet(), emptyList(), emptyList(), emptyMap())
        fun identities(bases: Collection<AccessPathBase>) = EMPTY.withIdentities(bases)
    }
}

/** I11 (b): every statement micro edge is mark-reversible; a binding has `*` marks (S10). */
internal fun revOrFail(e: PathEdge): PathEdge = revEdge(e) ?: error("not mark-reversible (interpreter.md I11 (b)): $e")   // revEdge: Part I §6
```

### 23.3 The three application modes

The core applies a `StatementSummary` in one of three modes. The mode comes from the place of the form, not from a
field. `FormsReference` (§23.8) is the per-path reference of each mode.

| Mode | Forms | Rule |
|---|---|---|
| STATEMENT | `statementSummary`, `RuleStatement.summary`, `CleanStep.Kill.keepEdges` | `interpreter.md` §2.1 steps 2–5: an untouched base passes; a touched base keeps only what an edge gives |
| STAGE | `CallStage.Edges.summary` | only the edges give results; the plan relevance (`CallPlan.touched`) does the pass-over (`analyzer-core.md` §4.5). A stage summary has every base of its edges in `touched`, so `reversed()` adds no identity edge |
| GEN | `RuleStatement.endFacts`, `SinkRule.endFacts` | the input stays where it is; the edges add results (`interpreter.md` §4.1 END FACTS, §4.7 step 2) |

### 23.4 Sinks, rule statements, exit rules, clean steps

```kotlin
/** One alternative (one DNF cube) of one sink rule at one place (interpreter.md §4.1, §4.2; ap.md §4.9). */
class SinkRule(
    val rule: CommonTaintConfigurationSink,
    val patterns: List<Pattern>,          // one per positive literal; [ZERO_PATTERN] for an unconditional sink
    val endFacts: List<MicroEdge>,        // GEN: zero.$ (zeroMark) -> P.$ (T) per `trackFactsReachAnalysisEnd` action
) {
    val unconditional: Boolean get() = patterns.size == 1 && patterns[0].fact.base == AccessPathBase.Zero
    val conjunctive: Boolean get() = patterns.size >= 2                         // ap.md §4.9, §8.9
    /** ap.md §9.2 SINK SEEDS: one requirement per positive literal; none for an unconditional sink. */
    fun seedPatterns(): List<Pattern> = if (unconditional) emptyList() else patterns
}

/** analyzer-core.md §4.9. `summary` is STATEMENT mode; `endFacts` is GEN mode (the union of `sinks[*].endFacts`). */
class RuleStatement(val summary: StatementSummary, val endFacts: StatementSummary, val sinks: List<SinkRule>) {
    /** interpreter.md §4.9 RULE ROLES: the sources and the end facts reverse; the sinks stay (the place of the seeds);
     *  every filter goes (the context filter of the entry rules too). */
    fun reversed(): RuleStatement {
        val s = summary.reversed()
        // Forward, an end-fact target is a GEN target: it passes the place. So the requirement on it passes (A5).
        val genTargets = endFacts.edges.map { it.edge.to.base }.filter { it !in s.touched }.toSet()
        val revEnd = StatementSummary(emptySet(), endFacts.edges.map { MicroEdge(revOrFail(it.edge), it.forward) },
            emptyList(), emptyMap())
        return RuleStatement(s.withIdentities(genTargets), revEnd, sinks)
    }
    companion object { val EMPTY = RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, emptyList()) }
}

/** interpreter.md §4.7, at an exit (normal or exceptional). `globalStateDrop`: step 3 applies (the exit has an exit sink).
 *  `entryMarks`: step 4. Steps 3 to 5 apply only at the normal exit, so at the exceptional exit `globalStateDrop` is false
 *  and `entryMarks` is empty. */
class ExitRules(val rules: RuleStatement, val globalStateDrop: Boolean, val entryMarks: Set<TaintMark>) {
    /** interpreter.md §4.9: the reversal drops G2 (steps 3 and 4). */
    fun reversed(): RuleStatement = rules.reversed()

    /** interpreter.md §4.7 step 4, "as today" (`JIRMethodSequentFlowFunction.kt:300-314`): today `TaintMarkRemover`
     *  rejects only a mark child of the ROOT and accepts every other child with its whole subtree. So only the `$` leaf
     *  `(b, [], $, T)` of an entry mark goes; `b.f.$ (T)` and `b.[any] (T)` stay. The core removes each part with
     *  `ops.without(tree, ops.targetTree(part, tree.layer))` (Part I §5.8): exact, the other leaves stay in their layer.
     *  A cleaner is not exact here: `atAndBelow` drops the deeper leaves, and `exact` moves a root `[any]` leaf to the
     *  demand layer (ap.md §4.7). */
    fun entryMarkParts(base: AccessPathBase): List<PathFact> =
        if (base != AccessPathBase.This && base !is AccessPathBase.Argument) emptyList()
        else entryMarks.map { PathFact(base, emptyList(), Tail.EXACT, MarkSlot.Concrete(it)) }

    companion object { val EMPTY = ExitRules(RuleStatement.EMPTY, false, emptySet()) }
}

/** analyzer-core.md §4.9, unchanged. `Kill.keepEdges` is STATEMENT mode with `touched = {S}`. Each step is its own
 *  reversal (ap.md §9.2; Lean `Reverse.revInstr`). */
sealed interface CleanStep {
    class Clean(val cleaner: Cleaner) : CleanStep
    class Kill(val keepEdges: StatementSummary) : CleanStep
}
```

### 23.5 Call points, stages, guards

`StageKind` is an addition to `analyzer-core.md` §4.9 (§22.2). The core needs it for three things: the static
exception (the statement micro edges at a call, `ap.md` §4.10 item 1), the source seeds and the source hits of the
sources stage (`analyzer-core.md` §4.7), and the `Origin` of a fact for the alias guard.

```kotlin
enum class CallPoint { BEFORE, BOUND, ADDED, RETURNED, REWRITTEN, AFTER }

enum class StageKind {
    BIND_IN, END_FACTS, SOURCES, UNRESOLVED, CONSTRUCTOR, BIND_BACK, ALIASES,
    PASS_OVER;                                   // reversed plans only: the identity of the alias bases (A5, Part II §23.6)
    /** ap.md §4.10 item 1: these are statement micro edges (with `CleanStep.Kill`). */
    val statementEdges: Boolean get() = this == SOURCES || this == UNRESOLVED
}

/** interpreter.md §3.8 AC3, AC4: where a forward fact at REWRITTEN comes from. The core sets it at the stage that made
 *  the fact and keeps it through the rewriter. */
enum class Origin {
    SOURCE,          // StageKind.SOURCES                                                       (AC3)
    END_FACT,        // StageKind.END_FACTS                                                     (AC3)
    PASS,            // StageKind.UNRESOLVED, an edge that is not `isIdentity`                  (AC3)
    SUMMARY_EFFECT,  // a summary or record j -> g with g not the start fact of j; any zero premise (AC3)
    IDENTITY,        // an identity summary, an identity edge of UNRESOLVED, StageKind.CONSTRUCTOR (AC4)
}

/** A forward-only selection of the inputs of a stage (analyzer-core.md §4.9). The reversal drops it. */
sealed interface Guard {
    /** interpreter.md §4.1 END FACTS. The sink TRIGGERS at BOUND: for a plain sink, `checkSink` gives `Triggered` on a
     *  bound fact of the caller edge `(i, layer)` (the layer of that sink edge); for a conjunctive sink, the conjunction
     *  store gives a new full combination (the layer of the combination; ap.md §4.9, §8.9). Then the core applies the
     *  stage to the ZERO fact, with that layer: `Zero -> (s, P.$ (T))`. Each result goes to REWRITTEN with
     *  `Origin.END_FACT`. */
    class SinkTriggered(val sink: SinkRule) : Guard
    /** interpreter.md §3.8 AC3, AC4. Today: `JIRMethodCallSummaryHandler.kt:59-63, 98-101`, `JIRMethodCallFlowFunction.kt:353-363`. */
    data object MemoryEffect : Guard {
        fun admits(o: Origin): Boolean = o != Origin.IDENTITY
    }
}

sealed interface CallStage {
    val from: CallPoint
    val to: CallPoint
    fun reversed(): CallStage

    /** `kind` is an addition to analyzer-core.md §4.9 (Part II §22.2). The summary is STAGE mode. */
    data class Edges(override val from: CallPoint, override val to: CallPoint, val kind: StageKind,
                     val summary: StatementSummary, val guard: Guard? = null) : CallStage {
        override fun reversed() = Edges(to, from, kind, summary.reversed(), guard = null)     // no guard, no filter
    }
    data class Clean(override val from: CallPoint, override val to: CallPoint, val steps: List<CleanStep>) : CallStage {
        override fun reversed() = Clean(to, from, steps)                                      // own reversal
    }
    data class Rewrite(override val from: CallPoint, override val to: CallPoint, val cleaners: List<Cleaner>) : CallStage {
        override fun reversed() = Rewrite(to, from, cleaners)
    }
    data class Callees(override val from: CallPoint, override val to: CallPoint, val callees: List<MethodKey>) : CallStage {
        override fun reversed() = Callees(to, from, callees)                                  // backward summaries
    }
}
```

### 23.6 The call plan and its reversal

```kotlin
class CallPlan(val touched: Set<AccessPathBase>, val stages: List<CallStage>, val sinks: List<SinkRule>,
               val entry: CallPoint, val exit: CallPoint) {
    /** analyzer-core.md §4.5: the stages from one point read the same facts; their order does not matter. */
    val stagesFrom: Map<CallPoint, List<CallStage>> = stages.groupBy { it.from }

    /** analyzer-core.md §4.5 THE REVERSAL; Lean `Reverse.Call.rev` (toCallee and fromCallee swap and reverse). */
    fun reversed(): CallPlan {
        check(entry == CallPoint.BEFORE && exit == CallPoint.AFTER) { "the core reverses only a forward plan" }
        val aliasBases = stages.asSequence()
            .filter { it.to == exit }.filterIsInstance<CallStage.Edges>()
            .flatMap { st -> st.summary.edges.asSequence().map { it.edge.to.base } }
            .filterTo(LinkedHashSet()) { it !in touched }
        val rev = stages.mapTo(ArrayList()) { it.reversed() }
        // Forward, an alias base is untouched: its fact passes over the call. Backward, it is touched (for the reversed
        // alias edges), so its requirement passes over by an explicit identity stage from the entry to the exit (A5).
        if (aliasBases.isNotEmpty())
            rev += CallStage.Edges(CallPoint.AFTER, CallPoint.BEFORE, StageKind.PASS_OVER, StatementSummary.identities(aliasBases))
        return CallPlan(touched + aliasBases, rev, sinks, entry = exit, exit = entry)
    }
}
```

The reversed plan of a JVM call against the backward call order (`interpreter.md` §4.9; `analyzer-core.md` §4.5 table).
`JIRCallPlanBuilder` (§28) makes the forward stages; `reversed()` makes the right column:

| Backward step | Forward stage (§28) | Reversed stage |
|---|---|---|
| 1 relevance | `touched` = `{S, o, ai, r}` | `touched + aliasBases` |
| 2 reversed binding back, alias edges, alias identity | `REWRITTEN→AFTER BIND_BACK`, `REWRITTEN→AFTER ALIASES (MemoryEffect)` | `AFTER→REWRITTEN BIND_BACK`, `AFTER→REWRITTEN ALIASES` (no guard), `AFTER→BEFORE PASS_OVER` |
| 3 reversed sources, end facts | `BOUND→REWRITTEN SOURCES`, `BOUND→REWRITTEN END_FACTS (SinkTriggered)` | `REWRITTEN→BOUND SOURCES`, `REWRITTEN→BOUND END_FACTS` (no guard) |
| 4 reversed rewriter | `RETURNED→REWRITTEN Rewrite` | `REWRITTEN→RETURNED Rewrite` |
| 5.1 resolved callees | `ADDED→RETURNED Callees` | `RETURNED→ADDED Callees` |
| 5.2 unresolved callee | `ADDED→RETURNED UNRESOLVED` (identity; pass rules) | `RETURNED→ADDED UNRESOLVED` (both) |
| 5.3 constructor | `ADDED→REWRITTEN CONSTRUCTOR` | `REWRITTEN→ADDED CONSTRUCTOR` |
| 6 reversed cleaners, kill | `BOUND→ADDED Clean` | `ADDED→BOUND Clean` (same steps) |
| 7 seeds, read positions | `sinks` at `BOUND` | `sinks` at `BOUND` (the core seeds there) |
| 8 reversed binding in | `BEFORE→BOUND BIND_IN` | `BOUND→BEFORE BIND_IN` |
| 9 field limit | exit `AFTER` | exit `BEFORE` |

### 23.7 Forms cache and the direction view

Implements `analyzer-core.md` §4.8 (the forward forms and their reversals, made once) and the table "What the core uses in
each direction" of `analyzer-core.md` §4.9. `MethodContextCache.directed()` makes the `DirectedForms` of a run, and
`RunManager.forms` keeps it (`analyzer-impl.md` §3.2, §3.4).

```kotlin
/** A forward form and its reversal per slot (a statement index), each made once. Runs are sequential and one runner
 *  uses a method (analyzer-core.md O1), so a plain array is enough; a race only makes an equal form twice. */
class FormsCache<F : Any>(size: Int, private val reverse: (F) -> F) {
    private val slots = arrayOfNulls<Any>(2 * size)
    @Suppress("UNCHECKED_CAST")
    fun get(slot: Int, direction: Direction, forward: () -> F): F {
        val f = (slots[2 * slot] ?: forward().also { slots[2 * slot] = it }) as F
        if (direction == Direction.FORWARD) return f
        return (slots[2 * slot + 1] ?: reverse(f).also { slots[2 * slot + 1] = it }) as F
    }
}

/** The cached forms of one method key in both directions. The language part implements it (Part II §31.2). */
interface MethodForms {
    fun statement(direction: Direction, s: CommonInst): StatementSummary
    fun call(direction: Direction, s: CommonInst, call: CommonCallExpr): CallPlan
    fun entryRules(direction: Direction): RuleStatement                    // BACKWARD: `entryRules.reversed()`
    fun exitRules(direction: Direction, exit: CommonInst): ExitRules       // BACKWARD: `ExitRules(exitRules.reversed(), false, {})`
}

/** analyzer-core.md §4.9 table "What the core uses in each direction". */
class DirectedForms(val interp: Interpreter, val direction: Direction, private val forms: (MethodKey) -> MethodForms) {
    private val fwd get() = direction == Direction.FORWARD
    /** analyzer-core.md §4.4: forward the entry; backward every exit for the zero fact, the normal exits for another fact. */
    fun startNodes(m: MethodKey, zero: Boolean): List<CommonInst> =
        if (fwd) listOf(interp.entryNode(m)) else interp.exitNodes(m).filter { zero || !it.exceptional }.map { it.node }
    fun startRules(m: MethodKey, node: CommonInst): RuleStatement =
        if (fwd) forms(m).entryRules(Direction.FORWARD) else forms(m).exitRules(Direction.BACKWARD, node).rules
    fun statement(m: MethodKey, s: CommonInst) = forms(m).statement(direction, s)
    fun call(m: MethodKey, s: CommonInst, c: CommonCallExpr) = forms(m).call(direction, s, c)
    fun endNodes(m: MethodKey): List<CommonInst> =
        if (fwd) interp.exitNodes(m).filter { !it.exceptional }.map { it.node } else listOf(interp.entryNode(m))
    fun endRules(m: MethodKey, node: CommonInst): ExitRules =
        if (fwd) forms(m).exitRules(Direction.FORWARD, node)
        else ExitRules(forms(m).entryRules(Direction.BACKWARD), globalStateDrop = false, entryMarks = emptySet())
    fun isLive(m: MethodKey, b: AccessPathBase, s: CommonInst) = !fwd || interp.isLive(m, b, s)
}
```

### 23.8 Reference application (test oracle)

The tests compare the core and the reversal with this per-path code. It uses `concat` of `ap.md` §4.1 (Part I,
`Reference.kt`). It has no field limit, no static exception, no request and no conjunction. It reads a type filter as
`ApOps.filter` reads it (Part I §5.5, DD9): `may` on the path, then the mark policy on a concrete mark at the root path.

```kotlin
class FormsReference(private val manager: ApManager) {
    private fun outs(edges: List<MicroEdge>, c: Conclusion) =
        edges.mapNotNull { (concat(c, it.edge) as? EdgeOutcome.Fact)?.conclusion }

    private fun passes(f: Map<AccessPathBase, TypeFilter>, c: Conclusion): Boolean {
        val tf = f[c.fact.base] ?: return true
        var may: FactTypeChecker.FactApFilter = tf.may
        for (a in c.fact.path) when (val r = may.check(manager.accessors.accessor(a))) {
            FactTypeChecker.FilterResult.Accept -> break
            FactTypeChecker.FilterResult.Reject -> return false
            is FactTypeChecker.FilterResult.FilterNext -> may = r.filter
        }
        val mark = (c.fact.mark as? MarkSlot.Concrete)?.mark
        return c.fact.path.isNotEmpty() || mark == null || tf.markPolicy?.keeps(mark) != false
    }

    /** STATEMENT: interpreter.md §2.1 steps 2-5. */
    fun statement(s: StatementSummary, c: Conclusion): List<Conclusion> = when {
        c.fact.base !in s.touched -> listOf(c)
        !passes(s.typeFilters, c) -> emptyList()
        else -> outs(s.edgesOf(c.fact.base), c).filter { passes(s.resultFilters, it) }
    }
    /** STAGE: only the edges. */
    fun stage(s: StatementSummary, c: Conclusion): List<Conclusion> =
        if (!passes(s.typeFilters, c)) emptyList() else outs(s.edgesOf(c.fact.base), c).filter { passes(s.resultFilters, it) }
    /** GEN: the added results only. */
    fun gen(s: StatementSummary, c: Conclusion): List<Conclusion> = outs(s.edgesOf(c.fact.base), c)

    /** One fact through a plan, no guard. Gives every (point, fact) that it reaches. */
    fun run(plan: CallPlan, c: Conclusion, callee: (Conclusion) -> List<Conclusion>,
            clean: (Conclusion, Cleaner) -> List<Conclusion>): List<Pair<CallPoint, Conclusion>> {
        val seen = LinkedHashSet<Pair<CallPoint, Conclusion>>()
        val work = ArrayDeque<Pair<CallPoint, Conclusion>>()
        when {                                                                      // analyzer-core.md §4.5 "the zero fact"
            c.fact.base == AccessPathBase.Zero -> { seen += plan.exit to c; work.addLast(plan.entry to c) }   // passes over AND enters
            c.fact.base !in plan.touched -> return listOf(plan.exit to c)                                       // relevance (step 1)
            else -> work.addLast(plan.entry to c)
        }
        while (work.isNotEmpty()) {
            val (p, f) = work.removeFirst()
            if (!seen.add(p to f)) continue
            for (st in plan.stagesFrom[p].orEmpty()) {
                val outs = when (st) {
                    is CallStage.Edges -> stage(st.summary, f)
                    is CallStage.Clean -> st.steps.fold(listOf(f)) { fs, step -> fs.flatMap { x -> when (step) {
                        is CleanStep.Clean -> clean(x, step.cleaner)
                        is CleanStep.Kill -> statement(step.keepEdges, x) } } }
                    is CallStage.Rewrite -> st.cleaners.fold(listOf(f)) { fs, cl -> fs.flatMap { clean(it, cl) } }
                    is CallStage.Callees -> callee(f)
                }
                outs.forEach { work.addLast(st.to to it) }
            }
        }
        return seen.toList()
    }
}
```

---

## 24. `MicroEdgeBuilder` (common)

ADAPT of `StatementSummaryBuilder` (`DF/ap/ifds/summary/StatementSummaryBuilder.kt:12-143`). Implements
`interpreter.md` §2.1 (write rule I3), §2.2 rows, §2.5 A1–A4.

```kotlin
class MicroEdgeBuilder {
    private val touched = LinkedHashSet<AccessPathBase>()
    private val edges = LinkedHashSet<PathEdge>()
    private val conjunctions = LinkedHashSet<ConjunctiveEdge>()
    private val operand = LinkedHashMap<AccessPathBase, TypeFilter>()
    private val result = LinkedHashMap<AccessPathBase, TypeFilter>()

    fun touch(b: AccessPathBase) { touched += b }
    fun edge(e: PathEdge) { edges += e }
    fun conjunction(c: ConjunctiveEdge) { conjunctions += c }
    /** interpreter.md §5.1: two filters on one base are a conjunction (`TypeFilter.and`, DD9). */
    fun operandFilter(b: AccessPathBase, f: TypeFilter?) { if (f != null) operand.merge(b, f) { x, y -> x.and(y) } }
    fun resultFilter(b: AccessPathBase, f: TypeFilter?) { if (f != null) result.merge(b, f) { x, y -> x.and(y) } }

    /** `x = y`, `x = c`, `return v`, `throw t`; `from == null`: the kill (`x = new T`, ...). Today :67-72. */
    fun move(to: AccessPathBase, from: AccessPathBase?, toPath: List<AccessorIdx> = emptyList()) {
        touch(to)
        if (from == null) return
        touch(from)
        edge(keepEdge(from))                                                      // y.* -> y.*
        if (from != to || toPath.isNotEmpty()) edge(starEdge(from, emptyList(), to, toPath))   // y.* -> x.*
    }

    /** `x = y.p` (I3: a read adds no exclusion). Today :74-92 kept every prefix except `p` and refined (D1, D2, D3). */
    fun read(to: AccessPathBase, base: AccessPathBase, path: List<AccessorIdx>) {
        touch(to); touch(base)
        if (base != to) edge(keepEdge(base))                                       // y.* -> y.*        (D1)
        edge(starEdge(base, path, to, emptyList()))                                // y.p.* -> x.*      (D2 when base == to)
    }

    /** `b.p = v`: a strong write keeps every prefix except the written accessor (I3); a weak write keeps `b`.
     *  A2, A3: `v.* -> c.q.p.*` for each alias `(c, q)` of `b`; `c` is not touched. Today :94-121. */
    fun write(base: AccessPathBase, path: List<AccessorIdx>, weak: Boolean, values: List<AccessPathBase>,
              aliasPaths: List<Pair<AccessPathBase, List<AccessorIdx>>>) {
        touch(base)
        if (weak) edge(keepEdge(base)) else strongKeep(base, path).forEach { edge(it) }
        for (v in values) {
            touch(v)
            if (v != base) edge(keepEdge(v))
            edge(starEdge(v, emptyList(), base, path))
        }
        for ((c, q) in aliasPaths) {
            if (c == base) continue
            for (v in values) edge(starEdge(v, emptyList(), c, q + path))           // A6: not cut (I10)
        }
    }

    /** STATEMENT mode. */
    fun build(): StatementSummary = StatementSummary(LinkedHashSet(touched), edges.map { MicroEdge.of(it) },
        conjunctions.toList(), LinkedHashMap(operand), LinkedHashMap(result))

    /** STAGE mode (Part II §23.3): every base of an edge is touched. */
    fun buildStage(): StatementSummary {
        edges.forEach { touch(it.from.base); touch(it.to.base) }
        conjunctions.forEach { c -> c.literals.forEach { touch(it.fact.base) }; touch(c.target.base) }
        return build()
    }

    /** GEN mode: nothing is touched. */
    fun buildGen(): StatementSummary = StatementSummary(emptySet(), edges.map { MicroEdge.of(it) }, emptyList(), emptyMap())
}
```

A strong write with an empty path gives no keep edge (`strongKeep(b, [])` is empty). The JVM has no such write.

---

## 25. `JIRInterpreter`

```kotlin
package org.opentaint.dataflow.jvm.bidi.interp

class JIRInterpreter(
    val manager: ApManager,                        // Part I §5.1: the accessor and mark tables (DD6, DD7), the paths
    val rules: TaintRulesProvider,                 // the REDUCED rule set: the prescan called `selectRules(relevantRuleIds)`
    val checker: JIRFactTypeChecker,               // see below
    val callResolver: JIRCallResolver,
    val epResolver: JIRMethodEntrypointResolver,
    val entries: JIRMethodEntries,                 // Part II §31.2
    val defaultGetModel: JIRMethodGetDefault?,     // JIRAnalysisManager.Params.defaultGetModel
    val externalMethodTracker: ExternalMethodTracker?,
) : Interpreter, UnresolvedCallObserver {
    internal val errors = RuleErrors()
    internal val typeFilters = JIRTypeFilters(checker, manager)                                 // Part II §26.2
    internal val ruleForms = JIRRuleForms(rules, manager, errors)
    /** interpreter.md §4.7, §3.4: at the exceptional exit the rule position `Result` reads `exc`. */
    internal val ruleFormsAtThrow = JIRRuleForms(rules, manager, errors, resultBase = AccessPathBase.Exception)

    /** DD6: a JIR accessor as a path element. */
    fun idx(a: Accessor): AccessorIdx = manager.accessors.index(a)

    /** The cached forms of a method key (Part II §31.2): the forward forms below and their reversals. */
    fun forms(key: MethodKey): MethodForms = entries.forms(this, key)

    override fun entryNode(method: MethodKey): CommonInst = method.statement                   // analyzer-core.md §4.4
    override fun exitNodes(method: MethodKey): List<ExitNode> = entries[method].exitNodes(method)  // Part II §30
    override fun entryRules(method: MethodKey) = forms(method).entryRules(Direction.FORWARD)
    override fun exitRules(method: MethodKey, exit: CommonInst) = forms(method).exitRules(Direction.FORWARD, exit)
    override fun statementSummary(method: MethodKey, statement: CommonInst) =
        forms(method).statement(Direction.FORWARD, statement)
    override fun callPlan(caller: MethodKey, statement: CommonInst, call: CommonCallExpr) =
        forms(caller).call(Direction.FORWARD, statement, call)

    /** interpreter.md §2.1 step 1. REUSE JIRLocalVariableReachability.isReachable (JIRLocalVariableReachability.kt:27-31). */
    override fun isLive(method: MethodKey, base: AccessPathBase, statement: CommonInst): Boolean =
        entries[method].let { it.isEmpty || it.liveness.isReachable(base, statement) }

    /** Part II §30: every base except a local, the zero base too. */
    override fun isSummaryBase(base: AccessPathBase): Boolean = base !is AccessPathBase.LocalVar

    // override fun reached(...): Part II §28.5
}
```

`checker`: the checker of the prescan manager (`JIRAnalysisManager.factTypeChecker`, `JIRAnalysisManager.kt:68`) or a new
`JIRFactTypeChecker(cp)`. Both give the same filters (the checker has no state that changes the result). The reused one
keeps one set of statistics (`reportLanguageSpecificRunnerProgress`, `JIRAnalysisManager.kt:321-338`).
`JIRBidiAnalysis` uses the checker of the prescan (`analyzer-impl.md` §8.1). Part II does not depend on the choice.

---

## 26. Statement summaries of non-call statements

Implements `interpreter.md` §2.1, §2.2, §2.4, §2.5, §4.4, §5.1. ADAPT of `JIRStatementSummary`
(`JVM/analysis/JIRStatementSummary.kt:24-117`).

### 26.1 The builder

```kotlin
internal class JIRStatementForms(private val interp: JIRInterpreter, private val entry: JIRMethodEntry) {
    private fun filter(t: JIRType?) = interp.typeFilters.of(t)

    fun build(s: JIRInst): StatementSummary {
        check(s.callExpr == null) { "a call has a call plan (interpreter.md §2.1)" }
        val b = MicroEdgeBuilder()
        when (s) {
            is JIRAssignInst -> { b.assign(s, s.lhv, s.rhv); interp.ruleForms.readSources(b, s) }    // §4.4
            is JIRReturnInst -> b.move(AccessPathBase.Return, s.returnValue?.let(::accessPathBase))  // no filter
            is JIRThrowInst -> b.move(AccessPathBase.Exception, accessPathBase(s.throwable))
            else -> return StatementSummary.EMPTY      // branch, goto, monitor, catch, JMethod*Inst: {} (§2.2 last row)
        }
        return b.build()
    }

    /** Today :47-99. The lhs filter is a RESULT filter (§2.1 step 5). A static field ref adds no filter on `S`. */
    private fun MicroEdgeBuilder.assign(s: JIRInst, lhv: JIRValue, rhv: JIRExpr) {
        if (rhv is JIRBinaryExpr) { assign(s, lhv, rhv.lhv); assign(s, lhv, rhv.rhv); return }
        val from = when (rhv) {
            is JIRCastExpr -> mkAccess(rhv.operand)?.also { operandFilter(it.base, filter(rhv.type)) } ?: return
            is JIRImmediate -> mkAccess(rhv)?.also { operandFilter(it.base, filter(rhv.type)) } ?: return
            is JIRArrayAccess -> mkAccess(rhv)?.also { operandFilter(it.base, filter(rhv.array.type)) } ?: return
            is JIRFieldRef -> mkAccess(rhv)?.also { fieldFilters(it.base, rhv) } ?: return
            else -> null                                  // new, newarray, instanceof, neg, length, phi: kill
        }
        val to = when (lhv) {
            is JIRImmediate -> mkAccess(lhv)?.also { resultFilter(it.base, filter(lhv.type)) } ?: return
            is JIRArrayAccess -> mkAccess(lhv)?.also { operandFilter(it.base, filter(lhv.array.type)) } ?: return
            is JIRFieldRef -> mkAccess(lhv)?.also { fieldFilters(it.base, lhv) } ?: return
            else -> error("Assign to complex value: $lhv")
        }
        when {
            from is MemoryAccess -> read(to.base, from.base, path(from))
            to is MemoryAccess -> write(to.base, path(to), weak = (to as? RefAccess)?.accessor == ElementAccessor,
                values = listOfNotNull(from?.base), aliasPaths = aliasPaths(s, to.base))
            else -> move(to.base, from?.base)
        }
    }

    /** §5.1 "field read or write `y.f`": the static type of y AND the declaring class of f; none for a static field. */
    private fun MicroEdgeBuilder.fieldFilters(base: AccessPathBase, ref: JIRFieldRef) {
        val instance = ref.instance ?: return
        operandFilter(base, filter(instance.type)); operandFilter(base, filter(ref.field.enclosingType))
    }

    private fun path(a: MemoryAccess): List<AccessorIdx> = when (a) {                       // today :101-104; DD6
        is RefAccess -> listOf(interp.idx(a.accessor))
        is StaticRefAccess -> listOf(interp.idx(a.classStaticAccessor), interp.idx(a.accessor))
    }

    /** A1: the alias paths before the statement. REUSE JIRAliasUtil.forEachAliasPathAtStatement (:61-72); A4: only a
     *  local has aliases, so a static write has none. */
    private fun aliasPaths(s: JIRInst, base: AccessPathBase): List<Pair<AccessPathBase, List<AccessorIdx>>> {
        val result = ArrayList<Pair<AccessPathBase, List<AccessorIdx>>>()
        entry.aliasAnalysis?.forEachAliasPathAtStatement(s, base) { c, q -> result += c to q.map { interp.idx(it) } }
        return result
    }
}
```

The result for the rows of `interpreter.md` §2.2 (each is a test of §33):

| Statement | Builder calls | Edges |
|---|---|---|
| `x = y` | `move(x, y)` | `y.* → y.*`, `y.* → x.*` |
| `x = y.f` | `read(x, y, [f])` | `y.* → y.*`, `y.f.* → x.*` |
| `x = x.f` | `read(x, x, [f])` | `x.f.* → x.*` |
| `x = C.s` | `read(x, S, [<C>, s])` | `S.* → S.*`, `S.<C>.s.* → x.*` |
| `y.f = x` | `write(y, [f], weak = false, [x], aliases)` | `y.* →_{f} y.*`, `x.* → x.*`, `x.* → y.f.*` |
| `y[i] = x` | `write(y, [e], weak = true, [x], aliases)` | `y.* → y.*`, `x.* → x.*`, `x.* → y.[e].*` |
| `C.s = x` | `write(S, [<C>, s], weak = false, [x], [])` | `S.* →_{<C>} S.*`, `S.<C>.* →_{s} S.<C>.*`, `x.* → x.*`, `x.* → S.<C>.s.*` |
| `x = a op b` | `move(x, a)`, `move(x, b)` | `a.* → a.*`, `a.* → x.*`, `b.* → b.*`, `b.* → x.*` |

The static exception of run 1 (`interpreter.md` §2.1 step 4) is an AP rule:
`ApOps.applyEdge(..., statementEdge = true, ...)`. The interpreter gives no extra form for it.

### 26.2 Type filters (`interpreter.md` §5.1)

Part I's `TypeFilter(may, markPolicy)` (DD9). `may` is today's `AccessorFilter` of `JIRFactTypeChecker`
(`JVM/JIRFactTypeChecker.kt:75-155`): its Field, Element, Value, `<C>` and type-info cases (:84-136) are the `may(t, p)`
of `interpreter.md` §5.1 (Field: the declaring class, deeper fields not checked; Element: the array type, then
`FilterNext(element type)`; `Object`: accept). Its `TaintMarkAccessor`, `AnyAccessor` and `FinalAccessor` cases never run:
a path has no such accessor (W5), and a tail is not an accessor. GENERALIZE: one public member gives the private filter.

```kotlin
// JVM/JIRFactTypeChecker.kt — new member; `filterFactByLocalType` (:177-183) stays for the prescan.
fun localFilter(type: JIRType): FactTypeChecker.FactApFilter = AccessorFilter(type, isLocalCheck = true)
```

```kotlin
/** interpreter.md §5.1: `may` from the static type, then the mark policy (G6) on a primitive or boxed type. One filter per
 *  type (the forms of every method share it). */
class JIRTypeFilters(private val checker: JIRFactTypeChecker, private val manager: ApManager) {
    private val byType = ConcurrentHashMap<JIRType, TypeFilter>()

    fun of(t: JIRType?): TypeFilter? = t?.let { byType.computeIfAbsent(it, ::make) }

    private fun make(t: JIRType) = TypeFilter(
        may = checker.localFilter(t),
        markPolicy = if (t.unboxIfNeeded() is JIRPrimitiveType) MarkPolicy { isPrimitiveTracking(it) } else null)

    /** interpreter.md §5.1 `isPrimitiveTracking` (DD7). Today the TaintMarkAccessor case (:97-105). */
    fun isPrimitiveTracking(m: TaintMark): Boolean =
        manager.marks.name(m).endsWith(PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE)
}
```

`ApOps.filter` applies `may` to the path and then the policy to the concrete marks at the root path (Part I §5.5). The
filter never reads the tail: a `*` and an `[any]` fact keep their tail (`interpreter.md` D11, D12). Two filters on one
base are `TypeFilter.and` (`MicroEdgeBuilder.operandFilter`, §24).

---

## 27. Rules to forms

Implements `interpreter.md` §1.3, §1.4, §4.1, §4.2, §5.2, §5.3. The rule queries pass `fact = null`: every rule of the
method in the REDUCED set (`TaintRulesProvider`, the prescan selected it). The conditions use the rewriter of today:
`JIRMarkAwareConditionRewriter(positionResolver, checker, aliasAnalysis, statement)`
(`JVM/JIRMarkAwareConditionRewriter.kt:18-25`). It evaluates the non-mark atoms per statement (`JIRBasicAtomEvaluator`)
and gives the mark literals.

### 27.1 Positions, marks, literals, cubes

```kotlin
import org.opentaint.dataflow.configuration.jvm.TaintMark as RuleMark      // the rule mark; `TaintMark` is Part I's

internal class JIRRuleForms(
    val rules: TaintRulesProvider,
    private val manager: ApManager,
    val errors: RuleErrors,
    private val resultBase: AccessPathBase = AccessPathBase.Return,   // `exc` at the exceptional exit (interpreter.md §4.7)
) {

    /** interpreter.md §1.3: a rule position in callee coordinates. `any`: the position ends with AnyField. DD6: the path
     *  elements are AccessorIdx. */
    data class RulePos(val base: AccessPathBase, val path: List<AccessorIdx>, val any: Boolean) {
        val isClass: Boolean get() = base == AccessPathBase.ClassStatic && path.size == 1      // `S.<C>` (§1.4)
        fun fact(t: TaintMark) = PathFact(base, path, if (any) Tail.ANY else Tail.EXACT, MarkSlot.Concrete(t))
        fun star(forceAny: Boolean = false) = PathFact(base, path, if (any || forceAny) Tail.ANY else Tail.STAR, MarkSlot.STAR)
    }

    fun pos(p: Position): RulePos = pos(p.resolveAp())                  // REUSE TaintEvaluator.kt:81-101
    fun pos(p: PositionAccess): RulePos {
        val acc = p.accessors()
        val any = acc.lastOrNull() == AnyAccessor
        val path = if (any) acc.dropLast(1) else acc
        check(AnyAccessor !in path) { "inner AnyField (ap.md W4): $p" }
        val base = p.base().let { if (it == AccessPathBase.Return) resultBase else it }   // `Result` (§1.3; §4.7 at a throw)
        return RulePos(base, path.map { manager.accessors.index(it) }, any)           // DD6
    }

    /** The path of a Cleaner (Part I §6). */
    fun node(path: List<AccessorIdx>): PathNode? = manager.path(path)

    /** DD7: a rule mark (by its name) and a literal mark (`TaintMarkAccessor.mark` is the name). */
    fun mark(m: RuleMark): TaintMark = manager.marks.mark(m.name)
    fun mark(name: String): TaintMark = manager.marks.mark(name)

    /** §4.2: `ContainsMark(P, T)` -> `(P, $, T)`; `ContainsMarkOnAnyField(P, T)` or `ContainsMark(P.AnyField, T)` -> `(P, [any], T)`. */
    fun literal(l: TaintMarkAwareConditionExpr.Literal): PathFact = when (l) {
        is ContainsMarkLiteral -> pos(l.position).fact(mark(l.mark.mark))
        is ContainsMarkOnAnyAccessorLiteral -> pos(l.position).copy(any = true).fact(mark(l.mark.mark))
    }

    /** §4.2 for a source, a sink and a pass rule: a negated literal counts as true; `Or` gives one cube per alternative.
     *  REUSE removeTrueLiterals (TaintMarkAwareConditionExpr.kt:48-50) and explodeToDNF (:110-123). */
    fun cubes(cond: ExprOrConstant): List<List<PathFact>> = when {
        cond.isFalse -> emptyList()
        cond.isTrue -> listOf(emptyList())
        else -> {
            val positive = cond.expr.removeTrueLiterals { it.negated } ?: return listOf(emptyList())
            positive.explodeToDNF().map { cube -> cube.literals.map(::literal).distinct() }.distinct()
        }
    }
```

### 27.2 Sources (call, entry, exit, read)

```kotlin
    /** §4.1: `zero.$ (zeroMark) -> P.t (T)`; `Q.t' (T') -> P.t (T)`; a conjunction for two or more literals (§5.3).
     *  §1.4 rule errors on a class target. Returns false on a rule error. */
    fun source(b: MicroEdgeBuilder, rule: TaintConfigurationItem, cube: List<PathFact>, a: AssignMark): Boolean {
        val to = pos(a.position)
        if (to.isClass && to.any) return errors.reject(rule, "[any] target on a class position (§1.4)")
        if (to.isClass && cube.any { it.tail == Tail.ANY })
            return errors.reject(rule, "ContainsMarkOnAnyField with a class target (§1.4, I12 (b))")
        val target = to.fact(mark(a.mark))
        when (cube.size) {
            0 -> b.edge(PathEdge(ZERO_FACT, target, ExclusionSet.Empty))
            1 -> b.edge(PathEdge(cube[0], target, ExclusionSet.Empty))
            else -> b.conjunction(ConjunctiveEdge(cube.map { Pattern(it, ExclusionSet.Empty) }, target))   // W7
        }
        return true
    }

    /** §4.4: the read source at `x = C.s` (`TaintStaticFieldSource`); the condition must be true. Today
     *  JIRMethodSequentFlowFunction.kt:235-268 (a non-true condition was a TODO; here it is a rule error). */
    fun readSources(b: MicroEdgeBuilder, s: JIRAssignInst) {
        val field = (s.rhv as? JIRFieldRef)?.field?.field?.takeIf { it.isStatic } ?: return
        val x = accessPathBase(s.lhv) ?: return
        val found = rules.sourceRulesForStaticField(field, s, fact = null)
        if (found.none()) return
        b.touch(AccessPathBase.Zero); b.edge(ZERO_KEEP)                            // I11 (d)
        for (rule in found) {
            if (!rule.condition.isTrue()) { errors.reject(rule, "read source with a condition (§4.1)"); continue }
            for (a in rule.actionsAfter) {
                val p = pos(a.position)
                if (p.base != AccessPathBase.Return) { errors.reject(rule, "read source target is not the read value (§4.4)"); continue }
                b.edge(PathEdge(ZERO_FACT, p.copy(base = x).fact(mark(a.mark)), ExclusionSet.Empty))
            }
        }
    }
```

### 27.3 Sinks and end facts

```kotlin
    /** §4.1, §4.2, ap.md §4.9: one SinkRule per alternative. I11 (f): every pattern has the tail `$` or `[any]`.
     *  `mayBeArray(i)`: only for a sink at a call (Part II §28.1): ARRAY ELEMENTS OF A CALL SINK (§4.2). A literal on
     *  `arg(i)·ρ` whose argument may be an array is the `Or` of `(arg(i), ρ, t, T)` and `(arg(i), [e]·ρ, t, T)`, so a cube
     *  gives one alternative per choice (a conjunctive sink too). The entry and exit sinks pass no `mayBeArray`. All the
     *  alternatives have the same `rule`, so they have one vulnerability key; each one seeds its own patterns (§4.9). */
    fun sinks(rule: TaintConfigurationSink, cond: ExprOrConstant, mayBeArray: (Int) -> Boolean = { false }): List<SinkRule> {
        val ends = endFacts(rule)
        return cubes(cond).flatMap { cube ->
            if (cube.isEmpty()) return@flatMap listOf(SinkRule(rule, listOf(ZERO_PATTERN), ends))
            cube.map { elementChoices(it, mayBeArray) }                      // REUSE DF/util/ListUtils.kt:127
                .cartesianProductMapTo { choice -> SinkRule(rule, choice.map { Pattern(it, ExclusionSet.Empty) }.distinct(), ends) }
        }
    }

    /** Today `arrayElementConditionReaders` (`JVM/taint/JIRMethodCallTaintUtil.kt:191-203`): a reader with the prefix `[e]`
     *  on an `arg(i)` fact. Not for `this`, `Result` or `S`. */
    private fun elementChoices(lit: PathFact, mayBeArray: (Int) -> Boolean): List<PathFact> {
        val b = lit.base as? AccessPathBase.Argument ?: return listOf(lit)
        if (!mayBeArray(b.idx)) return listOf(lit)
        return listOf(lit, lit.copy(path = listOf(elementIdx) + lit.path))
    }
    private val elementIdx: AccessorIdx = manager.accessors.index(ElementAccessor)

    /** §4.1 END FACTS: `trackFactsReachAnalysisEnd` as the targets of a source from the zero fact. */
    fun endFacts(rule: TaintConfigurationSink): List<MicroEdge> = rule.trackFactsReachAnalysisEnd.mapNotNull { a ->
        val to = pos(a.position)
        if (to.isClass && to.any) { errors.reject(rule, "[any] end fact on a class position (§1.4)"); null }
        else MicroEdge.of(PathEdge(ZERO_FACT, to.fact(mark(a.mark)), ExclusionSet.Empty))
    }
```

### 27.4 Pass rules (unresolved callee)

```kotlin
    /** §4.1 pass-rule rows and the AnyField table; §1.4 rule errors; §5.3 for CopyMark with other literals. */
    fun pass(b: MicroEdgeBuilder, rule: TaintConfigurationItem, cube: List<PathFact>, action: Action) {
        val (fromPos, toPos) = when (action) {
            is CopyAllMarks -> action.from to action.to
            is CopyMark -> action.from to action.to
            else -> return
        }
        val from = pos(fromPos); val to = pos(toPos)
        if (from.isClass || to.isClass) { errors.reject(rule, "pass rule from or to a class position (§1.4)"); return }
        b.edge(keepEdge(from.base))                                                        // b.* -> b.*
        when (action) {
            // P.* -> Q.* ; P.* -> Q.[any] ; P.[any] -> Q.[any]. The cube is empty: a CopyAllMarks rule with a mark literal
            // is a rule error and applies without its mark literals (§4.2, D24; the caller, Part II §28.5).
            is CopyAllMarks -> { check(cube.isEmpty()); b.edge(PathEdge(from.star(), to.star(forceAny = from.any), ExclusionSet.Empty)) }
            // P.t (T) -> Q.t (T); the literal (P, t, T) is the premise itself; other literals make a conjunction.
            is CopyMark -> {
                val t = mark(action.mark)
                val e = PathEdge(from.fact(t), to.fact(t), ExclusionSet.Empty)
                val rest = cube.filter { it != e.from }
                if (rest.isEmpty()) b.edge(e)
                else b.conjunction(ConjunctiveEdge((listOf(e.from) + rest).map { Pattern(it, ExclusionSet.Empty) }, e.to))
            }
            else -> Unit
        }
    }
```

### 27.5 Cleaners (`interpreter.md` §4.2 cleaner rule, D20, §5.2, §1.4)

```kotlin
    /** The steps of one cleaner rule, actions in order (§4.8). §4.2 (D20): only an UNCONDITIONAL cleaner acts. The
     *  rewriter decides the non-mark atoms statically: false removes the rule, true drops out. If a mark literal is left
     *  (positive or negated, on any position, `ContainsMark` or `ContainsMarkOnAnyField`), the cleaner does not act and
     *  raises no request. So every acting cleaner is unconditional, and its `<string-bytes>` row (§5.2) applies. */
    fun cleanSteps(rule: TaintCleaner, cond: ExprOrConstant, types: PositionTypeResolver): List<CleanStep> =
        if (cond.isTrue) rule.actionsAfter.flatMap { unconditional(rule, it, types) } else emptyList()

    /** §5.2 mapping; `RemoveAllMarks` on S is the kill of §1.4. */
    fun unconditional(rule: TaintConfigurationItem, a: Action, types: PositionTypeResolver): List<CleanStep> = when (a) {
        is RemoveMark -> {
            val p = pos(a.position); val t = mark(a.mark)
            val reach = when {                                             // CleanReach: Part I §6
                p.any -> CleanReach.BELOW                                   // P.AnyField, Exact or ExactAndAnyField
                a.reach == TaintCleanReach.Exact -> CleanReach.EXACT
                else -> CleanReach.AT_AND_BELOW                             // ExactAndAnyField (D9)
            }
            val bytes = stringBytes(a.position, types)                    // ADAPT TaintEvaluator.kt:52-60
            listOfNotNull(Cleaner(p.base, node(p.path), reach, t), bytes?.let { Cleaner(p.base, node(p.path + it), reach, t) })
                .map { CleanStep.Clean(it) }
        }
        is RemoveAllMarks -> {
            val p = pos(a.position)
            when {
                p.base == AccessPathBase.ClassStatic && p.any -> { errors.reject(rule, "RemoveAllMarks(P.AnyField) on S (§1.4)"); emptyList() }
                p.base == AccessPathBase.ClassStatic -> listOf(CleanStep.Kill(MicroEdgeBuilder().apply {
                    touch(AccessPathBase.ClassStatic); strongKeep(AccessPathBase.ClassStatic, p.path).forEach { edge(it) }
                }.build()))
                else -> listOf(CleanStep.Clean(Cleaner(p.base, node(p.path),
                    if (p.any) CleanReach.BELOW else CleanReach.AT_AND_BELOW, mark = null)))   // D10
            }
        }
        else -> emptyList()
    }

    private fun stringBytes(p: Position, types: PositionTypeResolver): AccessorIdx? =
        if (types.resolve(p.resolveAp())?.typeName != "java.lang.String") null
        else manager.accessors.index(FieldAccessor("java.lang.String", "<string-bytes>", "byte[]"))
}

/** §1.4: the interpreter rejects a rule element and logs it once per (rule, reason). */
class RuleErrors {
    private val seen = ConcurrentHashMap.newKeySet<Pair<Any, String>>()
    fun reject(rule: Any, reason: String): Boolean {
        if (seen.add(rule to reason)) logger.warn { "Rule element rejected ($reason): $rule" }
        return false
    }
    private companion object { val logger = KotlinLogging.logger {} }
}
```

---

## 28. The call plan

Implements `interpreter.md` §3, §4.5, §4.6, §5.1–§5.3 and the stage table of `analyzer-core.md` §4.5. One plan per
(method key, call statement): the callees depend on the caller context (`JIRCallResolver` reads it,
`JVM/JIRCallResolver.kt:193-246`).

### 28.1 The builder

```kotlin
internal class JIRCallPlanBuilder(
    private val interp: JIRInterpreter,
    private val entry: JIRMethodEntry,
    private val caller: MethodKey,
    private val s: JIRInst,
    private val call: JIRCallExpr,
) {
    private val forms = interp.ruleForms
    private val callee: JIRMethod = call.method.method                    // the method that the call names (G4)
    private val returnValue: JIRImmediate? = (s as? JIRAssignInst)?.lhv as? JIRImmediate
    private val r: AccessPathBase? = returnValue?.let(::accessPathBase)
    private val o: AccessPathBase? = (call as? JIRInstanceCallExpr)?.instance?.let(::accessPathBase)
    private val args: List<AccessPathBase?> = call.args.map(::accessPathBase)
    private val rewriter = JIRMarkAwareConditionRewriter(
        CallPositionToJIRValueResolver(call, returnValue), interp.checker, entry.aliasAnalysis, s)
    private val types = JIRMethodPositionBaseTypeResolver(callee)
    private fun filter(t: JIRType?) = interp.typeFilters.of(t)

    fun build(): CallPlan {
        // §4.2 ARRAY ELEMENTS OF A CALL SINK: REUSE JIRFactTypeChecker.callArgumentMayBeArray (JIRFactTypeChecker.kt:195-199),
        // the static type of the argument value at this call.
        val mayBeArray = { i: Int -> interp.checker.callArgumentMayBeArray(call, AccessPathBase.Argument(i)) }
        val sinks = interp.rules.sinkRulesForMethod(callee, s, fact = null)
            .flatMap { forms.sinks(it, rewriter.rewrite(it.condition), mayBeArray) }
        val (callees, unresolved) = resolve()
        val back = bindBack()
        val stages = buildList {
            add(Edges(BEFORE, BOUND, BIND_IN, bindIn()))                                              // step 2
            for (sk in sinks) if (sk.endFacts.isNotEmpty())                                             // step 3
                add(Edges(BOUND, REWRITTEN, END_FACTS, MicroEdgeBuilder().apply { sk.endFacts.forEach { edge(it.edge) } }.buildStage(),
                    Guard.SinkTriggered(sk)))
            add(Edges(BOUND, REWRITTEN, SOURCES, sources()))                                          // step 4
            add(Clean(BOUND, ADDED, cleanSteps()))                                                    // step 5.1
            if (callees.isNotEmpty()) add(Callees(ADDED, RETURNED, callees))                          // step 5.2
            if (unresolved) {                                                                         // step 5.3 (Part II §28.5)
                add(Edges(ADDED, RETURNED, UNRESOLVED, identities(boundPositions())))                 // §3.7 item 1: no filter
                add(Edges(ADDED, RETURNED, UNRESOLVED, passRules()))                                 // §3.7 items 2, 3: declared types
            }
            if (callee.isConstructor) add(Edges(ADDED, REWRITTEN, CONSTRUCTOR, identities(boundPositions())))   // §3.5: every added fact, S too (SI5); Origin.IDENTITY: no alias (SI15)
            add(Rewrite(RETURNED, REWRITTEN, rewriterCleaners()))                                    // step 6
            add(Edges(REWRITTEN, AFTER, BIND_BACK, back))
            aliases(back)?.let { add(Edges(REWRITTEN, AFTER, ALIASES, it, Guard.MemoryEffect)) }
        }
        return CallPlan(touched(), stages, sinks, entry = BEFORE, exit = AFTER)
    }

    /** §3.1, §3.3, §4.5 step 1; today JIRMethodCallFactMapper.factIsRelevantToMethodCall (:247-278). Not the zero base. */
    private fun touched(): Set<AccessPathBase> =
        buildSet { add(AccessPathBase.ClassStatic); o?.let(::add); args.filterNotNullTo(this); r?.let(::add) }

    /** The callee positions that a binding fills (an added fact can be on them). */
    private fun boundPositions(): List<AccessPathBase> = buildList {
        add(AccessPathBase.ClassStatic)
        if (o != null) add(AccessPathBase.This)
        args.forEachIndexed { i, a -> if (a != null) add(AccessPathBase.Argument(i)) }
    }

    private fun identities(bases: List<AccessPathBase>) =
        MicroEdgeBuilder().apply { bases.forEach { edge(keepEdge(it)) } }.buildStage()
```

### 28.2 Bindings (`interpreter.md` §3.1–§3.3)

ADAPT of `JIRMethodCallFactMapper.mapMethodCallToStartFlowFact` (:210-242) and `mapMethodExitToReturnSingleFlowFact`
(:141-205). Each binding is a `*`-to-`*` micro edge with the mark `*` (I4, I11 (a)).

```kotlin
    /** BEFORE -> BOUND. Caller-side OPERAND filters: o by the declaring class of the method that the call names;
     *  ai by its static type; none on S and zero. */
    private fun bindIn(): StatementSummary = MicroEdgeBuilder().apply {
        edge(keepEdge(AccessPathBase.ClassStatic))                                     // S.* -> S.*
        edge(starEdge(AccessPathBase.Zero, emptyList(), AccessPathBase.Zero, emptyList()))   // zero.* -> zero.* (§3.3)
        o?.let { edge(starEdge(it, emptyList(), AccessPathBase.This, emptyList())); operandFilter(it, filter(callee.enclosingClass.toType())) }
        args.forEachIndexed { i, a ->
            if (a == null) return@forEachIndexed
            edge(starEdge(a, emptyList(), AccessPathBase.Argument(i), emptyList())); operandFilter(a, filter(call.args[i].type))
        }
    }.buildStage()

    /** REWRITTEN -> AFTER. RESULT filters at the caller. No `exc`, no local, no zero (I11 (c)). The constant back
     *  edge `const.* -> const.*` has no edge here: no form makes a fact on a constant base (spec issue SI6). */
    private fun bindBack(): StatementSummary = MicroEdgeBuilder().apply {
        edge(keepEdge(AccessPathBase.ClassStatic))
        if (o != null && o !is AccessPathBase.Constant) {
            edge(starEdge(AccessPathBase.This, emptyList(), o, emptyList()))
            resultFilter(o, filter((call as JIRInstanceCallExpr).instance.type))
        }
        args.forEachIndexed { i, a ->
            if (a == null || a is AccessPathBase.Constant) return@forEachIndexed
            edge(starEdge(AccessPathBase.Argument(i), emptyList(), a, emptyList())); resultFilter(a, filter(call.args[i].type))
        }
        if (r != null) { edge(starEdge(AccessPathBase.Return, emptyList(), r, emptyList())); resultFilter(r, filter(returnValue!!.type)) }
    }.buildStage()
```

### 28.3 Sources, cleaners, rewriter

```kotlin
    /** §4.1 THE RULE STATEMENT OF A CALL: the zero keep edge and the sources (no other keep edge). */
    private fun sources(): StatementSummary = MicroEdgeBuilder().apply {
        edge(ZERO_KEEP)
        for (rule in interp.rules.sourceRulesForMethod(callee, s, fact = null)) {
            val cubes = forms.cubes(rewriter.rewrite(rule.condition))
            for (a in rule.actionsAfter) for (cube in cubes) forms.source(this, rule, cube, a)
        }
    }.buildStage()

    /** §4.5 step 5.1, §4.8: the cleaner rules of the named method, in rule order. */
    private fun cleanSteps(): List<CleanStep> = interp.rules.cleanerRulesForMethod(callee, s, fact = null)
        .flatMap { forms.cleanSteps(it, rewriter.rewrite(it.condition), types) }

    /** §5.2 THE SUMMARY REWRITER. ADAPT of JIRMethodCallRuleBasedSummaryRewriter.userRuleDefinedActions (:54-88):
     *  the same rule queries (`allRelevant = true`), `clean(P, exact, T)` per relevant mark and action position. */
    private fun rewriterCleaners(): List<Cleaner> {
        val out = LinkedHashSet<Cleaner>()
        fun add(rule: TaintConfigurationItem, positions: List<Position>) {
            val info = rule.info as? UserDefinedRuleInfo ?: return
            for (p in positions) for (m in info.relevantTaintMarks) {
                val steps = forms.unconditional(rule, RemoveMark(RuleMark(m), p, TaintCleanReach.Exact), types)   // RuleMark: Part II §27.1
                steps.filterIsInstance<CleanStep.Clean>().mapTo(out) { it.cleaner }
            }
        }
        for (rule in interp.rules.sourceRulesForMethod(callee, s, fact = null, allRelevant = true))
            if (!rewriter.rewrite(rule.condition).isFalse) add(rule, rule.actionsAfter.map { it.position })
        for (rule in interp.rules.cleanerRulesForMethod(callee, s, fact = null, allRelevant = true))
            if (!rewriter.rewrite(rule.condition).isFalse) add(rule, rule.actionsAfter.filterIsInstance<RemoveMark>().map { it.position })
        return out.toList()
    }
```

### 28.4 Callees (`interpreter.md` §3.6, §3.9)

GENERALIZE `JIRCallResolver`: it reads two members of the caller context only (`JIRCallResolver.kt:198, 209, 216`). Four
declarations change their parameter type; the old core keeps its behaviour, because each one reads only these two members.

```kotlin
// JVM/JIRCallResolver.kt
interface JIRCallResolutionContext {
    val methodEntryPoint: MethodEntryPoint
    val aliasAnalysis: JIRLocalAliasAnalysis?
}
fun resolve(call: JIRCallExpr, location: JIRInst, context: JIRCallResolutionContext): List<MethodResolutionResult>   // :90
private fun resolveVirtualMethod(baseMethod: JIRMethod, call: JIRVirtualCallExpr, location: JIRInst,
                                 context: JIRCallResolutionContext): List<MethodResolutionResult>                // :116-121
private fun resolveValueTypeConstraints(value: JIRValue, location: JIRInst,
                                        context: JIRCallResolutionContext): Set<TypeConstraintInfo>?           // :193-197
private inner class MethodContextCreator(val context: JIRCallResolutionContext, /* other parameters unchanged */)  // :288-292

// JVM/analysis/JIRMethodAnalysisContext.kt
class JIRMethodAnalysisContext(
    /* ... */
    override val methodEntryPoint: MethodEntryPoint,           // overrides MethodAnalysisContext and JIRCallResolutionContext
    /* ... */
    override val aliasAnalysis: JIRLocalAliasAnalysis?,        // was `val` (:25)
    /* ... */
) : MethodAnalysisContext, JIRCallResolutionContext
```

```kotlin
    /** ADAPT of JIRMethodCallResolver.resolvedJirMethodCalls (:159-211): no subscription, no lambda event. §3.9 (D19): a
     *  `Lambda` result is the lambda methods that the prescan knows for this call, and nothing else (no unresolved path);
     *  if the prescan knows none, it is a resolution failure: the unresolved path (§3.7). */
    private fun resolve(): Pair<List<MethodKey>, Boolean> {
        val ctx = object : JIRCallResolutionContext {
            override val methodEntryPoint = caller
            override val aliasAnalysis = entry.aliasAnalysis
        }
        val callees = LinkedHashSet<MethodKey>()
        var unresolved = false
        for (res in interp.callResolver.resolve(call, s, ctx)) when (res) {
            JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> unresolved = true
            is JIRCallResolver.MethodResolutionResult.ConcreteMethod -> callees += keys(res.method)
            is JIRCallResolver.MethodResolutionResult.Lambda -> {
                val impls = entry.lambdas[s.location.index]
                if (impls.isNullOrEmpty()) unresolved = true
                else impls.forEach { callees += keys(MethodWithContext(it, EmptyMethodContext)) }
            }
        }
        return callees.toList() to unresolved
    }

    /** As MethodAnalyzer.methodEntryPoints (DF/ap/ifds/MethodAnalyzer.kt:815-821). */
    private fun keys(m: MethodWithContext): List<MethodKey> =
        interp.epResolver.resolveEntryPoints(m.method, m.ctx).map { MethodEntryPoint(m.ctx, it) }
```

### 28.5 Unresolved callee (`interpreter.md` §3.7)

ADAPT of `JIRMethodCallFlowFunction.propagateUnresolvedCallFact` (:253-339). Two `UNRESOLVED` stages start at `ADDED`:

* the default identity with no filter (today `unresolvedCallDefaultFactPropagation`, :330-339, has no type check);
* the pass rules with the declared-type filters (`interpreter.md` §5.1 row "pass rule"; today
  `DF/taint/Propagator.kt:55-87`, `:89-105`).

With one stage, the operand filter of a base would also filter its identity edge (STAGE mode filters the input before
every edge). The two stages start at one point, so the core gives each added fact to both and takes the union
(`analyzer-core.md` §4.5). Each stage reverses on its own.

```kotlin
    /** §3.7 items 2 and 3: the pass rules of the named method and the default getter rules (JIRMethodGetDefault.kt:37-51). */
    private fun passRules(): StatementSummary = MicroEdgeBuilder().apply {
        val rules = interp.rules.passTroughRulesForMethod(callee, s, fact = null).map { it to rewriter.rewrite(it.condition) } +
            interp.defaultGetModel?.defaultPropagationRules(callee).orEmpty().map { it.rule to it.condition }
        val read = HashSet<AccessPathBase>()
        val written = HashSet<AccessPathBase>()
        for ((rule, cond) in rules) {
            // A mark literal is left after the static atoms when the rewritten condition is an expression.
            val markLiterals = !cond.isTrue && !cond.isFalse
            for (a in rule.actionsAfter) {
                val cubes = if (a is CopyAllMarks && markLiterals) {                    // §4.2, D24: a rule error
                    forms.errors.reject(rule, "CopyAllMarks with a mark literal (interpreter.md §4.2, D24): applied without it")
                    listOf(emptyList())
                } else forms.cubes(cond)
                for (cube in cubes) forms.pass(this, rule, cube, a)
                when (a) {
                    is CopyAllMarks -> { read += forms.pos(a.from).base; written += forms.pos(a.to).base }
                    is CopyMark -> { read += forms.pos(a.from).base; written += forms.pos(a.to).base }
                    else -> Unit
                }
            }
        }
        fun declared(b: AccessPathBase) = filter(types.resolve(PositionAccess.Simple(b)) as? JIRType)
        read.forEach { operandFilter(it, declared(it)) }                          // the from positions
        written.forEach { resultFilter(it, declared(it)) }                        // the to positions
    }.buildStage()
```

The external method tracker records the arrival of TAINT at an unresolved callee, as today (per caller fact and callee
position, :285-295), not the call itself. So the builder does not call it. The core calls a hook, `UnresolvedCallObserver`
(§22.2: an addition to `analyzer-core.md` §4.9):

```kotlin
// bidi.interp
/** The core calls it in run 1 for each new added-fact delta on `position` at the UNRESOLVED stages of `plan`. Run 1 is the
 *  one full forward pass, as the full scan of today. No effect on facts. */
fun interface UnresolvedCallObserver {
    fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan)
}

// JIRInterpreter : Interpreter, UnresolvedCallObserver
override fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan) {
    val t = externalMethodTracker ?: return
    val callee = (call as JIRCallExpr).method.method
    if (position == AccessPathBase.ClassStatic || JIRCallResolver.alwaysIgnoreMethod(callee)) return    // as :285-287
    // today `startFactBase in passEvaluator.relevantPositionBase`: a pass rule reads this position
    val ruleApplied = plan.stages.any { st ->
        st is CallStage.Edges && st.kind == StageKind.UNRESOLVED &&
            (st.summary.edgesOf(position).any { !it.isIdentity } ||
                st.summary.conjunctions.any { c -> c.literals.any { it.fact.base == position } })
    }
    t.trackExternalMethod("${callee.enclosingClass.name}#${callee.name}", callee.description, position.toString(), ruleApplied)
}
```

Today `relevantPositionBase` holds the from-base of a rule only when the condition of the rule holds on the fact
(`TaintConfigUtils.kt:48-60`); the hook reads the rules of the plan. A conditional pass rule is rare, and `ruleApplied`
only splits the report into two lists.

### 28.6 Aliases on call results (`interpreter.md` §3.8)

GENERALIZE `JIRAliasUtil.kt`: add the helper of `BWD/../analysis/JIRAliasUtil.kt:31-35`, and let
`forEachAliasAfterCallStatement` (:25-35) call it (no behaviour change).

```kotlin
// JVM/analysis/JIRAliasUtil.kt
fun JIRLocalAliasAnalysis.aliasesPersistedThroughCall(base: AccessPathBase.LocalVar, statement: JIRInst): List<AliasApInfo> {
    val before = findAlias(base, statement) ?: return emptyList()
    val after = findAliasAfterStatement(base, statement)?.toSet() ?: return emptyList()
    return before.filter { it in after }.mapNotNull { it.relevantApInfo() }            // constant bases skipped
}
```

```kotlin
    /** AC1, AC2: for each binding back `P.* -> x.*` with a local `x`, the edge `P.* -> b.q.*` per alias (b, q) of x that
     *  holds before and after the call. The stage has the guard `MemoryEffect` (AC3, AC4). */
    private fun aliases(back: StatementSummary): StatementSummary? {
        val aa = entry.aliasAnalysis ?: return null
        val b = MicroEdgeBuilder()
        for (e in back.edges) {
            val x = e.edge.to.base as? AccessPathBase.LocalVar ?: continue
            for (alias in aa.aliasesPersistedThroughCall(x, s)) {
                if (alias.base == x && alias.accessors.isEmpty()) continue
                b.edge(starEdge(e.edge.from.base, emptyList(), alias.base, alias.accessors.map { interp.idx(it.apAccessor()) }))
            }
        }
        return b.buildStage().takeIf { it.edges.isNotEmpty() }
    }
}
```

The core applies the edges of a `SOURCES` or `UNRESOLVED` stage, and the keep edges of a `CleanStep.Kill`, with
`ApOps.applyEdge(c, premise, e, statementEdge = true, mode, out)` on the caller edge `(i -> c)`: the static exception and
its position request go to the caller, on `i` (`interpreter.md` §2.1 step 4, `ap.md` §4.10 item 1). Every other stage
uses `statementEdge = false`.

### 28.7 The zero fact at a call (`interpreter.md` §3.3, §4.6)

No extra form. The plan has: the zero binding in `BIND_IN`; `ZERO_KEEP` in `SOURCES`; no cleaner on the zero base; no
zero edge in `UNRESOLVED`, `CONSTRUCTOR`, `BIND_BACK`, `ALIASES`. So the zero fact fires the unconditional sinks and the
sources at `BOUND`, enters every callee at `ADDED`, and never comes back by a binding (I11 (c)). It also passes over
the call (it is not in `touched`).

---

## 29. Entry rules and exit rules

Implements `interpreter.md` §4.3, §4.7, §4.4 item 3; `analyzer-core.md` §4.4.

```kotlin
internal object JIRBoundaryForms {
    /** §4.3: zero keep, entry-point sources with a true condition, entry sinks (unconditional only), and the context
     *  filter of an initial fact. ADAPT of JIRMethodStartFlowFunction (:29-127). STATEMENT mode: a base with a
     *  context filter is touched with its identity edge, so the filter applies and the fact passes. */
    fun entryRules(interp: JIRInterpreter, entry: JIRMethodEntry, key: MethodKey): RuleStatement {
        val method = key.method as JIRMethod
        val s = key.statement as JIRInst
        val rw = JIRMarkAwareConditionRewriter(CalleePositionToJIRValueResolver(method), interp.checker, entry.aliasAnalysis, s)
        val b = MicroEdgeBuilder().apply { touch(AccessPathBase.Zero); edge(ZERO_KEEP) }
        val bases = listOf<AccessPathBase>(AccessPathBase.This) + method.parameters.indices.map { AccessPathBase.Argument(it) }
        for (base in bases) {
            val cls = key.context.locationClass(key, base) ?: continue                // copy of :64-84
            b.touch(base); b.edge(keepEdge(base)); b.operandFilter(base, interp.typeFilters.of(cls.toType()))
        }
        for (rule in interp.rules.entryPointRulesForMethod(method, s, fact = null))
            if (rw.rewrite(rule.condition).isTrue) rule.actionsAfter.forEach { interp.ruleForms.source(b, rule, emptyList(), it) }
        val sinks = interp.rules.sinkRulesForMethodEntry(method, s, fact = null)
            .filter { rw.rewrite(it.condition).isTrue }                                // as today (:99-101)
            .map { SinkRule(it, listOf(ZERO_PATTERN), interp.ruleForms.endFacts(it)) }
        return RuleStatement(b.build(), genSummary(sinks), sinks)
    }

    /** §4.3 step 3: the ENTRY MARKS. Today `taintMarksAssignedOnMethodEnter` (JIRMethodStartFlowFunction.kt:42-47). */
    fun entryMarks(rules: RuleStatement): Set<TaintMark> = rules.summary.edges
        .filter { it.isSource }.mapNotNullTo(HashSet()) { (it.edge.to.mark as? MarkSlot.Concrete)?.mark }

    /** §4.7 at both exits (`JMethodExitNormalInst`, `JMethodExitExceptionalInst`). ADAPT of
     *  JIRMethodSequentFlowFunction.propagateExitFact (:120-226; today it runs at both exits, :120-126). At the exceptional
     *  exit the rule position `Result` reads `exc` (`ruleFormsAtThrow`, Part II §25; today JIRSequentTaintUtil rebases the
     *  fact on `exc` to `Result`, :67, and back, :82). Steps 1 and 2 apply at both exits; steps 3 to 5 only at the normal
     *  exit. STATEMENT mode: the zero fact and the read bases keep themselves; every other fact passes (step 1). */
    fun exitRules(interp: JIRInterpreter, entry: JIRMethodEntry, key: MethodKey, exit: CommonInst, entryRules: RuleStatement): ExitRules {
        val normal = when (exit) {
            is JMethodExitNormalInst -> true
            is JMethodExitExceptionalInst -> false
            else -> return ExitRules.EMPTY
        }
        val forms = if (normal) interp.ruleForms else interp.ruleFormsAtThrow
        val method = key.method as JIRMethod
        val rw = JIRMarkAwareConditionRewriter(CalleePositionToJIRValueResolver(method), interp.checker, entry.aliasAnalysis, exit)
        val b = MicroEdgeBuilder().apply { touch(AccessPathBase.Zero); edge(ZERO_KEEP) }   // I11 (d): both exits
        for (rule in interp.rules.exitSourceRulesForMethod(method, exit, fact = null)) {
            for (cube in forms.cubes(rw.rewrite(rule.condition))) {
                if (cube.size >= 2) { interp.errors.reject(rule, "exit source with a conjunction (§5.3)"); continue }   // SI4
                cube.singleOrNull()?.let { b.touch(it.base); b.edge(keepEdge(it.base)) }          // f stays in the worklist
                rule.actionsAfter.forEach { forms.source(b, rule, cube, it) }
            }
        }
        val sinks = interp.rules.sinkRulesForMethodExit(method, exit, fact = null, initialFacts = null)   // every fact (D21)
            .flatMap { forms.sinks(it, rw.rewrite(it.condition)) }                    // no array alternative (§4.2)
        return ExitRules(RuleStatement(b.build(), genSummary(sinks), sinks),
            globalStateDrop = normal && sinks.isNotEmpty(),                           // §4.7 step 3 (G2): normal exit only
            entryMarks = if (normal) entryMarks(entryRules) else emptySet())          // §4.7 step 4 (G2): normal exit only
    }

    private fun genSummary(sinks: List<SinkRule>) =
        MicroEdgeBuilder().apply { sinks.forEach { sk -> sk.endFacts.forEach { edge(it.edge) } } }.buildGen()
}
```

The core uses `ExitRules` as `interpreter.md` §4.7 says:

* step 1: `rules.summary` (STATEMENT) on each fact; the results keep the premise;
* step 2: `checkSink` of each `SinkRule` on each item; on `Triggered`, `sk.endFacts` (GEN) on the zero fact, with the
  layer of the sink edge; the field limit; the results join the worklist;
* step 3: if `globalStateDrop`, an item on `S` loses the part that a sink triggered on (`SinkCheck.Triggered.facts`;
  today `dropFinalFacts`, `JIRMethodSequentFlowFunction.kt:271-278`);
* step 4: for a premise `{zero}`, `ops.without(item, ops.targetTree(p, item.layer))` for each `p` of
  `entryMarkParts(item.base)` (only the root `$` leaf, as today);
* step 5: the summary edge, only if `isSummaryBase`.

At the exceptional exit only steps 1 and 2 apply, and the results end there: it is not an end node and makes no summary
edge (`analyzer-core.md` §4.3, §4.4). The backward run starts the zero fact at both exits; the start rules of each exit
are `exitRules(method, exit).reversed()` and the seeds of its exit sinks; a seed also takes the reversed exit sources of
that exit (`interpreter.md` §4.9 SEEDS; `DirectedForms.startRules`, Part II §23.7).

---

## 30. Boundaries: entry, exits, wired graph

Implements `analyzer-core.md` §4.4 and `interpreter.md` I11 (e).

```kotlin
// in JIRMethodEntry (Part II §31.2)
/** analyzer-core.md §4.4: an empty method (no instruction, or a graph with no exit) ends at its entry statement. */
fun exitNodes(key: MethodKey): List<ExitNode> {
    if (isEmpty) return listOf(ExitNode(key.statement, exceptional = false))
    val exits = shared.graph.methodGraph(method).exitPoints()                // JApplicationSingleExitGraph.kt:26-29
        .map { ExitNode(it, it is JMethodExitExceptionalInst) }.toList()
    return exits.ifEmpty { listOf(ExitNode(key.statement, exceptional = false)) }
}
```

A summary edge exists for every base except a local (`isSummaryBase`, §25; today
`JIRMethodCallFactMapper.isValidMethodExitFact`, `JIRMethodCallFactMapper.kt:207-208`). The zero base is a summary base.
A backward summary `jb -> zero` (a requirement that reaches an unconditional source) must exist: the hand-off makes the
forward demand `(D-c = zero, D-p = jb)` from it (`analyzer-core.md` §7.4 item 3). Without the zero base this demand is lost.

```kotlin
// JIRInterpreter (Part II §25)
override fun isSummaryBase(base: AccessPathBase): Boolean = base !is AccessPathBase.LocalVar
//   AccessPathBase.Zero      -> true   (backward `jb -> zero`; forward `{zero} -> zero` is harmless: no binding back)
//   this, arg(i), S, ret     -> true
//   exc, const               -> true   (no binding back takes them; as today)
//   local(i)                 -> false
```

PORT of `BWD/JIRBackwardExitWiringGraph.kt:10-63`. The change: `JIRExitWiredGraph` makes the list of wired nodes once,
and `JIRMethodEntry` keeps the compact graph. So the BFS runs once per method (today: on each `methodGraph` call).

```kotlin
/** I11 (e): a node that reaches no forward exit gets a forward edge to the exceptional exit. Only the zero fact starts
 *  at the exceptional exit, so a caller requirement never enters this code. */
class JIRExitWiredGraph(private val forward: ApplicationGraph<CommonMethod, CommonInst>) :
    ApplicationGraph<CommonMethod, CommonInst> by forward {

    override fun methodGraph(method: CommonMethod): ApplicationGraph.MethodGraph<CommonMethod, CommonInst> {
        val graph = forward.methodGraph(method)
        val exceptionalExit = graph.exitPoints().firstOrNull { it is JMethodExitExceptionalInst } ?: return graph
        val exiting = BitSet()
        val queue = ArrayDeque<CommonInst>()
        for (exit in graph.exitPoints()) if (exiting.mark(exit)) queue.addLast(exit)
        while (queue.isNotEmpty()) for (p in graph.predecessors(queue.removeFirst())) if (exiting.mark(p)) queue.addLast(p)
        val wired = graph.statements().filter { !exiting[it.index] }.toList()
        if (wired.isEmpty()) return graph
        return Wired(this, graph, exceptionalExit, exiting, wired)
    }

    private class Wired(
        override val applicationGraph: ApplicationGraph<CommonMethod, CommonInst>,
        private val graph: ApplicationGraph.MethodGraph<CommonMethod, CommonInst>,
        private val exceptionalExit: CommonInst,
        private val exiting: BitSet,
        private val wired: List<CommonInst>,
    ) : ApplicationGraph.MethodGraph<CommonMethod, CommonInst> by graph {
        override fun successors(node: CommonInst) =
            if (exiting[node.index]) graph.successors(node) else graph.successors(node) + exceptionalExit
        override fun predecessors(node: CommonInst) =
            if (node != exceptionalExit) graph.predecessors(node) else graph.predecessors(node) + wired.asSequence()
    }

    private companion object {
        val CommonInst.index: Int get() = (this as JIRInst).location.index
        fun BitSet.mark(i: CommonInst): Boolean { if (get(i.index)) return false; set(i.index); return true }
    }
}
```

The backward graph is `JIRExitWiredGraph(forward).reversed` (`DF/graph/BackwardGraphs.kt:40-45`), as
`BWD/JIRBackwardAnalysisManager.kt:118`. `MethodInstGraph.build` reads it once per method.

---

## 31. The JIR method context

Implements `analyzer-core.md` §4.8 (the cached part) and §9 (the prescan values).

### 31.1 Prescan lambdas

GENERALIZE `JIRAnalysisManager`: export the lambda values of the prescan. The trackers keep their values after
`selectPhase` (`resetAnalysisCache` resets only the subscribers, `JIRMethodAnalysisContext.kt:78-85`).

```kotlin
/** Call-site index -> the lambda methods that the prescan found, per caller method. Read-only during a run (analyzer-core.md A4). */
typealias PrescanLambdas = Map<JIRMethod, Int2ObjectMap<Set<JIRMethod>>>

// JVM/analysis/JIRAnalysisManager.kt — new member; analyzer-core.md §9: copied once, before run 1.
fun prescanLambdas(): PrescanLambdas {
    val out = HashMap<JIRMethod, HashMap<Int, MutableSet<JIRMethod>>>()
    for (ctx in contexts) {                                                    // :76
        val caller = ctx.methodEntryPoint.method as JIRMethod
        for (e in ctx.lambdaCallResolution.int2ObjectEntrySet()) {
            e.value.forEachRegisteredLambda(object : JIRLambdaTracker.LambdaSubscriber {
                override fun newLambda(method: JIRMethod, lambdaClass: LambdaAnonymousClassFeature.JIRLambdaClass) {
                    val impl = lambdaClass.findMethodOrNull(method.name, method.description) ?: return  // JIRMethodCallResolver.kt:199-200
                    out.getOrPut(caller) { HashMap() }.getOrPut(e.intKey) { HashSet() } += impl
                }
            })
        }
    }
    return out.mapValues { (_, byIdx) -> Int2ObjectOpenHashMap<Set<JIRMethod>>().apply { byIdx.forEach { (i, m) -> put(i, m) } } }
}
```

### 31.2 Method entries and forms

Two levels (DD11):

* PER METHOD (`JIRMethodEntry`): the graphs, the alias analysis, the liveness, the prescan lambdas, and the forms that
  do not read the context: the statement summaries and the exit rules. Every context of the method shares them (today
  the `EmptyMethodContext` twin, `DF/ap/ifds/MethodAnalyzerStorage.kt:37-50`).
* PER METHOD KEY (`JIRMethodForms : MethodForms`): the forms that read the context of the key: the call plans (the
  callee resolution, `JVM/JIRCallResolver.kt:193-246`) and the entry rules (the start filter by the context type, §29).

`analyzer-core.md` §4.8 caches per method (spec issue SI16). The `Interpreter` calls take a `MethodKey`, so
`MethodForms` has the same key. `MethodContextCache` (`analyzer-impl.md` §3.4) gives these `MethodForms` and makes the
`DirectedForms` of each run. It has no forms cache of its own.

```kotlin
/** One per analysis. JIRMethodContextCache (analyzer-impl.md §3.4) holds it. */
class JIRMethodEntries(
    val graph: JApplicationGraph,                    // the forward graph (JApplicationSingleExitGraph)
    val languageManager: JIRLanguageManager,
    val callResolver: JIRCallResolver,
    val rules: TaintRulesProvider,                   // the alias model reads the pass rules (JIRLocalAliasAnalysis.kt:71-115)
    val aliasParams: JIRLocalAliasAnalysis.Params,
    val cancellation: Cancellation,
    val prescanLambdas: PrescanLambdas,
) {
    private val byMethod = ConcurrentHashMap<JIRMethod, JIRMethodEntry>()
    private val byKey = ConcurrentHashMap<MethodKey, JIRMethodForms>()

    operator fun get(key: MethodKey): JIRMethodEntry = get(key.method as JIRMethod)
    operator fun get(m: JIRMethod): JIRMethodEntry = byMethod.computeIfAbsent(m) { JIRMethodEntry(it, this) }

    /** The forms of one method key (both directions). */
    fun forms(interp: JIRInterpreter, key: MethodKey): JIRMethodForms =
        byKey.computeIfAbsent(key) { JIRMethodForms(interp, get(it), it) }
}

/** analyzer-core.md §4.8 "per method": the parts that do not read the context. */
class JIRMethodEntry internal constructor(val method: JIRMethod, internal val shared: JIRMethodEntries) {
    val isEmpty: Boolean = method.instList.size == 0                                  // JIRLanguageManager.isEmpty
    internal val size = if (isEmpty) 1 else shared.languageManager.getMaxInstIndex(method) + 1
    fun index(s: CommonInst): Int = if (isEmpty) 0 else shared.languageManager.getInstIndex(s)

    @Suppress("UNCHECKED_CAST")
    private val common get() = shared.graph as ApplicationGraph<CommonMethod, CommonInst>

    val liveness by lazy { JIRLocalVariableReachability(method, shared.graph, shared.languageManager) }  // REUSE; not for an empty method
    val aliasAnalysis: JIRLocalAliasAnalysis? by lazy {                                              // JIRAnalysisManager.kt:129-135
        if (!shared.aliasParams.useAliasAnalysis || isEmpty) null
        else JIRLocalAliasAnalysis(shared.graph.methodGraph(method).entryPoints().first(), shared.graph,
            shared.callResolver, shared.rules, liveness, shared.cancellation, shared.languageManager, shared.aliasParams)
    }
    val lambdas: Int2ObjectMap<Set<JIRMethod>> = shared.prescanLambdas[method] ?: Int2ObjectMaps.emptyMap()

    /** analyzer-core.md §4.4: the forward graph, and the wired reversed graph (Part II §30). */
    fun graph(direction: Direction): MethodInstGraph =
        if (direction == Direction.FORWARD) forwardGraph else backwardGraph
    private val forwardGraph by lazy { MethodInstGraph.build(shared.languageManager, common, method) }
    private val backwardGraph by lazy { MethodInstGraph.build(shared.languageManager, JIRExitWiredGraph(common).reversed, method) }

    /** The forms that do not read the context: one per method, for every key. */
    internal val statements = FormsCache<StatementSummary>(size) { it.reversed() }
    internal val exits = FormsCache<ExitRules>(size) { ExitRules(it.reversed(), globalStateDrop = false, entryMarks = emptySet()) }

    // fun exitNodes(key: MethodKey): List<ExitNode>: the code is in Part II §30
}

/** analyzer-core.md §4.8 "per (method, direction)", keyed by the METHOD KEY (DD11, SI16): the forms that read the context,
 *  and the per-method forms of `e`. */
class JIRMethodForms internal constructor(
    private val interp: JIRInterpreter,
    private val e: JIRMethodEntry,
    private val key: MethodKey,
) : MethodForms {
    private val plans = FormsCache<CallPlan>(e.size) { it.reversed() }
    private val entry = FormsCache<RuleStatement>(1) { it.reversed() }

    override fun statement(direction: Direction, s: CommonInst) =
        if (e.isEmpty) StatementSummary.EMPTY
        else e.statements.get(e.index(s), direction) { JIRStatementForms(interp, e).build(s as JIRInst) }
    override fun call(direction: Direction, s: CommonInst, call: CommonCallExpr) =
        plans.get(e.index(s), direction) { JIRCallPlanBuilder(interp, e, key, s as JIRInst, call as JIRCallExpr).build() }
    override fun entryRules(direction: Direction) =
        entry.get(0, direction) { if (e.isEmpty) RuleStatement.EMPTY else JIRBoundaryForms.entryRules(interp, e, key) }
    override fun exitRules(direction: Direction, exit: CommonInst) =
        if (e.isEmpty) ExitRules.EMPTY                                              // I8: no entry or exit rule
        else e.exits.get(e.index(exit), direction) { JIRBoundaryForms.exitRules(interp, e, key, exit, entryRules(Direction.FORWARD)) }
}
```

The exit rules read the key only for `entryMarks`, and the entry sources do not read the context (only the start filter
does), so the first key that builds them gives the same result as every other key.

MEMORY. The caches keep their forms with strong references for the whole analysis: the forward forms of every reached
method key, and the reversals after the first backward run. The forms are small against the run stores (one
`StatementSummary` per statement, with a few `PathEdge`s; one `CallPlan` per call). A soft reference as today
(`JVM/analysis/JIRMethodAnalysisContext.kt:53-85`) is not safe here. The core keys run state by the identity of form
objects: a `ConjunctiveEdge` or a conjunctive `SinkRule` is the `rule` key of `ConjunctionStore.add` (Part I §7.10), and
`Guard.SinkTriggered` names its `SinkRule`. A rebuilt form is a new key, and the stored literal inputs are lost. The
caches have the lifetime of the analysis (`JIRMethodEntries` lives as long as the `IterationDriver`).

The run part of today's context (`JIRTaintAnalysisContext`, the sink tracker) is not here. The core owns the stores of a
run (`analyzer-core.md` §4.8).

---

## 32. Deviations from today (`interpreter.md` §6) in code

| # | Reused class | Today | New |
|---|---|---|---|
| D1 | `StatementSummaryBuilder.read` (:74-92) | `keepAllExcept(base, accessors)` + `edge(source, source)` | `MicroEdgeBuilder.read`: `edge(keepEdge(base))` (§24) |
| D2 | same, `base == to` branch (:86-88) | `edge(fact(base).exclude(accessors.first()), null)` | no edge; only `x.f.* -> x.*` |
| D3 | `MethodSequentFlowFunction.transfer` (:65-68) | `to == null -> refineInitial(effect.exclusion)` | no `to == null` edge exists; `ApOps.applyEdge` gives the `above` case in the demand layer |
| D4 | `JIRMethodCallFlowFunction.propagateFact` (:141-143) | `addSideEffectRequirement(factReader)` | no reader; `ApOut.markRequest` (Part I) |
| D5 | `JIRMethodCallSummaryHandler.handleSummary` (:40-69) | `MethodSummaryEdgeApplicationUtils` delta with refinement | `ApOps.satisfying` + `ApOps.applySummary` (Part I) |
| D6 | `JIRMethodCallFactMapper` (:141-242) | `rebase` per fact | `bindIn`/`bindBack` micro edges (§28.2); same mapping and filters |
| D8 | `JIRTaintCleanActionEvaluator` (`TaintEvaluator.kt:29-71`) | `FinalFactAp.clean` with `DeepAccessorExclusion` | `Cleaner` + `ApOps.clean` (`*∖T`, the request on a partial clean) |
| D9 | same, `RemoveMark(.., ExactAndAnyField)` | cleans through an `[any]` only | `CleanReach.AT_AND_BELOW` (§27.5) |
| D10 | same, `RemoveAllMarks(P.AnyField)` | removes an `[any]` child | `CleanReach.BELOW`, every mark |
| D11 | `JIRFactTypeChecker.AccessorFilter` (:84-136) | `FilterResult` over the fact tree, marks as accessors | the same filter as `TypeFilter.may` on the path only (`localFilter`); the mark policy is `TypeFilter.markPolicy` (§26.2) |
| D12 | same, `AnyAccessor` case (:88-94) | `[any]` on a primitive base: Reject (keeps `$` only) | the filter never reads the tail: `[any]` stays |
| D13 | `AccessTree.concat` filter | the caller delta filtered at `*` | none (Part I) |
| D14 | `JIRMethodSummaryEdgeProcessor.process` (:15-25) | compatibility filter at the exit | removed |
| D16 | `MethodAnalyzer` depth gate | `INITIAL_ALLOWED_FACT_DEPTH` | none (`analyzer-impl.md` §2.1) |
| D17 | rules on `S` | applied as written | the mapping of `interpreter.md` §1.4 and the rule errors (`JIRRuleForms.source`, `pass`, `unconditional`, `endFacts`) |
| D18 | `TaintPassActionEvaluator.copyAllFacts` (`DF/taint/Propagator.kt:55-87`) | `readPosition` + `mkAccessPath` copy the subtree below the any-field node | `P.[any] -> Q.[any]` (§27.4); results in the demand layer (W6) |
| D19 | `JIRMethodCallResolver.resolvedJirMethodCalls` (:184-209) | a `Lambda` result adds `ResolutionFailure` beside the lambda methods | the prescan lambda methods only; a resolution failure only with no known lambda (`JIRCallPlanBuilder.resolve`, §28.4) |
| D20 | `TaintConfigUtils.applyCleaner` (`JVM/TaintConfigUtils.kt:62-92`) | the condition is evaluated on the bound fact (`TaintFactAwareConditionEvaluator`) | only a cleaner with no mark literal left acts (`JIRRuleForms.cleanSteps`, §27.5) |
| D21 | `JIRMethodExitRuleProvider.sinkRulesForMethodExit` (`core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/JIRMethodExitRuleProvider.kt:18-19`) | exit sinks only on zero-premise edges | the rules are read with `initialFacts = null`: every fact (§29) |
| D22 | `JIRMethodSequentFlowFunction.applyUnconditionalSinks` (:191-200) | a stub | `ZERO_PATTERN` (§27.3): it fires on the zero fact at each exit |
| D23 | `JIRMethodCallSummaryHandler.prepareFactToFactSummary` (:71-79), `handleZeroToZero` (:29-38); `JIRMethodCallFlowFunction.unresolvedCallDefaultFactPropagation` (:330-339) | the rewriter on fact-to-fact and ND summaries; the default identity in caller coordinates | the stage `Rewrite(RETURNED -> REWRITTEN)` on every result at `RETURNED` (§28.1, §28.3) |
| D24 | `TaintConfigUtils.applyPassThrough` (`JVM/TaintConfigUtils.kt:48-60`) | a `CopyAllMarks` condition is evaluated on the fact | a rule error; the rule applies without its mark literals (`passRules`, §28.5) |

D1 and D2 as code (the old builder stays for the prescan):

```kotlin
// Today, StatementSummaryBuilder.kt:83-88
if (base != to) { keepAllExcept(base, accessors); edge(source, source) }       // y\{f} -> y, y.f -> y.f
else { edge(fact(base).exclude(accessors.first()), null) }                     // x\{f} -> null (refine only)
// New, MicroEdgeBuilder.read (Part II §24)
if (base != to) edge(keepEdge(base))                                           // y.* -> y.*
edge(starEdge(base, path, to, emptyList()))                                    // y.f.* -> x.*
```

D12 as code:

```kotlin
// Today, JIRFactTypeChecker.kt:88-94: an `[any]` node under a primitive type is rejected
is AnyAccessor -> if (actualType.unboxIfNeeded() is JIRPrimitiveType) return FilterResult.Reject
// New: the same AccessorFilter walks only the path (ApOps.filter, Part I §5.5); the `[any]` tail is not an accessor,
// so this case never runs and the `[any]` leaf stays. The policy reads only a concrete mark at the root path.
TypeFilter(may = checker.localFilter(t), markPolicy = if (t.unboxIfNeeded() is JIRPrimitiveType) MarkPolicy { isPrimitiveTracking(it) } else null)
```

---

## 33. Test plan

Implements `interpreter.md` §7 in implementation terms. Proof first: each test names the Lean theorem or `example` that
it mirrors.

### 33.1 Test classes and the TDD order

In the column "Pins (`interpreter.md`)", a bare § number names a section of `interpreter.md`.

| # | Test class (module, package) | Needs (Part I) | Pins (`interpreter.md`) | Lean |
|---|---|---|---|---|
| 1 | `StatementSummaryReversalTest` (opentaint-dataflow, `bidi.interp`) | `Reference.kt` (`revEdge`) | §4.9 STATEMENTS: touched + targets; A5 identity for a gen-only target; a conjunction gives one edge per literal; no filter; `forward` kept | `Reverse.Stmt.rev`, `rev_touched`, `revNoId_breaks`, `Stmt.rev_step_iff` |
| 2 | `RuleStatementReversalTest` (same) | `Reference.kt` | §4.9 RULE ROLES; end-fact targets pass; `ExitRules.reversed` drops G2; clean steps unchanged | `Reverse.revInstr` |
| 3 | `MicroEdgeBuilderTest` (same) | `Reference.kt`, `ExclusionSet.of` | the write rule: `C.s = x` gives two keep edges with one exclusion each; a weak write keeps the base; A2/A3 alias edges; STAGE and GEN modes; `TypeFilter.and` on one base | `Cases.lean` `storeF` |
| 4 | `CallPlanReversalTest` (same) | `Reference.kt` (`revEdge`, `concat`), `ApManager` | the step table of Part II §23.6; guards and filters go; `PASS_OVER` for alias bases; entry/exit swap; a non-forward plan fails; the zero fact passes over and enters (`FormsReference.run`) | `Reverse.Call.rev`, `bindRev_of_star` |
| 5 | `JIRStatementFormsTest` (opentaint-jvm-dataflow, `jvm.bidi.interp`; replaces the edge asserts of `JIRStatementSummaryTest`) | `ApManager` | one test per row of §2.2; §2.4 pinned rows; operand vs result filters; read source at `x = C.s` with `ZERO_KEEP`; a read source with a non-`Result` target is a rule error | `Cases.lean` `loadF`, `loadF'`, `storeF` |
| 6 | `JIRRuleFormsTest` (same) | `ApManager` | §4.1 rows, AnyField table; §4.2 negated literal, `Or`, cubes; §5.3 conjunctions; §5.2 one test per mapping row with `<string-bytes>`; D20: a cleaner with a mark literal left gives no step and no request; D24: `CopyAllMarks` with a mark literal is a rule error and gives its edge without the literal; §4.2 array elements: the alternatives of a call sink; §1.4 rows and rule errors (§33.5 items 14, 16) | `Statics.SWF`, `Statics.CexAny`, `NDExact.LitConc` |
| 7 | `JIRCallPlanTest` (same) | `ApManager` | §3.1 bindings with filters; §3.3 S and zero; §3.5 constructor (no alias: SI15); §3.7 two `UNRESOLVED` stages, the identity has no filter, pass rules, default getter; `UnresolvedCallObserver` calls the tracker with `ruleApplied`; §3.8 aliases + `MemoryEffect`; §3.9 prescan lambdas (D19: no `UNRESOLVED` stage when the prescan knows a lambda); the forward stage table (§33.5 items 14, 17) | `Reverse.BindTargetsStar`, `Backward.NoZeroBack` |
| 8 | `JIRBoundaryFormsTest` (same) | `ApManager` | §4.3 context filter; §4.7 `globalStateDrop`, `entryMarks`, `entryMarkParts` gives only `(b, [], $, T)`; §4.7 at `JMethodExitExceptionalInst`: the exit sources and sinks with `Result` read as `exc`, `globalStateDrop = false`, no `entryMarks`; D22: an unconditional exit sink has `ZERO_PATTERN`; exit nodes; empty method; exit wiring of a loop that never returns | `Backward.ExitReach`, `Backward.ZeroKept` |
| 9 | `JIRFormsContractTest` (same) | `ApManager` | every method of the samples jar: I6, I7, I11 (a)–(f), I12 (a)–(f) over all forms | `Backward.StmtsMarkRev`, `Reverse.BindTargetsStar`, `Backward.NoZeroBack`, `Backward.ZeroKept`, `Statics.SWF`, `Invariant.no_univ_star` |
| 10 | `JIRTypeFiltersTest` (same) | `ApOps.filter` | §5.1 rows; `*`/`[any]` tails kept; the mark policy on `int` and `Integer`, a `%%primitive%%` mark kept; prefix-closed | `Exact.FiltValid`, `Core.filt_keeps` |
| 11 | `JIRStatementEffectTest` (same) | `ApOps` | the effect table of §2.4 and the table of `ap.md` §4.2; `ops.without` with `entryMarkParts` keeps `b.f.$ (T)` and `b.[any] (T)` | `Cases.lean` examples at lines 61–89 |
| 12 | the analysis tests of `interpreter.md` §7.1 | Part I and `analyzer-impl.md` | end to end, through phase 3 (`analyzer-impl.md` §8.1) | — |

Order: by the "Needs" column. 1 → 2 → 3 → 4 (`Reference.kt` and `ApManager` only, no JIR) → 5 → 6 → 7 → 8 → 9 (JIR and
`ApManager`) → 10 → 11 (Part I `ApOps`) → 12.

### 33.2 Example: the pinned rows of `interpreter.md` §2.4

`testInterpreter`, `testKey` and `TestRules` are helpers of `JIRInterpreterTestKit` (test sources): a `JIRMethodEntries`
over `cp` with `JApplicationSingleExitGraph`, a `TaintRulesProvider` made from lists, and the key
`MethodEntryPoint(EmptyMethodContext, entry statement)` of the method of a statement.

```kotlin
class JIRStatementFormsTest : BasicTestUtils() {
    private val cls = "sample.sequent.StatementSummarySample"          // the sample of JIRStatementSummaryTest
    private val f = FieldAccessor(cls, "f", "java.lang.Object")
    private val next = FieldAccessor(cls, "next", cls)
    private val interp by lazy { testInterpreter(cp, rules = TestRules.EMPTY) }   // JIRMethodEntries over cp, no alias analysis

    private fun assigns(m: String) = findMethod(cls, m).instList.instructions.filterIsInstance<JIRAssignInst>()
    private fun base(v: JIRValue) = accessPathBase(v)!!
    private fun star(b: AccessPathBase, vararg p: Accessor) = starSide(b, p.map { interp.idx(it) })     // DD6
    private fun e(from: PathFact, to: PathFact, ex: Accessor? = null) =
        PathEdge(from, to, ex?.let { ExclusionSet.of(interp.idx(it)) } ?: ExclusionSet.Empty)      // ExclusionSet.of(a): Part I §3.2
    private fun summary(s: JIRInst) = interp.statementSummary(testKey(s), s)
    private fun edges(s: JIRInst) = summary(s).edges.map { it.edge }.toSet()

    @Test // §2.4 row 1, D1; Lean Cases.lean `loadF'`
    fun `x = y_f keeps y whole and reads y_f`() {
        val s = assigns("fieldRead").first { it.rhv is JIRFieldRef }
        val x = base(s.lhv); val y = base((s.rhv as JIRFieldRef).instance!!)
        assertEquals(setOf(e(star(y), star(y)), e(star(y, f), star(x))), edges(s))
        assertEquals(setOf(x, y), summary(s).touched)
        assertTrue(x in summary(s).resultFilters && y in summary(s).typeFilters)      // §2.1 steps 3 and 5
    }

    @Test // §2.4 rows 2 and 4; I3; Lean Cases.lean `storeF`
    fun `y_f = x and a_f = a are strong writes`() {
        val w = assigns("fieldWrite").first { it.lhv is JIRFieldRef }
        val y = base((w.lhv as JIRFieldRef).instance!!); val x = base(w.rhv as JIRValue)
        assertEquals(setOf(e(star(y), star(y), f), e(star(x), star(x)), e(star(x), star(y, f))), edges(w))
        val sw = assigns("selfWrite").first { it.lhv is JIRFieldRef }
        val a = base(sw.rhv as JIRValue)
        assertEquals(setOf(e(star(a), star(a), f), e(star(a), star(a, f))), edges(sw))
    }

    @Test // §2.4 row 5, D2: no refine-only edge
    fun `x = x_next has only the read edge`() {
        val read = assigns("selfRead").first { (it.rhv as? JIRFieldRef)?.field?.name == "next" }
        val rhv = read.rhv as JIRFieldRef
        val s = JIRAssignInst(read.location, rhv.instance!!, rhv)                        // as JIRStatementSummaryTest
        val x = base(rhv.instance!!)
        // A synthetic statement has the index of `read`: build it with no cache, or the cache gives the form of `read`.
        val summary = JIRStatementForms(interp, interp.entries[read.location.method]).build(s)
        assertEquals(setOf(e(star(x, next), star(x))), summary.edges.map { it.edge }.toSet())
    }

    @Test // §2.2 static write; strongKeep of a two-accessor path
    fun `C_s = x keeps S except the class and the class except the field`() {
        val s = assigns("staticWrite").first { it.lhv is JIRFieldRef }
        val x = base(s.rhv as JIRValue)
        val c = ClassStaticAccessor(cls); val sf = FieldAccessor(cls, "sField", "java.lang.Object")
        val st = AccessPathBase.ClassStatic
        assertEquals(setOf(e(star(st), star(st), c), e(star(st, c), star(st, c), sf),
            e(star(x), star(x)), e(star(x), star(st, c, sf))), edges(s))
    }
}
```

### 33.3 Example: the reversed call plan against the backward step table

```kotlin
class CallPlanReversalTest {
    private val manager = ApManager(Cancellation())
    private val r = AccessPathBase.LocalVar(1); private val a = AccessPathBase.LocalVar(2); private val b = AccessPathBase.LocalVar(3)
    private val S = AccessPathBase.ClassStatic; private val ret = AccessPathBase.Return; private val arg0 = AccessPathBase.Argument(0)
    private val Z = AccessPathBase.Zero
    private val f: AccessorIdx = manager.accessors.index(FieldAccessor("C", "f", "java.lang.Object"))   // DD6
    private val T = manager.marks.mark("T")                                                              // DD7
    private val m = testMethodKey("m")

    /** `r = m(a)`; `m` is a source on `Result`; `b.f` is an alias of `r` through the call. */
    private fun forward(): CallPlan {
        fun stage(vararg es: PathEdge) = MicroEdgeBuilder().apply { es.forEach { edge(it) } }.buildStage()
        val src = PathEdge(ZERO_FACT, PathFact(ret, emptyList(), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty)
        return CallPlan(setOf(S, a, r), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, stage(keepEdge(S), starEdge(Z, listOf(), Z, listOf()), starEdge(a, listOf(), arg0, listOf()))),
            CallStage.Edges(BOUND, REWRITTEN, SOURCES, stage(ZERO_KEEP, src)),
            CallStage.Clean(BOUND, ADDED, emptyList()),
            CallStage.Callees(ADDED, RETURNED, listOf(m)),
            CallStage.Rewrite(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, stage(keepEdge(S), starEdge(arg0, listOf(), a, listOf()), starEdge(ret, listOf(), r, listOf()))),
            CallStage.Edges(REWRITTEN, AFTER, ALIASES, stage(starEdge(ret, listOf(), b, listOf(f))), Guard.MemoryEffect),
        ), sinks = emptyList(), entry = BEFORE, exit = AFTER)
    }

    @Test // analyzer-core.md §4.5 step table; Lean Reverse.Call.rev
    fun `the reversed plan has the stages of the backward call order`() {
        val rev = forward().reversed()
        assertEquals(AFTER to BEFORE, rev.entry to rev.exit)                              // steps 1 and 9
        assertEquals(setOf(S, a, r, b), rev.touched)                                     // step 1: + the alias base
        assertEquals(setOf(
            Triple(AFTER, REWRITTEN, BIND_BACK), Triple(AFTER, REWRITTEN, ALIASES),       // step 2
            Triple(AFTER, BEFORE, PASS_OVER),                                             // step 2, A5
            Triple(REWRITTEN, BOUND, SOURCES),                                            // step 3
            Triple(REWRITTEN, RETURNED, null),                                            // step 4 (Rewrite)
            Triple(RETURNED, ADDED, null),                                                // step 5.1 (Callees)
            Triple(ADDED, BOUND, null),                                                   // step 6 (Clean)
            Triple(BOUND, BEFORE, BIND_IN),                                               // step 8
        ), rev.stages.map { Triple(it.from, it.to, (it as? CallStage.Edges)?.kind) }.toSet())
        val edges = rev.stages.filterIsInstance<CallStage.Edges>()
        assertTrue(edges.all { it.guard == null && it.summary.typeFilters.isEmpty() && it.summary.resultFilters.isEmpty() })
        assertTrue(edges.single { it.kind == ALIASES }.summary.edges.any { it.edge == starEdge(b, listOf(f), ret, listOf()) })
    }

    @Test // the reversed plan run on requirements (FormsReference.run); the callee maps ret to arg0
    fun `a requirement on r reaches the source and the argument, and b passes over`() {
        val rev = forward().reversed()
        val callee = { c: Conclusion -> if (c.fact.base == ret) listOf(c.copy(fact = c.fact.copy(base = arg0))) else emptyList() }
        val req = Conclusion(PathFact(r, emptyList(), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty, demand = false)
        val ref = FormsReference(manager)
        val trace = ref.run(rev, req, callee, clean = { c, _ -> listOf(c) })
        assertTrue(trace.any { (p, c) -> p == BOUND && c.fact.base == Z })               // step 3: the zero demand
        assertTrue(trace.any { (p, c) -> p == BEFORE && c.fact.base == a })               // steps 5.1, 6, 8
        val onB = Conclusion(PathFact(b, listOf(f), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty, false)
        val tb = ref.run(rev, onB, callee, clean = { c, _ -> listOf(c) })
        assertTrue(tb.any { (p, c) -> p == BEFORE && c.fact.base == b })                  // PASS_OVER (A5)
        assertTrue(tb.any { (p, c) -> p == REWRITTEN && c.fact.base == ret })             // reversed alias edge (AC5)
    }
}
```

### 33.4 Contract test sketch (`JIRFormsContractTest`)

```kotlin
@TestFactory
fun `every form of every sample method meets I6, I7, I11 and I12`() = sampleMethods().map { method ->
    DynamicTest.dynamicTest(method.toString()) {
        val key = testKey(method)
        val forms = allForwardForms(interp, key)                                    // statements, plans, entry/exit rules
        for (e in forms.statementEdges()) {
            assertTrue(revEdge(e) != null)                                            // I11 (b), Backward.StmtsMarkRev
            assertTrue(e.from.tail != Tail.EXACT || e.from.mark is MarkSlot.Concrete) // I7, S8
            assertTrue(e.from.tail != Tail.EXACT || e.to.tail != Tail.STAR)           // I7, S8
            assertTrue(e.to.mark !is MarkSlot.Concrete || e.from.mark is MarkSlot.Concrete)  // I6, S7
        }
        for (e in forms.bindings()) assertEquals(MarkSlot.STAR, e.to.mark)          // I11 (a), Reverse.BindTargetsStar
        assertTrue(forms.bindBack().none { it.to.base == AccessPathBase.Zero })     // I11 (c), Backward.NoZeroBack
        // I11 (d) is about statements: the STATEMENT-mode summaries and the rule statement of a call (SOURCES). The
        // BIND_IN and END_FACTS stages touch zero with no keep edge, as they must (Part II §23.3).
        assertTrue((forms.statementModeSummaries() + forms.stages(StageKind.SOURCES))
            .filter { AccessPathBase.Zero in it.touched }.all { ZERO_KEEP in it.edges.map { e -> e.edge } })   // I11 (d)
        assertTrue(forms.cleaners().none { it.base == AccessPathBase.Zero })        // I11 (d); also Cleaner.init (Part I §6)
        assertTrue(forms.sinkPatterns().all { it.fact.tail != Tail.STAR })          // I11 (f)
        assertTrue(forms.staticEdges().all(::staticWellFormed))                     // I12 (a)-(e), Statics.SWF
    }
}
```

### 33.5 The new tests of `interpreter.md` §7.2 (items 14 to 17)

| Item | Test (class) | Form check (Part II) | End to end (`analyzer-impl.md`, phase 3) |
|---|---|---|---|
| 14 array elements of a call sink (§4.2) | `JIRRuleFormsTest`, `JIRCallPlanTest` | a sink `ContainsMark(Argument(0), T)` on an `Object[]` argument gives two `SinkRule`s with the patterns `(arg0, [], $, T)` and `(arg0, [e], $, T)`, one `rule`; on a `String` argument one `SinkRule`; a conjunctive sink on two array arguments gives four alternatives; the receiver, `Result`, the entry and the exit sinks get none | `arg(0).[e].$ (T)` triggers the sink; the backward run seeds `seedPatterns()` of both alternatives |
| 15 exit rules at the exceptional exit (§4.7) | `JIRBoundaryFormsTest` | `exitRules(m, JMethodExitExceptionalInst)`: an exit sink on `Result` has the pattern on `exc`; an exit source on `Result` targets `exc`; `globalStateDrop` false, `entryMarks` empty; `reversed()` gives the backward start rules of that exit | an exit sink on `Result` triggers on the thrown tainted value; an exit source at the exceptional exit adds no summary edge |
| 16 cleaners (§4.2, D20) | `JIRRuleFormsTest` | `RemoveMark(T, P) if ContainsMark(P, T)` and `RemoveMark(T, arg0) if Not(ContainsMark(arg1, RAW))` give no `CleanStep`; the same rule with no condition gives `Cleaner(P, EXACT, T)` (and `<string-bytes>` on a `String` position) | the first two do not clean; the third cleans |
| 17 lambdas (§3.9, D19) | `JIRCallPlanTest` | with prescan lambdas for the call: a `Callees` stage with the lambda methods, no `UNRESOLVED` stage; with none: no `Callees` stage for the lambda, the `UNRESOLVED` stages | the known lambda takes no unresolved path; the unknown one does |

```kotlin
@Test // interpreter.md §7.2 item 14; §4.2 ARRAY ELEMENTS OF A CALL SINK
fun `a call sink on an array argument has the element alternative`() {
    val rules = TestRules(sinks = listOf(sinkOn("sample.Sinks", "sink", ContainsMark(Argument(0), RuleMark("T")))))
    val interp = testInterpreter(cp, rules)
    val (key, s, call) = callOf("sample.ArraySink", "callWithArray")              // sink((Object[]) a)
    val plan = interp.callPlan(key, s, call)
    val t = interp.manager.marks.mark("T")
    val e = interp.idx(ElementAccessor)
    fun pat(vararg p: AccessorIdx) = Pattern(PathFact(AccessPathBase.Argument(0), p.toList(), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)
    assertEquals(setOf(listOf(pat()), listOf(pat(e))), plan.sinks.map { it.patterns }.toSet())
    assertTrue(plan.sinks.map { it.rule }.distinct().size == 1)                       // one vulnerability key
    val (key2, s2, call2) = callOf("sample.ArraySink", "callWithString")             // sink((String) a)
    assertEquals(listOf(listOf(pat())), interp.callPlan(key2, s2, call2).sinks.map { it.patterns })
}
```

`TestRules`, `sinkOn` and `callOf` are helpers of `JIRInterpreterTestKit` (§33.2). `sample.ArraySink` is a new sample
class: `callWithArray(Object[] a) { Sinks.sink(a); }` and `callWithString(String a) { Sinks.sink(a); }`.

---

## 34. Spec issues and deviations from today

This document implements the specs as they are. Each row below is a point where a spec was not clear, or where the spec
(and so this proposal) differed from today's code and `interpreter.md` §6 did not list the difference. The user decided
the rows on 2026-10-07 (`ap-history.md` F63); the specs now say the decisions. The column "Decision" gives the decision
and the place in the spec; "as proposed" means that the proposal stands. The columns "This proposal" and "Effect" give
the code of this document after the decision. Every row stays as a record. The ids `SI1` to `SI16` are ids of this
document; they are not the rules `S1` to `S14` of `ap.md`.

| Id | Spec | Today (`path:line`) | This proposal | Effect on the findings | Decision (2026-10-07) |
|---|---|---|---|---|---|
| SI1 | `interpreter.md` §4.1, §4.5 step 3 | A call sink on `Argument(i)` that can be an array also reads `arg(i).[e]` (`JVM/taint/JIRMethodCallTaintUtil.kt:186-203`). The spec has no such pattern. | A sink at a call has one alternative per array choice: the literal on `arg(i)·ρ`, and `(arg(i), [e]·ρ, t, T)` when `callArgumentMayBeArray` holds (§27.3, §28.1). (Was: no `[e]` pattern.) | None: as today. | As on main: `interpreter.md` §4.2 ARRAY ELEMENTS OF A CALL SINK; §6 "kept as today". |
| SI2 | `interpreter.md` §4.7 | The production rule provider fires the exit sinks only on zero-premise edges (`core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/JIRMethodExitRuleProvider.kt:18-19`, installed at `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/Provider.kt:52`). The spec checks every fact. | The exit sinks check every fact (`sinkRulesForMethodExit(..., initialFacts = null)`, §29). | More: exit-sink reports also for taint that enters the method through a parameter. | As proposed: `interpreter.md` D21. |
| SI3 | `interpreter.md` §4.1, §4.2; `ap.md` S9 | A pass rule applies only when its condition holds on the fact (`applyPassThrough`, `JVM/TaintConfigUtils.kt:48-60`; `applicableRules`, `:77-92`). The spec has no exact form for a `CopyAllMarks` rule with a mark condition: its `*` premise cannot be a conjunction literal (`ap.md` S9). | Such a rule is a rule error (`RuleErrors`), and it applies without its mark literals (§28.5). (Was: the condition was dropped with no error.) | More, only for such a rule; the JVM rule sets have none. | `interpreter.md` §4.2 (the `CopyAllMarks` bullet), D24. |
| SI4 | `interpreter.md` §5.3 | The spec says that exit sources never make an ND edge, but an exit source can have two positive literals. Today such a rule can reach `createNDEdge`, which calls `error("Unused operation")` (`JVM/analysis/JIRMethodSequentFlowFunction.kt:217-218`), and the analysis stops. | A rule error (§29): the interpreter rejects the cube and logs it once. | Fewer than the rule asks for: such an exit source gives no fact. Today the analysis can fail. | Not in F63: the proposal stands; the spec is unchanged. |
| SI5 | `analyzer-core.md` §4.5 (the stage table) and `interpreter.md` §3.5 | The constructor pass-over takes every added fact, also a fact on `S` (`JVM/analysis/JIRMethodCallFlowFunction.kt:213-216`). The stage table says "the receiver and argument positions"; `interpreter.md` §3.5 says "every added fact". | The `CONSTRUCTOR` stage has the identity of every bound position, `S` included (§28.1). | None: as today. | Not in F63: the proposal stands (`interpreter.md` §3.5); the spec is unchanged. |
| SI6 | `interpreter.md` §3.1 | The binding back keeps a fact on a constant base as it is (`JVM/JIRMethodCallFactMapper.kt:157-160`). The spec lists `const.* → const.*`, but no finite edge form exists for it, and no form makes a fact on a constant base. | No edge for a constant base (§28.2). | None: no fact has a constant base at a callee exit. | Not in F63: the proposal stands; the spec is unchanged. |
| SI7 | `interpreter.md` §3.9 | A lambda call is also an unresolved call: the resolver adds `ResolutionFailure` beside the lambda methods (`JVM/analysis/JIRMethodCallResolver.kt:191`). The spec says that the call "becomes a resolved call". It does not say if the unresolved path stays. | A `Lambda` result is the prescan lambda methods only; with none it is a resolution failure (§28.4). | Fewer: a flow that only the pass rules or the default identity of the lambda call give is lost. | As proposed: `interpreter.md` §3.9, D19. |
| SI8 | `analyzer-core.md` §4.9 | One list of filters per base (`StatementSummary.BaseTransfer.typeFilters`, `DF/ap/ifds/summary/StatementSummary.kt:10-14`) holds the operand filters and the lhs filter (`JVM/analysis/JIRStatementSummary.kt:71`). `transfer` applies all of them to the input fact (`DF/ap/ifds/analysis/MethodSequentFlowFunction.kt:50-53`). The spec has one `typeFilters` map per base, but `interpreter.md` §2.1 step 5 and `interpreter.md` §3.1 filter the results. | `StatementSummary.resultFilters` beside `typeFilters` (§23.2, §22.2). | Precision only: a result filter drops only paths that the static type cannot have (`ap.md` S5). The mark policy keeps its gap (`interpreter.md` G6). It can remove a false positive. | As proposed: an addition to `analyzer-core.md` §4.9 (§22.2); the spec is unchanged. |
| SI9 | `analyzer-core.md` §4.5 | On `origin/saloed/backward-main`, a requirement on a base that the call does not touch passes over the call (`skipCall`, `BWD/JIRBackwardMethodCallFlowFunction.kt:67-72`), and each alias adds its unaliased demand (`callSiteAliasDemands`, `:116-138`). The spec: `StatementSummary.reversed` adds the identity of `interpreter.md` A5 for an untouched target. Inside a call stage the two points have other coordinates, so that identity is wrong there. The alias-base identity must go from `AFTER` to `BEFORE`, and the step table has no such stage. | STAGE mode touches every base of its edges, so `reversed()` adds no identity. `CallPlan.reversed()` adds the stage `AFTER → BEFORE` of kind `PASS_OVER` (§23.6). | None: the requirement on an alias base passes over the call, as on the backward branch. | As proposed: an addition to `analyzer-core.md` §4.9 (§22.2); the spec is unchanged. |
| SI10 | `interpreter.md` §4.2, §5.2 | Every `RemoveMark` on a `String` position also cleans `P.<string-bytes>`, also for a cleaner with a condition (`JVM/taint/TaintEvaluator.kt:43-61`, after `applyCleaner`, `JVM/TaintConfigUtils.kt:62-75`). The spec gives the `<string-bytes>` row of `interpreter.md` §5.2 for every cleaner, but for a conditional cleaner the literal at `P` does not decide `P.<string-bytes>`. | Every acting cleaner is unconditional (SI13), so the `<string-bytes>` row of `interpreter.md` §5.2 applies to every acting cleaner and to the rewriter (§27.5). (Was: only for an unconditional cleaner.) | None beyond SI13: a conditional cleaner does not act at all. | Resolved by SI13: `interpreter.md` §4.2, §5.2 (only an unconditional cleaner acts), D20. |
| SI11 | `interpreter.md` §4.7, §6 ("as today") | The exit sources and the exit sinks also run at `JMethodExitExceptionalInst`, with `Result` read as the thrown value (`JVM/analysis/JIRMethodSequentFlowFunction.kt:124-126`, `JVM/taint/JIRSequentTaintUtil.kt:67, 82`). | The exit rules run at both exits; at the exceptional exit `Result` reads `exc`, and steps 3 to 5 do not apply (`ruleFormsAtThrow`, §29). (Was: `ExitRules.EMPTY` at the exceptional exit.) | None: as today. | As today: `interpreter.md` §3.4, §4.7, §6 ("kept as today"); `analyzer-core.md` §4.3, §4.4. |
| SI12 | `interpreter.md` §4.1, §4.7; `ap.md` §4.9 | An unconditional exit sink never fires on the zero fact (`JVM/analysis/JIRMethodSequentFlowFunction.kt:191-200`, a TODO). It fires once per non-zero fact at the exit (`DF/taint/TaintUtil.kt:183-186`). | Its pattern is `ZERO_PATTERN` (§27.3): it fires where the zero fact reaches the normal exit. | More: also in a method with no taint at the exit. | As proposed: `interpreter.md` D22. |
| SI13 | `interpreter.md` §4.2, §6 | A conditional cleaner fires when its condition holds on the bound fact. A negated literal counts as true (`DF/taint/TaintFactAwareConditionEvaluator.kt:37`, `JVM/TaintConfigUtils.kt:77-92`), and a literal with another mark at the same position reads the same fact. | Only an unconditional cleaner acts: a cleaner with a mark literal left after the static evaluation gives no step and no request (§27.5). (Was: the decided part `(P, exact, T)`.) | More: a conditional cleaner never cleans (possible false positives). | `interpreter.md` §4.2 (rewritten), D20; `ap.md` §4.2, §4.7. |
| SI14 | `interpreter.md` §3.7 item 1, §5.2 ("the same") | The summary rewriter acts only on fact-to-fact and ND summaries (`JVM/analysis/JIRMethodCallSummaryHandler.kt:71-90`, called at `DF/ap/ifds/MethodAnalyzer.kt:995, 1032, 1071, 1180`), not on a zero-premise summary (`handleZeroToZero`, `:29-38`). It rewrites the default identity in caller coordinates (`JVM/analysis/JIRMethodCallFlowFunction.kt:330-338`), so there it acts only by chance. | The `Rewrite` stage acts on every result at `RETURNED`: the zero-premise summaries and the default identity too (§28.3). | Fewer: on a method with a user-defined rule, a source of the same mark in the method body loses that mark at the rule positions. | As proposed: `interpreter.md` D23. |
| SI15 | `interpreter.md` §3.5 and §3.8 AC3, AC4 | The constructor pass-over takes no alias (`JVM/analysis/JIRMethodCallFlowFunction.kt:213-216`). `interpreter.md` §3.5 sends the pass-over "through the aliases", but AC3 does not list it, and AC4 drops an identity result. | The pass-over has `Origin.IDENTITY`, so `Guard.MemoryEffect` drops it (§28.1), as today. | None: the alias holds the same fact (AC4). | Not in F63: the proposal stands (as today); the spec is unchanged. |
| SI16 | `analyzer-core.md` §4.8, §4.9 ("per (method, statement)") | The flow-function caches are per context (`JVM/analysis/JIRMethodAnalysisContext.kt:41-76`). | The call plans and the entry rules read the context (the callees, the start filter), so they are cached per method key. The statement summaries and the exit rules are cached per method (§31.2, DD11). | None: a cache per method would give the callees of one context to another. | As proposed: DD11; the spec is unchanged. |
