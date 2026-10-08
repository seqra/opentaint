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
| DD1 | MODULES AND PACKAGES. The new code is in the Gradle modules of today's core, in new packages: `org.opentaint.dataflow.bidi.ap`, `bidi.store` and `bidi.interp` in `core/opentaint-dataflow-core/opentaint-dataflow`, and `org.opentaint.dataflow.jvm.bidi.interp` in `core/opentaint-dataflow-core/opentaint-jvm-dataflow`. `analyzer-impl.md` §1 adds `bidi.engine`, `bidi.driver` and `jvm.bidi`. | The new code uses the utilities of these modules (`AccessorIdx`, `FactTypeChecker`, `Cancellation`, `RefManager`, `LanguageManager`) and an `internal` declaration of the JVM module (`jIRDowncast`, `core/opentaint-dataflow-core/opentaint-jvm-dataflow/.../jvm/ap/ifds/JIRLanguageManager.kt:56`). The old core stays in the same modules, because the prescan runs it. | §1, §20 |
| DD2 | REFERENCE FORMS AND TRIES. The spec forms are per path (`Pattern`, `PathEdge`, `Conclusion`). The code keeps the conclusions of one edge group in ONE `Facts` value of one kind (DD12): `Reach`, `FlowTree` or `TaintTree` (`ap.md` §7.2). The per-path forms stay in `Reference.kt` as the reference forms. | The tests compare each operation on `Facts` with its reference form. | §6, §8 |
| DD3 | THE EDGE DELTA. A propagated item is `(premise: PremiseKey, node: CommonInst, facts: Facts)`. The layer is `facts.layer` (`analyzer-core.md` §4.3). There is no `Edge` class: the kind replaces it. REACH is today's `ZeroToZero`; TAINT is `ZeroToFact`, a concrete `FactToFact` and `NDFactToFact`; FLOW is an abstract `FactToFact` (`ap.md` §7.6). | The premise key and the base give the kind (`ap.md` §7.2): `nonZeroCount` names the edge (§4.6), the mark of the premise separates FLOW from the rest, and a conclusion on the zero base is REACH (`{zero}` and a backward `{jb}` have REACH and TAINT conclusions). | §3.4, §4.1 |
| DD4 | ADDED FACTS ARE `Facts` PER LINK KEY. After the binding and the cleaners, a caller fact is one `Facts` value in callee coordinates. Its leaves are the added facts. `AddedFactStore` keeps one merged value per (caller reference, link layer, kind key): REACH (no more), FLOW (base, exclusion, mark exclusion), TAINT (base). `add` returns the delta: the new leaves are the new links. A `Link` (the spec form) is one leaf with its `CallerRef`. The same value is the added-fact part of a subscription. | Today a subscription keeps caller fact trees too (`MethodTreeAccessPathSubscription`). The replay and the delivery read the satisfying part with one function, `ApOps.satisfying` (P4 of `analyzer-core.md` §5.3). | §5.4, §7.5 |
| DD5 | INTERNING. `ApManager` interns `PathNode`, `InitialAp`, `PremiseSet`, `MarkSet`, `ExclusionSet` and `TaintLeaves`, so equality is identity where a store key needs it. Each store hash-conses its trie nodes with its own `TrieInterner`. Its table is a cache behind a managed soft reference (the `SoftReferenceManager` of the `RefManager`), as today: the memory guard clears it, and the next intern makes a new one. The intern policy is per trie: a deliberate difference to today's store-wide pass (§4.5). `TrieNode` and `Facts` equality is structural, with an identity fast path. | A shared node table needs a lock and holds the tries of every store in one table. A cleared table loses only sharing: an interned node stays valid, and equality is structural. A callee publication meets a caller subscription of another store, so equality must not use identity alone. | §4.5, §5.1 |
| DD6 | A PATH ELEMENT IS `AccessorIdx` (an `Int`, `ap/ifds/access/util/AccessorInterner.kt:17`): a field, an element or a class accessor (`ap.md` §1, W5). A path is `List<AccessorIdx>` in the reference forms and `IntArray` or `PathNode` in the tries. `isClass` is `AccessorIdx.isStaticAccessor()`. Part II converts a JIR `Accessor` with `manager.accessors.index(a)`. | `ap.md` §3.4 says that the sets hold `AccessorIdx`. The type-info and value accessors serve the prescan only (W5). | §3.1, §6 |
| DD7 | `TaintMark` is `@JvmInline value class TaintMark(val id: Int)` in `bidi.ap`, with `MarkTable` (`manager.marks.mark(name)`, `manager.marks.name(m)`). The zero mark is `TaintMark.ZERO`. The JVM glue maps a rule mark to it by its name. | The JVM `TaintMark` is in `configuration-rules-jvm`. `opentaint-dataflow` does not see it: its `build.gradle.kts` has `configuration-rules-common` only. | §3.1 |
| DD8 | THE ZERO BASE is `AccessPathBase.Zero` (GENERALIZE of `ap/ifds/Accessors.kt:5`). | `ap.md` §1, §2.4. The old core never makes it, so its behaviour does not change. | §2, §3.4 |
| DD9 | `TypeFilter(may, markPolicy)` is a class in `bidi.ap`. `ApOps.filter` applies `may` to the path, then the mark policy to the concrete marks of a TAINT tree at the root path and at each node of the `[e]` chain below the root, with the type of that level (`MarkPolicy.keeps(mark, elements)`), as today. `TypeFilter.and` is the conjunction of two filters on one base. The backward run applies no filter and no policy. | `interpreter.md` §5.1 applies the mark policy "after the filter", to the same facts. Part II builds `may` with today's `JIRFactTypeChecker`. Today the filter of the element type (`FilterNext` of `[e]`) also reads the marks below `[e]` (§5.5). Only a TAINT leaf has a concrete mark. | §5.5, §26.2 |
| DD10 | THE VULNERABILITY KEY AND THE WITNESSES. The key is `(rule, method, statement)`: the method of the method key WITHOUT the context, so one sink statement reached in several contexts is one vulnerability (`ap-history.md` F67). `VulnerabilityStore` keeps SEVERAL witnesses per key: one entry per (key, alternative, method key, run, witness shape). A `SinkWitness` names its `alternative` (the index of the sink alternative of the rule at the statement) and its `methodKey`. The facts of an entry are the union of the triggering parts of every witness of that entry. | The confirmation reads only the method key and the shape (the premise set and the layer of each sink edge), and each sink edge stays a leaf. So the merge loses nothing. With the alternative and the method key in the entry, the union never joins two group keys at one literal and never mixes two alternatives (§7.12). | §7.12 |
| DD11 | FORMS PER METHOD KEY. `JIRMethodForms` caches the call plans and the entry rules per method key. `JIRMethodEntry` caches the statement summaries and the exit rules per method. | The callees of a call and the start filter read the context of the key. `analyzer-core.md` §4.8 caches per method (spec issue SI16). | §31.2 |
| DD12 | THREE CONCLUSION KINDS (`ap.md` §7.2). `Reach` (the zero fact: one bit per layer), `FlowTree` (abstract marks: a `*` leaf with the tree exclusion in the normal layer, an `[any]` leaf in the demand layer, the tree mark `*∖X`), `TaintTree` (concrete marks: `$` leaves; `$` and `[any]` leaves in the demand layer). FLOW follows from the premise (`PremiseKey.isFlow`), REACH from the zero base of the conclusion; a `PremiseSet` (an ND edge) is ALWAYS TAINT. The TYPES enforce W2 and the `$`/`*` split: a `FlowTree` has one flag per node and no concrete mark; a `TaintTree` has no `*` leaf, no exclusion and no mark exclusion. The constructors check W1 for the demand layer (a demand `FlowTree` has the Empty exclusion) and W6 (a normal `TaintTree` has no `[any]` mark), so no constructor path, `withRoot` included, makes a bad value. The restricted runs have REACH and TAINT only. Proved: `Kinds.kinds_D`, `kinds_DR`, `kinds_DB_taint`, `nd_taint`, `ndz_taint` (`ap.md` §10.10). For run 1 with the static rule (`Statics.DS`: the position answer and the static mark answer) the partition is argued (`ap.md` §11.2). | `ap.md` §7.2 gives the reasons (S7, S8, W2, W6, `Coverage.edge_conc`). The mark gate becomes simple (§5.3): every request comes from a FLOW fact. | §4.1, §5 |
| DD13 | THE PREMISE KEY is the `InitialAp` itself for one member, and a `PremiseSet` (a sorted array) for two or more. The union of premise sets (`ApManager.union`, `premiseOf`) DROPS the zero fact: `{zero}` only if every input is `{zero}`, so `{zero, i}` is `{i}`. So a `PremiseSet` is exactly an ND edge: no zero member, every member with a concrete mark, TAINT conclusions only (its `init` checks the members; `MethodEdgeStore` and `RunSummaryStore` check the kind). Proved equivalent to the list model of the Lean `ND.DN`: `NDZero.dnz_to_dn`, `dn_to_dnz` (`ap.md` §10.10). | `ap.md` §7.1, §4.6; `ap-history.md` F65. One member is the common case: no wrapper, no list. The zero fact adds no condition: it is at every node that an edge reaches. | §3.4, §5.1 |
| DD14 | ONE TRIE. `TrieNode<P>` is the one hash-consed node; the payload `P` is the leaf of the node (`FlowLeaf` or `TaintLeaves`), with its algebra `LeafAlgebra<P>`. ONE set of generic algorithms (`TrieOps.kt`; the code is in §4 and §5.5 to §5.7): merge and delta (T1, T4), maps, prepend and chain, `minusNode`, `graft`, the fold (T5), the subsumption, the cut (`ap.md` §4.4), the path filter, interning, `boundedDepth`; and one path walk (`walkPath`). No other depth bound: today's `limitFieldAccess`, `limitElementAccess` and `containsStatic` are not ported (§2, §4.2). Per kind only: the edge application, the gate, `clean`, `checkMark`, `satisfying`/`applySummary`, `restrict`, `emit`. The other shared utilities: `MarkGate` (one mark gate), `Results` (one result collector per kind), `Facts.groupKey` (one store key), and the two standing joins `KaryJoin` (k slots of one type) and `StandingJoin` (two sides with index lookups). | No non-trivial logic is written twice. Today's `AccessTree.AccessNode` algorithms are adapted once (§2). The two joins differ in what they own (§7.10). | §4, §5, §7.10 |
| DD15 | NAMES. `applyCompiledEdge` (with `EdgeApplication`) is the TREE FORM of `concat` of `ap.md` §4.1 ("delta-concat"): it computes the part of each fact that the premise selects (case `below` or `above`) and concatenates it with the target. The reference keeps the spec name `concat`. `MarkCheck`/`checkMark` is the one check of a mark literal: sinks, conjunction literals, conjunctive sinks. `MarkGate` is the one mark gate (`ap.md` §4.1 steps 4 and 5) of `applyCompiledEdge`, `checkMark` and `satisfying`. | `ap-history.md` F64. | §5.3, §5.8 |

---

## Part I — The access path and its stores

Scope: the AP with all its stores (`ap.md` §2 to §9) and the test plan of `ap.md` §13. The code is in the module
`core/opentaint-dataflow-core/opentaint-dataflow`, in the new packages `org.opentaint.dataflow.bidi.ap` and
`org.opentaint.dataflow.bidi.store` (DD1). The behaviour of the old core does not change (the prescan runs it).

## 0. Conventions and additions to the AP interface

### 0.1 Conventions

| # | Convention | Reason |
|---|---|---|
| K1 | A path element is `AccessorIdx` (DD6): a field, an element or a class accessor. `isClass` is `AccessorIdx.isStaticAccessor()`. A counted accessor is a field or an element accessor (`isCounted`, §3.1). | `ap.md` §1, §3.4, W5. |
| K2 | A mark is the value class `TaintMark` of `bidi.ap` (DD7). | The JVM `TaintMark` is not visible in `opentaint-dataflow`. |
| K3 | The zero base is `AccessPathBase.Zero` (DD8). Each exhaustive `when` over `AccessPathBase` gets a `Zero` branch (§2). | `ap.md` §1, §2.4. |
| K4 | `MethodKey` is `typealias MethodKey = MethodEntryPoint` (REUSE, `ap/ifds/MethodWithContext.kt:24`). | `ap.md` §1 and `analyzer-core.md` §1 define the method key as the `MethodEntryPoint` of the method (context and forward entry statement). |
| K5 | A RUN store has one writer (the runner of its method, `analyzer-core.md` O1). It has no lock. `ApManager`, `ApOps` and `VulnerabilityStore` are thread-safe. §7.1 gives the table. | `analyzer-core.md` §2. |
| K6 | A FLOW premise is one `InitialAp` with the mark `*` (`PremiseKey.isFlow`). Every other `InitialAp` gives REACH (a conclusion on the zero base) or TAINT conclusions; a `PremiseSet` gives TAINT only. | `ap.md` §7.2, §4.6. |

### 0.2 Additions to the AP interface

`ap.md` gives the types of `ap.md` §3.4, §7.1, §7.2 and §8.7, the operations of `ap.md` §4, §6.2 to §6.5 and §9.1,
and the stores of `ap.md` §8. Part I adds these members. `analyzer-impl.md` and Part II call them.

| What | Why | Code |
|---|---|---|
| `PremiseKey` (`size`, `member(k)`, `isZero`, `nonZeroCount`), `PremiseSet`, `ApManager.premiseOf(members)`, `ApManager.union(a, b)`, `PremiseKey.members`, `PremiseKey.forEachMember`, `PremiseKey.isFlow` | The premise set of `ap.md` §7.1 without a list (DD13); the union of `ap.md` §4.6, without the zero fact; the kind of `ap.md` §7.2 (K6). | §3.4, §5.1 |
| `Facts`, `Reach`, `FlowTree`, `TaintTree`, `Facts.groupKey` (`GroupKey`, `FactsKind`); `Layer.or(demand)` | The three conclusion kinds of `ap.md` §7.2 (DD12). | §4.1 |
| `TrieNode<P>`, `TrieLeaf`, `FlowLeaf`, `TaintLeaves`, `LeafAlgebra<P>`, `FlowAlgebra`, `TaintAlgebra`, `TrieInterner<P>`, `walkPath` | The one trie and its generic algorithms (DD14). | §4 |
| `FlowGroup`, `TaintGroup`, `ConclusionGroup`, `StoreInterners` | The merge rules T1 to T5 and the subsumption of `ap.md` §8.1, per kind and for all kinds of one premise key. | §4.3 |
| `ApMode`, `ApOut` (`result(f: Facts)`), `CollectingOut` | The constants of a run that the operations read; the receiver of the results and of the requests. | §3.2, §5.2 |
| `ApOps.applyEdge`, and inside it `applyCompiledEdge`, `EdgeApplication`, `MarkGate` | The micro edge on all paths of one `Facts` (`ap.md` §7.3; DD15). | §5.3 |
| `ApOps.satisfying(a, j, mode, record = false)` | The part of an added fact whose facts satisfy the premise `j` (P4 of `analyzer-core.md` §5.3, DD4). | §5.4 |
| `ApOps.applySummary(a, j, g, mode, out)`, `ApOps.applyCombination(parts, g, mode, out)` | A summary on the satisfying part, by kind; a summary with several premises on one full combination (`ap.md` §4.6, event E6). | §5.4 |
| `ApOps.filter`, `TypeFilter`, `MarkPolicy` (`keeps(mark, elements)`) | `ap.md` §4.8 and the mark policy of `interpreter.md` §5.1 at the root and below each `[e]` (DD9). | §5.5 |
| `ApOps.clean`, `Cleaner`, `CleanReach` | `ap.md` §4.7, per kind. | §5.6, §6 |
| `ApOps.limit` | `ap.md` §4.4, with the tables of the cut points and of the facts that can exceed `L`. | §5.7 |
| `ApOps.checkMark(c, p, mode): MarkCheck` (`None`, `Request`, `Holds(facts, covered)`) | The one check of a mark literal: a sink, a conjunction literal, a literal of a conjunctive sink (`ap.md` §4.6, §4.9; DD15). | §5.8 |
| `ApOps.without(c, part)`, `ApOps.targetTree(target, layer)`, `ConjunctiveEdge` | The exact removal of a part (the global-state rule and the entry marks of `interpreter.md` §4.7); a one-leaf TAINT tree for a conjunction target or an end fact; the conjunctive micro edge. | §5.8 |
| `ApOps.zero(layer): Reach`, `ApOps.policy(added)` | The end facts take no input fact: on a trigger they apply to the zero fact in the layer of the sink edge or of the combination (`interpreter.md` §4.1); `ap.md` §6.2 on one `Facts`. | §5.9 |
| `ApOps.requestAction(i, kind, a, caller): RequestAction` | The AP rule of one (request, link) pair (`ap.md` §4.5, §4.10 items 2 to 4). | §5.10 |
| `ApOps.leaves(f)`, `ApOps.leavesNear(f, p)` | The per-path view of one `Facts`, and its leaves that overlap `(f.base, p, *, {}, *)` (one walk of `p`). The links and the tests read it. | §5.11 |
| `ApManager(cancellation, refManager)`, `ApManager.softRefs`, `ExclusionSet.of(a: AccessorIdx)`, `InitialAp.manager` (internal), `ApManager.newInterners()`, `ApManager.flowTree`, `taintTree`, `factsOf` | The `RefManager` of the memory guard holds the soft trie tables (DD5); the exclusion `{a}` of one keep edge (`interpreter.md` §2.1 `strongKeep`); `Record.reversedAt` interns the reversed premise; the trie interners of one store (DD5); the canonical factories of the three kinds. | §3.2, §3.4, §4.5, §5.1 |
| `MethodEdgeStore(m, method, lm, fieldLimit)`, `edgesAt` | The edges per kind (`ap.md` §8.1), with the W3 assert; two queries of the edges at a statement for the tests (trace resolution is out of scope, `ap-history.md` F67). | §7.3 |
| `AddedFactStore` (the key per kind, `add` returns the delta, `overlapping(base, path)`, `links()`) | DD4. The request join of `ap.md` §8.8 and the support at the barrier read the links. | §7.5 |
| `DemandStore.Builder`; the implicit zero demand of `near` | The driver builds the store before the run (`analyzer-core.md` A4); every method key has the zero demand (`analyzer-core.md` §4.4). | §7.7 |
| `RecordStore` (an interface), `PersistentRecordStore`, `view()`, `persist(direction, summaries)`, `Record.reversedAt(a)` | A run reads the store through a read-only view (`analyzer-core.md` A4). The driver persists the records at a barrier (R1). A reader in the other direction reads the reversed records (R3). | §7.8 |
| `KaryJoin<T>`, `StandingJoin<A, B>(nearB, nearA, meet)` (`newA`, `newB`); `ConjunctionStore.add(rule, statement, arity, literal, input)`, `Input`, `Combination`, `ndJoin<S>(NdKey)`, `NdSummaryJoin` | The two standing joins: k slots of one type (the literals of a conjunction or of a conjunctive sink, the members of a summary with several premises; `ap.md` §8.9, `analyzer-core.md` §5.4), and two sides with index lookups (the request × link join of `ap.md` §8.8). | §7.10 |
| `RequestKind.Position(path: PathNode)` (the type of `analyzer-core.md` §10) | The path of a position is an interned `PathNode` (§3.3), not a list: the key of `RequestStore`, the argument of `ApOut.positionRequest` and of `ApManager.position`. | §5.2, §7.9 |
| `SourceHitStore.entries()` | The driver reads the source hits at the barrier. | §7.11 |
| `VulnerabilityKey(rule: CommonTaintConfigurationSink, method: CommonMethod, statement)`, `SinkEdge(premise, layer, facts: Facts)`, `SinkWitness(alternative, methodKey, edges, run, endFacts)`, `ConcurrentVulnerabilityStore` | The key reuses the rule object of every run and has the method without the context. Several witnesses per key, one per alternative and method key; the witness merge (DD10). | §7.12 |

---

## 1. Package map

```
core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/
├ ap/ifds/Accessors.kt              GENERALIZE: + AccessPathBase.Zero (DD8)
├ ap/ifds/AccessPathBaseStorage.kt  GENERALIZE: `Zero -> error(...)` in `getOrCreate`/`find` (the old core never makes Zero)
└ bidi/
  ├ ap/
  │ ├ Facts.kt             Direction, Layer, Tail, ApMode, TaintMark, MarkSet, MarkSlot, ExclusionSet (§3.2)
  │ ├ AccessorTable.kt     AccessorTable, MarkTable: id <-> value, no ConcurrentReadSafe map (§3.1)
  │ ├ PathNode.kt          PathNode: the interned accessor chain of a premise (§3.3)
  │ ├ Premise.kt           PremiseKey, InitialAp, PremiseSet, the zero fact (§3.4)
  │ ├ Trie.kt              TrieLeaf, FlowLeaf, TaintLeaves, TrieNode<P>, LeafAlgebra<P>, FlowAlgebra, TaintAlgebra (§4.1)
  │ ├ TrieOps.kt           the generic trie algorithms: merge, delta, maps, prepend, chain, minus, graft, fold, subtract, cut, filter (§4.2–§4.4)
  │ ├ TrieInterner.kt      T6 hash-consing, one per store and kind, its table behind a soft reference (§4.5)
  │ ├ PathWalk.kt          walkPath: the prefix nodes and the node of a path, for every trie (§4.6)
  │ ├ Conclusions.kt       Facts, Reach, FlowTree, TaintTree (§4.1)
  │ ├ Groups.kt            FlowGroup, TaintGroup, ConclusionGroup, StoreInterners: T1–T5 and the subsumption (§4.3)
  │ ├ ApManager.kt         the interners and the factories (§5.1)
  │ ├ ApOut.kt             ApOut, Results (one collector per kind), CollectingOut (§5.2)
  │ ├ ApOps.kt             the facade of the AP operations (§5)
  │ ├ MarkGate.kt          MarkGate: ap.md §4.1 steps 4 and 5 per kind (§5.3)
  │ ├ EdgeApplication.kt   CompiledEdge, applyCompiledEdge, EdgeApplication: the tree form of delta-concat (§5.3)
  │ ├ Summary.kt           satisfying, applySummary, applyCombination (§5.4)
  │ ├ Clean.kt             the cleaner per kind (§5.6)
  │ ├ Limit.kt             the field limit, the cut (§5.7)
  │ ├ MarkCheck.kt         MarkCheck, checkMark, without, targetTree (§5.8)
  │ ├ Demand.kt            zero, startFact, policy, emit, restrict (§5.9)
  │ ├ Primitives.kt        Cleaner, CleanReach, TypeFilter, MarkPolicy, ConjunctiveEdge, RequestAction
  │ └ Reference.kt         the per-path forms of ap.md §3.4, §4.1, §6.3, §6.4 and of §6 (DD2)
  └ store/
    ├ PathTrie.kt          the path index of ap.md §8 (§7.2)
    ├ MethodEdgeStore.kt   ap.md §8.1, per kind (§7.3)
    ├ InitialFactStore.kt  ap.md §8.2 (§7.4)
    ├ AddedFactStore.kt    ap.md §8.3; CallerRef, Link (§7.5)
    ├ RunSummaryStore.kt   ap.md §8.5 (§7.6)
    ├ DemandStore.kt       ap.md §8.6; DemandStore.Builder (§7.7)
    ├ RecordStore.kt       ap.md §8.7; Record, RecordStore, PersistentRecordStore (§7.8)
    ├ RequestStore.kt      ap.md §8.8; RequestKind (§7.9)
    ├ KaryJoin.kt          the standing joins: KaryJoin, StandingJoin (§7.10)
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
| `FieldAccessor`, `ElementAccessor`, `ClassStaticAccessor` (`ap/ifds/Accessors.kt:96`, `:125`, `:148`) | REUSE | the values of `AccessorTable`; `TypeFilter` reads them |
| `TypeInfoAccessor`, `TypeInfoGroupAccessor`, `ValueAccessor`, `TaintMarkAccessor`, `FinalAccessor`, `AnyAccessor` (`ap/ifds/Accessors.kt`) | REMOVE, NOT USED | the prescan only (type info), the tail and the mark of a fact (`ap.md` §1, W5) |
| `AccessorIdx`, the bit layout and its tests (`ap/ifds/access/util/AccessorInterner.kt:17`, `:94-137`) | REUSE | path elements; `isFieldAccessor`, `ELEMENT_ACCESSOR_IDX` (counted), `isStaticAccessor` (class) |
| `AccessorInterner.AccessorStorage` (`ap/ifds/access/util/AccessorInterner.kt:20-38`) on `ConcurrentReadSafeObject2IntMap` | ADAPT | `AccessorTable`, `MarkTable`: `ConcurrentHashMap` and a volatile copy-on-write array (§3.1); only the field and the class storages |
| `ConcurrentReadSafeObject2IntMap`, `ConcurrentReadSafeInt2ObjectMap` (`src/main/java/.../util/`) | REPLACE | not used by the new core (§3.1) |
| `ExclusionSet` (`ap/ifds/ExclusionSet.kt:6`) | REPLACE | `bidi.ap.ExclusionSet`: no `Universe`, `IntArray` of `AccessorIdx` |
| `AccessPath.AccessNode` (`ap/ifds/access/tree/AccessPath.kt:261`) | ADAPT | `PathNode`: interned, no manager field, no `addParent` collapse (`:316`, `limitFieldAccess` `:375`, `limitElementAccess` `:354`) |
| `AccessPath` (`ap/ifds/access/tree/AccessPath.kt:27`) | REPLACE | `InitialAp` (also the premise key of one member, DD13) |
| `AccessTree.AccessNode` (`ap/ifds/access/tree/AccessTree.kt:261`) | ADAPT | `TrieNode<P>` (DD14): one generic node; the leaf payload `P` replaces `isAbstract`/`isFinal`/`deepAccessorExclusion`; no `[any]` edge, no `$` child. DROPPED: the other depth bounds of today's node, `limitFieldAccess` (the repeated-field fold, `:1468`, through `addParentFieldAccess`, `:625`), `limitElementAccess` with `SUBSEQUENT_ARRAY_ELEMENTS_LIMIT = 2` (`:599`, `:1635`) and the `containsStatic` guard (`:273`, `:436`). The new AP has only the field limit `L` (`ap.md` §4.4; §4.2, §5.7), as for `PathNode` |
| `mergeAdd`, `mergeAddDelta`, `mergeAddStep`, `mergeAddDeltaStep`, `AccessNodeMergePair`, `mergeNodeLoop`, `pushSharedChildPairs`, `mergeAccessorsRaw`, `transformAccessors`, `removeSingleAccessor`, `trimModifiedAccessors` (`AccessTree.kt:815`, `:854`, `:826`, `:859`, `:803`, `:912`, `:1005`, `:1388`, `:1671`, `:1638`, `:1712`) | ADAPT | `TrieOps.kt` (§4.2), generic over `LeafAlgebra<P>`: the leaf union and the leaf delta replace the flags; the parameter `foldToAny` (`:815`, `:854`) and `trimAnyCoveredAndPushChildren` (`:965`) go |
| `TreeApManager.create`, `createElementAndField` (`AccessTree.kt:1784`, `:1806`) | ADAPT | `LeafAlgebra.node`: one shared leaf node per payload |
| `annotateAbstractNodes(cache)` (`AccessTree.kt:735`) | ADAPT | the identity memo of every node map (`mapLeaves`) |
| `filterAccessNode(FactApFilter)` (`AccessTree.kt:1031`) | ADAPT | `filterPath` (§5.5), generic: no `[any]` edge, no `FinalAccessor` check. A mark is a leaf payload, not an accessor, so the mark check of the filter below `[e]` (`:1039-1045` with `FilterNext`) becomes the `[e]` chain walk of the mark policy (`markPolicyOnElements`, §5.5), as today |
| `concatToLeafAbstractNodes` (`AccessTree.kt:1114`, `:1281-1326`) | ADAPT | `graft` (§4.2) in `applySummary` (§5.4), generic over the kinds of the summary and of the result; it MERGES at nested occurrences as today (`:1321-1324`). DROPPED: `filterTypes` (`:1290`; no summary-side filter, `ap.md` §4.8), `limitElementAccess` (`:1291`), `filterDeepExclusion` (`:1292`), `limitFieldAccess` (`:1299`) and the `isFinal` leaf of the summary (`:1321`): the field limit `L` is the only depth bound |
| `filterStartsWith` (`AccessTree.kt:1329`) | ADAPT | the run-1 part of `satisfying` (§5.4) |
| `internNodes` (`AccessTree.kt:1125-1172`), `markInterned` (`:1174`), `AccessTreeInterner` (`ap/ifds/access/tree/AccessTreeInterner.kt:8`) | ADAPT | `TrieInterner<P>.internBottomUp` and its `InternStrategy` (§4.5): the copy with `interned = true`, the children by identity |
| `AccessTreeSoftInterner` (`ap/ifds/access/tree/AccessTreeSoftInterner.kt:7`) | ADAPT | the soft table of `TrieInterner` (§4.5): `refs.createRef(table)` (`:18-23`), re-created on demand |
| `TreeSetWithCompression.internIfRequired`, `intern(idx)` (`ap/ifds/access/tree/TreeSetWithCompression.kt:14`, `:19`) | ADAPT | `TrieInterner.internIfRequired` (§4.5): the force size and the rate stay; the rate tick interns the trie of the add, not every trie of the store (a deliberate difference, §4.5) |
| `RefManager`, `SoftReferenceManager` (`util/RefManager.kt:6`, `util/SoftReferenceManager.kt:8`) | REUSE | `ApManager.softRefs = refManager.softRefManager("bidi")`: the memory guard clears every trie table (DD5) |
| `boundedDepthRaw`, `FieldLimiter.limit` (branch `saloed/any-field-limit`, `ap/ifds/access/tree/AccessTree.kt:298`, `:722`) | ADAPT | `TrieNode.boundedDepth`, `FieldLimitCut` (§5.7): generic; no `[any]` edge to keep |
| `TreeApManager.isCounted` (branch, `ap/ifds/access/tree/TreeApManager.kt:79`) | ADAPT | `AccessorIdx.isCounted()`: field or element, no unroll strategy (`ap.md` §1) |
| `TreeFieldLimitCheck` (branch) | ADAPT | the W3 assert of `MethodEdgeStore.add` (§7.3) and the test `FieldLimitTest` (§8) |
| `TreeApManager` (`ap/ifds/access/tree/TreeApManager.kt:34`), `ap/ifds/access/ApManager.kt` | REPLACE | `bidi.ap.ApManager` (§5.1) |
| `AnyAccessorUnrollStrategy`, `AccessTreeAnySuffixMatcher`, `DeepAccessorExclusion` (`ap/ifds/access/DeepAccessorExclusion.kt:6`), `TreeInitialFactAbstraction`, mark/`$`/`[any]` accessors in paths | REPLACE | the `[any]` tail, the mark exclusion `*∖X` of a FLOW tree, the policy and the emission (§5.9; `ap.md` §6.2, §6.3, §7.6) |
| `AccessBasedStorage` (`ap/ifds/access/tree/AccessBasedStorage.kt:12`) | ADAPT | `PathTrie` (§7.2): keyed by `IntArray`, plain fastutil maps, `walkPath`, `lookupPrefixes`/`lookupExtensions`/`around` |
| `MethodAnalyzerEdges` (`ap/ifds/MethodAnalyzerEdges.kt:13`): `SameInitialZeroFactEdges` (`:150`), `instructionStorageIdx` (`:272`) | REUSE the structure | `MethodEdgeStore` (§7.3): the REACH bit sets per statement (now per premise key and layer), the statement index |
| `MethodAnalyzerEdges.EdgeStorage`, `CommonF2FSet` (`ap/ifds/MethodAnalyzerEdges.kt:240`, `ap/ifds/access/common/CommonF2FSet.kt:131`) | REPLACE | `ConclusionGroup` (§4.3): one premise key, every base and kind |
| `EdgeNonUniverseExclusionMergingStorage` (`ap/ifds/access/tree/MethodEdgesInitialToFinalTreeApSet.kt:75`) | REPLACE | `FlowGroup`, `TaintGroup` (§4.3): the union of `:95` is forbidden by T3 |
| `MethodInitialToFinalApSummaries` (`ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt:13`) | REPLACE | `RunSummaryStore` (§7.6): the union of `:271` is forbidden by T3 |
| `MethodTreeAccessPathSubscription`, `AccessTreeIndex` (`ap/ifds/access/tree/MethodTreeAccessPathSubscription.kt:22`, `:199`) | REPLACE | `PathTrie` (the delivery-side miss of `analyzer-core.md` Appendix A P4 goes) |
| `FactTypeChecker.FactApFilter`, `FilterResult` (`ap/ifds/FactTypeChecker.kt:27`, `:12`) | REUSE | `TypeFilter.may` (§5.5) |
| `TaintSinkTracker` rule assumptions (`ap/ifds/taint/TaintSinkTracker.kt:173-240`) and vulnerability nodes (`:15`) | REPLACE | `KaryJoin`, `ConjunctionStore` (§7.10), `VulnerabilityStore` (§7.12) |
| `Edge` (`ZeroToZero`, `ZeroToFact`, `FactToFact`, `NDFactToFact`) | REPLACE | `PremiseKey` + `Facts` (DD3, DD12) |
| `Cancellation` (`util/Cancellation.kt:5`) | REUSE | `ApManager.cancellation.checkpoint()` in long walks |
| `LanguageManager.getInstIndex`, `getMaxInstIndex` (`ap/ifds/LanguageManager.kt:9`) | REUSE | the statement index of `MethodEdgeStore` |
| `CommonTaintConfigurationSink` (`configuration-rules-common`) | REUSE | `VulnerabilityKey.rule` |

---

## 3. The fact model (`ap.md` §2, §3.4, §7.1)

### 3.1 Accessors and marks

```kotlin
package org.opentaint.dataflow.bidi.ap

/** AccessorIdx <-> Accessor. ADAPT of AccessorInterner (ap/ifds/access/util/AccessorInterner.kt:19): the same index layout
 *  (REUSE of its companion, :94-137), a new storage. Today AccessorStorage.index reads a ConcurrentReadSafeObject2IntMap
 *  without a lock (:24-26). Its getInt re-reads non-volatile fields in a `while (true)` loop
 *  (ConcurrentReadSafeObject2IntMap.java:27-33). The JIT can hoist the reads, and the loop then never ends
 *  (analyzer-core.md Appendix A). AccessorTable uses a ConcurrentHashMap for value -> id and a volatile copy-on-write array
 *  for id -> value. A read has no retry loop. */
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

    /** ap.md §1, W5: a path holds fields, elements and class accessors only. The type-info and value accessors serve the
     *  lambda analysis of the prescan (the old core); no statement and no rule of the new core makes them. */
    fun index(a: Accessor): AccessorIdx = when (a) {
        is FieldAccessor -> setAccessorKind(fields.index(a), FIELD_KIND, BASIC_KIND_BITS)
        is ClassStaticAccessor -> setAccessorKind(statics.index(a), STATIC_KIND, BASIC_KIND_BITS)
        ElementAccessor -> ELEMENT_ACCESSOR_IDX
        else -> error("W5: $a is not an accessor of a path")          // a mark, `$`, `[any]`, type info, value
    }

    fun accessor(i: AccessorIdx): Accessor = when {                  // the decode of AccessorInterner.accessor (:70-92)
        i.isFieldAccessor() -> fields.value(i.getAccessorIdx(BASIC_KIND_BITS))
        i.isStaticAccessor() -> statics.value(i.getAccessorIdx(BASIC_KIND_BITS))
        i == ELEMENT_ACCESSOR_IDX -> ElementAccessor
        else -> error("W5: not a path accessor: $i")
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

/** ap.md §2.2: a demand input or a demand step gives a demand result; the layer never goes back to normal. */
infix fun Layer.or(demand: Boolean): Layer = if (demand) Layer.DEMAND else this

/** The constants of one run that the AP operations read (ap.md §4.1, §4.4, §6.1). */
class ApMode(val run1: Boolean, val direction: Direction, val fieldLimit: Int) {
    val restricted: Boolean get() = !run1
    init { require(!run1 || (direction == Direction.FORWARD && fieldLimit >= 1)) }   // run 1 is forward; S12 (d): L >= 1
}

/** ap.md §3.4: a canonical set of concrete marks (sorted ids, no duplicates): the X of `*∖X`, the marks of a TAINT leaf.
 *  ApManager interns it (T6), so equal sets are mostly the same object; equals also compares the content, so a reference
 *  form can make a set without the manager. */
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

// Facts.kt helpers: `fun IntArray.sortedDistinct(): IntArray`; `fun sortedUnion(a: IntArray, b: IntArray): IntArray` and
// `fun sortedSubset(a: IntArray, b: IntArray): Boolean` (a merge walk of two sorted arrays); `fun IntArray.startsWith(p:
// IntArray): Boolean` (the `startsWith` of ap.md §3.4 on arrays); `val EMPTY_PATH = IntArray(0)`.
```

### 3.3 `PathNode`

```kotlin
/** ap.md §7.1: the concrete path of a premise, a position or a demand chain, linked from the root. No `[any]`, `$` or mark
 *  accessor (W4, W5). ADAPT of AccessPath.AccessNode (ap/ifds/access/tree/AccessPath.kt:261): the same (accessor, next)
 *  cell with a cached hash and size. Changes: no `manager` field; ApManager.path interns every node, so equality is
 *  identity; no `addParent`. The old `addParent` (:316) collapses a repeated field (`limitFieldAccess`, :375) and long
 *  element chains (`limitElementAccess`, :354). These are depth bounds; the field limit must be the only one (ap.md §4.4). */
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

### 3.4 `PremiseKey`, `InitialAp`, `PremiseSet`, the zero fact

```kotlin
/** ap.md §7.1: the premise SET of an edge, never empty, interned (equal keys are one object; DD13). One member is the
 *  common case: the InitialAp itself is the key, with no wrapper and no list. Two or more members: a PremiseSet, an ND
 *  edge (no zero member, ap.md §4.6). The layer is not part of the key. */
sealed interface PremiseKey {
    val size: Int
    fun member(k: Int): InitialAp
    val isZero: Boolean                        // the one member is the zero fact
    val nonZeroCount: Int                      // ap.md §4.6: 0 = zero-to-fact ({zero}), 1 = fact-to-fact, >= 2 = ND edge
}

val PremiseKey.members: List<InitialAp> get() = List(size, ::member)          // on a PremiseSet receiver: its array
inline fun PremiseKey.forEachMember(body: (InitialAp) -> Unit) { for (k in 0 until size) body(member(k)) }

/** K6, ap.md §7.2: the conclusions of a premise with the mark `*` (a policy fact, a position answer) are FLOW. Every other
 *  InitialAp gives REACH (a conclusion on the zero base) or TAINT; a PremiseSet gives TAINT only (ap.md §4.6). */
val PremiseKey.isFlow: Boolean get() = this is InitialAp && mark is MarkSlot.Star

/** ap.md §7.1: the premise; also the premise key of one member. ApManager.initial interns it: equality is identity (DD5). */
class InitialAp internal constructor(
    val base: AccessPathBase,
    val path: PathNode?,
    val tail: Tail,
    val exclusion: ExclusionSet,                  // Empty unless STAR; a restricted run can emit a `*/E` demand exclusion (§6.3)
    val mark: MarkSlot,                           // `*` or `T`, never `*∖X` (§2.2)
    @JvmField val id: Int,                        // the intern order: the sort key of a PremiseSet
    @JvmField internal val manager: ApManager,    // Record.reversedAt (Part I §7.8) interns the reversed premise
) : PremiseKey {
    init {
        check(mark !is MarkSlot.Star || mark.excluded.isEmpty)
        check(tail == Tail.STAR || exclusion == ExclusionSet.Empty)
    }
    @JvmField val pathArray: IntArray = path?.toIntArray() ?: EMPTY_PATH
    override val size: Int get() = 1
    override fun member(k: Int): InitialAp = also { check(k == 0) }
    override val isZero: Boolean get() = base == AccessPathBase.Zero
    override val nonZeroCount: Int get() = if (isZero) 0 else 1
    fun toPattern(): Pattern = Pattern(PathFact(base, pathArray.asList(), tail, mark), exclusion)
}

/** ap.md §7.1, §4.6: an ND edge. Two or more members, sorted by the intern id, no duplicates; no member is the zero fact
 *  (the union drops it) and every member has a concrete mark (an input of a conjunction passes the mark gate of its
 *  literal; a member of an E6 summary is satisfied only by a concrete added fact). ApManager.premiseOf interns it. */
class PremiseSet internal constructor(@JvmField val members: Array<InitialAp>) : PremiseKey {
    init {
        check(members.size >= 2)
        check(members.none { it.isZero }) { "ap.md §4.6: a premise set with two or more members has no zero member" }
        check(members.all { it.mark is MarkSlot.Concrete }) { "ap.md §4.6: every member of an ND edge is concrete" }
    }
    override val size: Int get() = members.size
    override fun member(k: Int): InitialAp = members[k]
    override val isZero: Boolean get() = false
    override val nonZeroCount: Int get() = members.size
}

// In ApManager (Part I §5.1):
//   fun premiseOf(members: Collection<InitialAp>): PremiseKey   drops the zero fact (only zero: {zero}); one member: the
//                                                                InitialAp itself; else the interned PremiseSet
//   fun union(a: PremiseKey, b: PremiseKey): PremiseKey          ap.md §4.6: the union of two premise sets, without zero
//   val zero: InitialAp = initial(AccessPathBase.Zero, null, Tail.EXACT, ExclusionSet.Empty, MarkSlot.Concrete(TaintMark.ZERO))
//                                                                the zero fact, also the premise key {zero} (ap.md §2.4)
```

---

## 4. Tries and conclusions (`ap.md` §7.2, §7.5, §8.1)

### 4.1 `TrieNode<P>`, the leaf algebras, the three kinds

```kotlin
/** The leaf payload of a trie node (DD14). `hasAny`: the payload has an `[any]` leaf with a concrete mark (TAINT). */
interface TrieLeaf { val isEmpty: Boolean; val hasAny: Boolean }

/** FLOW: ONE flag. In a normal tree the flag is the leaf `p.*` with the tree exclusion; in a demand tree it is the leaf
 *  `p.[any]`. The mark is `*∖X` of the tree. So a FLOW tree has no `$` leaf and no concrete mark (DD12). */
enum class FlowLeaf : TrieLeaf {
    NONE, LEAF;
    override val isEmpty: Boolean get() = this == NONE
    override val hasAny: Boolean get() = false                // the layer of the tree says `[any]`, not the leaf
}

/** TAINT: the concrete marks of the `$` leaves and of the `[any]` leaves at one node. No `[any]` mark in a normal tree
 *  (W6). Interned by TaintAlgebra (T6): TaintLeaves.EMPTY is the only empty object. */
class TaintLeaves internal constructor(@JvmField val exact: MarkSet, @JvmField val any: MarkSet) : TrieLeaf {
    private val hash = exact.hashCode() * 31 + any.hashCode()
    override val isEmpty: Boolean get() = exact.isEmpty && any.isEmpty
    override val hasAny: Boolean get() = !any.isEmpty
    override fun equals(other: Any?) = this === other || (other is TaintLeaves && hash == other.hash && exact == other.exact && any == other.any)
    override fun hashCode() = hash
    companion object { @JvmField val EMPTY = TaintLeaves(MarkSet.EMPTY, MarkSet.EMPTY) }
}

/** The ONE trie node (DD14). ADAPT of AccessTree.AccessNode (ap/ifds/access/tree/AccessTree.kt:261): the leaf payload
 *  replaces isAbstract, isFinal and deepAccessorExclusion; no `[any]` edge, no `$` child. Immutable. Every child subtree
 *  is non-empty. */
class TrieNode<P : TrieLeaf> internal constructor(
    @JvmField val leaf: P,
    @JvmField val accessors: IntArray?,          // sorted AccessorIdx, as today
    @JvmField val children: Array<TrieNode<P>>?,
    @JvmField val interned: Boolean,
) {
    @JvmField val hash: Long                     // structural (AccessTree.kt:281), with the child accessor
    @JvmField val boundedDepth: Short            // max counted accessors on a path below (§4.5); not in the hash
    @JvmField val hasAny: Boolean                // an `[any]` mark at or below (TAINT): the W6 split
    @JvmField val size: Long                     // nodes, shared subtrees counted again (AccessTree.kt:316-322): the intern policy
    @JvmField internal var allLeaves: P? = null  // the lazy foldAll: the leaf of this node and every leaf below it; a benign race

    init {
        var h = leaf.hashCode().toLong()
        var depth = 0
        var any = leaf.hasAny
        var count = 1L
        if (children != null) for (i in children.indices) {
            val c = children[i]
            count += c.size
            h += (c.hash * 31 + accessors!![i]) shl 5
            val d = c.boundedDepth + if (accessors[i].isCounted()) 1 else 0
            if (d > depth) depth = d
            any = any || c.hasAny
        }
        hash = h
        boundedDepth = minOf(depth, Short.MAX_VALUE.toInt()).toShort()   // saturating, as branch any-field-limit AccessTree.kt:366
        hasAny = any; size = count
    }

    val isEmpty: Boolean get() = leaf.isEmpty && accessors == null
    fun child(a: AccessorIdx): TrieNode<P>? =                          // getNodeByAccessor (AccessTree.kt:385)
        accessors?.binarySearch(a)?.let { if (it >= 0) children!![it] else null }
    override fun hashCode() = hash.toInt()
    override fun equals(other: Any?): Boolean =                        // AccessNode.equals (:326); see §4.5
        this === other || (other is TrieNode<*> && hash == other.hash && leaf == other.leaf &&
            accessors.contentEquals(other.accessors) && children.contentEquals(other.children))
}

typealias FlowNode = TrieNode<FlowLeaf>
typealias TaintNode = TrieNode<TaintLeaves>

/** The algebra of one leaf payload (DD14). The generic algorithms of TrieOps.kt read only these members. */
abstract class LeafAlgebra<P : TrieLeaf> {
    abstract val empty: P
    abstract fun union(a: P, b: P): P
    abstract fun minus(a: P, b: P): P                     // the leaves of a that b does not have
    /** ap.md §8.1, T5: what a leaf `p` covers strictly below its node inside one DEMAND tree (an `[any]` leaf). */
    abstract fun below(p: P): P
    /** ap.md §4.4: the leaves `p` of a cut subtree as one `[any]` leaf at the cut point (the mark stays). */
    abstract fun asAny(p: P): P
    abstract fun intern(p: P): P
    private val leafNodes = ConcurrentHashMap<P, TrieNode<P>>()
    /** One shared leaf node per payload (ADAPT of TreeApManager.create, AccessTree.kt:1784). */
    fun leafNode(p: P): TrieNode<P> = leafNodes.computeIfAbsent(intern(p)) { TrieNode(it, null, null, interned = true) }
    fun node(p: P, accessors: IntArray?, children: Array<TrieNode<P>>?): TrieNode<P> =
        if (accessors == null || accessors.isEmpty()) leafNode(p) else TrieNode(intern(p), accessors, children, interned = false)
}

object FlowAlgebra : LeafAlgebra<FlowLeaf>() {
    override val empty = FlowLeaf.NONE
    override fun union(a: FlowLeaf, b: FlowLeaf) = if (a == FlowLeaf.LEAF || b == FlowLeaf.LEAF) FlowLeaf.LEAF else FlowLeaf.NONE
    override fun minus(a: FlowLeaf, b: FlowLeaf) = if (a == FlowLeaf.LEAF && b == FlowLeaf.NONE) FlowLeaf.LEAF else FlowLeaf.NONE
    override fun below(p: FlowLeaf) = p                    // an `[any]` flag covers every leaf below it (the mark is the same)
    override fun asAny(p: FlowLeaf) = p                    // in the demand tree of the cut, the flag is `[any]`
    override fun intern(p: FlowLeaf) = p
    val LEAF_NODE: FlowNode get() = leafNode(FlowLeaf.LEAF)
}

class TaintAlgebra(private val m: ApManager) : LeafAlgebra<TaintLeaves>() {
    private val table = ConcurrentHashMap<TaintLeaves, TaintLeaves>()
    override val empty = TaintLeaves.EMPTY
    fun leaves(exact: MarkSet, any: MarkSet): TaintLeaves = intern(TaintLeaves(m.intern(exact), m.intern(any)))
    override fun intern(p: TaintLeaves) = if (p.isEmpty) TaintLeaves.EMPTY else table.putIfAbsent(p, p) ?: p
    override fun union(a: TaintLeaves, b: TaintLeaves) = if (a === b) a else leaves(a.exact + b.exact, a.any + b.any)
    override fun minus(a: TaintLeaves, b: TaintLeaves) = leaves(a.exact - b.exact, a.any - b.any)
    override fun below(p: TaintLeaves) = leaves(p.any, p.any)          // `[any]` with T covers the `$` and `[any]` leaves with T below
    override fun asAny(p: TaintLeaves) = leaves(MarkSet.EMPTY, p.exact + p.any)
}
```

The three kinds of `ap.md` §7.2:

```kotlin
/** ap.md §7.2: the conclusions of one edge group at a node. ONE kind (DD12). */
sealed interface Facts { val base: AccessPathBase; val layer: Layer }

/** REACH: the zero fact is at the node (today ZeroToZero). Two objects. */
class Reach private constructor(override val layer: Layer) : Facts {
    override val base: AccessPathBase get() = AccessPathBase.Zero
    companion object {
        @JvmField val NORMAL = Reach(Layer.NORMAL)
        @JvmField val DEMAND = Reach(Layer.DEMAND)
        fun of(layer: Layer): Reach = if (layer == Layer.NORMAL) NORMAL else DEMAND
    }
}

/** FLOW (run 1; a run-1 record with a `*` premise): the flag of a node is `p.*/E` (normal) or `p.[any]` (demand), with the
 *  mark `*∖X`. W2 and W6 hold by the type (no concrete mark, no `$` leaf; the flag of a demand tree IS `[any]`); `init`
 *  checks W1 for the demand layer. ApManager.flowTree is the normalising factory (it maps a demand exclusion to Empty). */
class FlowTree internal constructor(
    override val base: AccessPathBase,
    override val layer: Layer,
    val exclusion: ExclusionSet,
    val markExclusion: MarkSet,
    val root: FlowNode,
) : Facts {
    init { check(layer == Layer.NORMAL || exclusion == ExclusionSet.Empty) { "W1: a demand flag is `[any]`" } }   // O(1)
    internal fun withRoot(r: FlowNode) = FlowTree(base, layer, exclusion, markExclusion, r)
    override fun equals(other: Any?) = this === other || (other is FlowTree && layer == other.layer && base == other.base &&
        exclusion == other.exclusion && markExclusion == other.markExclusion && root == other.root)
    override fun hashCode() = ((root.hashCode() * 31 + base.hashCode()) * 31 + exclusion.hashCode()) * 31 + markExclusion.hashCode() + layer.ordinal
}

/** TAINT: concrete marks only. No `*` leaf, no exclusion, no mark exclusion (by the type); no `[any]` mark in the normal
 *  layer (W6: `init`, O(1) through `TrieNode.hasAny`). */
class TaintTree internal constructor(
    override val base: AccessPathBase,
    override val layer: Layer,
    val root: TaintNode,
) : Facts {
    init { check(layer == Layer.DEMAND || !root.hasAny) { "W6: an `[any]` leaf is in the demand layer" } }
    internal fun withRoot(r: TaintNode) = TaintTree(base, layer, r)
    override fun equals(other: Any?) = this === other || (other is TaintTree && layer == other.layer && base == other.base && root == other.root)
    override fun hashCode() = (root.hashCode() * 31 + base.hashCode()) * 2 + layer.ordinal
}
```

```kotlin
/** ap.md §8.1: the store key of a value without the statement and the premise. Two values with the same group key merge
 *  (T1, T4); two values with different group keys never merge (T3). REACH: the layer. FLOW: the base, the layer, the
 *  exclusion and the mark exclusion. TAINT: the base and the layer. Users: AddedFactStore (Part I §7.5), the identity
 *  test of a summary (analyzer-impl.md `summaryParts`). */
enum class FactsKind { REACH, FLOW, TAINT }
data class GroupKey(val kind: FactsKind, val layer: Layer, val base: AccessPathBase,
                    val exclusion: ExclusionSet = ExclusionSet.Empty, val markExclusion: MarkSet = MarkSet.EMPTY)

val Facts.groupKey: GroupKey get() = when (this) {
    is Reach -> GroupKey(FactsKind.REACH, layer, base)
    is FlowTree -> GroupKey(FactsKind.FLOW, layer, base, exclusion, markExclusion)
    is TaintTree -> GroupKey(FactsKind.TAINT, layer, base)
}
```

Value equality is structural (DD5). The analyzer compares `Facts` by value: the set of the unchanged queue
(`DeltaWorklist`), the inputs of `ConjunctionStore`, the AC4 identity test and the split of a summary delta
(`analyzer-impl.md` §4).

### 4.2 T1 merge, T4 delta and the other generic trie operations

`mergeAdd` and `mergeAddDelta` keep the iterative pair loop of today, without the `[any]` fold. The loop and the two
steps:

```kotlin
// TrieOps.kt. ADAPT of AccessNode.mergeAdd, mergeAddDelta and mergeNodeLoop (AccessTree.kt:815, :854, :912-963). The
// parameter `foldToAny` (:815, :854) and `trimAnyCoveredAndPushChildren` (:965) go (no `[any]` edge): the loop always
// calls `pushSharedChildPairs` (:1005-1029). `mergeAccessors` (:1368) and `mergeAccessorsRaw` (:1388) are copied as they
// are, with the type parameter P: the sorted merge of the children of `a` with (`accessors`, `children`) of `b`; it
// calls `onOtherNode` for a child that only `b` has and `merge` for a shared accessor, and it returns null if `a`
// keeps its children. `getComputedResult` is `get(key) ?: error(...)` (:1851).

/** The key of the pair memo: the identity of both nodes (AccessNodeMergePair, AccessTree.kt:803-813). */
internal class NodePair<P : TrieLeaf>(@JvmField val a: TrieNode<P>, @JvmField val b: TrieNode<P>) {
    private val hash = System.identityHashCode(a) * 31 + System.identityHashCode(b)
    override fun hashCode() = hash
    override fun equals(other: Any?) = other is NodePair<*> && a === other.a && b === other.b
}

internal object Expanding                                                  // NodeExpansionRequested of today

/** The pair loop: the first visit of a pair pushes its shared child pairs; the second visit merges it with `step`, which
 *  reads the results of the child pairs. No recursion, so a wide or deep trie needs no deep call stack. */
@Suppress("UNCHECKED_CAST")
internal inline fun <P : TrieLeaf, T : Any> mergeNodeLoop(a0: TrieNode<P>, b0: TrieNode<P>, same: (TrieNode<P>) -> T,
                                                          step: (TrieNode<P>, TrieNode<P>, Object2ObjectOpenHashMap<NodePair<P>, T>) -> T): T {
    if (a0 === b0) return same(a0)
    val results = Object2ObjectOpenHashMap<NodePair<P>, Any>()
    val stack = ArrayList<NodePair<P>>()
    val initial = NodePair(a0, b0).also { stack += it }
    while (stack.isNotEmpty()) {
        val pair = stack.last()
        if (pair.a === pair.b) { results[pair] = same(pair.a); stack.removeLast(); continue }
        when (results.putIfAbsent(pair, Expanding)) {
            null -> pushSharedChildPairs(pair.a, pair.b, stack)                       // first visit: the child pairs first
            Expanding -> { results[pair] = step(pair.a, pair.b, results as Object2ObjectOpenHashMap<NodePair<P>, T>); stack.removeLast() }
            else -> stack.removeLast()                                                // a shared pair: merged already
        }
    }
    return results[initial] as T
}

internal fun <P : TrieLeaf> pushSharedChildPairs(a: TrieNode<P>, b: TrieNode<P>, stack: MutableList<NodePair<P>>) {
    val x = a.accessors ?: return
    val y = b.accessors ?: return
    var i = 0
    var j = 0
    while (i < x.size && j < y.size) when {
        x[i] < y[j] -> i++
        x[i] > y[j] -> j++
        else -> { stack += NodePair(a.children!![i], b.children!![j]); i++; j++ }
    }
}

fun <P : TrieLeaf> LeafAlgebra<P>.mergeAdd(a: TrieNode<P>, b: TrieNode<P>): TrieNode<P> =
    mergeNodeLoop(a, b, { it }) { x, y, results -> mergeAddStep(x, y, results) }

fun <P : TrieLeaf> LeafAlgebra<P>.mergeAddDelta(a: TrieNode<P>, b: TrieNode<P>): Pair<TrieNode<P>, TrieNode<P>?> =
    mergeNodeLoop(a, b, { it to null }) { x, y, results -> mergeAddDeltaStep(x, y, results) }

/** ADAPT of AccessNode.mergeAddStep (AccessTree.kt:826-852): the leaf union replaces the flags. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.mergeAddStep(
    a: TrieNode<P>, b: TrieNode<P>, results: Object2ObjectOpenHashMap<NodePair<P>, TrieNode<P>>,
): TrieNode<P> {
    val leaf = union(a.leaf, b.leaf)
    val merged = mergeAccessors(a, b.accessors, b.children, onOtherNode = { _, _ -> }) { _, x, y ->
        results.getComputedResult(NodePair(x, y)) }
    if (leaf == a.leaf && merged == null) return a
    return node(leaf, merged?.first ?: a.accessors, merged?.second ?: a.children)
}

/** ADAPT of AccessNode.mergeAddDeltaStep (AccessTree.kt:859-910). */
internal fun <P : TrieLeaf> LeafAlgebra<P>.mergeAddDeltaStep(
    a: TrieNode<P>, b: TrieNode<P>, results: Object2ObjectOpenHashMap<NodePair<P>, Pair<TrieNode<P>, TrieNode<P>?>>,
): Pair<TrieNode<P>, TrieNode<P>?> {
    val leaf = union(a.leaf, b.leaf)                       // was: isAbstract ||, isFinal ||, intersectDeepExclusion
    val leafDelta = minus(b.leaf, a.leaf)                  // was: isAbstractDelta, isFinalDelta, deltaDeepExclusion
    val deltaAccessors = IntArrayList()
    val deltaNodes = ArrayList<TrieNode<P>>()
    val merged = mergeAccessors(a, b.accessors, b.children,
        onOtherNode = { acc, n -> deltaAccessors.add(acc); deltaNodes.add(n) }) { acc, x, y ->
        val (node, delta) = results.getComputedResult(NodePair(x, y))
        if (delta != null) { deltaAccessors.add(acc); deltaNodes.add(delta) }
        node
    }
    if (leaf == a.leaf && merged == null) return a to null
    val delta = node(leafDelta, deltaAccessors.toIntArray(), deltaNodes.toTypedArray()).takeIf { !it.isEmpty }
    return node(leaf, merged?.first ?: a.accessors, merged?.second ?: a.children) to delta
}
```

T1 (`Tree.rule1_mem`): two values with the same key merge by `mergeAdd`. T4: `mergeAddDelta` returns the new part only.
The same rule on two `Facts` of one group key (§4.1), for the stores that merge exactly (no subsumption):

```kotlin
/** T1, T4 on two values of one group key: (the merged value, the delta or null). Users: AddedFactStore.add (Part I §7.5),
 *  ConcurrentVulnerabilityStore.union (Part I §7.12). */
internal fun ApManager.mergeAddDelta(old: Facts, new: Facts): Pair<Facts, Facts?> {
    check(old.groupKey == new.groupKey)                                     // T3: never across keys
    return when (old) {
        is Reach -> old to null                                             // one bit
        is FlowTree -> FlowAlgebra.mergeAddDelta(old.root, (new as FlowTree).root).let { (n, d) -> old.withRoot(n) to d?.let(old::withRoot) }
        is TaintTree -> taintAlg.mergeAddDelta(old.root, (new as TaintTree).root).let { (n, d) -> old.withRoot(n) to d?.let(old::withRoot) }
    }
}
```

The other generic functions of `TrieOps.kt` (extension functions on `LeafAlgebra<P>`; each returns `null` for an empty
node and shares every child that it does not change; a map over a whole subtree has an identity memo for one call, as
`annotateAbstractNodes`, `AccessTree.kt:735`):

| Function | Result | Users | Code |
|---|---|---|---|
| `mergeAdd(a, b)`, `mergeAddDelta(a, b)` | T1, T4 | the groups (§4.3), `Results` (§5.2), `AddedFactStore` (§7.5), `VulnerabilityStore` (§7.12) | above |
| `mapChildren(n, leaf, f)` | `n` with a new leaf and each child `c` at `a` replaced by `f(a, c)` (ADAPT of `transformAccessors`, `AccessTree.kt:1461`) | every map below | below |
| `replaceChild(n, leaf, a, c)`, `withLeaf(n, leaf)` | one child replaced (a null `c` removes it); the leaf of `n` replaced (`n` may be null: a leaf node) | `clean`, `satisfying`, `restrict`, the mark policy | below |
| `mapLeaves(n, f)` | every leaf of the subtree replaced by `f(leaf)` | the gate on a subtree, the mark filter of `satisfying`, `clean` | below |
| `retainChildren(n, pred)` | a node with the empty leaf and only the children whose accessor `pred` accepts | `applyCompiledEdge`, `satisfying`, `restrict`, `clean` | below |
| `foldAll(n)`, `foldLeaves(n, pred)` | `foldAll(n)`: the union of the leaf of `n` and of every leaf in the subtree of `n` (AT OR BELOW `n`; cached in `TrieNode.allLeaves`). `foldLeaves(n, pred)`: the leaf of `n` and `foldAll(c)` of each child `c` whose accessor `pred` accepts | the fold to one `[any]` or `$` leaf (`applyCompiledEdge`), the cut (`foldAll` of the cut child: its own leaf is beyond `L` too), the leaf kinds of a summary (`foldAll(g.root)`: a root leaf `ret.$ (T)` is a kind) | below |
| `prepend(m, path, n)`, `chain(m, path, leaves, tip = null)` | `path ++ n` (`Tree.prependPath`); one leaf per depth on one path and the node `tip` at its end, no other child | every operation that makes a result at a path | below |
| `minusNode(n, k)` | the leaves of `n` not in `k`, walked along `k` (a subtree of `n` off `k` is shared) | `without` (§5.8), `checkMark` | below |
| `subtract(n, s, above, at, below)`, `foldUnder(n, above, below)` | the subsumption of `ap.md` §8.1 and the fold T5 | the groups | §4.3, §4.4 |
| `splitAny(n)` (TAINT) | (the `$` leaves, the `[any]` leaves) | the W6 split of `Results` | below |
| `forEachLeaf(n, prefix, f)`, `forEachLeafPosition(n, f)` | `f(path, leaf)` per node with a leaf; `f(path)` | `leaves`, `emit`, the indexes of the stores | below |
| `graft(g, occurs, r)` | `r` at every node of `g` whose leaf `occurs` holds, MERGED with the grafts below it | `applySummary` (§5.4) | below |
| `filterPath(m, n, may)` | the paths that the type filter accepts | `filter` | §5.5 |
| `cleanSpine(n, p, reach, d, atNode, inside)` | the spine walk of a cleaner | `clean`, both kinds | §5.6 |
| `FieldLimitCut(alg, m).keep(n, L)` | (the paths within `L`, the `[any]` leaves at the cut points) | `limit`, both kinds | §5.7 |
| `TrieInterner.intern` (`internBottomUp`), `TrieNode.boundedDepth` | T6; the counted depth below a node | the stores; `limit`, the W3 assert | §4.5, §4.1 |

NO OTHER DEPTH BOUND. Today's node operations also collapse paths: `addParent` folds a repeated field
(`addParentFieldAccess` → `limitFieldAccess`, `AccessTree.kt:625-639`, `:1468-1496`), folds a chain of more than
`SUBSEQUENT_ARRAY_ELEMENTS_LIMIT = 2` elements (`limitElementAccess`, `:599-615`, `:1635`), refuses a parent above a class
accessor (`containsStatic`, `:273`, `:436`), and `concatToLeafAbstractNodes` applies the first two to the caller delta
(`:1291`, `:1299`). None of them is ported: `prepend`, `chain`, `graft` and every map build exactly the paths of the
spec. The field limit `L` (`ap.md` §4.4, Part I §5.7) is the only depth bound, as for `PathNode` (§3.3).

```kotlin
// TrieOps.kt: the code of the rows above.

/** ADAPT of transformAccessors (AccessTree.kt:1461-1466, :1671-1710): `f` maps each child (null drops it); an unchanged
 *  child list and leaf give `n` itself. */
internal inline fun <P : TrieLeaf> LeafAlgebra<P>.mapChildren(n: TrieNode<P>, leaf: P, f: (AccessorIdx, TrieNode<P>) -> TrieNode<P>?): TrieNode<P>? {
    val acc = n.accessors ?: return withLeaf(n, leaf)
    val kids = n.children!!
    var changed = false
    val outAcc = IntArrayList(acc.size)
    val outKids = ArrayList<TrieNode<P>>(acc.size)
    for (i in acc.indices) {
        val c = f(acc[i], kids[i])
        if (c !== kids[i]) changed = true
        if (c != null) { outAcc.add(acc[i]); outKids.add(c) }
    }
    if (!changed) return withLeaf(n, leaf)
    return node(leaf, outAcc.toIntArray(), outKids.toTypedArray()).takeIf { !it.isEmpty }
}

internal fun <P : TrieLeaf> LeafAlgebra<P>.withLeaf(n: TrieNode<P>?, leaf: P): TrieNode<P>? = when {
    n == null -> if (leaf.isEmpty) null else leafNode(leaf)
    leaf == n.leaf -> n
    else -> node(leaf, n.accessors, n.children).takeIf { !it.isEmpty }
}

/** The child at `a` replaced by `c` (inserted at its sorted place if `n` has no child `a`; removed if `c` is null), and the
 *  leaf replaced by `leaf`. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.replaceChild(n: TrieNode<P>?, leaf: P, a: AccessorIdx, c: TrieNode<P>?): TrieNode<P>? {
    val old = n?.child(a)
    if (old === c) return withLeaf(n, leaf)                                       // the child does not change
    val outAcc = IntArrayList()
    val outKids = ArrayList<TrieNode<P>>()
    var put = c == null
    n?.accessors?.forEachIndexed { i, x ->
        if (!put && x > a) { outAcc.add(a); outKids.add(c!!); put = true }       // insert before the first larger accessor
        if (x == a) { if (c != null) { outAcc.add(a); outKids.add(c) }; put = true }   // replace or remove
        else { outAcc.add(x); outKids.add(n.children!![i]) }
    }
    if (!put) { outAcc.add(a); outKids.add(c!!) }
    return node(leaf, outAcc.toIntArray(), outKids.toTypedArray()).takeIf { !it.isEmpty }
}

internal inline fun <P : TrieLeaf> LeafAlgebra<P>.retainChildren(n: TrieNode<P>, pred: (AccessorIdx) -> Boolean): TrieNode<P>? =
    mapChildren(n, empty) { a, c -> if (pred(a)) c else null }

fun <P : TrieLeaf> LeafAlgebra<P>.mapLeaves(n: TrieNode<P>, f: (P) -> P): TrieNode<P>? = mapLeavesMemo(n, f, IdentityHashMap())

private fun <P : TrieLeaf> LeafAlgebra<P>.mapLeavesMemo(n: TrieNode<P>, f: (P) -> P,
                                                        memo: IdentityHashMap<TrieNode<P>, Optional<TrieNode<P>>>): TrieNode<P>? {
    memo[n]?.let { return it.orElse(null) }
    val r = mapChildren(n, intern(f(n.leaf))) { _, c -> mapLeavesMemo(c, f, memo) }
    memo[n] = Optional.ofNullable(r)
    return r
}

/** Cached per node: the result is a function of the node (immutable), so the race of two writers is benign. */
fun <P : TrieLeaf> LeafAlgebra<P>.foldAll(n: TrieNode<P>): P {
    n.allLeaves?.let { return it }
    var acc = n.leaf
    n.children?.forEach { acc = union(acc, foldAll(it)) }
    return acc.also { n.allLeaves = it }
}

internal inline fun <P : TrieLeaf> LeafAlgebra<P>.foldLeaves(n: TrieNode<P>, pred: (AccessorIdx) -> Boolean): P {
    var acc = n.leaf
    n.accessors?.forEachIndexed { i, a -> if (pred(a)) acc = union(acc, foldAll(n.children!![i])) }
    return acc
}

/** `path ++ n`: one node with the empty leaf per accessor of `path` (Tree.prependPath). `m` is only passed on: one
 *  signature for every helper that makes a result at a path (`chain` does not read it either). */
fun <P : TrieLeaf> LeafAlgebra<P>.prepend(m: ApManager, path: PathNode?, n: TrieNode<P>): TrieNode<P> =
    if (path == null) n else node(empty, intArrayOf(path.accessor), arrayOf(prepend(m, path.next, n)))

/** One leaf per depth on `path` (`spine[d]` at depth d; a missing entry is empty) and the node `tip` at the end of the
 *  path (its leaf joins `spine[path.size]`). `spine` is shorter than `path.size + 1` when the walk that made it stopped
 *  early; then `tip` is null. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.chain(@Suppress("UNUSED_PARAMETER") m: ApManager, path: IntArray, spine: List<P>,
                                                 tip: TrieNode<P>? = null): TrieNode<P>? {
    check(spine.size <= path.size + 1)
    var r = if (spine.size == path.size + 1) withLeaf(tip, union(tip?.leaf ?: empty, spine[path.size])) else tip
    for (d in path.indices.reversed()) r = replaceChild(null, spine.getOrNull(d) ?: empty, path[d], r)
    return r
}

/** The leaves of `n` that `k` does not have, at the same path; `k` comes from `n` (a part), so the walk follows `k` and
 *  shares every child of `n` off `k`. */
fun <P : TrieLeaf> LeafAlgebra<P>.minusNode(n: TrieNode<P>, k: TrieNode<P>): TrieNode<P>? {
    if (n === k) return null
    return mapChildren(n, minus(n.leaf, k.leaf)) { a, c -> val kc = k.child(a); if (kc == null) c else minusNode(c, kc) }
}

/** TAINT, W6: (the `$` leaves, the `[any]` leaves) of one tree. */
internal fun TaintAlgebra.splitAny(n: TaintNode): Pair<TaintNode?, TaintNode?> =
    if (!n.hasAny) n to null
    else mapLeaves(n) { leaves(it.exact, MarkSet.EMPTY) } to mapLeaves(n) { leaves(MarkSet.EMPTY, it.any) }

/** `f(path, leaf)` for each node with a non-empty leaf; a shared subtree is visited once per path (each path is a leaf). */
fun <P : TrieLeaf> LeafAlgebra<P>.forEachLeaf(n: TrieNode<P>, prefix: IntArray, f: (IntArray, P) -> Unit) {
    if (!n.leaf.isEmpty) f(prefix, n.leaf)
    n.accessors?.forEachIndexed { i, a -> forEachLeaf(n.children!![i], prefix + a, f) }
}

fun <P : TrieLeaf> LeafAlgebra<P>.forEachLeafPosition(n: TrieNode<P>, f: (IntArray) -> Unit) = forEachLeaf(n, EMPTY_PATH) { p, _ -> f(p) }

/** The leaf positions of one Facts: `(Zero, [])` for REACH. Users: the indexes of AddedFactStore and PersistentRecordStore. */
fun ApManager.forEachLeafPosition(f: Facts, action: (AccessPathBase, IntArray) -> Unit) = when (f) {
    is Reach -> action(AccessPathBase.Zero, EMPTY_PATH)
    is FlowTree -> FlowAlgebra.forEachLeafPosition(f.root) { action(f.base, it) }
    is TaintTree -> taintAlg.forEachLeafPosition(f.root) { action(f.base, it) }
}

/** `r` (the result of one summary leaf kind, computed at the empty path, Part I §5.4) at every node of `g` whose leaf
 *  `occurs` holds, and no other leaf of `g`. ADAPT of concatToLeafAbstractNodes (AccessTree.kt:1281-1326). At an
 *  occurring node the result is the MERGE of `r` and the grafts below it, as today (:1321-1324: `bulkMergeAddAccessors` of
 *  the nested results, then `mergeAdd(concatNode)`). So an occurrence below an occurring node keeps both: the child of `r`
 *  from the graft above and `r` grafted again (a "replace" loses the leaves below: a false negative). A node of `g` with
 *  no occurrence at or below it gives null. The identity memo over `g` keeps the shared subtrees of `g` shared: the
 *  result depends only on the node of `g`. The ADAPT drops `filterTypes` (:1290; the AP has no summary-side filter,
 *  ap.md §4.8), `limitElementAccess` (:1291), `filterDeepExclusion` (:1292), `limitFieldAccess` (:1299; `L` is the only
 *  depth bound) and the `isFinal` leaf of `g` (:1321; one LeafKind per leaf kind, Part I §5.4). */
fun <G : TrieLeaf, R : TrieLeaf> LeafAlgebra<R>.graft(g: TrieNode<G>, occurs: (G) -> Boolean, r: TrieNode<R>): TrieNode<R>? =
    graftMemo(g, occurs, r, IdentityHashMap())

private fun <G : TrieLeaf, R : TrieLeaf> LeafAlgebra<R>.graftMemo(g: TrieNode<G>, occurs: (G) -> Boolean, r: TrieNode<R>,
                                                                  memo: IdentityHashMap<TrieNode<G>, Optional<TrieNode<R>>>): TrieNode<R>? {
    memo[g]?.let { return it.orElse(null) }
    val acc = IntArrayList()
    val kids = ArrayList<TrieNode<R>>()
    g.accessors?.forEachIndexed { i, a -> graftMemo(g.children!![i], occurs, r, memo)?.let { acc.add(a); kids.add(it) } }
    val below = node(empty, acc.toIntArray(), kids.toTypedArray()).takeIf { !it.isEmpty }   // the grafts below; no leaf of g
    val res = when {
        !occurs(g.leaf) -> below
        below == null -> r
        else -> mergeAdd(r, below)                                                // :1324
    }
    memo[g] = Optional.ofNullable(res)
    return res
}
```

Example (the merge): the summary `g = FlowTree(ret, {[]: LEAF, [f]: LEAF})` (`ret.*` and `ret.f.*`) and the result
`r = {[]: $ (T), [f]: $ (T)}` of the caller part `{j.$ (T), j.f.$ (T)}`. The graft at `[f]` gives `r` there
(`ret.f.$`, `ret.f.f.$`); the occurrence at `[]` gives `r` (`ret.$`, `ret.f.$`). The merge at `[]` keeps all three
leaves `ret.$ (T)`, `ret.f.$ (T)`, `ret.f.f.$ (T)`, the per-leaf union of `ap.md` §4.3. A replace at `[]` keeps only
`r` and loses `ret.f.f.$ (T)`.

### 4.3 The groups: T1, T2, T2', T3, T5 and the subsumption of `ap.md` §8.1

```kotlin
/** ap.md §8.1 subsumption, generic. `at(s)`: what a stored leaf `s` covers at its own node; `below(s)`: what it covers
 *  strictly below (an `[any]` leaf). The result is the part of `n` that no stored leaf covers. One layer only. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.subtract(
    n: TrieNode<P>, s: TrieNode<P>?, above: P, at: (P) -> P, below: (P) -> P,
): TrieNode<P>? {
    if (s == null && above.isEmpty) return n                                        // nothing covers below: share
    val cover = if (s == null) above else union(above, at(s.leaf))
    val next = if (s == null) above else union(above, below(s.leaf))
    return mapChildren(n, minus(n.leaf, cover)) { a, c -> subtract(c, s?.child(a), next, at, below) }
}

/** FLOW trees of one (statement, premise, base): per layer a few trees with distinct (exclusion, mark exclusion). T1,
 *  T2 (normal), T2', T3, T4, T5 (demand), the subsumption of ap.md §8.1. Single writer. REPLACE of
 *  EdgeNonUniverseExclusionMergingStorage (ap/ifds/access/tree/MethodEdgesInitialToFinalTreeApSet.kt:75), which unions
 *  exclusions across edges (:95): T3 forbids it (Subsume.union_loses_pairs). */
class FlowGroup(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
    private val trees = arrayOf(ArrayList<FlowTree>(1), ArrayList<FlowTree>(1))           // NORMAL, DEMAND: T3
    fun all(): Sequence<FlowTree> = trees[0].asSequence() + trees[1].asSequence()

    /** Returns the delta (T4) or null if `t` adds nothing. */
    fun add(t: FlowTree): FlowTree? {
        val list = trees[t.layer.ordinal]
        val i = list.indexOfFirst { it.exclusion == t.exclusion && it.markExclusion == t.markExclusion }
        if (i >= 0) {                                                                     // T1: the same key
            // §8.1 FIRST, against every tree of the layer, the same-key tree included: a leaf that the stored tree has, or
            // that one of its `[any]` leaves absorbed (T5), is not new. Without it an absorbed leaf is a delta on every
            // arrival, and a loop never empties the worklist.
            val rest = subtractSubsumed(t, list) ?: return null
            val (merged, d) = FlowAlgebra.mergeAddDelta(list[i].root, rest.root)
            if (d == null) return null
            val kept = if (t.layer == Layer.DEMAND) FlowAlgebra.foldUnder(merged, FlowLeaf.NONE, FlowAlgebra::below) ?: merged else merged
            list[i] = list[i].withRoot(interner.internIfRequired(kept))                   // T5 on the stored tree (Part I §4.4)
            return m.flowTree(t.base, t.layer, t.exclusion, t.markExclusion, d)
        }
        val k = list.indexOfFirst { it.root == t.root &&                                  // EQUAL content (Tree.rule2_den)
            (it.markExclusion == t.markExclusion || it.exclusion == t.exclusion) }
        if (k >= 0) {                                                                     // T2 / T2': intersect, never union
            val s = list[k]
            val merged = m.flowTree(t.base, t.layer, s.exclusion.intersect(t.exclusion), s.markExclusion.intersect(t.markExclusion), s.root)
            if (merged.exclusion == s.exclusion && merged.markExclusion == s.markExclusion) return null   // s covers t
            list.removeAt(k)
            return add(merged)                         // T4 exception: the WHOLE merged tree (or its delta to a tree with that key)
        }
        val fresh = subtractSubsumed(t, list) ?: return null                               // §8.1
        list += fresh.withRoot(interner.internIfRequired(fresh.root))
        return fresh
    }

    /** §8.1 for FLOW (Subsume.subsumesB, markSubsB): a stored flag covers a flag of `t` at its node if its mark exclusion
     *  is a subset (`*∖Xs` over `*∖Xn`) and, for `*` leaves, its exclusion is a subset (`*/Es` over `*/En`); a demand flag
     *  (`[any]`) also covers every flag below it. */
    private fun subtractSubsumed(t: FlowTree, others: List<FlowTree>): FlowTree? {
        var root: FlowNode = t.root
        for (s in others) {
            val marks = s.markExclusion.isSubsetOf(t.markExclusion)
            val atOk = marks && (t.layer == Layer.DEMAND || s.exclusion.isSubsetOf(t.exclusion))
            val belowOk = marks && t.layer == Layer.DEMAND
            root = FlowAlgebra.subtract(root, s.root, FlowLeaf.NONE,
                at = { if (atOk) it else FlowLeaf.NONE }, below = { if (belowOk) it else FlowLeaf.NONE }) ?: return null
        }
        return if (root === t.root) t else t.withRoot(root)
    }
}

/** TAINT trees of one (statement, premise key, base): ONE tree per layer (ap.md §8.1). T1, T4, T5 (demand), and the
 *  subsumption of an `[any]` leaf with the mark T over the leaves with T at or below it. Single writer. */
class TaintGroup(private val m: ApManager, private val interner: TrieInterner<TaintLeaves>) {
    private val trees = arrayOfNulls<TaintTree>(2)
    fun all(): Sequence<TaintTree> = trees.asSequence().filterNotNull()

    fun add(t: TaintTree): TaintTree? {
        val alg = m.taintAlg
        val s = trees[t.layer.ordinal] ?: return t.also { trees[t.layer.ordinal] = it.withRoot(interner.internIfRequired(it.root)) }
        val rest = alg.subtract(t.root, s.root, TaintLeaves.EMPTY,
            at = { alg.leaves(it.exact + it.any, it.any) }, below = alg::below) ?: return null      // `[any]` T covers `$` T at its node
        val (merged, d) = alg.mergeAddDelta(s.root, rest)
        if (d == null) return null
        val kept = if (t.layer == Layer.DEMAND && d.hasAny) alg.foldUnder(merged, TaintLeaves.EMPTY, alg::below) ?: merged else merged
        trees[t.layer.ordinal] = s.withRoot(interner.internIfRequired(kept))
        return m.taintTree(t.base, t.layer, d)
    }
}

/** The conclusions of ONE premise key, every base and kind, with the rules above. REACH: one bit per layer. Users:
 *  MethodEdgeStore (one per statement and premise key), RunSummaryStore, PersistentRecordStore. NdSummaryJoin keeps
 *  TaintGroups only (an ND conclusion is TAINT). */
class ConclusionGroup(private val m: ApManager, private val interners: StoreInterners) {
    private val reach = BooleanArray(2)
    private val flow = HashMap<AccessPathBase, FlowGroup>(2)
    private val taint = HashMap<AccessPathBase, TaintGroup>(2)

    fun add(f: Facts): Facts? = when (f) {
        is Reach -> if (reach[f.layer.ordinal]) null else f.also { reach[f.layer.ordinal] = true }
        is FlowTree -> flow.getOrPut(f.base) { FlowGroup(m, interners.flow) }.add(f)
        is TaintTree -> taint.getOrPut(f.base) { TaintGroup(m, interners.taint) }.add(f)
    }

    fun all(): Sequence<Facts> = Layer.entries.asSequence().filter { reach[it.ordinal] }.map(Reach::of) +
        flow.values.asSequence().flatMap { it.all() } + taint.values.asSequence().flatMap { it.all() }
}

/** The trie interners of one store, one per kind (DD5); each table is soft (Part I §4.5). ApManager.newInterners makes it. */
class StoreInterners(refs: SoftReferenceManager, cancellation: Cancellation) {
    val flow = TrieInterner<FlowLeaf>(refs, cancellation)
    val taint = TrieInterner<TaintLeaves>(refs, cancellation)
}
```

The subscriptions and the links do not use subsumption (`analyzer-core.md` §5.3): `AddedFactStore` and `RequestStore`
deduplicate exactly (§7.5, §7.9).

### 4.4 T5: the fold under `[any]` (generic)

```kotlin
/** T5 (ap.md §7.2): inside ONE demand tree, an `[any]` leaf at p absorbs the leaves strictly below p that `below` covers
 *  (FLOW: every flag; TAINT: the leaves with its marks). The denotation does not change (argued, ap.md §11.2). The groups
 *  apply it to the STORED tree after the delta is computed, so a fold never hides a new leaf from the delta. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.foldUnder(n: TrieNode<P>, above: P, below: (P) -> P): TrieNode<P>? {
    if (above.isEmpty && n.accessors == null) return n                              // a leaf node with nothing above it
    val next = union(above, below(n.leaf))
    return mapChildren(n, minus(n.leaf, above)) { _, c -> foldUnder(c, next, below) }
}
```

T5 is optional ("may", `ap.md` §7.2). Its cost is one walk of the stored trie, so a group applies it only when the delta
has an absorbing leaf: every FLOW demand delta (each flag is an `[any]` leaf), a TAINT demand delta with an `[any]` mark
(`hasAny`).

### 4.5 T6 interning, `boundedDepth`, equality across interners

```kotlin
/** T6, ap.md §7.5: bottom-up hash-consing. ADAPT of AccessTreeInterner (ap/ifds/access/tree/AccessTreeInterner.kt:8), of
 *  AccessTreeSoftInterner (AccessTreeSoftInterner.kt:7) and of AccessNode.internNodes (AccessTree.kt:1125-1172).
 *  THE TABLE IS A CACHE behind a managed soft reference, as today (AccessTreeSoftInterner.kt:18-23, TreeApManager.kt:39):
 *  `refs` is the SoftReferenceManager of the analysis (ApManager.softRefs, Part I §5.1). The first stage of the memory
 *  guard clears it (util/MemoryManager.kt:62-76), and the next intern makes a new table. This is exact: an interned node
 *  stays valid and equality is structural (DD5); only the sharing with later equal nodes is lost. While the guard keeps
 *  the manager disabled (`createRef` gives null), the table lives for one intern call, as today. Not thread-safe: one per
 *  store and kind (owner-local, Part I §7.1; DD5). */
class TrieInterner<P : TrieLeaf>(private val refs: SoftReferenceManager, private val cancellation: Cancellation) {
    private class Table<P : TrieLeaf> {
        private val buckets = Long2ObjectOpenHashMap<Object2ObjectOpenCustomHashMap<TrieNode<P>, TrieNode<P>>>()
        fun intern(n: TrieNode<P>): TrieNode<P> =                                     // AccessTreeInterner.intern (:46-52)
            buckets.computeIfAbsent(n.hash) { Object2ObjectOpenCustomHashMap<TrieNode<P>, TrieNode<P>>(InternStrategy) }
                .putIfAbsent(n, n) ?: n
    }

    private var cache: Reference<Table<P>>? = null
    private var operationsBeforeIntern = INTERN_RATE

    private fun table(): Table<P> = cache?.get() ?: Table<P>().also { cache = refs.createRef(it) }   // AccessTreeSoftInterner.kt:18-23

    /** A node with `interned = true` (this store or another one made it) stays as it is (AccessTree.kt:1134, :1157-1161). */
    fun intern(n: TrieNode<P>): TrieNode<P> = if (n.interned) n else internBottomUp(n, table(), IdentityHashMap())

    /** Bottom-up: the children first, then a COPY of the node with the interned children and `interned = true` (the flag is
     *  a constructor val: markInterned, AccessTree.kt:1174-1182). `memo` is the identity memo of one call, so a shared
     *  subtree is walked once. The recursion depth is the trie depth: W3 bounds it (at most L counted accessors and the
     *  uncounted class accessor), so the explicit stack of :1136-1169 is not needed. */
    private fun internBottomUp(n: TrieNode<P>, t: Table<P>, memo: IdentityHashMap<TrieNode<P>, TrieNode<P>>): TrieNode<P> {
        if (n.interned) return n
        memo[n]?.let { return it }
        cancellation.checkpoint()
        val kids = n.children
        var out = kids                                                     // copied only when a child changes
        if (kids != null) for (i in kids.indices) {
            val c = internBottomUp(kids[i], t, memo)
            if (c !== kids[i]) { if (out === kids) out = kids.copyOf(); out!![i] = c }
        }
        return t.intern(TrieNode(n.leaf, n.accessors, out, interned = true)).also { memo[n] = it }
    }

    /** THE POLICY, a deliberate difference to today: a large trie at once (as TreeSetWithCompression.internIfRequired,
     *  ap/ifds/access/tree/TreeSetWithCompression.kt:14-17), else the trie of one add in INTERN_RATE when it is not small.
     *  Today the same tick re-interns EVERY trie of the store (`intern(idx)`, `internImpl`, :19-29, :32-55). Reason: each
     *  group stores its trie at the place of its add (a FLOW list, a TAINT array, a map value of NdSummaryJoin or
     *  AddedFactStore), so the policy acts on the trie that the add stores, with no enumeration of the store. A later
     *  intern of the same trie walks only its new nodes (an interned subtree keeps its flag). The cost: a trie of a store
     *  with few adds is shared only by the operations (they share every unchanged subtree, §4.2), not by the table. The
     *  groups call it on every stored trie. */
    fun internIfRequired(n: TrieNode<P>): TrieNode<P> = when {
        n.size >= SIZE_TO_FORCE_INTERN -> intern(n)
        --operationsBeforeIntern > 0 || n.size < MIN_SIZE_TO_INTERN -> n
        else -> { operationsBeforeIntern = INTERN_RATE; intern(n) }
    }

    companion object { const val MIN_SIZE_TO_INTERN = 100L; const val SIZE_TO_FORCE_INTERN = 100_000L; const val INTERN_RATE = 100 }
}

/** AccessTreeInterner.InternStrategy (AccessTreeInterner.kt:9-42): the hash, the leaf by `==` (a FlowLeaf is an enum, a
 *  TaintLeaves is interned by the one ApManager), the accessors by content, the children by IDENTITY (bottom-up: equal
 *  children are one object in one table). */
private object InternStrategy : Hash.Strategy<TrieNode<*>> {
    override fun hashCode(o: TrieNode<*>?): Int = o?.hashCode() ?: 0
    override fun equals(a: TrieNode<*>?, b: TrieNode<*>?): Boolean {
        if (a === b) return true
        if (a == null || b == null || a.hash != b.hash || a.leaf != b.leaf) return false
        if (!a.accessors.contentEquals(b.accessors)) return false
        val x = a.children ?: return b.children == null
        val y = b.children ?: return false
        return x.size == y.size && x.indices.all { x[it] === y[it] }
    }
}
```

`TrieNode.size` (§4.1) is the node count with shared subtrees counted again, as `AccessNode.size`
(`AccessTree.kt:316-322`). `boundedDepth` is the number of counted accessors on the longest path below a node. It is
part of the node and not of the hash (`ap.md` §7.5). `limit` reads it: a trie with `root.boundedDepth <= L` needs no
walk (§5.7), and `MethodEdgeStore.add` asserts W3 with it (§7.3).

EQUALITY ACROSS INTERNERS (DD5). Each store has its own interners, so two equal nodes of two stores can be two objects.
A callee publication (from the callee `RunSummaryStore`) meets a caller subscription (from the caller `AddedFactStore`)
in `satisfying`, `applySummary` and the groups of the caller. So no operation reads identity as equality:

| Place | Why it is correct with two interners |
|---|---|
| `TrieNode.hash`, `equals` | the leaf by its value hash and `==` (an enum, or a `TaintLeaves` with a content hash), the children by their structural hash and `equals`: the same for equal content in every store; `this === other` is only a fast path |
| `TrieInterner` | it compares children by identity, which is exact inside one table (bottom-up: equal children are one object there). A node that another store interned, or that a cleared table of this store interned, stays as it is: it is immutable and equality is structural; it only is not shared with the equal nodes of the current table |
| `mergeNodeLoop` | identity pairs (`NodePair`) are only a memo and `a === b` only a shortcut: two equal nodes of two stores take the full merge, with the same result |
| T2 (§4.3), `minusNode` (§5.8), `Facts.equals` (§4.1) | they use `==`, so they also work for a trie that another store made |

### 4.6 `walkPath`: the one path walk

```kotlin
/** The walk of `path` from `root` (ap.md §7.3 step 1): `onPrefix(d, node)` for each proper prefix node (depth d; the rest of
 *  the path starts at path[d]); the result is the node of the path, or null if the trie has no such node. ONE walk for
 *  every trie of Part I. */
inline fun <N : Any> walkPath(root: N, path: IntArray, child: (N, AccessorIdx) -> N?, onPrefix: (Int, N) -> Unit = { _, _ -> }): N? {
    var n = root
    for (d in path.indices) {
        onPrefix(d, n)
        n = child(n, path[d]) ?: return null
    }
    return n
}

inline fun <P : TrieLeaf> TrieNode<P>.walk(path: IntArray, onPrefix: (Int, TrieNode<P>) -> Unit = { _, _ -> }): TrieNode<P>? =
    walkPath(this, path, { n, a -> n.child(a) }, onPrefix)
```

| User | The prefix nodes | The node of the path |
|---|---|---|
| `applyCompiledEdge` (§5.3) | the case `above` | the subtree U of the case `below` |
| `satisfying` (§5.4) | `inside`: the leaves above `j` | `applicable`: the subtree at `j`; `inside`: the leaves at `j` |
| `checkMark` (§5.8) | the leaves above the pattern | the leaves at and below the pattern |
| `restrict`, `emit` (§5.9) | the moved `[any]` marks; the emissions above `D-c` | the node of `D-p`; the meet and the facts below `D-c` |
| `PathTrie` (§7.2) | `lookupPrefixes` | `find` (`lookupExtensions`, `around`) |

`clean` (§5.6) does not use `walkPath`: it rebuilds the spine of `x.p` with its own recursion (`cleanSpine`).

---

## 5. `ApManager` and `ApOps` (`ap.md` §4, §6.3–§6.5, §7.3, §7.4, §9.1)

### 5.1 `ApManager`

```kotlin
/** The interners and the factories of the AP. One per analysis (analyzer-core.md §2). Thread-safe (O4): every shared table is
 *  a ConcurrentHashMap (lock-free reads that are correct under the JMM) or the copy-on-write arrays of Part I §3.1. No
 *  ConcurrentReadSafe map. Trie hash-consing is owner-local (Part I §4.5, DD5), so no node table is shared, and no run leaks
 *  its tries into the next run. The trie tables of the stores are soft: `softRefs` is a SoftReferenceManager of the
 *  RefManager that the memory guard of every run reads (REUSE, util/RefManager.kt:10-11), so the guard clears them, as
 *  today's "Tree" manager (TreeApManager.kt:39). The analysis passes the RefManager of its memory guard
 *  (`SharedObjects.refManager`, analyzer-impl.md §3.1, made in `JIRBidiAnalysis`, §8.1); the default serves the tests.
 *  The tables of ApManager itself stay strong: a store key compares their objects by identity (DD5). */
class ApManager(val cancellation: Cancellation, refManager: RefManager = RefManager()) {
    val softRefs: SoftReferenceManager = refManager.softRefManager("bidi")
    val accessors = AccessorTable()
    val marks = MarkTable()
    val flowAlg: FlowAlgebra get() = FlowAlgebra
    val taintAlg = TaintAlgebra(this)                                              // interns TaintLeaves (T6)

    private val markSets = ConcurrentHashMap<MarkSet, MarkSet>()
    private val exclusions = ConcurrentHashMap<ExclusionSet, ExclusionSet>()
    private val paths = ConcurrentHashMap<PathNode, PathNode>()
    private val initials = ConcurrentHashMap<InitialKey, InitialAp>()
    private val premiseSets = ConcurrentHashMap<List<InitialAp>, PremiseSet>()
    private val nextId = AtomicInteger()
    private data class InitialKey(val base: AccessPathBase, val path: PathNode?, val tail: Tail, val exclusion: ExclusionSet, val mark: MarkSlot)

    fun intern(s: MarkSet): MarkSet = if (s.isEmpty) MarkSet.EMPTY else markSets.putIfAbsent(s, s) ?: s
    fun intern(e: ExclusionSet): ExclusionSet = if (e == ExclusionSet.Empty) e else exclusions.putIfAbsent(e, e) ?: e
    fun markSetOf(t: TaintMark): MarkSet = intern(MarkSet(intArrayOf(t.id)))
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

    /** ap.md §7.1, §4.6, DD13. The zero fact adds no condition (it is at every node that an edge reaches), so it is
     *  dropped; the result is {zero} only if every member is the zero fact. One member: the InitialAp itself; two or more:
     *  the interned PremiseSet (an ND edge). */
    fun premiseOf(members: Collection<InitialAp>): PremiseKey {
        check(members.isNotEmpty()) { "a premise set is never empty" }
        val sorted = members.filter { !it.isZero }.distinct().sortedBy { it.id }
        return when (sorted.size) {
            0 -> zero                                                                // every member is the zero fact
            1 -> sorted[0]                                                           // {zero, i} is {i}
            else -> premiseSets.computeIfAbsent(sorted) { PremiseSet(it.toTypedArray()) }
        }
    }

    /** ap.md §4.6: the union of two premise sets without the zero fact (a conjunction result, a conjunctive sink, the caller
     *  edges of E6). {zero} ∪ {zero} = {zero}; {zero} ∪ {i} = {i}; {i} ∪ {k} = {i, k}. */
    fun union(a: PremiseKey, b: PremiseKey): PremiseKey = if (a === b) a else premiseOf(a.members + b.members)

    val zero: InitialAp = initial(AccessPathBase.Zero, null, Tail.EXACT, ExclusionSet.Empty, MarkSlot.Concrete(TaintMark.ZERO))

    /** The canonical FLOW tree: a demand flag is `[any]`, so its exclusion is Empty (W1, W2). */
    fun flowTree(base: AccessPathBase, layer: Layer, exclusion: ExclusionSet, mx: MarkSet, root: FlowNode): FlowTree {
        check(!root.isEmpty)
        return FlowTree(base, layer, if (layer == Layer.DEMAND) ExclusionSet.Empty else intern(exclusion), intern(mx), root)
    }

    fun taintTree(base: AccessPathBase, layer: Layer, root: TaintNode): TaintTree {
        check(!root.isEmpty)
        return TaintTree(base, layer, root)                                   // the constructor checks W6
    }

    fun taintLeaves(exact: MarkSet, any: MarkSet): TaintLeaves = taintAlg.leaves(exact, any)
    fun newInterners(): StoreInterners = StoreInterners(softRefs, cancellation)
}
```

The one-leaf `Facts` of a `PathFact`, through the normal form of `ap.md` §4.1 step 6. Users: `targetTree` (§5.8) and
`Record.reversedAt` (§7.8):

```kotlin
/** TrieOps.kt. REACH on the zero base, FLOW for an abstract mark, TAINT for a concrete mark; W2 and W6 by `normalize`. */
fun ApManager.factsOf(f: PathFact, exclusion: ExclusionSet, layer: Layer): Facts {
    val n = normalize(f, exclusion, layer == Layer.DEMAND)                         // ap.md §4.1 step 6 (Part I §6)
    val l = if (n.demand) Layer.DEMAND else Layer.NORMAL
    val p = path(n.fact.path)
    return when (val mk = n.fact.mark) {
        is MarkSlot.Star -> {
            check(n.fact.tail != Tail.EXACT) { "S8: a `$` leaf has a concrete mark" }
            flowTree(f.base, l, n.exclusion, mk.excluded, FlowAlgebra.prepend(this, p, FlowAlgebra.LEAF_NODE))
        }
        is MarkSlot.Concrete -> if (f.base == AccessPathBase.Zero) Reach.of(l) else taintTree(f.base, l,
            taintAlg.prepend(this, p, taintAlg.leafNode(
                if (n.fact.tail == Tail.EXACT) taintLeaves(markSetOf(mk.mark), MarkSet.EMPTY) else taintLeaves(MarkSet.EMPTY, markSetOf(mk.mark)))))
    }
}
```
 The trie functions are the generic functions
of `TrieOps.kt` (§4.2); `ApManager` has no node function of its own.

### 5.2 `ApOut` and the result collectors

```kotlin
/** Receives the results of one operation on one input. Requests exist only in run 1, and only for FLOW input (DD12). */
interface ApOut {
    fun result(f: Facts)                          // one result value: its own kind and canonical key
    fun markRequest(mark: TaintMark)              // ap.md §4.5, on the premise of the input edge
    fun positionRequest(position: PathNode)       // ap.md §4.10 item 1, the path cut to <= 2 accessors
}

/** ap.md §7.3 steps 5 to 7: the results of one operation on one input, one value per kind and canonical key. REACH: the
 *  layer. FLOW: (layer, exclusion, mark exclusion), the exclusion Empty in the demand layer. TAINT: the layer, after the W6
 *  split. Users: applyCompiledEdge, clean (and through them applySummary, applyCombination). */
internal class Results(private val m: ApManager, private val base: AccessPathBase) {
    private val reach = BooleanArray(2)
    private data class FlowKey(val layer: Layer, val exclusion: ExclusionSet, val mx: MarkSet)
    private val flow = LinkedHashMap<FlowKey, FlowNode>(2)
    private val taint = arrayOfNulls<TaintNode>(2)

    fun reach(layer: Layer) { reach[layer.ordinal] = true }

    fun flow(layer: Layer, exclusion: ExclusionSet, mx: MarkSet, node: FlowNode) {
        val k = FlowKey(layer, if (layer == Layer.DEMAND) ExclusionSet.Empty else m.intern(exclusion), m.intern(mx))
        flow[k] = flow[k]?.let { FlowAlgebra.mergeAdd(it, node) } ?: node
    }

    fun taint(layer: Layer, node: TaintNode) {
        if (layer == Layer.NORMAL && node.hasAny) {                              // W6: an `[any]` mark leaves the normal layer
            val (exact, any) = m.taintAlg.splitAny(node)
            exact?.let { taint(Layer.NORMAL, it) }
            any?.let { taint(Layer.DEMAND, it) }
            return
        }
        taint[layer.ordinal] = taint[layer.ordinal]?.let { m.taintAlg.mergeAdd(it, node) } ?: node
    }

    fun flush(out: ApOut) {
        for (l in Layer.entries) if (reach[l.ordinal]) out.result(Reach.of(l))
        for ((k, n) in flow) out.result(m.flowTree(base, k.layer, k.exclusion, k.mx, n))
        for (l in Layer.entries) taint[l.ordinal]?.let { out.result(m.taintTree(base, l, it)) }
        reach.fill(false); flow.clear(); taint.fill(null)
    }
}

/** An ApOut that keeps everything: tests, applySummary (Part I §5.4), the barrier. */
class CollectingOut : ApOut {
    val results = ArrayList<Facts>(); val markRequests = ArrayList<TaintMark>(); val positionRequests = ArrayList<PathNode>()
    override fun result(f: Facts) { results += f }
    override fun markRequest(mark: TaintMark) { markRequests += mark }
    override fun positionRequest(position: PathNode) { positionRequests += position }
}
```

### 5.3 The facade, `MarkGate`, `applyCompiledEdge` (`ap.md` §4.1, §4.2 step 4, §7.3; DD15)

```kotlin
/** The facade of the AP operations. Stateless: every memo is local to one call, so one instance serves every thread. */
class ApOps(val manager: ApManager) {
    fun applyEdge(c: Facts, premise: PremiseKey, e: PathEdge, statementEdge: Boolean, mode: ApMode, out: ApOut) {
        val ce = e.compiled ?: manager.compile(e).also { e.compiled = it }        // §7.5: the identity cache of the edge
        applyCompiledEdge(c, ce, edgeDemand = false, staticAt = staticIdentityDepth(c, premise, ce, statementEdge, mode), mode, out)
    }
    // Part I §5.4: satisfying, applySummary, applyCombination.   Part I §5.5: filter.   Part I §5.6: clean.
    // Part I §5.7: limit.   Part I §5.8: checkMark, without, targetTree.   Part I §5.9: zero, startFact, policy, emit, restrict.
    // Part I §5.10: requestAction.   Part I §5.11: reverse, leaves.
}
```

§5.4 to §5.11 write each operation as `fun ApOps.x(...)` to show its file. In the code each one is a member of `ApOps`
with the same signature. The member calls the internal helper of its file (`EdgeApplication`, `FlowClean`, `TaintClean`,
`FieldLimitCut`).

```kotlin
/** A PathEdge in the form that the tree walk reads. PathEdge caches it (`@JvmField internal var compiled`, Part I §6): a
 *  benign race, because CompiledEdge is immutable with final fields (JLS §17.5). Part II makes the PathEdges once per
 *  statement and keeps them in the method context cache, so the cache hits. */
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
        check(toMark !is MarkSlot.Concrete || fromMark is MarkSlot.Concrete)                  // S7
        check(fromTail != Tail.EXACT || fromMark is MarkSlot.Concrete)                        // S8
        check(fromTail != Tail.EXACT || toTail != Tail.STAR)                                  // S8
        check(toTail != Tail.EXACT || fromMark is MarkSlot.Concrete)                          // S8 (ExactTargetConc)
        check(fromTail == Tail.STAR || toTail == Tail.STAR || exclusion == ExclusionSet.Empty)  // W1: else `admitsRest`
    }                                                   // would silently drop children of U (also the edges of leafKinds)
}

/** ap.md §4.1 static exception, §4.10 item 1. The depth of the `*` leaf of an identity static `*` edge `(S, q, */E0, *) -> c`
 *  at `q = []` or `q = [<C>]`, when a statement micro edge reads strictly below q in run 1; else -1. Only a normal FLOW tree
 *  has `*` leaves. The walk tests condition 4 (`Ec admits r`). */
private fun staticIdentityDepth(c: Facts, premise: PremiseKey, ce: CompiledEdge, statementEdge: Boolean, mode: ApMode): Int {
    if (c !is FlowTree || c.layer != Layer.NORMAL || !mode.run1 || !statementEdge) return -1
    if (c.base != STATIC || ce.fromBase != STATIC) return -1
    val i = premise as? InitialAp ?: return -1                                                  // a FLOW premise is one InitialAp (K6)
    if (i.base != STATIC || i.tail != Tail.STAR) return -1
    val q = i.pathArray
    if (!(q.isEmpty() || (q.size == 1 && q[0].isClass()))) return -1                            // rootOrClass(q)
    if (ce.fromPath.size <= q.size || !ce.fromPath.startsWith(q)) return -1                      // case `above`
    return q.size
}
```

THE MARK GATE. One class for `applyCompiledEdge` (micro edges, summaries, records), `checkMark` (sinks, literals) and
`satisfying` (`markSub`):

```kotlin
/** ap.md §4.1 steps 4 and 5, per kind (§7.3; Lean markGate, markComp). `premise` is never `*∖X` (S7). */
internal class MarkGate(private val m: ApManager, val premise: MarkSlot, val target: MarkSlot) {
    init {
        check(premise !is MarkSlot.Star || premise.excluded.isEmpty)                               // S7
        check(premise is MarkSlot.Concrete || target is MarkSlot.Star)                             // S7: a concrete target needs a concrete premise
    }

    /** FLOW input with the mark `*∖x`: the mark exclusion of the result (a `*` premise passes every mark; a `*∖Y` target
     *  adds Y), or null: a concrete premise mark gives no fact (§7.3). */
    fun flowMarks(x: MarkSet): MarkSet? =
        if (premise is MarkSlot.Concrete) null else m.intern(x + (target as MarkSlot.Star).excluded)

    /** FLOW input under a concrete premise mark T: the request T (run 1), or null if `*∖x` excludes T (cleaned). */
    fun flowRequest(x: MarkSet): TaintMark? = (premise as? MarkSlot.Concrete)?.mark?.takeIf { it !in x }

    /** TAINT or REACH input: the result marks of the concrete marks `ms`, or null (no fact). */
    fun taintMarks(ms: MarkSet): MarkSet? {
        if (ms.isEmpty) return null
        val passed = when (premise) {
            is MarkSlot.Concrete -> if (premise.mark in ms) m.markSetOf(premise.mark) else return null   // T' ≠ T
            is MarkSlot.Star -> ms                                                                     // `*` passes every mark
        }
        val result = when (target) {
            is MarkSlot.Concrete -> m.markSetOf(target.mark)
            is MarkSlot.Star -> m.intern(passed - target.excluded)                                    // a mark in Y: no fact
        }
        return result.takeIf { !it.isEmpty }
    }
}
```

THE EDGE APPLICATION. `applyCompiledEdge` is the tree form of `concat` (`ap.md` §4.1, "delta-concat"; the reference
`concat` of `Reference.kt`): it computes, for every fact of `c`, the part that the premise selects (the case `below` or
`above`) and concatenates it with the target. One walk (`walk`, §4.6), one gate (`MarkGate`), one collector
(`Results`), per kind:

```kotlin
/** ap.md §7.3 steps 1 to 5 and 7 on all paths of `c` at once. Step 6 (the field limit) is not here: the caller cuts at the
 *  cut points of §4.4 (Part I §5.7). Cost: |from.path| + 1 nodes for the walk, the subtree U for the transform
 *  (Tree.walkSteps_le). */
internal fun ApOps.applyCompiledEdge(c: Facts, ce: CompiledEdge, edgeDemand: Boolean, staticAt: Int, mode: ApMode, out: ApOut) {
    if (c.base != ce.fromBase) return                                                       // §4.1 step 1
    val app = EdgeApplication(manager, ce, edgeDemand, mode, out)
    when (c) {
        is Reach -> app.reach(c)
        is FlowTree -> app.flow(c, staticAt)
        is TaintTree -> app.taint(c)
    }
    app.results.flush(out)
}

internal class EdgeApplication(private val m: ApManager, private val ce: CompiledEdge, private val edgeDemand: Boolean,
                               private val mode: ApMode, private val out: ApOut) {
    val results = Results(m, ce.toBase)
    private val gate = MarkGate(m, ce.fromMark, ce.toMark)
    private val admitsRest = { a: AccessorIdx -> ce.fromTail != Tail.EXACT && ce.exclusion.admits(a) }  // §4.1 step 3, row 1
    private val aboveTail = if (ce.toTail == Tail.EXACT) Tail.EXACT else Tail.ANY                        // case `above`
    private var requested = false

    /** REACH (§7.3): only an edge from the zero fact applies. The zero keep edge and the zero binding `zero.* -> zero.*`
     *  (ap.md §3.5: a binding has the premise mark `*`) give REACH, a source gives TAINT. */
    fun reach(c: Reach) {
        check(ce.fromPath.isEmpty() && ce.fromTail != Tail.ANY)      // `zero.$ (zeroMark)`, or the zero binding `zero.* (*)`
        gate.taintMarks(m.markSetOf(TaintMark.ZERO))?.let { put(c.layer or edgeDemand, ce.toTail, it) }
    }

    /** FLOW (run 1): the flag of a node is `p.*/Ec` (normal) or `p.[any]` (demand), with the mark `*∖Xc`. */
    fun flow(c: FlowTree, staticAt: Int) {
        val mx = gate.flowMarks(c.markExclusion)                     // null: a concrete premise mark; a hit is a request
        check(mx == null || ce.toTail != Tail.EXACT)                 // S8: a `$` target has a concrete premise mark
        val normal = c.layer == Layer.NORMAL
        val layer = c.layer or edgeDemand
        val u = c.root.walk(ce.fromPath) { d, n ->                   // §7.3 step 1: the case `above`
            if (n.leaf.isEmpty || (normal && !c.exclusion.admits(ce.fromPath[d]))) return@walk    // Tree.cS: `*/Ec` admits r
            if (normal && d == staticAt) out.positionRequest(m.position(ce.fromPath))               // §4.10 item 1: no fact, no request
            else flowHit(mx, c) { results.flow(Layer.DEMAND, ExclusionSet.Empty, it, flagAtTarget()) }  // `[any]` at to.path
        } ?: return
        val kids = FlowAlgebra.retainChildren(u, admitsRest)          // the case `below`, r ≠ []
        when (ce.toTail) {
            Tail.STAR -> {
                if (kids != null) flowHit(mx, c) {                   // r ≠ []: `to.path ++ r`, the tail of c with Ec
                    results.flow(layer, c.exclusion, it, FlowAlgebra.prepend(m, ce.toPath, kids)) }
                if (!u.leaf.isEmpty) flowHit(mx, c) {                // r = []: `*/(Ec ∪ E)` (normal); `[any]` (demand, W6)
                    results.flow(layer, c.exclusion.union(ce.exclusion), it, flagAtTarget()) }
            }
            else -> if (kids != null || !u.leaf.isEmpty)             // fold U: `[any]` (W6); `$`: only the request (S8)
                flowHit(mx, c) { results.flow(Layer.DEMAND, ExclusionSet.Empty, it, flagAtTarget()) }
        }
    }

    /** One FLOW result (the premise mark `*`), or the request of a concrete premise mark: the gate comes after the
     *  position test, so an apart fact gives no request (§4.1 step 4). */
    private inline fun flowHit(mx: MarkSet?, c: FlowTree, add: (MarkSet) -> Unit) {
        if (mx != null) { add(mx); return }
        val t = gate.flowRequest(c.markExclusion) ?: return                     // `*∖X` with T ∈ X: cleaned, no request
        if (!requested) { check(mode.run1) { "a restricted run is concrete (ap.md §6.3)" }; out.markRequest(t); requested = true }
    }

    /** TAINT: at a node the marks of the `$` leaves and of the `[any]` leaves. No `*` leaf, so no `lostCorr` (§4.1 step 3). */
    fun taint(c: TaintTree) {
        val layer = c.layer or edgeDemand
        val u = c.root.walk(ce.fromPath) { _, n ->                    // the case `above`: an `[any]` leaf admits r, a `$` leaf does not
            gate.taintMarks(n.leaf.any)?.let { put(Layer.DEMAND, aboveTail, it) }
        } ?: return
        when (ce.toTail) {
            Tail.STAR -> {
                m.taintAlg.retainChildren(u, admitsRest)?.let { kids ->          // r ≠ []: `to.path ++ r`, the tails of c
                    gateTree(kids)?.let { results.taint(layer, m.taintAlg.prepend(m, ce.toPath, it)) } }
                gate.taintMarks(u.leaf.exact)?.let { put(layer, Tail.EXACT, it) }            // r = [], `$`
                gate.taintMarks(u.leaf.any)?.let { put(Layer.DEMAND, Tail.ANY, it) }         // r = [], `[any]` (W6)
            }
            else -> {                                                            // fold U into one `[any]` (W6) or one `$` leaf
                val all = m.taintAlg.foldLeaves(u, admitsRest)
                gate.taintMarks(all.exact + all.any)?.let { put(if (ce.toTail == Tail.ANY) Layer.DEMAND else layer, ce.toTail, it) }
            }
        }
    }

    /** One TAINT leaf at to.path. A target on the zero base is the zero fact: REACH (a reversed source, ap.md §9.2). */
    private fun put(layer: Layer, tail: Tail, ms: MarkSet) {
        if (ce.toBase == AccessPathBase.Zero) { results.reach(layer); return }
        val leaf = when (tail) {
            Tail.EXACT -> m.taintLeaves(ms, MarkSet.EMPTY)
            Tail.ANY -> m.taintLeaves(MarkSet.EMPTY, ms)
            Tail.STAR -> error("S8: a concrete mark has no `*` leaf (W2)")
        }
        results.taint(layer, m.taintAlg.prepend(m, ce.toPath, m.taintAlg.leafNode(leaf)))
    }

    /** The gate on every leaf of a TAINT subtree. No copy for `*` -> `*` (the common case). */
    private fun gateTree(n: TaintNode): TaintNode? =
        if (ce.fromMark == MarkSlot.STAR && ce.toMark == MarkSlot.STAR) n
        else m.taintAlg.mapLeaves(n) { p -> m.taintLeaves(gate.taintMarks(p.exact) ?: MarkSet.EMPTY, gate.taintMarks(p.any) ?: MarkSet.EMPTY) }

    private fun flagAtTarget(): FlowNode = FlowAlgebra.prepend(m, ce.toPath, FlowAlgebra.LEAF_NODE)
}
```

`Tree.applyTreeE_mem`, `applyTreeE_den` prove this walk for a `*`-to-`*` edge with the mark `*` on both sides (a FLOW
tree). The gate, the static exception, the TAINT kind and the other target tails are the per-path rows of `ap.md` §4.1
applied per leaf. The test `FactsEquivalenceTest` (§8) compares every case with the reference `concat`.

### 5.4 `satisfying`, `applySummary`, `applyCombination` (`ap.md` §4.3, §4.6; DD4)

`satisfying` reads the leaves of a trie as tails (`ap.md` §3.4 `tailSub`, `tailAdmits`). The kind gives the tails:

```kotlin
/** The tails of the leaves of one trie: a FLOW flag is `*/Ea` (normal) or `[any]` (demand); a TAINT node has `$` and
 *  `[any]` leaves. `select` keeps the leaves of the accepted tails. */
private class Tails<P : TrieLeaf>(val exclusion: ExclusionSet, val select: (P, star: Boolean, any: Boolean, exact: Boolean) -> P)

private fun flowTails(a: FlowTree) = Tails<FlowLeaf>(a.exclusion) { p, star, any, _ ->
    if (if (a.layer == Layer.NORMAL) star else any) p else FlowLeaf.NONE }
private fun ApOps.taintTails() = Tails<TaintLeaves>(ExclusionSet.Empty) { p, _, any, exact ->
    manager.taintLeaves(if (exact) p.exact else MarkSet.EMPTY, if (any) p.any else MarkSet.EMPTY) }

/** The part of the added fact `a` whose facts satisfy `j`: `applicable` (run 1), `inside` (restricted), both (a record,
 *  §8.7 R4). ONE function for the replay and the delivery (analyzer-core.md P4). */
fun ApOps.satisfying(a: Facts, j: InitialAp, mode: ApMode, record: Boolean = false): Facts? {
    if (a.base != j.base) return null
    val below = record || mode.run1                                          // applicable: a at or below j
    val inside = record || mode.restricted                                   // inside (satI): j at or below a
    val m = manager
    return when (a) {
        is Reach -> a.takeIf { j.isZero }                                    // applicable(zero, zero), inside(zero, zero)
        is FlowTree -> if (j.mark !is MarkSlot.Star) null                    // markSub(T, *∖X) is false: see "Run 1" below
            else part(a.root, FlowAlgebra, flowTails(a), j, below, inside)?.let { m.flowTree(a.base, a.layer, a.exclusion, a.markExclusion, it) }
        is TaintTree -> part(a.root, m.taintAlg, taintTails(), j, below, inside)
            ?.let { n -> MarkGate(m, j.mark, MarkSlot.STAR).let { g -> m.taintAlg.mapLeaves(n) { p ->      // markSub(j.mark, T)
                m.taintLeaves(g.taintMarks(p.exact) ?: MarkSet.EMPTY, g.taintMarks(p.any) ?: MarkSet.EMPTY) } } }
            ?.let { m.taintTree(a.base, a.layer, it) }
    }
}

private fun <P : TrieLeaf> ApOps.part(root: TrieNode<P>, alg: LeafAlgebra<P>, t: Tails<P>, j: InitialAp, below: Boolean, inside: Boolean): TrieNode<P>? {
    val b = if (below) applicablePart(root, alg, t, j) else null
    val i = if (inside) insidePart(root, alg, t, j) else null
    return if (b == null) i else if (i == null) b else alg.mergeAdd(b, i)
}

/** applicable(j, leaf) (ap.md §3.4): j covers the leaf, and an `[any]` premise needs an `[any]` fact. ADAPT of
 *  AccessNode.filterStartsWith (AccessTree.kt:1329): walk j.path, take the subtree, rebuild the chain. */
private fun <P : TrieLeaf> ApOps.applicablePart(root: TrieNode<P>, alg: LeafAlgebra<P>, t: Tails<P>, j: InitialAp): TrieNode<P>? {
    val u = root.walk(j.pathArray) ?: return null
    val ej = j.exclusion
    val at = when (j.tail) {                                                  // r = []: tailSub(j, leaf)
        Tail.STAR -> t.select(u.leaf, ej.isSubsetOf(t.exclusion), ej == ExclusionSet.Empty, true)
        Tail.EXACT -> t.select(u.leaf, false, false, true)
        Tail.ANY -> t.select(u.leaf, false, true, false)
    }
    val kids = when (j.tail) {                                                // r ≠ []: j.tail admits r
        Tail.STAR -> alg.retainChildren(u) { ej.admits(it) }
        Tail.EXACT -> null
        Tail.ANY -> alg.retainChildren(u) { true }?.let { k -> alg.mapLeaves(k) { t.select(it, false, true, false) } }
    }
    return alg.withLeaf(kids, at)?.let { alg.prepend(manager, j.path, it) }
}

/** inside(j, leaf) (ap.md §3.4, Lean satI): j lies inside the leaf as locations. Such a leaf is at or above j.path. */
private fun <P : TrieLeaf> ApOps.insidePart(root: TrieNode<P>, alg: LeafAlgebra<P>, t: Tails<P>, j: InitialAp): TrieNode<P>? {
    val p = j.pathArray
    val spine = ArrayList<P>(p.size + 1)
    val u = root.walk(p) { d, n -> spine += t.select(n.leaf, t.exclusion.admits(p[d]), true, false) }   // above j: the tail admits r
    if (u != null) spine += t.select(u.leaf,                                                              // at j: tailSub(leaf, j)
        star = when (j.tail) { Tail.EXACT -> true; Tail.STAR -> t.exclusion.isSubsetOf(j.exclusion); Tail.ANY -> t.exclusion == ExclusionSet.Empty },
        any = true, exact = j.tail == Tail.EXACT)
    return alg.chain(manager, p, spine)
}
```

RUN 1: A SUMMARY WITH A CONCRETE PREMISE MARK AND A `*` FACT IN THE CALLER. Let `j = (x, [], *, {}, T)` or `(x, [], $, {}, T)` (a chain answer of the policy fact) and
let the added fact be a FLOW tree `a` (mark `*∖X`, `T ∉ X`). The summaries of `j` are TAINT (a concrete premise has
concrete conclusions, `Coverage.edge_conc`):

```kotlin
satisfying(a, j, run1)        // null: `applicable` needs markSub(T, *∖X), which is false. So applySummary never runs:
                              // a FLOW added fact never meets a TAINT summary, and the application raises NO request
                              // (Coverage.summary_step: a summary application never requests).
// The callee raised the standing request (m, i, T) when its rule met its policy fact i (§4.5, a FLOW fact). For the
// link of this caller (the added fact a: mark `*`, T not excluded) requestAction gives Climb(callerPremise, Mark(T))
// (Part I §5.10): the caller premise gets the request, and its own callers answer it. The FLOW fact a itself satisfies
// the policy fact i (`*`), and gets the FLOW summary of i.
```

`applySummary` is `concat(a, j -> g)` with `edgeDemand` = the layer of `g`, on every leaf of `g`. The leaves of one
(tail, mark) kind of `g` differ only by their path, so ONE `applyCompiledEdge` with `to.path = []` gives the result of
every such leaf, and `graft` puts it at each path (ADAPT of `concatToLeafAbstractNodes`, `AccessTree.kt:1281`, which puts
a caller delta under every abstract node of a summary):

```kotlin
/** ap.md §4.3, by kind (§7.2): FLOW a × FLOW g -> FLOW; TAINT a × FLOW g -> TAINT (a run-1 record with a `*` premise is a
 *  transfer function); TAINT a × TAINT g -> TAINT; TAINT a × REACH g -> REACH (backward: a requirement reached a source);
 *  REACH a × (REACH | TAINT) g -> the kind of g. FLOW a × TAINT g never occurs (above). Precondition: a = satisfying(...). */
fun ApOps.applySummary(a: Facts, j: InitialAp, g: Facts, mode: ApMode, out: ApOut) {
    check(a !is FlowTree || g is FlowTree) { "a FLOW fact satisfies only a `*` premise, whose summaries are FLOW" }
    for (kind in leafKinds(g, j)) {
        val one = CollectingOut()
        applyCompiledEdge(a, kind.edge, edgeDemand = g.layer == Layer.DEMAND, staticAt = -1, mode, one)
        check(one.markRequests.isEmpty())                                  // Coverage.summary_step
        for (r in one.results) out.result(kind.graft(r))
    }
}

/** One (tail, mark) kind of the leaves of g: the edge `j -> (tail, mark)` at the empty path, and the graft of a result into
 *  the paths of g with that kind. */
private class LeafKind(val edge: CompiledEdge, val graft: (Facts) -> Facts)

private fun ApOps.leafKinds(g: Facts, j: InitialAp): List<LeafKind> {
    val m = manager
    fun edge(tail: Tail, mark: MarkSlot, excl: ExclusionSet) =
        CompiledEdge(j.base, j.pathArray, j.tail, j.mark, g.base, null, tail, mark, m.intern(excl))
    return when (g) {
        is Reach -> listOf(LeafKind(edge(Tail.EXACT, MarkSlot.Concrete(TaintMark.ZERO), ExclusionSet.Empty)) { it })   // the zero fact
        is FlowTree -> listOf(                                                     // one kind: the flag, the mark `*∖Xg`
            if (g.layer == Layer.NORMAL) LeafKind(edge(Tail.STAR, MarkSlot.Star(g.markExclusion), j.exclusion.union(g.exclusion))) { graft(g.root, { it == FlowLeaf.LEAF }, it) }
            else LeafKind(edge(Tail.ANY, MarkSlot.Star(g.markExclusion), j.exclusion)) { graft(g.root, { it == FlowLeaf.LEAF }, it) })
        is TaintTree -> {                                                          // one kind per mark of the `$` and the `[any]` leaves
            val all = m.taintAlg.foldAll(g.root)
            all.exact.ids.map { t -> LeafKind(edge(Tail.EXACT, MarkSlot.Concrete(TaintMark(t)), j.exclusion)) { graft(g.root, { TaintMark(t) in it.exact }, it) } } +
            all.any.ids.map { t -> LeafKind(edge(Tail.ANY, MarkSlot.Concrete(TaintMark(t)), j.exclusion)) { graft(g.root, { TaintMark(t) in it.any }, it) } }
        }
    }
}

/** A result `r` (computed at the empty path) at every node of g whose leaf `occurs` holds; no other leaf of g. REACH has no
 *  path. An identity memo over g keeps shared subtrees of g shared. */
private fun <G : TrieLeaf> ApOps.graft(g: TrieNode<G>, occurs: (G) -> Boolean, r: Facts): Facts = when (r) {
    is Reach -> r
    is FlowTree -> r.withRoot(FlowAlgebra.graft(g, occurs, r.root)!!)
    is TaintTree -> r.withRoot(manager.taintAlg.graft(g, occurs, r.root)!!)
}
```

`LeafAlgebra<R>.graft(g: TrieNode<G>, occurs, r: TrieNode<R>)` (`TrieOps.kt`, code in §4.2) is generic over the kind
`G` of the summary and the kind `R` of the result (TAINT a × FLOW g grafts a TAINT result into a FLOW skeleton). It
keeps an identity memo over `g`. At an occurring node with occurrences below it, it MERGES `r` with the grafts below
(`mergeAdd`), as today: `ap.md` §4.3 is the union over every leaf of `g`.

Event E6 applies a summary with several premises to one full combination (`ap.md` §4.6 "at a call", `ap.md` §4.3; Lean
`ND.DN.ndBind`). The caller keeps the combination (`analyzer-core.md` §5.4). For each member `jm`, it gives the
satisfying part of the added fact of its link, `satisfying(a, jm, mode)`. The layer of that `Facts` IS the layer of the
added fact on the link (§7.5: `add` asserts `linkLayer == added.layer`). So the link layer enters through `part.layer`,
and the same `applySummary` of E2 and E4 gives the layer of each member:

```kotlin
/** One full combination: parts[m] = (the satisfying part for member m, the member jm). The summary has a PremiseSet, so
 *  its conclusion g is TAINT with no `*` tail (W7, ap.md §4.6) and every part is TAINT (a concrete member is satisfied
 *  only by a concrete added fact). Every member application gives the leaves of g (an uncorrelated target puts the result at
 *  to.path with the tail and the mark of the target, §4.1 step 3); only its LAYER differs. The result is in the demand
 *  layer if g is, if one part is demand on its link, or if one application moves it there (case `above`). The analyzer
 *  gives the result the union of the premise sets of the caller edges (ApManager.union), binds it back and cuts it. */
fun ApOps.applyCombination(parts: List<Pair<Facts, InitialAp>>, g: TaintTree, mode: ApMode, out: ApOut) {
    check(parts.size >= 2 && parts.all { it.first is TaintTree })               // ap.md §4.6: an ND edge is TAINT
    var normal = g.layer == Layer.NORMAL                                         // a choice of leaves with every member normal
    var demand = g.layer == Layer.DEMAND                                         // a choice with one member in the demand layer
    for ((part, j) in parts) {
        val one = CollectingOut()
        applySummary(part, j, g, mode, one)
        check(one.markRequests.isEmpty())                                        // satisfying: the gate passes (C4)
        if (one.results.isEmpty()) return                                        // not a full combination
        normal = normal && one.results.any { it.layer == Layer.NORMAL }
        demand = demand || one.results.any { it.layer == Layer.DEMAND }
    }
    if (normal) out.result(manager.taintTree(g.base, Layer.NORMAL, g.root))     // every result is a TaintTree
    if (demand) out.result(manager.taintTree(g.base, Layer.DEMAND, g.root))     // W6 holds: a normal g has no `[any]`
}
```

### 5.5 `filter` and the mark policy (`ap.md` §4.8, `interpreter.md` §5.1)

```kotlin
/** The mark policy of interpreter.md §5.1 (`markPolicyKeeps`): it reads a concrete mark on the value of the base itself
 *  (`elements = 0`) or on the value at `[e]^k` below the base (`elements = k`: the k-th element type), as today. It is NOT
 *  a may-predicate: it reads the mark, not the path, and it can drop a real flow (outside ap.md S5; gap G6). Part II
 *  builds it from the static type t: `MarkPolicy { mark, k -> the type at level k is not primitive or boxed, or
 *  isPrimitiveTracking(mark) }`; null if no level of t is primitive or boxed. */
fun interface MarkPolicy { fun keeps(mark: TaintMark, elements: Int): Boolean }

/** ap.md §4.8: the primitive `filter(b, may)`; `may` is prefix-closed (S5). The base is the key of
 *  StatementSummary.typeFilters (and resultFilters, Part II §23.2). Part II builds `may` with JIRFactTypeChecker (REUSE of
 *  its FactApFilter). `markPolicy` is the policy of the same static type and of its element types, or null (DD9). */
class TypeFilter(val may: FactTypeChecker.FactApFilter, val markPolicy: MarkPolicy? = null) {
    /** interpreter.md §5.1: two filters on one base are a conjunction. */
    fun and(o: TypeFilter): TypeFilter = TypeFilter(AndFilter(may, o.may), when {
        markPolicy == null -> o.markPolicy
        o.markPolicy == null -> markPolicy
        else -> MarkPolicy { t, k -> markPolicy.keeps(t, k) && o.markPolicy.keeps(t, k) }
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

/** ap.md §4.8: `filter(b, may)`, then the mark policy (interpreter.md §5.1: "after the filter", on the same facts). The
 *  path filter checks the concrete path only and keeps every tail whole. The zero fact passes (S11 (d)). The backward run
 *  calls neither (analyzer-core.md §3). */
fun ApOps.filter(c: Facts, f: TypeFilter): Facts? = when (c) {
    is Reach -> c
    is FlowTree -> FlowAlgebra.filterPath(manager, c.root, f.may)                 // no concrete mark: no policy
        ?.let { if (it === c.root) c else c.withRoot(it) }
    is TaintTree -> {
        var r = manager.taintAlg.filterPath(manager, c.root, f.may)
        val p = f.markPolicy
        if (r != null && p != null) r = markPolicyOnElements(r, p, 0)
        r?.let { if (it === c.root) c else manager.taintTree(c.base, c.layer, it) }
    }
}

/** TrieOps.kt, generic. ADAPT of AccessNode.filterAccessNode(FactApFilter) (AccessTree.kt:1031): no `[any]` edge, no
 *  FinalAccessor check. A filter never rejects the empty path, so the leaf of the root stays. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.filterPath(m: ApManager, n: TrieNode<P>, may: FactTypeChecker.FactApFilter): TrieNode<P>? =
    mapChildren(n, n.leaf) { a, child ->
        when (val r = may.check(m.accessors.accessor(a))) {
            FactTypeChecker.FilterResult.Accept -> child                         // the whole subtree (prefix-closed, S5)
            FactTypeChecker.FilterResult.Reject -> null
            is FactTypeChecker.FilterResult.FilterNext -> filterPath(m, child, r.filter)
        }
    }

/** interpreter.md §5.1 `markPolicyKeeps(t, f)`: true unless `f.path` is `[e]^k` (k >= 0: the root path or a chain of
 *  element accessors from the root) and `f.mark` is a concrete mark that the policy of level k rejects. So the marks of
 *  the TAINT leaves at the root and at each node of the `[e]` chain can go, for both tails; a leaf off the chain stays
 *  (below a field or a class accessor). As today: AccessorFilter gives FilterNext(element type) at `[e]`
 *  (core/opentaint-dataflow-core/opentaint-jvm-dataflow/.../jvm/ap/ifds/JIRFactTypeChecker.kt:114-123), and
 *  filterAccessNode (AccessTree.kt:1039-1045) shows the mark accessors of that subtree to it, so its TaintMarkAccessor
 *  case (JIRFactTypeChecker.kt:96-104) acts below each `[e]` with the element type. Here a mark is a leaf payload, so
 *  the policy walks the `[e]` chain itself. `n` is the result of filterPath. */
private fun ApOps.markPolicyOnElements(n: TaintNode, p: MarkPolicy, k: Int): TaintNode? {
    fun keep(ms: MarkSet) = if (ms.isEmpty) ms else manager.intern(MarkSet(ms.ids.filter { p.keeps(TaintMark(it), k) }.toIntArray()))
    val kept = manager.taintLeaves(keep(n.leaf.exact), keep(n.leaf.any))
    val e = n.child(ELEMENT_ACCESSOR_IDX)
    val below = e?.let { markPolicyOnElements(it, p, k + 1) }                      // the next level of the `[e]` chain
    if (kept === n.leaf && below === e) return n                                   // nothing dropped: share
    return if (e == null) manager.taintAlg.withLeaf(n, kept)
           else manager.taintAlg.replaceChild(n, kept, ELEMENT_ACCESSOR_IDX, below)   // null `below`: the `[e]` child goes
}
```

Part II gives the policy of each level from the static type: level 0 is the type itself, level `k + 1` is the element
type of level `k` (`ifArrayGetElementType`, the type that `FilterNext` of `[e]` carries today). A level with an unknown
type keeps every mark (today `[e]` gives `Accept` there, so no mark check runs below it).

### 5.6 `clean` (`ap.md` §4.7)

The position of a leaf against the cleaned locations is one table for every kind (`ap.md` §4.7 first table, Lean
`cleanPos`). One spine walk (`cleanSpine`) rebuilds only the spine of `x.p`; a node off the spine is `disjoint` and
stays shared. The result rows are per kind:

```kotlin
/** ap.md §4.7 first table, for a leaf with the tail `tail` at depth d of the spine of x.p (d < |p|: strictly above;
 *  d = |p|: at). `admitsRest`: the exclusion of a `*` leaf admits the rest of x.p. Strictly below x.p: `inside`, or
 *  `disjoint` for the reach `exact` (`cleanSpine`). */
internal fun cleanPosAt(cl: Cleaner, tail: Tail, d: Int, admitsRest: Boolean): Pos =
    if (d < cl.pathArray.size) when (tail) {
        Tail.EXACT -> Pos.DISJOINT
        Tail.STAR -> if (admitsRest) Pos.PART else Pos.DISJOINT
        Tail.ANY -> Pos.PART
    } else when (tail) {
        Tail.EXACT -> if (cl.reach == CleanReach.BELOW) Pos.DISJOINT else Pos.INSIDE
        else -> if (cl.reach == CleanReach.AT_AND_BELOW) Pos.INSIDE else Pos.PART
    }

/** TrieOps.kt, generic: `atNode(d, leaf)` returns the leaf that stays on the spine node of depth d (and moves the rest);
 *  `inside(kids)` returns what stays of the children strictly below x.p (reach below or atAndBelow). */
internal fun <P : TrieLeaf> LeafAlgebra<P>.cleanSpine(n: TrieNode<P>, p: IntArray, reach: CleanReach, d: Int,
                                                      atNode: (Int, P) -> P, inside: (TrieNode<P>) -> TrieNode<P>?): TrieNode<P>? {
    val kept = atNode(d, n.leaf)
    if (d < p.size) return replaceChild(n, kept, p[d], n.child(p[d])?.let { cleanSpine(it, p, reach, d + 1, atNode, inside) })
    if (reach == CleanReach.EXACT) return withLeaf(n, kept)                       // strictly below x.p: disjoint
    return withLeaf(retainChildren(n) { true }?.let(inside), kept)
}

fun ApOps.clean(c: Facts, premise: PremiseKey, cl: Cleaner, mode: ApMode, out: ApOut) {
    if (c.base != cl.base) { out.result(c); return }                           // another base: disjoint
    when (c) {
        is Reach -> out.result(c)                                               // S11 (d): no cleaner on the zero base
        is FlowTree -> FlowClean(manager, c, cl, mode, out).run()
        is TaintTree -> TaintClean(manager, c, cl, out).run()                   // a restricted run has only these (RExact.DR_concrete)
    }
}

/** ap.md §4.7, the rows of an abstract mark `*∖X` (run 1). */
private class FlowClean(val m: ApManager, val c: FlowTree, val cl: Cleaner, val mode: ApMode, val out: ApOut) {
    private val results = Results(m, c.base)
    private val tail = if (c.layer == Layer.NORMAL) Tail.STAR else Tail.ANY
    private val t = cl.mark
    private val cleanedMx = t?.let { m.intern(c.markExclusion + it) }          // `*∖(X ∪ {T})`
    private var requested = false

    fun run() {
        FlowAlgebra.cleanSpine(c.root, cl.pathArray, cl.reach, 0, ::row) { kids ->       // strictly below x.p: inside
            if (t != null) results.flow(c.layer, c.exclusion, cleanedMx!!, FlowAlgebra.prepend(m, cl.path, kids))   // one mark: `*∖(X ∪ {T})`
            null                                                                         // all marks: dropped
        }?.let { results.flow(c.layer, c.exclusion, c.markExclusion, it) }               // the kept part keeps the key of c
        results.flush(out)
    }

    private fun row(d: Int, leaf: FlowLeaf): FlowLeaf {
        if (leaf.isEmpty) return leaf
        val pos = cleanPosAt(cl, tail, d, admitsRest = d < cl.pathArray.size && c.exclusion.admits(cl.pathArray[d]))
        if (pos == Pos.DISJOINT) return leaf
        val at = FlowAlgebra.prepend(m, m.path(cl.pathArray.copyOf(d)), FlowAlgebra.LEAF_NODE)
        when {
            t != null -> {
                results.flow(c.layer, c.exclusion, cleanedMx!!, at)                     // inside and part: `*∖(X ∪ {T})`, the same layer
                if (pos == Pos.PART && t !in c.markExclusion && !requested) {          // part: the request T; §11.2: none for T ∈ X
                    check(mode.run1); out.markRequest(t); requested = true
                }
            }
            pos == Pos.PART -> results.flow(Layer.DEMAND, ExclusionSet.Empty, c.markExclusion, at)   // all marks, part: demand (W2)
            else -> Unit                                                               // all marks, inside: dropped
        }
        return FlowLeaf.NONE
    }
}

/** ap.md §4.7, the rows of a concrete mark: inside -> dropped; part -> concPart; a mark that the cleaner does not clean stays. */
private class TaintClean(val m: ApManager, val c: TaintTree, val cl: Cleaner, val out: ApOut) {
    private val results = Results(m, c.base)
    private fun gone(ms: MarkSet) = if (cl.mark == null) ms else ms.intersect(m.markSetOf(cl.mark))

    fun run() {
        m.taintAlg.cleanSpine(c.root, cl.pathArray, cl.reach, 0, ::row) { kids ->        // strictly below x.p: inside, cleaned marks go
            m.taintAlg.mapLeaves(kids) { p -> m.taintLeaves(p.exact - gone(p.exact), p.any - gone(p.any)) }
        }?.let { results.taint(c.layer, it) }
        results.flush(out)
    }

    private fun row(d: Int, leaf: TaintLeaves): TaintLeaves = m.taintLeaves(cut(d, Tail.EXACT, leaf.exact), cut(d, Tail.ANY, leaf.any))

    private fun cut(d: Int, tail: Tail, ms: MarkSet): MarkSet {
        val g = gone(ms)
        if (g.isEmpty) return ms
        when (cleanPosAt(cl, tail, d, admitsRest = true)) {
            Pos.DISJOINT -> return ms
            Pos.INSIDE -> Unit                                                        // dropped
            Pos.PART -> {                                                             // concPart (Lean)
                val at = m.path(cl.pathArray.copyOf(d))
                if (tail == Tail.ANY && cl.reach == CleanReach.BELOW && d == cl.pathArray.size) put(c.layer, at, Tail.EXACT, g)   // `(x, p, $, T)`
                else put(Layer.DEMAND, at, tail, g)                                   // any other part: the demand layer
            }
        }
        return ms - g
    }

    private fun put(layer: Layer, at: PathNode?, tail: Tail, ms: MarkSet) = results.taint(layer, m.taintAlg.prepend(m, at,
        m.taintAlg.leafNode(if (tail == Tail.EXACT) m.taintLeaves(ms, MarkSet.EMPTY) else m.taintLeaves(MarkSet.EMPTY, ms))))
}
```

### 5.7 `limit` and the field-limit tables (`ap.md` §4.4, W3)

```kotlin
/** ap.md §4.4. A path with more than L counted accessors is cut before the (L+1)-th one; the tail becomes `[any]`, the
 *  exclusion Empty, the mark stays (also `*∖X`), the layer becomes demand. `L = 0` keeps the empty path. */
fun ApOps.limit(c: Facts, fieldLimit: Int, out: ApOut) {
    when (c) {
        is Reach -> out.result(c)                                                          // the empty path
        is FlowTree -> limitTrie(FlowAlgebra, c.root, fieldLimit, { out.result(if (it === c.root) c else c.withRoot(it)) }) {
            out.result(manager.flowTree(c.base, Layer.DEMAND, ExclusionSet.Empty, c.markExclusion, it)) }   // `[any]`, `*∖X`
        is TaintTree -> limitTrie(manager.taintAlg, c.root, fieldLimit, { out.result(if (it === c.root) c else c.withRoot(it)) }) {
            out.result(manager.taintTree(c.base, Layer.DEMAND, it)) }                      // `[any]` with the marks of the cut leaves
    }
}

/** One trie, both kinds: the O(1) check (Part I §4.5), else the cut: the kept trie and the cut trie (each may be absent). */
private inline fun <P : TrieLeaf> ApOps.limitTrie(alg: LeafAlgebra<P>, root: TrieNode<P>, fieldLimit: Int,
                                                  kept: (TrieNode<P>) -> Unit, cut: (TrieNode<P>) -> Unit) {
    if (root.boundedDepth <= fieldLimit) { kept(root); return }
    val (k, c) = FieldLimitCut(alg, manager).keep(root, fieldLimit)
    k?.let(kept); c?.let(cut)
}

/** The cut on a trie, generic. ADAPT of FieldLimiter.limit (branch saloed/any-field-limit, AccessTree.kt:722): the same
 *  budget walk over the nodes with boundedDepth > budget, with a memo per budget; no `[any]` edge to keep, so the cut part
 *  is a separate demand trie. */
internal class FieldLimitCut<P : TrieLeaf>(private val alg: LeafAlgebra<P>, private val m: ApManager) {
    private val memo = Int2ObjectOpenHashMap<IdentityHashMap<TrieNode<P>, Pair<TrieNode<P>?, TrieNode<P>?>>>()

    /** (the paths within the budget, the `[any]` leaves at the cut points); both rooted at n, so the memo is path-free. */
    fun keep(n: TrieNode<P>, budget: Int): Pair<TrieNode<P>?, TrieNode<P>?> {
        if (n.boundedDepth <= budget) return n to null
        memo.getOrPut(budget, ::IdentityHashMap)[n]?.let { return it }
        m.cancellation.checkpoint()
        var cutHere = alg.empty                                                    // the leaves of the cut subtrees, as `[any]`
        val keptKids = IntArrayList(); val keptNodes = ArrayList<TrieNode<P>>()
        val cutKids = IntArrayList(); val cutNodes = ArrayList<TrieNode<P>>()
        n.accessors?.forEachIndexed { i, a ->
            val child = n.children!![i]
            if (a.isCounted() && budget == 0) { cutHere = alg.union(cutHere, alg.asAny(alg.foldAll(child))); return@forEachIndexed }
            val (k, ct) = keep(child, if (a.isCounted()) budget - 1 else budget)   // an uncounted accessor stays in the prefix
            k?.let { keptKids.add(a); keptNodes.add(it) }
            ct?.let { cutKids.add(a); cutNodes.add(it) }
        }
        val kept = alg.node(n.leaf, keptKids.toIntArray(), keptNodes.toTypedArray()).takeIf { !it.isEmpty }
        val cut = alg.node(cutHere, cutKids.toIntArray(), cutNodes.toTypedArray()).takeIf { !it.isEmpty }
        return (kept to cut).also { memo[budget]!![n] = it }
    }
}
```

THE CUT POINTS (`ap.md` §4.4). `analyzer-impl.md` makes each call through its one `cut(...)` helper; the helper calls
`ApOps.limit` with `RunConfig.fieldLimit`:

| Cut point (`ap.md` §4.4) | `Cut` of `analyzer-impl.md` §4.3 | Call site | What is cut |
|---|---|---|---|
| the statement transfer, after the micro edges and the lhs filter (`ap.md` §4.2 step 6); the read sources | `STATEMENT` | `runStatement` (`analyzer-impl.md` §4.3), after the result filters | the results of the statement on the touched bases |
| the call return: after the rewriter, the binding back and the aliases (`ap.md` §5.3 step 5) | `CALL` | `flow` at the exit point of the plan (`analyzer-impl.md` §4.5): one site for every result of a call (§4.6: `applySummary`, `applyRecord`, `zret`) | the summary results `g.path ++ r`, the record results, the unresolved and pass results, the alias results |
| the source results and the end facts of a sink at a call, after the binding back (`ap.md` §5.3 step 3) | `CALL` | the same site | the source targets and the end facts in caller coordinates |
| the entry rules (`interpreter.md` §4.3) | `ENTRY_RULES` | `RuleWorklist` of `startAt` (forward, `analyzer-impl.md` §4.4); of `endAt` (backward: the reversed entry rules, §4.7) | the entry-point sources and the end facts of an entry sink |
| the exit rules, before the summary edge (`interpreter.md` §4.7) | `EXIT_RULES` | `RuleWorklist` of `endAt` (forward, both exits, `analyzer-impl.md` §4.7); of `startAt` (backward: the reversed exit rules, §4.4) | the exit sources and the end facts of an exit sink |
| a conjunction result; a summary with several premises (`ap.md` §4.6, E6) | `STATEMENT`, `CALL` | the conjunction of a statement: `runStatement` (§4.3); the conjunction of a stage (an ND source; a pass rule never makes one, `interpreter.md` §4.2) and E6 (`applyCombination`, §4.11): the plan exit (§4.5) | the target `z.π.t(T)`; the E6 result |
| the backward seed (`ap.md` §9.2) | `SEED` | `fireSinkSeeds` (`analyzer-impl.md` §4.9); a seed at a call is cut again at the plan exit (no change) | the sink pattern as a requirement |

WHERE A FACT CAN EXCEED `L` (`ap.md` W3: only a micro edge has no bound; every result of an operation is in the bound
after its cut):

| Object | Longer than `L`? | Reason |
|---|---|---|
| a micro edge: a statement edge, a binding, an alias edge, a rule edge | yes: never cut | I10, `ap.md` §4.2, W3: the limit applies to the RESULT of an operation, never to an edge |
| a rule pattern: a sink pattern, a literal pattern, the end-fact patterns of a witness | yes: never cut | the check compares; it makes no fact (`checkMark`) |
| the intermediate result of one operation before its cut point: a statement transfer before step 6 | yes | row 1 of the cut points |
| the points `BOUND` to `REWRITTEN` of a call plan: a summary result `g.path ++ r`, a pass result, a source result, an end fact, an alias path | yes | the cut comes at the plan exit (rows 2, 3) |
| the results of the entry rules or of the exit rules before their cut | yes | rows 4, 5 |
| a conjunction result or an E6 result before its cut | yes | row 6 |
| a seed before its cut | yes | row 7 |
| a summary edge, a record (applied as an edge) | NO, and not cut again before the application (I10) | each one is a cut result of an earlier operation or run (the next two rows and the last row) |
| a stored conclusion (`MethodEdgeStore`) | NO (W3) | every result is cut before `edges.add`; the store asserts it (§7.3) |
| an initial fact | NO | the policy fact has the path `[]`; a chain answer is never deeper than its request premise (`ap.md` §4.5); a static mark answer is the added fact (below); a position answer has at most two accessors, and the class accessor is not counted, so at most one counted (`L >= 1`); an emission is `a` itself, its meet (the path of `a`) or the demand chain of the run before (`L' <= L`, non-decreasing limits, `ap.md` §6.6) |
| an added fact, a link, a subscription | NO | a binding does not make a path longer (`ai.* -> argi.*`, `S.* -> S.*`); a cleaner does not; the caller fact was cut |
| a publication, a run summary | NO | an exit fact after the exit rules and their cut (row 5); in a restricted run the restriction moves a conclusion only to `D-p.path`, a path of a run with `L' <= L` (`ap.md` §6.4) |
| a record, a demand pattern | NO | a summary of a run with `L' <= L` (non-decreasing limits); a demand pattern is only read, as a filter (`emit`, `restrict`) |

The NO rows are W3. It is argued, not proved (`ap.md` §11.2). `MethodEdgeStore.add` asserts it (§7.3).

### 5.8 `MarkCheck`, `without`, `targetTree`, `ConjunctiveEdge` (`ap.md` §4.6, §4.9; DD15)

```kotlin
/** The one check of a mark literal (ap.md §4.9 sinks, §4.6 conjunction literals; Lean check, conj, markGate). */
sealed interface MarkCheck {
    data object None : MarkCheck
    /** A FLOW fact that may carry T: the request T on the premise (run 1). */
    class Request(val mark: TaintMark) : MarkCheck
    /** REACH (an unconditional sink: the zero pattern), or the overlapping TAINT leaves with T. `covered`: the part inside
     *  the pattern (`coversB`), for the layer of a conjunction input (ap.md §4.6, ND.conjLayer). */
    class Holds(val facts: Facts, val covered: Facts?) : MarkCheck {
        val normalPart: Boolean get() = covered != null && facts.layer == Layer.NORMAL     // a normal conjunction input
        val demandPart: Boolean get() = facts.layer == Layer.DEMAND || covered != facts    // a demand conjunction input
    }
}

fun ApOps.checkMark(c: Facts, p: Pattern, mode: ApMode): MarkCheck {
    val t = (p.fact.mark as MarkSlot.Concrete).mark                                     // a literal names its mark (S9)
    if (c.base != p.fact.base) return MarkCheck.None
    val gate = MarkGate(manager, p.fact.mark, p.fact.mark)                              // the gate of the premise mark T (§4.1 step 4)
    return when (c) {
        is Reach -> if (t == TaintMark.ZERO) MarkCheck.Holds(c, c) else MarkCheck.None  // the zero pattern
        is FlowTree -> {
            if (!flowOverlaps(c, p)) return MarkCheck.None                              // overlap first, marks ignored (§3.2)
            val r = gate.flowRequest(c.markExclusion) ?: return MarkCheck.None          // `*∖X` with T ∈ X: no request
            check(mode.run1) { "a restricted run is concrete (ap.md §6.3)" }
            MarkCheck.Request(r)
        }
        is TaintTree -> {
            val hit = taintOverlap(c.root, p) ?: return MarkCheck.None                 // the leaves that overlap p
            val withT = manager.taintAlg.mapLeaves(hit) { l ->
                manager.taintLeaves(gate.taintMarks(l.exact) ?: MarkSet.EMPTY, gate.taintMarks(l.any) ?: MarkSet.EMPTY) } ?: return MarkCheck.None
            MarkCheck.Holds(manager.taintTree(c.base, c.layer, withT), coveredPart(withT, p)?.let { manager.taintTree(c.base, c.layer, it) })
        }
    }
}

// ap.md §4.9: on a request, "i.mark is abstract too ... the implementation asserts it". checkMark has no premise
// parameter; the request comes only from a FLOW fact, whose premise has the mark `*` (K6), and RequestStore.add
// (Part I §7.9) checks that the premise has the mark `*`.

/** Lean overlapB per leaf, on the walk of p.path: above p, a flag whose tail admits the rest (`*/Ec`: Ec admits it;
 *  `[any]`: always); at p, the flag; below p, a flag if p has the `[any]` tail. */
private fun flowOverlaps(c: FlowTree, p: Pattern): Boolean {
    val path = p.fact.path.toIntArray()
    var hit = false
    val u = c.root.walk(path) { d, n -> if (!n.leaf.isEmpty && (c.layer == Layer.DEMAND || c.exclusion.admits(path[d]))) hit = true }
    return hit || (u != null && (!u.leaf.isEmpty || (p.fact.tail == Tail.ANY && u.accessors != null)))
}

/** The TAINT leaves that overlap p (marks ignored): above p, the `[any]` leaves; at p, every leaf; below p, every leaf if p
 *  has the `[any]` tail. Rebuilt on the path (TrieOps.chain). */
private fun ApOps.taintOverlap(c: TaintNode, p: Pattern): TaintNode? {
    val path = p.fact.path.toIntArray()
    val spine = ArrayList<TaintLeaves>(path.size + 1)
    val u = c.walk(path) { _, n -> spine += manager.taintLeaves(MarkSet.EMPTY, n.leaf.any) }
    val tip = u?.let { if (p.fact.tail == Tail.ANY) it else manager.taintAlg.leafNode(it.leaf) }
    return manager.taintAlg.chain(manager, path, spine, tip)
}

/** coversB(p, leaf): a `$` pattern covers the `$` leaves at p; an `[any]` pattern covers every leaf at or below p. */
private fun ApOps.coveredPart(hit: TaintNode, p: Pattern): TaintNode? {
    val u = hit.walk(p.fact.path.toIntArray()) ?: return null
    val at = if (p.fact.tail == Tail.EXACT) manager.taintAlg.leafNode(manager.taintLeaves(u.leaf.exact, MarkSet.EMPTY)).takeIf { !it.isEmpty } else u
    return at?.let { manager.taintAlg.prepend(manager, manager.path(p.fact.path), it) }
}

/** The leaves of `c` that are not in `part` (same path, tail and mark); the same kind. The global-state rule
 *  (interpreter.md §4.7 step 3) drops from the summary edge the part of an item on S that satisfies a mark literal of an
 *  exit sink, plain or conjunctive (`MarkCheck.Holds.facts`). For a conjunctive sink the same part is the stored input of
 *  that literal (ConjunctionStore.Input.facts, Part I §7.10), so a later item can complete the combination with it. */
fun ApOps.without(c: Facts, part: Facts): Facts? = when {
    c.base != part.base -> c
    c is Reach -> if (part is Reach && part.layer == c.layer) null else c
    c is FlowTree && part is FlowTree -> FlowAlgebra.minusNode(c.root, part.root)?.let { if (it === c.root) c else c.withRoot(it) }
    c is TaintTree && part is TaintTree -> manager.taintAlg.minusNode(c.root, part.root)?.let { if (it === c.root) c else c.withRoot(it) }
    else -> c
}

/** A conjunction result `z.π.t(T)` (ap.md §4.6) or an end fact `P.$ (T)` (interpreter.md §4.1): a one-leaf TAINT tree.
 *  REACH only for the zero pattern (a seed of an unconditional sink); a conjunction target is never on the zero base
 *  (ConjunctiveEdge), so its result is a TaintTree. */
fun ApOps.targetTree(target: PathFact, layer: Layer): Facts {
    check(target.mark is MarkSlot.Concrete && target.tail != Tail.STAR)                 // W7
    return manager.factsOf(target, ExclusionSet.Empty, layer)
}

/** ap.md §4.6: `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)`. Each literal has a concrete mark (S9) and the tail `$` or
 *  `[any]`; the target has a concrete mark and no `*` tail (W7, S10). Part II reverses it into one PathEdge per literal,
 *  `revEdge(PathEdge(lit.fact, target, Empty))` (ap.md §9.2). The analyzer checks each literal with checkMark and gives
 *  the inputs to ConjunctionStore.add (Part I §7.10). */
class ConjunctiveEdge(val literals: List<Pattern>, val target: PathFact) {
    init {
        check(literals.size >= 2)
        check(literals.all { it.fact.mark is MarkSlot.Concrete && it.fact.tail != Tail.STAR })
        check(target.mark is MarkSlot.Concrete && target.tail != Tail.STAR)
        check(target.base != AccessPathBase.Zero)                       // so targetTree(target, layer) is a TaintTree
    }
}
```

`TrieOps.chain(m, path, spine, tip)` builds one leaf per depth on `path` and the node `tip` at its end (`null` if
everything is empty); `minusNode` walks `part` inside `c`. Both are in §4.2.

### 5.9 `zero`, `startFact`, `policy`, `emit`, `restrict` (`ap.md` §2.4, §6.2–§6.5, §7.4)

```kotlin
/** The zero fact in a layer (ap.md §2.4). The END FACTS of a sink take no input fact: on a trigger they apply
 *  `zero.$ (zeroMark) -> P.$ (T)` to the zero fact in the layer of the sink edge or of the combination (interpreter.md
 *  §4.1), so a demand sink edge needs the demand REACH. */
fun ApOps.zero(layer: Layer): Reach = Reach.of(layer)

/** ap.md §6.5 (Lean startFact), by kind. */
fun ApOps.startFact(i: InitialAp): Facts {
    if (i.isZero) return Reach.NORMAL                                                    // the zero fact starts as itself
    val m = manager
    return when (val mk = i.mark) {
        is MarkSlot.Star -> when (i.tail) {                                              // FLOW: a policy fact, a position answer
            Tail.STAR -> m.flowTree(i.base, Layer.NORMAL, i.exclusion, MarkSet.EMPTY, FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE))   // identity
            Tail.ANY -> m.flowTree(i.base, Layer.DEMAND, ExclusionSet.Empty, MarkSet.EMPTY, FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE))
            Tail.EXACT -> error("S8: a `$` premise has a concrete mark")
        }
        is MarkSlot.Concrete -> {                                                        // TAINT: an answer, an emission
            val ms = m.markSetOf(mk.mark)
            if (i.tail == Tail.EXACT) m.taintTree(i.base, Layer.NORMAL, m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(m.taintLeaves(ms, MarkSet.EMPTY))))
            else m.taintTree(i.base, Layer.DEMAND, m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, ms))))   // `*` with T: `[any]` (W2)
        }
    }
}

/** ap.md §6.2 (Lean policy1): the zero fact for the zero fact, else `(x, [], *, {}, *)`. One per added value (one base). */
fun ApOps.policy(added: Facts): InitialAp =
    if (added is Reach) manager.zero else manager.initial(added.base, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)

/** ap.md §6.3: `a ∩ D-c` for every leaf a of `added`, with the mark of a. One initial fact per distinct result (no sharing). */
fun ApOps.emit(d: DemandPattern, added: Facts): List<InitialAp> {
    val m = manager
    val dc = d.entry
    if (dc.fact.base != added.base) return emptyList()
    val markOk = { t: TaintMark -> dc.fact.mark !is MarkSlot.Concrete || (dc.fact.mark as MarkSlot.Concrete).mark == t }   // markMatchB: `*∖X` counts as `*`
    return when (added) {
        is Reach -> if (markOk(TaintMark.ZERO)) listOf(m.zero) else emptyList()          // the zero demand emits the zero fact
        is FlowTree -> error("C3: a restricted run is concrete (RCore.emitM_not_full_any)")
        is TaintTree -> {
            val p = m.path(dc.fact.path)
            val pa = dc.fact.path.toIntArray()
            val res = LinkedHashSet<InitialAp>()
            fun add(path: PathNode?, tail: Tail, excl: ExclusionSet, ms: MarkSet) {
                for (id in ms.ids) if (markOk(TaintMark(id))) res += m.initial(added.base, path, tail, excl, MarkSlot.Concrete(TaintMark(id)))
            }
            val u = added.root.walk(pa) { _, n -> add(p, dc.fact.tail, dc.exclusion, n.leaf.any) }   // above: `[any]` admits r; the demand chain
            if (u != null) {
                add(p, dc.fact.tail, dc.exclusion, u.leaf.any)                                       // at: meet([any], t) = t
                add(p, Tail.EXACT, ExclusionSet.Empty, u.leaf.exact)                                 // at: meet($, t) = $
                u.accessors?.forEachIndexed { i, a ->                                                // below: a itself if t admits r
                    if (dc.tailAdmits(listOf(a))) m.taintAlg.forEachLeaf(u.children!![i], pa + a) { path, leaf ->
                        add(m.path(path), Tail.EXACT, ExclusionSet.Empty, leaf.exact)
                        add(m.path(path), Tail.ANY, ExclusionSet.Empty, leaf.any)
                    }
                }
            }
            res.toList()
        }
    }
}

/** ap.md §6.4 on a whole value (§7.4, RStore.restrictTree). Cost |D-p.path| + 1 + width; kept subtrees are shared. A
 *  restricted run has REACH and TAINT only. */
fun ApOps.restrict(j: InitialAp, g: Facts, d: DemandPattern): Facts? {
    val dp = d.exit ?: return null                                         // the demand does not reach the exit
    if (!overlap(j.toPattern(), d.entry)) return null                      // the premise: all of j or nothing
    if (g.base != dp.fact.base) return null
    return when (g) {
        is Reach -> g                                                      // the zero fact at the empty path of D-p
        is FlowTree -> error("a restricted run is concrete")
        is TaintTree -> {
            val m = manager
            val pa = dp.fact.path.toIntArray()
            var moved = MarkSet.EMPTY                                      // the `[any]` marks above D-p.path
            val u = g.root.walk(pa) { _, n -> moved += n.leaf.any }       // step 1: `$` leaves and off-chain children go
            val movedLeaf = if (dp.fact.tail == Tail.EXACT) m.taintLeaves(moved, MarkSet.EMPTY) else m.taintLeaves(MarkSet.EMPTY, moved)
            val at = if (u == null) m.taintAlg.leafNode(movedLeaf).takeIf { !it.isEmpty }
                     else m.taintAlg.withLeaf(m.taintAlg.retainChildren(u) { dp.tailAdmits(listOf(it)) },   // step 2: the children that D-p admits
                                              m.taintAlg.union(u.leaf, movedLeaf))
            at?.let { m.taintTree(g.base, g.layer, m.taintAlg.prepend(m, m.path(pa), it)) }   // the layer and the mark of g
        }
    }
}
```

### 5.10 `requestAction` (`ap.md` §4.5, §4.10 items 2 to 4)

The analyzer joins a request with a link (`analyzer-core.md` §4.6, through `StandingJoin`, §7.10). The AP rule of the pair
is here:

```kotlin
sealed interface RequestAction {
    class Answer(val initial: InitialAp) : RequestAction                             // a new initial fact of this method
    class Climb(val premise: InitialAp, val request: RequestKind) : RequestAction    // RequestIn to the caller, on its premise
    data object None : RequestAction
}

/** One (request, link) pair. `a` is one leaf of the added fact of the link; it overlaps the request (RequestStore and
 *  AddedFactStore give only such pairs). */
fun ApOps.requestAction(i: InitialAp, kind: RequestKind, a: Pattern, caller: CallerRef): RequestAction {
    check(i.tail == Tail.STAR && i.exclusion == ExclusionSet.Empty && i.mark == MarkSlot.STAR)   // §4.5: a policy fact or a position answer
    val m = manager
    return when (kind) {
        is RequestKind.Mark -> when (val am = a.fact.mark) {
            is MarkSlot.Concrete ->
                if (am.mark == kind.mark) RequestAction.Answer(m.initial(answer(i.toPattern(), a, kind.mark)))   // `answer`, Part I §6
                else RequestAction.None                                                // T' ≠ T
            is MarkSlot.Star ->                                                        // a FLOW link: its caller edge is FLOW (K6)
                if (kind.mark in am.excluded) RequestAction.None                       // `*∖X` with T ∈ X: does not climb
                else RequestAction.Climb(caller.premise as InitialAp, kind)            // Lean climbsB
        }
        is RequestKind.Position -> when {
            a.fact.path.startsWith(kind.path.toList()) ->                               // item 2: at or below p
                RequestAction.Answer(m.initial(STATIC, kind.path, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR))
            (caller.premise as? InitialAp)?.base == STATIC -> RequestAction.Climb(caller.premise as InitialAp, kind)   // item 3: above p
            else -> RequestAction.None
        }
    }
}
```

A `Climb` reads the caller premise as an `InitialAp`: an added fact with an abstract mark comes from a FLOW caller edge,
whose premise is one `InitialAp` with the mark `*` (K6). An ND caller edge is TAINT (W7), so its added facts are concrete
and never climb.

RUN 1, A CONCRETE SUMMARY PREMISE AND A `*` CALLER FACT (§5.4): the summary is not applicable, and its application
raises no request. The request that reaches that caller is the standing request of the callee: the rule of the callee
raised it on its own policy fact, and the link of the caller (the `*` added fact) gives `Climb` here.

### 5.11 `reverse`, `leaves`, `leavesNear` (`ap.md` §9.1)

```kotlin
/** ap.md §9.1: null if the edge is not mark-reversible. Part II uses it for every micro edge (StatementSummary.reversed);
 *  Record.reversedAt uses it per conclusion leaf (Part I §7.8). */
fun ApOps.reverse(e: PathEdge): PathEdge? = revEdge(e)                              // Part I §6

/** The per-path view: one Pattern per leaf and mark. REACH: the zero pattern. FLOW: `*/E` (normal) or `[any]` (demand),
 *  with the mark `*∖X`. TAINT: `$` and `[any]` with each concrete mark. The tests read every result through it. */
fun ApOps.leaves(f: Facts): Sequence<Pattern> = when (f) {
    is Reach -> sequenceOf(manager.zero.toPattern())
    is FlowTree -> buildList { FlowAlgebra.forEachLeaf(f.root, EMPTY_PATH) { path, _ -> add(flowPattern(f, path)) } }.asSequence()
    is TaintTree -> buildList {
        manager.taintAlg.forEachLeaf(f.root, EMPTY_PATH) { path, leaf -> taintPatterns(f, path, leaf) { add(it) } }
    }.asSequence()
}

/** The leaves of `f` that overlap `(f.base, p, *, {}, *)` (ap.md §3.2): strictly above p, a leaf whose tail admits the rest
 *  of p (`*/E` with `p[d]` not in E, `[any]`; a `$` leaf does not); at or below p, every leaf. One walk of p (walkPath,
 *  §4.6), then the leaves of the subtree at p. Equal to `leaves(f).filter { overlap(it, q) }`. User: AddedFactStore.overlapping. */
fun ApOps.leavesNear(f: Facts, p: IntArray): Sequence<Pattern> = when (f) {
    is Reach -> if (p.isEmpty()) leaves(f) else emptySequence()
    is FlowTree -> buildList {
        val u = f.root.walk(p) { d, n ->
            if (!n.leaf.isEmpty && (f.layer == Layer.DEMAND || f.exclusion.admits(p[d]))) add(flowPattern(f, p.copyOf(d))) }
        u?.let { FlowAlgebra.forEachLeaf(it, p) { path, _ -> add(flowPattern(f, path)) } }
    }.asSequence()
    is TaintTree -> buildList {
        val u = f.root.walk(p) { d, n ->                                              // above p: the `[any]` leaves only
            taintPatterns(f, p.copyOf(d), manager.taintLeaves(MarkSet.EMPTY, n.leaf.any)) { add(it) } }
        u?.let { manager.taintAlg.forEachLeaf(it, p) { path, leaf -> taintPatterns(f, path, leaf) { add(it) } } }
    }.asSequence()
}

/** The leaf of a FLOW node at `path`: `*/E` (normal) or `[any]` (demand), with the mark `*∖X`. */
private fun flowPattern(f: FlowTree, path: IntArray): Pattern {
    val tail = if (f.layer == Layer.NORMAL) Tail.STAR else Tail.ANY
    return Pattern(PathFact(f.base, path.asList(), tail, MarkSlot.Star(f.markExclusion)), if (tail == Tail.STAR) f.exclusion else ExclusionSet.Empty)
}

/** The leaves of a TAINT node at `path`: `$` and `[any]` with each concrete mark. */
private inline fun taintPatterns(f: TaintTree, path: IntArray, leaf: TaintLeaves, add: (Pattern) -> Unit) {
    for (id in leaf.exact.ids) add(Pattern(PathFact(f.base, path.asList(), Tail.EXACT, MarkSlot.Concrete(TaintMark(id))), ExclusionSet.Empty))
    for (id in leaf.any.ids) add(Pattern(PathFact(f.base, path.asList(), Tail.ANY, MarkSlot.Concrete(TaintMark(id))), ExclusionSet.Empty))
}
```
---

## 6. The reference forms (`Reference.kt`)

`Reference.kt` holds the Kotlin of the spec as the spec gives it (DD2): `ap.md` §3.4 (from `startsWith`, `STATIC` and
`PathFact` to `inside`; `Tail`, `MarkSet`, `ExclusionSet` and `MarkSlot` are in `Facts.kt`, §3.2), `ap.md` §4.1
(`PathEdge` to `normalize`), `ap.md` §6.3 (`meet`, `emit`, `satisfies`) and `ap.md` §6.4 (`restrict`). The `Accessor`
of the spec is `AccessorIdx` (DD6), so `rootOrClass` calls `q[0].isClass()` (a function here, a property in `ap.md`
§4.1). The reference `concat` is the per-path delta-concat of `ap.md` §4.1; `applyCompiledEdge` (§5.3) is its tree
form (DD15). The tests compare every operation on `Facts` with these forms, through `ApOps.leaves` (§5.11). `PathEdge`
has one addition: the cache of §5.3.

```kotlin
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet) {
    @JvmField internal var compiled: CompiledEdge? = null                   // not in equals/hashCode (not a constructor property)
}
```

The forms that `ap.md` does not give in Kotlin (from the Lean definitions in `Basic.lean`, `ND.lean` and
`Subsume.lean`):

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

/** ap.md §4.7 (Lean cleanPos). The tree form is cleanPosAt (§5.6). */
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

sealed interface CheckResult { data object None : CheckResult; data object Holds : CheckResult; data class Request(val mark: TaintMark) : CheckResult }

/** ap.md §4.9 and §4.6 (Lean `check`, `conj`; renamed: `check` is the Kotlin assert): the check of one mark literal `s`
 *  on one fact. The tree form is ApOps.checkMark (§5.8). The §11.2 difference: the effective-mark case is asserted away. */
fun markCheck(i: Pattern, f: Conclusion, s: Pattern): CheckResult {
    val t = (s.fact.mark as MarkSlot.Concrete).mark
    if (!overlap(Pattern(f.fact, f.exclusion), s)) return CheckResult.None
    return when (val mk = f.fact.mark) {
        is MarkSlot.Concrete -> if (mk.mark == t) CheckResult.Holds else CheckResult.None
        is MarkSlot.Star -> if (t in mk.excluded) CheckResult.None
                            else { check(i.fact.mark is MarkSlot.Star); CheckResult.Request(t) }
    }
}

/** ap.md §4.6 (Lean ND.conjLayer): the layer of one input of a literal that holds on it. Demand if the input is in the
 *  demand layer, or if the literal does not cover it. MarkCheck.Holds.normalPart and demandPart are its tree form. */
fun conjDemand(f: Conclusion, lit: Pattern): Boolean = f.demand || !covers(lit, Pattern(f.fact, f.exclusion))

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

/** ap.md §8.1 (Subsume.subsumesB, markSubsB): s subsumes n inside one layer. FlowGroup and TaintGroup are its tree form. */
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

The test sources add the denotation `den(i, f)(l0, l1)` of `ap.md` §3.2, a statement transfer (`transfer` of
`Basic.lean`: the union of `concat` over the micro edges, an untouched base unchanged, then `limit`) for the vector
tests, and `asConclusions(f: Facts)`: the leaves of `f` (§5.11) with the layer of `f` (§8).

---

## 7. The stores (`ap.md` §8)

### 7.1 Ownership and concurrency (`analyzer-core.md` §2, O1–O5)

| Store | Lifetime | Writer | Readers | Concurrency |
|---|---|---|---|---|
| `MethodEdgeStore`, `InitialFactStore`, `AddedFactStore`, `RequestStore`, `ConjunctionStore` (with its `KaryJoin`s), the `StandingJoin` of the requests and links | RUN | the runner of the method (O1) | the same runner; the driver at the barrier (O5) | none: single writer; the join of the runners (`analyzer-core.md` §6.3) orders the barrier reads |
| `RunSummaryStore`, `SourceHitStore` | HAND-OFF | the runner of the method (O1) | the driver at the barrier | as above |
| `DemandStore` | RUN, read-only | the driver, before the run (`Builder.build`) | any runner (`analyzer-core.md` A4) | immutable after `build`; the start of the run publishes it |
| `RecordStore` | PERSISTENT | the driver, at a barrier (`persist`) | any runner, through `view()` (`analyzer-core.md` A4) | written only when no runner is alive; `view()` rejects writes |
| `VulnerabilityStore` | PERSISTENT | any runner (O4) | the driver at the barrier | nested `ConcurrentHashMap`s; `merge` is atomic per (key, shape) (§7.12) |
| `PathTrie`, `TrieInterner`, the groups of §4.3 | inside a store | the owner of the store | the owner | none; `SummaryStorage` (`analyzer-impl.md` §5.2) guards its trie with its lock (P3). The memory guard clears the soft table of a `TrieInterner` from its own thread; `Reference.clear` and `get` are thread-safe, and the owner then makes a new table (§4.5) |
| `ApManager`, `ApOps`, `FlowAlgebra`, `TaintAlgebra` | analysis | any | any | `ConcurrentHashMap`; `ApOps` is stateless (§5.3); a `TrieNode` is immutable |

### 7.2 `PathTrie` (`ap.md` §8 PATH TRIES)

```kotlin
package org.opentaint.dataflow.bidi.store

/** Entries keyed by `base :: path`. ADAPT of AccessBasedStorage (ap/ifds/access/tree/AccessBasedStorage.kt:12): the same child walk
 *  (`getOrCreateNode` :19, `find` :34, `allNodes` :76), keyed by IntArray instead of the old AccessPath.AccessNode, and plain
 *  fastutil maps instead of ConcurrentReadSafeInt2ObjectMap. The lookups use walkPath (§4.6). Single writer. Store.lean
 *  proves each lookup equals its list filter (`lookupPrefixes_equiv`, `lookupExtensions_equiv`, `mem_around_indexBy`).
 *  A node holds a SET of values: a value is at most once per position, and `add` costs O(1). A hot callee has one
 *  AddedFactStore key per (call site, caller premise) at `arg0 :: []`, so a list with a linear test is O(n²) there. The
 *  linked set keeps the insertion order, so every lookup is deterministic. */
class PathTrie<V : Any> {
    private class Node<V : Any> {
        val values = ObjectLinkedOpenHashSet<V>(2)
        var children: Int2ObjectOpenHashMap<Node<V>>? = null
        fun child(a: Int): Node<V>? = children?.get(a)
        fun getOrCreate(a: Int): Node<V> = (children ?: Int2ObjectOpenHashMap<Node<V>>().also { children = it }).getOrPut(a) { Node() }
    }
    private val roots = HashMap<AccessPathBase, Node<V>>(4)

    /** False if the value is at this position already (the equality of V; the users' values are interned or data classes). */
    fun add(base: AccessPathBase, path: IntArray, value: V): Boolean = node(base, path).values.add(value)

    private fun node(base: AccessPathBase, path: IntArray): Node<V> {
        var n = roots.getOrPut(base) { Node() }
        for (a in path) n = n.getOrCreate(a)
        return n
    }

    /** The entries at or above `path` (also at `path`). Cost: |path| + 1 nodes (Store.prefHits_le). */
    fun lookupPrefixes(base: AccessPathBase, path: IntArray): MutableList<V> {
        val out = ArrayList<V>()
        val root = roots[base] ?: return out
        walkPath(root, path, Node<V>::child) { _, n -> out += n.values }?.let { out += it.values }
        return out
    }

    /** The entries at or below `path` (also at `path`). */
    fun lookupExtensions(base: AccessPathBase, path: IntArray): List<V> =
        ArrayList<V>().also { out -> find(base, path)?.let { collect(it, out, self = true) } }

    /** lookupPrefixes ++ the entries strictly below: each entry once per position (Store.around; a value at two positions
     *  comes twice). It is also the `near` of ap.md §8.6 (RStore.nearBy_iff_around). Cost: walk + Σ|rel|
     *  (RStore.near_query_cost); a radix trie would give walk + count. */
    fun around(base: AccessPathBase, path: IntArray): List<V> =
        lookupPrefixes(base, path).also { out -> find(base, path)?.let { collect(it, out, self = false) } }

    fun all(): Sequence<V> = roots.values.asSequence().flatMap { r -> ArrayList<V>().also { collect(r, it, self = true) } }

    private fun find(base: AccessPathBase, path: IntArray): Node<V>? = roots[base]?.let { walkPath(it, path, Node<V>::child) }

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
/** ap.md §8.1, per kind (§7.2): REACH bits per (statement, premise key, layer); FLOW trees per (statement, premise, layer,
 *  base, exclusion, mark exclusion); TAINT trees per (statement, premise key, layer, base). REUSE of the structure of
 *  MethodAnalyzerEdges (ap/ifds/MethodAnalyzerEdges.kt:13): the zero edges in a BitSet per statement (SameInitialZeroFactEdges,
 *  :150), here one per premise key and layer; the statement as its instruction index (instructionStorageIdx, :272). The
 *  FLOW and TAINT keys below the premise are inside ConclusionGroup (Part I §4.3). */
class MethodEdgeStore(private val m: ApManager, private val method: MethodKey, private val lm: LanguageManager,
                      private val fieldLimit: Int) {
    private val size = lm.getMaxInstIndex(method.method) + 1
    private val reach = Reference2ObjectOpenHashMap<PremiseKey, Array<BitSet>>()                 // premise -> [NORMAL, DEMAND]
    private val groups = Reference2ObjectOpenHashMap<PremiseKey, Array<ConclusionGroup?>>()      // premise keys are interned
    private val interners = m.newInterners()

    /** Returns the delta (T4) or null (`analyzer-core.md` §4.3). */
    fun add(node: CommonInst, premise: PremiseKey, f: Facts): Facts? {
        check((f is FlowTree) == premise.isFlow)                     // K6: the kind follows from the premise (ap.md §7.2)
        check(premise !is PremiseSet || f is TaintTree)              // ap.md §4.6: an ND edge is TAINT
        val idx = lm.getInstIndex(node)
        when (f) {
            is Reach -> {                                            // premise {zero}, or {jb} in a backward run: the reversed
                                                                     // source `x.p.$ (T) -> zero.$ (zeroMark)` (ap.md §9.2 SOURCE HITS)
                val bits = reach.getOrPut(premise) { arrayOf(BitSet(size), BitSet(size)) }[f.layer.ordinal]
                if (bits[idx]) return null
                bits.set(idx)
                return f
            }
            is FlowTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion is within L (Part I §5.7)" }
            is TaintTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion is within L (Part I §5.7)" }
        }
        val byStatement = groups.getOrPut(premise) { arrayOfNulls(size) }
        val g = byStatement[idx] ?: ConclusionGroup(m, interners).also { byStatement[idx] = it }
        return g.add(f)
    }

    /** A query for the tests (not a query of ap.md §8.1): the edges at `node`, of one premise key or of every premise key.
     *  A set REACH bit is the Reach of that premise key and layer; the FLOW and TAINT values are the stored trees of the
     *  groups (Part I §4.3). */
    fun edgesAt(node: CommonInst, premise: PremiseKey? = null): Sequence<Pair<PremiseKey, Facts>> {
        val idx = lm.getInstIndex(node)
        val keys = premise?.let(::sequenceOf) ?: (reach.keys.asSequence() + groups.keys.asSequence()).distinct()
        return keys.flatMap { p ->
            val bits = reach[p]
            val r = Layer.entries.asSequence().filter { bits != null && bits[it.ordinal][idx] }.map { p to (Reach.of(it) as Facts) }
            r + groups[p]?.get(idx)?.all().orEmpty().map { p to it }
        }
    }

    /** A query for the tests: the stored values at `node` with a leaf that overlaps `pattern` (ap.md §3.2, the reference
     *  `overlap`). The result is the WHOLE stored value, not its overlapping part. */
    fun edgesAt(node: CommonInst, pattern: Pattern): Sequence<Pair<PremiseKey, Facts>> {
        val ops = ApOps(m)
        val p = pattern.fact.path.toIntArray()
        return edgesAt(node).filter { (_, f) -> f.base == pattern.fact.base && ops.leavesNear(f, p).any { overlap(it, pattern) } }
    }
}
```

The two queries read the store during its run. They are for the tests (`MethodEdgeStoreTest`, §8 test 22); `ap.md`
§8.1 has no query of the edges. The store lives for its run (`ap.md` §8.1). Trace resolution is out of scope
(`ap-history.md` F67), so no run keeps its store for a trace resolver.

The W3 assert is a JVM `assert`: the Gradle test task enables it (`-ea`), a production run does not pay for it. It
replaces the check of `TreeFieldLimitCheck` (branch `saloed/any-field-limit`). The items of the unchanged path
(`ap.md` §8.1) skip the store, as today: they go to the `unchanged` queue of the method analyzer and not through `add`
(`analyzer-impl.md` `DeltaWorklist.addUnchanged`).

### 7.4 `InitialFactStore` (`ap.md` §8.2)

```kotlin
class InitialFactStore {
    private val initials = ReferenceOpenHashSet<InitialAp>()            // interned: identity
    fun add(i: InitialAp): Boolean = initials.add(i)                    // also deduplicates the answers of §8.8
    fun all(): Collection<InitialAp> = initials
}
```

The store keeps no supported premise sets. The confirmation (`ap.md` §4.9 condition 3) reads `Support`, which the
driver computes at the barrier from the links (`analyzer-impl.md` §7.5).

### 7.5 `AddedFactStore`, `CallerRef`, `Link` (`ap.md` §8.3; DD4)

```kotlin
/** E-2 of analyzer-core.md §5.1: the caller side of a link. */
data class CallerRef(val caller: MethodKey, val premise: PremiseKey, val callerLayer: Layer, val call: CommonInst)

/** ap.md §8.3, the spec form: one leaf of an added value with its caller reference and its layer on the link. */
data class Link(val addedFact: Pattern, val linkLayer: Layer, val caller: CallerRef)

/** ap.md §8.3. The added facts of one caller reference are ONE value per (link layer, kind key): REACH (no more), FLOW
 *  (base, exclusion, mark exclusion), TAINT (base). The leaves of the value are the added facts (DD4). Two values with
 *  different keys never merge (T3).
 *  EXACT DEDUPLICATION (analyzer-core.md §5.3, E-3): the only merge is the T1 union of leaves (mergeAddDelta, Part I §4.2,
 *  with no fold). A leaf that the value of its key has (same path, tail, mark) is dropped, nothing else: no T5, no
 *  subsumption (no FlowGroup, TaintGroup, foldUnder, subtract). Reason: `applicable` is not monotone in the added fact
 *  (a fact above j does not satisfy j), so a subsumed leaf can satisfy a premise that the subsuming leaf does not; dropping
 *  it loses a link, an answer or a summary application. Each leaf has exactly ONE key: a FLOW leaf has no `$` tail and a
 *  TAINT key has no exclusion (DD12). So a leaf is a new link once. The analyzer reuses this store to merge its
 *  subscription values. */
class AddedFactStore(private val m: ApManager) {
    private data class Key(val ref: CallerRef, val group: GroupKey)                     // the layer of the group is the link layer
    private val values = Object2ObjectOpenHashMap<Key, Facts>()
    private val index = PathTrie<Key>()                                   // one entry per new leaf position (§8.8 overlap queries)

    /** Event E1/E2: returns the delta (the new links) or null. */
    fun add(ref: CallerRef, linkLayer: Layer, added: Facts): Facts? {
        check(linkLayer == added.layer)                                    // the layer of the added fact on the link (§8.3)
        val key = Key(ref, added.groupKey)
        val old = values[key]
        val delta: Facts = if (old == null) added.also { values[key] = it } else {
            val (merged, d) = m.mergeAddDelta(old, added)                   // T1, T4 (Part I §4.2); no subsumption
            values[key] = merged
            d ?: return null
        }
        m.forEachLeafPosition(delta) { base, path -> index.add(base, path, key) }   // a key once per position (a set, §7.2)
        return delta
    }

    /** §8.3, §8.8: the links whose added fact overlaps `(base, path, *, {}, *)` (a request premise or a position, §4.5).
     *  The index gives the candidate keys near the path; each candidate value is walked along the path (walkPath,
     *  ApOps.leavesNear, Part I §5.11), so only its leaves that overlap the query become links: no list of every leaf. */
    fun overlapping(base: AccessPathBase, path: PathNode?): Sequence<Link> {
        val p = path?.toIntArray() ?: EMPTY_PATH
        val ops = ApOps(m)
        return index.around(base, p).distinct().asSequence()                 // a key at several positions comes once
            .flatMap { key -> ops.leavesNear(values.getValue(key), p).map { Link(it, key.group.layer, key.ref) } }
    }

    fun links(): Sequence<Link> = values.keys.asSequence().flatMap { links(it) }      // the support at the barrier (analyzer-core.md §7.5)
    private fun links(k: Key) = ApOps(m).leaves(values.getValue(k)).map { Link(it, k.group.layer, k.ref) }
}
```

`ApManager.forEachLeafPosition(f: Facts, action: (AccessPathBase, IntArray) -> Unit)` (`TrieOps.kt`, §4.2) is
`forEachLeafPosition` of the algebra of the kind, and `(Zero, [])` for REACH. The analyzer computes the satisfying part
of a stored value with `ApOps.satisfying` (P4); `satisfying` reads the value, not the per-leaf links.

COST. A hot callee (for example a library method that 50 000 call sites reach) has one key per (call site, caller
premise) at the same position. `PathTrie.add` is O(1) per key (a hash set per node, §7.2), and a request reads, per
candidate key, the walk of its path and the leaves at or below it (`leavesNear`), not every leaf of the value.

### 7.6 `RunSummaryStore` (`ap.md` §8.5)

```kotlin
/** ap.md §8.5. Key (premise key, layer, kind key) -> the exit conclusions, BEFORE the restriction (analyzer-core.md
 *  §4.6). HAND-OFF. REPLACE of MethodInitialToFinalApSummaries (ap/ifds/access/tree/MethodInitialToFinalApSummaries.kt:13),
 *  which unions the exclusions of different summaries (:271). */
class RunSummaryStore(private val m: ApManager) {
    private val groups = Reference2ObjectOpenHashMap<PremiseKey, ConclusionGroup>()
    private val interners = m.newInterners()

    fun add(premise: PremiseKey, g: Facts): Facts? {
        check((g is FlowTree) == premise.isFlow)                         // K6
        check(premise !is PremiseSet || g is TaintTree)                  // ap.md §4.6: an ND summary is TAINT
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(g)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = groups.asSequence().flatMap { (p, g) -> g.all().map { p to it } }
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
 *  delta of the conclusion; the union of the records of one premise is the persisted conclusion. The kind of the
 *  conclusion follows from the premise (K6): FLOW for a `*` premise (run 1), TAINT for a concrete premise, REACH for the
 *  backward `{jb} -> zero` (a requirement that reached a source). */
class Record(val method: MethodKey, val direction: Direction, val premise: InitialAp, val conclusion: Facts) {
    /** R3, §9.1: the reversal of each conclusion leaf near `a` (byExit returned this record for `a`), if mark-reversible.
     *  The reversed record has the reversed leaf as its premise and the reversed premise as its one-leaf conclusion. A
     *  backward REACH record `jb -> zero` reverses into the forward source `zero -> jb` (a TAINT record). */
    fun reversedAt(a: Pattern): Sequence<Record> {
        val m = premise.manager
        val p = premise.toPattern()
        return ApOps(m).leaves(conclusion)
            .filter { it.fact.path.startsWith(a.fact.path) || a.fact.path.startsWith(it.fact.path) }   // the leaves that byExit found
            .mapNotNull { leaf ->
                val rev = revEdge(PathEdge(p.fact, leaf.fact, p.exclusion.union(leaf.exclusion))) ?: return@mapNotNull null
                Record(method, if (direction == Direction.FORWARD) Direction.BACKWARD else Direction.FORWARD,   // read in the other direction (R3)
                    m.initial(Pattern(rev.from, ExclusionSet.Empty)),        // the new premise has the Empty exclusion (§9.1)
                    m.factsOf(rev.to, rev.exclusion, Layer.NORMAL))          // a one-leaf conclusion; a record is normal (R1)
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
    private val merged = HashMap<Triple<MethodKey, Direction, InitialAp>, ConclusionGroup>()
    private val interners = m.newInterners()

    override fun add(record: Record) {
        entry.getOrPut(record.method, ::PathTrie).add(record.premise.base, record.premise.pathArray, record)
        m.forEachLeafPosition(record.conclusion) { base, p -> exit.getOrPut(record.method, ::PathTrie).add(base, p, record) }
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

    /** A delta per premise: ConclusionGroup (Part I §4.3) merges the same record of several runs, so a record never repeats. */
    override fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>) {
        for ((method, store) in summaries) for ((premise, g) in store.all()) {
            if (g.layer == Layer.DEMAND) continue                        // normal only
            val j = premise as? InitialAp ?: continue                    // ONE member; a PremiseSet is never a record (R1)
            if (direction == Direction.BACKWARD && j.isZero) continue    // a zero-premise backward edge is never persisted
            val delta = merged.getOrPut(Triple(method, direction, j)) { ConclusionGroup(m, interners) }.add(g) ?: continue
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

/** ap.md §8.8. RUN 1 only. A mark request is keyed by `base :: i.path`, a position request by `S :: p`. Every request
 *  comes from a FLOW fact (DD12), so its premise is a FLOW premise: one InitialAp with the mark `*` (K6). */
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
`RequestStore.overlapping(leaf)` for each new leaf. `ApOps.requestAction` (§5.10) gives the action of each pair. The
analyzer joins the pairs with `StandingJoin` (§7.10), with these two stores as its two sides (`analyzer-impl.md`
§4.8).

### 7.10 `KaryJoin`, `StandingJoin`, `ConjunctionStore`, `NdSummaryJoin` (`ap.md` §8.8, §8.9, `analyzer-core.md` §5.4)

THE STANDING JOINS. Two utilities for the rule "the input that arrives last completes the combination". `KaryJoin` has
`k` slots of one input type and owns them; `StandingJoin` has two sides of two types that the Part I stores own:

```kotlin
/** The standing k-ary join (DD14). `add(s, x)` stores x in slot s and returns the NEW full combinations: x at s, a stored
 *  input at every other slot. The input that arrives last completes each combination, so each combination comes out
 *  exactly once, in every arrival order; an input that is in two slots joins with itself. Single writer. REPLACE of the
 *  rule assumptions of TaintSinkTracker (ap/ifds/taint/TaintSinkTracker.kt:173-240): the same "the last input sees every
 *  earlier input" join, with premise sets and layers. */
class KaryJoin<T : Any>(val arity: Int) {
    private val slots = Array(arity) { LinkedHashSet<T>() }

    fun add(slot: Int, x: T): List<List<T>> {
        if (!slots[slot].add(x)) return emptyList()                     // stored already (exact deduplication, E-3)
        val out = ArrayList<List<T>>()
        val acc = ArrayList<T>(arity)
        fun product(k: Int) {
            if (k == arity) { out += ArrayList(acc); return }
            for (y in if (k == slot) listOf(x) else slots[k]) { acc += y; product(k + 1); acc.removeAt(acc.lastIndex) }
        }
        product(0)
        return out
    }
}
```

| User | Slots | Input |
|---|---|---|
| `ConjunctionStore.add` (below) | one per literal of a conjunction (`ap.md` §4.6) or of a conjunctive sink (`ap.md` §4.9) | `Input(premise, layer, facts)` from `MarkCheck.Holds` |
| `NdSummaryJoin` (below) | one per member of a summary with several premises (`ap.md` §4.6, E6); the conclusion is a `TaintTree` | the subscription of the analyzer that satisfies the member |


```kotlin
/** The two-sided standing join. The caller stores and deduplicates each side (E-3) BEFORE it calls newA or newB; a new
 *  element meets every stored element of the other side that `near` gives, so each pair meets once (one thread, O1).
 *  `near` must be symmetric: b is in nearB(a) if and only if a is in nearA(b). Users: the requests and the links of
 *  RunMethodAnalyzer (analyzer-impl.md §4.8): nearB = AddedFactStore.overlapping, nearA = RequestStore.overlapping
 *  (both path-index lookups, Part I §7.2), meet = ApOps.requestAction (Part I §5.10). */
class StandingJoin<A, B>(private val nearB: (A) -> Sequence<B>, private val nearA: (B) -> Sequence<A>,
                         private val meet: (A, B) -> Unit) {
    fun newA(a: A) { for (b in nearB(a)) meet(a, b) }
    fun newB(b: B) { for (a in nearA(b)) meet(a, b) }
}
```

| User | Join | Input |
|---|---|---|
| the request × link join (`analyzer-impl.md` §4.8, events E2, E5, E7) | `StandingJoin`: the requests (`RequestStore`) and the links (`AddedFactStore`) | a request, a link |

WHY TWO FORMS. Both keep the invariant "the input that arrives last completes the combination, so each combination
comes out once" (Store `standing_complete`). They differ in what they own and in what a combination is:

| | `KaryJoin<T>` | `StandingJoin<A, B>` |
|---|---|---|
| sides | `k >= 2` slots, one type | 2 sides, two types (a request, a link) |
| storage and deduplication | its own slots (`LinkedHashSet`) | none: the Part I stores (`RequestStore`, `AddedFactStore`) store and deduplicate, and the analyzer reads them at the barrier |
| partners of a new input | every stored input of every other slot: the full product (a literal input carries no position to index) | only the overlapping elements: the path-index lookups of the stores (`around`, Part I §7.2) |
| result | the list of new combinations (the caller makes one conjunction result or one E6 application per combination) | a callback per pair (`requestAction`: answer, climb or nothing) |

A `KaryJoin` with arity 2 is a `StandingJoin` whose `near` is "all stored inputs of the other slot". The converse does
not hold: a `KaryJoin` slot cannot use the stores' index without the index of every slot, and for `k >= 3` a "near"
of one new input does not bound the product. So the product code stays in `KaryJoin`, and `StandingJoin` is the two
loops above; no line of logic is in both.

```kotlin
/** ap.md §8.9. RUN. The literals of a source conjunction (an ND source) and of a conjunctive sink; a pass rule never
 *  makes a conjunction (interpreter.md §4.2). A combination has the union of the input premise sets WITHOUT the zero
 *  fact (ApManager.union): `{zero}` only if every input has `{zero}`. */
class ConjunctionStore(private val m: ApManager) {
    /** One input of a literal: its premise set and the layer of its contribution (§4.6: MarkCheck.Holds.normalPart gives
     *  a NORMAL input, demandPart a DEMAND input; both can hold), and for a conjunctive sink the facts on which the literal
     *  holds (§4.9: MarkCheck.Holds.facts). */
    data class Input(val premise: PremiseKey, val layer: Layer, val facts: Facts? = null)
    class Combination(val premise: PremiseKey, val layer: Layer, val inputs: List<Input>)

    private val joins = HashMap<Pair<Any, CommonInst>, KaryJoin<Input>>()

    /** `rule`: the conjunctive micro edge (a ConjunctiveEdge) or the sink alternative (a conjunctive SinkRule: one object
     *  per alternative, interpreter.md §5.3). So the join is per (conjunctive micro edge or sink alternative, statement),
     *  and its slot is the literal index. Returns the NEW full combinations. */
    fun add(rule: Any, statement: CommonInst, arity: Int, literal: Int, input: Input): List<Combination> =
        joins.getOrPut(rule to statement) { KaryJoin(arity) }.add(literal, input).map(::combine)

    private fun combine(inputs: List<Input>) = Combination(
        inputs.map { it.premise }.reduce(m::union),                     // the union without the zero fact (ap.md §4.6)
        if (inputs.any { it.layer == Layer.DEMAND }) Layer.DEMAND else Layer.NORMAL, inputs)

    /** analyzer-core.md §5.4 (E6): one join per (callee, premise key, layer of the publication, call statement). `S` is the
     *  link type of the analyzer (its Subscription), so this package does not depend on bidi.engine. */
    data class NdKey(val callee: MethodKey, val premise: PremiseKey, val layer: Layer, val call: CommonInst)
    private val ndJoins = HashMap<NdKey, NdSummaryJoin<*>>()
    @Suppress("UNCHECKED_CAST")
    fun <S : Any> ndJoin(key: NdKey): NdSummaryJoin<S> =
        ndJoins.getOrPut(key) { NdSummaryJoin<S>(m, key.premise.size) } as NdSummaryJoin<S>
}

/** E6: the members of a summary with several premises (a KaryJoin) and its conclusion, which grows by deltas. The
 *  summary has a PremiseSet, so its conclusion is TAINT (ap.md §4.6): one TaintGroup per base (T1, T4, T5). */
class NdSummaryJoin<S : Any>(private val m: ApManager, arity: Int) {
    private val members = KaryJoin<S>(arity)
    private val full = ArrayList<List<S>>()                              // the full combinations so far
    private val interners = m.newInterners()
    private val conclusion = HashMap<AccessPathBase, TaintGroup>(2)

    /** A subscription that satisfies member `index` (it goes under EVERY index that it satisfies): the new full
     *  combinations, each with every stored conclusion value. */
    fun addSubscription(index: Int, s: S): List<Pair<List<S>, TaintTree>> {
        val fresh = members.add(index, s)
        full += fresh
        return fresh.flatMap { c -> conclusion.values.flatMap { it.all() }.map { c to it } }
    }

    /** A new conclusion: its delta with every full combination (the key holds no conclusion, so every order works). */
    fun addConclusion(g: TaintTree): List<Pair<List<S>, TaintTree>> {
        val delta = conclusion.getOrPut(g.base) { TaintGroup(m, interners.taint) }.add(g) ?: return emptyList()
        return full.map { it to delta }
    }
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

/** ap.md §8.10: the key; the same key in two runs is the same vulnerability. `method` is the METHOD of the method key,
 *  WITHOUT the context: one sink statement that the analysis reaches in several contexts is ONE vulnerability
 *  (ap-history.md F67). Each witness keeps its own method key. */
data class VulnerabilityKey(val rule: RuleId, val method: CommonMethod, val statement: CommonInst)

/** ap.md §4.9: a sink edge. `facts` is the part of the conclusion on which the sink holds (MarkCheck.Holds.facts): REACH
 *  for an unconditional sink, else TAINT. Not one leaf. */
class SinkEdge(val premise: PremiseKey, val layer: Layer, val facts: Facts) {
    init { check(facts !is FlowTree) }                                 // MarkCheck: a FLOW fact gives only a request
}

/** One sink edge, or the sink edge set of a conjunctive sink, of ONE alternative in ONE method key; confirmed as a whole
 *  (analyzer-core.md §7.5). `alternative`: the index of the sink alternative of the rule at the statement (its cube and
 *  its array choice, as Part II numbers them: `SinkRule.alternative`); the same index in every run and every context
 *  (interpreter.md I5). `methodKey`: the method key of the sink edges; the confirmation reads the support of the premise
 *  set in this method key. */
class SinkWitness(val alternative: Int, val methodKey: MethodKey, val edges: List<SinkEdge>, val run: Int,
                  val endFacts: List<PathFact> = emptyList()) {
    @Volatile var confirmed: Boolean = false                           // set only at the barrier of a complete forward run

    /** ap.md §4.9 condition 3: the premise set whose joint support confirms the witness. A conjunctive sink: the union of
     *  the premise sets of its edges, without the zero fact (`{zero}` if every edge has `{zero}`). */
    fun supportPremise(m: ApManager): PremiseKey = edges.map { it.premise }.reduce(m::union)
}

interface VulnerabilityStore {
    fun add(key: VulnerabilityKey, witness: SinkWitness)
    fun witnessesOf(run: Int): Sequence<Pair<VulnerabilityKey, SinkWitness>>
}

/** PERSISTENT; any runner adds (O4). SEVERAL WITNESSES PER KEY (DD10): one entry per (key, alternative, method key, run,
 *  shape); its facts are the union of the parts of every witness of that entry on which the sink holds. */
class ConcurrentVulnerabilityStore(private val m: ApManager) : VulnerabilityStore {
    /** The SHAPE of a witness: its alternative, its method key, its run and, per literal, the premise set and the layer of
     *  its sink edge and the group key of its facts. One alternative has one pattern per literal, so the base and the
     *  kind of edge k are fixed; the group key adds the layer of the facts (a conjunction input can be demand on normal
     *  facts, §7.10). So two entries with one shape never have two group keys at one literal. */
    private data class Shape(val alternative: Int, val methodKey: MethodKey, val run: Int,
                             val edges: List<Triple<PremiseKey, Layer, GroupKey>>)

    private val byKey = ConcurrentHashMap<VulnerabilityKey, ConcurrentHashMap<Shape, SinkWitness>>()

    override fun add(key: VulnerabilityKey, witness: SinkWitness) {
        check(witness.methodKey.method == key.method) { "the witness is in a method key of the method of its key" }
        val shape = Shape(witness.alternative, witness.methodKey, witness.run,
            witness.edges.map { Triple(it.premise, it.layer, it.facts.groupKey) })
        byKey.computeIfAbsent(key) { ConcurrentHashMap() }.merge(shape, witness, ::union)     // atomic per (key, shape)
    }

    /** Edge k of the result: the same premise set and layer; the facts are the union (T1) of the two parts. Both parts have
     *  the same group key: the base of literal k of the alternative, the kind (REACH or TAINT), the layer of the facts. */
    private fun union(a: SinkWitness, b: SinkWitness): SinkWitness {
        check(a.alternative == b.alternative && a.methodKey == b.methodKey && a.edges.size == b.edges.size)
        return SinkWitness(a.alternative, a.methodKey,
            a.edges.zip(b.edges) { x, y ->
                check(x.facts.groupKey == y.facts.groupKey) { "T3: the union of one literal never crosses group keys" }
                SinkEdge(x.premise, x.layer, m.mergeAddDelta(x.facts, y.facts).first)                // Part I §4.2
            },
            a.run, (a.endFacts + b.endFacts).distinct())
    }

    override fun witnessesOf(run: Int) = byKey.entries.asSequence()
        .flatMap { (k, byShape) -> byShape.values.asSequence().filter { it.run == run }.map { k to it } }
}
```

`analyzer-core.md` §4.7 says "it never merges two witnesses into one". This merge (DD10) is not that merge:

* The forbidden merge is LOSSY. Today `TaintVulnerability.mergeAdd` (`ap/ifds/taint/TaintSinkTracker.kt:27`) can drop a
  witness: an `Unconditional` node replaces a `Fact` node (`:50`), a `Fact` node with another trigger position is ignored
  (`:62`), and a `Fact` node replaces a `WithRequirement` node (`:79`). The premise sets of the dropped witness are lost.
* This merge joins only witnesses of the SAME shape: the same alternative, the same method key, the same run and, per
  literal, the same premise set, the same layer and the same group key of the facts. The confirmation of `ap.md` §4.9
  reads only the method key and these: condition 1 (the layer of each sink edge), condition 2 (each member of the premise set is zero or exact
  concrete) and condition 3 (the premise set is supported jointly in the method key). So the merged entry is confirmed
  exactly when each of its witnesses is confirmed. `analyzer-core.md` §7.5 step 2 gives the same answer.
* The alternative is part of the shape. So the union never joins the sink edges of two alternatives: two alternatives
  on `arg0` and on `arg1` (an `Argument(*)` sink) with the same premise set stay two entries, and each literal of a union
  has one pattern, one base and one group key (the `check` in `union`).
* The method key is part of the shape. So one statement reached in two contexts is one vulnerability key with a witness
  per method key, and each witness is confirmed in its own method key.
* Each sink fact stays a leaf of the union value. So a later trace resolution can find each sink edge again.
* A conjunctive sink: the union of `(a1, b1)` and `(a2, b2)` of one alternative also denotes `(a1, b2)`. That
  combination is a witness too: `a1` and `b2` are stored inputs of the literals of that alternative at that statement,
  and `ConjunctionStore.add` (§7.10, one join per alternative) gives every combination of the stored inputs.
* The run is part of the shape. So a witness of one run never merges with a witness of another run
  (`RunResult.hasDemandVulnerability`, `analyzer-core.md` §10, reads the witnesses of one run).
* The merge only makes the number of entries per key smaller: one entry per shape, not one per delta that triggers the
  sink.

The driver builds the report at the barrier from `witnessesOf(run)` (`analyzer-impl.md` §7.6, `Report`): the
vulnerabilities that a complete forward run confirmed, and the DEMAND vulnerabilities of the latest complete forward
run; an incomplete run adds nothing and refutes nothing (`ap-history.md` F67). The fields of an entry are those of
`Report.Entry`; the witnesses of its key (one or more per alternative and method key) give the patterns, the sink edges
and the end facts of `ap.md` §8.10. Trace resolution is out of scope: no run keeps its stores for it, and phase 3
gives each CONFIRMED vulnerability a trace with only the sink statement.

---

## 8. Test plan (`ap.md` §13)

Tests are in `core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ap/` and
`.../bidi/store/`, with `kotlin.test` as today (`ap/ifds/access/tree/AnyFieldMarkExclusionTest.kt`). Write each test
class before its code, in this order. Each row names the Lean theorem or `example` that it mirrors. A generic test
runs once per leaf algebra (`FlowAlgebra`, `TaintAlgebra`): the trie code is shared (DD14), so is its test.

| # | Test class | Checks (`ap.md` §13 item) | Lean |
|---|---|---|---|
| 1 | `FactModelTest` | `MarkSet`/`ExclusionSet` canonical form, no empty `Concrete`; `PathNode`, `InitialAp`, `PremiseSet`, `TaintLeaves` interning gives identity; `premiseOf` of one member is the `InitialAp` itself, of two or more a `PremiseSet` sorted by id; `union` is the set union WITHOUT the zero fact: `{zero} ∪ {i} = {i}`, `{zero} ∪ {zero} = {zero}`, `{i} ∪ {k} = {i, k}`, `{zero} ∪ {i, k} = {i, k}`; a `PremiseSet` with a zero member or with a `*` member is rejected; `nonZeroCount` names the edge (§4.6); `AccessorTable` decodes field, element and class accessors as `AccessorInternerTest` and REJECTS a type-info or a value accessor (W5); `TrieNode` and `Facts` equality across two interners (DD5) | — |
| 2 | `ApManagerConcurrencyTest` | 8 threads intern the same accessors, marks, paths, premises and leaves: one object each, no hang (a timeout fails the test) | — |
| 3 | `ReferenceDenotationTest` | `covers`, `overlap`, `applicable`, `inside`, `cleanPos` against `den` (`ap.md` §3.2) on a bounded universe with a fresh accessor and a fresh mark (item 2) | `coversB_sound`, `overlapB_of_common`, `cleanPos_inside_sound`, `cleanPos_disjoint_sound` |
| 4 | `TrieOpsTest`, `TrieInternerTest` | each generic function of §4.2 and §4.6 on both algebras against a list-of-leaves model: `mergeAdd`/`mergeAddDelta` (the delta unions to the merge; a shared subtree pair is merged once; a deep trie needs no deep stack), `mapChildren` (an unchanged child list returns the node itself), `replaceChild` (insert, replace, and remove with a null child), `withLeaf`, `mapLeaves`, `retainChildren`, `prepend`/`chain` (also a spine shorter than the path, and a tip with its own leaf), `minusNode`, `splitAny`, `forEachLeaf`, `foldUnder`, `subtract`, `filterPath`, `FieldLimitCut`, `walk`; `graft` MERGES at nested occurrences (`g = {ret.*, ret.f.*}` with `r` at `[]` and `[f]` keeps both `ret.f` leaves), drops a node of `g` with no occurrence, keeps a shared subtree of `g` shared; no operation collapses a repeated field, a chain of three `[e]` or a path below a class accessor (only `L` bounds a path); `foldAll` and `foldLeaves` include the leaf of the node itself (a trie with only a root leaf; a cut child with a leaf); `boundedDepth` and `hasAny` equal a recount. `TrieInterner`: two equal tries give one object, with `interned = true`; after `SoftReferenceManager.cleanup()` the next intern makes a new table, and the earlier interned nodes stay valid and equal (only sharing is lost); with a disabled manager (`createRef` gives null) interning still works within one call; `internIfRequired` interns a trie of `SIZE_TO_FORCE_INTERN` nodes at once and one add in `INTERN_RATE` otherwise | `Tree.rule1_mem`, `Tree.prependPath` |
| 5 | `KindTest` | the types enforce W1, W2, W6: `taintTree` rejects an `[any]` mark in the normal layer; `flowTree` gives the Empty exclusion in the demand layer; `Results` routes each result to its kind and canonical key (a source on REACH gives TAINT, the zero keep edge and the zero binding `zero.* -> zero.*` on `Reach.NORMAL` and `Reach.DEMAND` give the same `Reach`, a `*` edge on FLOW gives FLOW); the W6 split of a normal TAINT result; the `init` checks of `FlowTree` and `TaintTree` (W1 demand, W6) fail on a bad `withRoot` (item 1) | `Invariant.final_star_legal`, `Coverage.edge_conc` |
| 6 | `ApplyEdgeVectorsTest` | every `example` of `Cases.lean` and `RestrictedCases.lean`, on the reference forms AND on `ApOps`; W6 vectors assert the demand layer; the zero binding on the zero fact (item 1) | `Cases.lean`, `RestrictedCases.lean` |
| 7 | `FactsEquivalenceTest` | random `Facts` of each kind and random edges (every tail and mark row, the static exception, `*∖X`, the bindings of Part II §28.2 with the zero binding): the results of `applyCompiledEdge`, read by `leaves`, equal the per-leaf `concat`, layer, exclusion, mark exclusion and requests included; the same for `clean`, `filter`, `limit`, `restrict`, `checkMark` and `satisfying` against their reference forms (item 2) | `Tree.applyTreeE_mem`, `applyTreeE_den`, `applyTreeE_grouped_key`, `RStore.restrictTreeE_mem_U` |
| 8 | `MarkGateTest` | every row of `ap.md` §4.1 steps 4 and 5 per kind: FLOW + `T` gives no fact and the request `T` if `T ∉ X`, nothing if `T ∈ X`; TAINT + `T` keeps the leaves with `T`; `*` passes every mark; a `*∖Y` target drops the marks in `Y`; the `check` preconditions of `CompiledEdge` fail: S7 (a `*∖X` premise; a concrete target under a `*` premise), S8 (a `$` premise with `*`; a `$` premise with a `*` target; a `$` target under a `*` premise) and W1 (`x.[any] (T) →_{f} y.$ (T)`: a non-empty exclusion with no `*` side); the request comes after the position test (an apart fact gives none) (items 3, 4) | `markComp_sound`, `Core.applyEdge_sound` |
| 9 | `MergeRulesTest` | per kind: T1; FLOW: T2 and T2' only for equal content, the delta of T2 is the whole merged tree minus what the §8.1 subsumption drops (one case with a subsuming tree, one without), no union across trees; TAINT: one tree per layer; T4 deltas union to the value; a leaf below a stored `[any]` of the same mark gives null, also on its second arrival (the termination guard of T5) (item 8) | `Tree.rule1_mem`, `rule2_den`, `rule2_mark`, `Subsume.merge_inter`, `union_loses_pairs` |
| 10 | `SubsumptionTest` | `FlowGroup.add` and `TaintGroup.add` drop exactly what `subsumes` (§6) drops; never across layers or kinds | `Subsume.subsumes_sound`, `recordSubsumesLB_layer` |
| 11 | `LayerRulesTest` | items 3 and 4: the cut, W6, W2, demand in -> demand out | `applyEdge_demand_monotone` |
| 12 | `FieldLimitTest` | `limit` equals the per-leaf `limit` (§6) for both kinds; `L = 0`; an uncounted class accessor stays; the `MethodEdgeStore.add` assert fires on a value deeper than `L` (W3, §5.7) | `limitF_sound` |
| 13 | `CleanerTest` | every row of the two tables of `ap.md` §4.7, per kind; the split; no request for T ∈ X; the all-marks cleaner; a cleaned fact `*∖{T}` through a field write past the field limit keeps its mark exclusion in the cut demand tree (`limit` of the FLOW tree keeps `c.markExclusion`, §5.7) (item 5) | `CleanCases` in `Cases.lean`, `Core.cleanRes_sound`, `Exact.cleanRes_exact` |
| 14 | `TypeFilterTest` | accepted path passes with its tail; rejected path drops; `FilterNext`; `and` is the conjunction (of the paths and of the policies); the mark policy drops a rejected concrete mark of a TAINT leaf, both tails, at the root path (level 0) and at each node of the `[e]` chain (`b.[e].$ (T)` with level 1, `b.[e].[e].[any] (T)` with level 2, as today on `byte[]`, `int[][]`, `Integer[]`), after the path filter; a leaf below a field or off the `[e]` chain stays; an `[e]` child whose marks all go is removed; an unchanged tree is returned as it is; a FLOW tree has no policy (item 6; `interpreter.md` §5.1) | `Core.filt_keeps` (path part; the policy is gap G6, no theorem) |
| 15 | `MarkCheckTest` | the `check` vectors of `ap.md` §4.9 on `checkMark` and `markCheck`; `*∖X` with T ∈ X; the static premise; REACH holds for the zero pattern; `Holds.normalPart`/`demandPart` equal `conjDemand` per leaf (a fully covered input is normal only); `without(c, Holds.facts)` has no leaf of the part and keeps every other leaf | `check_sound`, `check_request_star`, `ND.conjLayer`, `ND.Example.c3_normal` |
| 16 | `SummaryKindsTest` | `applySummary` for every kind pair of §5.4 equals the per-leaf `concat` with the summary edge, also for a summary with a root leaf (`ret.$ (T)`, `arg0.[any] (T)`); `satisfying(FLOW a, concrete j)` is null and no request comes (item 9); `applyCombination` gives the layer of `ND.DN.ndBind` | `Coverage.summary_step`, `applicable_mark`, `ND.DN.ndBind` |
| 17 | `EmissionTest`, `RestrictionTest` | every row of `ap.md` §6.3 and §6.4; two insertion orders; programs 1 and 2 (items 11, 12) | `RCore.emitM_inter`, `emitM_complete`, `RCases.p1_found_M`, `p2_found_M` |
| 18 | `RequestActionTest` | answer, climb, nothing; the chain answer; `ap.md` §4.10 items 2–4; the run-1 case of §5.10: a FLOW link under a concrete callee request climbs; `requestAction` rejects a premise that is not a policy fact `(x, [], *, {}, *)` or a static position answer `(S, p, *, {}, *)`; a request in a restricted run fails its assert (`EdgeApplication.flowHit`, `checkMark`, `FlowClean`) (item 9) | `answerInit_covers`, `Statics.CexClean.shallow_misses` |
| 19 | `ReversalTest` | every row of `ap.md` §9.1 that occurs for a record, with `*∖X`; converse results on one concrete pair; a backward REACH record reverses into a forward source (item 15) | `Reverse.revEdge_exact`, `rev_starEx_exact` |
| 20 | `PathTrieTest` | `lookupPrefixes`, `lookupExtensions`, `around` equal their list filters on random keys; `add` of a value that is at the position already returns false and stores nothing; the lookups give the values in insertion order (item 14) | `Store.lookupPrefixes_equiv`, `lookupExtensions_equiv`, `mem_around_indexBy` |
| 21 | `KaryJoinTest` | `KaryJoin`: every combination comes out exactly once, in every arrival order (all permutations of a few inputs, arity 2 to 4); an input in two slots; a repeated input gives nothing. `StandingJoin`: with two `PathTrie`-backed sides and an overlap `near`, every overlapping pair meets exactly once in every arrival order, and no other pair meets | `standing_complete` |
| 22 | `AddedFactStoreTest`, `RequestStoreTest`, `DemandStoreTest`, `RecordStoreTest`, `ConjunctionStoreTest`, `VulnerabilityStoreTest`, `MethodEdgeStoreTest` | each index against its list filter; a new caller edge of an existing added fact is a new link (the example of `ap.md` §4.5); each leaf has one key; `AddedFactStore.overlapping` equals `links().filter { overlap(it.addedFact, q) }` for queries above, at and below the leaves, and for a `*/E` leaf above the query whose `E` excludes the next accessor (no link); `ApOps.leavesNear` equals `leaves(f).filter { overlap }` per kind; 100 000 caller keys at one position are added and queried in linear time (a timeout fails the test); `RequestStore.add` rejects a premise that is not `(x, [], *, {}, *)` (item 9); a backward edge `{jb} → zero` is stored as REACH and its repeat gives null; the kind assert of `add` (K6), and a `PremiseSet` key with a REACH or FLOW value is rejected (`MethodEdgeStore`, `RunSummaryStore`); `MethodEdgeStore.edgesAt` (both overloads) against a list of every added edge: the REACH bits as `Reach` per layer, one premise or all, the pattern overload returns the whole stored value; a combination of a `{zero}` input and an `{i}` input has the premise `{i}`, and of two `{zero}` inputs `{zero}` (`ConjunctionStore`); `SinkWitness.supportPremise` drops the zero fact; E6 in two orders. `VulnerabilityStoreTest`: two alternatives of one `Argument(*)` sink on `arg0` and on `arg1`, both with `{zero}` and normal, give two entries of one key and no exception; two method keys (two contexts) of one method at one statement give ONE `VulnerabilityKey` and two entries, each with its own method key; a witness whose method key is not of the key's method is rejected; the merge of one entry keeps every sink leaf and its end facts, never crosses group keys (also a demand input on normal facts), and the confirmation of a merged entry equals that of its witnesses (DD10) (items 7, 14) | `standing_complete`, `RStore.near_equiv`, `PipelineStore.record_lookup`, `NDConfirmed.CexSites.cex_sites` |

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
        val e1 = ExclusionSet.of(h)
        val c = Conclusion(pf(b, emptyList(), Tail.STAR), e1, demand = false)
        val expected = Conclusion(pf(a, emptyList(), Tail.ANY), ExclusionSet.Empty, demand = true)

        // the reference form (ap.md §4.1)
        val ref = loadF.map { concat(c, it) }.filterIsInstance<EdgeOutcome.Fact>().map { it.conclusion }.filter { it.fact.base == a }
        assertEquals(listOf(expected), ref)

        // the tree form (ap.md §7.3): the same fact, the same layer, the kind FLOW, no request (Cases.lean:74)
        val premise = m.initial(b, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)     // the key IS the InitialAp (DD13)
        val tree = m.flowTree(b, Layer.NORMAL, e1, MarkSet.EMPTY, FlowAlgebra.LEAF_NODE)
        val out = CollectingOut()
        for (e in loadF) ops.applyEdge(tree, premise, e, statementEdge = true, run1, out)
        val onA = out.results.filter { it.base == a }
        assertEquals(listOf(Layer.DEMAND), onA.map { it.layer })
        assertTrue(onA.single() is FlowTree)                                                   // the mark `*` keeps the kind
        assertEquals(listOf(Pattern(expected.fact, ExclusionSet.Empty)), onA.flatMap { ops.leaves(it).toList() })
        assertTrue(out.markRequests.isEmpty() && out.positionRequests.isEmpty())
    }
}
```

Example 2 — `FactsEquivalenceTest`, the property that makes the tree form safe (`Tree.applyTreeE_mem` and its
extension to the mark gate and the kinds):

```kotlin
class FactsEquivalenceTest {
    private val gen = RandomFacts(seed = 42, accessors = 3, marks = 2, maxDepth = 3)   // a fresh accessor and mark are outside

    @Test
    fun `tree delta-concat equals the per-leaf reference concat`() = repeat(10_000) {
        val (facts, premise) = gen.facts()                        // a canonical Facts of a random kind and its premise (K6)
        val edge = gen.pathEdge()                                 // S7, S8 hold; every tail and mark
        val mode = gen.mode()                                     // run 1 or restricted (then only REACH and TAINT)
        val treeOut = CollectingOut()
        gen.ops.applyEdge(facts, premise, edge, statementEdge = true, mode, treeOut)

        val refOut = gen.asConclusions(facts).map { concat(it, edge, staticIdentity = gen.isStaticIdentity(facts, premise, it), restricted = mode.restricted) }
        assertEquals(refOut.facts().toSet(), treeOut.results.flatMap { gen.asConclusions(it) }.toSet())     // fact, layer, exclusion
        assertEquals(refOut.markRequests().toSet(), treeOut.markRequests.toSet())
        assertEquals(refOut.positionRequests().toSet(), treeOut.positionRequests.map { it.toList() }.toSet())
        treeOut.results.forEach { gen.assertKind(it) }            // FLOW <=> abstract mark; REACH <=> zero base; W1, W2, W6
    }
}
```

Example 3 — `SummaryKindsTest`, run 1 with a concrete summary premise and a `*` caller fact (§5.4, §5.10; item 9):

```kotlin
@Test
fun `a FLOW added fact does not satisfy a concrete premise and climbs`() {
    val t = m.marks.mark("T")
    val j = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.Concrete(t))   // the chain answer (x, [], *, {}, T)
    val a = m.flowTree(x, Layer.NORMAL, ExclusionSet.Empty, MarkSet.EMPTY, FlowAlgebra.LEAF_NODE)    // the added fact x.* (*)
    assertNull(ops.satisfying(a, j, run1))     // path and tail match; only markSub(T, *) is false: no application, no request

    val policyOfCallee = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)          // its rule raised T on it
    val caller = CallerRef(callerKey, m.initial(y, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR), Layer.NORMAL, call)
    val action = ops.requestAction(policyOfCallee, RequestKind.Mark(t), ops.leaves(a).single(), caller)
    assertTrue(action is RequestAction.Climb && action.premise === caller.premise)      // the caller premise gets the request
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
    FormApplier.kt        FormApplier, FactAlgebra, Place: the three application modes, once (§23.3)
    FormsReference.kt     ReferenceAlgebra (the per-path FactAlgebra), FormsReference (the oracle of the forms) (§23.8)
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
| `JVM/JIRFactTypeChecker.kt` | REUSE + GENERALIZE | REUSE `AccessorFilter` (:75-155) as `TypeFilter.may` (only its Field, Element and `<C>` cases run: `ap.md` W5); GENERALIZE: a new public member `localFilter(type)` builds it (today the class `AccessorFilter`, :75, is private, and only `filterFactByLocalType`, :177-183, and `accessPathFilter`, :185-188, build it); the mark policy moves to `TypeFilter.markPolicy`, one level per node of the `[e]` chain (§26.2) |
| `JVM/JIRLocalAliasAnalysis.kt` | REUSE | one per method in `JIRMethodEntry` |
| `JVM/JIRLocalVariableReachability.kt:18-22` | REUSE | only as an input of the alias analysis, as today (`JIRMethodEntry.aliasAnalysis`, §31.2). The forms have no liveness step (§32 D25) |
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
| `DF/util/SoftReferenceManager.kt` | NOT USED by Part II | the forms stay strongly held: their objects are keys of the run stores (§31.2). Part I holds the trie tables of the stores through it (DD5, Part I §4.5) |
| `core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringWebProject.kt:244-334` (`ndMethodDispatch`) | ADAPT | the dispatcher saves and restores the registry fields around `__cleanup__()` (§31.3) |
| `core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringRuleProvider.kt:104-128` (`cleanerRulesForMethod`) | ADAPT | with no fact: the whole-base cleaner `RemoveAllMarks(AnyClassStatic)`; with a fact: today's code (§31.3) |
| `core/opentaint-configuration-rules/configuration-rules-jvm/src/main/kotlin/org/opentaint/dataflow/configuration/jvm/Position.kt:7-19` | GENERALIZE | the rule position `AnyClassStatic` (§31.3) |

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
| `TypeFilter(may: FactTypeChecker.FactApFilter, markPolicy: MarkPolicy? = null)`, `fun interface MarkPolicy { fun keeps(mark: TaintMark, elements: Int): Boolean }`, `TypeFilter.and` | §5.5 (DD9) | `StatementSummary.typeFilters`, `resultFilters`; the policy of each level of the `[e]` chain (§26.2) |
| `ConjunctiveEdge(literals: List<Pattern>, target: PathFact)` | §5.8 | the ND sources (`interpreter.md` §5.3); a pass rule makes none (`interpreter.md` §4.2, D24) |
| `PathFact(base, path: List<AccessorIdx>, tail, mark)`, `Pattern(fact, exclusion)`, `PathEdge(from, to, exclusion)`, `Conclusion`, `EdgeOutcome`, `concat` | §6 (DD2) | the micro edges; `FormsReference` |
| `revEdge(e: PathEdge): PathEdge?` | §6 | every `reversed()` |
| `Cleaner(base, path: PathNode?, reach: CleanReach, mark: TaintMark?)`, `enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }` | §6 | `CleanStep.Clean`, the summary rewriter |
| `Facts` (`base`, `layer`), `Reach`, `FlowTree`, `TaintTree`, `Layer` | §7.2 of `ap.md`; Part I §3, §4 | the conclusions that the core applies the forms to (§23.3); `FormsReference.conclusions` |
| `PremiseKey` (`size`, `member(k)`, `isZero`, `nonZeroCount`), `InitialAp : PremiseKey` | §3.4 | `Origin.SUMMARY_EFFECT` (`j.isZero`), the zero premise of the exit rules (§29 step 4) |
| `MarkCheck` (`None`, `Request(mark)`, `Holds(facts, covered)`), `ApOps.checkMark(c: Facts, p: Pattern, mode)` | §5.8 | the patterns of a `SinkRule` and the literals of a `ConjunctiveEdge` (§23.3, §23.4, §29) |
| `ApOps.applyEdge(c, premise, e, statementEdge, mode, out)` (its internal tree step: `applyCompiledEdge`), `ApOut`, `ApMode`, `RequestKind`, `ApOps.leaves(f: Facts): Sequence<Pattern>`, `ApOps.targetTree(target, layer)`, `ApOps.without(c, part)`, `ApOps.startFact(j)`, `ConjunctionStore` (its k-ary join), `rootOrClass` | §3.2, §5, §6, §7.9, §7.10 | the application of a micro edge (§23.3, `EngineAlgebra` of `analyzer-impl.md`); `ReferenceAlgebra`, `FormsReference`; the end facts and the entry marks (§29); `Origin` |

### 22.2 Additions to the interface of `analyzer-core.md` §4.9

`analyzer-core.md` §4.9 gives the interpreter interface. Part II adds these members. `analyzer-impl.md` calls them.

| What | Why | Code |
|---|---|---|
| `StatementSummary.resultFilters` (default empty) | `interpreter.md` §2.1 step 5 and the binding-back filters of `interpreter.md` §3.1 act on the results. One map per base cannot hold the operand filter and the result filter of one base (`x = x.f`; `o.m(this)`). | §23.2 |
| `CallStage.Edges.kind: StageKind`, with the member `StageKind.statementEdges` | The core must find the sources stage (the source seeds and the source hits), the statement micro edges (the static exception of `ap.md` §4.10 item 1) and the `Origin` of a fact. | §23.5 |
| `Origin`; the `Guard` members `SinkTriggered(sink)` and `MemoryEffect` (`admits(origin)`) | Not an addition: `analyzer-core.md` §4.9 defines them with these members (and §4.5 THE ALIAS GUARD gives the rule). Part II gives the code and the `Origin` of each stage kind (`StageKind.originOf`, below). The alias guard needs the origin of a fact (`interpreter.md` §3.8 AC3, AC4). | §23.5 |
| `SinkRule.unconditional`, `conjunctive`, `seedPatterns()` | `analyzer-core.md` §4.9 defines `SinkRule(rule, alternative, patterns, endFacts)`; Part II adds these three derived members. `alternative` names the sink alternative of a witness (`ap.md` §8.10: the witnesses of two alternatives never merge). | §23.4 |
| `ExitRules.entryMarkParts(base)` | The core removes the entry marks of `interpreter.md` §4.7 step 4 exactly, with `ApOps.without`. | §23.4 |
| `MicroEdge.isSource`, `MicroEdge.isIdentity`, `StatementSummary.edgesOf`, `StatementSummary.targets`, `CallPlan.stagesFrom`, `identityEdge(b)` | The source-seed places (`analyzer-core.md` §4.7), the alias guard (AC4), the edges of one base, the target bases (A5), the stages from one point, the identity edge of `interpreter.md` A5, §3.5 and §3.7. | §23.1, §23.2, §23.6 |
| the stage `AFTER → BEFORE` of kind `PASS_OVER` in `CallPlan.reversed()` | The identity edge `b.* → b.*` of an alias base (`analyzer-core.md` §4.5, `interpreter.md` A5). The step table of `analyzer-core.md` §4.5 has no such stage (spec issue SI9). | §23.6 |
| `FormsCache`, `MethodForms`, `DirectedForms` | The forms cache of `analyzer-core.md` §4.8 and the direction table of `analyzer-core.md` §4.9. `analyzer-impl.md` §3.4 uses them. | §23.7 |
| `UnresolvedCallObserver` (`reached(call, position, plan)`); `JIRInterpreter` implements it; `CallPlan.passReads` | The external method tracker records the taint that reaches an unresolved callee, as today. `passReads`: the positions that a pass rule of the rule set reads (not a default model), for its `ruleApplied`. | §28.5, §23.6 |
| `FormApplier<P, F>` (`statement`, `stage`, `gen`), `FactAlgebra<P, F>`, `Place(node, statementEdge, sources)` | The three application modes belong to the forms; one implementation for the engine (`EngineAlgebra`, `analyzer-impl.md` §4.3) and both oracles. | §23.3 |
| `ReferenceAlgebra(mode, request, allowsSource, sourceHit, manager, conjunction)`, `FormsReference(ops, algebra)` (`applier`, `conclusions`, `apply`, `agrees`, `run(plan, inputs, at, hooks, from)`), `PlanItem(premise, c, origin)`, `PlanHooks(guards, atBound, callees, clean, exit)` | The per-path algebra on `Reference.kt`, with the static exception and the filter test, and the one per-path walk of a call plan; `NaiveClosure` (`analyzer-impl.md` §9.2) passes its hooks. | §23.8 |
| `StageKind.originOf(me, prev)`; `FormApplier.statement(..., untouched)` | The `Origin` rule of `interpreter.md` §3.8 AC3, AC4, once for the engine and the per-path walk; the unchanged path of the engine through the STATEMENT mode. | §23.3, §23.5 |

---

## 23. The common forms (`bidi.interp`)

Implements `analyzer-core.md` §4.9, `ap.md` §9.1, §9.2, `interpreter.md` §4.9.

### 23.1 Interpreter and micro edges

```kotlin
package org.opentaint.dataflow.bidi.interp

/** analyzer-core.md §4.9. The interpreter gives FORWARD forms only. It has no liveness member: the statement step keeps
 *  a fact on a dead local (`interpreter.md` §2.1 step 1, D25; Part II §32). */
interface Interpreter {
    fun entryNode(method: MethodKey): CommonInst
    fun exitNodes(method: MethodKey): List<ExitNode>
    fun entryRules(method: MethodKey): RuleStatement
    fun exitRules(method: MethodKey, exit: CommonInst): ExitRules
    fun statementSummary(method: MethodKey, statement: CommonInst): StatementSummary
    fun callPlan(caller: MethodKey, statement: CommonInst, call: CommonCallExpr): CallPlan
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
    val conjunctions: List<ConjunctiveEdge>,                                 // the ND sources only (interpreter.md §5.3)
    val typeFilters: Map<AccessPathBase, TypeFilter>,
    val resultFilters: Map<AccessPathBase, TypeFilter> = emptyMap(),          // an addition (Part II §22.2)
) {
    private val byBase: Map<AccessPathBase, List<MicroEdge>> = edges.groupBy { it.edge.from.base }
    fun edgesOf(b: AccessPathBase): List<MicroEdge> = byBase[b].orEmpty()

    /** The target bases of the forward edges: the micro edges and the conjunctive edges. */
    val targets: Set<AccessPathBase>
        get() = LinkedHashSet<AccessPathBase>().also { t ->
            edges.mapTo(t) { it.edge.to.base }; conjunctions.mapTo(t) { it.target.base }
        }

    /** ap.md §9.1, §9.2; interpreter.md §4.9 STATEMENTS; Lean `Reverse.Stmt.rev`. */
    fun reversed(): StatementSummary {
        val rev = ArrayList<MicroEdge>()
        for (e in edges) rev += MicroEdge(revOrFail(e.edge), e.forward)
        for (c in conjunctions) for (lit in c.literals) {                                  // an OR of the requirements
            val fwd = PathEdge(lit.fact, c.target, ExclusionSet.Empty)                    // a literal is a Pattern (Part I §5.8)
            rev += MicroEdge(revOrFail(fwd), fwd)
        }
        val back = StatementSummary(touched + targets, rev, emptyList(), emptyMap())      // no filter (§5.1 last rows)
        return back.withIdentities(passOverBases(targets, touched))                     // A5
    }

    /** The identity edges of `bases`, added to this summary (touched too). */
    fun withIdentities(bases: Collection<AccessPathBase>): StatementSummary =
        if (bases.isEmpty()) this
        else StatementSummary(touched + bases, edges + bases.map(::identityEdge), conjunctions, typeFilters, resultFilters)

    companion object {
        val EMPTY = StatementSummary(emptySet(), emptyList(), emptyList(), emptyMap())
        /** A summary of identity edges only (STAGE mode: every base of an edge is touched). */
        fun identities(bases: Collection<AccessPathBase>) = EMPTY.withIdentities(bases)
    }
}

/** I11 (b): every statement micro edge is mark-reversible; a binding has `*` marks (S10). */
internal fun revOrFail(e: PathEdge): PathEdge = revEdge(e) ?: error("not mark-reversible (interpreter.md I11 (b)): $e")   // revEdge: Part I §6

/** THE IDENTITY OF A REVERSAL (interpreter.md A5, §4.9; ap.md §9.2; Lean `Reverse.idEdge`, `revNoId_breaks`). A forward
 *  target base that the forward form does not touch keeps its old value (a weak, gen-only target), so the reversed form
 *  keeps the requirement on it by `b.* -> b.*`. The one helper of the three reversals: `StatementSummary.reversed` (the
 *  alias targets of a write), `RuleStatement.reversed` (the end-fact targets), `CallPlan.reversed` (the alias bases of a
 *  call: the stage PASS_OVER). */
internal fun passOverBases(targets: Iterable<AccessPathBase>, touched: Set<AccessPathBase>): Set<AccessPathBase> =
    targets.filterTo(LinkedHashSet()) { it !in touched }

/** `b.* -> b.*`: the identity edge of A5, of the default identity of an unresolved callee (interpreter.md §3.7) and of the
 *  constructor pass-over (§3.5). */
fun identityEdge(b: AccessPathBase): MicroEdge = MicroEdge.of(keepEdge(b))
```

### 23.3 The three application modes: `FormApplier`

The core applies a `StatementSummary` in one of three modes. The mode comes from the place of the form, not from a
field.

| Mode | Forms | Rule |
|---|---|---|
| STATEMENT | `statementSummary`, `RuleStatement.summary`, `CleanStep.Kill.keepEdges` | `interpreter.md` §2.1 steps 2–5: an untouched base passes; a touched base keeps only what an edge gives |
| STAGE | `CallStage.Edges.summary` | only the edges give results; the plan relevance (`CallPlan.touched`) does the pass-over (`analyzer-core.md` §4.5). A stage summary has every base of its edges in `touched`, so `reversed()` adds no identity edge |
| GEN | `RuleStatement.endFacts`, `SinkRule.endFacts` | the input stays where it is; the edges add results (`interpreter.md` §4.1 END FACTS, §4.7 step 2) |

ONE FORM APPLIER. `FormApplier` writes the three modes once, generic over the fact algebra `FactAlgebra<P, F>` (`P`:
the premise set; `F`: the facts of one input). Users, each with its own algebra:

| User | Algebra | Facts |
|---|---|---|
| the engine (`RunMethodAnalyzer`, `analyzer-impl.md` §4.3) | `EngineAlgebra` (`analyzer-impl.md` §4.3): `ApOps` on `Facts`, premise `PremiseKey` | the trees of `ap.md` §7.2 |
| the closure oracle (`NaiveClosure`, `analyzer-impl.md` §9.2) | `ReferenceAlgebra` (§23.8), one per method, with the hooks of the closure: its requests, seeds, hits and joins | per-path `Conclusion`s |
| the oracle of the forms (`FormsReference`, §23.8) | `ReferenceAlgebra` | per-path `Conclusion`s |

So the engine and both oracles share the mode logic and differ only in the algebra.

```kotlin
package org.opentaint.dataflow.bidi.interp          // FormApplier.kt

/** Where a form applies. `statementEdge`: the static exception of ap.md §4.10 item 1 (run 1, a statement micro edge:
 *  StageKind.statementEdges, a CleanStep.Kill, a statement summary). `sources`: a source-seed place (§23.1). */
data class Place(val node: CommonInst, val statementEdge: Boolean, val sources: Boolean)

/** The operations that the three modes read. P: the premise set; F: the facts of one input. */
interface FactAlgebra<P, F> {
    fun base(c: F): AccessPathBase
    fun filter(c: F, filter: TypeFilter): F?                                   // null: the filter rejects every fact
    fun applyEdge(me: MicroEdge, c: F, premise: P, statementEdge: Boolean, out: (P, F) -> Unit)
    fun conjunction(cj: ConjunctiveEdge, premise: P, c: F, node: CommonInst, out: (P, F) -> Unit)
    fun allowsSource(node: CommonInst, me: MicroEdge): Boolean                 // the source-seed filter (analyzer-core.md §4.7)
    fun sourceHit(node: CommonInst, me: MicroEdge)                             // backward: ap.md §8.11
}

/** The three application modes, once. */
class FormApplier<P, F>(private val alg: FactAlgebra<P, F>) {
    /** STATEMENT (interpreter.md §2.1 steps 2-5): an untouched base passes; a touched base gets the operand filters, the
     *  edges of its base (the kill) and the result filters. A statement summary, RuleStatement.summary, CleanStep.Kill.
     *  `untouched`: where an untouched input goes (the engine: the unchanged path with no `edges.add`, analyzer-core.md
     *  §4.3; default: with the results). A conjunction literal READS its base and does not kill it, so the conjunctions
     *  also see an untouched input (an untouched base has no operand filter); a touched input meets them in `stage`. */
    fun statement(s: StatementSummary, premise: P, c: F, at: Place, sink: (P, F) -> Unit,
                  untouched: (P, F) -> Unit = sink) {
        if (alg.base(c) !in s.touched) {
            for (cj in s.conjunctions) alg.conjunction(cj, premise, c, at.node, sink)
            untouched(premise, c); return
        }
        stage(s, premise, c, at) { pr, x, _ -> sink(pr, x) }
    }

    /** STAGE: only the edges, with the operand filters on the input and the result filters on the results.
     *  CallStage.Edges.summary; the plan relevance (CallPlan.touched) does the pass-over. Each result comes with the
     *  micro edge that made it (null: a conjunction), so the plan runner reads its Origin (§23.5). */
    fun stage(s: StatementSummary, premise: P, c: F, at: Place, emit: (P, F, MicroEdge?) -> Unit) {
        val input = filterBy(s.typeFilters, c) ?: return                                       // operand filters
        for (me in s.edgesOf(alg.base(input)))
            micro(me, input, premise, at) { pr, x -> filterBy(s.resultFilters, x)?.let { emit(pr, it, me) } }   // result filters
        for (cj in s.conjunctions) alg.conjunction(cj, premise, input, at.node) { pr, x -> emit(pr, x, null) }
    }

    /** GEN: the edges add results; the input stays where it is; no filter; never a source-seed place (§23.1).
     *  RuleStatement.endFacts, SinkRule.endFacts. */
    fun gen(edges: List<MicroEdge>, premise: P, c: F, sink: (P, F) -> Unit) {
        for (me in edges) if (me.edge.from.base == alg.base(c)) alg.applyEdge(me, c, premise, statementEdge = false, sink)
    }

    private fun filterBy(filters: Map<AccessPathBase, TypeFilter>, c: F): F? {
        val f = filters[alg.base(c)] ?: return c
        return alg.filter(c, f)                                                // Part I §5.5: may, then the mark policy
    }

    /** One micro edge. At a source-seed place, the source-seed filter acts before it (a forward restricted run), and the
     *  source hit is recorded after a result (a backward run), BEFORE any edges.add (analyzer-core.md §4.7). */
    private fun micro(me: MicroEdge, c: F, premise: P, at: Place, sink: (P, F) -> Unit) {
        val source = at.sources && me.isSource
        if (source && !alg.allowsSource(at.node, me)) return
        var produced = false
        alg.applyEdge(me, c, premise, at.statementEdge) { pr, x -> produced = true; sink(pr, x) }
        if (source && produced) alg.sourceHit(at.node, me)
    }
}
```

The engine applies one micro edge with the public `ApOps.applyEdge(c, premise, e, statementEdge, mode, out)` (Part I
§5.3; it is `EngineAlgebra.applyEdge`). Its internal tree step is `applyCompiledEdge`, the tree form of the delta-concat
of `ap.md` §4.1. The kind of the result follows from the edge and the input (`ap.md` §7.2): the zero keep edge keeps
`Reach`; an edge from the zero fact (a source, an end fact) gives a TAINT tree; a `*`-to-`*` edge keeps the kind of its
input (FLOW or TAINT); an edge with a concrete premise mark gives TAINT from TAINT, and only the request from FLOW
(run 1). A conjunctive edge does not go through `applyEdge` (`FactAlgebra.conjunction`): the engine checks each literal
with `ApOps.checkMark` (Part I), and each `MarkCheck.Holds` (with its `covered` part, for the layer of `ap.md` §4.6) is one
input of the k-ary join (`ConjunctionStore`, Part I §7.10); a full combination gives the target as a TAINT tree
(`ApOps.targetTree`). Its premise set is the union of the premise sets of the inputs without the zero fact, or `{zero}`
if every input has `{zero}` (`interpreter.md` §5.3, `ap.md` §4.6), so a premise set with two or more members is an ND
edge, and an ND edge is always TAINT. Only an ND source makes a conjunctive edge: a pass rule makes none
(`interpreter.md` §4.2, D24).

### 23.4 Sinks, rule statements, exit rules, clean steps

```kotlin
/** One alternative (one DNF cube) of one sink rule at one place (interpreter.md §4.1, §4.2; ap.md §4.9). The core checks
 *  each pattern with `ApOps.checkMark(c, pattern, mode)` (Part I): `MarkCheck.Holds` triggers the pattern,
 *  `MarkCheck.Request` raises the request (run 1: a FLOW fact that may carry the mark), `MarkCheck.None` does nothing.
 *  A plain sink triggers on `Holds`; a conjunctive sink gives each `Holds` to the k-ary join of its literals
 *  (`ConjunctionStore`, Part I §7.10), and a full combination triggers it. An unconditional sink has `ZERO_PATTERN`,
 *  which holds on the `Reach` conclusion (the zero fact). The same check serves the literals of a conjunctive edge
 *  (§23.3).
 *  `alternative`: the index of this alternative among the alternatives of `rule` at its place (the cube and the array
 *  choice, in the order of `JIRRuleForms.sinks`, Part II §27.3). The forms are the same in every run and every context
 *  (`interpreter.md` I5), so the index is stable across runs and contexts. The vulnerability store keeps the witnesses
 *  of two alternatives apart (`ap.md` §8.10; `SinkWitness.alternative`); it never reads the identity of the object. */
class SinkRule(
    val rule: CommonTaintConfigurationSink,
    val alternative: Int,
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
        val revEnd = StatementSummary(emptySet(), endFacts.edges.map { MicroEdge(revOrFail(it.edge), it.forward) },
            emptyList(), emptyMap())
        return RuleStatement(s.withIdentities(passOverBases(endFacts.targets, s.touched)), revEnd, sinks)
    }
    companion object { val EMPTY = RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, emptyList()) }
}

/** interpreter.md §4.7, at an exit (normal or exceptional). `globalStateDrop`: step 3 applies (the exit has an exit sink):
 *  the part of an `S` item on which a mark literal of an exit sink holds is dropped (Part II §29). `entryMarks`: step 4.
 *  Steps 3 to 5 apply only at the normal exit, so at the exceptional exit `globalStateDrop` is false and `entryMarks` is
 *  empty. */
class ExitRules(val rules: RuleStatement, val globalStateDrop: Boolean, val entryMarks: Set<TaintMark>) {
    /** interpreter.md §4.9: the reversal drops G2 (steps 3 and 4). */
    fun reversed(): RuleStatement = rules.reversed()

    /** interpreter.md §4.7 step 4, "as today" (`JIRMethodSequentFlowFunction.kt:300-314`): today `TaintMarkRemover`
     *  rejects only a mark child of the ROOT and accepts every other child with its whole subtree. So only the `$` leaf
     *  `(b, [], $, T)` of an entry mark goes; `b.f.$ (T)` and `b.[any] (T)` stay. The core removes each part with
     *  `ops.without(tree, ops.targetTree(part, tree.layer))` (Part I §5.8) on the item, a TAINT tree (a zero premise has
     *  concrete marks, ap.md §7.2): exact, the other leaves stay in their layer.
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
 *  the fact and keeps it through the rewriter. Only a COMPLETE identity result skips the aliases: an incomplete
 *  (DEMAND-layer) summary result always goes to the aliases, also when it equals its start fact (the start of a W2
 *  premise can be coarser than the premise, so the alias does not hold it). */
enum class Origin {
    SOURCE,          // StageKind.SOURCES                                                       (AC3)
    END_FACT,        // StageKind.END_FACTS                                                     (AC3)
    PASS,            // StageKind.UNRESOLVED, an edge that is not `isIdentity`                  (AC3)
    SUMMARY_EFFECT,  // a summary or record result j -> g that is not IDENTITY: a DEMAND-layer result (always),
                     // a NORMAL-layer g != ops.startFact(j), every j with j.isZero                (AC3)
    IDENTITY,        // a COMPLETE identity summary result: layer NORMAL and g == ops.startFact(j) (only then);
                     // an identity edge of UNRESOLVED; StageKind.CONSTRUCTOR                      (AC4)
}

/** interpreter.md §3.8 AC3, AC4: the Origin of a result of an `Edges` stage of this kind, made by the micro edge `me`
 *  (null: a conjunction result, from an ND source), from an input with the Origin `prev`. The bindings and the aliases keep `prev`; the
 *  cleaners and the rewriter keep it too (they are not `Edges` stages). The callees stage gives SUMMARY_EFFECT or IDENTITY
 *  by the summary (above). Users: the plan runner of the engine (analyzer-impl.md §4.5), `FormsReference.run` (§23.8). */
fun StageKind.originOf(me: MicroEdge?, prev: Origin?): Origin? = when (this) {
    StageKind.SOURCES -> Origin.SOURCE
    StageKind.END_FACTS -> Origin.END_FACT
    StageKind.UNRESOLVED -> if (me?.isIdentity == true) Origin.IDENTITY else Origin.PASS
    StageKind.CONSTRUCTOR -> Origin.IDENTITY
    else -> prev
}

/** A forward-only selection of the inputs of a stage (analyzer-core.md §4.9). The reversal drops it. */
sealed interface Guard {
    /** interpreter.md §4.1 END FACTS. The sink TRIGGERS at BOUND: for a plain sink, `checkMark` gives `MarkCheck.Holds` on
     *  a bound fact of the caller edge `(i, layer)` (the layer of that sink edge); for a conjunctive sink, the k-ary join
     *  gives a new full combination (the layer of the combination; ap.md §4.9, §8.9). Then the core applies the stage to
     *  the ZERO fact (the `Reach` conclusion), with that layer: `Zero -> (s, P.$ (T))`, a TAINT conclusion (the end fact
     *  has a concrete mark; ap.md §7.2). Each result goes to REWRITTEN with `Origin.END_FACT`. */
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
/** `passReads`: the callee positions that a pass rule of the rule set reads at an unresolved callee (not the default
 *  identity, not a default model such as the JVM default getter rules). Only the `UnresolvedCallObserver` reads it
 *  (Part II §28.5); it has no effect on facts. */
class CallPlan(val touched: Set<AccessPathBase>, val stages: List<CallStage>, val sinks: List<SinkRule>,
               val entry: CallPoint, val exit: CallPoint, val passReads: Set<AccessPathBase> = emptySet()) {
    /** analyzer-core.md §4.5: the stages from one point read the same facts; their order does not matter. */
    val stagesFrom: Map<CallPoint, List<CallStage>> = stages.groupBy { it.from }

    /** analyzer-core.md §4.5 THE REVERSAL; Lean `Reverse.Call.rev` (toCallee and fromCallee swap and reverse). */
    fun reversed(): CallPlan {
        check(entry == CallPoint.BEFORE && exit == CallPoint.AFTER) { "the core reverses only a forward plan" }
        val exitTargets = stages.filter { it.to == exit }.filterIsInstance<CallStage.Edges>().flatMap { it.summary.targets }
        val aliasBases = passOverBases(exitTargets, touched)                            // the A5 helper (Part II §23.2)
        val rev = stages.mapTo(ArrayList()) { it.reversed() }
        // Forward, an alias base is untouched: its fact passes over the call. Backward, it is touched (for the reversed
        // alias edges), so its requirement passes over by an explicit identity stage from the entry to the exit (A5).
        if (aliasBases.isNotEmpty())
            rev += CallStage.Edges(CallPoint.AFTER, CallPoint.BEFORE, StageKind.PASS_OVER, StatementSummary.identities(aliasBases))
        return CallPlan(touched + aliasBases, rev, sinks, entry = exit, exit = entry, passReads = passReads)
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
    // No liveness member: no run drops a fact on a dead local (interpreter.md §2.1 step 1, D25; Part II §32).
}
```

### 23.8 The per-path algebra and the oracle of the forms

`ReferenceAlgebra` is the `FactAlgebra` of the per-path reference forms (Part I `Reference.kt`, DD2): one `Conclusion`
per fact and a premise SET of patterns. It applies a micro edge with `concat` of `ap.md` §4.1 (`ApOps.applyEdge` is its
tree form), with the static exception of run 1 inside it, and it reads a type filter as `ApOps.filter` reads it
(Part I §5.5, DD9): `may` on the path, then the mark policy on a concrete mark at the root path or at `[e]^k` (the
policy of level `k`). The constructor takes the
mode of the run and the hooks of the user: `request` (run 1: a mark request, and the position request of the static
exception), `allowsSource` (the source-seed filter), `sourceHit` (the source hits), `conjunction` (the standing join of a
conjunctive edge, that is of an ND source; the premise set of its result drops the zero fact, `interpreter.md` §5.3).
`manager` decodes the accessors for the filter and makes the path of a position request. The defaults
do nothing; `NaiveClosure` (`analyzer-impl.md` §9.2) passes its own.

`FormsReference` is the oracle of the forms: `FormApplier` over a `ReferenceAlgebra`, plus `conclusions` (the per-path
view of a `Facts`), `agrees` (the core result and the reference result denote the same locations in each layer) and
`run`, THE ONE PER-PATH WALK OF A CALL PLAN. It has no mode logic of its own. `run` carries the `Origin` of each item
(`StageKind.originOf`, §23.5) and takes `PlanHooks`: the forward guards (the sink trigger of `END_FACTS`, the alias
selection by `Origin`), the sink check at `BOUND`, the callees stage, the cleaners and the field limit at the exit point.
With the default hooks it is the walk of the forms tests (§33.3). The closure oracle (`analyzer-impl.md` §9.2) calls it
with its own hooks and one `FormsReference` per method, so it has no walk of its own. The engine keeps its own plan
runner (`analyzer-impl.md` §4.5): it is the code under test; it shares `FormApplier` and `originOf`.

```kotlin
package org.opentaint.dataflow.bidi.interp          // FormsReference.kt

typealias ReferenceSink = (Set<Pattern>, Conclusion) -> Unit

/** The per-path fact algebra. Users: FormsReference (below); NaiveClosure (analyzer-impl.md §9.2), one per method. */
class ReferenceAlgebra(
    private val mode: ApMode,                                                     // run1, restricted (Part I §3.2)
    request: (Set<Pattern>, RequestKind) -> Unit = { _, _ -> },                   // reqStmt, sreqStmt (run 1)
    allowsSource: (CommonInst, MicroEdge) -> Boolean = { _, _ -> true },          // the source seeds (analyzer-core.md §4.7)
    sourceHit: (CommonInst, MicroEdge) -> Unit = { _, _ -> },                     // srcHit (ap.md §8.11)
    private val manager: ApManager,                                               // the accessors of the filter; a position path
    conjunction: (ConjunctiveEdge, Set<Pattern>, Conclusion, CommonInst, ReferenceSink) -> Unit = { _, _, _, _, _ -> },  // conj: ND sources
) : FactAlgebra<Set<Pattern>, Conclusion> {
    private val onRequest = request
    private val seedAllows = allowsSource
    private val onHit = sourceHit
    private val join = conjunction

    override fun base(c: Conclusion) = c.fact.base

    override fun filter(c: Conclusion, filter: TypeFilter): Conclusion? = c.takeIf { passes(filter, it) }

    override fun applyEdge(me: MicroEdge, c: Conclusion, premise: Set<Pattern>, statementEdge: Boolean, out: ReferenceSink) {
        val identity = mode.run1 && statementEdge && isStaticIdentity(premise, c)     // ap.md §4.1, the static exception
        when (val o = concat(c, me.edge, staticIdentity = identity, restricted = mode.restricted)) {   // Reference.kt
            is EdgeOutcome.Fact -> out(premise, o.conclusion)
            is EdgeOutcome.Request -> onRequest(premise, RequestKind.Mark(o.mark))                   // reqStmt
            is EdgeOutcome.PositionRequest -> onRequest(premise, RequestKind.Position(manager.path(o.path)!!))   // sreqStmt
            EdgeOutcome.None -> Unit
        }
    }

    override fun conjunction(cj: ConjunctiveEdge, premise: Set<Pattern>, c: Conclusion, node: CommonInst, out: ReferenceSink) =
        join(cj, premise, c, node, out)
    override fun allowsSource(node: CommonInst, me: MicroEdge) = seedAllows(node, me)
    override fun sourceHit(node: CommonInst, me: MicroEdge) = onHit(node, me)

    /** As ApOps.filter (Part I §5.5): `may` on the path, then the mark policy on a concrete mark at the root path or at
     *  `[e]^k` below the base (`markPolicyKeeps` of interpreter.md §5.1: level k). A leaf off the `[e]` chain stays. */
    fun passes(filter: TypeFilter, c: Conclusion): Boolean {
        var may: FactTypeChecker.FactApFilter = filter.may
        for (a in c.fact.path) when (val r = may.check(manager.accessors.accessor(a))) {
            FactTypeChecker.FilterResult.Accept -> break
            FactTypeChecker.FilterResult.Reject -> return false
            is FactTypeChecker.FilterResult.FilterNext -> may = r.filter
        }
        val mark = (c.fact.mark as? MarkSlot.Concrete)?.mark ?: return true
        val policy = filter.markPolicy ?: return true
        if (c.fact.path.any { it != ELEMENT_ACCESSOR_IDX }) return true                // off the `[e]` chain
        return policy.keeps(mark, elements = c.fact.path.size)
    }

    /** ap.md §4.1 static exception, conditions 1 and 2: the edge `premise -> c` is an identity static `*` edge, premise
     *  `{(S, q, */E0, *)}` and `c = (S, q, */Ec, *)` or `*∖X` at the same `q`, normal layer, `rootOrClass(q)`. */
    private fun isStaticIdentity(premise: Set<Pattern>, c: Conclusion): Boolean {
        val i = premise.singleOrNull()?.fact ?: return false
        val f = c.fact
        return i.base == AccessPathBase.ClassStatic && f.base == AccessPathBase.ClassStatic &&
            i.tail == Tail.STAR && f.tail == Tail.STAR && i.mark == MarkSlot.STAR && f.mark is MarkSlot.Star &&
            f.path == i.path && !c.demand && rootOrClass(i.path)                    // rootOrClass: Reference.kt
    }
}

/** One fact of a per-path plan walk: its premise set, its conclusion and its Origin (interpreter.md §3.8 AC3, AC4). */
data class PlanItem(val premise: Set<Pattern>, val c: Conclusion, val origin: Origin?)

/** The hooks of a per-path plan walk. The defaults give the walk of the forms tests: no guard, no sink, no limit, the
 *  callees give nothing, a cleaner keeps the fact. The closure oracle (analyzer-impl.md §9.2) passes its own. */
class PlanHooks(
    /** The forward guards (analyzer-core.md §4.5): `Guard.SinkTriggered` and `Guard.MemoryEffect`. Off in a backward walk
     *  (a reversed plan has no guard) and in the forms tests. */
    val guards: Boolean = false,
    /** The rule point BOUND of a forward walk: the hook checks the sinks of the plan on the items (it records the witness
     *  or the request) and gives each sink that triggered with the layer of its sink edge (a conjunctive sink: of the new
     *  combination). The END_FACTS stage of a fired sink applies to the zero fact with that layer. */
    val atBound: (List<PlanItem>) -> List<Pair<SinkRule, Layer>> = { emptyList() },
    /** The callees stage: the closure adds a link per callee and gives nothing now (a summary resumes the walk at
     *  `RETURNED`, `run(from = RETURNED)`); a forms test gives the callee results. */
    val callees: (CallStage.Callees, PlanItem) -> List<PlanItem> = { _, _ -> emptyList() },
    /** One cleaner on one item (`cleanRes` of Reference.kt; the closure also records the request of a `part`). */
    val clean: (Cleaner, PlanItem) -> List<PlanItem> = { _, it -> listOf(it) },
    /** The exit point: the field limit of the run (`limit` of Reference.kt; ap.md §4.4 rows 2, 3, 6). */
    val exit: (PlanItem) -> PlanItem = { it },
)

/** The oracle of the forms: FormApplier over a ReferenceAlgebra (the same mode logic as the engine, §23.3), and the one
 *  per-path walk of a call plan. Users: the forms tests (§33), and the closure oracle (analyzer-impl.md §9.2), with one
 *  FormsReference per method over the ReferenceAlgebra with its hooks. */
class FormsReference(
    private val ops: ApOps,
    algebra: ReferenceAlgebra = ReferenceAlgebra(ApMode(run1 = true, Direction.FORWARD, fieldLimit = Int.MAX_VALUE),
        manager = ops.manager),
) {
    val applier = FormApplier(algebra)
    private val zeroPremise = setOf(ZERO_PATTERN)

    /** The per-path view of a conclusion of the core: one Conclusion per leaf and mark (`ApOps.leaves`, Part I). */
    fun conclusions(f: Facts): List<Conclusion> {
        val demand = f.layer == Layer.DEMAND
        return when (f) {
            is Reach -> listOf(Conclusion(ZERO_FACT, ExclusionSet.Empty, demand))
            else -> ops.leaves(f).map { Conclusion(it.fact, it.exclusion, demand) }.toList()
        }
    }

    enum class Mode { STATEMENT, STAGE, GEN }
    /** `premise`: the premise set of the input edge as patterns (the members of its `PremiseKey`). The static exception
     *  of run 1 reads it (`ReferenceAlgebra.isStaticIdentity`, ap.md §4.1), as the core reads the premise of its edge. */
    fun apply(mode: Mode, s: StatementSummary, premise: Set<Pattern>, c: Conclusion, at: Place): List<Conclusion> = buildList {
        when (mode) {
            Mode.STATEMENT -> applier.statement(s, premise, c, at, { _, x -> add(x) })
            Mode.STAGE -> applier.stage(s, premise, c, at) { _, x, _ -> add(x) }
            Mode.GEN -> applier.gen(s.edges, premise, c) { _, x -> add(x) }
        }
    }

    /** The core applied `s` in `mode` to `input` (on an edge with the premise set `premise`) and gave `core`. Each
     *  reference result is covered by a core leaf of its layer, and each core leaf by a reference result (`covers`,
     *  ap.md §3.4): the same locations, also when the core merged leaves (T1) or folded them under an `[any]` leaf (T5).
     *  A request that the reference raises is checked by the caller with the `request` hook of the algebra. */
    fun agrees(mode: Mode, s: StatementSummary, at: Place, premise: Set<Pattern>, input: Facts, core: List<Facts>): Boolean {
        val ref = conclusions(input).flatMap { apply(mode, s, premise, it, at) }
        val got = core.flatMap(::conclusions)
        fun Conclusion.p() = Pattern(fact, exclusion)
        return ref.all { r -> got.any { g -> g.demand == r.demand && covers(g.p(), r.p()) } } &&
            got.all { g -> ref.any { r -> r.demand == g.demand && covers(r.p(), g.p()) } }
    }

    /** THE PER-PATH WALK OF A CALL PLAN (analyzer-core.md §4.5; interpreter.md §4.5, §4.9). From `from` (the entry point:
     *  the relevance test of step 1, and the zero fact passes over AND enters), each item goes through every stage from its
     *  point; each `Edges` stage applies its summary in STAGE mode at `at` (`statementEdge` and `sources` by its kind), and
     *  the result gets `kind.originOf`; `Clean` and `Rewrite` fold their steps; `Callees` calls the hook. An item at the
     *  exit point goes through `hooks.exit`. Gives every (point, item) that the walk reaches. */
    fun run(plan: CallPlan, inputs: List<PlanItem>, at: Place, hooks: PlanHooks = PlanHooks(),
            from: CallPoint = plan.entry): List<Pair<CallPoint, PlanItem>> {
        val seen = LinkedHashSet<Pair<CallPoint, PlanItem>>()
        val work = ArrayDeque<Pair<CallPoint, List<PlanItem>>>()
        val start = ArrayList<PlanItem>()
        for (i in inputs) when {
            from != plan.entry -> start += i
            i.c.fact.base == AccessPathBase.Zero -> { seen += plan.exit to hooks.exit(i); start += i }   // passes over AND enters
            i.c.fact.base !in plan.touched -> seen += plan.exit to hooks.exit(i)                         // relevance (step 1)
            else -> start += i
        }
        if (start.isNotEmpty()) work.addLast(from to start)
        while (work.isNotEmpty()) {
            val (p, batch) = work.removeFirst()
            val items = batch.filter { seen.add(p to it) }
            if (items.isEmpty() || p == plan.exit) continue
            val fired = if (hooks.guards && p == CallPoint.BOUND) hooks.atBound(items) else emptyList()
            for (st in plan.stagesFrom[p].orEmpty()) {
                val out = ArrayList<PlanItem>()
                when (st) {
                    is CallStage.Edges -> {
                        val place = at.copy(statementEdge = st.kind.statementEdges, sources = st.kind == StageKind.SOURCES)
                        val guard = if (hooks.guards) st.guard else null
                        when {
                            guard is Guard.SinkTriggered ->                                     // END_FACTS: the zero fact, the fired layer
                                for ((sink, layer) in fired) if (sink === guard.sink) {
                                    val zero = Conclusion(ZERO_FACT, ExclusionSet.Empty, demand = layer == Layer.DEMAND)
                                    applier.stage(st.summary, zeroPremise, zero, place) { pr, x, me ->
                                        out += PlanItem(pr, x, st.kind.originOf(me, null)) }
                                }
                            else -> for (i in items) {
                                if (guard == Guard.MemoryEffect && !Guard.MemoryEffect.admits(checkNotNull(i.origin))) continue   // AC3, AC4
                                applier.stage(st.summary, i.premise, i.c, place) { pr, x, me ->
                                    out += PlanItem(pr, x, st.kind.originOf(me, i.origin)) }
                            }
                        }
                    }
                    is CallStage.Clean -> for (i in items) out += st.steps.fold(listOf(i)) { fs, step -> fs.flatMap { x ->
                        when (step) {
                            is CleanStep.Clean -> hooks.clean(step.cleaner, x)
                            is CleanStep.Kill -> buildList { applier.statement(step.keepEdges, x.premise, x.c,
                                at.copy(statementEdge = true, sources = false), { pr, y -> add(PlanItem(pr, y, x.origin)) }) }
                        } } }
                    is CallStage.Rewrite -> for (i in items) out += st.cleaners.fold(listOf(i)) { fs, cl -> fs.flatMap { hooks.clean(cl, it) } }
                    is CallStage.Callees -> for (i in items) out += hooks.callees(st, i)
                }
                val next = if (st.to == plan.exit) out.map(hooks.exit) else out
                if (next.isNotEmpty()) work.addLast(st.to to next)
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
    /** `b` keeps its value: touched, with `b.* -> b.*`. Users: move, read, write (below); the entry rules (a base with a
     *  context filter) and the exit rules (a read base), Part II §29. */
    fun keep(b: AccessPathBase) { touch(b); edge(keepEdge(b)) }
    /** interpreter.md I11 (d): a form that touches the zero base keeps the zero fact. Users: the read sources (§27.2), the
     *  sources stage of a call (§28.3), the entry rules and the exit rules (§29). */
    fun keepZero() { touch(AccessPathBase.Zero); edge(ZERO_KEEP) }
    /** interpreter.md §5.1: two filters on one base are a conjunction (`TypeFilter.and`, DD9). */
    fun operandFilter(b: AccessPathBase, f: TypeFilter?) { if (f != null) operand.merge(b, f) { x, y -> x.and(y) } }
    fun resultFilter(b: AccessPathBase, f: TypeFilter?) { if (f != null) result.merge(b, f) { x, y -> x.and(y) } }

    /** `x = y`, `x = c`, `return v`, `throw t`; `from == null`: the kill (`x = new T`, ...). Today :67-72. */
    fun move(to: AccessPathBase, from: AccessPathBase?, toPath: List<AccessorIdx> = emptyList()) {
        touch(to)
        if (from == null) return
        keep(from)                                                                // y.* -> y.*
        if (from != to || toPath.isNotEmpty()) edge(starEdge(from, emptyList(), to, toPath))   // y.* -> x.*
    }

    /** `x = y.p` (I3: a read adds no exclusion). Today :74-92 kept every prefix except `p` and refined (D1, D2, D3). */
    fun read(to: AccessPathBase, base: AccessPathBase, path: List<AccessorIdx>) {
        touch(to); touch(base)
        if (base != to) keep(base)                                                  // y.* -> y.*        (D1)
        edge(starEdge(base, path, to, emptyList()))                                // y.p.* -> x.*      (D2 when base == to)
    }

    /** `b.p = v`: a strong write keeps every prefix except the written accessor (I3); a weak write keeps `b`.
     *  A2, A3: `v.* -> c.q.p.*` for each alias `(c, q)` of `b`; `c` is not touched. Today :94-121. */
    fun write(base: AccessPathBase, path: List<AccessorIdx>, weak: Boolean, values: List<AccessPathBase>,
              aliasPaths: List<Pair<AccessPathBase, List<AccessorIdx>>>) {
        touch(base)
        if (weak) keep(base) else strongKeep(base, path).forEach { edge(it) }
        for (v in values) {
            if (v != base) keep(v) else touch(v)
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

    /** DD6: a JIR accessor as a path element. The JIR builders make only `FieldAccessor`, `ElementAccessor` and
     *  `ClassStaticAccessor` (ap.md W5; interpreter.md §1.2): from `MethodFlowFunctionUtils.mkAccess` (JVM/MethodFlowFunctionUtils.kt:37-63),
     *  `PositionAccessor.toApAccessor` (JVM/taint/TaintEvaluator.kt:103-107; `AnyField` is a tail, §27.1) and
     *  `AliasAccessor.apAccessor` (JVM/analysis/JIRAliasUtil.kt:77-81). The type-info accessors of the prescan
     *  (`TypeInfoSequentFlowFunction`, JVM/analysis/JIRMethodCallResolver.kt:145-157) and `ValueAccessor` never reach
     *  here; `AccessorTable.index` rejects them (Part I §3.1). */
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

    // No liveness member (interpreter.md §2.1 step 1, D25): today's isReachable (JIRLocalVariableReachability.kt:27-31)
    // is not called. The alias analysis keeps its own reachability input (Part II §31.2).

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
            from is MemoryAccess -> {
                check(to !is MemoryAccess) { "Complex assignment: $lhv = $rhv" }       // as today, JIRStatementSummary.kt:82
                read(to.base, from.base, path(from))
            }
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
(`JVM/JIRFactTypeChecker.kt:75-155`). A path of the new analysis has only `FieldAccessor`, `ElementAccessor` and
`ClassStaticAccessor` (`ap.md` W5; `interpreter.md` §1.2). On them the cases of `checkAccessor` (:84-136) are the
`may(t, p)` of `interpreter.md` §5.1: Field: the declaring class, deeper fields not checked; Element: the array type,
then `FilterNext(element type)`, `Object`: accept; `<C>`: accept. The other cases of `checkAccessor` (`ValueAccessor`,
`TypeInfoAccessor`, `TypeInfoGroupAccessor`, `TaintMarkAccessor`, `AnyAccessor`, `FinalAccessor`) never run: no path has
such an accessor (`AccessorTable` rejects them, Part I §3.1), and a tail is not an accessor. They stay for the prescan,
which runs the old core. The mark policy of today's `TaintMarkAccessor` case (:96-104) moves to `TypeFilter.markPolicy`:
today the filter of the element type (`FilterNext` at `[e]`, :114-123) also reads the marks below `[e]`, so the policy
has one level per node of the `[e]` chain (Part I §5.5). GENERALIZE: one public member gives the private filter.

```kotlin
// JVM/JIRFactTypeChecker.kt — new member; `filterFactByLocalType` (:177-183) stays for the prescan.
fun localFilter(type: JIRType): FactTypeChecker.FactApFilter = AccessorFilter(type, isLocalCheck = true)
```

```kotlin
/** interpreter.md §5.1: `may` from the static type, then the mark policy (G6) on each level of the `[e]` chain whose
 *  type is primitive or boxed. One filter per type (the forms of every method share it). */
class JIRTypeFilters(private val checker: JIRFactTypeChecker, private val manager: ApManager) {
    private val byType = ConcurrentHashMap<JIRType, TypeFilter>()

    fun of(t: JIRType?): TypeFilter? = t?.let { byType.computeIfAbsent(it, ::make) }

    /** Level 0 is `t`; level k + 1 is the element type of level k (`ifArrayGetElementType`, the type that `FilterNext` of
     *  `[e]` carries today, JIRFactTypeChecker.kt:114-123). A level with no known type keeps every mark (today `[e]`
     *  gives `Accept` there, so no mark check runs below it). No primitive or boxed level: no policy. */
    private fun make(t: JIRType): TypeFilter {
        val primitive = generateSequence(t) { it.ifArrayGetElementType }.map { it.unboxIfNeeded() is JIRPrimitiveType }.toList()
        return TypeFilter(
            may = checker.localFilter(t),
            markPolicy = if (true !in primitive) null
                         else MarkPolicy { m, k -> !primitive.getOrElse(k) { false } || isPrimitiveTracking(m) })
    }

    /** interpreter.md §5.1 `isPrimitiveTracking` (DD7). Today the TaintMarkAccessor case (:96-104). */
    fun isPrimitiveTracking(m: TaintMark): Boolean =
        manager.marks.name(m).endsWith(PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE)
}
```

`ApOps.filter` applies `may` to the path and then the policy to the concrete marks at the root path and at each node of
the `[e]` chain, with the level of that node (Part I §5.5). The filter never reads the tail: a `*` and an `[any]` fact
keep their tail (`interpreter.md` D11, D12). Two filters on one base are `TypeFilter.and`
(`MicroEdgeBuilder.operandFilter`, §24).

---

## 27. Rules to forms

Implements `interpreter.md` §1.3, §1.4, §4.1, §4.2, §5.2, §5.3. The rule queries pass `fact = null`: every rule of the
method in the REDUCED set (`TaintRulesProvider`, the prescan selected it). So no rule of the new analysis needs the
fact: a provider gives the same rules with no fact (the Spring provider: §31.3). The conditions use the rewriter of today:
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

    /** §1.3: the position of a rule element, or null after a rule error. It NEVER throws.
     *  THE TWO INVARIANTS OF A RULE POSITION: (1) at most one `AnyField` accessor; (2) an `AnyField` is the LAST accessor
     *  (no concrete accessor after it). A position that breaks one (`[arg0, ".*", ".f"]`, `.*.*`) is a rule error: the
     *  rule element is rejected and logged once (`RuleErrors`), as every other rule error (§1.4, D29).
     *  `AnyClassStatic` (Part II §31.3) is the whole static base `S` with the empty path. It is allowed only as the whole
     *  position of a `RemoveAllMarks` action (`kill = true`); in every other rule element, and with an accessor after
     *  it, it is a rule error. */
    fun pos(rule: Any, p: Position, kill: Boolean = false): RulePos? {
        if (p.root() == AnyClassStatic) {
            if (kill && p == AnyClassStatic) return RulePos(AccessPathBase.ClassStatic, emptyList(), any = false)
            errors.reject(rule, "AnyClassStatic outside RemoveAllMarks (§1.3)"); return null
        }
        return pos(rule, p.resolveAp())                                    // REUSE TaintEvaluator.kt:81-101
    }
    private tailrec fun Position.root(): Position = if (this is PositionWithAccess) base.root() else this
    fun pos(rule: Any, p: PositionAccess): RulePos? {
        val acc = p.accessors()
        val anyCount = acc.count { it == AnyAccessor }
        if (anyCount > 1) { errors.reject(rule, "two AnyField accessors in a position (§1.3)"); return null }        // (1)
        if (anyCount == 1 && acc.last() != AnyAccessor) {
            errors.reject(rule, "an accessor after AnyField in a position (§1.3)"); return null                     // (2)
        }
        val any = anyCount == 1
        val path = if (any) acc.dropLast(1) else acc
        val base = p.base().let { if (it == AccessPathBase.Return) resultBase else it }   // `Result` (§1.3; §4.7 at a throw)
        return RulePos(base, path.map { manager.accessors.index(it) }, any)           // DD6
    }

    /** The path of a Cleaner (Part I §6). */
    fun node(path: List<AccessorIdx>): PathNode? = manager.path(path)

    /** DD7: a rule mark (by its name) and a literal mark (`TaintMarkAccessor.mark` is the name). */
    fun mark(m: RuleMark): TaintMark = manager.marks.mark(m.name)
    fun mark(name: String): TaintMark = manager.marks.mark(name)

    /** §4.2: `ContainsMark(P, T)` -> `(P, $, T)`; `ContainsMarkOnAnyField(P, T)` or `ContainsMark(P.AnyField, T)` -> `(P, [any], T)`.
     *  Null after a rule error of the position. */
    fun literal(rule: Any, l: TaintMarkAwareConditionExpr.Literal): PathFact? = when (l) {
        is ContainsMarkLiteral -> pos(rule, l.position)?.fact(mark(l.mark.mark))
        is ContainsMarkOnAnyAccessorLiteral -> pos(rule, l.position)?.copy(any = true)?.fact(mark(l.mark.mark))
    }

    /** §4.2 for a source and a sink: a negated literal counts as true; `Or` gives one cube per alternative. A cube with a
     *  rejected literal goes (a rule error, logged once). A pass rule takes no cube: it has no mark literal (§4.2, D24;
     *  Part II §28.5). REUSE removeTrueLiterals (TaintMarkAwareConditionExpr.kt:48-50) and explodeToDNF (:110-123). */
    fun cubes(rule: Any, cond: ExprOrConstant): List<List<PathFact>> = when {
        cond.isFalse -> emptyList()
        cond.isTrue -> listOf(emptyList())
        else -> {
            val positive = cond.expr.removeTrueLiterals { it.negated } ?: return listOf(emptyList())
            positive.explodeToDNF().mapNotNull { cube ->
                cube.literals.map { literal(rule, it) ?: return@mapNotNull null }.distinct()
            }.distinct()
        }
    }
```

### 27.2 The rule-to-edge path and the sources (call, entry, exit, read)

Every rule element that makes a mark is `premises -> target`: a source and an end fact (`AssignMark`, from the zero fact
or from the literals of the condition) and a `CopyMark` pass rule (from its own premise, the copied mark). One
function makes the edge for all of them (`ruleEdge`), and one function checks the target of an `AssignMark`
(`markTarget`, `interpreter.md` §1.4). Users: `source` (the sources stage of a call, §28.3; the entry rules and the exit rules, §29),
`endFacts` (§27.3), `pass` (§27.4), `readSources` (below).

```kotlin
    /** THE RULE-TO-EDGE PATH (§4.1, §5.3). The premises have the tail `$` or `[any]` and a concrete mark (S9); the
     *  target has a concrete mark and no `*` tail (W7). No premise: from the zero fact (an unconditional source, an end
     *  fact). One: a plain micro edge (a conditional source, a `CopyMark`). Two or more: a conjunctive edge (an ND source;
     *  a pass rule has one premise, §4.2, D24). */
    fun ruleEdge(b: MicroEdgeBuilder, premises: List<PathFact>, target: PathFact) = when (premises.size) {
        0 -> b.edge(PathEdge(ZERO_FACT, target, ExclusionSet.Empty))
        1 -> b.edge(PathEdge(premises[0], target, ExclusionSet.Empty))
        else -> b.conjunction(ConjunctiveEdge(premises.map { Pattern(it, ExclusionSet.Empty) }, target))
    }

    /** §1.4: the target `P.t (T)` of an `AssignMark` (a source, an end fact), or null after a rule error. A class position
     *  takes no `[any]` target, and with a class target no `[any]` premise (I12 (b)). */
    fun markTarget(rule: Any, a: AssignMark, premises: List<PathFact>): PathFact? {
        val to = pos(rule, a.position) ?: return null
        if (to.isClass && to.any) { errors.reject(rule, "[any] target on a class position (§1.4)"); return null }
        if (to.isClass && premises.any { it.tail == Tail.ANY }) {
            errors.reject(rule, "ContainsMarkOnAnyField with a class target (§1.4, I12 (b))"); return null
        }
        return to.fact(mark(a.mark))
    }

    /** §4.1: `zero.$ (zeroMark) -> P.t (T)`, `Q.t' (T') -> P.t (T)`, or a conjunction (§5.3). */
    fun source(b: MicroEdgeBuilder, rule: TaintConfigurationItem, cube: List<PathFact>, a: AssignMark) {
        markTarget(rule, a, cube)?.let { ruleEdge(b, cube, it) }
    }

    /** §4.4: the read source at `x = C.s` (`TaintStaticFieldSource`); the condition must be true. Today
     *  JIRMethodSequentFlowFunction.kt:235-268 (a non-true condition was a TODO; here it is a rule error). */
    fun readSources(b: MicroEdgeBuilder, s: JIRAssignInst) {
        val field = (s.rhv as? JIRFieldRef)?.field?.field?.takeIf { it.isStatic } ?: return
        val x = accessPathBase(s.lhv) ?: return
        val found = rules.sourceRulesForStaticField(field, s, fact = null)
        if (found.none()) return
        b.keepZero()                                                               // I11 (d)
        for (rule in found) {
            if (!rule.condition.isTrue()) { errors.reject(rule, "read source with a condition (§4.1)"); continue }
            for (a in rule.actionsAfter) {
                val p = pos(rule, a.position) ?: continue
                if (p.base != AccessPathBase.Return) { errors.reject(rule, "read source target is not the read value (§4.4)"); continue }
                ruleEdge(b, emptyList(), p.copy(base = x).fact(mark(a.mark)))     // `x` is a local: no class target
            }
        }
    }
```

### 27.3 Sinks and end facts

A sink is not an edge: it is a set of patterns that the core checks with `ApOps.checkMark` (Part I; `ap.md` §4.9). On
each pattern of a `SinkRule`, `MarkCheck.Holds` triggers the pattern (a plain sink: the sink; a conjunctive sink: one
input of the k-ary join of its literals), `MarkCheck.Request` raises the request (run 1, a FLOW fact), and
`MarkCheck.None` does nothing.

```kotlin
    /** §4.1, §4.2, ap.md §4.9: one SinkRule per alternative. I11 (f): every pattern has the tail `$` or `[any]`.
     *  `mayBeArray(i)`: only for a sink at a call (Part II §28.1): ARRAY ELEMENTS OF A CALL SINK (§4.2). A literal on
     *  `arg(i)·ρ` whose argument may be an array is the `Or` of `(arg(i), ρ, t, T)` and `(arg(i), [e]·ρ, t, T)`, so a cube
     *  gives one alternative per choice (a conjunctive sink too). The entry and exit sinks pass no `mayBeArray`. All the
     *  alternatives have the same `rule`, so they have one vulnerability key; each one seeds its own patterns (§4.9).
     *  `SinkRule.alternative` is the index in this list: the cube order of `explodeToDNF`, then the order of the
     *  cartesian product of the array choices. Both orders are fixed for a rule at a statement, so the index is the same
     *  in every run and every context (I5). */
    fun sinks(rule: TaintConfigurationSink, cond: ExprOrConstant, mayBeArray: (Int) -> Boolean = { false }): List<SinkRule> {
        val ends = endFacts(rule)
        val alternatives: List<List<Pattern>> = cubes(rule, cond).flatMap { cube ->
            if (cube.isEmpty()) return@flatMap listOf(listOf(ZERO_PATTERN))
            cube.map { elementChoices(it, mayBeArray) }                      // REUSE DF/util/ListUtils.kt:127
                .cartesianProductMapTo { choice -> choice.map { Pattern(it, ExclusionSet.Empty) }.distinct() }
        }.distinct()
        return alternatives.mapIndexed { i, patterns -> SinkRule(rule, alternative = i, patterns, ends) }
    }

    /** Today `arrayElementConditionReaders` (`JVM/taint/JIRMethodCallTaintUtil.kt:191-203`): a reader with the prefix `[e]`
     *  on an `arg(i)` fact. Not for `this`, `Result` or `S`. */
    private fun elementChoices(lit: PathFact, mayBeArray: (Int) -> Boolean): List<PathFact> {
        val b = lit.base as? AccessPathBase.Argument ?: return listOf(lit)
        if (!mayBeArray(b.idx)) return listOf(lit)
        return listOf(lit, lit.copy(path = listOf(elementIdx) + lit.path))
    }
    private val elementIdx: AccessorIdx = manager.accessors.index(ElementAccessor)

    /** §4.1 END FACTS: `trackFactsReachAnalysisEnd` as the targets of a source from the zero fact (the rule-to-edge path,
     *  GEN mode). */
    fun endFacts(rule: TaintConfigurationSink): List<MicroEdge> = MicroEdgeBuilder().apply {
        for (a in rule.trackFactsReachAnalysisEnd) markTarget(rule, a, emptyList())?.let { ruleEdge(this, emptyList(), it) }
    }.buildGen().edges
```

### 27.4 Pass rules (unresolved callee)

`CopyMark(T, P → Q)` copies one mark. The copied mark is not a condition: it is the premise `P.t (T)` of the pass edge
(`t` = `$`, or `[any]` for `P.AnyField`; `interpreter.md` §4.1, §4.2), so a fact at `P` with `T` gives `Q.t (T)`. A
pass rule has no mark-dependent condition (`interpreter.md` §4.2, D24): a pass rule with a mark literal is a rule error,
and it applies without its mark literals. One check in the caller does this for `CopyAllMarks` and `CopyMark`
(`passRules`, §28.5). So `pass` takes no cube, and a pass rule never makes a conjunctive edge.

```kotlin
    /** §4.1 pass-rule rows and the AnyField table; §1.4 rule errors. The caller removed the mark literals (§4.2, D24;
     *  Part II §28.5), so a pass rule gives plain micro edges only. Gives the from base and the to base of the edges that
     *  it made, or null (not a pass action, or a rule error). */
    fun pass(b: MicroEdgeBuilder, rule: TaintConfigurationItem, action: Action): Pair<AccessPathBase, AccessPathBase>? {
        val (fromPos, toPos) = when (action) {
            is CopyAllMarks -> action.from to action.to
            is CopyMark -> action.from to action.to
            else -> return null
        }
        val from = pos(rule, fromPos) ?: return null
        val to = pos(rule, toPos) ?: return null
        if (from.isClass || to.isClass) { errors.reject(rule, "pass rule from or to a class position (§1.4)"); return null }
        b.edge(keepEdge(from.base))                                                        // b.* -> b.*
        when (action) {
            // P.* -> Q.* ; P.* -> Q.[any] ; P.[any] -> Q.[any]
            is CopyAllMarks -> b.edge(PathEdge(from.star(), to.star(forceAny = from.any), ExclusionSet.Empty))
            // P.t (T) -> Q.t (T): the copied mark is the one premise (§4.2), not a condition
            is CopyMark -> mark(action.mark).let { t -> ruleEdge(b, listOf(from.fact(t)), to.fact(t)) }
            else -> Unit
        }
        return from.base to to.base
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

    /** §5.2 mapping; `RemoveAllMarks` on S is the kill of §1.4; `RemoveAllMarks(AnyClassStatic)` is the whole-base
     *  cleaner (Part II §31.3). A rule error of a position gives no step. */
    fun unconditional(rule: TaintConfigurationItem, a: Action, types: PositionTypeResolver): List<CleanStep> = when (a) {
        is RemoveMark -> {
            val p = pos(rule, a.position) ?: return emptyList()
            val t = mark(a.mark)
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
            val p = pos(rule, a.position, kill = true) ?: return emptyList()
            when {
                // AnyClassStatic: the WHOLE-BASE CLEANER (S, atAndBelow, all), the empty path (interpreter.md §1.4, I12 (e)).
                // Every fact on S lies inside it, so it drops the fact whole and raises no request.
                p.base == AccessPathBase.ClassStatic && p.path.isEmpty() ->
                    listOf(CleanStep.Clean(Cleaner(AccessPathBase.ClassStatic, path = null, CleanReach.AT_AND_BELOW, mark = null)))
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
    private val returnValue: JIRImmediate? = (s as? JIRAssignInst)?.lhv?.let {                // as today, JIRMethodCallFactMapper.kt:151-153
        it as? JIRImmediate ?: error("Non simple return value: $s")
    }
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
            .flatMap { forms.sinks(it, rewriter.rewrite(it.condition), mayBeArray) }               // SinkRule.alternative: per rule (§27.3)
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
                add(Edges(ADDED, RETURNED, UNRESOLVED, StatementSummary.identities(boundPositions())))   // §3.7 item 1: no filter
                add(Edges(ADDED, RETURNED, UNRESOLVED, passRules()))                                 // §3.7 items 2, 3: declared types
            }
            if (callee.isConstructor) add(Edges(ADDED, REWRITTEN, CONSTRUCTOR, StatementSummary.identities(boundPositions())))   // §3.5: every added fact, S too (SI5); Origin.IDENTITY: no alias (SI15)
            add(Rewrite(RETURNED, REWRITTEN, rewriterCleaners()))                                    // step 6
            add(Edges(REWRITTEN, AFTER, BIND_BACK, back))
            aliases(back)?.let { add(Edges(REWRITTEN, AFTER, ALIASES, it, Guard.MemoryEffect)) }
        }
        return CallPlan(touched(), stages, sinks, entry = BEFORE, exit = AFTER, passReads = passReads)   // passReads: §28.5
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
        keepZero()
        for (rule in interp.rules.sourceRulesForMethod(callee, s, fact = null)) {
            val cubes = forms.cubes(rule, rewriter.rewrite(rule.condition))
            for (a in rule.actionsAfter) for (cube in cubes) forms.source(this, rule, cube, a)
        }
    }.buildStage()

    /** §4.5 step 5.1, §4.8: the cleaner rules of the named method, in rule order. */
    private fun cleanSteps(): List<CleanStep> = interp.rules.cleanerRulesForMethod(callee, s, fact = null)
        .flatMap { forms.cleanSteps(it, rewriter.rewrite(it.condition), types) }

    /** §5.2 THE SUMMARY REWRITER: RULE-GUIDED FLOW. It acts for the methods that user-defined rules cover. Its purpose:
     *  the rule overrides the real data flow of the callee. At the action positions of a selected rule, the rewriter
     *  cleans the relevant marks of the rule from every result at RETURNED, so for these marks the rule, not the callee
     *  body, decides what comes back (a source then adds its own target in the SOURCES stage). This is a by-design
     *  override, not a cleaner placement: D20 does not govern it.
     *  RULE SELECTION (the non-mark atoms are decided statically by the rewriter of the call):
     *  * every user-defined SOURCE rule whose condition is not statically false (`!isFalse`, as today);
     *  * every user-defined CLEANER rule only if it is UNCONDITIONAL (`isTrue`). A conditional user cleaner does not act
     *    through the rewriter, as it does not act in step 5.1 (D20). Today it acts here when its condition is not
     *    statically false (:77-85; `interpreter.md` D23).
     *  ADAPT of JIRMethodCallRuleBasedSummaryRewriter.userRuleDefinedActions (:54-88): the same rule queries
     *  (`allRelevant = true`), `clean(P, exact, T)` for each relevant mark and action position. A rule with no
     *  `UserDefinedRuleInfo` is not selected (the Spring `__cleanup__` cleaner, §31.3, too). */
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
            if (!rewriter.rewrite(rule.condition).isFalse) add(rule, rule.actionsAfter.map { it.position })       // sources: !isFalse
        for (rule in interp.rules.cleanerRulesForMethod(callee, s, fact = null, allRelevant = true))
            if (rewriter.rewrite(rule.condition).isTrue) add(rule, rule.actionsAfter.filterIsInstance<RemoveMark>().map { it.position })   // cleaners: isTrue only
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
     *  if the prescan knows none, it is a resolution failure: the unresolved path (§3.7).
     *  §3.6, I8 (D28): an EMPTY METHOD (no instruction: a native or an abstract method, a method with no body) is not
     *  analysable, so it is never a callee: the resolver drops it. If every resolution result is an empty method, the
     *  call is an UNRESOLVED call (§3.7: the default identity and the pass rules). An abstract method never comes here
     *  (`isValidConcreteMethod`, JIRCallResolver.kt:183-184); a native method of a project class does. */
    private fun resolve(): Pair<List<MethodKey>, Boolean> {
        val ctx = object : JIRCallResolutionContext {
            override val methodEntryPoint = caller
            override val aliasAnalysis = entry.aliasAnalysis
        }
        val callees = LinkedHashSet<MethodKey>()
        var unresolved = false
        val results = interp.callResolver.resolve(call, s, ctx)
        for (res in results) when (res) {
            JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> unresolved = true
            is JIRCallResolver.MethodResolutionResult.ConcreteMethod ->
                if (!isEmptyMethod(res.method.method)) callees += keys(res.method)                   // an empty method: dropped
            is JIRCallResolver.MethodResolutionResult.Lambda -> {
                val impls = entry.lambdas[s.location.index]
                if (impls.isNullOrEmpty()) unresolved = true
                else impls.forEach { callees += keys(MethodWithContext(it, EmptyMethodContext)) }
            }
        }
        if (results.isNotEmpty() && results.all { it is JIRCallResolver.MethodResolutionResult.ConcreteMethod && isEmptyMethod(it.method.method) })
            unresolved = true                                                                        // every result is empty: §3.7
        return callees.toList() to unresolved
    }

    private fun isEmptyMethod(m: JIRMethod): Boolean = m.instList.size == 0                            // JIRLanguageManager.isEmpty

    /** As MethodAnalyzer.methodEntryPoints (DF/ap/ifds/MethodAnalyzer.kt:815-821). Never an empty method (above), so the
     *  method has its entry statement (`JMethodEnterInst`, §31.2). */
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
    /** The from bases of the pass rules of the rule set (not of the default getter rules): `CallPlan.passReads`. */
    private val passReads = LinkedHashSet<AccessPathBase>()

    /** §3.7 items 2 and 3: the pass rules of the named method and the default getter rules (JIRMethodGetDefault.kt:37-51). */
    private fun passRules(): StatementSummary = MicroEdgeBuilder().apply {
        val rules = interp.rules.passTroughRulesForMethod(callee, s, fact = null).map { Triple(it, rewriter.rewrite(it.condition), true) } +
            interp.defaultGetModel?.defaultPropagationRules(callee).orEmpty().map { Triple(it.rule, it.condition, false) }
        val read = HashSet<AccessPathBase>()
        val written = HashSet<AccessPathBase>()
        for ((rule, cond, ofRuleSet) in rules) {
            if (cond.isFalse) continue                                                  // §4.2: a false static atom removes the rule
            // §4.2, D24: a pass rule has no mark-dependent condition. A mark literal is left after the static atoms when
            // the rewritten condition is an expression: ONE check for CopyAllMarks and CopyMark, one rule error, and the
            // rule applies without its mark literals.
            if (!cond.isTrue) forms.errors.reject(rule, "pass rule with a mark literal (interpreter.md §4.2, D24): applied without it")
            for (a in rule.actionsAfter) {
                val (from, to) = forms.pass(this, rule, a) ?: continue                // null: not a pass action, or a rule error
                read += from; written += to
                if (ofRuleSet) passReads += from
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
    // today `startFactBase in passEvaluator.relevantPositionBase`: a pass rule of the rule set reads this position.
    // Today the tracker runs BEFORE the default getter rules (JIRMethodCallFlowFunction.kt:282-302), so they do not count.
    val ruleApplied = position in plan.passReads
    t.trackExternalMethod("${callee.enclosingClass.name}#${callee.name}", callee.description, position.toString(), ruleApplied)
}
```

Today `relevantPositionBase` holds the from-base of a rule only when the condition of the rule holds on the fact
(`TaintConfigUtils.kt:48-60`); the hook reads `CallPlan.passReads`: the from-bases of the pass rules of the rule set whose
condition is not statically false. A pass rule with a mark literal applies without it (D24), so the hook counts its
from-base on every fact. Such a rule is rare, and `ruleApplied` only splits the report into two lists. The default
getter rules are not in `passReads`, as today: a library getter with no model stays in the list "without rules"
(`ExternalMethodTracker.kt:37-54`).

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
     *  holds before and after the call. The stage has the guard `MemoryEffect` (AC3, AC4). The alias analysis is out of
     *  scope and not changed: no filter for a static alias base `b = S`, which does not occur under A1 (§32). */
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
        val rw = calleeRewriter(interp, entry, method, s)
        val b = MicroEdgeBuilder().apply { keepZero() }
        val bases = listOf<AccessPathBase>(AccessPathBase.This) + method.parameters.indices.map { AccessPathBase.Argument(it) }
        for (base in bases) {
            val cls = key.context.locationClass(key, base) ?: continue                // copy of :64-84
            b.keep(base); b.operandFilter(base, interp.typeFilters.of(cls.toType()))
        }
        for (rule in interp.rules.entryPointRulesForMethod(method, s, fact = null))
            if (rw.rewrite(rule.condition).isTrue) rule.actionsAfter.forEach { interp.ruleForms.source(b, rule, emptyList(), it) }
        val sinks = interp.rules.sinkRulesForMethodEntry(method, s, fact = null).flatMap { rule ->
            val cond = rw.rewrite(rule.condition)
            if (cond.isTrue) interp.ruleForms.sinks(rule, cond) else emptyList()       // unconditional only, as today (:99-101)
        }
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
            else -> error("not a boundary exit: $exit (the boundary feature, Part II §31.2)")   // exitNodes gives only these two
        }
        val forms = if (normal) interp.ruleForms else interp.ruleFormsAtThrow
        val method = key.method as JIRMethod
        val rw = calleeRewriter(interp, entry, method, exit)
        val b = MicroEdgeBuilder().apply { keepZero() }                              // I11 (d): both exits
        for (rule in interp.rules.exitSourceRulesForMethod(method, exit, fact = null)) {
            for (cube in forms.cubes(rule, rw.rewrite(rule.condition))) {             // the empty cube too: both exits (D26)
                if (cube.size >= 2) { interp.errors.reject(rule, "exit source with a conjunction (§5.3)"); continue }   // SI4
                cube.singleOrNull()?.let { b.keep(it.base) }                                       // f stays in the worklist
                rule.actionsAfter.forEach { forms.source(b, rule, cube, it) }
            }
        }
        val sinks = interp.rules.sinkRulesForMethodExit(method, exit, fact = null, initialFacts = null)   // every fact (D21)
            .flatMap { forms.sinks(it, rw.rewrite(it.condition)) }   // no array alternative (§4.2); ZERO_PATTERN at both exits (D22, D26)
        return ExitRules(RuleStatement(b.build(), genSummary(sinks), sinks),
            globalStateDrop = normal && sinks.isNotEmpty(),                           // §4.7 step 3 (G2): normal exit only
            entryMarks = if (normal) entryMarks(entryRules) else emptySet())          // §4.7 step 4 (G2): normal exit only
    }

    /** The rewriter of the entry and exit rules: rule positions in the coordinates of the method (today
     *  JIRTaintAnalysisContext.prepareMethodRules, JVM/taint/JIRTaintAnalysisContext.kt:170-186). */
    private fun calleeRewriter(interp: JIRInterpreter, entry: JIRMethodEntry, method: JIRMethod, s: CommonInst) =
        JIRMarkAwareConditionRewriter(CalleePositionToJIRValueResolver(method), interp.checker, entry.aliasAnalysis, s)

    private fun genSummary(sinks: List<SinkRule>) =
        MicroEdgeBuilder().apply { sinks.forEach { sk -> sk.endFacts.forEach { edge(it.edge) } } }.buildGen()
}
```

The core uses `ExitRules` as `interpreter.md` §4.7 says:

* step 1: `rules.summary` (STATEMENT) on each fact; the results keep the premise;
* step 2: `checkMark` of each pattern of each `SinkRule` on each item; on `MarkCheck.Holds` (for a conjunctive sink, a
  new full combination of the k-ary join), `sk.endFacts` (GEN) on the zero fact, with the layer of the sink edge; the
  field limit; the results join the worklist;
* step 2, a conjunctive exit sink: each `MarkCheck.Holds` of a literal is stored as the input of that literal in the
  conjunction store (`ConjunctionStore`, Part I §7.10), also when it completes no combination;
* step 3 (THE GLOBAL-STATE RULE): if `globalStateDrop`, the EVALUATED STATICS go. For an item on `S`, each part on which
  a mark literal (`ContainsMark`, `ContainsMarkOnAnyField`) of an exit sink holds (`MarkCheck.Holds.facts`) is dropped
  from the item before the summary edge (`ops.without`). This holds for a plain and for a conjunctive exit sink. The rest
  of the item stays. For a conjunctive sink the dropped part stays the stored input of its literal (step 2): the
  evaluated facts are an assumption for the next evaluation attempts of that sink, so a later item can complete the
  combination with them. Today drops only the evaluated `S` facts of a sink that was reached
  (`JIRSequentTaintUtil.kt:76-85`, `dropFinalFacts`, `JIRMethodSequentFlowFunction.kt:186-188, 271-278`; §34 SI17);
* step 4: for a zero premise (`premise.isZero`; the item is a TAINT tree), `ops.without(item, ops.targetTree(p,
  item.layer))` for each `p` of `entryMarkParts(item.base)` (only the root `$` leaf, as today);
* step 5: the summary edge, only if `isSummaryBase`.

At the exceptional exit only steps 1 and 2 apply, and the results end there: it is not an end node and makes no summary
edge (`analyzer-core.md` §4.3, §4.4). The unconditional exit sources and the unconditional exit sinks (the empty cube,
`ZERO_PATTERN`) fire on the zero fact at both exits, so an unconditional exit sink can report at both exits: expected
and approved (D22, D26; §34 SI11, SI12). The backward run starts the zero fact at both exits; the start rules of each exit
are `exitRules(method, exit).reversed()` and the seeds of its exit sinks; a seed also takes the reversed exit sources of
that exit (`interpreter.md` §4.9 SEEDS; `DirectedForms.startRules`, Part II §23.7).

---

## 30. Boundaries: entry, exits, wired graph

Implements `analyzer-core.md` §4.4 and `interpreter.md` I11 (e).

```kotlin
// in JIRMethodEntry (Part II §31.2)
/** analyzer-core.md §4.4: the two boundary exits, `JMethodExitNormalInst` and `JMethodExitExceptionalInst`. Every
 *  analysed method has them: an empty method is never analysed (§28.4), and `JIRMethodEntry` asserts the boundary
 *  instructions (§31.2). */
fun exitNodes(key: MethodKey): List<ExitNode> =
    shared.graph.methodGraph(method).exitPoints()                            // JApplicationSingleExitGraph.kt:26-29
        .map { ExitNode(it, it is JMethodExitExceptionalInst) }.toList()
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

* PER METHOD (`JIRMethodEntry`): the graphs, the alias analysis, the prescan lambdas, and the forms that do not read
  the context: the statement summaries and the exit rules. Every context of the method shares them (today the
  `EmptyMethodContext` twin, `DF/ap/ifds/MethodAnalyzerStorage.kt:38-47`). No liveness: the forms have no liveness step
  (D25); the alias analysis keeps its own reachability input, as today.
* PER METHOD KEY (`JIRMethodForms : MethodForms`): the forms that read the context of the key: the call plans (the
  callee resolution, `JVM/JIRCallResolver.kt:193-246`) and the entry rules (the start filter by the context type, §29).

`analyzer-core.md` §4.8 caches per method (spec issue SI16). The `Interpreter` calls take a `MethodKey`, so
`MethodForms` has the same key. `MethodContextCache` (`analyzer-impl.md` §3.4) gives these `MethodForms` and makes the
`DirectedForms` of each run. It has no forms cache of its own.

THE REQUIRED CLASSPATH FEATURES. Part II reads the JIR that these features make. Production installs all of them
(`core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisContext.kt:122-136`). The test kit installs the
first one (`core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/test/kotlin/org/opentaint/dataflow/jvm/BasicTestUtils.kt:48`);
a test that needs another one installs it.

| Feature | Why Part II needs it | Without it |
|---|---|---|
| `JMethodBoundaryInstFeature` (`core/opentaint-utils/opentaint-jvm-util/src/main/kotlin/org/opentaint/jvm/graph/JMethodBoundaryInstFeature.kt:10-22`; the last feature) | The method key is the entry statement `JMethodEnterInst`; the exit nodes and the exit rules are the boundary exits `JMethodExitNormalInst` and `JMethodExitExceptionalInst` (§29, §30); `JIRExitWiredGraph` wires to the exceptional exit (I11 (e)) | the method key, the exit nodes and the exit rules have no statement, and no wiring is made. `JIRMethodEntry` asserts the feature (below), as today (`JIRAnalysisManager.kt:118-120`), and `exitRules` fails on an exit that is not a boundary exit (§29) |
| `LambdaAnonymousClassFeature` + `LambdaExpressionToAnonymousClassTransformerFeature` (`JVM/LambdaAnonymousClassFeature.kt:60`, `JVM/LambdaExpressionToAnonymousClassTransformerFeature.kt:28`) | A lambda value is an allocation of a `JIRLambdaClass`, so the prescan finds the lambda methods of a call (§31.1) and a lambda call has its callees (§3.9, D19) | a raw `JIRLambdaExpr` stays: the resolver gives no result for it (`JIRCallResolver.kt:98-101`), so the call has no callee stage, and the prescan knows no lambda |
| `JStringConcatTransformer` (`core/opentaint-utils/opentaint-jvm-util/src/main/kotlin/org/opentaint/jvm/transformer/JStringConcatTransformer.kt:32`) | `makeConcatWithConstants` becomes calls of `String.concat`, so each operand flows by the rules of `String.concat` (§3.7) | the `invokedynamic` call is an unresolved call with the coarse pass rule of `StringConcatRuleProvider` (`core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/StringConcatRuleProvider.kt:20-30`) |

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

/** analyzer-core.md §4.8 "per method": the parts that do not read the context. Only an analysed method has an entry: a
 *  method key needs an entry statement, and an empty method is never a callee (§28.4) and has no entry statement. */
class JIRMethodEntry internal constructor(val method: JIRMethod, internal val shared: JIRMethodEntries) {
    init {
        val instructions = method.instList.instructions
        check(instructions.isNotEmpty()) { "Method $method has no instruction: an empty method is never analysed" }   // I8, D28
        check(instructions.last() is JMethodExitExceptionalInst) {                            // as today, JIRAnalysisManager.kt:118-120
            "Method $method is analysed without method boundary instructions"
        }
    }
    internal val size = shared.languageManager.getMaxInstIndex(method) + 1
    fun index(s: CommonInst): Int = shared.languageManager.getInstIndex(s)

    @Suppress("UNCHECKED_CAST")
    private val common get() = shared.graph as ApplicationGraph<CommonMethod, CommonInst>

    /** The alias analysis keeps its own inputs, as today (JIRAnalysisManager.kt:122-135): the reachability of the locals
     *  is its input only. No form reads it (no liveness step, D25). The alias analysis is not changed (§32). */
    val aliasAnalysis: JIRLocalAliasAnalysis? by lazy {
        if (!shared.aliasParams.useAliasAnalysis) null
        else JIRLocalAliasAnalysis(shared.graph.methodGraph(method).entryPoints().first(), shared.graph,
            shared.callResolver, shared.rules, JIRLocalVariableReachability(method, shared.graph, shared.languageManager),
            shared.cancellation, shared.languageManager, shared.aliasParams)
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
        e.statements.get(e.index(s), direction) { JIRStatementForms(interp, e).build(s as JIRInst) }
    override fun call(direction: Direction, s: CommonInst, call: CommonCallExpr) =
        plans.get(e.index(s), direction) { JIRCallPlanBuilder(interp, e, key, s as JIRInst, call as JIRCallExpr).build() }
    override fun entryRules(direction: Direction) =
        entry.get(0, direction) { JIRBoundaryForms.entryRules(interp, e, key) }
    override fun exitRules(direction: Direction, exit: CommonInst) =
        e.exits.get(e.index(exit), direction) { JIRBoundaryForms.exitRules(interp, e, key, exit, entryRules(Direction.FORWARD)) }
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
caches have the lifetime of the analysis (`JIRMethodEntries` lives as long as the `IterationDriver`). The vulnerability
store does not read this identity: a witness names its sink alternative by `SinkRule.alternative` (§23.4), which a
rebuilt form keeps.

The run part of today's context (`JIRTaintAnalysisContext`, the sink tracker) is not here. The core owns the stores of a
run (`analyzer-core.md` §4.8).

### 31.3 The Spring dispatcher: no rule needs the fact

Implements `interpreter.md` §1.3 (`AnyClassStatic`), §1.4, §5.2 and D27. The generated Spring dispatcher calls a
controller, then `__cleanup__()`, and loops (`ndMethodDispatch`). Today the cleaner of `__cleanup__` is built from the
fact: for a fact on `S`, `RemoveAllMarks(ClassStatic(C))` for each class of the fact except the registry class
`__spring_registry__` (`SpringRuleProvider.kt:110-143`). The new core queries every rule with `fact = null` (§27), so
that cleaner would be lost, and static taint would cross the dispatched controllers. Three changes make the cleaner
fact-free. The effect stays the same: the static content outside the registry goes, and the registry stays.

1. THE GENERATOR saves and restores the registry around each `__cleanup__()` call. The registry class has one static
   field per component (`SpringWebProject.kt:160-200`); the components are registered before the dispatcher is generated
   (`createSpringProjectContext`, :97-127).

```kotlin
// core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringWebProject.kt, ndMethodDispatch: replaces the cleanup
// call (:308-313). `loopEnd` is the jump target of every block (:327) and of the switch default (:331), so it is the
// first save, or the cleanup call when the registry is empty.
val registry = componentRegistryField.values.sortedBy { it.name }                // the static fields of __spring_registry__
val saved = registry.mapIndexed { i, f -> JIRLocalVar(index = 1 + i, "%reg_${f.name}", f.type) }   // index 0 is %sel (:275)
var firstSave: JIRInstLocation? = null
for ((f, local) in registry.zip(saved)) instructions.addInstWithLocation(dispatcher) { loc ->
    if (firstSave == null) firstSave = loc
    JIRAssignInst(loc, local, JIRFieldRef(instance = null, f))                      // %reg_f = __spring_registry__.f
}
val cleanupLoc: JIRInstLocation
instructions.addInstWithLocation(dispatcher) { loc ->
    cleanupLoc = loc
    JIRCallInst(loc, JIRStaticCallExpr(cleanupMethod.staticMethodRef(), emptyList()))   // __cleanup__()
}
for ((f, local) in registry.zip(saved)) instructions.addInstWithLocation(dispatcher) { loc ->
    JIRAssignInst(loc, JIRFieldRef(instance = null, f), local)                      // __spring_registry__.f = %reg_f
}
val loopEnd: JIRInstLocation = firstSave ?: cleanupLoc
```

2. THE RULE POSITION `AnyClassStatic`: the whole static base. A new JVM rule position; Part II maps it to `S` with the
   empty path, only in a `RemoveAllMarks` action (`JIRRuleForms.pos`, §27.1; elsewhere a rule error), and the action is
   the whole-base cleaner `(S, atAndBelow, all)` (`JIRRuleForms.unconditional`, §27.5). The current core never applies
   it (item 3), so its readers only map it to `ClassStatic` with the empty path, and the resolvers give no value.

```kotlin
// core/opentaint-configuration-rules/configuration-rules-jvm/src/main/kotlin/org/opentaint/dataflow/configuration/jvm/Position.kt
/** The whole static base `S` (every class). Only in `RemoveAllMarks` (interpreter.md §1.3, §1.4). */
data object AnyClassStatic : Position {
    override fun toString(): String = javaClass.simpleName
}

// Every exhaustive `when` over `Position` gets a branch:
//   JVM/taint/TaintEvaluator.kt:73-79   resolveBaseAp:      is AnyClassStatic -> AccessPathBase.ClassStatic
//   JVM/taint/TaintEvaluator.kt:83-101  resolveAp:          is AnyClassStatic -> PositionAccess.Simple(baseAp)
//   JVM/JIRCallPositionResolver.kt:39-48, 56-69:           is AnyClassStatic -> CallPositionValue.None
//   JVM/JIRLocalAliasAnalysis.kt:90-104 toExternalObject:  is AnyClassStatic -> return null
//   core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/MethodTaintConfigurationResolver.kt:499-505, 555-561: as ClassStatic
//   core/src/test/kotlin/org/opentaint/jvm/sast/project/tester/TestTraces.kt:41-48: as ClassStatic
```

3. THE RULE PROVIDER gives the whole-base cleaner for a query with no fact, and today's cleaner for a query with a fact.

```kotlin
// core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringRuleProvider.kt, cleanerRulesForMethod (:104-128)
if (method is SpringGeneratedMethod) {
    if (method.name != GeneratedSpringControllerDispatcherCleanupMethod) return emptyList()
    // The new core (fact == null): the unconditional cleaner of the whole static base. The dispatcher restores the
    // registry after the call (item 1), so no rule needs the fact.
    if (fact == null) return listOf(TaintCleaner(method, mkTrue(), listOf(RemoveAllMarks(AnyClassStatic)), info = null))
    // The current core of the prescan (with a fact): today's code, unchanged.
    val cleanupPositions = fact.cleanupPositions() ?: return emptyList()
    return listOf(TaintCleaner(method, mkTrue(), cleanupPositions.map { RemoveAllMarks(it) }, info = null))
}
```

The current core never applies the fact-free cleaner. It queries the cleaners with a fact (`cleanRulesForCallStatement`,
`JVM/taint/JIRTaintAnalysisContext.kt:85-94`, from `JIRMethodCallFlowFunction.kt:167`). It queries with `fact = null`
only outside the prescan (`allRelevantCleanRulesForCallStatement`, `JIRTaintAnalysisContext.kt:58-61`, which gives
nothing in the prescan), and its only user, the summary rewriter, skips a rule with no `UserDefinedRuleInfo`
(`JIRMethodCallRuleBasedSummaryRewriter.kt:77-78`). The new rewriter skips it too (§28.3).

In the new core, the plan of the call `__cleanup__()` (a static call with no argument: only `S` and the zero fact are
bound) has the step `CleanStep.Clean(Cleaner(S, [], AT_AND_BELOW, all))` at `BOUND -> ADDED`: every fact on `S` goes,
whole, with no request. `S` is always touched, so no `S` fact passes over the call. The restores then write the saved
registry facts back: `%reg_f.* -> S.<__spring_registry__>.f.*`. A mark on the bare class position
`S.<__spring_registry__>` is not restored; no rule makes one (the registry class is generated, and no rule names it).

---

## 32. Deviations from today (`interpreter.md` §6) in code

| # | Reused class | Today | New |
|---|---|---|---|
| D1 | `StatementSummaryBuilder.read` (:74-92) | `keepAllExcept(base, accessors)` + `edge(source, source)` | `MicroEdgeBuilder.read`: `keep(base)` (§24) |
| D2 | same, `base == to` branch (:86-88) | `edge(fact(base).exclude(accessors.first()), null)` | no edge; only `x.f.* -> x.*` |
| D3 | `MethodSequentFlowFunction.transfer` (:65-68) | `to == null -> refineInitial(effect.exclusion)` | no `to == null` edge exists; `ApOps.applyEdge` gives the `above` case in the demand layer |
| D4 | `JIRMethodCallFlowFunction.propagateFact` (:141-143) | `addSideEffectRequirement(factReader)` | no reader; `ApOut.markRequest` (Part I) |
| D5 | `JIRMethodCallSummaryHandler.handleSummary` (:40-69) | `MethodSummaryEdgeApplicationUtils` delta with refinement | `ApOps.satisfying` + `ApOps.applySummary` (Part I) |
| D6 | `JIRMethodCallFactMapper` (:141-242) | `rebase` per fact | `bindIn`/`bindBack` micro edges (§28.2); same mapping and filters |
| D8 | `JIRTaintCleanActionEvaluator` (`TaintEvaluator.kt:29-71`) | `FinalFactAp.clean` with `DeepAccessorExclusion` | `Cleaner` + `ApOps.clean` (`*∖T`, the request on a partial clean) |
| D9 | same, `RemoveMark(.., ExactAndAnyField)` | cleans through an `[any]` only | `CleanReach.AT_AND_BELOW` (§27.5) |
| D10 | same, `RemoveAllMarks(P.AnyField)` | removes an `[any]` child | `CleanReach.BELOW`, every mark |
| D11 | `JIRFactTypeChecker.AccessorFilter` (:84-136) | `FilterResult` over the fact tree, marks, `[value]` and type info as accessors | the same filter as `TypeFilter.may` on the path only (`localFilter`), whose accessors are fields, elements and `<C>` (`ap.md` W5); the mark policy is `TypeFilter.markPolicy`, at the root and below each `[e]` with the element type, as today (§26.2) |
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
| D23 | `JIRMethodCallSummaryHandler.prepareFactToFactSummary` (:71-79), `handleZeroToZero` (:29-38); `JIRMethodCallFlowFunction.unresolvedCallDefaultFactPropagation` (:330-339); `JIRMethodCallRuleBasedSummaryRewriter.userRuleDefinedActions` (:67-85) | the rewriter on fact-to-fact and ND summaries; the default identity in caller coordinates; a user cleaner rule is selected when its condition is not statically false (:80-81) | the stage `Rewrite(RETURNED -> REWRITTEN)` on every result at `RETURNED` (§28.1, §28.3); a user source rule with `!isFalse`, a user cleaner rule only with `isTrue` (`rewriterCleaners`, §28.3) |
| D24 | `TaintConfigUtils.applyPassThrough` (`JVM/TaintConfigUtils.kt:48-60`) | the condition of a pass rule (`CopyAllMarks`, `CopyMark`) is evaluated on the fact | a pass rule with a mark literal is a rule error; it applies without its mark literals (one check, `passRules`, §28.5) and makes no conjunctive edge (`pass`, §27.4) |
| D25 | `JIRAnalysisManager.isReachable` (`JVM/analysis/JIRAnalysisManager.kt:293-301`), called by the method analyzer (`DF/ap/ifds/MethodAnalyzer.kt:296`); `JIRLocalVariableReachability` (`JVM/JIRLocalVariableReachability.kt:27-41`) | a fact on a local that is dead at the statement is dropped; in code that reaches no exit every local is dead (the liveness goes backward from `exitPoints()` of the unwired graph) | no liveness member in `Interpreter`, `DirectedForms` or `JIRMethodEntry` (§23.1, §23.7, §31.2): the statement step keeps a fact on a dead local. The alias analysis keeps its own `JIRLocalVariableReachability` input, as today (§31.2) |
| D26 | `JIRMethodSequentFlowFunction.applyUnconditionalSources` (:228-233), `applyUnconditionalSinks` (:191-200) | the unconditional exit sources fire only at `JMethodExitNormalInst`; the unconditional exit sink is a stub | `exitRules` builds every cube, the empty cube too, and every sink (`ZERO_PATTERN`) at both exits (§29) |
| D27 | `SpringRuleProvider.cleanerRulesForMethod` (`core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringRuleProvider.kt:104-143`); `ndMethodDispatch` (`SpringWebProject.kt:308-313`) | the `__cleanup__` cleaner is built from the fact (`fact ?: return emptyList()`) | the dispatcher saves and restores the registry around `__cleanup__()`; with no fact the provider gives `RemoveAllMarks(AnyClassStatic)`, the whole-base cleaner `(S, atAndBelow, all)` (§31.3, §27.1, §27.5) |
| D28 | `EmptyMethodAnalyzer` (`DF/ap/ifds/MethodAnalyzerStorage.kt:19-31`) | a resolved empty callee, whose analyzer publishes the identity summary; for JIR an empty method has no entry statement (`JMethodBoundaryInstFeature.kt:13`), so it gets no method key and the call drops the bound facts | `resolve()` drops an empty method; every result empty: the unresolved path (§28.4). The empty-method branches go: `JIRMethodEntry` asserts that its method has instructions (§31.2) |
| D29 | `readPositionWithAnyAccessorSplit` (`DF/taint/FactReaderUtils.kt:54-138`) | a rule position with an inner or a repeated `AnyField` is read | `JIRRuleForms.pos` checks the two invariants and rejects the rule element (`RuleErrors`, logged once); it never throws (§27.1) |

D1 and D2 as code (the old builder stays for the prescan):

```kotlin
// Today, StatementSummaryBuilder.kt:83-88
if (base != to) { keepAllExcept(base, accessors); edge(source, source) }       // y\{f} -> y, y.f -> y.f
else { edge(fact(base).exclude(accessors.first()), null) }                     // x\{f} -> null (refine only)
// New, MicroEdgeBuilder.read (Part II §24)
if (base != to) keep(base)                                                     // y.* -> y.*
edge(starEdge(base, path, to, emptyList()))                                    // y.f.* -> x.*
```

D12 as code:

```kotlin
// Today, JIRFactTypeChecker.kt:88-94: an `[any]` node under a primitive type is rejected
is AnyAccessor -> if (actualType.unboxIfNeeded() is JIRPrimitiveType) return FilterResult.Reject
// New: the same AccessorFilter walks only the path (ApOps.filter, Part I §5.5); the `[any]` tail is not an accessor,
// so this case never runs and the `[any]` leaf stays. The policy reads a concrete mark at the root path and at each
// node of the `[e]` chain, with the type of that level (JIRTypeFilters.make, §26.2).
TypeFilter(may = checker.localFilter(t), markPolicy = /* one level per node of the `[e]` chain: JIRTypeFilters.make */)
```

D25 and D28 as code:

```kotlin
// Today, DF/ap/ifds/MethodAnalyzer.kt:296: the statement step runs only for a fact on a live base
if (edgeFactBase == null || analysisManager.isReachable(apManager, analysisContext, edgeFactBase, edge.statement)) { /* step */ }
// New: the step runs for every fact. JIRMethodEntry builds the reachability only as the input of the alias analysis (§31.2).

// Today, a JIR native method of a project class is a ConcreteMethod callee with no entry statement: no key, no stage
// New, JIRCallPlanBuilder.resolve (§28.4)
is ConcreteMethod -> if (!isEmptyMethod(res.method.method)) callees += keys(res.method)
if (results.isNotEmpty() && results.all { it is ConcreteMethod && isEmptyMethod(it.method.method) }) unresolved = true
```

KEPT AS TODAY IN CODE (no row above). The gaps G9 and G10 of `interpreter.md` stay as today: a catch handler reads the
facts after each statement of the try range (the JIR graph adds the handlers to the successors of a throwing statement,
`core/opentaint-utils/opentaint-jvm-util/src/main/kotlin/org/opentaint/jvm/graph/JApplicationGraphImpl.kt:25-29`), and
the catch statement does not kill its local (`JIRStatementForms.build`: a
`catch` gives `StatementSummary.EMPTY`, §26.1); no class initializer `<clinit>` is analysed (no call site, and the entry
points exclude it). The alias analysis is out of scope: Part II does not change it. Its settings (A1: the
interprocedural depth 0, on or off, its time limit) are as configured (`JIRLocalAliasAnalysis.Params`). `aliases()`
(§28.6) has no filter for a static alias base: under A1 such an alias does not hold both before and after a call, so it
does not occur.

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
| 4 | `CallPlanReversalTest` (same) | `Reference.kt` (`revEdge`, `concat`), `ApManager` | the step table of Part II §23.6; guards and filters go; `PASS_OVER` for alias bases; entry/exit swap; a non-forward plan fails; the zero fact passes over and enters (`FormsReference.run`); forward, `FormsReference.run` with `PlanHooks(guards = true)` on a hand-built plan: `END_FACTS` acts only on the zero fact and gives the layer of the sink that fired at `BOUND`, `ALIASES` skips an `IDENTITY` origin, each result gets `StageKind.originOf`, a run from `RETURNED` starts at that point | `Reverse.Call.rev`, `bindRev_of_star` |
| 4a | `FormApplierTest` (same) | `Reference.kt`, `ApManager` | the three modes of `FormApplier` over `ReferenceAlgebra` and over a recording algebra: STATEMENT passes an untouched base and kills a touched one; the operand filter acts on the input before every edge, the result filter on each result; STAGE passes nothing by itself and gives the micro edge of each result; GEN adds results, applies no filter and is never a source-seed place; at a source-seed place the seed filter acts before a source edge and the hit is recorded only after a result; the static exception only with `Place.statementEdge` in run 1; `ReferenceAlgebra.passes` against `ApOps.filter` (Part I §5.5) | `Reverse.Stmt.rev` (the modes), `Statics.genFireB` (the static exception), `Core.filt_keeps` |
| 5 | `JIRStatementFormsTest` (opentaint-jvm-dataflow, `jvm.bidi.interp`; replaces the edge asserts of `JIRStatementSummaryTest`) | `ApManager` | one test per row of §2.2; §2.4 pinned rows; operand vs result filters; read source at `x = C.s` with `ZERO_KEEP`; a read source with a non-`Result` target is a rule error | `Cases.lean` `loadF`, `loadF'`, `storeF` |
| 6 | `JIRRuleFormsTest` (same) | `ApManager` | §4.1 rows, AnyField table; §4.2 negated literal, `Or`, cubes; §5.3 conjunctions (ND sources only); `pass`: a `CopyMark(T, P → Q)` gives the one edge `P.t (T) -> Q.t (T)`; §5.2 one test per mapping row with `<string-bytes>`; D20: a cleaner with a mark literal left gives no step and no request; §4.2 array elements: the alternatives of a call sink, with `SinkRule.alternative` = 0, 1, ... in the cube and array-choice order, the same for two builds; §1.3 the two invariants of a rule position: `[arg0, ".*", ".f"]` and `.*.*` in a source, a sink, a pass rule and a cleaner are each one rule error, logged once, and `pos` does not throw (D29); `AnyClassStatic` in `RemoveAllMarks` gives `CleanStep.Clean(Cleaner(S, [], AT_AND_BELOW, all))`, in any other rule element a rule error; §1.4 rows and rule errors (§33.5 items 14, 16) | `Statics.SWF`, `Statics.CexAny`, `NDExact.LitConc` |
| 7 | `JIRCallPlanTest` (same) | `ApManager` | §3.1 bindings with filters; §3.3 S and zero; §3.5 constructor (no alias: SI15); §3.7 two `UNRESOLVED` stages, the identity has no filter, pass rules, default getter; D24: a pass rule (`CopyAllMarks` or `CopyMark`) with a mark literal is one rule error and gives its plain pass edge without the literal (a `CopyMark(T, P → Q)` with a literal on another position gives `P.$ (T) -> Q.$ (T)`), and the `UNRESOLVED` stages have no conjunctive edge; `UnresolvedCallObserver` calls the tracker with `ruleApplied`; §3.8 aliases + `MemoryEffect`; §3.9 prescan lambdas (D19: no `UNRESOLVED` stage when the prescan knows a lambda); the forward stage table (§33.5 items 10, 14, 17); `passReads` holds the from-bases of the rule-set pass rules and not the `this` of a default getter rule (the tracker gets `ruleApplied = false` for a library getter with no model); §3.6, D28: a call to a native method of a project class has no `Callees` stage and has the `UNRESOLVED` stages, and a call with an empty and a non-empty callee has only the non-empty one; §28.1 a non-immediate call lhs fails (`error`), as today; D27: the Spring `__cleanup__()` call (`SpringRuleProvider` over the rule set, `fact = null`) has the one step `Cleaner(S, [], AT_AND_BELOW, all)`, and the dispatcher restores the registry fields after it | `Reverse.BindTargetsStar`, `Backward.NoZeroBack` |
| 8 | `JIRBoundaryFormsTest` (same) | `ApManager` | §4.3 context filter; §4.7 `globalStateDrop`, `entryMarks`, `entryMarkParts` gives only `(b, [], $, T)`; §4.7 at `JMethodExitExceptionalInst`: the exit sources and sinks with `Result` read as `exc`, `globalStateDrop = false`, no `entryMarks`; D22, D26: an unconditional exit sink has `ZERO_PATTERN` and an unconditional exit source has its zero edge at both exits; §4.7 step 3: `globalStateDrop` is true at a normal exit with a plain or a conjunctive exit sink; exit nodes (the two boundary exits); a method with no boundary instructions fails the `JIRMethodEntry` assert; exit wiring of a loop that never returns | `Backward.ExitReach`, `Backward.ZeroKept` |
| 9 | `JIRFormsContractTest` (same) | `ApManager` | every method of the samples jar: I6, I7 (both `$` clauses), I11 (a)–(d), (f), I12 (a), (b), (c), (e) over `allForwardForms` (§33.4; I11 (e) is test 8, I12 (d) a check of the run config) | `Backward.StmtsMarkRev`, `Reverse.BindTargetsStar`, `Backward.NoZeroBack`, `Backward.ZeroKept`, `Statics.SWF`, `Invariant.no_univ_star` |
| 10 | `JIRTypeFiltersTest` (same) | `ApOps.filter` | §5.1 rows; `*`/`[any]` tails kept; the mark policy on `int` and `Integer`, a `%%primitive%%` mark kept; below `[e]`: on `int[]` and `Integer[]` the policy drops `a.[e].$ (T)` and keeps `a.[e].$ (T%%primitive%%)`, on `int[][]` level 2, on `Object[]` and `String[]` no policy; a leaf off the `[e]` chain stays; prefix-closed | `Exact.FiltValid`, `Core.filt_keeps` |
| 11 | `JIRStatementEffectTest` (same) | `ApOps` | the effect table of §2.4 and the table of `ap.md` §4.2; for each statement form and each mode, the core result (`Facts`) `agrees` with `FormsReference` (§23.8) on FLOW, TAINT and `Reach` inputs, with the premise of each input (so the static exception agrees: `x = C.s` on `S.*` with the premise `S.*` in run 1 gives the position request `[<C>, s]` and no fact on `x` in both); a synthetic `a.f = b.g` (as the synthetic statement of §33.2) fails the `to !is MemoryAccess` check (§26.1), as today; `ops.without` with `entryMarkParts` keeps `b.f.$ (T)` and `b.[any] (T)`; the zero binding: the `BIND_IN` stage of a `JIRCallPlanBuilder` plan, applied by `ops.applyEdge` (STAGE mode), gives `Reach.NORMAL` from `Reach.NORMAL` and `Reach.DEMAND` from `Reach.DEMAND`, and `FormsReference.run` agrees per path (the zero fact reaches `BOUND` and the entry of the callee) | `Cases.lean` examples at lines 61–89 |
| 12 | the analysis tests of `interpreter.md` §7.1 | Part I and `analyzer-impl.md` | end to end, through phase 3 (`analyzer-impl.md` §8.1) | — |

Order: by the "Needs" column. 1 → 2 → 3 → 4 → 4a (`Reference.kt` and `ApManager` only, no JIR) → 5 → 6 → 7 → 8 → 9
(JIR and `ApManager`) → 10 → 11 (Part I `ApOps`) → 12.

### 33.2 Example: the pinned rows of `interpreter.md` §2.4

`testInterpreter`, `testKey` and `TestRules` are helpers of `JIRInterpreterTestKit` (test sources): a `JIRMethodEntries`
over `cp` with `JApplicationSingleExitGraph`, a `TaintRulesProvider` made from lists, and the key
`MethodEntryPoint(EmptyMethodContext, entry statement)` of the method of a statement. `cp` is the classpath of
`BasicTestUtils` (`UnknownClasses`, `JMethodBoundaryInstFeature`: the boundary feature of §31.2); test 17 also installs
the two lambda features.

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
        val hooks = PlanHooks(callees = { _, i ->                                         // the callee maps ret to arg0
            if (i.c.fact.base == ret) listOf(i.copy(c = i.c.copy(fact = i.c.fact.copy(base = arg0)))) else emptyList() })
        fun item(c: Conclusion) = listOf(PlanItem(emptySet(), c, origin = null))
        val req = Conclusion(PathFact(r, emptyList(), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty, demand = false)
        val ref = FormsReference(ApOps(manager))
        val at = Place(testCall(), statementEdge = false, sources = false)            // a JIR call statement of the test kit
        val trace = ref.run(rev, item(req), at, hooks)
        assertTrue(trace.any { (p, i) -> p == BOUND && i.c.fact.base == Z })             // step 3: the zero demand
        assertTrue(trace.any { (p, i) -> p == BEFORE && i.c.fact.base == a })             // steps 5.1, 6, 8
        val onB = Conclusion(PathFact(b, listOf(f), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty, false)
        val tb = ref.run(rev, item(onB), at, hooks)
        assertTrue(tb.any { (p, i) -> p == BEFORE && i.c.fact.base == b })                // PASS_OVER (A5)
        assertTrue(tb.any { (p, i) -> p == REWRITTEN && i.c.fact.base == ret })           // reversed alias edge (AC5)
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
            assertTrue(e.from.tail != Tail.EXACT || e.from.mark is MarkSlot.Concrete) // I7, S8: a `$` premise
            assertTrue(e.to.tail != Tail.EXACT || e.from.mark is MarkSlot.Concrete)   // I7, S8: a `$` target
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
        assertTrue(forms.staticWellFormed())                                        // I12 (a), (b), (c), (e), Statics.SWF
    }
}
```

The helpers (test sources, beside the test). `allForwardForms` lists the forward forms of ONE method key: the
statement summary of every non-call instruction, the call plan of every call instruction (the plans are per key, §28;
the key is `testKey(method)`, the `EmptyMethodContext` key of §33.2), the entry rules, and the exit rules at both exits.
The backward forms are their reversals (tests 1, 2, 4), so the contract over the forward forms covers them.

```kotlin
/** The forward forms of one method key. */
class ForwardForms(val statements: List<StatementSummary>, val plans: List<CallPlan>, val entry: RuleStatement,
                   val exits: List<ExitRules>)

fun allForwardForms(interp: JIRInterpreter, key: MethodKey): ForwardForms {
    val (calls, others) = (key.method as JIRMethod).instList.instructions.partition { it.callExpr != null }
    return ForwardForms(
        statements = others.map { interp.statementSummary(key, it) },
        plans = calls.map { interp.callPlan(key, it, it.callExpr!!) },
        entry = interp.entryRules(key),
        exits = interp.exitNodes(key).map { interp.exitRules(key, it.node) })
}

private fun pathEdges(ss: List<StatementSummary>): List<PathEdge> = ss.flatMap { s -> s.edges.map { it.edge } }
private fun ForwardForms.edgeStages(kind: StageKind) =
    plans.flatMap { p -> p.stages.filterIsInstance<CallStage.Edges>().filter { it.kind == kind } }
fun ForwardForms.stages(kind: StageKind): List<StatementSummary> = edgeStages(kind).map { it.summary }
private fun ForwardForms.kills(): List<CleanStep.Kill> =
    plans.flatMap { p -> p.stages.filterIsInstance<CallStage.Clean>().flatMap { it.steps.filterIsInstance<CleanStep.Kill>() } }

/** The STATEMENT-mode summaries (§23.3): the statement summaries, the rule statements of the entry and of the exits,
 *  the keep edges of the kills. */
fun ForwardForms.statementModeSummaries(): List<StatementSummary> =
    statements + entry.summary + exits.map { it.rules.summary } + kills().map { it.keepEdges }
/** The STATEMENT MICRO EDGES (ap.md §4.10 item 1): the STATEMENT-mode summaries and the stages with
 *  `StageKind.statementEdges` (SOURCES, UNRESOLVED). */
fun ForwardForms.statementEdges(): List<PathEdge> =
    pathEdges(statementModeSummaries() + stages(StageKind.SOURCES) + stages(StageKind.UNRESOLVED))
fun ForwardForms.bindings(): List<PathEdge> = pathEdges(stages(StageKind.BIND_IN) + stages(StageKind.BIND_BACK))
fun ForwardForms.bindBack(): List<PathEdge> = pathEdges(stages(StageKind.BIND_BACK))
fun ForwardForms.aliasEdges(): List<PathEdge> = pathEdges(stages(StageKind.ALIASES))
/** Every cleaner: the steps of the `Clean` stages and the rewriter. */
fun ForwardForms.cleaners(): List<Cleaner> = plans.flatMap { p -> p.stages.flatMap { st ->
    when (st) {
        is CallStage.Clean -> st.steps.filterIsInstance<CleanStep.Clean>().map { it.cleaner }
        is CallStage.Rewrite -> st.cleaners
        else -> emptyList()
    } } }
fun ForwardForms.sinkPatterns(): List<Pattern> =
    (plans.flatMap { it.sinks } + entry.sinks + exits.flatMap { it.rules.sinks }).flatMap { it.patterns }

/** I12 (a), (b), (c), (e) (Lean `Statics.SWF`: `ss`, `toC`, `fromC`, `clean`). (d) is a check of the run config
 *  (`fieldLimit >= 1` in run 1), (f) holds by the type of `AccessPathBase`, (g) is a rule of the engine (ap.md §6.2).
 *  (b) is checked in its strong form: a target path on `S` with fewer than two accessors (the root or a class `[<C>]`)
 *  counts as strictly above a static position. The forms of §1.4 meet the strong form. */
fun ForwardForms.staticWellFormed(): Boolean {
    val s = AccessPathBase.ClassStatic
    fun dollarConcrete(f: PathFact) = f.tail == Tail.EXACT && f.mark is MarkSlot.Concrete
    // (a) S to S: an identity restriction `S.q.* ->_E S.q.*`, or a field-to-field edge (a pass rule between static fields)
    val a = statementEdges().filter { it.from.base == s && it.to.base == s }.all { e ->
        (e.from == e.to && e.from.tail == Tail.STAR && e.from.mark == MarkSlot.STAR) ||
            (e.from.path.size >= 2 && e.to.path.size >= 2)
    }
    // (b) another base into S above a static position: a `$` target and a `$` premise with a concrete mark; a
    //     conjunctive edge: each literal
    val b = statementEdges().filter { it.from.base != s && it.to.base == s && it.to.path.size < 2 }
        .all { dollarConcrete(it.to) && dollarConcrete(it.from) }
    val bConj = (statementModeSummaries() + stages(StageKind.SOURCES)).flatMap { it.conjunctions }
        .filter { it.target.base == s && it.target.path.size < 2 }
        .all { c -> dollarConcrete(c.target) && c.literals.all { dollarConcrete(it.fact) } }
    // (c) a call binds S only by `S.* -> S.*`; an alias edge never targets S (under A1 no static alias base occurs, §32)
    val c = (bindings() + aliasEdges()).filter { it.from.base == s || it.to.base == s }.all { it == keepEdge(s) }
    // (e) a cleaner on S names its mark, except the whole-base cleaner `(S, atAndBelow, all)` with the empty path
    val e = cleaners().filter { it.base == s }.all { it.mark != null || (it.path == null && it.reach == CleanReach.AT_AND_BELOW) }
    return a && b && bConj && c && e
}
```

### 33.5 The new tests of `interpreter.md` §7.2 (items 8 to 10 and 14 to 17)

Items 1 to 7 and 11 to 13 are rows of §33.1 (tests 1 to 11). Part of items 8 and 9 is also in `analyzer-impl.md`
(`ModesTest`: a request in a restricted run fails; `FactKindsTest`: no request from a TAINT or a `Reach` input).
Items 18 to 25 are rows of §33.1 or of `analyzer-impl.md` §9.1: 18 (no liveness) `DeltaWorklistTest`; 19 (rule
positions) test 6; 20 (the whole-base cleaner) tests 6 and 7; 21 (empty methods) test 7 and `ModesTest`; 22 (aliases on
call results) and 25 (end facts) `CallPlanRunnerTest`; 23 (the global-state rule) test 8 and `ExitRulesTest`; 24 (the
mark policy below `[e]`) test 10.

| Item | Test (class) | Form check (Part II) | End to end (`analyzer-impl.md`, phase 3) |
|---|---|---|---|
| 8 requests (§5.4) | `JIRStatementEffectTest` (the forms of a JIR sample with `ApOps` in run 1), `JIRCallPlanTest` | one case per row of §5.4, each on a FLOW input with the mark `*`: a sink at a call and an exit sink: `checkMark` gives `MarkCheck.Request(T)`; a conjunctive sink: one request per literal; a conditional source at a call and an exit source, a `CopyMark(T)` pass rule, an ND source literal: the mark gate of `applyEdge` gives the mark request; a cleaner action and the rewriter on a partly cleaned position: the `clean` request, and none if the mark excludes `T`; the static rows: `x = C.s` on `S.*` (premise `S.*`) gives the position request `[<C>, s]`, `C.s = x` the request `[<C>]` of the class keep edge, a sink on `S.<C>.f` the mark request; the entry rules and a read source: no request. The same forms in a restricted forward run and in the backward run: the request assert fails (ap.md §13 item 9) | the run-1 request reaches the caller premise (`interpreter.md` §5.4) |
| 9 ND (§5.3) | `JIRRuleFormsTest`, `JIRStatementEffectTest` | `AssignMark(T, Result) if ContainsMark(Argument(0), A) && ContainsMark(Argument(1), B)` gives one `ConjunctiveEdge` with two literals in the `SOURCES` stage; the two inputs in both orders give the same result (`ConjunctionStore`, Part I §7.10), with the union of the premise sets without the zero fact; a sink with the same condition is one `SinkRule` with two patterns: one `Holds` stores an input and gives no witness, the second gives one | the conjunctive source and the conjunctive sink act only when both arguments are tainted, in either order of arrival |
| 10 the rule statement of a call (§4.1) | `JIRCallPlanTest` | the `SOURCES` stage has `ZERO_KEEP` and the source edges only (no keep edge of another base); `FormsReference.run` on the plan: the zero fact reaches `REWRITTEN` by `ZERO_KEEP` and gives the target of an unconditional source; with `AssignMark(T, Result) if ContainsMark(Argument(0), T)`, a fact on `arg0` with `T` gives only `ret.$ (T)` through `SOURCES`, and `arg0` reaches `REWRITTEN` only through the callees or the `UNRESOLVED` stages | the read argument comes back only through the callee summary or the unresolved path |
| 14 array elements of a call sink (§4.2) | `JIRRuleFormsTest`, `JIRCallPlanTest` | a sink `ContainsMark(Argument(0), T)` on an `Object[]` argument gives two `SinkRule`s with the patterns `(arg0, [], $, T)` and `(arg0, [e], $, T)`, one `rule`; on a `String` argument one `SinkRule`; a conjunctive sink on two array arguments gives four alternatives; the receiver, `Result`, the entry and the exit sinks get none | `arg(0).[e].$ (T)` triggers the sink; the backward run seeds `seedPatterns()` of both alternatives |
| 15 exit rules at the exceptional exit (§4.7) | `JIRBoundaryFormsTest` | `exitRules(m, JMethodExitExceptionalInst)`: an exit sink on `Result` has the pattern on `exc`; an exit source on `Result` targets `exc`; `globalStateDrop` false, `entryMarks` empty; `reversed()` gives the backward start rules of that exit | an exit sink on `Result` triggers on the thrown tainted value; an exit source at the exceptional exit adds no summary edge |
| 16 cleaners (§4.2, D20) | `JIRRuleFormsTest` | `RemoveMark(T, P) if ContainsMark(P, T)` and `RemoveMark(T, arg0) if Not(ContainsMark(arg1, RAW))` give no `CleanStep`; the same rule with no condition gives `Cleaner(P, EXACT, T)` (and `<string-bytes>` on a `String` position) | the first two do not clean; the third cleans |
| 17 lambdas (§3.9, D19) | `JIRCallPlanTest` (a cp with the lambda features, §31.2) | a call through a FUNCTIONAL INTERFACE OF THE PROJECT (`sample.lambda.StringOp`, one abstract method): with prescan lambdas for the call, a `Callees` stage with the lambda methods and no `UNRESOLVED` stage; with none, no `Callees` stage for the lambda and the `UNRESOLVED` stages. A second case through a JDK interface (`java.util.function.Function`): the resolver adds its own `MethodResolutionFailed` (`JIRCallResolver.kt:160-163, 174-178`), so the `UNRESOLVED` stages stay beside the `Callees` stage | the known lambda of a project interface takes no unresolved path; the unknown one does; a JDK interface keeps the unresolved path |

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
    assertEquals(listOf(0, 1), plan.sinks.map { it.alternative })                     // one witness per alternative
    val again = JIRCallPlanBuilder(interp, interp.entries[key], key, s as JIRInst, call as JIRCallExpr).build()   // no cache
    assertEquals(plan.sinks.map { it.alternative to it.patterns }, again.sinks.map { it.alternative to it.patterns })   // stable
    val (key2, s2, call2) = callOf("sample.ArraySink", "callWithString")             // sink((String) a)
    assertEquals(listOf(listOf(pat())), interp.callPlan(key2, s2, call2).sinks.map { it.patterns })
}
```

`TestRules`, `sinkOn` and `callOf` are helpers of `JIRInterpreterTestKit` (§33.2). `sample.ArraySink` is a new sample
class: `callWithArray(Object[] a) { Sinks.sink(a); }` and `callWithString(String a) { Sinks.sink(a); }`.

### 33.6 Example: `FormApplierTest`

```kotlin
class FormApplierTest {
    private val manager = ApManager(Cancellation())
    private val x = AccessPathBase.LocalVar(1); private val y = AccessPathBase.LocalVar(2); private val z = AccessPathBase.LocalVar(3)
    private val T = manager.marks.mark("T")
    private fun conc(b: AccessPathBase) = Conclusion(PathFact(b, emptyList(), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty, false)
    private val hits = ArrayList<MicroEdge>()
    private val alg = ReferenceAlgebra(ApMode(run1 = true, Direction.FORWARD, fieldLimit = 4),
        allowsSource = { _, _ -> true }, sourceHit = { _, me -> hits += me }, manager = manager)
    private val applier = FormApplier(alg)
    private val at = Place(testCall(), statementEdge = false, sources = true)

    @Test // §23.3 STATEMENT: x = y passes z, kills the old x, moves y to x
    fun `statement passes an untouched base and kills a touched one`() {
        val s = MicroEdgeBuilder().apply { move(x, y) }.build()
        fun run(c: Conclusion) = buildList { applier.statement(s, emptySet(), c, at) { _, r -> add(r.fact.base) } }
        assertEquals(listOf(z), run(conc(z)))                                    // untouched: passes
        assertEquals(emptyList(), run(conc(x)))                                  // touched, no edge from x: the kill
        assertEquals(setOf(x, y), run(conc(y)).toSet())                          // y.* -> y.*, y.* -> x.*
    }

    @Test // §23.1 the source-seed places: a source hit in a source stage, never in GEN
    fun `a source edge records its hit only at a source-seed place`() {
        val src = MicroEdgeBuilder().apply { keepZero(); edge(PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, MarkSlot.Concrete(T)), ExclusionSet.Empty)) }
        val zero = Conclusion(ZERO_FACT, ExclusionSet.Empty, false)
        applier.statement(src.build(), emptySet(), zero, at) { _, _ -> }
        assertEquals(1, hits.size)                                               // the source, not the zero keep edge
        applier.gen(src.buildGen().edges, emptySet(), zero) { _, _ -> }
        assertEquals(1, hits.size)                                               // GEN: no hit
    }
}
```

---

## 34. Spec issues and deviations from today

This document implements the specs as they are. Each row below is a point where a spec was not clear, or where the spec
(and so this proposal) differed from today's code and `interpreter.md` §6 did not list the difference. The user decided
the rows on 2026-10-07 (`ap-history.md` F63), SI3 again on 2026-10-08 (F65), and SI11, SI12 and SI17 on 2026-10-08
(F67); the specs now say the decisions. The column "Decision" gives the decision
and the place in the spec; "as proposed" means that the proposal stands. The columns "This proposal" and "Effect" give
the code of this document after the decision. Every row stays as a record. The ids `SI1` to `SI17` are ids of this
document; they are not the rules `S1` to `S14` of `ap.md`.

| Id | Spec | Today (`path:line`) | This proposal | Effect on the findings | Decision (2026-10-07 unless the row says another date) |
|---|---|---|---|---|---|
| SI1 | `interpreter.md` §4.1, §4.5 step 3 | A call sink on `Argument(i)` that can be an array also reads `arg(i).[e]` (`JVM/taint/JIRMethodCallTaintUtil.kt:186-203`). The spec has no such pattern. | A sink at a call has one alternative per array choice: the literal on `arg(i)·ρ`, and `(arg(i), [e]·ρ, t, T)` when `callArgumentMayBeArray` holds (§27.3, §28.1). (Was: no `[e]` pattern.) | None: as today. | As on main: `interpreter.md` §4.2 ARRAY ELEMENTS OF A CALL SINK; §6 "kept as today". |
| SI2 | `interpreter.md` §4.7 | The production rule provider fires the exit sinks only on zero-premise edges (`core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/JIRMethodExitRuleProvider.kt:18-19`, installed at `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/Provider.kt:52`). The spec checks every fact. | The exit sinks check every fact (`sinkRulesForMethodExit(..., initialFacts = null)`, §29). | More: exit-sink reports also for taint that enters the method through a parameter. | As proposed: `interpreter.md` D21. |
| SI3 | `interpreter.md` §4.1, §4.2, §5.3; `ap.md` S9 | A pass rule applies only when its condition holds on the fact (`applyPassThrough`, `JVM/TaintConfigUtils.kt:48-60`; `applicableRules`, `:77-92`). The spec has no exact form for a `CopyAllMarks` rule with a mark condition: its `*` premise cannot be a conjunction literal (`ap.md` S9). | Every pass rule (`CopyAllMarks`, `CopyMark`) with a mark literal is a rule error (`RuleErrors`), and it applies without its mark literals (one check, §28.5); a pass rule makes no conjunctive edge (§27.4). (Was: only `CopyAllMarks`; a `CopyMark` with another literal made a conjunctive edge.) | More, only for such a rule; the JVM rule sets probably have none. | Every pass rule (user decision, 2026-10-08; `ap-history.md` F65): `interpreter.md` §4.2 (the pass-rule bullet), §5.3, D24. |
| SI4 | `interpreter.md` §5.3 | The spec says that exit sources never make an ND edge, but an exit source can have two positive literals. Today such a rule can reach `createNDEdge`, which calls `error("Unused operation")` (`JVM/analysis/JIRMethodSequentFlowFunction.kt:217-218`), and the analysis stops. | A rule error (§29): the interpreter rejects the cube and logs it once. | Fewer than the rule asks for: such an exit source gives no fact. Today the analysis can fail. | Not in F63: the proposal stands; the spec is unchanged. |
| SI5 | `analyzer-core.md` §4.5 (the stage table) and `interpreter.md` §3.5 | The constructor pass-over takes every added fact, also a fact on `S` (`JVM/analysis/JIRMethodCallFlowFunction.kt:213-216`). The stage table says "the receiver and argument positions"; `interpreter.md` §3.5 says "every added fact". | The `CONSTRUCTOR` stage has the identity of every bound position, `S` included (§28.1). | None: as today. | Not in F63: the proposal stands (`interpreter.md` §3.5); the spec is unchanged. |
| SI6 | `interpreter.md` §3.1 | The binding back keeps a fact on a constant base as it is (`JVM/JIRMethodCallFactMapper.kt:157-160`). The spec lists `const.* → const.*`, but no finite edge form exists for it, and no form makes a fact on a constant base. | No edge for a constant base (§28.2). | None: no fact has a constant base at a callee exit. | Not in F63: the proposal stands; the spec is unchanged. |
| SI7 | `interpreter.md` §3.9 | A lambda call is also an unresolved call: the resolver adds `ResolutionFailure` beside the lambda methods (`JVM/analysis/JIRMethodCallResolver.kt:191`). The spec says that the call "becomes a resolved call". It does not say if the unresolved path stays. | A `Lambda` result is the prescan lambda methods only; with none it is a resolution failure (§28.4). | Fewer: a flow that only the pass rules or the default identity of the lambda call give is lost. | As proposed: `interpreter.md` §3.9, D19. |
| SI8 | `analyzer-core.md` §4.9 | One list of filters per base (`StatementSummary.BaseTransfer.typeFilters`, `DF/ap/ifds/summary/StatementSummary.kt:10-14`) holds the operand filters and the lhs filter (`JVM/analysis/JIRStatementSummary.kt:71`). `transfer` applies all of them to the input fact (`DF/ap/ifds/analysis/MethodSequentFlowFunction.kt:50-53`). The spec has one `typeFilters` map per base, but `interpreter.md` §2.1 step 5 and `interpreter.md` §3.1 filter the results. | `StatementSummary.resultFilters` beside `typeFilters` (§23.2, §22.2). | Precision only: a result filter drops only paths that the static type cannot have (`ap.md` S5). The mark policy keeps its gap (`interpreter.md` G6). It can remove a false positive. | As proposed: an addition to `analyzer-core.md` §4.9 (§22.2); the spec is unchanged. |
| SI9 | `analyzer-core.md` §4.5 | On `origin/saloed/backward-main`, a requirement on a base that the call does not touch passes over the call (`skipCall`, `BWD/JIRBackwardMethodCallFlowFunction.kt:67-72`), and each alias adds its unaliased demand (`callSiteAliasDemands`, `:116-138`). The spec: `StatementSummary.reversed` adds the identity of `interpreter.md` A5 for an untouched target. Inside a call stage the two points have other coordinates, so that identity is wrong there. The alias-base identity must go from `AFTER` to `BEFORE`, and the step table has no such stage. | STAGE mode touches every base of its edges, so `reversed()` adds no identity. `CallPlan.reversed()` adds the stage `AFTER → BEFORE` of kind `PASS_OVER` (§23.6). | None: the requirement on an alias base passes over the call, as on the backward branch. | As proposed: an addition to `analyzer-core.md` §4.9 (§22.2); the spec is unchanged. |
| SI10 | `interpreter.md` §4.2, §5.2 | Every `RemoveMark` on a `String` position also cleans `P.<string-bytes>`, also for a cleaner with a condition (`JVM/taint/TaintEvaluator.kt:43-61`, after `applyCleaner`, `JVM/TaintConfigUtils.kt:62-75`). The spec gives the `<string-bytes>` row of `interpreter.md` §5.2 for every cleaner, but for a conditional cleaner the literal at `P` does not decide `P.<string-bytes>`. | Every acting cleaner is unconditional (SI13), so the `<string-bytes>` row of `interpreter.md` §5.2 applies to every acting cleaner and to the rewriter (§27.5). (Was: only for an unconditional cleaner.) | None beyond SI13: a conditional cleaner does not act at all. | Resolved by SI13: `interpreter.md` §4.2, §5.2 (only an unconditional cleaner acts), D20. |
| SI11 | `interpreter.md` §4.7, §6 ("as today") | The conditional exit sources and the exit sinks also run at `JMethodExitExceptionalInst` on a non-zero fact, with `Result` read as the thrown value (`JVM/analysis/JIRMethodSequentFlowFunction.kt:124-126`, `JVM/taint/JIRSequentTaintUtil.kt:67, 82`). The UNCONDITIONAL exit sources fire only at the normal exit: the zero fact runs them only at `JMethodExitNormalInst` (`JVM/analysis/JIRMethodSequentFlowFunction.kt:228-233`), and the fact path skips a rule with a true condition (`DF/taint/TaintUtil.kt:82-83`). The unconditional exit sink is a stub at the normal exit only (`:191-200`). | The exit rules run at both exits; at the exceptional exit `Result` reads `exc`, and steps 3 to 5 do not apply (`ruleFormsAtThrow`, §29). The unconditional exit sources (the empty cube) and the unconditional exit sinks (`ZERO_PATTERN`) fire on the zero fact at BOTH exits (§29). (Was: `ExitRules.EMPTY` at the exceptional exit.) | The conditional exit rules: none, as today. More: an unconditional exit source also fires at the exceptional exit (its facts end there, but an exit sink of that exit can read them, and the backward run records its source hit there); an unconditional exit sink can report at both exits (two statements, so two vulnerabilities). | Both exits: expected and approved (2026-10-08, `ap-history.md` F67): `interpreter.md` §4.7, D26 (the conditional exit rules stay "kept as today", §6); `analyzer-core.md` §4.3, §4.4. |
| SI12 | `interpreter.md` §4.1, §4.7; `ap.md` §4.9 | An unconditional exit sink never fires on the zero fact (`JVM/analysis/JIRMethodSequentFlowFunction.kt:191-200`, a TODO, at the normal exit only). It fires once per non-zero fact at the exit (`DF/taint/TaintUtil.kt:183-186`). | Its pattern is `ZERO_PATTERN` (§27.3): it fires where the zero fact reaches an exit, at both exits (§29), as D22 says. | More: also in a method with no taint at the exit, and at both exits. | As proposed: `interpreter.md` D22; both exits: D26 (2026-10-08, `ap-history.md` F67). |
| SI13 | `interpreter.md` §4.2, §6 | A conditional cleaner fires when its condition holds on the bound fact. A negated literal counts as true (`DF/taint/TaintFactAwareConditionEvaluator.kt:37`, `JVM/TaintConfigUtils.kt:77-92`), and a literal with another mark at the same position reads the same fact. | Only an unconditional cleaner acts: a cleaner with a mark literal left after the static evaluation gives no step and no request (§27.5). (Was: the decided part `(P, exact, T)`.) | More: a conditional cleaner never cleans (possible false positives). | `interpreter.md` §4.2 (rewritten), D20; `ap.md` §4.2, §4.7. |
| SI14 | `interpreter.md` §3.7 item 1, §5.2 ("the same") | The summary rewriter acts only on fact-to-fact and ND summaries (`JVM/analysis/JIRMethodCallSummaryHandler.kt:71-90`, called at `DF/ap/ifds/MethodAnalyzer.kt:995, 1032, 1071, 1180`), not on a zero-premise summary (`handleZeroToZero`, `:29-38`). It rewrites the default identity in caller coordinates (`JVM/analysis/JIRMethodCallFlowFunction.kt:330-338`), so there it acts only by chance. | The `Rewrite` stage acts on every result at `RETURNED`: the zero-premise summaries and the default identity too (§28.3). | Fewer: on a method with a user-defined rule, a source of the same mark in the method body loses that mark at the rule positions. | As proposed: `interpreter.md` D23. |
| SI15 | `interpreter.md` §3.5 and §3.8 AC3, AC4 | The constructor pass-over takes no alias (`JVM/analysis/JIRMethodCallFlowFunction.kt:213-216`). `interpreter.md` §3.5 sends the pass-over "through the aliases", but AC3 does not list it, and AC4 drops an identity result. | The pass-over has `Origin.IDENTITY`, so `Guard.MemoryEffect` drops it (§28.1), as today. | None: the alias holds the same fact (AC4). | Not in F63: the proposal stands (as today); the spec is unchanged. |
| SI16 | `analyzer-core.md` §4.8, §4.9 ("per (method, statement)") | The flow-function caches are per context (`JVM/analysis/JIRMethodAnalysisContext.kt:41-76`). | The call plans and the entry rules read the context (the callees, the start filter), so they are cached per method key. The statement summaries and the exit rules are cached per method (§31.2, DD11). | None: a cache per method would give the callees of one context to another. | As proposed: DD11; the spec is unchanged. |
| SI17 | `interpreter.md` §4.7 step 3, G2, §5.3 | The global-state rule drops the evaluated `S` facts of an exit sink that was REACHED: `allEvaluatedFacts` is filled only in `handleReachedSink` (`JVM/taint/JIRSequentTaintUtil.kt:76-85`) and dropped by `dropFinalFacts` (`JVM/analysis/JIRMethodSequentFlowFunction.kt:186-188, 271-278`). A literal of a conjunctive exit sink that does not complete it stores an assumption (`JIRSequentTaintUtil.kt:47-59`), and its `S` fact stays in the summary. | THE EVALUATED STATICS GO: the part of an `S` item on which a mark literal of an exit sink holds is dropped from the summary edge, for a plain and for a conjunctive exit sink; the conjunctive branch stores that part as the input of its literal, so it stays an assumption for the next evaluation attempts of the sink (§29 steps 2 and 3). | Fewer facts in the callers: an `S` part that a literal of an incomplete conjunctive exit sink read no longer reaches them. The combination is not lost: a later item completes it with the stored input. The shape exists: the rule generator joins the state check to the condition of an exit sink (`addStateCheck`); it is rare. | Drop the evaluated statics, keep them as the stored literal input (2026-10-08, `ap-history.md` F67): `interpreter.md` §4.7 step 3, G2, §5.3. |
