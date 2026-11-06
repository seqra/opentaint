# Directed local alias analysis — implementation proposal

This document tells how to implement the analysis of `directed-alias-analysis-spec.md` (the spec) in the JVM dataflow engine. The spec is normative. This document adds only the implementation decisions, the data structures, the proof obligations of the implementation, and the test plan. Section numbers `§S n` refer to the spec.

Lean model: `formal/directed-alias` (`./check.sh`). The proofs of this document are in `DirectedAlias/Impl/`.

## 1. Semantic scope

### 1.1 Selected changes

All changes come from the spec. The user selected them (decisions D1, D2, D15 and the spec review). The table gives the behaviour of main and the new behaviour.

| Change | Main (DSU) | New | Invariants and proofs |
|---|---|---|---|
| Relation | Partition: symmetric, transitive, congruent | Order on origin sets; may-alias = a common origin (§S 2) | `node_antisymm`, `above_trans`, `path_mono`, `may_iff_common_lower` |
| Join `if (c) a = x else a = y` | `x ~ a ~ y`, so `x ~ y` | `x ~ a`, `a ~ y`, not `x ~ y` | `transitive_sound_relates_x_y` |
| Strong update | Guard counts elements (defect U1) | One unique origin, no reached prefix, not in `Eval` (§S 5.3) | `csoundVS`, `store_shortcut` |
| Unresolved call | Removes heap aliases of the arguments (U2) | Passive: no heap write; it only blocks later strong updates (§S 5.6) | `csoundVS`, `callVSO_heap_frame` |
| Field read | Reader joins the group of the cell | Reader gets the cell content; nulls have an identity (§S 5.2) | `user_answers`, `nulls_exact` |
| Recency | none | `new(s)` / `old(s)` (§S 3, §S 5.1) | `csoundVS` (with `retireV`), `den_retireE` |
| Constants | One element for each site | `const(v)`, shared by value (§S 3). Boxes: see I3 | `const_answers` |
| Exceptions | State after the cut-graph thrower | Join of the states before and after each thrower of the raw graph, also inside inlined callees (§S 5.5) | `csoundCfg`, `inlined_answer` |
| Loop at the first instruction | Back edge ignored | Back edge joined | `loopEntry_answers` |
| Answers | Group members, cut by an order-dependent cache | Backward search, complete to depth D, sorted, no duplicates (§S 5.7) | `findAlias_iff`, `holders_iff` |

### 1.2 Decisions of this proposal

The user decided these items on 2026-11-06.

| Id | Item | Decision |
|---|---|---|
| I1 | Strong-update test after calls (§S 7, D14) | The forward sets: `Etree` and `Eval` are two reserved keys of `env` (§S 5.6). The on-demand test (design §7.6) is not implemented. |
| I2 | Catch variable | As the spec: `{⟨s⟩}` only. A value that a `throw` of the analyzed code throws is not related to the catch variable (gap G3 of §1.4). |
| I3 | Box constants | `Integer.valueOf(<constant v>)` gives `const(Integer, v)`, shared by all sites with the same `v`. A box of a non-constant value gives an own origin `box(s)` for each site. Both are never unique. |
| I4 | Array element query (CS8, vararg) | Paths of §S 5.7 plus the allocation and constant items of the element value |

Other parameters: `entryUnique` on (D1). Recency on, with no switch: it is the proposed value (§S 7), and the Lean model of design VS proves only this form. K = 7 and D = 6 are parameters (open, §S 7). No volume control yet: D11 is decided after the shadow measurement (§8).

### 1.3 Behaviour that does not change

- The public types `AliasInfo`, `AliasApInfo`, `AliasAllocInfo`, `AliasAccessor`. Their `equals` and `hashCode` do not change.
- The consumers: no code change except the vararg branch of `JIRBasicAtomEvaluator` (I4, §6.3).
- `null` answer on a time-out, on an unreachable statement, and when `useAliasAnalysis = false`.
- Static writes are ignored (A5, §S 5.3), as on main. The static type name in `AliasAccessor.Static` is the string of main (`field.enclosingType.typeName`).
- `null` is never reported. Callee variables and callee allocations are never reported.
- Inlining depth: 1 in production, 0 in tests (D12).
- No exemption for calls with only primitive arguments (§S 5.6 has none; D10).
- CS7 type constraints: no change of `JIRCallResolver` (D9 is out of scope).
- The shared module `opentaint-dataflow` and Go: no change (D6). The DSU stays as it is (D13).

### 1.4 Accepted losses and gaps

Precision losses. The analysis keeps an alias that no execution has.

| Id | Shape | Example | Lean |
|---|---|---|---|
| L1 | Store through a value read before a call on its holder | `t = x.f; m(x); t.g = z` is weak | `losses_VS`, `losses_noneV` |
| L4 | Store through a value found in a reached cell | `this.box = b; touch(this); b.value = v` is weak | `losses_VS`, `losses_noneV` |

Soundness gaps. The analysis misses a real alias. Each gap is an assumption of §S 3. For G1-G3 the Lean model gives an execution that has the alias.

| Id | Shape | Example | Lean |
|---|---|---|---|
| G1 | Static write (A5) | `C.f = v; t = C.f`: `t ~ v` is false | `gapA`, `gapB` |
| G2 | Entry aliasing (A1) | A caller passes one object as two arguments, or passes an interned constant | `skip_unsound` |
| G3 | Local throw (I2) | `e = new E(); try { throw e; } catch (E c) { c.f = v; } t = e.f`: `t ~ v` is false | `catch_gap`, `catch_real`, `csoundCfgA6` |
| G4 | Box cache (I3) | `a = Integer.valueOf(n); b = Integer.valueOf(1)`: `a ~ b` is false, also if `n == 1` | none (outside the model) |

### 1.5 Hidden changes (checked)

| Place | Effect | Status |
|---|---|---|
| Order and duplicates of answers | Answers are sorted and have no duplicates. CS4/CS5 copy a fact one time for each path, not one time for each duplicate. | Accepted: facts are deduplicated downstream. |
| `null` against empty list | Main gives `null` when the local has no element. The new engine gives an empty list. | All consumers treat both the same (checked: CS1-CS8). |
| Builder `Stmt.Return` | It carries the constant of `return "s"` and `return null` (today `null`). | The DSU reads only a `RefValue` there, so its answers do not change. |
| Liveness | The engine computes its own liveness (§5.3). `JIRLocalVariableReachability` filters only the reported bases, as on main. | Required for soundness (`live_spec_unsound`). |
| Catch variable and other fresh values | Main reports a catch variable as `AliasAllocInfo(catch index)`. The new engine reports nothing for a `FRESH` origin. | No consumer reads it: CS7 needs a `JIRNewExpr`, CS8 needs a call expression. |
| Box and class constants | `AliasAllocInfo` for each statement that makes the same constant, not only the statement of the value | CS8 reads the constant argument; it is the same for these statements. |
| Constant heap paths | Main can report a heap path on a `Constant` base. The new engine reports a constant only as an item of the seeds. | Consumers drop `Constant` bases before they apply an alias (`relevantApInfo`); CS8 reads only `Constant` items without accessors. |
| Data classes | No new field in a public data class. The new classes are internal. | No effect on deduplication. |

## 2. Architecture

```
JIRLocalAliasAnalysis (facade, same constructor, mode switch)
 ├─ DSU      → JIRDsuAliasAnalysis      (main's class, renamed, unchanged)
 ├─ DIRECTED → JIRDirectedAliasAnalysis (new)
 └─ SHADOW   → both; answers of the DSU; AliasShadowStats

JIRDirectedAliasAnalysis
  AliasCfg.build(method)        alias CFG: normal edges, exceptional edges, liveness, WTO
  DirectedFixpoint.run(cfg)     WTO iteration over AliasState with Transfer
  DirectedAliasResult           frozen tables, statesBefore[], statesAfter[]
  AliasQuery                    backward search, answer conversion, caches
```

New package: `org.opentaint.dataflow.jvm.ap.ifds.alias.directed` (module `opentaint-jvm-dataflow`). The engine core (tables, state, transfer, fixpoint) does not depend on JIR. A test driver runs it on small programs.

The facade keeps its constructor and its answer types. It does not extend `LocalAliasAnalysis` (D6):

```kotlin
class JIRLocalAliasAnalysis(/* the constructor of main */) {
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    internal fun findHeapAlias(base: AccessPathBase.LocalVar, path: List<AliasAccessor>, statement: CommonInst): List<AliasInfo>?
}
```

`findHeapAlias` exists for the probe tests (DSU: `forEachHeapAlias`; directed: the heap-path query of §S 5.7). `JIRAliasUtil.kt` keeps the facade as receiver. It gets a copy of the one generic loop that it uses from the shared `AliasUtil.kt` (`forEachAliasAtStatementAmongBases`). The two unused wrappers (`forEachAliasAtStatement` for an `InitialFactAp`, `forEachHeapAliasBeforeStatement`) are deleted.

## 3. Data structures

### 3.1 Ids

```kotlin
typealias OriginId = Int
typealias NodeId = Int
typealias CellId = Int
typealias VarId = Int
typealias HeapKey = Long

const val EMPTY_NODE: NodeId = 0
const val ELEM_CELL: CellId = 0
const val ETREE: VarId = 0
const val EVAL: VarId = 1

inline fun heapKey(o: OriginId, c: CellId): HeapKey = (o.toLong() shl 32) or (c.toLong() and 0xFFFF_FFFFL)
```

`CellTable` gives an id to `ELEM_CELL` and to each field (class name, field name, type). `VarTable` gives an id to each pair (local index, context). It reserves `ETREE` and `EVAL`.

### 3.2 Origins

```kotlin
enum class BaseKind { THIS, ARG, STATIC, FRESH, CONST, BOX, NULL, ALLOC_CHILD }

sealed interface OriginKey {
    data class Sym(val base: BaseId, val parent: OriginId, val cell: CellId) : OriginKey  // parent = -1: the base itself
    data class Deep(val base: BaseId) : OriginKey
    data class AllocNew(val site: SiteId) : OriginKey
    data class AllocOld(val site: SiteId) : OriginKey
}
```

| Spec origin | Engine origin | Unique by kind |
|---|---|---|
| `⟨r.q⟩` (this, argument, static holder `C`) | `Sym` with base `THIS`, `ARG(i)` or `STATIC(C)`, path `q` | yes, if `q` has no `ELEM_CELL` |
| `⟨s.q⟩` (call result, unknown expression, catch) | `Sym` with base `FRESH(s)`, path `q` | yes, if `s` is not a loop site and `q` has no `ELEM_CELL` |
| `new(s)`, `old(s)` | `AllocNew(s)`, `AllocOld(s)` | `new(s)`: yes; `old(s)`: no |
| `⟨@s.c.q⟩` | `Sym` with base `ALLOC_CHILD(s, c)`, path `q` | no |
| `null(i)` and its cells | `Sym` with base `NULL(i)`, path `q` | no |
| `const(v)` (string value, `(box type, constant)`, class literal) and `box(s)` (I3) | `Sym` with base `CONST(key)` or `BOX(s)`, path `q` | no |
| `deep(b)` | `Deep(b)` | no |

A `Sym` origin stores its parent and its last cell. So a path is a parent chain of at most K steps, and the prefix test of §S 5.3 walks this chain. A path longer than K gives `Deep(base)`. The origin `Sym(b, [])` of each base is the base value itself: `⟨r⟩`, `⟨s⟩`, `⟨@s.c⟩`, `null(i)`, `const(v)`, `box(s)`.

Sites. `SiteTable` gives an id to each pair (instruction index, context). The null site of a statement is its site. A site is a loop site if its node is on a cycle of the alias CFG (§5.4). For an inlined callee, a site is also a loop site if the call statement is on a cycle of the caller.

Markers. Two extra origins exist only in `Etree` and `Eval`: `REACHED_STATICS` (each static root and each origin below it is reached) and `REACHED_ALL` (the closure budget ran out: no origin is unique).

Default content by rule (`OriginTable.defaultNode(o, c)`, cached for each heap key):

| Origin `o` | Default of cell `c` |
|---|---|
| `Sym(b, q)` with `|q| < K` | `{Sym(b, q.c)}` |
| `Sym(b, q)` with `|q| = K`, `Deep(b)` | `{Deep(b)}` |
| `AllocNew(s)`, `AllocOld(s)` | `{Sym(ALLOC_CHILD(s, c), [])}` |

So a `NULL` base has default children too. A read through a null throws, so no execution observes them.

### 3.3 Node table

```kotlin
class NodeTable {
    fun members(n: NodeId): IntArray          // sorted origin ids
    fun singleton(o: OriginId): NodeId
    fun intern(sorted: IntArray): NodeId
    fun union(a: NodeId, b: NodeId): NodeId   // memo key: (min, max); a == b, a == 0, b == 0 need no memo
    fun subset(a: NodeId, b: NodeId): Boolean
    fun contains(n: NodeId, o: OriginId): Boolean
    fun rename(n: NodeId, from: OriginId, to: OriginId): NodeId   // memoized
    fun freeze()
}
```

Two node ids are equal if and only if their sets are equal (`Tbl.id_inj`). Node 0 is the empty set.

### 3.4 State

```kotlin
class AliasState(
    val env: Int2IntOpenHashMap,     // VarId -> NodeId; absent: unassigned
    val heap: Long2IntOpenHashMap,   // HeapKey -> NodeId; absent: default content by rule
)
```

- `this` and the arguments are not in `env`. JIR does not assign them. Their value is `{Sym(THIS)}` or `{Sym(ARG(i))}` by rule.
- `ETREE` and `EVAL` are `env` keys. Absent means the empty set.
- Normal form: `heap` has no entry equal to its default node, and `env` has no entry for a dead variable or for the empty set. Then two states are equal if and only if their maps are equal (`nf_mapEq_iff`). The comparison is one `Int` comparison for each key.
- Copy on write: a statement that changes a map copies it. A statement that does not change a map shares it.

## 4. Transfer

`val(v)` is `env[v]`, or the root value by rule. `read(o, c)` is `heap[(o, c)]`, or `defaultNode(o, c)`. `put(o, c, n)` removes the key if `n` is the default node, else it writes `n`.

### 4.1 Statements

The engine reads `Stmt` from `InstEvalContext.evalInst` (`JIRDSUAABuilder.kt`), as main does.

| `Stmt` | Operation |
|---|---|
| `Copy(l, r)` | `env[l] := val(r)` |
| `Assign(l, Alloc(new / newarray))` at `s` | `retire(s)`; `env[l] := {AllocNew(s)}` |
| `Assign(l, Alloc(catch))` at `s` | `env[l] := {Sym(FRESH(s))}` (I2) |
| `Assign(l, Alloc(box valueOf))` at `s` | constant argument `v`: `{const(T, v)}`; else `{Sym(BOX(s))}` (I3) |
| `Assign(l, Alloc(other))`, `Assign(l, Unknown)` at `s` | `{Sym(FRESH(s))}` |
| `Assign(l, RefConst(null))` at `s` | `{Sym(NULL(s))}` |
| `Assign(l, RefConst(string v))` | `{const(String, v)}` |
| `Assign(l, RefConst(class C))`, other constant `k` | `{const(Class, C)}`, `{const(type of k, text of k)}` |
| `Assign(l, FieldLoad(Static, f))` | `{Sym(STATIC(C), [f])}`, with `C = f.enclosingClass.name` |
| `Assign(l, FieldLoad(i, f))`, `Assign(l, ArrayLoad(i))` | `env[l] := load(val(i), f)` (or `ELEM_CELL`) |
| `FieldStore(i, f, v)` | `store(val(i), f, value(v))` |
| `ArrayStore(i, v)` | `storeWeak(val(i), ELEM_CELL, value(v))` |
| `WriteStatic` | no change (A5) |
| `Call`, resolved | inline (§5.5) |
| `Call`, unresolved, at `s` | `call(args + receiver)`; `env[l] := {Sym(FRESH(s))}`; then the pass-through models (§4.5) |
| `Return`, `Throw` | no change (a callee `Return` gives the value of the call, §5.5) |

`value(v)` evaluates a stored `Expr` with the `Assign` rules. So `x.f = null` stores `{Sym(NULL(s))}` with the site of the store.

The static key is the binary class name `f.enclosingClass.name`, so two reads of one static field give one origin. `BaseTable` records the type name of `RefValue.Static` at the first static read of each class. The answer uses this name (§1.3).

A primitive value is never stored. A primitive local has no `env` entry.

### 4.2 Load and store

```kotlin
fun load(s: AliasState, base: NodeId, c: CellId): NodeId =
    nodes.members(base).fold(EMPTY_NODE) { acc, o -> nodes.union(acc, read(s, o, c)) }

fun store(s: AliasState, base: NodeId, c: CellId, v: NodeId): AliasState {
    val os = nodes.members(base)
    if (os.size == 1) {
        val o = os[0]
        if (nodes.subset(read(s, o, c), v)) return s.put(o, c, v)    // strong == weak (store_shortcut)
        if (isUnique(s, o)) return s.put(o, c, v)
    }
    return storeWeak(s, base, c, v)
}

fun storeWeak(s: AliasState, base: NodeId, c: CellId, v: NodeId): AliasState =
    nodes.members(base).fold(s) { st, o -> st.put(o, c, nodes.union(read(st, o, c), v)) }

fun isUnique(s: AliasState, o: OriginId): Boolean {
    if (!origins.uniqueByKind(o)) return false
    val etree = nodes.members(s.env[ETREE]); val eval = nodes.members(s.env[EVAL])
    if (REACHED_ALL in etree) return false
    if (REACHED_STATICS in etree && origins.base(o).kind == STATIC && origins.depth(o) > 0) return false
    if (origins.properAncestors(o).any { it in etree }) return false      // at most K binary searches
    return o !in eval
}
```

### 4.3 Retire

`retire(s)` runs before `x = new` at site `s`. It is the rule of §S 5.1.

```kotlin
fun retire(st: AliasState, s: SiteId): AliasState {
    val n = origins.allocNew(s); val o = origins.allocOld(s)
    val cells = writtenCells(st, n) union writtenCells(st, o)       // BOTH origins (retireNaive_ne)
    var r = st
    for (c in cells) r = r.put(o, c, nodes.union(read(st, o, c), read(st, n, c)))
    for (c in writtenCells(st, n)) r = r.remove(n, c)               // new(s) gets its default content
    return r.renameAll(n, o)                                        // every env and heap node, ETREE and EVAL included
}
```

The loop must read the cells of `old(s)` too. If `(old(s), c)` is written and `(new(s), c)` is not, `old(s).c` gets the default `⟨@s.c⟩` of the retired object. A rule over the cells of `new(s)` only is wrong as a state function (`retireNaive_ne`). It gives the same answers only through a global invariant (`oldDflt_analyzeVS`), so the engine does not use it.

`writtenCells` and `renameAll` use two indexes of the state: the written cells grouped by origin, and the holders of `AllocNew(s)` for each loop site. Only loop sites retire. At another site, `new(s)` cannot exist before its statement.

### 4.4 Unresolved call

```kotlin
fun call(st: AliasState, roots: NodeId): AliasState {
    val index = HeapIndex(st)                         // written keys grouped under each ancestor and each base
    val r = OriginSet(nodes.members(roots)) + REACHED_STATICS
    val v = OriginSet()
    val work = ArrayDeque(r)
    while (work.isNotEmpty()) {
        if (r.size > params.maxCallClosure) return st.addSets(REACHED_ALL, REACHED_ALL)
        val a = work.removeFirst()
        for (key in index.keysCoveredBy(a)) {         // each written key one time
            for (x in nodes.members(st.heap[key])) {
                if (origins.canBeUnique(x)) v += x
                if (r.add(x)) work += x
            }
        }
    }
    return st.addSets(etree = r.filter { origins.isSym(it) || it.isMarker }, eval = v)
}
```

- An origin is covered if it is in `R` or below an origin of `R`: a `Sym` descendant, an allocation child of `AllocNew(t)` or `AllocOld(t)`, or `Deep(b)` with a `Sym` origin of base `b` in `R`. `REACHED_STATICS` covers each origin with a `STATIC` base (for example `⟨C.f⟩` after `t = C.f; t.g = z`). `HeapIndex` registers each written key under its origin, under each ancestor of its origin, under its base (for `Deep`), and under `REACHED_STATICS` (for a `STATIC` base). `keysCoveredBy(a)` gives the keys registered under `a` that are not yet visited.
- The closure reads only written cells. An unwritten cell holds its default, and the default is below a covered origin. So the model sets are in the completion of the engine sets, and the strong-update answers are the same (`call_bridge`, `closure_cover_eq`, `uniqueBO_comp`).
- `addSets` does two memoized unions: `env[ETREE] ∪= …`, `env[EVAL] ∪= …`. The call writes no heap entry.
- Cost: at most `3·(|R0| + Σ |content of written cells|) + (K + 2)·|written cells| + 1` steps (`callWork_le`). The model closure costs at least `|universe|`, which grows as `|cells|^K` (`separation`).
- Budget `maxCallClosure`: over it, both sets get `REACHED_ALL`. This is sound, and it blocks all strong updates. A budget of `|R0| + Σ |content|` never runs out (`closeE_some`).

The receiver is an argument. For an unresolved `<init>`, the receiver is the new object.

### 4.5 Pass-through models

A model `from → to` of `ExternalCallModelProvider` is a weak copy after the call (§S 5.6):

| `to` | Rule |
|---|---|
| result, argument or receiver without accessors | `env[v] := env[v] ∪ pts(from)` |
| a base with accessors `a1..ak` | `storeWeak(eval(base.a1..a(k-1)), ak, pts(from))` |

`pts(from)` reads the state before the call, except a `from` on the result. `AnyFieldAccessor` and static positions are skipped, as on main.

### 4.6 Join

```kotlin
fun join(a: AliasState, b: AliasState): Joined   // key in either map; an absent heap key gives its default node
```

The join does one memoized union for each key, `ETREE` and `EVAL` included. It normalizes (`den_joinE`, `NF_joinE`). `changed` is true if some key now holds a node that is not its old node (`joinO_flag`).

## 5. Control flow

### 5.1 Alias CFG

`AliasCfg` has the nodes of `MethodInstGraph` (the same instruction indices as main). It has two edge kinds:

- Normal edges: the successors of `MethodInstGraph`, without the edges into a `JIRCatchInst`.
- Exceptional edges: for each `JIRCatchInst h`, an edge `t → h` for each `t` in `h.throwers` (the raw JIR graph). The production graph cuts most of these edges (`JTryBoundaryExceptionsApplicationGraph`). The alias analysis needs all of them (§S 5.5).

State before a node:

| Node | State before |
|---|---|
| entry | `join(initial state, states after the predecessors)` |
| catch handler `h` | `join` of `statesBefore[t]` and `statesAfter[t]` for each thrower `t` of `h` |
| loop head (WTO) | `join(accumulated head state, inputs)` (§5.2) |
| other | `join` of `statesAfter` of the predecessors |

Then the dead locals of the current context are removed (§5.3). The result is `statesBefore[v]`, and the node evaluates it.

### 5.2 Iteration

The engine iterates in the weak topological order (WTO, Bourdoncle) of the alias CFG, both edge kinds included (§S 5.5).

```kotlin
fun stabilize(component: WtoComponent) {
    if (component.isNode) { evalNode(component.node, inputs(component.node)); return }
    val h = component.head
    var acc: AliasState? = null                       // a new accumulator for each run: the inner loop restarts
    while (true) {
        val joined = join(acc, inputs(h))
        if (acc != null && !joined.changed) break
        acc = joined.state
        evalNode(h, acc)
        component.body.forEach(::stabilize)
    }
}
```

- A head state only grows, and the universe is finite. So each component stops.
- The entry node can be a head (a back edge to the first instruction). Then its inputs include the initial state (`loopEntry_answers`).
- When the iteration stops, the states are a post-fixpoint of the transfer. The last test of each head saw its inputs included, and every other node was evaluated from the final states of its predecessors. So the result is sound for any WTO and for irreducible graphs (`csoundCfg`, §7).
- Time limit and cancellation: `AnalysisCancellation`, as main (10 s, one checkpoint for each evaluated node and for each 1024 steps of a join, a closure or a retire).

### 5.3 Liveness

The engine computes its own live sets on the alias CFG, both edge kinds:

```
live_in(v) = use(v) ∪ ⋃_{w normal successor} (live_in(w) \ def(v)) ∪ ⋃_{h handler of v} live_in(h)
```

An exception happens before the write of `v`. So a handler keeps all its live variables at `v`, also `def(v)`. The rule of `JIRLocalVariableReachability` removes `def(v)` on each edge, and it runs on the cut graph. With that rule, a kill drops a real alias (`live_spec_unsound`: `x = new; y = x; x = m()` with a handler `x.f = y`). With the rule above, the kills keep each alias of the live variables (`kill_sim`, `csoundKill`).

At each node, the engine removes the locals of the current context that are not in `live_in(v)`. It never removes `ETREE` or `EVAL`.

### 5.4 Loop sites

A site is a loop site if its node is on a cycle of the alias CFG (`onceB_spec`, `budget_of`). For a callee site, the call statement must also be on no cycle of the caller. `⟨s⟩` of a loop site is never unique.

### 5.5 Inlining (depth 1)

The resolution is as on main (`JirCallResolver`, `CallTreeNode`). For a resolved call `c` with the overrides `m1..mk`:

1. Each override runs on a new `AliasCfg` of its own body, with new state arrays, from `statesBefore[c]`. Callee locals get the callee context. `NestedCallInstEvalCtx` maps the callee `this` and arguments to the caller values.
2. Normal exit: for each `Return(v)`: `env[l] := value(v)` (a constant or `null` uses the `Assign` rules with the callee site). Then remove all callee variables. `statesAfter[c]` is the join over all returns of all overrides. With no return state, the call is unresolved (§4.4).
3. Exceptional exit: if `c` is a thrower of a caller handler `h`, `h` also gets the join of `statesBefore[t]` and `statesAfter[t]` of each callee node `t`, with the callee variables removed. This is the spliced CFG of the proof: each callee node has an exceptional edge to `h` (`inlined_answer`: a callee writes `this.f = a` and throws; the caller handler sees `x.f ~ a`).
4. An unresolved call inside the callee is a passive call on the shared state. It grows `ETREE` and `EVAL`, and the caller sees the growth.

## 6. Queries and answers

### 6.1 Search

`findAlias(x, stmt)` reads `statesBefore[stmt]`. `findAliasAfterStatement` reads `statesAfter[stmt]`. Both run the backward search of §S 5.7:

1. Seeds: `members(val(x))`.
2. Holders of an origin `o`: the live locals whose node holds `o`; the root variables by rule (`this`, arguments, static holders); the written heap entries whose node holds `o`; the default parent `(p, c)` if `o` is the cell name of `(p, c)` and `(p, c)` is not written (`holders_iff`).
3. Prefix the cell to the path, up to D accessors. Never expand the self cell of a `Deep` origin.

The search gives the paths of the enumeration and no duplicates (`findAlias_iff`, `search_nodup`). A lazy reverse index for each queried state makes step 2 fast.

### 6.2 Conversion

| Item | `AliasInfo` |
|---|---|
| Path from a root-context local, argument or `this` | `AliasApInfo(LocalVar(i) / Argument(i) / This, accessors)`. The base must pass `JIRLocalVariableReachability.isReachable`, as main's `compress`. The path `(x, [])` is not reported. |
| Path from a static holder `C` | `AliasApInfo(ClassStatic, [Static(typeName of C)] + accessors)` |
| `AllocNew(s)` or `AllocOld(s)` in the seeds, root context | `AliasAllocInfo(instIdx(s))` |
| `const(String, v)` in the seeds | `AliasApInfo(Constant("java.lang.String", v), [])` |
| `const(box or class key)` in the seeds | `AliasAllocInfo(i)` for each root-context statement `i` that makes this constant (CS8 reads the constant argument of the box call) |
| `box(s)` in the seeds, root context | `AliasAllocInfo(instIdx(s))` |
| `NULL`, `FRESH` and `ALLOC_CHILD` bases, callee origins | nothing |

The list is sorted with one fixed comparator. A cache keyed by `(stmt, before/after, var)` holds full answers. So the answers do not depend on the query order.

### 6.3 Array elements (I4)

`findArrayElementAliases(x, stmt)` seeds the same search with `load(val(x), ELEM_CELL)`. It reports the paths (without the path `x[*]` itself) and the items of the seeds (§6.2). The vararg branch of `JIRBasicAtomEvaluator.resolveLocalVarValue` calls it in place of `getAllAliasAtStatement` and of the search for the group of `lv[*]`. The DSU backend implements it with the group logic of main, so DSU answers do not change.

### 6.4 Thread safety

The fixpoint is single-threaded. After it, `freeze()` makes the tables read-only. A query that needs a default node that the analysis did not make computes it in a query-local table. The answer cache is a `ConcurrentHashMap`. The reverse indexes are in an `AtomicReferenceArray`.

## 7. Proof obligations

The engine refines the Lean concept in three steps. Each step has a theorem.

```
concept (sets, structured programs)        csoundVS, csoundVSS         sound under A1-A5
  = node interning (O)                     mayProgVSO_eq, csoundVSO
  = engine state (written cells, NF)       den_*, call_bridge, mayProgVS_engine
on CFGs: any post-fixpoint is sound        csoundCfg, csoundEngineCfg
```

| Engine choice | Theorem (`DirectedAlias/...`) | Status |
|---|---|---|
| Concept sound for value aliases (A1-A5) | `csoundVS`, `csoundVSS` (`Sound/ValueSem/`) | proved |
| Node table = sets | `mayProgVSO_eq`, `csoundVSO` (`Opt/ValueSem.lean`) | proved |
| Written cells, default by rule, normal form, map equality = state equality | `den_putH`, `den_joinE`, `den_storeE`, `nf_mapEq_iff`, `mapEqB_iff` (`Impl/EngineState.lean`) | proved |
| Store shortcut `H(o, f) ⊆ pts(y)` | `store_shortcut` | proved |
| Retire over the cells of both origins | `den_retireE`; the naive rule: `retireNaive_ne` | proved |
| Closure over written cells, filters, markers, fallback | `closure_cover_eq`, `call_bridge`, `uniqueBO_comp`, `closeE_some` (`Impl/EngineCall.lean`) | proved |
| Engine = concept on loop-free programs | `mayProgVS_engine` (`Impl/EngineRun.lean`) | proved |
| Closure cost and separation | `callWork_le`, `separation`, `mapEqBW_eq` (`Impl/EngineCost.lean`) | proved |
| Holders by rule (query) | `holders_iff` (`Impl/EngineQuery.lean`); `findAlias_iff` (`Opt/Query.lean`) | proved |
| Any post-fixpoint on a CFG is sound: WTO, irreducible graphs, exceptional edges, inlining as a spliced CFG | `csoundCfg`, `csoundCfg_may`, `csoundCfg_after` (`Impl/CfgSound.lean`) | proved |
| Engine post-fixpoint gives a model post-fixpoint, so the engine result is sound (A1-A6) | `ePostFix_postFix`, `csoundEngineCfg` (`Impl/CfgEngine.lean`) | proved |
| Loop sites on a CFG | `onceB_spec`, `budget_of` | proved |
| Liveness with handlers | `kill_sim`, `csoundKill`; the rule without handlers: `live_spec_unsound` | proved |
| Catch rule `{⟨s⟩}` (I2) | sound for the semantics where a caught exception is unknown (A6: each `throw` becomes an unknown exception): `csoundCfgA6`, `reach_a6`; the loss is exactly the local throw: `catch_gap`, `catch_real` | proved |
| Constants, boxes and never-unique origins (store guard) | `weak_soundVS`, `const_answers`, `guard_answers`, `box_guard`, `box_key` | proved |
| Post-fixpoint checker | `postFixB_sound` (`Impl/CfgCheck.lean`) | proved |

Argued, not proved:

- The JIR mapping: `evalInst` gives the statements of §4.1, and each JIR local is assigned before use (A4, the JVM verifier).
- The WTO iteration stops (the heads only grow on a finite universe), and its result is a post-fixpoint (§5.2).
- A resolved call executes one of its overrides (resolution soundness), so inlining is a spliced CFG.
- The markers: `REACHED_STATICS` stands for the list of all static roots of the model; `REACHED_ALL` for the whole universe.
- The cost model of `HeapIndex` (one lookup for each ancestor) and the one-`Int` comparison of nodes.
- I3: a box of a non-constant value is not a box of another site (G4).

## 8. Modes, parameters and statistics

```kotlin
enum class AliasAnalysisMode { DSU, SHADOW, DIRECTED }

data class Params(
    val useAliasAnalysis: Boolean = true,
    val aliasAnalysisInterProcCallDepth: Int = 0,
    val aliasAnalysisTimeLimit: Duration = 10.seconds,
    val mode: AliasAnalysisMode = AliasAnalysisMode.DSU,
    val symDepth: Int = 7,              // K
    val maxAccessors: Int = 6,          // D
    val maxCallClosure: Int = 10_000,
)
```

- `DSU`: the default. `SHADOW`: both backends run, the consumers get the DSU answers, and `AliasShadowStats` records both answers of each query. `DIRECTED`: the consumers get the directed answers.
- Plumbing: CLI option `--experimental-alias-analysis-mode`, then `CommonAnalysisOptions`, `TaintAnalyzerOptions`, `JIRTaintAnalyzer.analysisParams`, `JIRAnalysisManager.Params`. Tests: the system property `opentaint.test.aliasAnalysisMode`, set by `-PaliasAnalysisMode` in the three `tasks.withType<Test>` blocks.
- `AliasVolumeStats` (both backends): for each query, the number of answers, the sum of the accessors, the longest path; totals for each method and each project.
- `DirectedAliasStats`: statement evaluations, head iterations, node count, table content, call closure sizes, fallbacks, retained map entries, fixpoint time.

The volume of alias answers is the main risk (R0: each answer path becomes taint facts). The order is: shadow runs on thingsboard, Conductor and tms; the user sets the thresholds and decides the volume control (D11); only then `DIRECTED` feeds the taint analysis.

## 9. Test plan

Each step is one PR. Each step starts with its failing tests. Gate commands: `G-JVM`, `G-QL`, `G-ROOT` (as in the design, §10.2), and `G-LEAN` (`cd formal/directed-alias && ./check.sh`).

| Step | Failing tests first | Implementation |
|---|---|---|
| T0 | Characterization probes on main: a loop at the first instruction; a catch after a throwing call; a static write and read in a generic class and in a nested class; vararg constants | none (answers of main) |
| T1 | `vararg element aliases equal the group answer in dsu mode`; `mode directed is accepted by params` | Facade, `JIRDsuAliasAnalysis` (rename), copies of the receiver helpers (D6), `findArrayElementAliases` (DSU), `findHeapAlias` for tests, mode plumbing |
| T2 | `NodeTableTest`, `OriginTableTest`, `AliasStateTest` (normal form, map equality), transfer tests from the Lean examples (§9.1) | Tables, state, load, store with the shortcut, weak store, null, constants, statics, retire (both origins), join |
| T3 | `loop at the first instruction joins the back edge`; `handler gets the state before a throwing call`; `kill keeps a variable that a handler reads`; post-fixpoint check on each test | `AliasCfg`, liveness, WTO iteration, exceptional edges, `PostFixChecker` |
| T4 | Call tests of the spec: §S 5.6 examples, §S 6.7, the losses L1 and L4, `call writes no heap entry`, `closure over budget blocks all strong updates` | Call closure, `HeapIndex`, sets, markers, fallback |
| T5 | Query tests: §S 6.1-6.8, `findAlias of z gives x.f y.f`, `answers do not depend on query order`, `concurrent queries give equal answers`, vararg element constants | `AliasQuery`, conversion, caches, freeze, `findArrayElementAliases` |
| T6 | `callee writes this.f then throws: handler sees x.f ~ a`; `getter aliases this field` and the other inlining samples at depth 1 | Inlining, callee exceptional exit, pass-through models |
| T7 | Probe suite in `DIRECTED` mode (expected sets from the oracle); the changed tests of main (`test swap fields`, `test external call invalidates heap aliases`, design §9.2) | Test changes only |
| T8 | `shadow mode gives the DSU answers`; `shadow mode records both answer sizes` | `SHADOW`, statistics; then the shadow runs |
| T9 | Full suites with `-PaliasAnalysisMode=DIRECTED` | Fixes, each with a failing test; the volume control that the user chooses |
| T10 | — | Default `DIRECTED` (separate PR), when the user accepts the measurements |

### 9.1 Oracles

1. Lean examples. A small `#eval` file (`formal/directed-alias/Export/Vectors.lean`, not imported by the library) prints each example program of the VS and Impl files with its `decide` answer. `LeanVectorTest` runs the engine on each line through a test driver and requires equal answers.
2. Naive concept. `NaiveConcept` is a Kotlin port of `astepVS` with explicit sets and a total heap. A seeded generator makes random CFGs (calls, loops, nulls, handlers). The engine and the naive concept run with the same WTO. Their answers must be equal.
3. Post-fixpoint checker. A port of `postFixB` checks the final states of each test method: entry, node, normal-edge and exceptional-edge conditions, and no written heap entry holds the empty set (A4 makes this true; `EPostFix` needs it). A pass is a soundness certificate for that method (`postFixB_sound`, `csoundEngineCfg`).
4. Concrete fuzz. A port of the instrumented executor (`runAliasV`): random executions of the random CFGs, with callees that write new objects or nulls into reached cells (A2). Each value alias of an execution must be a may-alias of the engine.

## Appendix. Lean files of the implementation

| File | Content |
|---|---|
| `Impl/Cfg.lean` | CFG, instructions, concrete semantics with exceptions and kills, transfer, `PostFix` |
| `Impl/CfgSound.lean` | Loop sites, local steps, `csoundCfg` |
| `Impl/CfgLive.lean` | Liveness with handlers, `kill_sim`, `csoundKill`, `live_spec_unsound` |
| `Impl/CfgCheck.lean` | `postFixB`, `solveCfg` |
| `Impl/CfgExamples.lean` | Loop at the entry, catch, nested loops, inlined callee, constants |
| `Impl/CfgEngine.lean` | `csoundCfgA6`, `csoundEngineCfg` |
| `Impl/EngineState.lean` | Engine state, normal form, operations, retire |
| `Impl/EngineCall.lean` | Closure over written cells, completion, bridge |
| `Impl/EngineRun.lean` | Engine = concept on loop-free programs |
| `Impl/EngineCost.lean` | Closure cost, separation, change test |
| `Impl/EngineQuery.lean` | Holders by rule |
