# Directed alias analysis for the JVM: design proposal

Status: proposal. Base: main `f945f92c5`. The formal model `formal/directed-alias/` (Lean 4, constructive) and the probe suite `DirectedAliasProbeTest` are not committed yet. Step P0 commits the probe suite, and step P0a commits the model and this document (§10.2). The user decided seven of the thirteen decisions on 2026-10-29 (§12).

## Conventions

### Evidence labels

| Label | Meaning |
|---|---|
| proved | A Lean theorem states the claim. The theorem name and the file follow the claim. |
| measured | A test in `DirectedAliasProbeTest` shows the claim on the Kotlin code of main. |
| computed | The Lean model was evaluated with `#eval` on one input. No theorem states the number. The `#eval` lines are not in the library yet. Step P3 adds them to `Export/Computed.lean`. |
| argued | The text gives a reason. No proof and no test exist. |
| open | No proof, no test and no counterexample exist. |
| false | A Lean theorem or a computed counterexample refutes the claim. |
| limited | The claim holds only under a condition that the row gives. |
| checked | The output of the Lean audit script `check.sh`. |

### Path prefixes

| Prefix | Path |
|---|---|
| `LEAN/` | `formal/directed-alias/DirectedAlias/`. Lean file names in this document are relative to it. |
| `JVM/` | `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/` |
| `CORE/` | `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/` |
| `JTEST/` | `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/test/kotlin/org/opentaint/dataflow/jvm/ap/ifds/` |

"Probe row n" is row n of Appendix B. Each probe is a test in `JTEST/alias/DirectedAliasProbeTest.kt`. Its sample is `DirectedAliasSample.java` in the `samples` source set of the same module.

### Terms

This document uses one term for each concept. Prose uses the term in the first column. Lean and Kotlin names occur only in code spans.

| Term | Meaning | Lean | Kotlin |
|---|---|---|---|
| origin | An abstract object. The kinds are the next eight rows. | `Origin` | `OriginId`, `OriginKind` |
| symbolic origin `sym(b, q)` | The entry object (or the result object of an unknown expression or call) at path `q` below base `b`, with `\|q\| ≤ K`. | `sym b q` | `SYM` |
| deep origin `deep(b)` | All objects below base `b` at a depth greater than K. | `deep b` | `DEEP` |
| allocation origin `alloc(s)` | All objects of allocation site `s`. | `alloc s` | `ALLOC` |
| `alloc-new(s)`, `alloc-old(s)` | With recency: the most recent object of site `s`, and all older objects of `s` (§4.2). | `rNew s`, `rOld s` | `ALLOC_NEW`, `ALLOC_OLD` |
| site havoc origin `havoc(s)` | All objects that call site `s` writes, and all objects below them. The Lean concept C uses it (A2-wide). The engine has no such origin (§7.6). | `havoc s` | none |
| per-cell havoc origin `havocC(s, k, c, q)`, `havocDeep(s, k, c)` | The new object that call site `s` writes into cell `c` of a holder with key `k`, and the tree below it. Only the Lean model has it: the per-cell reference (§4.9). The engine has no such origin (§7.6). | `hsym s k c q`, `hdeep s k c` | none |
| allocation child origin `⟨@s.c.q⟩`, `deep(@s.c)` | The object that a callee writes into cell `c` of an object of allocation site `s`, the objects at path `q` (at most K cells) below it, and the objects deeper than K there. Never unique. The call rule makes it (§4.11). | `hsym 0 (rOld s) c q`, `hdeep 0 (rOld s) c` | `SYM`, `DEEP` over an `ALLOC_CHILD` base |
| cell name `name(o, c)` | The origin that names each object that a callee can write into cell `c` of origin `o`: the default child of a symbolic origin, or the allocation child of an allocation origin (§4.11). | `childCN K o c` | `OriginTable.cellName` |
| exposed set `E` | The origins that some unresolved call on some path to this point reached. A symbolic origin below an exposed origin is not unique (§4.11). | `CtxN.xe`, `X.env xe`, `expB` | the reserved key `EXPOSED_VAR` of `env` |
| covered origin, call closure | At a call: an origin of the closure `R`, or an origin below one. `R` starts at the arguments and the static roots and adds the content of each cell of each covered origin (§4.11). | `coveredB`, `callRoots`, `closeN` | `DirectedTransfer.havoc` |
| constant origin | One origin for each box type, class literal or string value (§7.5). | none | `BOX_CONST`, `CLASS_CONST`, `STRING_CONST`, `SITE_CONST` |
| holder | A variable, or a heap cell `(o, c)` of origin `o` and cell `c`. | `Key` (`v x`, `h o c`) | `VarId`, `HeapKey` |
| points-to set `pts(p)` | The origins that the access path `p` may hold. | `aevalPath` | `valueOf`, `load` |
| congruence `≡` | A reflexive, symmetric and transitive relation with `x ≡ y ⇒ x.f ≡ y.f`. The DSU keeps one (§1.7). | `DMay` | DSU partition |
| order `p ⊒ q` | `pts(p) ⊇ pts(q)`: `p` may hold each object that `q` may hold. The edge `p → q` of the task notation. A congruent order: reflexive, transitive, congruent (`p ⊒ q ⇒ p.f ⊒ q.f`), and antisymmetric on nodes (§1.7). | `Above`, `aboveB` | the node DAG of `NodeTable` |
| may-alias, `p ~ q` | `pts(p) ∩ pts(q) ≠ ∅`: one origin is below `p` and `q` in the order. Derived, not stored (§1.7). | `may` | `findAlias` |
| false alias | A may-alias that no execution (or pair of executions) has. | `NoCrossAlias` | — |
| one-execution alias | One execution makes `p` and `q` the same object. | `CAlias` | — |
| cross-execution alias | `p` at the end of one execution and `q` at the end of a second execution are the same object. | `CAliasX` | — |
| exact | Each may-alias is a cross-execution alias (completeness). | `CCompleteIn` | — |
| concept C | The directed points-to semantics, with explicit sets (§4). | `analyze`, `mayProg` | `NaiveConcept` (test oracle) |
| optimization O | C on interned origin-set nodes with a union memo and one map for each state (§5). | `analyzeO`, `mayProgO` | `NodeTable`, `DirectedState`, `DirectedTransfer` |
| directed engine | The Kotlin implementation of O for JIR (§7). | — | `DirectedAliasAnalysis` |
| DSU | Disjoint-set union (union-find). Here: the JVM local alias analysis on main (§2). | `DSU/Model.lean` | `DSUAliasAnalysis` |
| group | A class of the DSU partition. | node | DSU set |
| strong update, weak update | A store that replaces the content of a cell; a store that adds to it. | `setCell`, `weakStore` | `store`, `storeWeak` |
| unique origin | An origin that denotes at most one live object in one state. | `uniqueB`, `uniqueR` | `isUnique` |
| strong-update policy `entryUnique` | `true` (the default, D1): symbolic origins of entry paths and of once-site results are unique. `false`: only allocation origins of once sites (and `alloc-new`) are unique (§3.2). | `Ctx.entryUnique`, `eu` | `DirectedAliasPolicy.entryUnique` |
| entry root | `this`, an argument, or a static root at method entry. | `Base.root r` | `ROOT_THIS`, `ROOT_ARG`, `ROOT_STATIC` |
| unresolved call | A call that the analysis does not inline. | `call s args` | `Stmt.Call` without a resolved callee |
| A2-wide | Concrete call semantics: one call can write one new object into many cells (§3.1). | `Havoc`, `Exec` | — |
| A2-strict | Concrete call semantics: one call writes a distinct new object into each cell that it changes. The callee can reach each symbolic object (§3.1). | `HavocS`, `ExecS` | — |
| A2-narrow | Concrete call semantics: A2-strict, and the callee reaches only the closure of its arguments (receiver included) and of the static roots (§3.1). The assumption of the call rule. | `ReachN`, `HavocN`, `ExecN`, `CAliasN` | — |
| call rule CN | The abstract call rule of the engine: cell-named havoc with narrow reach, sound for A2-narrow (§4.11). It is the only call rule of the engine. The engine has no havoc mode switch (D2). The Lean model also has per-cell havoc origins (sound for A2-strict, the formal reference for the precision comparison, §4.9) and site havoc origins (sound for A2-wide). | `astepCN`; `astepH`, `astepHR`; `astep`, `astepR` | `DirectedTransfer.havoc` |
| exposed key | The reserved environment key that holds the node of the exposed set. Join, change bit, equality and `retire` treat it as each other key (§7.6). | `xe` (`ctxCN`) | `EXPOSED_VAR` |
| origin depth K | The depth limit of symbolic origins. | `Ctx.K` | `symDepth` |
| query depth D | The maximum number of accessors of a reported path. | `findAlias D` | `maxAccessors` (main: `HEAP_CHAIN_LIMIT = 5`, which allows 6 accessors) |
| inlining depth | The number of call levels that the analysis inlines. | none | `aliasAnalysisInterProcCallDepth` |
| heap map | The map of the written cells of a state. | `OState` entries `h o c` | `DirectedState.heap` |
| universe | The finite set of origins, variables and cells of one analysis. | `ctx.origins`, `ctx.vars`, `ctx.cells` | the tables |
| once site, loop site | A site that occurs at most one time and not under a loop; a site on a cycle. | `Prog.onceB` | `SiteTable.isLoopSite` |
| change bit | The result bit of an O join: true if the state grew. | `joinO_flag` | `Joined.changed` |
| exactness certificate | A check on the abstract states that puts a program in the certified store scope (§4.7). | `bcert` | `DirectedAliasStats.exactMethods` |
| flip | The `directed` answer of a probe differs from its `today` answer. | — | — |
| alias answer volume | The number and the length of the alias paths that the queries report, for one query, one method or one project. The taint analysis copies one fact for each reported path (R0). | none | `AliasVolumeStats` |
| shadow mode | Mode `SHADOW`: both engines run, the consumers get the DSU answers, and the statistics compare the two answers of each query (P9a). | none | `AliasAnalysisMode.SHADOW`, `AliasShadowStats` |

Technical verbs: **intern** (find the id of a set in the node table, or add the set); **memoize** (store a result under its inputs); **retire** (rename `alloc-new(s)` to `alloc-old(s)`, §4.2); **havoc** (apply the effect of an unresolved call).

### Identifier families

| Ids | Meaning | Section |
|---|---|---|
| A1-A3 | Scope assumptions | §3.1 |
| CK1-CK13 | Contract items of the alias API | §8.1 |
| CS1-CS8 | JVM consumers of the alias analysis | §8 |
| CX1-CX7 | Counterexamples at the completeness boundary | §4.8 |
| D1-D13 | Decisions for the user | §12 |
| F1-F11 | Lean follow-ups | §11.4 |
| G-JVM, G-CORE, G-QL, G-ROOT, G-LEAN | Test gates | §10.2 |
| L0-L4 | Test layers | §10.1 |
| M1-M8 | Consumer changes | §8.2 |
| P0-P13 | Implementation steps (one pull request each), with P0a, P0c and P9a | §10.2 |
| PL1-PL7, U1-U4, LT1 | DSU defects: precision losses, unsound defects (U1 has shapes U1.a1-U1.a4), one latent defect | §2.3 |
| PS1-PS13 | Probe scenarios | §2.2, Appendix B |
| R0-R16 | Risks | §11.1 |

### Abbreviations and projects

| Abbreviation | Meaning |
|---|---|
| A/B | A comparison of two builds on the same input. |
| CEGAR | Counterexample-guided abstraction refinement. |
| CFG | Control-flow graph. |
| DAG | Directed acyclic graph. |
| HAMT | Hash array mapped trie, a persistent map structure. |
| IFDS | Interprocedural finite distributive subset problems: the framework of the taint analysis. |
| IR | Intermediate representation. The Lean IR is in `Syntax.lean`. |
| JIR | The JVM IR of the analyzer (`core/opentaint-ir`). |
| PR | Pull request. |
| SARIF | The output format of the analyzer findings. |
| TDD | Test-driven development: each change starts with a test that fails. |
| WTO | Weak topological order of a CFG (Bourdoncle). |
| fastutil | A Java library of collections for primitive types. |
| tms | A Java project of the end-to-end suite (`opentaint-test/opentaint-test-tms`, a checkout next to this repository). One scan takes about 37 s. It is the standard check for changed findings. |
| Conductor | Netflix Conductor, a large Java workflow engine in the end-to-end suite (`opentaint-test/opentaint-test-conductor`). Its scan is memory bound at 8 GB. |
| thingsboard | ThingsBoard, a large Java IoT platform in the end-to-end suite (`opentaint-test/opentaint-test-thingsboard`). Its scan is memory bound at 8 GB. With a fix of the DSU defects of main, the number of taint facts explodes and the scan runs out of memory fast (user report, R0). So it is the first project of each volume measurement. |
| dataflowbench | `BrokkAi/dataflowbench`, a public data-flow benchmark with an OpenTaint adapter. It has 58 Java and 58 Kotlin assertions. |

---

## 0. Summary

**Problem.** Today, the JVM local alias analysis is a disjoint-set union (DSU). It keeps a congruence (symmetric, transitive, `x ≡ y ⇒ x.f ≡ y.f`), so it loses the direction of `a = x`: it merges `a` and `x`, and transitivity then merges `x` and `y` (§1). The analysis needs a congruent order `⊒`. `a ⊒ x` means "`a` may hold each object that `x` may hold". May-alias is derived from the order and is not transitive (§1.7).

**Design.**

1. Concept C: points-to sets keyed by origin. The order is set inclusion; may-alias is set intersection (§4).
2. Optimization O: hash-consed origin-set nodes with a union memo (§5).
3. Queries: a backward search over a lazy reverse index (§6).
4. CEGAR steps (§1.8): recency for loop allocation sites (step 1); per-cell havoc origins for unresolved calls (step 2, now only the formal reference in the Lean model, §4.9); cell-named havoc with narrow reach, the call rule CN (step 4, decided by the user 2026-10-29, §4.11). CN creates no origin at a call. It names each unknown object by its cell and keeps an `exposed` set that removes uniqueness below a reached object. CN is the only call rule of the engine. The user dropped the havoc modes `SHARED` and `PER_CELL` from the engine (D2).
5. The mode switch `aliasAnalysisMode = DSU | SHADOW | DIRECTED`, default `DSU` (D7). In `SHADOW`, the taint analysis gets the DSU answers, and statistics compare both answers (§10.2).

**Results.**

| Area | Result | Status |
|---|---|---|
| Order | The stored relation is a congruent order; may-alias is derived (§1.5, §1.7). | proved |
| Soundness | Each one-execution alias is a may-alias under A1-A3. The call rule CN under A2-narrow: `csoundCN` (both policies, recency, each K, each list of static roots) (§4.11). The references: site havoc under A2-wide, per-cell havoc under A2-strict (§4.5, §4.9). | proved |
| Completeness | Exact in two scopes without loops and calls, with computable witnesses (§4.7). | proved |
| DSU defects | U1-U4 (unsound), LT1 (latent), PL1-PL7 (precision) (§2.3). | proved, measured |
| O ≡ C | Equal answers for each combination of recency and call rule, CN included (`mayProgCNO_eq`, `csoundCNO`) (§5.5). | proved |
| Cost | O is linear where C is a product or exponential on three families (§5.6, §5.8). | proved; argued |
| Audit | No `Classical`, no `sorryAx`, no `ofReduceBool` (Appendix A). | checked |

**Limits.**

1. Alias answer volume (R0). The taint analysis copies one fact for each reported alias path. On main, the call drop and the cache truncation limit this volume by accident. A fix of either explodes the fact count, and thingsboard runs out of memory fast (user report). The directed engine removes both limits; its non-transitive answers are smaller. The net volume is unknown and is the first gate (§11.2, D11).
2. Entry aliasing: A1 is an accepted precondition, and strong updates on entry roots can lose aliases (D1, §3.3).
3. Loops and calls are in no completeness scope (§4.8). The call rule is proved sound only under A2-narrow; with generous reach or with one object in two cells it misses aliases (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`, §3.1, §4.11).
4. The node table can hold Θ(m²) set elements on a join chain (§5.7).
5. CN has three accepted precision losses (the user accepted them, D2): a weak store below an exposed origin, a false alias with the entry content of a cell, and a false alias between the objects of two calls in one cell (`losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`, §4.11). CN and per-cell havoc are incomparable in precision (`precision_order_fails`). No cost theorem exists for the O call of CN (F10).

**Decisions** (§12):

| Status | Decisions |
|---|---|
| Decided by the user (2026-10-29) | D1 (`entryUnique = true`), D2 (no alias drop at unresolved calls; the call rule CN), D5 (must-alias postponed), D6 (copy the helpers), D7 (mode switch), D12 (inlining depth 1 stays), D13 (the DSU of main stays unchanged). |
| Open until the spec revisit | D3 (recency), D4 (depths K, D), D8 (state container), D9 (unknown-origin signal), D10 (`cantMutateAliasedHeap()`), D11 (volume control). |

---

## 1. Problem and goal

### 1.1 Task example

```java
if (c) a = x; else a = y;
```

| Query | Executions | DSU on main | Wanted |
|---|---|---|---|
| `alias(x)` | `a == x` in the left run | `{a, y}` | `{a}` |
| `alias(y)` | `a == y` in the right run | `{a, x}` | `{a}` |
| `alias(a)` | both | `{x, y}` | `{x, y}` |

Notation. The task writes `alias(x) = {x, a}`. The API answer `alias(x)` does not contain the queried path itself (contract item CK4, §8.1). So this document writes `{a}`. The Lean function `findAlias` keeps the queried path. This document gives each Lean result in the API form.

No execution makes `x == y` (proved: `join_x_y_none`, Examples.lean). The DSU says `x ~ y` (proved: `dsu_join_x_y`, DSU/Examples.lean; measured: probe rows 1 and 2).

### 1.2 Directed graph view

Concept C keeps a directed graph. An edge goes from a holder to each origin that the holder may hold. A copy `a = x` adds the edges of `x` to `a`. In the notation of the task, `a -> x` means `pts(a) ⊇ pts(x)` after the copy. This is the order `a ⊒ x` of §1.7.

Task example, after the join:

```
  holders           origins
    x  ───────────►  ox
    a  ──┬────────►  ox
         └────────►  oy
    y  ───────────►  oy
```

`pts(x) ∩ pts(a) = {ox}`: alias. `pts(a) ∩ pts(y) = {oy}`: alias. `pts(x) ∩ pts(y) = ∅`: no alias. The may-alias relation is symmetric and not transitive. The order `⊒` under it is transitive (§1.7).

### 1.3 Field example

```java
if (c) a = x; else a = y;
a.f = z;
a = w;
```

`a` has two origins at `a.f = z`. So the store is a weak update of `(ox, f)` and of `(oy, f)`.

Concept C, after `a.f = z`. The second edge of each cell goes to the entry content of the cell:

```
  holders             origins
    x  ─────────────►  ox
    y  ─────────────►  oy
    a  ──┬──────────►  ox
         └──────────►  oy
    z  ─────────────►  oz
  (ox,f) ──┬────────►  oz
           └────────►  ox.f
  (oy,f) ──┬────────►  oz
           └────────►  oy.f
```

Concept C, after `a = w`. Only the edge of `a` changes. The cells keep their edges, because origins key the cells, not variables:

```
  holders             origins
    x  ─────────────►  ox
    y  ─────────────►  oy
    a  ─────────────►  ow
    z  ─────────────►  oz
  (ox,f) ──┬────────►  oz
           └────────►  ox.f
  (oy,f) ──┬────────►  oz
           └────────►  oy.f
```

| Query after `a = w` | `pts` | C answer | Theorem (Examples.lean) |
|---|---|---|---|
| `x.f ~ z` | `{oz, ox.f} ∩ {oz}` | yes | `field_xf_z`, `field_xf_z_witness` |
| `y.f ~ z` | `{oz, oy.f} ∩ {oz}` | yes | `field_yf_z`, `field_yf_z_witness` |
| `x.f ~ y.f` | `{oz, ox.f} ∩ {oz, oy.f}` | yes | `field_xf_yf` |
| `x ~ y` | `{ox} ∩ {oy}` | no | `field_x_y` |
| `a ~ x` | `{ow} ∩ {ox}` | no | `field_a_x` |
| `a ~ w` | `{ow} ∩ {ow}` | yes | `field_a_w` |

`x.f ~ y.f` is a cross-execution alias: `x.f == z` in the left run and `y.f == z` in the right run. No single execution makes `x.f == y.f`. §4.6 shows why this is the correct target.

### 1.4 The DSU view of the same program

A DSU state is a set of groups. A heap element `HeapAlias(G, f)` is a member of a group. Its key is the group `G` of the instance. So the heap cell belongs to a **group**, not to an object.

```
  after a.f = z:   G1 = { x, y, a, ox-elem, oy-elem }
                   G2 = { z, oz-elem, HeapAlias(G1, f) }
  after a = w:     G1 = { x, y, ox-elem, oy-elem }
                   G2 = { z, oz-elem, HeapAlias(G1, f) }
                   G3 = { a, w, ow-elem }
```

The DSU cannot split `x` and `y`, for three reasons:

1. The join is a union of the parent relations of both branches. After it, the state has no record of which branch contributed which member. Removal of `a` cannot undo the union of `x` and `y`.
2. The heap element `HeapAlias(G1, f)` has the group of `x` as its key. A split of `G1` into `{x}` and `{y}` needs two heap elements in the group of `z`. A partition holds one element for each group and accessor.
3. A partition is transitive. §1.5 shows that each sound transitive relation relates `x` and `y`.

Measured: probe rows 3 and 4. Proved: `field_precision_loss` (DSU/Examples.lean).

### 1.5 Why a partition cannot answer the query

| Claim | Status | Theorem (file) |
|---|---|---|
| `x ~ a` and `a ~ y` are one-execution aliases. `x ~ y` is no cross-execution alias. | proved | `alias_not_transitive` (Sound/Facts.lean) |
| Each transitive relation that contains all one-execution aliases of the task example relates `x` and `y`. C answers no. | proved | `transitive_sound_relates_x_y` (Sound/Facts.lean) |
| Each sound partition of the variables puts `x` and `y` in one class. | proved | `partition_sound_merges_x_y` (Sound/Facts.lean) |
| The DSU answer is symmetric, transitive and a congruence. It is reflexive on each variable that has a group. | proved | `DMay.refl`, `DMay.symm`, `DMay.trans`, `DMay.ext` (DSU/Props.lean) |
| No DSU state and no program give `x ~ a`, `a ~ y` and not `x ~ y`. | proved | `dsu_never_directed`, `dsuMay_never_directed` (DSU/Props.lean) |

Consequence: a better DSU cannot fix the task example. The may-alias relation must not be transitive. The stored relation stays transitive and congruent, but it is an order, not a congruence (§1.7).

### 1.6 Goal

| Goal | Measure |
|---|---|
| Precision | Non-transitive may-alias, derived from a transitive congruent order (§1.7). Exact across executions in the largest checkable scope. |
| Soundness | Sound under A1-A3 (§3) for each program of the IR. |
| Efficiency | Join and fixpoint test by node ids. Query cost bounded by output size times depth. State size relative to the DSU: measured in L4 (§5.8, §11.2). |
| Separation | Concept C and optimization O are separate. O is proved equal to C. |

### 1.7 The relation the analysis keeps

Today, the DSU keeps a congruence `≡`. The analysis needs a congruent order `⊒`. Both relations are transitive and congruent. The difference is symmetry against antisymmetry.

| Property | DSU: congruence `≡` | Needed: congruent order `⊒` | Lean theorem |
|---|---|---|---|
| Reflexive | `x ≡ x`, for each variable that has a group | `p ⊒ p` | `DMay.refl` (DSU/Props.lean); `above_refl` |
| Symmetric | `x ≡ y ⇒ y ≡ x` | no: `a ⊒ x`, but not `x ⊒ a` | `DMay.symm`; `join_order` |
| Antisymmetric | no: a symmetric relation that is antisymmetric is equality | on O nodes: `u ⊒ v` and `v ⊒ u` ⇒ `u = v` | `symm_antisymm_eq`; `node_antisymm` |
| Transitive | yes | yes | `DMay.trans`; `above_trans` |
| Congruent | `x ≡ y ⇒ x.f ≡ y.f` | monotone: `a ⊒ x ⇒ a.f ⊒ x.f`, for each path | `DMay.ext`; `aread_mono`, `aevalFrom_mono`, `path_mono` |
| Store `a.f = z` | a union of groups | writes down the order: each `x ⊑ a` reads `z` at `f` | `store_down`, `weak_cell`, `strong_cell` |
| May-alias | the relation itself; transitive | derived: one origin below both paths; symmetric, not transitive | `dsu_never_directed`; `may_iff_common_lower`, `may_of_above`, `may_symm`, `may_not_transitive` |

The new theorems of this table are in `Order.lean` (namespace `DirectedAlias.Order`). The other theorems are in the files of §1.5 and §4.4.

Definition. In concept C, `p ⊒ q` if `pts(p) ⊇ pts(q)`: "`p` may hold each object that `q` may hold" (Lean `Above`; `aboveB` decides it, `aboveB_iff`). The edge `a → x` of the task notation is `a ⊒ x`. `x ⊑ a` is the same fact. Concept C realizes the order as inclusion of points-to sets.

Antisymmetry. On variables and paths, `⊒` is a preorder: two variables can hold the same set and stay two variables. O interns each set as one canonical node (§5.2). On nodes, `⊒` is antisymmetric: two nodes that are above each other are one node (`node_antisymm`, from `Tbl.id_inj`). So variables with the same node hold the same set.

Writes go down the order. A store through `a` writes the cell of each origin of `pts(a)`. Each `x ⊑ a` that holds an origin then reads at least the stored value in that cell. This holds for a strong store and for a weak store (`store_down`). In the field example: after `a.f = z`, `x.f` and `y.f` both alias `z`.

May-alias is derived, not stored. `p ~ q` if one origin `o` is below both paths: `p ⊒ {o}` and `q ⊒ {o}` (`may_iff_common_lower`). If `p ⊒ q` and `q` holds an origin, then `p ~ q` (`may_of_above`). The stored order is transitive and congruent. The derived may-alias is symmetric (`may_symm`) and not transitive (`may_not_transitive`): `x ⊑ a ⊒ y` gives `x ~ a` and `a ~ y`, but `x` and `y` have no common lower origin.

The order is a relation of one state. A copy or a strong store can remove a pair from it: after `a = w`, `a` is not above `x` (`field_order`).

Why the DSU cannot keep it. The DSU relation is symmetric. A symmetric relation that is also antisymmetric relates only equal elements (`symm_antisymm_eq`). So the DSU can record `a ⊒ x` only as `a ≡ x`: it merges `a` and `x`. In the task example, transitivity then merges `x` and `y` (`partition_sound_merges_x_y`, `transitive_sound_relates_x_y`, §1.5).

Examples (Order.lean, on the programs of Examples.lean):

| Example | State | Order facts | Theorem |
|---|---|---|---|
| Task | after `if (c) a = x; else a = y;` | `a ⊒ x` and `a ⊒ y`. `x` and `y` are not ordered. `x` is not above `a`. | `join_order` |
| Field | after the join, `a.f = z; a = w` | `x.f ⊒ z` and `y.f ⊒ z`. `a` is above neither `x` nor `y`. `x` and `y` are not ordered. | `field_order` |

O keeps the order as a DAG of nodes (§5.1). A union node keeps its two children, so each DAG edge is a pair of the order.

### 1.8 Method

The work used this order. Each phase has a gate.

| Phase | Work | Gate |
|---|---|---|
| 1 | Model the DSU in Lean. Prove its invariants. Match the model to the measured Kotlin answers (§2). | `G-LEAN`; probe suite green on main |
| 2 | Model concept C and optimization O. Prove soundness, completeness in a scope, and O ≡ C (§4, §5). | `G-LEAN` |
| 3 | Use the model to find design bugs, in the DSU (§2.3) and in the new design (table below). Refine with CEGAR (table below). | a theorem or a computed counterexample for each bug |
| 4 | Implement with TDD (§10). Each step starts with its failing test. | the gates of §10.2 |

CEGAR log. Each row is one refinement step.

| Step | Counterexample | Cause | Change | Scope after the step | Evidence after the step |
|---|---|---|---|---|---|
| 1. Recency | CX7: `loop { b = new; b.f = x; b.f = y }`, query `b.f ~ x` (`loop_bf_x`, `loop_none`). Here the DSU is more precise than C (`loop_dsu_more_precise`). | A loop site has one origin, so its stores are weak. | Two origins for each site: `alloc-new(s)` and `alloc-old(s)` (§4.2). | The same concrete semantics. A true refinement. | `csoundR`, `mayProgRO_eq`, `loop_bf_x_exact` |
| 2. Per-cell havoc | `pHv = m(x); a = x.f; b = y.g`, query `a ~ b` (§4.9). | One site havoc origin for each call. Under A2-wide the alias is real. | First, narrow the call semantics from A2-wide to A2-strict. The soundness claim then covers fewer callees. Second, refine the abstraction: per-cell havoc origins. Site havoc stays in the Lean model for A2-wide. Since step 4, per-cell havoc is the precise reference of the Lean model only. The engine does not implement it. | A2-strict (§3.1) | `csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `strict_answers`, `strict_ab_none`, `generous_breaks_strict` (§4.9) |
| 3. Store certificate | CX4-CX6: correlated control and correlated values break "a strong store is exact" (§4.8). CX3: null blocking. | A per-variable domain has no correlation. | Completeness scopes with checks: the null-kind check (`nullSafeB`) and the certificate `bcert` (§4.7). | Completeness only; soundness does not change. | `ccomplete_coreB`, `ccomplete_store` |
| 4. Cell-named havoc with narrow reach (CN) | A cost problem, then a counterexample. Cost (user, 2026-10-29): per-cell havoc adds `havocC(s, key(o), c, [])` to each cell of each reachable origin at each call, and each symbolic object is reachable. So each call writes almost the whole heap map, and the values grow with the number of calls. Counterexample to the cheap "dead-end" rule (an unknown object gets no origin): `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, query `b ~ d`. The alias is real (`dead_realN`). | Per-cell havoc makes one origin for each call, holder and cell. The dead-end rule drops the object that the callee writes into `n.f`, so `b` and `d` share no origin. | First, narrow the concrete call semantics from A2-strict to A2-narrow: the callee reaches only the closure of its arguments and of the static roots. Second, refine the abstraction: name each unknown object by its cell (`name(o, c)`), keep the set `exposed` of the reached origins, and make each symbolic origin below an exposed origin not unique. No call creates an origin. The user rejected a lazy havoc log (it complicates state identity and the join) and accepted CN with its three precision losses (D2). | A2-narrow (§3.1) | `csoundCN`, `mayProgCNO_eq`, `csoundCNO`, `dead_answerCN`, `need_answersCN`, `spread_goneCN`, `gain_answersCN`; the losses `losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`; the scope `generous_reach_breaks_CN`, `generous_havoc_breaks_CN` (§4.11) |

Design bugs of the new design. The Lean model, a hand evaluation of its definitions, or a review of the design against the model found each bug before the implementation.

| First design | Counterexample | Change | Section |
|---|---|---|---|
| The fixpoint test is "state equal to the old state". | The transfer is not monotone (`astep`: a store with `pts(x) = ∅` against `{o}`). A copy-on-write add and remove gives a new object with equal content. | The change bit of the join is the signal (`joinO_flag`). | §7.10 |
| One site havoc origin for each call. | `pHv`: a value loaded after a call may-aliases each outer path. | Per-cell havoc origins under A2-strict. | §4.9 |
| Per-cell havoc origins at each call, with each symbolic object reachable. | Cost: each call writes almost the whole heap map, and the values grow with the number of calls (user, 2026-10-29). | The call rule CN under A2-narrow. | §4.11 |
| An unknown object gets no origin ("dead end"): the call keeps the old content and adds nothing. | `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`: `b ~ d` is real (`dead_realN`). CN answers true (`dead_answerCN`). | The cell name: the object in `n.f` is `⟨@s.f⟩`. | §4.11 |
| The hypothesis "CN is at least as precise as per-cell havoc". | `precision_order_fails`: on `pNest` per-cell havoc answers true and CN answers false, and no execution has the alias (`nest_noneN`). The three losses go the other way. | The two rules are incomparable. The Lean examples give the losses and the nesting gain. The engine implements only CN. | §4.11 |
| `entryUnique = true` is sound. | Entry aliasing: `skip_unsound`, `write_read_unsound`, `swap_strong`. | Document A1 as a precondition of the intra-procedural analysis. The user keeps the default `entryUnique = true` and accepts the loss (D1). | §3.3 |
| "Each strong store is exact." | CX4, CX5 (`corr_none`, `strongTwo_none`); null blocking CX3 (`block_none`). | Certified store scope with null kinds. | §4.7, §4.8 |
| K = D. | `deep(b)` holds itself in each cell. After a long list walk the query output is `\|cells\|^D`. | K ≥ D + 1, and the search never expands a self edge of a deep origin. | §6.2, §6.4 |
| A flat CFG worklist with accumulating loop heads. | Nested loops with strong stores: the inner head keeps stale entry states. | Recursive WTO iteration; new state arrays for each callee evaluation. | §7.10 |
| Keep the `cantMutateAliasedHeap()` exemption. | A constructor call with no reference argument does not havoc its receiver. Two loads of one field of the new object then do not alias. | An unresolved `<init>` always havocs its receiver. | §7.6 |
| The catch state is the state after the thrower. | A throwing instruction does not do its effect. | Catch edges use the join of the states before and after the thrower. | §7.10 |
| The catch variable is an allocation with null cells. | Fields of a caught exception read as null. | The catch variable gets a fresh symbolic origin. | §7.5 |

---

## 2. The DSU on main

Status (D13, decided by the user). This section documents the defects of the DSU. The design does not fix them on main. The DSU of main stays as it is, and it is the A/B baseline. The user: "The issues are known, but we don't land the fix. The problem is the analyzer itself: after any of the fixes the AA starts producing way more alias chains, resulting in analysis explosion." So the call drop (U2) and the cache truncation (§8.5) also limit the alias answer volume by accident (R0, §11.1).

### 2.1 Model

The Lean model `DSU/Model.lean` is a graph model of `DSUAliasAnalysis`, `State` and `IntDisjointSets`. It is executable. Its concrete checks use `decide`, or `decide +kernel` for large terms.

| DSU concept | Model |
|---|---|
| Non-heap element (`Local`, `Arg`, `This`, `Static`, `Alloc`, `CallReturn`, `Unknown`) | atom |
| Group | node |
| `HeapAlias(G, acc)` in group `T` | edge `(G, acc) ↦ T`. Edges are functional (the congruence invariant). |
| Join (`State.merge`) | disjoint union, then `normalize` (resolve atom and edge conflicts by union) |
| `x = y` | remove `x`, union `x` with `y` |
| `x = y.f` | remove `x`, union `x` with `HeapAlias(group(y), f)`. The root choice is as in Kotlin (`isRepr`). |
| `x.f = v` | strong if not `containsMultipleConcreteOrOuterLocations(x)` (model: `multi`), then union |
| `x[i] = v` | always weak |
| Unresolved call | `lValue := CallReturn`, then `invalidateOuterHeapAliases` (this **removes** heap elements) |
| `Stmt.WriteStatic` | no change of state |
| Query | a split `px = p1 ++ s`, `py = q1 ++ s` with the same group for `x.p1` and `y.q1` (`dsuMayD_iff`) |

Invariants of the model (DSU/Lemmas.lean, DSU/Props.lean):

| Invariant | Theorem |
|---|---|
| `normalize` only renames groups, and its result has no atom conflict. | `normalize_spec` |
| A union puts the atoms of both groups into one group and keeps the old co-membership. | `unite_spec` |
| The join keeps the co-membership of both inputs on the universe. | `joinD_spec` |
| The loop result is a fixpoint: the join of the entry and the body result. | `loopD_spec` |
| The answer is a congruence: equal groups give equal groups after one more accessor. | `DMay.ext` |

The model gives the measured Kotlin answers on 11 probe scenarios: `s7_matches`, `s8_matches`, `s9_matches`, `s11_matches`, `s31_matches`, `s33_matches`, `s34_matches`, `s4copied_matches` (DSU/Probes.lean), and PS1, PS2, PS10 (`dsu_join_x_y`, `dsu_field_xf_z`, `static_unsound`, DSU/Examples.lean). The Lean names use the old scenario numbers: `s31` is PS3.1.

Abstractions of the model (each keeps the measured answers):

| Item | Model choice | Effect |
|---|---|---|
| Union-find | Partition with canonical node ids. Path compression and rank do not change the partition. | The root choice matters only in a load into the root (U4). The model includes it. |
| Dead locals | All locals are live. | Locals do not count in the guard and in the removal start. The probe matches confirm the answers. |
| Call arguments | All IR arguments count. Kotlin uses `stmt.args` without the receiver, and skips the removal for some static calls. | Kotlin keeps more heap aliases (sound direction). |
| Final fields | The IR has no `final`. | All model fields are mutable. |

Parts of the DSU that the model does not include:

| Part | Modelled | Reason | Risk |
|---|---|---|---|
| `simulateGraph` (worklist and change test) | no | The model uses structured loops. | §7.10 found two defects of this kind by hand. |
| Alias conversion and its cache | no | Outside the analysis. | The cache defect (§8.5) was found by code review. |
| Inlining of callees | no | Out of the IR (§3.4). | Argued only. |
| External pass-through models (`ExternalAssign`) | no | Models are not in the IR. | PL6 is measured, not proved. |
| Dead-variable removal | no | All locals are live in the model. | The probe matches cover the shapes. |

### 2.2 Measured behaviour

The probe suite `DirectedAliasProbeTest` has 42 tests in 13 scenarios. All pass on main `f945f92c5`. The name of each test starts with `today`. Each test asserts the answer of the DSU on main. The existing `AliasSampleTest` (32 tests) passes. A runtime Java witness program runs each unsound case and prints the concrete alias that the DSU loses. Step P0 commits this program with the probes. Appendix B lists all probes.

Probe scenarios:

| Scenario | Shape | Defect |
|---|---|---|
| PS1 | join of two values | PL1 |
| PS2 | field write through a join | PL2 |
| PS3.1-PS3.4 | strong-update guard | U1 (U1.a2, U1.a4, U1.a3, U1.a1) |
| PS3.5 | predecessors that block the loop strong update | none |
| PS4 | unresolved call after a load | U2 |
| PS5 | pass-through models | PL6 |
| PS6 | correlated branches | none (§4.6) |
| PS7 | loop reassignment | PL3 |
| PS8 | heap chain load; load through a join | PL4 |
| PS9 | store through a join | none |
| PS10 | static field write | U3 |
| PS11 | `this` field writes | PL5 |
| PS12 | self copy (scan of JIR) | LT1 |
| PS13.1-PS13.4 | load into the root of the instance group, list walks | U4 (PS13.1), PL7 (PS13.2, PS13.4), none (PS13.3) |

### 2.3 Defects found

Verdict: PL = precision loss (sound). U = unsound. LT = latent (unsound in the model, but javac and JIR do not produce the shape).

| Id | Java shape | Probe rows | Lean theorem (file) | Verdict |
|---|---|---|---|---|
| PL1 | `if (c) a = x; else a = y;` then `x ~ y` | 1, 2 | `join_precision_loss` (DSU/Examples.lean) | PL |
| PL2 | field example: `x ~ y` after `a = w` | 3, 4 | `field_precision_loss` (DSU/Examples.lean) | PL |
| PL3 | `cur = a; while (..) cur = b;` then `a ~ b` | 8 | `s7_matches` (DSU/Probes.lean) | PL |
| PL4 | `a = c ? p : q; t = a.value;` then `p.value ~ q.value` | 10 | `s8_matches` (DSU/Probes.lean) | PL |
| PL5 | `this.value = v1; this.value = v2;` in a method is weak | 30 | `s11_matches` (DSU/Probes.lean), `root_concept_more_precise` (DSU/Examples.lean, policy `entryUnique = true`) | PL |
| PL6 | two pass-through models into one result: `x ~ y` | 11 | none (models are not in the IR) | PL, measured |
| PL7 | conditional load into the root; linked-list walk | 37, 41, 42 | none | PL, measured |
| U1 | strong-update guard, 4 shapes (§2.4) | 13-16 | `a1_unsound`, `a2_unsound`, `a3_unsound`, `a4_unsound` (DSU/Examples.lean) | U |
| U2 | `w = x.f; touch(x);` then no `w ~ x.f` | 21, 22, 24, 25, 27 | `b_unsound`, `b_local_unsound` (DSU/Examples.lean) | U |
| U3 | `F = v; t = F;` then no `t ~ v` | 28 | `static_unsound` (DSU/Examples.lean) | U |
| U4 | `x = p; w = p.next; x = x.next;` then no `x ~ w`. The probe uses `w = p.next; x = p; x = p.next`. Both load through the root of the group of `p`. | 35, 36 | `repr_unsound`, `repr_self_loop`, `repr_partition_ok` (DSU/Examples.lean) | U |
| LT1 | `z = x; x = x;` then no `x ~ z` | 31-34 (0 self copies in 5914 methods) | `self_copy_unsound` (DSU/Examples.lean) | LT |

Notes:

- U2 depends on the IR shape (measured). If the code uses an argument directly (`arg$0`), an unrelated call keeps its heap aliases. If the code first copies the argument to a local, the call removes them (row 24). One program meaning gives two answers. U2 also removes final fields of arguments (row 25).
- U4 needs a dead copy right before the load. JIR keeps the left side alive at its own statement. So `x` is still the root of the group of `p`. `evalHeapLoad` computes the instance before it removes `x`. With pure partition semantics the DSU is sound here (`repr_partition_ok`). The root choice is the cause.
- Main also has a query-order defect outside the analysis: the conversion cache key has no depth, so heap chains can be cut (§8.5). It is not fixed (D13). Step P0c counts the cut conversions (§10.2).

### 2.4 The strong-update guard (U1)

The guard counts concrete **elements** of a group. It does not count **objects**. It is unsound when a group holds two live objects and at most one concrete element. Such a group needs an object without a concrete element in the group.

| Shape | Loop | Source of the object without an element | Probe row | Theorem (DSU/) |
|---|---|---|---|---|
| U1.a1: join of a removed load and an allocation | no | a load whose heap element a call removed | 16 | `a1_unsound`, `s34_matches` |
| U1.a2: summary site after a removed load | yes | the same, then one `Alloc` element for many objects | 13 | `a2_unsound`, `s31_matches` |
| U1.a3: constructor `this` joined with an allocation | no | `this` in `<init>` is not outer (`This(isOuter = !isConstructor)`) | 15 | `a3_unsound`, `s33_matches` |
| U1.a4: loop in a constructor | yes | constructor `this`, then a summary site | 14 | `a4_unsound` |

Shapes that block the strong update (sound on main):

| Value before the loop | Probe row | Theorem (DSU/Examples.lean) |
|---|---|---|
| `new` | 17 | `a2new_blocked` |
| `null` | 18 | `a2null_blocked` |
| argument | 19 | `a2arg_blocked` |
| call result | 20 | none (measured) |
| unbound IR variable | none (javac does not allow it) | `a2u_strong`, `a2u_no_alias`: the update occurs, but no execution runs the body |
| constructor `this` in a method | none | `a3_method_blocked` |

### 2.5 Soundness and dominance of the DSU

| Claim | Status | Theorem (file) |
|---|---|---|
| In the heap-free fragment (`new`, `null`, `unknown`, `copy x y` with `x ≠ y`, any `seq`/`choice`/`loop`), the DSU is sound, if the DSU model run succeeds (`dsuProg ... isSome`). | proved | `dsu_sound_heapFree` (DSU/HeapFree.lean) |
| In the same fragment, each C alias of two variables (empty paths only) is a DSU alias (dominance). Conditions: the DSU model run succeeds, and no loop of C runs out of fuel (`aOk`). | proved | `dsu_dominates_heapFree` (DSU/HeapFree.lean) |
| The DSU is not exact, also in the smallest scope. | proved | `dsu_join_x_y` (DSU/Examples.lean), `pJoin_exact` (Sound/Boundary.lean) |

Known cases where dominance fails. Each case has a theorem or a computed example. The list is not complete: dominance with loads and stores is not proved (F6).

| Kind | Example | Evidence | Effect on the design |
|---|---|---|---|
| The DSU is unsound | U1-U4, LT1 | `a1_concept`, `a2_concept`, `b_unsound`, `static_unsound` (DSU/Examples.lean): C keeps the alias | C is sound there. |
| A sound DSU strong update in a loop | `loop { b = new; b.f = x; b.f = y }`, query `b.f ~ x` | `loop_dsu_more_precise` (DSU/Examples.lean) | Recency removes it: `loop_bf_x_exact` (Sound/Recency/Examples.lean). |
| The origin depth K of C | K = 1, `x.f.f ~ x.f.f.f` | `deep_concept_imprecise` (DSU/Examples.lean) | K ≥ D + 1 (D4). |
| The origin depth K of C, list walk | `cur = head; while (c) cur = cur.next;`, a walk longer than K | argued: `deep(head)` holds itself in each cell (`adefault`, Concept.lean) | The search rule of §6.2. |

On a root store, C with `entryUnique = true` (the default policy, D1) is more precise than the DSU: `root_concept_more_precise`.

Volume. Where dominance holds, each directed answer is a subset of the DSU answer, so it adds no alias volume (R0, §11.1). This is proved only for the heap-free fragment (`dsu_dominates_heapFree`).

---

## 3. Scope and assumptions

### 3.1 Assumptions built into the concrete semantics

The concrete semantics (`Concrete.lean`) builds A1-A3 in. So the soundness theorems have no extra hypothesis.

| Id | Assumption | How `Concrete.lean` builds it in |
|---|---|---|
| A1 | No entry aliasing. Entry roots are distinct objects. The entry heap below them is a tree. Objects that unknown expressions and calls return are new, with a tree below them. | `Obj.sym (Base.root r) p`: distinct root ids give distinct objects. `cdefault`: cell `c` of `sym b p` holds `sym b (p ++ [c])`. `Base.fresh s n` for results. |
| A2 | An unresolved call returns a new object. It keeps each cell, or writes a new object into a cell of a reachable object. It never makes existing objects alias. Three forms exist: A2-wide, A2-strict and A2-narrow (below). The call rule needs A2-narrow. | A2-wide: `Havoc st args s n h'`: `h' o c = st.heap o c`, or `Reach st args o` and `h' o c = sym (havoc s n k) []`. A2-strict: `HavocS` (Sound/Havoc/Concept.lean, §4.9). A2-narrow: `HavocN` (Sound/CellNamed/Concept.lean, §4.11). |
| A3 | Origin depth limit K for symbolic objects. The abstraction maps each deeper object to one origin `deep(b)`. | Only in the abstraction: `alpha K` maps paths longer than K to `deep b`. Concrete paths have no limit. |

The three forms of A2:

| Form | Reach of the callee | Objects written | Abstract call rule | Sound for |
|---|---|---|---|---|
| A2-wide | each symbolic object (`Reach`) | one call can write the same new object into several cells (free tag `k`) | site havoc origin `havoc(s)` (Lean only) | A2-wide, A2-strict, A2-narrow |
| A2-strict | each symbolic object (`Reach`) | a distinct new object into each cell that the call changes (`HavocS`) | per-cell havoc origins (Lean only; the precise reference, §4.9) | A2-strict, A2-narrow |
| A2-narrow | the closure of the argument values (receiver included) and of the static roots, through cells (`ReachN`) | as A2-strict (`HavocN`) | CN, the only call rule of the engine (§4.11) | A2-narrow only |

A2-narrow is the assumption of the call rule. Statement: an unresolved callee reaches only the closure of its arguments (receiver included) and of the static roots. It keeps each reachable cell, or overwrites it with a distinct new object for each cell. It makes no alias between existing objects. Each A2-narrow execution is an A2-strict execution and an A2-wide execution (`ExecN.toExecS`, `ExecN.toExec`). Under A1, the narrow reach is the faithful reach: an object that no argument and no static root reaches is reachable only through the locals of the method.

Both parts of A2-narrow are necessary for CN. Each part has a counterexample (Sound/CellNamed/Scope.lean):

| Part removed | Program and query | CN answer | Concrete fact | Theorem |
|---|---|---|---|---|
| narrow reach (the callee writes into a cell that no argument reaches) | `w = x.f; e = w.g; touch(); t = x.f; t.g = z`, query `w.g ~ e` | false: `x` is not exposed, so `t.g = z` is strong | an A2-strict execution with generous reach writes a new object into `x.f`; then `w.g` is still `e` | `generous_reach_breaks_CN` (`touch_noneN`: no A2-narrow execution has the alias) |
| strict havoc (one object in two cells) | `pHv = m(x); a = x.f; b = y.g`, query `a ~ b` | false: the names `⟨x.f⟩` and `⟨y.g⟩` differ | an A2-wide callee writes one object into `x.f` and `y.g` | `generous_havoc_breaks_CN` |

Out of scope under A2-narrow: (1) a callee that writes one new object into two cells, for example `void m(A x, B y) { Object o = new Object(); x.f = o; y.g = o; }`. The DSU also misses this shape (§4.9). (2) A callee that changes a cell of an object that its arguments and the static roots do not reach. Under A1 a Java callee cannot reach such an object: the entry trees are disjoint, and the method holds the other objects only in its locals (argued). A violation of (2) needs an entry alias, for example `this` of a singleton that a static field also holds, and §3.4 already puts that out of scope (argued). For such callees, only the taint analysis of the callee itself gives cover (§3.4).

Other properties of the concrete semantics:

| Property | Rule | Reason |
|---|---|---|
| Null dereference | A load or store through null **blocks** (no step). | Exceptions are out of the model (§3.4). |
| Array index | `aload`/`astore` take any index `i`. | Array cells are not separated. |
| Wide reach (A2-wide, A2-strict) | `Reach` makes each symbolic object reachable by the callee. This includes entry objects that the method detached, and objects that a later unknown expression or call returns (the heap is total). | It matches the DSU idea "groups with outer elements". It makes A2-wide wider again. |
| Narrow reach (A2-narrow) | `ReachN st statics args`: the argument values, the entry objects `sym (root r) []` of the static roots `r ∈ statics`, and each object in a cell of a reachable object of the current heap. | The proof of CN holds for each list `statics` (`csoundCN`). |
| Sites | Counter `cnt s` for each site. The n-th run of `new@s` makes `alloc s n`. | Distinct objects for each run. |

### 3.2 Parameters of the abstraction

| Parameter | Meaning | Lean |
|---|---|---|
| K | Origin depth: `sym(b, q)` with `\|q\| ≤ K`, else `deep(b)`. | `Ctx.K`, `symOrDeep` |
| `entryUnique` | Strong-update policy for symbolic origins. `true` (A1; the default, decided by the user, D1): unique entry paths and unique once-site results get strong updates. `false`: only allocations of once sites (and `alloc-new`) get strong updates. `false` is the intended policy of the DSU for outer bases. The measured DSU also strong-updates constructor `this` and summary sites (U1, §2.4). | `Ctx.entryUnique` (Concept.lean) |
| recency | Two origins for each allocation site: the most recent object and all older objects. | Sound/Recency/Concept.lean |
| D | Query depth: the number of accessors of a reported path. | `findAlias D` (Opt/Query.lean) |

K and D are different limits. K bounds the origin universe. D bounds the output paths. The design uses K ≥ D + 1 (§6.4).

### 3.3 Entry aliasing

A1 is a real restriction. The model shows that no local analysis can remove it. The user accepts A1 as a precondition of the intra-procedural analysis (D1, decided by the user): "We may lose some aliases, but it is acceptable. We remain intra-proc." So the default is `entryUnique = true`. The theorems below document the accepted loss.

| Claim | Status | Theorem (Sound/EntryAlias.lean) |
|---|---|---|
| The empty program aliases `x` and `y` if both are one root. Both policies answer no. | proved | `skip_unsound` |
| `x.f = z`: `y.f` aliases `z`. Both policies answer no. The missing alias is on the **read** side, so weak stores do not help. | proved | `write_read_unsound` |
| `swapFields(box, box)` aliases the two values. The default policy `entryUnique = true` answers no (unsound; the accepted loss of D1). The policy `false` answers yes, because the kept old value is the entry value. | proved | `swap_alias`, `swap_strong`, `swap_weak` |
| On the exact concrete frame of the execution (`frC`), both policies answer yes. | proved | `write_read_quotient`, `swap_quotient` |

Result: without caller information, no local analysis that separates two entry roots is sound under entry aliasing. Both policies are unsound there. The default policy `true` also loses aliases that the policy `false` keeps (`swap_strong`, `swap_weak`). No theorem orders the two policies in general. The user accepts this loss (D1). The policy `false` stays a policy value for an A/B check. Under A1, the soundness theorems hold for both policies (§4.5), and the completeness theorems use the default value `true` (§4.7).

The Lean quotient result needs the **exact** concrete root partition (`frC`). A caller partition that is only a may-partition (roots that are equal in some calls) makes a merged root denote two objects. Such a root is not unique. Use weak stores on merged roots, or analyze one time for each exact partition. This extension is not proved. The DSU has the same limit, because it also separates distinct arguments (argued).

### 3.4 Out of scope

| Item | Status | Reason |
|---|---|---|
| Exceptions | out of the Lean model | A null dereference blocks. The engine joins the states before and after each thrower on catch edges (§7.10), and gives the catch variable a fresh symbolic origin (§7.5). Both rules are argued. |
| Inlining of callees | out of the Lean model | Production uses inlining depth 1, and the directed engine keeps it (D12, decided by the user: "we keep inlining"). An inlined callee body is ordinary IR, so C applies to it (argued). §7.7 gives the design. |
| Callee-made aliasing of existing objects | out | A2 allows only new havoc objects. Example: an unresolved `m(x, y) { x.f = y; }`. The IFDS taint analysis covers a resolved callee through its own summary, and a library callee through its pass-through rules (argued). §9.1 lists the effect. |
| One new object in two cells | out under A2-narrow and A2-strict | §3.1 (`generous_havoc_breaks_CN`). Only the Lean site havoc rule covers it; the engine has no such mode (§7.6). |
| A callee that reaches an object that its arguments and the static roots do not reach | out under A2-narrow | §3.1 (`generous_reach_breaks_CN`). Under A1 a Java callee cannot reach such an object (argued). |
| Entry aliasing | out | §3.3. The user accepts the loss (D1). |
| Static roots and A1 | out | A static path and an argument (or `this` of a singleton) can be one object at entry. This breaks A1 more often than argument aliasing does. |
| Concurrency | out | Other threads can write shared cells between statements. Strong stores assume one thread. |
| Static initializers | out | A first static access can run `<clinit>`. It is not modelled as a call. |
| External pass-through models | not in the IR | §7.8 models `CopyAllMarks(from, to)` as a directed copy (`to ⊇ from`). |
| Static fields | not in the IR | The DSU model uses a static holder variable. C treats a static field as a cell of one root origin for each class (argued, §7.5). |

---

## 4. Concept C

### 4.1 Domain

Origins (`Origin`, Concept.lean):

| Origin | Denotes | Default cell content (`adefault K o c`) | Outer |
|---|---|---|---|
| `sym(b, q)`, `b = root r` or `fresh s`, `\|q\| ≤ K` | the entry object (or result object) at path `q` | `{symOrDeep K b (q ++ [c])}` | yes |
| `deep(b)` | all objects below `b` deeper than K | `{deep(b)}` | yes |
| `alloc(s)` | all objects of allocation site `s` | `∅` (null) | no |
| `havoc(s)` | all havoc objects of call site `s`, and all objects below them | `{havoc(s)}` | yes |
| `havocC(s, k, c, q)` | the object at path `q` below the new object that call `s` writes into cell `c` of a holder with key `k` (§4.9) | at cell `c'`: `{havocC(s, k, c, q ++ [c'])}` if `\|q\| + 1 ≤ K`, else `{havocDeep(s, k, c)}` | yes |
| `havocDeep(s, k, c)` | the objects of that tree deeper than K | `{havocDeep(s, k, c)}` | yes |
| `⟨@s.c.q⟩` (allocation child) | each object that a callee writes into cell `c` of an object of allocation site `s`, and the objects at path `q` below it, with recency below `alloc-new(s)` or `alloc-old(s)` (§4.11) | at cell `c'`: `{⟨@s.c.q.c'⟩}` if `q.c'` has at most K cells, else `{deep(@s.c)}` | yes |
| `deep(@s.c)` | the objects of the tree below `⟨@s.c⟩` deeper than K | `{deep(@s.c)}` | yes |

Concept C makes only the first four kinds. The per-cell refinement (§4.9) makes `havocC` and `havocDeep`. The call rule CN (§4.11) makes no call origin: it makes only allocation children, and it names every other unknown object by a symbolic or deep origin of the first rows.

Abstract state (`AState`): `env : Var → List Origin` and `heap : Origin → ACell → List Origin`. The entry heap is `adefault K`. The entry env maps each frame variable bound to root `r` to `{sym(root r, [])}`, and each other variable to `∅`. Abstract cells are `fld f` and `elem` (all array indices). Null is no origin. An empty set means "always null".

### 4.2 Uniqueness

`once s` (`Prog.onceB`): site `s` occurs at most one time in the program, and not under a loop.

`Origin.uniqueB once entryUnique` (Concept.lean):

| Origin | `uniqueB` |
|---|---|
| `sym(root r, q)` | `entryUnique` and `elem ∉ q` |
| `sym(fresh s, q)` | `entryUnique` and `once s` and `elem ∉ q` |
| `deep(b)` | false |
| `alloc(s)` | `once s` |
| `havoc(s)`, `havocC`, `havocDeep`, `⟨@s.c.q⟩`, `deep(@s.c)` | false |

Recency (Sound/Recency/Concept.lean): `alloc-new(s)` (Lean `rNew s`, encoded `alloc (2s)`) is the most recent object of site `s`. `alloc-old(s)` (Lean `rOld s`, encoded `alloc (2s+1)`) is all older objects.

| Origin | `uniqueR once entryUnique` |
|---|---|
| `alloc-new(s)` | true, for each site, also in a loop |
| `alloc-old(s)` | false |
| other | `uniqueB once entryUnique` |

`retire s X`: rename `alloc-new(s)` to `alloc-old(s)` in each value. Move the cells of `alloc-new(s)` into the cells of `alloc-old(s)` (union). Give `alloc-new(s)` empty cells.

With the call rule CN (Sound/CellNamed/Concept.lean), uniqueness also reads the exposed set `E` of the state: `uniqueCN = uniqueR && !expB E`. `expB E (sym(b, q))` is true if `E` holds `sym(b, p)` for a proper prefix `p` of `q`. So a symbolic origin below an exposed origin is not unique. The exposed origin itself keeps its uniqueness: a callee cannot change the value of a variable. Allocation origins and depth-0 origins (entry roots, results `sym(fresh s, [])`) keep the rules above. §4.11 gives the reason.

### 4.3 Transfer table

Notation: `H(o, c)` is the content of cell `c` of origin `o`. `S ∪= T` is a weak add.

| Statement | Rule of C (`astep`) | Rule with recency (`astepR`) |
|---|---|---|
| `x = new@s` | `pts(x) := {alloc(s)}` | `retire s`, then `pts(x) := {alloc-new(s)}` |
| `x = null` | `pts(x) := ∅` | same as C |
| `x = y` | `pts(x) := pts(y)` | same as C |
| `x = y.f` | `pts(x) := ⋃ { H(o, f) : o ∈ pts(y) }` | same as C |
| `x.f = y` | strong if `single? pts(x) = some o` and `o` is unique: `H(o, f) := pts(y)`. Else weak: `H(o, f) ∪= pts(y)` for each `o ∈ pts(x)`. | the same with `uniqueR` |
| `x = y[i]` | `pts(x) := ⋃ { H(o, elem) : o ∈ pts(y) }` | same as C |
| `x[i] = y` | always weak: `H(o, elem) ∪= pts(y)` for each `o ∈ pts(x)` | same as C |
| `x = unknown@s` | `pts(x) := {sym(fresh s, [])}` | `retire s`, then the same |
| `x = call@s(args)` | havoc: `H(o, c) ∪= {havoc(s)}` for each universe cell `c` and each `o` with `reachB o`. Then `pts(x) := {sym(fresh s, [])}`. Per-cell havoc: §4.9. The call rule CN: §4.11. | havoc, then `retire s`, then the same |

The strong-update condition, as in Lean (`AState.store`):

```lean
match single? (X.env x) with
| some o => if o.uniqueB once entryUnique then X.setCell o c S else X.weakStore (X.env x) c S
| none   => X.weakStore (X.env x) c S
```

`single? l = some o` if `l` is not empty and each element is `o`. So `[o, o]` counts as one origin. With `pts(x) = ∅` the store does nothing. This is sound, because the concrete store blocks.

Reach of a call (`reachB ctx X args`): `o` is reachable if `o` is outer, or if `o` is in the closure of `pts(args) ∪ {outer universe origins}` under all universe cells. If the closure does not converge within its fuel, each origin is reachable. This is the generous reach of A2-wide and A2-strict. CN uses the narrow closure of §4.11 (`closeN`).

Remarks:

- `astep` is not monotone (a strong update with `pts(x) = ∅` against `{o}`). The soundness proof uses local soundness and upward closure only (`step_sound`, `Inv.mono`).
- In the model, `unknown` and `call` share the site counter with `new`. In JIR each statement has its own site, so `retire` matters only for `new` (argued).

### 4.4 Join, loops, query

| Operation | Rule | Lean (Concept.lean) |
|---|---|---|
| Join | Pointwise union of `env` and `heap`. | `join` |
| Loop | Kleene iteration from the entry state. Stop at the first state `Y` with `f Y ⊆ Y` on the universe (a checked post-fixpoint). If the fuel runs out, give `top` (each universe origin everywhere). An inner loop starts a new iteration from the current state in each outer iteration. | `loopIter`, `loopIter_post`, `sub_loopIter` |
| Fuel | `(\|vars\| + \|O\|·\|cells\|)·\|O\| + 1`. This bounds the number of strict increases over the universe (argued; no theorem). | `Ctx.ofProg` |
| Path value | `aevalPath X x [c1..cn]`: start at `pts(x)`, then read cell `ci` of each origin. | `aevalPath` |
| May-alias | `may X x px y py = meetB (aevalPath X x px) (aevalPath X y py)` | `may`, `may_iff` |
| Program query | `mayProg K fr p x px y py`: analyze `p` from `ainit K fr` with the query fields in the universe, then `may`. | `mayProg` |

`may` is symmetric (`may_symm`, Sound/Facts.lean). It is not transitive (`may_not_transitive`, Examples.lean).

### 4.5 Soundness

Statement (`CSound K`, Concept.lean):

```lean
∀ fr p x px y py, CAlias fr p x px y py →
  mayProg K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true
```

`CAlias fr p x px y py`: one execution of `p` from the entry state of frame `fr` ends with `x.px` and `y.py` the same object. Null is never an alias.

| Theorem | Statement | File |
|---|---|---|
| `csound K` | `CSound K` for each K (`entryUnique = true`, the default policy). | Sound/Soundness.lean |
| `csoundE eu K ...` | The same for both policies (`mayProgE eu`). | Sound/Soundness.lean |
| `csoundR eu K ...` | The same with recency, both policies (`mayProgR eu`). | Sound/Recency/Soundness.lean |
| `csoundH src eu K ...` | Per-cell havoc without recency (`mayProgH eu`): each one-execution alias under A2-strict (`CAliasS src`), for each tag naming `src`, is a may-alias. Both policies. | Sound/Havoc/Soundness.lean |
| `csoundHR src eu K ...` | Per-cell havoc with recency (`mayProgHR eu`). The same statement, both policies. | Sound/HavocRecency/Soundness.lean |
| `csoundCN src statics eu K ...` | The call rule CN with recency (`mayProgCN eu K statics`): each one-execution alias under A2-narrow (`CAliasN src statics`) is a may-alias. For each tag naming `src`, each list of static roots, each K and both policies. | Sound/CellNamed/Soundness.lean |

The first three theorems use A2-wide (`CAlias`). `csoundH` and `csoundHR` use A2-strict, and they do not hold under A2-wide (`generous_breaks_strict`, §4.9). `csoundCN` uses A2-narrow, and it holds neither with generous reach nor under A2-wide (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`, §3.1). `no_alias_of_mayProgCN` is the contrapositive: a false answer of CN excludes each A2-narrow execution with the alias.

The invariant (`Inv`, Sound/Invariant.lean) is the contract of each transfer rule. It relates a concrete state to an abstract state:

- each live concrete object `o` has the origin `alpha K o` in the universe;
- for each variable, `alpha K` of its value is in `pts` of the variable;
- for each cell of a live object, `alpha K` of its content is in `H(alpha K o, c)`;
- a unique origin denotes at most one live object (`unique_obj`, Sound/Step.lean).

Main lemmas:

- Each statement keeps the invariant (`step_sound`).
- The invariant is closed upward (`Inv.mono`).
- The weak havoc keeps it (`reachB_of_reach`, `Inv.havoc`).
- A once site runs at most one time (`Exec.cnt_le`).
- A loop keeps it (`loop_keeps`).
- With recency, a counter increase keeps it (`retire_inv`, `alphaR_bump`, `unique_objR`).
- With CN, the call keeps the extended invariant `InvCN` (`havocCN_sound`, §4.11).

Soundness has no hypothesis beyond the concrete semantics: A1-A3, one thread, no exceptional flow, and callees that write only new objects (A2-wide for site havoc, A2-strict for per-cell havoc, A2-narrow for CN).

Scope of the statement. It is about the end of the program and a cell universe that contains the query fields. Soundness at an inner point follows for a structured program by a prefix argument (argued). Soundness of the query (`findAlias`) follows from `csound` and `findAlias_iff` for paths over the analysis cells. The engine never reports a path over a field outside the analysis cells. Under mode `SHARED` such a path can be a real alias.

The O invariants are `Tbl.Good` (§5.2) and `Rel` (§5.5).

### 4.6 Completeness: what it means

Completeness here means cross-execution exactness:

```lean
CCompleteIn K scope :=
  ∀ fr p x px y py, scope fr p px py → mayProg K fr p x px y py = true →
    ∃ cx cy, cx.map Cell.abs = px ∧ cy.map Cell.abs = py ∧ CAliasX fr p x cx y cy
```

`CAliasX`: `x.cx` at the end of one execution and `y.cy` at the end of a second execution are the same object.

Why not one-execution exactness (argued; measured for the DSU):

```java
if (c) { a = x; b = y; } else { a = y; b = x; }
```

- No execution makes `a == b`.
- A sound analysis must have `ox ∈ pts(a)` (left run: `a == x`) and `ox ∈ pts(b)` (right run: `b == x`).
- So `pts(a) ∩ pts(b) ≠ ∅` in each non-relational points-to analysis (one set for each holder, intersection as may-alias).
- Thus no such analysis is one-execution exact. A relational domain (correlations between variables) is necessary for that.
- Across executions, `a` (left run) and `b` (right run) are the same object `x`. So C is exact in the cross-execution sense.
- Measured: probe row 7. The DSU gives the same answer.

### 4.7 Completeness scopes

Scope 1, the store-free core (`coreScopeB`, Sound/NullSafe.lean). All conditions are checkable:

| Condition | Lean |
|---|---|
| No loop, no call, no store, no array store | `coreP p` |
| Each site is `once` | `p.sites.all p.onceB` |
| Depth bound | `loadsP p + \|px\| ≤ K` and `loadsP p + \|py\| ≤ K` |
| No execution blocks | `nullSafeB fr p` (null kinds `sym` / `obj` / `maybe`) |

Scope 2, the certified store scope (`storeScopeB`, Sound/StoreScope.lean):

| Condition | Lean |
|---|---|
| Each site is `once`. The depth bound holds. | `p.sites.all p.onceB`, `loadsP p + \|px\| ≤ K`, `loadsP p + \|py\| ≤ K` |
| The certificate accepts the program | `(bcert ctx p (entryKinds fr) (ainit K fr)).isSome` |

The certificate `bcert` runs with the analysis:

| Program part | `bcert` condition |
|---|---|
| Store `x.f = y` | `x` and `y` are not `maybe` null. Each has exactly one origin (`single?`), and the origin is unique. |
| Load | It cannot block: the base is not `maybe` null. |
| Join of `p` and `q` | `joinOK` holds for each universe origin and cell if one of two conditions is true. (1) The two branch heaps are equal. (2) The origin is `alloc(s)` for a site of one branch, and the cell is empty in the other branch. |
| Loop, call, array store | rejected |

| Theorem | Statement | File |
|---|---|---|
| `ccomplete_core K` | `CCompleteIn K (CoreScope K)` | Sound/Complete.lean |
| `ccomplete_coreB K` | `CCompleteIn K` for the Boolean scope `coreScopeB` | Sound/NullSafe.lean |
| `coreScopeB_sound` | The Boolean scope implies the semantic scope. | Sound/NullSafe.lean |
| `ccomplete_store K` | `CCompleteIn K` for `storeScopeB` | Sound/StoreScope.lean |
| `value_of_strong` | A variable with one unique origin holds the canonical object of that origin when it is not null. So a certified store is deterministic. | Sound/StoreScope.lean |
| `realize`, `realizeB` | An execution realizes each origin in the result. The proof builds the execution. | Sound/Complete.lean, Sound/StoreScope.lean |
| `init_in_scope`, `init_exact` | `if (*) { a = new; a.f = x } else { a = y }; t = a.f` is certified and exact. | Sound/StoreExamples.lean |
| `pre_in_scope` | `x.f = z; if (*) a = x else a = y; t = a.f` is certified. | Sound/StoreExamples.lean |
| `field_rejected` | The certificate rejects the field example (`a.f = z` through two origins is weak). | Sound/StoreExamples.lean |

The completeness theorems use the policy `entryUnique = true`. This is the default policy (D1), so the theorems cover the default value of `entryUnique`. Completeness of recency is not proved (F9 would carry the theorems to recency when each site is once). With the A/B value `entryUnique = false`, the store-free core does not depend on the policy, because it has no store (argued). The certified store scope then accepts only stores on unique allocation origins (argued).

Witnesses. Each example witness is an explicit choice list (the branch choices of one execution). The executor `runFrom` runs it, and `decide` checks the result (`runAliasB_sound`, Concrete.lean). For example, `field_xf_z_witness` is `runAliasB_sound (cs := [.left]) (by decide)`. Executable witnesses for the completeness theorems (Sound/Witness/). The theorems above conclude a Prop-level `∃`, which Lean cannot run. So the model adds a computable search `crossWitness fr p x px y py`. It tries every choice list of a loop-free, call-free program and every concrete path that abstracts to the query paths, with array indices below a fixed bound. It returns the first pair of executions that aliases the two paths. `crossWitness_sound`: each result is a cross-execution alias. `crossWitness_complete`: for each loop-free, call-free program, each cross-execution alias makes the search succeed, so `crossWitness_none_iff` decides `NoCrossAlias`. `witness_core` and `witness_store`: in the core scope and in the certified store scope, `mayProg = true` makes the search succeed. `coreWitness` and `storeWitness` return the witness as a value (`coreWitness_spec`, `storeWitness_spec`). `oneWitness` is the same search for one-execution aliases (`oneWitness_sound`, `oneWitness_complete`). Example: on `pJoin`, the search returns the choice lists `[left]`, `[left]` for `a ~ x`, and `none` for `x ~ y`. Loops and calls are outside the search; it then returns `none`, which stays sound.

Exactness certificate as an analysis output (argued). `bcert` reads only the abstract states and the null kinds. The engine can compute it in the same pass. Proposed uses:

- an exactness result for each method and query depth: true if the method has no loop and no call, and is in a scope for paths up to that depth;
- a test oracle: if the result is true, each reported may-alias must have a witness pair of executions;
- a precision metric: the share of methods (and of queries) with exact answers (`DirectedAliasStats.exactMethods`, §11.2).

The next scope to prove is "the core plus unresolved calls under A2-narrow" (F6). The three losses of CN (§4.11) bound it: such a scope must exclude them. Calls are the most common reason that a method is outside the proved scopes.

### 4.8 The boundary: counterexamples CX1-CX7

Each row has a theorem `mayProg = true` and a theorem `NoCrossAlias`: no concrete paths that abstract to the query paths alias in any pair of executions. File: Sound/Boundary.lean. CX7 uses `loop_bf_x` from Examples.lean.

| Id | Condition broken | Program | Query | `may` theorem | no-alias theorem |
|---|---|---|---|---|---|
| CX1 | depth bound | `skip`, K = 1 | `x.f.f ~ x.f.f.f` (both `deep`) | `deep_may` | `deep_none` |
| CX2 | once sites | `x = new@7; y = new@7` | `x ~ y` | `twice_may` | `twice_none` |
| CX3 | no blocking | `if (*) { y = x; u = null } else { y = null; u = z }; t = y.f` | `u ~ z` | `block_may` | `block_none` (`block_unsafe`: the null check rejects it) |
| CX4 | store-free (strong store in a branch) | `e = x.f; if (*) { x.f = z; a = x } else { a = y }; t = a.f` | `t ~ e` | `corr_may` | `corr_none` |
| CX5 | store-free (strong store, value with 2 origins) | `if (*) a = x else a = y; x.f = a` (and `...; x.g = a`) | `x.f.f ~ y` (and `x.f.g ~ y`) | `strongTwo_may`, `strongTwoG_may` | `strongTwo_none`, `strongTwoG_none` |
| CX6 | store-free (weak store) | `if (*) a = x else a = y; a.f = y` | `x.f.f ~ y` | `weak_may` | `weak_none` |
| CX7 | loop-free | `loop { b = new@7; b.f = x; b.f = y }` | `b.f ~ x` | `loop_bf_x` (Examples.lean) | `loop_none` |

`noCrossB_sound` and `run_complete` (Sound/Boundary.lean) give the decision procedure for the loop-free cases. The certificate rejects CX4, CX5, CX6 (`corr_rejected`, `strongTwo_rejected`, `strongTwoG_rejected`, `weak_rejected`, Sound/StoreExamples.lean).

Findings from the boundary:

| Finding | Evidence |
|---|---|
| "Stores are exact when each store is strong" is false. Correlated control (CX4) and correlated values (CX5) break it. | CX4, CX5 |
| Null blocking correlates variables. A per-variable domain cannot express it. The null check is the scope guard. | CX3 |
| A site that runs twice without a loop is not exact. JIR has one site for each statement. | CX2 |
| In loops, "unique = once site" is too weak. Recency fixes the tested shape: `mayProgR` answers no, and this is exact. | CX7, `loop_bf_x_fixed`, `loop_bf_x_fixed_weak`, `loop_bf_x_exact` (Sound/Recency/Examples.lean) |

Calls are in no proved scope. Under A2-wide, any reachable cell can get a havoc object, so we expect that each abstract `havoc(s)` edge has a concrete execution. No proof exists. Status: open (F6). §4.9 shows that A2-wide is not the right target for calls. Under the narrower call semantics, completeness counterexamples for calls exist: `cost_answers` with `cost_none` for per-cell havoc (§4.9), `precision_order_fails` with `nest_noneN` for per-cell havoc, and the three losses `losses_CN` with `loss1_noneN`, `loss2_noneN`, `loss3_noneN` for CN (§4.11).

### 4.9 CEGAR step 2: per-cell havoc origins (the precise reference)

Status. Per-cell havoc was the call rule until 2026-10-29. Then the user found it too expensive, and CEGAR step 4 replaced it by the call rule CN (§4.11). Per-cell havoc stays in the Lean model only, as the formal reference for the precision comparison: it is proved sound under A2-strict. The engine does not implement it. The user dropped the engine mode `PER_CELL` on 2026-10-29 (§7.6, D2). CN and per-cell havoc are incomparable in precision (`precision_order_fails`, §4.11).

This step has two parts. First, it narrows the concrete call semantics from A2-wide to A2-strict. This is a scope change, not an abstraction error: under A2-wide, the aliases of the counterexample below are real. After the change, the soundness claim covers fewer callees. Second, it refines the abstraction, so that C keeps its precision under A2-strict. The site havoc rule stays in the Lean model, and it stays sound for A2-wide. The engine does not implement it (§7.6).

Counterexample. The program uses the frame of Examples.lean:

```
pHv = m(x); a = x.f; b = y.g
```

| Query | `mayProg 1 fr pHv ...` |
|---|---|
| `a ~ b` | true |
| `a ~ z.f` | true |
| `a ~ w.g` | true |

Proved: `havoc_spread` (Sound/Havoc/Examples.lean).

Cause. C has one origin `havoc(s)` for each call site. The call adds `havoc(s)` to each universe cell of each reachable origin. Each outer origin is reachable. So after one call, each value that the method loads from an outer cell holds `havoc(s)`, and each outer cell holds `havoc(s)`. That value may-aliases each outer heap path of each root, up to the query depth. `findAlias(a)` then has about `|vars|·|cells|^D` paths.

Verdict under each concrete semantics:

| Concrete call semantics | Is `a ~ b` real? | Consequence |
|---|---|---|
| A2-wide (`Havoc`, §3.1): one call can write **one** object into many cells | yes: the callee can write one object into `x.f` and `y.g` | C is exact here. |
| A2-strict: the callee writes a distinct new object into each cell, with a new tree below it | no: no execution aliases `a` and `b` (`strict_ab_none`) | The alias is false. The DSU does not report it (`dsu_ab`): after the removal, a later load makes a new heap element for each cell. |

Out of scope after this step: a callee that writes one new object into two cells (§3.1, §3.4).

Refinement. Replace `havoc(s)` by per-cell havoc origins:

| Item | Rule |
|---|---|
| Origin | `havocC(s, k, c, [])`: the object that call `s` writes into cell `c` of a holder with key `k`, and the tree below it. Never unique. |
| Key | The key of a holder `o` is `o` itself, except for a havoc-derived holder: its key is its site origin `havoc(s0)` (Lean `keyOf`). So keys never nest. With recency, both `alloc-new(s')` and `alloc-old(s')` have the key `alloc-old(s')` (Lean `keyOfR`). So the key does not depend on the site counter. |
| Call rule | For each reachable universe origin `o`, and each universe cell `c`: `H(o, c) ∪= {havocC(s, keyOf(o), c, [])}` (`AState.havocH`; with recency `havocHR`, then `retire s`). |
| Default content below `havocC` | As in §4.1. |
| Finite universe | Keys range over origins that are not havoc-derived. The universe stays finite, so loops terminate. |
| Concrete side | A2-strict (`HavocS`): a distinct new object for each cell. |

Status: proved. The theorems are in Sound/Havoc/, Sound/HavocRecency/, Opt/Havoc.lean and Opt/HavocRecency.lean.

| Claim | Theorem | Status |
|---|---|---|
| A2-strict as a concrete semantics: each new object goes into one cell only; each strict run is a wide run | `HavocS.inj`, `fresh_at_call`, `ExecS.toExec` | proved |
| Per-cell havoc is sound under A2-strict, for each K and both policies | `csoundH` (the only new step: `InvS.havocH`) | proved |
| Recency with per-cell havoc is sound under A2-strict, both policies | `csoundHR` (shared invariant `InvG`; new step `InvG.havocHR`) | proved |
| The key does not depend on the site counter, so `retire` never renames a per-cell havoc origin | `keyOfR_alphaRS` | proved |
| O equals the concept, per-cell havoc | `mayProgHO_eq`; cost of one call `addHv_work` | proved |
| O equals the concept, recency with per-cell havoc; so O is sound | `mayProgHRO_eq`, `csoundHRO` | proved |
| On `pHv`, the spread is gone: `a ~ b`, `a ~ z.f`, `a ~ w.g` are false; `a ~ x.f` stays true | `strict_answers`, `strict_ab_none`, `strict_az_none`, `strict_axf_keep`, `strict_axf_new` | proved |
| Under A2-wide, the spread is real, so the refinement needs A2-strict | `spread_real_ab`, `spread_real_az`, `generous_breaks_strict` | proved |
| `loop_bf_x` stays exact with both refinements | `loop_bf_x_exactHR` | proved |
| Per-cell havoc needs recency too: on `pBoth = loop { b = new@7; b.f = x; b.f = y }; m(x); a = x.f; c = y.g`, only the combination answers `b.f ~ x` and `a ~ c` false, and both are exact | `both_answers`, `both_bf_x_none`, `both_a_c_none` | proved |
| The shared key `alloc-old(s)` is sound, and it has a precision cost: `o = new@7; b = new@7; m(b, o); t = b.f; u = o.f` answers `t ~ u` true, but no strict execution aliases them. Recency alone and per-cell havoc alone also answer true, so this is no regression against a proved configuration | `keyOfR_alphaRS`, `csoundHR`; `cost_answers`, `cost_none` | proved |
| "The combination is at least as precise as each refinement alone" | none (evidence: all examples) | open (F6) |
| A finer key (the current recency origin of the holder) removes the `cost_answers` alias | none (`retire` must then rename and merge per-cell havoc origins) | open (F6) |
| A more precise rule for havoc-derived holders: the new object goes into the tree of its holder, with no new origin | none for per-cell havoc. The proved rule is the model rule of the Key row. CN uses this idea for each holder: a callee object below a callee object extends the path of its cell name (§4.11). | open for per-cell havoc (F1) |
| Completeness for calls | none | open (F6) |

Why the call needs a havoc origin at all (HavocNeed.lean). The weak havoc keeps the old content, because the callee can keep the cell. It also adds a havoc origin, because the callee can write a new object. Without the havoc origin (keep the old content, add nothing) the analysis is unsound in two ways:

| Case | Program | Real alias (witness) | Without havoc | With havoc |
|---|---|---|---|---|
| A later strong update writes the old object | `w = x.f; e = w.g; m(x); t = x.f; t.g = z` | `w.g ~ e`, if `m` writes a new object into `x.f` (`strong_after_call_real`) | `pts(t) = {⟨x.f⟩}` is unique, so `t.g = z` is strong and removes `e` from `w.g`: false (`strong_after_call_nohavoc`) | `pts(t)` has two origins, so the store is weak: true (`strong_after_call_havoc`, `strong_after_call_havocHR`) |
| The old content is empty | `n = new N(); m(n); a = n.f; b = n.f` | `a ~ b`, if `m` writes one new object into `n.f` (`empty_cell_real`) | `n.f` stays null: false (`empty_cell_nohavoc`) | both loads hold the havoc origin: true (`empty_cell_havoc`, `empty_cell_havocHR`) |

The second case is each constructor that the analysis does not inline (§7.6). CN answers both cases true (`need_answersCN`), and both aliases are real under A2-narrow (`strong_after_call_realN`, `empty_cell_realN`, §4.11).

Effect: on `pHv`, `a ~ b`, `a ~ z.f` and `a ~ w.g` become false. The old content of each cell stays, so the fix of U2 stays. The user decided that the may analysis keeps the old content (no alias drop, D2). Per-cell havoc was the first havoc-origin form of D2. The user replaced it by CN on 2026-10-29 (§4.11, §12).

### 4.10 Precision relative to the DSU

| Program | C | DSU | Exact answer | Evidence |
|---|---|---|---|---|
| task example, `x ~ y` | no | yes | no | `join_precision_loss` |
| field example after `a = w`, `x ~ y` | no | yes | no | `field_precision_loss` |
| field example, `x.f ~ z`, `y.f ~ z` | yes | yes | yes | `dsu_field_xf_z`, `field_xf_z` |
| root store `x.f = y; x.f = z`, `x.f ~ y`, policy `entryUnique = true` (the default) | no | yes | no | `root_concept_more_precise` |
| loop strong update, `b.f ~ x` | yes (C), no (recency) | no | no | `loop_dsu_more_precise`, `loop_bf_x_exact` |
| K = 1, `x.f.f ~ x.f.f.f` | yes | no | no | `deep_concept_imprecise` |
| U1-U4 | yes (sound) | no (unsound) | yes | §2.3 |
| `pHv`, `a ~ b` after a call | yes (site havoc), no (per-cell havoc, CN) | no | no under A2-strict and A2-narrow | §4.9, §4.11 (`spread_goneCN`) |

Recency keeps the other answers (`join_answers`, `field_answers`, `strong_answers`, `call_answer`, Sound/Recency/Examples.lean). Not proved: "recency is at least as precise as C" in general (F6).

The volume table of §11.1 (R0) gives the effect of each row on the alias answer volume.

### 4.11 CEGAR step 4: cell-named havoc with narrow reach (the call rule)

Status: the call rule of the design (D2, decided by the user 2026-10-29). Short name: CN. It is the only call rule of the engine (§7.6). The compact specification states the same rule (`directed-alias-analysis-spec.md` §4, §5.6). Lean: Sound/CellNamed/ and Opt/CellNamed.lean.

History. The step started from a cost problem, not from a wrong answer:

| Order | Finding | Evidence |
|---|---|---|
| 1 | Per-cell havoc (§4.9) is too expensive (the user, 2026-10-29). At each call it adds `havocC(s, keyOf(o), c, [])` to each universe cell of each reachable origin, and each symbolic origin is reachable (§4.3). So each call writes almost the whole heap map. Each call site adds new origins, so the values grow with the number of calls. | the user; the cost of one call is linear in the number of keys (`addSets_work`, §5.5) |
| 2 | A lazy havoc log records the calls and applies them at a read. The havoc layer of the earlier engine design was such a log. The user rejected it: it complicates state identity and the join. | the user |
| 3 | A "dead-end" rule gives an unknown object no origin: the call keeps the old content and adds nothing. It is unsound. In `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, `m` can write a new object into `n.f`. Then the left branch makes `b == d`. With the dead-end rule, `pts(a) = ∅`, so `b ~ d` is false. | `dead_realN` (the alias is real); `dead_answerCN` (CN answers true) |
| 4 | CN. The user accepted it with its three precision losses (below). | `csoundCN`, `mayProgCNO_eq` |

Scope change. CN needs A2-narrow (§3.1): the callee reaches only the closure of its arguments (receiver included) and of the static roots, and it writes a distinct new object into each cell that it changes. Both parts are necessary (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`, §3.1).

Cell names. The rule names each unknown object by the cell where the method finds it. `name(o, c)` is the name of each object that a callee can write into cell `c` of origin `o` (Lean `childCN K o c`):

| `o` | `name(o, c)` | Lean |
|---|---|---|
| `sym(b, q)` | `symOrDeep(b, q ++ [c])`: the default content of the cell | `symOrDeep K b (q ++ [c])` |
| `deep(b)` | `deep(b)` | `deep b` |
| `alloc(t)`, `alloc-new(t)`, `alloc-old(t)` | `⟨@t.c⟩`, the same name for the most recent object and the older objects | `hsym 0 (rOld t) c []` (the key `keyOfR`) |
| `⟨@t.c0.q⟩` | `⟨@t.c0.q.c⟩`, or `deep(@t.c0)` beyond K | `extendCN`: the path grows |

Consequences of the definition:

- The name is a function of `(o, c)` only. So a call creates no origin. A cell can get its name, but no call adds a second name to it. Repeated calls do not grow the values (argued from the definition).
- For an unwritten cell of a symbolic origin, the name is the default content. So the call needs no work there.
- `alloc-new(t)` and `alloc-old(t)` give the same name. So `retire` renames no name.
- A callee object below a callee object has a name that extends the path of the name of its holder. So the names never nest, and the universe stays finite.

Lean encoding. The model encodes `⟨@t.c.q⟩` as `hsym 0 (rOld t) c q` and `deep(@t.c)` as `hdeep 0 (rOld t) c`, and keeps `Concept.lean` unchanged (no new base constructor). The depth limit counts the path `q` below the first cell `c`. The specification and the engine use the same form, so the Lean vectors compare by equality.

Exposed set. The abstract state gets one more component: the set `exposed` (`E`) of the origins that some call reached. It is empty at entry. A call adds its closure `R`. The join is the union. `retire` renames inside it. The Lean model keeps it as the value of one reserved variable `xe` (`CtxN.xe`, `ctxCN`), so the join, the loop test and `top` treat it as each other variable.

Uniqueness rule: `uniqueCN = uniqueR && !expB E` (§4.2). A symbolic origin `sym(b, q)` is not unique if `E` holds `sym(b, p)` for a proper prefix `p` of `q`. Reason: a call that reaches `sym(b, p)` can put a new object into a cell below it. That object has the name of its cell, and the name of the cell is the name of the old object. So the name can denote two live objects. Example (HavocNeed.lean): `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. After `m(x)`, `⟨x.f⟩` can denote the old object in `w` and a new object of `m`. So `t.g = z` must be weak, and `w.g ~ e` stays (`need_answersCN`; real: `strong_after_call_realN`). The exposed origin itself stays unique. A callee object gets the name `sym(b, p)` only in a cell of a covered origin `sym(b, p')` with `p = p' ++ [c]`. Then `R` holds a prefix of `p'`, which is a proper prefix of `p`, so `sym(b, p)` is below an exposed origin. A callee cannot change the value of a variable.

Closure. At call site `s` with arguments `a1 .. an`:

1. Start set (`callRoots`): `R := pts(a1) ∪ ... ∪ pts(an) ∪ {sym(root r, []) : r a static root}`. The receiver is an argument.
2. Covered origins (`coveredB R`): each origin of `R`; each `sym(b, q)` with `sym(b, p) ∈ R` and `p` a prefix of `q`; each `deep(b)` with some `sym(b, p) ∈ R`. Lean `descB` also counts the allocation children of a covered allocation. This has no effect on the result: an allocation child is never unique, so its cells always keep the default child.
3. Closure (`succsN`, `closeN`): add to `R` the content of each universe cell of each covered origin. Repeat until `R` does not grow. The closure is a checked closure with fuel, as `closeIter` of Concept.lean.
4. Fallback (`havocCN`): if the closure does not converge within its fuel, the call covers each origin and exposes each universe origin. This is sound.

Coverage includes the descendants for a reason. A callee can reach an object through a cell that the method never names. Such an object can come back to a universe name only as `deep(b)` (`reach_cover`, the `outside` part of the invariant). The model does not prove that a narrower coverage is sound. So the engine keeps the rule as stated.

Call rule (`astepCN`, the call case):

1. Compute `R` (closure above).
2. Weak havoc by name (`havocWith`): for each covered origin `o` and each universe cell `c`: `H(o, c) ∪= {name(o, c)}`. The old content stays, because the callee can keep the cell. For an unwritten cell of a covered symbolic origin this changes nothing.
3. Exposure: `E := E ∪ R`.
4. Recency: `retire(s)`. Result: `pts(x) := {sym(fresh s, [])}`.

The store is `storeCN`: strong if `single? pts(x) = some o` and `uniqueCN o`, else weak. Each other statement is as in recency with per-cell havoc (`astepHR`): copy, `new` (with `retire`), null, load, array load, array store (weak), `unknown`, join, `loopIter`.

Origins of the default configuration (Lean `originsCN`):

| Origin | Source |
|---|---|
| `sym(b, q)`, `deep(b)` | `b` an entry root, a static root, or the result of an unknown expression or call at site `s` (`sym(fresh s, [])`) |
| `alloc-new(s)`, `alloc-old(s)` | allocation sites (recency) |
| `⟨@s.c.q⟩`, `deep(@s.c)` | allocation sites (`heapKids`): the callee objects below allocations |

The default configuration has no `havoc(s)`, no `havocC` and no `havocDeep`. The engine adds the constant origins of §7.5.

Proof (Sound/CellNamed/). The abstraction of a callee object needs the name of its holder, and the holder can itself be a callee object. A direct definition through the tag map `src` does not terminate. So the proof uses a ghost naming `N`: when call `(s, n)` writes tag `k` into the cell `src k = (O, c)`, the proof sets `N s n k := childCN (alpha O) c` (`namesAfter`). The invariant is `InvCN = ∃ N, InvG ∧ InvX ∧ CntOK`. `InvG` is the generic invariant of Sound/HavocRecency/Inv.lean; its lemmas for variables, stores, `retire`, loops and queries are used without change. `InvX` adds the facts about names (`NameOK`, `ExpOK`). The three new facts:

| Fact | Lemma |
|---|---|
| A written object has the name of its cell, and the abstract call adds that name, because the holder of the cell is covered. | `InvG.havocCN`, `reach_cover` |
| A unique origin denotes at most one live object. A callee object never has a unique origin: its name is junk, or not symbolic, or below an exposed origin. | `unique_objCN`, `not_havoc_of_unique`, `expOK_closure` |
| A narrow call keeps each cell that the callee cannot reach. So an unchanged abstract cell is sound. | `reach_facts`, `junk_kept`, `written_reach` |

The main lemmas are `havocCN_sound`, `step_soundCN`, `analyze_soundCN` and `inv_initCN`.

Theorems:

| Claim | Theorem | Status |
|---|---|---|
| A2-narrow as a concrete semantics; each A2-narrow execution is an A2-strict and an A2-wide execution | `ReachN`, `HavocN`, `ExecN`, `CAliasN`; `ExecN.toExecS`, `ExecN.toExec`, `CAliasN.toCAliasS` | proved |
| CN with recency is sound under A2-narrow, for each `src`, each list of static roots, each K and both policies | `csoundCN`, `no_alias_of_mayProgCN` | proved |
| O equals the concept, and O is sound | `mayProgCNO_eq`, `csoundCNO` (§5.5) | proved |
| A computable executor for A2-narrow witnesses | `runAliasBN`, `runAliasBN_sound` (Run.lean) | proved |
| Both cases of HavocNeed answer true, and both aliases are real | `need_answersCN`, `strong_after_call_realN`, `empty_cell_realN` | proved |
| On `pHv`, the spread is gone: `a ~ b`, `a ~ z.f`, `a ~ w.g` are false, and `a ~ x.f` stays true | `spread_goneCN`, `spread_ab_noneN`, `spread_axf_keepN` | proved |
| The dead-end case answers `b ~ d` true, and the alias is real | `dead_answerCN`, `dead_realN` | proved |
| Gain of narrow reach: in `t = this.box; u = t.value; touch(); t.value = z`, `touch()` does not reach `this`, so `⟨this⟩` is not exposed and the store stays strong (with generous reach, the call would expose `⟨this⟩`), so `t.value ~ u` is false. It is true (weak store) with `touch(this)` or with `this` as a static root. An unrelated static root does not change the answer. The false answer is exact. | `gain_answersCN`, `gain_noneN` | proved |
| The three accepted losses: CN answers true, the per-cell analysis answers false, and no A2-narrow execution has the alias | `losses_CN`, `losses_HR`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN` | proved |
| The join example, the field example, the strong-update example, the call example and `loop_bf_x` keep their answers | `other_answersCN`, `loop_bf_x_CN` | proved |
| O gives the concept answers on the gain, loss and dead-end examples | `o_answersCN` | proved |
| "CN is at least as precise as per-cell havoc" | `precision_order_fails`, `nest_noneN` | false |
| The order holds on each example query | `precision_need`, `precision_old`, `precision_new` | proved |
| Both scope restrictions are necessary | `generous_reach_breaks_CN`, `touch_noneN`, `generous_havoc_breaks_CN` (§3.1) | proved |
| The narrow per-cell reference `mayProgHRN` (Reference.lean) is sound | none | open (F11; model only, not needed by the engine) |
| A cost bound for the O call | none | open (F10) |
| Completeness for calls under A2-narrow | none; the three losses bound the scope | open (F6) |

Accepted precision losses. A cell name stands for the entry object of the cell and for each object that a callee writes into the cell. So CN cannot tell these objects apart. The user accepted the three losses (D2):

| Id | Program | Query | CN | Per-cell havoc | Concrete fact | Cause |
|---|---|---|---|---|---|---|
| L1 | `t = x.f; u = t.g; m(x); t.g = z` | `t.g ~ u` | true: `⟨x.f⟩` is below the exposed `⟨x⟩`, so `t.g = z` is weak | false | `t` holds one object, so the store is strong in each execution (`loss1_noneN`) | the old object and the new object of `m` have one name |
| L2 | `w = x.f; x.f = b; m(x); t = x.f` | `t ~ w` | true | false | `t` is `b` or a new object; never the old object in `w` (`loss2_noneN`) | the name of the new object is the entry content of `x.f` |
| L3 | `x.f = b1; m(x); a = x.f; x.f = b2; m(x); c = x.f` (two call sites; 9 and 8 in Lean) | `a ~ c` | true | false | the two calls write two different new objects (`loss3_noneN`) | the objects of two calls in one cell have one name |

`losses_CN` gives the CN answers (K = 0 and 1). `losses_HR` gives the answers of the proved per-cell analysis `mayProgHR` (generous reach), and `precision_new` gives those of the narrow reference.

Measurement status. The engine does not implement per-cell havoc. So the three losses and the opposite case (`precision_order_fails`, below) are known only from the Lean examples: `losses_CN`, `losses_HR`, `precision_new`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN` and `nest_noneN`. The engine does not measure them on real code. The shadow runs measure the alias answer volume and the call cost of CN (§11.2), not the losses.

Comparison with per-cell havoc. The two rules are incomparable. Per-cell havoc is more precise on L1-L3. CN is more precise where per-cell havoc merges the objects of two holders that are callee objects of one call: `m(x, y)@9; m'(x, y)@8; t = x.f; a = t.g; u = y.f; b = u.g`, query `a ~ b`. The second call writes into `x.f.g` and into `y.f.g` two objects with the one origin `hsym 8 (havoc 9) g []`, because the key of a callee holder is only its call site. So per-cell havoc answers true (both `mayProgHRN` and `mayProgHR`). CN answers false (the names `⟨x.f.g⟩` and `⟨y.f.g⟩`), and no A2-narrow execution has the alias (`precision_order_fails`, `nest_noneN`). On each example query, each true answer of the narrow reference is also a true answer of CN (`precision_need`, `precision_old`, `precision_new`).

Requirements for the engine. The proof depends on these rules (§7.6):

1. The exposed set takes part in each join (union) and in the loop test. In the model, `xe` is in `ctx.vars`, so `leOn` tests it. If the loop test ignores it, a loop can stop before `exposed` is stable.
2. `top` exposes each universe origin.
3. If the closure does not converge, cover each origin and expose each universe origin.
4. Coverage includes the descendants (step 2 of the closure).

---

## 5. Optimization O

### 5.1 Idea

O shares origin sets in the way that congruence closure shares classes, but it keeps the direction. Congruence closure keeps a congruence. O keeps a directed congruence: the congruent order `⊒` of §1.7.

| Congruence closure (DSU) | O |
|---|---|
| The relation is a congruence: symmetric, transitive, closed under fields. | The relation is a congruent order: transitive, monotone under fields (`path_mono`), antisymmetric on nodes (`node_antisymm`). |
| A node is an equivalence class. | A node is a canonical origin set. |
| A union merges two classes in place. The operands are lost. | A union makes a **new** node. Its two children are the operands. The operands stay. |
| Holders in one class are one holder. | Each holder points to its own node. Holders never merge. |
| Congruence: the work on a class is shared by all its members. | O shares **sets** (hash-consing), but not **loads**. A load through a node is a memoized union over the cells of its member origins. It does not reuse the loads of the two children of the node. |
| State equality is partition equality. | State equality is node-id equality. |

DAG view: an edge `u -> v` means `L(u) ⊇ L(v)`, that is `u ⊒ v` (§1.7). The DAG edges are the stored edges of the order, in the role of Hasse edges: O stores only these edges, and each path of edges is a pair of the order (`Tbl.kids_den`, `above_trans`). A union node keeps its two children, so a union adds two order edges and removes none. The DAG does not hold each pair of the order: two nodes can be ordered with no path of edges between them (argued; for example, the node of `union({o1}, {o2, o3})` is above a node `{o1, o2}` of the table, but no path of edges connects them). The denotation of a node is the set of leaves below it (`Tbl.mem_iff_leaf`).

### 5.2 Nodes and table (Opt/Table.lean)

| Item | Definition |
|---|---|
| Universe `U` | `ctx.origins` (from `originsOf`). |
| Canonical form | `canon U S = U.filter (· ∈ S)`: the members in universe order (a bit-vector view). |
| Node | `{set, kids : Option (Nat × Nat)}`. A union miss records its two children. An intern records a leaf. |
| Table | `{nodes, memo, work}`. The node id is the index. The memo key `mkey a b` puts the smaller id first. `work` counts cost. |
| `intern U T S kids` | Find the canonical form of `S`, or add it. Cost `\|S\| + 1`. |
| `union U T a b` | If `a = b`: `a` (cost 1). Memo hit: the memo id (cost 1). Else merge, intern with kids `(a, b)`, add a memo entry (cost `1 + \|A\| + \|B\| + \|A ∪ B\| + 1`). |
| Invariant `Tbl.Good` | Sets are canonical. No two nodes have one set. Children have smaller ids, and the parent set is the union of the child sets. Each memo entry is the union of its key nodes. |

| Theorem | Statement |
|---|---|
| `Tbl.id_inj`, `Tbl.id_eq_iff` | In a good table, two valid ids are equal if and only if their members are set-equal. So the fixpoint test is an id test. |
| `Tbl.intern_spec`, `Tbl.union_spec` | Intern and union keep the table good and give the correct members. |
| `Tbl.union_hit` | A memo hit adds no node and costs one unit. |
| `Tbl.union_again` | Each pair is merged at most one time in one analysis. |
| `Tbl.kids_den` | A union node has the union of the members of its children. |
| `Tbl.mem_iff_leaf` | An origin is in node `i` if and only if it is in a leaf below `i`. |
| `canon_eq_of_setEq`, `canon_setEq` | Set-equal sets give one canonical form. |

### 5.3 State and operations (Opt/Prim.lean, Opt/Machine.lean)

State: `OState = List (Key × NodeId)` with `Key = v x | h o c`. A missing key has its default content: null for a variable, `adefault K o c` for a cell. The denotation `den K T st` is the C state.

| C operation | O operation | Table work |
|---|---|---|
| `x := y` | `copyO`: share the node id of `y` (erase `x` if `y` is null) | none |
| `x := new s`, `unknown`, call result | `setKey`: intern a set of one origin | one intern |
| `x := null` | `oerase` | none |
| `x := y.c` | `loadO`: memoized union over cells `c` of the members of the node of `y` | one union for each member |
| `x.c := y` | `storeO`: `single?` on the members of the node of `x`, and the `uniqueB` test with `ctx.entryUnique`. Strong: set `(o, c)` to the node of `y`. Weak: `addAll`. | one union for each member (weak) |
| `x[*] := y` | `weakO` | one union for each member |
| call havoc | `havocO` (site havoc): `reachB` on the denotation, then add the node `{havoc(s)}` to each reachable universe cell. `havocHO` (per-cell havoc): the same reach test, then add the interned node `{havocC(s, keyOf(o), c, [])}` to each reachable universe cell `(o, c)` (`addHv`). `havocCNO` (CN, the default): `closeN` on the denotation, then one `addSets`: the exposed key gets the closure, and each universe cell of each covered origin gets its cell name. | one union for each cell |
| join | `joinO`: one memoized union for each key of either map. The change bit is true if some id differs from the first state. | one union for each key |
| top | `topO` | one union for each key |
| loop | `loopO`: the same fuel and checked post-fixpoint. The test is the change bit. | one join for each iteration |
| may | `omay`: `oevalPath`, then `meetB` of the two member lists | unions along the path |
| retire (recency) | `retireO`: §5.5 | §5.5 |

### 5.4 Field example in O (DAG view)

After `a.f = z`. The ids are examples. `n5` and `n7` are default contents. O adds a default node to the table only when a statement reads that cell.

```
 env:   x→n1   y→n2   a→n3   z→n4
 heap:  (ox,f)→n6   (oy,f)→n8

 n3 {ox,oy}    ──► n1 {ox}
               └─► n2 {oy}
 n6 {oz,ox.f}  ──► n4 {oz}
               └─► n5 {ox.f}
 n8 {oz,oy.f}  ──► n4 {oz}
               └─► n7 {oy.f}
```

The kid edges of O are the arrows of the task: `a -> x` is the edge `n3 → n1`, that is `n3 ⊒ n1`.

After `a = w`, only the entry of `a` changes. `n3` stays in the table, but no holder holds it:

```
 env:   x→n1   y→n2   a→n9 {ow}   z→n4
 heap:  (ox,f)→n6   (oy,f)→n8
```

`x` and `y` hold different leaf nodes with disjoint members: no alias. `(ox, f)` and `(oy, f)` both reach leaf `n4`: both alias `z`. Proved: `o_field` (Opt/Examples.lean). For the query layer, `field_findAlias_z` (Opt/QueryFam.lean) gives `alias(z) = {x.f, y.f}`.

### 5.5 Equivalence O ≡ C

Relation: `Rel ctx T st X = EntOK ∧ Agree ∧ Supp ctx X`. `Agree`: on each universe key, the members of the O node and the C value are set-equal. `Supp` (Opt/Support.lean): the C state keeps all universe keys inside the universe origins.

Without recency:

| Theorem | Statement | File |
|---|---|---|
| `setKey_rel`, `copyO_rel`, `nullO_rel`, `loadO_rel`, `weakO_rel`, `storeO_rel`, `callO_rel`, `ostep_rel` | Each statement keeps `Rel`. The table stays good and grows. | Opt/Machine.lean |
| `reachB_congr` | The call reach test is the same on agreeing states. | Opt/Machine.lean |
| `joinO_rel`, `joinO_flag` | The O join represents the C join. The change bit is `!(leOn ctx (f Y) Y)`. | Opt/Equiv.lean |
| `topO_rel`, `loopO_rel`, `analyzeO_rel`, `initO_rel` | Top, loop, analysis and entry state. | Opt/Equiv.lean |
| `oevalPath_spec`, `omay_eq` | Path evaluation and may-alias agree. | Opt/Equiv.lean |
| `analyzeProgO_rel`, `mayProgO_eq` | For each program, the final O state represents the final C state, and `mayProgO = mayProg`. | Opt/Equiv.lean |
| `analyzeProgOE_rel`, `mayProgOE_eq` | The same for both strong-update policies. | Opt/Equiv.lean |

O soundness without recency is a composition: `csoundE` and `mayProgOE_eq`. The two `mayProgE` definitions (`Sound.mayProgE`, `Opt.mayProgE`) are equal by unfolding. For this configuration, no single theorem states "a one-execution alias is an O may-alias" (F9). For the default configuration (recency with CN), `csoundCNO` states it (below). For recency with per-cell havoc, `csoundHRO` states it.

With recency (Opt/Recency.lean). The O retire `retireO ctx s T st` has two steps:

1. `mergeCells`: for each universe cell `c`, the key `(alloc-old(s), c)` gets the memoized union of the nodes of `(alloc-new(s), c)` and `(alloc-old(s), c)`. The key `(alloc-new(s), c)` is removed; its default content is null. The step reads the input map and writes a second map, so the order of the cells has no effect.
2. `renameKeys`: each key whose node holds `alloc-new(s)` gets the interned node of the renamed set. Other keys keep their node ids. A default content has no allocation origin (`renameL_dflt`), so keys without an entry need no work.

`analyzeRO` is `analyzeO` with four changes:

1. `new` retires, then sets `{alloc-new(s)}`.
2. `unknown` retires, then sets the fresh origin.
3. A call does the havoc, retires, then sets the fresh result.
4. A store uses `storeRO` (the `uniqueR` test).

Joins and loops do not change.

| Theorem | Statement | File |
|---|---|---|
| `retireO_skip` | If the universe does not have `alloc-new(s)`, the retire changes nothing. | Opt/Recency.lean |
| `mergeCells_spec`, `renameKeys_spec` | The values after each step of the O retire. | Opt/Recency.lean |
| `retireO_rel` | The O retire represents `retire s`. | Opt/Recency.lean |
| `storeRO_rel` | The O recency store represents `storeR`. | Opt/Recency.lean |
| `ostepR_rel`, `analyzeRO_rel` | Each statement, and the whole analysis, represent the recency concept on the universe. | Opt/Recency.lean |
| `analyzeProgRO_rel`, `mayProgRO_eq` | For both policies and each program, `mayProgRO eu = mayProgR eu`. | Opt/Recency.lean |
| `retireO_work` | One retire costs at most `\|cells\|·(6 + 4\|U\|)` for the merge of the cells, plus `\|U\| + 1` for each key whose node holds `alloc-new(s)` after step 1. The model does not charge the scan for holders (it models a reverse index). | Opt/Recency.lean |
| `o_loop_bf_x`, `o_loop_bf_y`, `o_loop_bf_x_weak`, `o_field` | CX7 is exact in O with recency (both policies). The field example keeps its answers. | Opt/Recency.lean (namespace `RExamples`) |

Cost notes for `retireO_work`:

- Step 2 costs nothing for a key that does not hold `alloc-new(s)`. This models a reverse index from an origin to the keys that hold it. With such an index, step 2 visits only the holders of `alloc-new(s)`. Without it, step 2 also tests each map entry (one unit for each entry).
- Step 1 touches only the cells of `alloc-new(s)` and `alloc-old(s)`. A heap map grouped by origin makes it proportional to the written cells of `alloc-new(s)`.
- The renamed node depends only on `(s, node id)`. A rename memo keyed by `(s, id)` stays valid across states, as the union memo does. The model does not include this memo.

With per-cell havoc (Opt/Havoc.lean, Opt/HavocRecency.lean). The O call `havocHO` (`havocHRO` with recency) adds, for each universe cell of each reachable universe origin, the interned singleton of its per-cell havoc origin by one memoized union. Copy, load, store, join, loop, top and queries are the O operations above. With recency, the O retire does not change: a per-cell havoc origin is never `alloc-new(s)`, so `retireO` never renames it.

| Theorem | Statement | File |
|---|---|---|
| `callHO_rel`, `ostepH_rel`, `analyzeHO_rel`, `analyzeProgHO_rel` | One call, one statement, the analysis and the final state of O represent the per-cell havoc concept on every universe key. | Opt/Havoc.lean |
| `mayProgHO_eq` | For both policies and each program, `mayProgHO eu = mayProgH eu` on the variables of the program and the frame. | Opt/Havoc.lean |
| `addHv_spec`, `addHv_work` | The per-cell havoc adds the correct origin to each listed key. One call over keys `ks` costs at most `\|ks\|·(6 + 4\|U\|)`. | Opt/Havoc.lean |
| `havocHRO_rel`, `ostepHR_rel`, `analyzeHRO_rel`, `analyzeProgHRO_rel` | The same with recency. `retireO_rel` is used without change. | Opt/HavocRecency.lean |
| `mayProgHRO_eq`, `csoundHRO` | For both policies, `mayProgHRO eu = mayProgHR eu`. So O with recency and per-cell havoc is sound under A2-strict. | Opt/HavocRecency.lean |
| `addSets_work` | One per-cell havoc with recency has the same cost bound as `addHv_work`. | Opt/HavocRecency.lean |

Cost note. Site havoc adds one node `{havoc(s)}` to all cells, so equal unions give memo hits. Per-cell havoc interns up to `\|ks\|` new singleton nodes and up to `\|ks\|` new union nodes for each call. This is the cost that made the user replace per-cell havoc by CN (§4.11).

With CN (Opt/CellNamed.lean). The O state is the map of Opt/Prim.lean. The exposed set is the node of one reserved variable key `.v xe`, so the O join, the change bit, the loop test and `retireO` apply to it without change. The O call `havocCNO` has four steps: `closeN` on the denotation of the state; one `addSets` (the reserved key gets the closure, and each universe cell of each covered origin gets the interned singleton of its cell name, by one memoized union); `retireO`; the result. A cell name depends only on `(o, c)`, so the second call on the same cell gives a memo hit, and the values do not grow with the number of calls (argued). The O store is the O recency store with `uniqueCN` on the node of the reserved key (`storeCNO`).

| Theorem | Statement | File |
|---|---|---|
| `havocCNO_rel`, `storeCNO_rel`, `ostepCN_rel` | The O call, the O store and each O statement represent the CN concept on every universe key. | Opt/CellNamed.lean |
| `analyzeCNO_rel`, `analyzeProgCNO_rel` | The analysis and the final O state represent the CN concept. | Opt/CellNamed.lean |
| `mayProgCNO_eq` | For both policies, each list of static roots and each program, `mayProgCNO = mayProgCN` on the variables of the program and the frame. | Opt/CellNamed.lean |
| `csoundCNO` | O with CN is sound under A2-narrow. | Opt/CellNamed.lean |
| `o_answersCN` | O gives the concept answers on the gain, loss and dead-end examples. | Opt/CellNamed.lean |

No theorem bounds the cost of the O call of CN. An analogue of `addSets_work` is not stated (F10). The engine cost of §7.6 is argued.

Limits of the equivalence:

- It holds on the universe only. `mayProgO_eq`, `mayProgRO_eq`, `mayProgHO_eq`, `mayProgHRO_eq` and `mayProgCNO_eq` need `x, y ∈ p.vars ++ fr.vars`. Outside, C can differ only after a loop ran out of fuel (`top`) (argued). All queries are on such variables.
- O does not remove a cell entry whose node equals the default content. This has no effect on the equivalence and on the bounds. The Kotlin state must remove such entries (§7.10).
- Not in the O model: the engine form of the CN call of §7.6 (the closure over written cells only, the filtered exposed node with its markers, the explicit cells of covered allocations), the iteration strategy of §7.10, exceptional edges.

### 5.6 Cost separations

Cost models: C uses explicit sets with the sorted-merge cost `|A| + |B|` for each union or inclusion test. This is the cheapest list model for C. O counts the table `work`. Map lookups are free in the model.

| Separation | Family | C cost (lower bound) | O cost (upper bound) | Theorem (file) |
|---|---|---|---|---|
| State size | `fam n m`: `a := new 0 \| ... \| new m`, then `b := a` for `b = 1..n` | `(n+1)(m+1)` set elements | `(n+1) + (m+1)` map entries. The shared table of the same family has Θ(m²) elements (`chain_table`, Opt/Findings.lean). | `fam_csize`, `fam_osize` (Opt/Cost.lean) |
| Loop test and join | `loopFam n m`: `fam n m`, then `loop { t := 0 }` | `(n+1)(m+1)` | `20(n+m+3) + 4(6 + 4(m+1))`. Both bounds count the loop only (tests and joins), not the prefix `fam n m`. | `loopFam_sep` (Opt/LoopCost.lean) |
| Query | `qfam n`: `i := new i` for `i = 0..n`, query fields `0..c-1`, query `findAlias(0)` | enumeration `≥ (n+1)(c+1)^D` | search `≤ (n+1)((D+2)(c+2)+D)` | `qfam_sep` (Opt/QueryFam.lean) |

The table has two concept/optimization pairs. C/O is the pair for the state (rows 1 and 2). Enumeration/search is the pair for the query (row 3). The search also runs on C states.

Supporting bounds: `osize_le_ukeys` (Opt/Cost.lean: one entry for each universe key), `joinO_work` (at most 5 for each key with set-equal values, at most `6 + 4|U|` for other keys), `loop_copy_work`, `loopCost_ge` (Opt/LoopCost.lean).

Computed numbers:

| Input | C | O |
|---|---|---|
| `fam 8 8`, state size | `csize = 81` | `osize = 9`, table `tsize = 70` |
| `loopFam (4,4)`, loop cost | 170 | 35 |
| `loopFam (8,8)` | 522 | 59 |
| `loopFam (12,12)` | 1066 | 83 |
| `loopFam (16,16)` | 1802 | 107 |

Practical scope (argued). The families are synthetic. They model two real shapes: a value with m allocation origins that flows into n holders (a join before a loop), and a query over a heap with c fields. The separations matter for real methods only where these shapes are frequent. L4 measures the same counters (`contentSize`, `memoMisses`, `queryNodes`) on tms and Conductor, and compares them with the bounds (§11.2).

### 5.7 False and limited claims

| Claim | Status | Evidence | Meaning for the implementation |
|---|---|---|---|
| "O space is `c·(n+m)`" with the table counted | false | `chain_table`: 17 allocations give 33 nodes with 169 set elements. Computed for 5, 9, 13, 17, 21 allocations: content 19, 53, 103, 169, 251; nodes 9, 17, 25, 33, 41. | The map part is linear. The table content can grow as `m²/2` on a join chain. The node count is linear (`2m + 1`). Store nodes compactly. Cap the content (§7.14). |
| "The O fixpoint test is one id comparison for each key" | false | `test_miss`: `a := new0 \| new2; b := new1; loop { b := a }` adds a memo entry in the test iteration. | A strict-subset body result with a new id costs one merge, the same order as C. It is never worse than C (argued). The memo does not help while the loop state still grows. |
| The state-size separation does not depend on the C representation | limited | argued | A C with shared immutable lists also shares on a copy. The separations that do not depend on the representation are the loop test and join (`loopFam_sep`) and the query (`qfam_sep`). |
| An eager reverse index is cheap | false on small programs | computed: field example, D = 2: 71 index edges, search cost 412, enumeration 35 | The separation is asymptotic in D and the number of cells. Build the reverse index lazily (§6.4). |
| O ≡ C everywhere | limited | `mayProgO_eq` hypothesis | Only universe keys and program or frame variables. All queries need only these. |

### 5.8 Cost relative to the DSU

All proved separations compare O with C. No theorem compares O with the DSU. This table gives the cost of each operation (argued, except the cited theorems). `|p|` is the size of a points-to set. α is the inverse Ackermann function.

| Operation | DSU | O | O worst case |
|---|---|---|---|
| copy `x = y` | one union, O(α) | share the node id, O(1) | O(1) |
| load `x = y.f` | one union with one heap element | one memo union for each member of `pts(y)`: O(`\|pts(y)\|`) memo operations | a memo miss merges two sets (`Tbl.union_work`) |
| store `x.f = y` | removal and union | strong: O(1). Weak: one memo union for each member of `pts(x)` | as load |
| unresolved call | `invalidateOuterHeapAliases`: remove the heap elements of outer groups | CN: the closure over the written cells of the covered origins, then one memo union for each written cell of a covered origin and for each cell of a covered allocation, then one union for the exposed key (§7.6) | the closure visits each written cell of a covered origin (no theorem, F10) |
| join | union of the parent relations, then congruence repair until stable | one memo union for each key (`joinO_work`) | `6 + 4\|U\|` for each key with different values |
| fixpoint test | partition equality | the change bit, one id comparison for each key | a memo miss (`test_miss`) |
| query | enumerate the group, then convert paths up to depth D | backward search, bounded by the output (`searchCost_le`) | `\|cells\|^D` output on cyclic heaps (§6.2) |
| table content | linear | Θ(m²) on a join chain (`chain_table`) | capped (`maxTableContent`, §7.14) |

Practical condition (argued). If each points-to set has at most `c` origins, each statement costs O(`c`) memo operations, and a join costs one memo operation for each key. Then O is in the same order as the DSU for each statement. L4 measures `|pts|` and the memo counters (§11.2).

---

## 6. Query layer

### 6.1 Query semantics

| Query | Meaning in C |
|---|---|
| `findAlias(x, P)` | `{ (v, π) : v a holder variable, \|π\| ≤ D, may(v.π, x) at P }` (the enumeration `enumAlias`). The Lean result contains `(x, [])`. The API answer `alias(x)` does not contain it (CK4, §8.1). |
| `forEachHeapAlias(x, π, P)` | For each prefix `pre` of `π`: the paths that may alias `x.pre` (`heapAliases`). |
| `AliasAllocInfo(s)` in `alias(x)` | `alloc(s) ∈ pts(x)`. With recency: `alloc-new(s) ∈ pts(x)` or `alloc-old(s) ∈ pts(x)`. Never inside a heap path. |

Query for a heap path `x.π`. The seed is `T = aevalPath(x, π)`: read the cells of `π` from `pts(x)`, with default content for unwritten cells. Then run the same backward search from `T` (`heapAliases_iff`). Rules:

- The answer is every path `v.ρ` (`|ρ| ≤ D`) with `pts(v.ρ) ∩ T ≠ ∅`, except `x.π` itself. The query path `π` can be longer than D. The answer paths cannot.
- The answer cannot be derived from `findAlias(x)`. Congruence gives `v.π` for each `v` that shares an origin with `x`, if the cell is not empty. But a path can also reach the content of the cell by a write: after `x.f = z`, `z ~ x.f`, and `z` is not an alias of `x` (`field_heapAliases_x`).
- If `T` is empty (`x.π` is always null), the answer is empty.
- If `π` passes depth K, `T` holds `deep(b)`. Its holders are the variables that hold it and the symbolic parents at depth K. The search does not follow its self cells (§6.2). So the answer is the paths that may reach the deep summary, not all paths over all cells.
- An unwritten cell on `π` gives a default origin, for example `⟨x.f.g⟩`. The query computes it by rule and does not intern it (§7.12). Its holders are the default parent cell and the variables that loaded it.
- After a strong update of `x.f`, the old holders of the cell content are no longer in the answer.

`AliasAllocInfo` follows the points-to set of the queried local only, not "the allocations of a group". This fixes the transitive answer for `JIRCallResolver` (CK5). A symbolic, deep, allocation child or catch origin in `pts(x)` means "an object that is not a local allocation". §8.2 (M6) uses it as an "unknown origin present" signal.

### 6.2 Backward search (Opt/Query.lean)

| Item | Definition |
|---|---|
| Reverse heap index `hidx` | Each edge `(o', c, o)` with `o ∈ H(o', c)`, over the universe. |
| Reverse variable index `vidx` | Each pair `(v, o)` with `o ∈ pts(v)`. |
| Preimage `pre c G` | `{ o' : H(o', c) ∩ G ≠ ∅ }`. |
| Holders `holders G` | `{ v : pts(v) ∩ G ≠ ∅ }`. |
| Liveness `live j` | The origins that some variable reaches with a path of length at most `j`. |
| `search j σ G` | Output `(v, σ)` for each holder of `G`. For each cell `c`: if `pre c G` meets `live (j-1)`, recurse on `c :: σ` with `pre c G`. |
| `findAlias D x` | `search D [] pts(x)`. |

The search starts at the target and walks the heap backward. It expands a child only if some variable can still reach it within the remaining depth. So each expanded node leads to output.

Deep self edges. `deep(b)` holds itself in each cell (`adefault`, Concept.lean). After a list walk longer than K, a variable holds `deep(b)`. A search through these self edges reports each path over each cell up to D: `|cells|^D` answers, and most of them are false aliases. The DSU gives only the accessed chain. Rule: the backward search never expands a self edge of a deep origin. The heap holders of `deep(b)` are then the variables that hold it and the symbolic parents `sym(b, q)` with `|q| = K`. With K ≥ D + 1 (§6.4), no path from a root of length at most D reaches a deep origin. This rule removes reported paths only through deep origins (argued; F7).

Cost of K for list walks (argued). A loop that walks `w` fields from one base reaches up to `Σ_{i≤K} w^i` symbolic origins (K = 7: 255 for w = 2, 21 845 for w = 4). Each node set can hold them. This is the worst case. Real loops walk one or two fields. L4 measures `nodeCount` and `contentSize`.

### 6.3 Theorems

| Theorem | Statement | File |
|---|---|---|
| `search_mem` | The search below suffix `σ` gives exactly the paths `ρ ++ σ` (`\|ρ\| ≤ j`) from a variable that reaches a seed. | Opt/Query.lean |
| `findAlias_iff` | `findAlias` by search has the same members as `findAlias` by enumeration. | Opt/Query.lean |
| `search_nodup`, `findAlias_nodup` | Each path occurs one time. No deduplication pass is necessary. | Opt/Query.lean |
| `progCtx_vars_nodup`, `progCtx_cells_nodup` | The program context lists have no duplicates. | Opt/QueryFam.lean |
| `search_nodes` | The search expands at most `1 + (D+1)·\|output\|` nodes. | Opt/Query.lean |
| `searchCost_le` | Cost at most `(1 + (D+1)\|output\|)(I + \|cells\|·\|U\|) + D·I`, with `I` the index size. | Opt/Query.lean |
| `heapAliases_iff` | `forEachHeapAlias(x, π)` is the same search seeded by `aevalPath x pre` for each prefix. Its result is exactly the paths that may alias `x.pre`. | Opt/Query.lean |
| `findAliasO_iff` | The search on the denotation of the O state gives exactly the C enumeration on the C state. | Opt/QueryFam.lean |
| `field_findAlias_z` | Field example: `alias(z) = {x.f, y.f}` (the Lean result also has `z`). | Opt/QueryFam.lean |
| `field_heapAliases_x` | Field example: `forEachHeapAlias(x, [f])` gives `{x}` for `[]` and `{z, x.f, y.f}` for `[f]`. | Opt/QueryFam.lean |

The Lean search has no deep-self-edge rule. The rule of §6.2 is a Kotlin restriction of `search` (F7).

### 6.4 Recommendations

| Topic | Recommendation | Basis |
|---|---|---|
| Index | Build the reverse heap index lazily from the **written** heap entries. Compute default edges by rule (§7.12). | §5.7 eager index cost |
| Liveness | Compute the liveness layers forward from the live variables, up to depth D. | `search_nodes` |
| Depths | D = 6 accessors (main: `HEAP_CHAIN_LIMIT = 5`, counted from 0). K = D + 1 = 7. D is also the main knob of the alias answer volume (R0, D11 (b)). | CK3, D4, §6.2 |
| Deep self edges | Never expand them. | §6.2 |
| Sub-search cache (optional) | A cache keyed by (seed node id, suffix, remaining depth) can share work between queries at one point. The key must include the depth. | the cache defect of main (§8.5) |
| Determinism | The search is a pure function of (state, `x`, D). Answers do not depend on query order or threads. | definition of `search` |
| `forEachHeapAlias` | One search for each prefix of the fact path. | `heapAliases_iff` |
| Roots | Arguments and `this` are holder variables that never change. A static field is a cell of a static root origin. | argued |

---

## 7. Architecture

### 7.1 Packages and entities

| Package (module) | Entity | Role |
|---|---|---|
| `org.opentaint.dataflow.ap.ifds.analysis.alias` (`opentaint-dataflow`, shared with Go) | `LocalAliasAnalysis`, `AliasUtil.kt` (no change, D6) | The DSU base. Go and the JVM DSU backend use it. The directed backend and the facade do not extend it (§8.3). |
| `org.opentaint.dataflow.graph` (`opentaint-dataflow`) | `CompactGraphTopSort.weakTopologicalOrder`, `CompactGraphTopSort.onCycle` (new public functions) | The WTO of a graph (null for an irreducible graph), and the nodes on a cycle |
| same | `simulateGraphWto` (new) | Recursive WTO iteration with an accumulating join and a change bit at loop heads (§7.10) |
| `org.opentaint.dataflow.jvm.ap.ifds` (`opentaint-jvm-dataflow`) | `JIRLocalAliasAnalysis` (changed: facade, no shared base class) | Same constructor, same public queries. It selects a backend by `Params.aliasAnalysisMode` (D7). In mode `SHADOW` it runs both backends, returns the DSU answer, and records both answers in `AliasShadowStats`. |
| same | `AliasVolumeStats` (new, P0c), `AliasShadowStats` (new, P9a) | Volume counters for each query, method and project (DSU path and directed path); the per-query comparison of shadow mode (§10.2, §11.3) |
| `org.opentaint.dataflow.jvm.ap.ifds.analysis` | `JIRAliasUtil.kt` (changed) | The copies of the shared receiver helpers, with the facade as receiver (M3, §8.3) |
| `org.opentaint.dataflow.jvm.ap.ifds.alias` | `JIRDsuAliasBackend` (the body of `JIRLocalAliasAnalysis` on main, renamed) | The DSU backend. It extends `LocalAliasAnalysis`, as on main. Its behaviour does not change. |
| `org.opentaint.dataflow.jvm.ap.ifds.alias.directed` (new) | `NodeTable` | Interned origin sets (nodes), union memo |
| same | `OriginTable`, `BaseTable`, `SiteTable`, `CellTable`, `VarTable` | Dense `Int` ids for origins, bases, sites, cells and variables |
| same | `DirectedState` | State for each statement: environment map (with the exposed key), heap map |
| same | `DirectedTransfer` | The operations of O (copy, allocate, load, store, the call rule, retire, join, garbage collection) |
| same | `DirectedAliasAnalysis` | JIR driver: maps `Stmt` (from `JIRDSUAABuilder`) to `DirectedTransfer` operations; inlining |
| same | `DirectedAliasResult` | Frozen tables and the states of each statement after the fixpoint |
| same | `DirectedAliasQuery`, `ReverseIndex` | Lazy reverse index, backward search, conversion to `AliasInfo` |
| same | `JIRDirectedAliasBackend` | Implements the facade queries on `DirectedAliasResult`. It has no shared base class. |

The directed engine is in the JVM module. It does not change shared behaviour. The shared alias classes do not change (D6, decided by the user). The only shared-code changes are two additive graph functions and two additive counters in the conversion cache of `LocalAliasAnalysis` (P0c: cut conversions and hits of cut lists, §8.5). The counters do not change answers. They are an exception to "the shared alias code does not change" (D6), and the user approved them (2026-10-29). The DSU cache is not fixed (D13). Go code does not call the graph functions and does not read the counters, so Go behaviour stays the same.

The engine core (`NodeTable`, `OriginTable`, `DirectedState`, `DirectedTransfer`, the simulator) does not depend on JIR. A test driver (`MiniDriver`, in test sources) runs it on the Lean IR. Thus the Lean vectors and the naive oracle test the code that production uses (§10).

### 7.2 Interaction

```
JIR method ──MethodInstGraph──► JIRInstGraph ──evalInst (JIRDSUAABuilder)──► Stmt
Stmt ──DirectedAliasAnalysis──► DirectedTransfer ops ──simulateGraphWto──► DirectedState[] (before, after)
DirectedState[] + tables ──freeze──► DirectedAliasResult
consumer ──JIRLocalAliasAnalysis.findAlias──► JIRDirectedAliasBackend ──DirectedAliasQuery──► List<AliasInfo>
```

### 7.3 Kotlin signatures

The project owner does not allow `@JvmInline value class` for packed types, and does not allow comments in production code. No repository file states these rules. So packed types use `typealias` and inline functions, and this document records the reasons for the code.

```kotlin
typealias NodeId = Int
typealias OriginId = Int
typealias BaseId = Int
typealias SiteId = Int
typealias CellId = Int
typealias VarId = Int
typealias HeapKey = Long
typealias PairKey = Long

const val EMPTY_NODE: NodeId = 0
const val ABSENT: Int = -1
const val ELEM_CELL: CellId = 0
const val EXPOSED_VAR: VarId = 0

inline fun heapKey(origin: OriginId, cell: CellId): HeapKey =
    (origin.toLong() shl 32) or (cell.toLong() and 0xFFFF_FFFFL)

inline fun heapKeyOrigin(key: HeapKey): OriginId = (key ushr 32).toInt()

inline fun heapKeyCell(key: HeapKey): CellId = key.toInt()

inline fun pairKey(a: NodeId, b: NodeId): PairKey =
    if (a <= b) (a.toLong() shl 32) or b.toLong() else (b.toLong() shl 32) or a.toLong()
```

Node table:

```kotlin
class NodeTable {
    val nodeCount: Int
    val contentSize: Long
    val memoHits: Long
    val memoMisses: Long

    fun members(node: NodeId): IntArray
    fun size(node: NodeId): Int
    fun contains(node: NodeId, origin: OriginId): Boolean
    fun meets(a: NodeId, b: NodeId): Boolean
    fun singleton(origin: OriginId): NodeId
    fun intern(sortedOrigins: IntArray): NodeId
    fun union(a: NodeId, b: NodeId): NodeId
    fun unionUncached(a: IntArray, b: IntArray): IntArray
    fun rename(node: NodeId, from: OriginId, to: OriginId): NodeId
    fun freeze()
}
```

Origins and bases. `SiteTable`, `CellTable` and `VarTable` give dense ids in the same way. `SiteTable.isLoopSite(site)` is the loop test of §7.5:

```kotlin
enum class OriginKind { SYM, DEEP, ALLOC, ALLOC_NEW, ALLOC_OLD, BOX_CONST, CLASS_CONST, STRING_CONST, SITE_CONST, EXPOSED_STATICS, EXPOSED_ALL }

enum class BaseKind { ROOT_THIS, ROOT_ARG, ROOT_STATIC, FRESH, ALLOC_CHILD }

class BaseTable {
    fun thisBase(): BaseId
    fun argBase(index: Int): BaseId
    fun staticBase(binaryClassName: String): BaseId
    fun freshBase(site: SiteId): BaseId
    fun allocChildBase(site: SiteId): BaseId
    fun kind(base: BaseId): BaseKind
    fun freeze()
}

class OriginTable(val symDepth: Int, val bases: BaseTable) {
    fun kind(origin: OriginId): OriginKind
    fun isOuter(origin: OriginId): Boolean
    fun base(origin: OriginId): BaseId
    fun parent(origin: OriginId): OriginId
    fun symRoot(base: BaseId): OriginId
    fun symChild(parent: OriginId, cell: CellId): OriginId
    fun cellName(origin: OriginId, cell: CellId): OriginId
    fun alloc(site: SiteId, level: Int, kind: OriginKind): OriginId
    fun boxConst(boxType: String): OriginId
    fun classConst(binaryClassName: String): OriginId
    fun stringConst(value: String): OriginId
    fun siteConst(site: SiteId): OriginId
    fun exposedStatics(): OriginId
    fun exposedAll(): OriginId
    fun freeze()
}
```

Policy and parameters:

```kotlin
enum class AliasAnalysisMode { DSU, SHADOW, DIRECTED }

data class DirectedAliasPolicy(
    val entryUnique: Boolean = true,
    val recency: Boolean = true,
    val maxCallClosure: Int = 10_000,
    val symDepth: Int = 7,
    val maxAccessors: Int = 6,
    val maxTableContent: Long = 50_000_000L,
    val maxQueryPaths: Int = Int.MAX_VALUE,
    val diagnosticCallDrop: Boolean = false,
)

data class Params(
    val useAliasAnalysis: Boolean = true,
    val aliasAnalysisInterProcCallDepth: Int = 0,
    val aliasAnalysisTimeLimit: Duration = 10.seconds,
    val aliasAnalysisMode: AliasAnalysisMode = AliasAnalysisMode.DSU,
    val directedPolicy: DirectedAliasPolicy = DirectedAliasPolicy(),
)
```

Status of the defaults: `aliasAnalysisMode = DSU` (D7) and `entryUnique = true` (D1) are decided by the user. The call rule CN (D2) is decided by the user (2026-10-29). It is the only call rule, so the policy has no havoc mode field (§7.6). `maxCallClosure` (the closure budget of §7.6) is open until the measurement. `recency` (D3), `symDepth` and `maxAccessors` (D4), `maxQueryPaths` and `diagnosticCallDrop` (D11), and `maxTableContent` (§7.11) are open until the spec revisit. The defaults of the two D11 fields mean "no volume control" (D11 (a)).

Modes:

| Mode | Backends that run | Answers that the consumers get | Use |
|---|---|---|---|
| `DSU` | DSU | DSU | Default (D7). The DSU of main without change (D13). |
| `SHADOW` | DSU and directed | DSU | Measurement only: the volume gate (§11.2). Findings must equal the `DSU` findings. Time and memory are not budgets, because two engines run. |
| `DIRECTED` | directed | directed | Only after the shadow volume gate passes (§10.2). |

`maxQueryPaths` is D11 (c): a per-query budget of reported paths, shortest paths first, with a `truncated` counter. `diagnosticCallDrop` is D11 (e): the alias drop of main at unresolved calls, for an A/B diagnosis only. It is not a default, and D2 stands.

Volume statistics:

```kotlin
class AliasVolumeStats {
    val queries: Long
    val answerPaths: Long
    val accessorSum: Long
    val maxAnswerSize: Int
    val maxChainLength: Int
    val truncatedQueries: Long
    val cutConversions: Long
    val cutCacheHits: Long

    fun record(query: AliasQueryKind, answer: List<AliasInfo>?)
    fun addTo(total: AliasVolumeStats)
}

enum class AliasQueryKind { BEFORE, AFTER, ARRAY_ELEMENT, HEAP }

class AliasShadowStats {
    val dsu: AliasVolumeStats
    val directed: AliasVolumeStats
    val directedNotSubset: Long
    val dsuNotSubset: Long

    fun record(query: AliasQueryKind, method: JIRMethod, stmtIdx: Int, base: AccessPathBase.LocalVar, dsu: List<AliasInfo>?, directed: List<AliasInfo>?)
}
```

`accessorSum` is the sum of the accessor counts of the reported paths. `cutConversions` and `cutCacheHits` exist only on the DSU path (§8.5). `AliasQueryKind` tells the facade query: `BEFORE` is `findAlias` (CS1-CS3, CS6-CS8), `AFTER` is `findAliasAfterStatement` (CS4/CS5). One `AliasVolumeStats` exists for each method analysis, and one total for each project run. Both are logged at DEBUG; the project total is also logged at INFO at the end of the run.

State and transfer:

```kotlin
class DirectedState(
    val env: Int2IntOpenHashMap,
    val heap: Long2IntOpenHashMap,
) {
    override fun equals(other: Any?): Boolean
    override fun hashCode(): Int
}

class Joined<S>(val state: S, val changed: Boolean)

class DirectedTransfer(
    val nodes: NodeTable,
    val origins: OriginTable,
    val sites: SiteTable,
    val cells: CellTable,
    val vars: VarTable,
    val policy: DirectedAliasPolicy,
    val cancellation: AnalysisCancellation,
) {
    fun valueOf(s: DirectedState, v: VarId): NodeId
    fun read(s: DirectedState, origin: OriginId, cell: CellId): NodeId
    fun load(s: DirectedState, base: NodeId, cell: CellId): NodeId
    fun assign(s: DirectedState, target: VarId, value: NodeId): DirectedState
    fun allocate(s: DirectedState, target: VarId, site: SiteId, kind: OriginKind): DirectedState
    fun store(s: DirectedState, base: NodeId, cell: CellId, value: NodeId): DirectedState
    fun storeWeak(s: DirectedState, base: NodeId, cell: CellId, value: NodeId): DirectedState
    fun exposed(s: DirectedState): NodeId
    fun havoc(s: DirectedState, reachRoots: NodeId, site: SiteId): DirectedState
    fun retire(s: DirectedState, site: SiteId): DirectedState
    fun dropVars(s: DirectedState, keep: (VarId) -> Boolean): DirectedState
    fun collectGarbage(s: DirectedState): DirectedState
    fun isUnique(s: DirectedState, origin: OriginId): Boolean
    fun mergeAll(states: List<DirectedState>): DirectedState
    fun join(old: DirectedState?, incoming: DirectedState): Joined<DirectedState>
}
```

`env` and `heap` use `defaultReturnValue(ABSENT)`. `EMPTY_NODE` is a valid written value (`x.f = null`). It must stay different from "absent", because absent means default content. `VarTable` reserves the id `EXPOSED_VAR` for the exposed key. `isUnique` reads the exposed node of the state (§7.5, §7.6).

Simulator:

```kotlin
class Wto(val order: IntArray, val isHead: BitSet, val componentEnd: IntArray)

fun CompactGraphTopSort.weakTopologicalOrder(startNode: Int): Wto?

fun CompactGraphTopSort.onCycle(startNode: Int): BitSet

inline fun <reified S : Any> simulateGraphWto(
    graph: CompactGraph,
    wto: Wto?,
    initialState: S,
    statesBefore: Array<S?>,
    statesAfter: Array<S?>,
    throwers: (Int) -> IntArray,
    merge: (Int, List<S>) -> S,
    join: (Int, S?, S) -> Joined<S>,
    eval: (Int, S) -> S,
)
```

Driver:

```kotlin
class DirectedAliasAnalysis(
    private val callResolver: CallResolver,
    private val reachabilityOf: (JIRMethod) -> JIRLocalVariableReachability?,
    private val cancellation: AnalysisCancellation,
    private val policy: DirectedAliasPolicy,
) {
    fun analyze(jig: JIRIntraProcAliasAnalysis.JIRInstGraph): DirectedAliasResult
}
```

`DirectedAliasResult` holds the frozen tables and `statesBefore` / `statesAfter`. `DirectedAliasQuery` implements the facade queries below on it, with a lazy `ReverseIndex` for each state.

The backend switch is in `JIRIntraProcAliasAnalysis.compute`, which also holds the time limit. In directed mode it returns `DirectedAliasResult?`. `getJIG` and the private `CallResolver` of that file become `internal`. A table-limit stop throws the JVM exception `DirectedTableLimitExceeded`. `compute` catches it, logs the table statistics, and returns `null`. So the shared `AnalysisCancellation` does not change.

The facade has no shared base class (D6, M3). The shared `LocalAliasAnalysis` does not change. JVM facade:

```kotlin
class JIRLocalAliasAnalysis(
    entryPoint: JIRInst,
    graph: JApplicationGraph,
    callResolver: JIRCallResolver,
    modelProvider: TaintRulesProvider?,
    localVariableReachability: JIRLocalVariableReachability,
    cancellation: Cancellation,
    languageManager: JIRLanguageManager,
    params: Params,
) {
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun mayHoldUnknownObject(base: AccessPathBase.LocalVar, statement: CommonInst): Boolean
    fun findHeapAlias(base: AccessPathBase.LocalVar, accessors: List<AliasAccessor>, statement: CommonInst): List<AliasInfo>?
}
```

`AliasInfo`, `AliasApInfo`, `AliasAllocInfo` and `AliasAccessor` do not change. All consumers keep their types.

### 7.4 Reuse of the code of main

| Code on main | Reuse in the directed engine |
|---|---|
| `JIRDSUAABuilder.kt`: `Stmt`, `Expr`, `RefValue`, `InstEvalContext.evalInst` | Use as is, with one change: `Stmt.Return` carries a constant value or `null` (today a constant return gives `Stmt.Return(null)`). The U4 cause is in the DSU load, not in the builder. |
| `InterProcCallNode.kt`: `NestedCallInstEvalCtx`, `JirCallResolver`, `mkContextId`, `ContextInfo` | Use as is for callee contexts. Add the type parameter `<S>` to `GraphAnalysisState`, `ResolvedCallMethod` and `CallTreeNode`. Then both engines use one resolver. This change does not change behaviour. |
| `JIRIntraProcAliasAnalysis.getJIG`, `JIRInstGraph` | Use as is. Make `getJIG` `internal`. |
| `simulateGraph` (`CORE/graph/CompactGraphSimulator.kt`) | Copy its structure into `simulateGraphWto`. Do not change `simulateGraph` (Go and the DSU use it). |
| `CompactGraphTopSort` back-edge finder | Add `weakTopologicalOrder` and `onCycle`. |
| `JIRLocalVariableReachability` | Drop dead variables of the current context only. At a head, drop inside `merge` and on the incoming state, then `join`. Never drop after `join`. A callee uses its own reachability, as `DSUAliasAnalysis.methodReachabilityInfo` does. Filter reported bases as `compress` does. |
| `AnalysisCancellation`, `withAnalysisCancellation` | Use as is (time limit 10 s, parent cancellation). |
| `ExternalCallModelProvider`, `CallModelProvider` in `JIRLocalAliasAnalysis` | Use as is. Apply the `<rule-storage>` filter (CK11) in the directed model step only, so that DSU answers do not change. |
| `LocalAlias.Alloc(stmt, ctx)` keys | Replace with `SiteTable.site(ctx, instIdx)`. Same key content, dense id. |
| `AliasUtil.kt`: the generic `forEachAliasAtStatement` overloads and `forEachAliasAtStatementAmongBases` (receiver `LocalAliasAnalysis`) | Copy them into `JVM/analysis/JIRAliasUtil.kt` with the facade as receiver (D6, M3). The copies call the shared `applyAlias` and `unapplyAlias`, which have no receiver. Do not change `AliasUtil.kt`. |
| `Convert.convertBaseAccessor` | Reuse its mapping rules for bases (Local, Arg, This, Static, string constant, other allocation) in `DirectedAliasQuery`. |

### 7.5 Transfer rules (JIR `Stmt` to O operation)

`val(v)` is `valueOf(state, varId(v))`. A root variable (`Arg`, `This`, static root) has the default value `{symRoot(base)}` if the map has no entry.

| `Stmt` (from `evalInst`) | Operation |
|---|---|
| `Copy(l, r)` | `assign(l, val(r))`. No table work: the node id is shared (`copyO_rel`). |
| `Assign(l, Alloc(JIRNewExpr))`, `Assign(l, Alloc(JIRNewArrayExpr))` | Recency on and loop site: `retire(s)`, then `env[l] := {alloc-new(s)}`. Otherwise `env[l] := {alloc(s)}` (§7.9). |
| `Assign(l, Alloc(JIRCatchInst))` | `env[l] := {sym(fresh(s), [])} ∪ val(v)` for each `Throw(v)` of this method or of an inlined callee with an edge to this handler. The fresh origin is outer, has the symbolic default content (as Lean `unknown`), and is never unique. No recency. |
| `Assign(l, Alloc(box valueOf call))` | `env[l] := {boxConst(T)}`: one origin for each box class `T`, for all sites. Never unique. No recency. `Boolean.valueOf` can also return the static fields `Boolean.TRUE` and `Boolean.FALSE`. The engine does not relate them (accepted loss; boxes have no reference fields). |
| `Assign(l, Alloc(inst))`, any other `inst` | `env[l] := {sym(fresh(s), [])}`. Never unique. |
| `Assign(l, RefConst(null))` | `env[l] := ∅`: erase the entry (`nullO_rel`). |
| `Assign(l, RefConst(string v))` | `env[l] := {stringConst(v)}`. Keyed by value, not by site: equal literals are one object at run time. This adds aliases between locals that hold the same literal (§9.1). |
| `Assign(l, RefConst(class literal C))` | `env[l] := {classConst(C)}`, keyed by the binary name of `C`. |
| `Assign(l, RefConst(other))` | `env[l] := {siteConst(s)}` |
| `Assign(l, Primitive)` | no origin: erase the entry of `l`. |
| `Assign(l, FieldLoad(i, f))` | `env[l] := load(val(i), f)`. A static `i` uses the static root (key below). |
| `Assign(l, ArrayLoad(i))` | `env[l] := load(val(i), ELEM_CELL)` |
| `Assign(l, Unknown)` | `env[l] := {sym(fresh(s), [])}` |
| `FieldStore(i, f, v)` | `store(val(i), f, val(v))`. Strong if `size(val(i)) == 1` and `isUnique(o)`. Else weak (`storeO_rel`, `storeRO_rel`). A primitive `v` is skipped. |
| `ArrayStore(i, v)` | `storeWeak(val(i), ELEM_CELL, val(v))`. Always weak. A primitive `v` is skipped. |
| `WriteStatic(f, v)` | `store({symRoot(static C)}, f, val(v))`. This fixes U3 (probe row 28, Lean `static_unsound`). A primitive `v` is skipped. |
| `Call`, unresolved | `havoc(args + receiver, s)` (§7.6). Then `env[l] := {sym(fresh(s), [])}`. Then the pass-through models (§7.8). |
| `Call`, resolved (inlining depth 1) | Inline the callees (§7.7). |
| `Return`, `Throw` | No state change. A callee `Return` gives the value for the caller (§7.7). |

Static root key. Key the static root origin by the binary class name `field.enclosingClass.name` of the `JIRField`, for both `FieldLoad(Static(_), field)` and `WriteStatic(field, _)`. Do not use `RefValue.Static.type` as the key: it adds `<T>` for a generic class and uses `Outer.Inner` for a nested class. Keep `AliasAccessor.Static(type)` only for the output. `BaseTable` records the mapping.

A store value can be an `Expr` (for example `x.f = "s"` or `x.f = null`). First evaluate it to a node with the `Assign` rules. Then store that node.

Order inside a statement: evaluate the right side first, then write the left side. This removes the U4 cause. A self copy `x = x` is `assign(x, val(x))`, which does nothing (LT1 does not apply).

Builder notes. `Character.valueOf` is an unresolved call, because the builder list has `java.lang.Char`, not `java.lang.Character`. P6 fixes the list. A `JIRFieldRef` of an instance field without an instance gives `Expr.Alloc`; it takes the "any other `inst`" row.

Multi-dimensional arrays. `new T[n][m]` makes non-null inner arrays. For a `JIRNewArrayExpr` with `k > 1` dimensions, the default content of `ELEM_CELL` of the level-`j` array origin is `{alloc(s, j + 1)}` for `j < k`. Without this rule, `a[0]` reads as null, and later loads through it lose aliases. The Lean model has no such case (allocation cells are null).

Mixed encoding (argued). With recency on, a site that is not a loop site uses `alloc(s)`. It equals `alloc-new(s)` of Lean recency, because `alloc-old(s)` stays empty for such a site.

Uniqueness (`isUnique`), with `entryUnique = policy.entryUnique`:

| Origin | Unique | Lean source |
|---|---|---|
| `sym(root, q)`, `q` without `ELEM_CELL` | `entryUnique`, and `q` is not below an exposed origin | `Origin.uniqueB` (Concept.lean), `uniqueCN` (Sound/CellNamed/Concept.lean) |
| `sym(fresh s, q)`, `q` without `ELEM_CELL` | `entryUnique` and not `isLoopSite(s)`, and `q` is not below an exposed origin | same |
| allocation children `⟨@s.c.q⟩`, `deep(@s.c)` | no | `uniqueR_name`; `hsym`, `hdeep` |
| `deep(b)` | no | same |
| `alloc(s)` (recency off) | not `isLoopSite(s)` | same (`once s`) |
| `alloc-new(s)` | yes | `uniqueR` (Sound/Recency/Concept.lean) |
| `alloc-old(s)`, constants | no | `uniqueR`, `uniqueB` |

`isLoopSite(s)` is true in two cases. Case 1: the statement of `s` is on a cycle of its graph (`onCycle`). Case 2: `s` is in a callee, and the call statement is on a cycle of the caller. Each JIR statement index occurs one time in each context. So "occurs at most one time" in `Prog.onceB` holds for each JIR site.

Constructor `this`. `this` is the root `sym(root this, [])` in each method, also in `<init>`. The builder flag `This(isOuter)` has no effect on the directed engine. This fixes shapes U1.a3 and U1.a4 (Lean `a3_unsound`, `a4_unsound`): `env n = {this, alloc}` has two origins, so the store is weak. With the default `entryUnique = true` (D1), a store on `this` alone is strong in each method, also in a constructor (probe row 29 keeps its answer, and probe row 30 flips, §9.3). With `entryUnique = false`, it is weak in each method (probe row 29 then loses precision against the DSU).

### 7.6 Calls: havoc model

No alias drop (D2, decided by the user). The may analysis does not drop aliases at an unresolved call. The drop of main (`invalidateOuterHeapAliases`) is a must-side rule: a callee can overwrite a cell, so a must relation through that cell ends. A future must analysis keeps the drop (§8.4). Main has no must analysis, so the directed (may) analysis removes the drop and uses weak havoc.

Volume effect. On main the drop removes heap aliases after each unresolved call, so it also limits the alias answer volume. The user reports that a fix of the drop on main explodes the analysis (R0). D2 stands. The flag `diagnosticCallDrop` (D11 (e), default `false`) applies the drop of main in the directed engine, for an A/B diagnosis only: it isolates the volume effect of D2. It is unsound (U2) and never a default.

The engine has one call rule: CN (D2, decided by the user 2026-10-29, §4.11). It keeps the old content of each cell, so it fixes U2. Call `s` adds the cell name `name(o, c)` to each written cell of each covered origin and to each cell of each covered allocation. It adds the closure to the exposed set. Concrete call semantics: A2-narrow (§3.1). Proof state: proved (`csoundCN`, `mayProgCNO_eq`, `csoundCNO`, §4.11). The engine has no havoc mode switch.

Dropped modes. On 2026-10-29 the user dropped the two other call rules from the engine (D2):

- `SHARED` (site havoc origins). As a call rule it makes each value loaded after a call alias each outer path (`havoc_spread`, R1). As a diagnostic it gives no clear signal: almost each answer after a call differs from the CN answer, so a comparison cannot isolate one cause. Its only gain is the cover of a callee that writes one object into two cells (A2-wide), and that shape stays out of scope (§3.4). The site havoc rule stays in the Lean model as the proof for A2-wide (`csoundE`, `csoundR`).
- `PER_CELL` (per-cell havoc origins with the closure of CN), dropped for simplicity. It was only a diagnostic reference. It needed a separate havoc layer in the state, it had the cost that CN removes, and its narrow form is not proved sound (F11). Per-cell havoc stays in the Lean model only, as the formal reference for the precision comparison (§4.9). The three accepted losses of CN and the opposite case (`precision_order_fails`) are known from the Lean examples, not measured in the engine (§4.11).

Reach roots. The receiver is part of the reach roots. The DSU uses only `stmt.args`. The directed engine needs the receiver: after an unresolved `x.<init>(v)`, the cells of the allocation of `x` get their cell names. Without it they read as null, and later loads lose aliases. The static roots are reach roots of each call (A2-narrow). So each call exposes each static root.

Constructor calls. An unresolved `<init>` call always havocs its receiver, also with no reference argument. The directed engine does not use the `cantMutateAliasedHeap()` exemption of the DSU (D10). With CN, the receiver `alloc-new(s)` is covered, so each cell `f` of the new object gets `⟨@s.f⟩`. Two loads of one field of the new object then alias, as in the DSU (`need_answersCN`, `empty_cell_realN`). Test: `directed no-argument constructor call makes the allocation fields havoc content`.

The call. `havoc(s, roots, site)` implements `havocCNO` (Opt/CellNamed.lean) with these steps:

1. Start set. `R := members(roots)`. `roots` is the union of the nodes of the arguments and of the receiver. Add the marker origin `EXPOSED_STATICS`. It stands for each static root `sym(static C, [])`, also for a class that `BaseTable` does not have yet.
2. Closure over the written heap entries only. An unwritten cell of a covered origin holds its default content, and that content is null or below a covered origin. So it adds no covered origin. A worklist visits each written entry `(o, c)` with `o` covered, and adds the members of its node to `R`. `o` is covered if one of these is true: `o ∈ R`; `o` is `SYM` and an ancestor of `o` (the `parent` chain, at most K steps) is in `R`; `o` is `DEEP` over base `b` and `R` has a `SYM` origin over `b`; the base of `o` is a static root and `R` has `EXPOSED_STATICS`. The worklist uses an index from a base to its written origins. The retire of §7.9 needs the heap grouped by origin too. The Lean closure reads each universe cell (`succsN`). The engine closure has the same covered origins and the same exposed answers: the extra Lean members are below members of `R` (argued; F3). Lean `descB` also covers the allocation children of a covered allocation. The engine does not: an allocation child is never unique, so each of its cells keeps its default child, which is its cell name. So the Lean step adds nothing there.
3. Budget. If `R` has more than `maxCallClosure` origins, stop the closure and use the fallback: cover each origin, and set the exposed node to `{EXPOSED_ALL}`. This is the `none` branch of `havocCN`, so it is sound (`csoundCN`). On a finite heap the closure always ends. The budget only bounds its cost.
4. Names on written cells. For each written entry `(o, c)` with `o` covered: `heap[(o, c)] := union(heap[(o, c)], singleton(cellName(o, c)))`. For a `SYM` origin the name is its default child. So if the new node is equal to the default content (example: `x.f = null` before the call), remove the entry (normal form, §7.10).
5. Names on covered allocations. For each covered allocation origin (`ALLOC`, `ALLOC_NEW`, `ALLOC_OLD`) and each cell `c` of `CellTable`: `heap[(o, c)] := union(read(o, c), singleton(⟨@s'.c⟩))`, with `s'` the allocation site of `o`. The default content of an allocation cell is null, not its name, so this step writes each cell. `CellTable` is fixed before the fixpoint: a pre-pass collects `ELEM_CELL` and the fields of the method and of its inlined callees. A cell outside `CellTable` is not an analysis cell, and the engine never reports a path over it (§4.5).
6. Exposure. `env[EXPOSED_VAR] := union(env[EXPOSED_VAR], intern(filter(R)))`. The filter keeps the markers and the `SYM` origins with a path shorter than K. Only these members can change the uniqueness test: a unique origin has at most K cells, and the test reads only its proper prefixes. So the filter does not change answers (argued).
7. Result. `env[l] := {sym(fresh(s), [])}` (Lean `astepCN`, call case). Then the pass-through models (§7.8).

Uniqueness. `isUnique(s, o)` applies the table of §7.5. For a `SYM` origin with a non-empty path, it also tests each proper prefix (the `parent` chain, at most K steps): the exposed node of `s` must not contain it (binary search). If the exposed node has `EXPOSED_ALL`, no `SYM` origin with a non-empty path is unique. If it has `EXPOSED_STATICS`, no `SYM` origin with a non-empty path over a static root is unique. Cost: `O(K · log |E|)` for each strong-store candidate.

The exposed key. The proof of `csoundCN` needs these rules (§4.11):

- The join makes the union of the exposed key as of each other key, and the change bit includes it. So a loop does not stop before `exposed` is stable.
- `dropVars` and `collectGarbage` never remove `EXPOSED_VAR`. The garbage collection does not use exposed origins as roots.
- `retire` renames inside the exposed node as inside each environment entry. After the filter of step 6 the node has no allocation origin, so the rename has no effect (argued).
- At method entry the key is absent (the empty set). `top` sets it to `{EXPOSED_ALL}`.

Cost of one call (argued; no theorem, F10). Let `W` be the written entries of the covered origins and `A` the covered allocation origins. The closure costs `O(|W| · K)`. The names cost `|W| + |A| · |CellTable|` memoized unions. The exposure costs one intern and one union. A cell name depends only on `(o, c)`. So the second call on a cell gives a memo hit, and the values do not grow with the number of calls. A call on an object with a large written subtree costs more (R15). Counters: `callClosureSize`, `callWrittenCellsTouched`, `callAllocCellsTouched`, `exposedSize`, `callFallbacks` (§11.2).

Lean has no written-cells-only closure. The Lean proofs use explicit writes over the universe (`havocCN`, `havocCNO`).

### 7.7 Inlining, depth 1

Decided by the user (D12): "we keep inlining". The directed engine inlines at depth 1, as main does.

Production uses inlining depth 1 (`experimentalAAInterProcCallDepth = 1` in `core/src/main/kotlin/org/opentaint/common/sast/CommonAnalysisOptions.kt`). Unit and integration tests use depth 0. The directed engine keeps the structure of main (`DSUAliasAnalysis.evalCall` with resolved methods).

| Item | Rule in the directed state |
|---|---|
| Resolution | `CallTreeNode.resolveCall` and `JirCallResolver.resolveMethodCall` as on main (`level < depth`, and all overrides are known) |
| Callee entry state | The caller state before the call. The callee shares the node, origin, site, cell and variable tables. |
| Callee state arrays | New `statesBefore` / `statesAfter` arrays for each evaluation of the call in the caller fixpoint. So callee loop heads start from the current caller state. |
| Callee `this` and arguments | `NestedCallInstEvalCtx.createThis` / `createArg` give the caller `Value` directly. JIR arguments are not assignable, so no copy is necessary. |
| Callee locals | `VarTable.local(idx, calleeCtx)`. The context comes from `mkContextId(stmt, overrideIdx)`. |
| Callee sites | `SiteTable.site(calleeCtx, instIdx)`. Allocation, fresh and constant origins of the callee keep their site with the context. |
| Loop sites in the callee | A callee site is a loop site if it is on a callee cycle or the call statement is on a caller cycle (§7.5). |
| Callee statics | Stores on the static root origin. The heap is shared, so the caller sees them. |
| Return | For each `JIRReturnInst` with a state after it: a reference value `v` gives `env[l] := val(v)`. A constant gives the `Assign(l, RefConst)` rule (§7.5) with the callee site. `null` gives `env[l] := ∅`. Never keep the old value of `l`. Then `dropVars` removes all variables with `context.level > callerLevel`. Then `collectGarbage`. |
| Join | `mergeAll` over all return states of all overrides |
| No return state | Use the unresolved model (§7.6), as on main. |
| Exceptions in the callee | A caller catch edge from the call gets `join(statesBefore[call], statesAfter[call])` (v1 rule, §7.10). |
| Calls in the callee | Unresolved (level 1 ≥ depth 1): havoc on the shared heap |
| Answers | Callee variables never appear. A callee allocation origin has no root instruction index, so it gives no `AliasAllocInfo`. `mayHoldUnknownObject` is true for it (M6). A string constant from a callee is reported by value. |

A callee constructor at depth 1 writes `this.f = v` through the caller receiver. If the receiver is `{alloc-new(s)}`, the store is strong. So `x = new Box(v); w = x.value` gives `w ~ v` at depth 1.

### 7.8 External pass-through models (directed)

On main, `ExternalAssign(from, to)` becomes `mergeWith(from, to)`, an undirected union (PL6). The directed rule is a weak copy `to := from`:

| `to` | Rule |
|---|---|
| `RetVal`, no accessors | `env[l] := env[l] ∪ pts(from)`. The fresh return origin stays. |
| `Arg(i)` or `This`, no accessors | `env[v] := env[v] ∪ pts(from)` for the variable `v` of that call operand |
| any base with accessors `a1..ak` | `storeWeak(post(base.a1..a(k-1)), ak, pts(from))` |
| a path with `<rule-storage>` or `AnyFieldAccessor` | skip the model (CK11; main also skips `AnyFieldAccessor`) |

`pts(from)`: for a `from` with base `RetVal`, the value in the state after the return assignment and before the havoc content is read (`{sym(fresh(s), [])}` plus the path). For other bases, the value in the state before the call. `post` evaluates a path in the state after the havoc and the return assignment. The models apply after the havoc, as on main.

Expected answer for the sample `passThroughOfTwoArgs`: `env r = {fresh, px, py}`, `alias(x) = {arg:px, r}`, `alias(r) = {x, y, arg:px, arg:py}`.

### 7.9 Recency (`alloc-new` / `alloc-old`)

Concept C without recency is weak on a loop allocation site. There it is less precise than the DSU (`loop_dsu_more_precise`, DSU/Examples.lean; `loop_bf_x`, Examples.lean). §1.8 gives the CEGAR step and its theorems.

Transfer rule (`astepR`, `retire` in Sound/Recency/Concept.lean; `retireO` in Opt/Recency.lean), for `x = new` at site `s`, with recency on:

1. `retire(s)`, with `n = alloc-new(s)` and `o = alloc-old(s)`:
   - each written cell `c` of `n`: `heap[o, c] := union(read(o, c), read(n, c))`. Then remove all entries `(n, c)`. After this, each cell of `n` is empty (`mergeCells`).
   - each environment entry and each heap entry whose node holds `n`: replace the node by `rename(node, n, o)` (`renameKeys`).
   - the exposed key is an environment entry, so this step renames inside it too.
2. `env[x] := {n}`.

`NodeTable.rename` is memoized by `(node, from)`. A site that is not a loop site cannot hold `alloc-new(s)` before its own statement, because no path goes from the statement back to it. So only loop sites retire.

Cell names (proved: `renameO_childCN`, `csoundCN`; §4.11). The cell name of `alloc-new(s)` and of `alloc-old(s)` is the same allocation child `⟨@s.c⟩`. So `retire` never renames a cell name, and the merge of step 1 keeps the names.

Cost: `retireO_work` bounds one retire by `|cells|·(6 + 4|U|)` for the merge of the cells, plus `|U| + 1` for each key whose node holds `alloc-new(s)`. The model does not charge the scan for holders. To reach this bound, the implementation needs two indexes (§5.5): written cells grouped by origin, and holders of `alloc-new(s)` for each loop site. Without the holder index, step 2 scans the state: `O(|env| + |heap|)` for each loop allocation (R6).

### 7.10 Loops, join and the fixpoint signal

Lean `loopIter` tests `leOn (f Y) Y` at a loop head, else it continues with `join Y (f Y)`. An inner loop starts a new `loopIter` from the current state in each outer iteration. Lean O tests the change bit (`joinO_flag`), never object identity. The JVM worklist `simulateGraph` instead recomputes the merge of the predecessors and tests `currentStateAfter == stateAfter`. The transfer is not monotone (strong updates, §4.3). So a plain recompute has no termination guarantee.

Iteration strategy (argued; F5). `simulateGraphWto` iterates by a recursive weak topological order (Bourdoncle):

- Each loop head accumulates: its new state is the join with its previous head state.
- An inner loop restarts from its entry state at each outer iteration. Before the inner component runs again, clear the stored states of its nodes and of its head accumulator.
- An inlined callee gets new state arrays for each evaluation of the call (§7.7).

For a reducible CFG (javac output), this strategy gives the states of the structured `loopIter` of the Lean model. An irreducible CFG (rare: obfuscated bytecode) has no WTO here (`weakTopologicalOrder` returns null). Then the engine accumulates at each back-edge target in a flat worklist. This is sound, but it can be less precise: on nested loops with strong stores, a flat worklist keeps stale inner entry states.

| Node | State before |
|---|---|
| entry | A synthetic entry node with the initial state precedes the first instruction. So a back edge to the first instruction makes it an ordinary loop head. |
| loop head | `join(oldBefore, merge(preds))`. The result has an explicit change bit. If the bit is false, the component is stable. |
| catch handler | `join(statesBefore[t], statesAfter[t])` for each thrower `t` of the handler, plus `merge(preds)` of normal predecessors |
| other node with two or more predecessors | `merge(preds)` (pointwise union; Lean `choice` = `join`) |
| node with one predecessor | the state after that predecessor |

Exceptional edges (argued). `MethodInstGraph` merges normal and exceptional successors. An instruction that throws does not do its effect. So a catch handler needs the state before the thrower too. For an inlined callee the v1 rule is `join(statesBefore[call], statesAfter[call])`. The Lean model has no exceptional flow. The DSU on main uses only the state after the thrower, so it has the same defect (argued; P0 adds a characterization probe for it). The production graph (`JTryBoundaryExceptionsApplicationGraph`) has fewer catch edges than the test graph (`JApplicationGraphImpl`). The rule above does not depend on the graph: it uses `flowGraph.throwers(catch)` of the raw JIR graph.

Change test at other nodes. Propagate if the new state is not equal to the old state. Use content equality (`DirectedState.equals`). Node ids are canonical (`Tbl.id_inj`), so content equality is one `Int` comparison for each key. Content equality needs one canonical form: remove a heap entry whose node equals the default content of its cell (also after a call, §7.6 step 4). Otherwise equal states compare unequal. This costs only extra propagation, because each cycle has a head.

Do not use object identity as the change signal. A copy-on-write operation that adds and then removes an entry gives a new object with equal content. At a loop head, an identity test then makes the analysis run forever. `join` computes `changed` from the union ids: `changed` is true if some union id is not the old id for that key. The exposed key is a key, so a growth of `exposed` sets the bit. This is `joinO_flag`.

Termination (argued): the heads only grow, and the universe is finite (symbolic paths up to K, deep origins, sites, cells, allocation children up to K below each allocation site). So the heads become stable. Other nodes are functions of the heads.

### 7.11 Data structures

| Structure | Choice | Reason |
|---|---|---|
| Node | Sorted `IntArray` of origin ids. Id 0 is the empty set. | Union and meet are linear merges. `contains` is a binary search. `Tbl.id_inj`: one id for each set, so set equality is id equality. |
| Intern map | `Object2IntOpenCustomHashMap<IntArray>(IntArrays.HASH_STRATEGY)` | Content hash and content equality on the array |
| Singletons | `IntArrayList` indexed by origin id | `singleton(o)` is the most frequent intern (new, unknown, call result). |
| Union memo | `Long2IntOpenHashMap`, key `pairKey(a, b)`, default return `-1` | Symmetric key (`mkey`). `Tbl.union_again`: each pair is merged at most one time. Before the lookup, test three cases: `a == b`, `a == 0` and `b == 0`. In each case, the result is known without the memo. |
| Rename memo | `Long2IntOpenHashMap`, key `(node shl 32) or from` | `retire` renames the same nodes in each loop iteration. |
| Default content | By rule, not stored: `sym(b, q).c → {symOrDeep(b, q + c)}`; `deep(b) → {deep(b)}`; allocations and constants `→ {}`; catch and other fresh origins as `sym(fresh s, [])`; allocation children `⟨@s.c.q⟩.c' → {⟨@s.c.q.c'⟩}`, `deep(@s.c)` beyond K (§4.1); multi-dimensional arrays as in §7.5. During the analysis, a `Long2IntOpenHashMap` caches the default node for each heap key. | Lean `adefault`. The heap map holds only written cells (§5.5). |
| Environment | `Int2IntOpenHashMap` `VarId → NodeId`, live non-null variables only, plus the exposed key `EXPOSED_VAR` | Copy cost `O(live vars)`. Dead variables are removed at each statement, as on main. The exposed key is never removed. |
| Heap | `Long2IntOpenHashMap` `HeapKey → NodeId`, written cells only (a call writes the cells of §7.6 steps 4 and 5) | `fam_osize`: the map part is linear in the program. |
| Heap index | written origins grouped by origin and by base | the call closure (§7.6 step 2) and `retire` (§7.9) |
| Exposed set | the node of `EXPOSED_VAR`: filtered `SYM` origins and the markers `EXPOSED_STATICS`, `EXPOSED_ALL` | no own join, comparison or copy (§7.6) |
| State containers | fastutil maps, copy-on-write (copy, then change, for each statement that changes the state) | See below. |
| Reverse index | Lazy, one for each state that a query uses, cached in an `AtomicReferenceArray<ReverseIndex?>` | §5.7: the eager index costs more than enumeration on small programs. Default edges are computed by rule. |
| Answer cache | `ConcurrentHashMap<Long, List<AliasInfo>>`, key `(stmtIdx shl 33) or (after shl 32) or varId` | Full answers only (or the answer cut by the deterministic budget `maxQueryPaths`, which depends only on the key). No depth in the key, because no outer call truncates an answer. So the directed path does not have the cache-order defect of main (CK7). |

Memory (to be measured; gate in §11.2). The DSU removes heap elements of removed groups (`State.removeUnsafe`) and dead locals. The directed heap map has no such removal by itself. So the engine does four things:

1. Abstract garbage collection at each join and at the method exit of each inlined callee: drop each heap entry whose origin is not reachable from live variables, entry roots or statics, through written cells and default content. This is sound, because each query starts only from these roots.
2. `DirectedState` shares each component map (`env`, `heap`) by reference when a statement does not change it.
3. For a node with one predecessor, `statesBefore[i]` is the same object as `statesAfter[pred]`.
4. After the fixpoint, intern equal states (one copy for each distinct content). `DirectedAliasStats.retainedEntries` counts the map entries after this step.

Container decision (D8): fastutil copy-on-write, not `kotlinx.collections.immutable` persistent maps. Reasons:

1. No boxing of `Int` and `Long` keys and values. A HAMT of boxed keys costs more for each entry.
2. The O join cost is per key (`joinO_work`: at most 5 units for a key with equal ids). A tight loop over two primitive maps is fast. The HAMT benefit (skip shared subtrees) needs access to internal nodes, which `kotlinx.collections.immutable` does not give.
3. The change signal is the explicit change bit. So the identity property of persistent sets is not necessary.

If the memory gate fails (§11.2), measure a persistent variant. The container is private to `DirectedState`, so the change is local.

Table growth (`chain_table`, §5.7): count `contentSize`. If it exceeds `maxTableContent`, stop the analysis of the method (§7.14). The initial value 50 000 000 is about 200 MB of `int` content for one method. The shadow runs (P9a) measure the maximum on thingsboard and Conductor. P10 sets the cap from these maxima, the 16 GB budget and the number of parallel method analyses. Memo misses (`test_miss`, §5.7): count `memoMisses` for the measurement plan.

### 7.12 Query implementation

`findAlias(x, P)` implements §6.2 (`findAlias_iff`, `search_mem`, `findAliasO_iff`):

1. Seeds: `members(val(x))` at state `P`.
2. Holders of an origin `o`: variables `v` with `o ∈ env[v]` (reverse environment index); static roots and argument roots by rule; heap holders `(p, c)` with `o ∈ read(p, c)`. Heap holders come from two sources:
   - the heap map: each written entry;
   - default edges by rule:
     - `sym(b, q)` holds `sym(b, q + c)` at `c` if `(sym(b, q), c)` is not written;
     - `sym(b, q)` with `|q| = K` holds `deep(b)`;
     - `deep(b)` holds `deep(b)` at each cell, but the search never expands this self edge (§6.2);
     - an allocation child `⟨@s.c.q⟩` holds `⟨@s.c.q.c'⟩` at `c'` if `(⟨@s.c.q⟩, c')` is not written.
3. Backward search with suffixes, up to `maxAccessors = 6` heap accessors. Prune a child suffix if its preimage set does not meet the liveness layer of the remaining depth (`mem_live`).
4. Output: variable holders become `AliasApInfo(LocalVar | Argument | This, path)`. Static roots become `AliasApInfo(ClassStatic, [Static(T)] + path)`. Filter bases by `JIRLocalVariableReachability.isReachable(base, stmtIdx)`, as `compress` does. Drop `(x, [])` (CK4). Keep other paths with base `x`.
5. Allocation origins in `val(x)`: `AliasAllocInfo(instIdx)` for root-context `new`, `newarray` and catch sites, and for box, class and other non-string constants (CK5; both `alloc-new(s)` and `alloc-old(s)` map to `s`). String constants: `AliasApInfo(Constant("java.lang.String", v), [])` (CK6). No heap path on a `Constant` base. Never report `null`.
6. Sort the list with one fixed comparator (kind, base, accessors). The search gives no duplicates (`search_nodup`), so no deduplication pass is necessary.
7. Path budget (D11 (c), only if `maxQueryPaths` is less than `Int.MAX_VALUE`). The search runs by suffix length: all paths with `j` accessors before the paths with `j + 1` accessors. Inside one length, the order is the comparator of step 6. The query stops after `maxQueryPaths` paths, increments `truncatedQueries`, and returns the paths so far. The cut is unsound like the cut of main, but it is a function of (state, `x`, D, budget), so it does not depend on query order. It changes CK3.
8. Volume statistics: `AliasVolumeStats.record` for each answer (§7.3).

Cost: `searchCost_le`. Enumeration is exponential in D (`qfam_sep`).

| Query | Implementation |
|---|---|
| `findHeapAlias(x, π)` | The same search, seeded by `aevalPath(x, prefix)` for each prefix of `π` (`heapAliases_iff`). The JVM has no consumer (M4). Tests use it in place of `forEachHeapAlias` (probe helper `heapAnswer`). |
| `findArrayElementAliases(x)` | The search seeded by `load(val(x), ELEM_CELL)`, plus the allocation and constant origins of that node. It replaces `getAllAliasAtStatement` in the vararg branch of CS8 (M1). |
| `mayHoldUnknownObject(x)` | `val(x)` holds an origin that is not a root-context allocation and not an entry root `sym(This \| Arg, [])` (M6). |

Queries do not write tables. After `freeze()`, the tables are read-only:

- A query read computes default content by rule. It merges with `unionUncached` on `IntArray`s and does not intern.
- A query read of a default symbolic child that the analysis did not create gives a virtual origin: a negative id in a query-local table, described by (parent, cell). Its only heap holder is `(parent, c)`. A virtual origin is never reported as an allocation.
- A query-local cache keyed by (origin, cell) holds the computed default content. It is confined to one query.
- The default-node cache of §7.11 is filled only during the analysis. A query never writes it.

Test: a query at depth 6 on a new symbolic chain after `freeze()`.

### 7.13 Thread safety and determinism

| Property | Mechanism |
|---|---|
| Lazy compute | `lazy(LazyThreadSafetyMode.SYNCHRONIZED)` in the facade, as `LocalAliasAnalysis.aliasInfo`. On parent cancellation the exception leaves the `lazy`, and the next access tries again (as on main). |
| Frozen tables | `freeze()` on `NodeTable`, `OriginTable`, `BaseTable` after the fixpoint. A write after `freeze()` throws. |
| Read-only queries | Uncached merges and query-local virtual origins (§7.12). No shared mutable state except the two caches. |
| Caches | Answer cache: `ConcurrentHashMap.computeIfAbsent`. Reverse index: `AtomicReferenceArray.compareAndSet`. Two threads can build an index for the same state. `compareAndSet` keeps the first index and discards the second. The two indexes are equal, so the answers do not change. |
| Determinism (CK7) | The fixpoint is single-threaded. fastutil iteration order depends only on the insertion sequence. Node ids can depend on the order of unions, but the answers depend only on sets. The output list is sorted. The cache keys have no depth, so query order cannot truncate an answer. |

### 7.14 Time limit and failure

| Event | Behaviour |
|---|---|
| Fixpoint time over `aliasAnalysisTimeLimit` (10 s) | `AnalysisCancelled`. Log "Alias analysis for M exceed 10s" (the same text as on main). All queries answer `null`. CS7 uses its default constraint. |
| `contentSize > maxTableContent` | Throw `DirectedTableLimitExceeded`. `JIRIntraProcAliasAnalysis.compute` logs the table statistics. All queries answer `null`. |
| Parent `Cancellation.Cancelled` | Leaves the `lazy`, as on main. |
| Checkpoints | One for each evaluated statement (as `DSUAliasAnalysis.eval`), and one for each 1024 entries inside `join`, `havoc`, `retire` and `collectGarbage`. |
| Query cost | Bounded by `searchCost_le`. The query calls `parentCancellation.checkpoint()` for each 1024 expanded nodes. On main the query has no check. A per-query path budget (`maxQueryPaths`, §7.12 step 7) is option (c) of D11. It changes CK3. |

---

## 8. API and consumer migration

Consumers (eight JVM sites in main sources):

| Id | Consumer | Query used |
|---|---|---|
| CS1/CS2/CS3 | Sequent store summary (forward and backward), through `JIRStatementSummary` | `findAlias` before the store |
| CS4/CS5 | Copy of call-created facts to aliases (`forEachAliasAfterCallStatement`) | `findAlias` ∩ `findAliasAfterStatement` at a call |
| CS6 | Call precondition (trace) | `findAlias` for each local of the call |
| CS7 | Receiver and argument type constraints (`JIRCallResolver.resolveValueTypeConstraints`) | `findAlias`; `AliasAllocInfo` gives exact-type constraints |
| CS8 | Rule-condition atoms (`JIRBasicAtomEvaluator`) | `findAlias`; the vararg branch uses `getAllAliasAtStatement` |

Cost of an answer. CS1-CS6 turn each reported path into facts: the store summary adds a fact for each alias path of the stored base (CS1-CS3), the call rule copies a fact to each path of `before ∩ after` (CS4/CS5), and the precondition adds a candidate for each path (CS6). A longer path gives a fact with a longer access path. So the taint cost grows with the number and the length of the reported paths, not with the cost of the alias fixpoint (R0, §11.1).

No JVM consumer needs symmetry. Only the CS8 vararg branch needs transitivity (it takes "the alias set that contains `lv[*]`"). No JVM main code calls `forEachHeapAlias`. Only Go and the untracked probe suite call it.

### 8.1 Contract CK1-CK13

| Item | Contract | How the proposal keeps it |
|---|---|---|
| CK1 | `findAlias` / `findAliasAfterStatement`; `null` or empty if no answer | The facade keeps both: `statesBefore[idx]` / `statesAfter[idx]`. `null` on timeout or for an unreachable statement. A variable with an empty value gives an empty list (main: `null` when the element is absent). Consumers treat both the same. |
| CK2 | Meaning of `AliasApInfo(base, accessors)` | The path may hold an object that `x` may hold at P: `pts(path) ∩ pts(x) ≠ ∅`. Same bases and accessors. |
| CK3 | Completeness up to the query depth | The backward search gives exactly the paths of the enumeration (`findAlias_iff`, `findAliasO_iff`), except paths through a deep self edge (§6.2). D is `maxAccessors = 6` (the effective value of main), a parameter. Volume controls (b), (c) and (d) of D11 change this item: a smaller D, a path budget, or simple paths only. Soundness of C: `csoundCN` (the call rule CN, A2-narrow); the references `csoundE`, `csoundR` (site havoc, A2-wide) and `csoundH`, `csoundHR` (per-cell havoc, A2-strict). |
| CK4 | Exclude `(x, [])` | Step 4 of §7.12 |
| CK5 | `AliasAllocInfo(i)` if and only if `alloc(i) ∈ pts(x)` | Step 5 of §7.12. Only from `val(x)`, never from heap paths, and not from group members (the transitive set of main). |
| CK6 | String constants as `Constant`; never `null`; no heap path on a constant | `stringConst(value)` origin; step 5 |
| CK7 | Determinism | §7.13. Test `directed answers do not depend on query order`. |
| CK8 | Thread-safe shared instance | §7.13. Test `directed concurrent queries give equal answers`. |
| CK9 | Cost bounds, cancellation, `null` on timeout | §7.14 |
| CK10 | Before/after at calls with a documented model | Before = the state before the call. After = havoc (§7.6) + return + models (§7.8). Documented as a behaviour change (§9). |
| CK11 | Pass-through models after the call; `<rule-storage>` excluded | Directed weak copy (§7.8) |
| CK12 | Inlining depth 1 works; no callee elements in answers | §7.7. Inlining stays (D12, decided by the user). |
| CK13 | No symmetry or transitivity required | The may-alias relation is derived from the order `⊒` (§1.7). It is symmetric (`may_symm`) and not transitive (`alias_not_transitive`). No consumer needs more after M1. |

### 8.2 Changes M1-M8

| Item | Change | Step (§10.2) |
|---|---|---|
| M1 | `JIRBasicAtomEvaluator.resolveLocalVarValue`, vararg branch: replace `getAllAliasAtStatement` + "the set that contains `lv[*]`" with `findArrayElementAliases(lv)`. The DSU backend implements it with the partition logic of main, so DSU answers stay the same. | P1 |
| M2 | `getAllAliasAtStatement` leaves the JVM API. It stays in `LocalAliasAnalysis` for the DSU backend. | P1 |
| M3 | Base class (D6, decided by the user: copy). The facade `JIRLocalAliasAnalysis` does not extend `LocalAliasAnalysis`. Copy the generic receiver helpers of `AliasUtil.kt` into `JVM/analysis/JIRAliasUtil.kt`, with the facade as receiver (§7.4). `JIRDsuAliasBackend` extends `LocalAliasAnalysis`, as on main. The shared code and Go do not change. | P1 |
| M4 | Delete the unused JVM wrappers `forEachHeapAliasBeforeStatement` and `forEachAliasAtStatement(InitialFactAp)` in `JVM/analysis/JIRAliasUtil.kt`. Add `findHeapAlias` to the facade, with a DSU implementation over `forEachHeapAlias`. Change the probe helper `heapAnswer` to it, so the probe suite compiles after P1. | P1 |
| M5 | `forEachAliasAfterCallStatement`: no code change. The weak havoc (no alias drop, D2) keeps heap paths in the after set, so the intersection copies more facts (§9). A direct query is a later option. | — |
| M6 | `JIRCallResolver.resolveValueTypeConstraints`: if `mayHoldUnknownObject(x)`, add `defaultConstraint` (D9). | P8 |
| M7 | Negated atoms: no change. Must-alias is postponed (D5, §8.4). | — |
| M8 | Tests: keep `DSUAliasAnalysisStateTest` for the shared DSU. `DSUAliasAnalysisInvalidateOuterHeapAliasesTest` tests the JVM class `DSUAliasAnalysis`, so P13 removes it with that class. Add state-law tests for `DirectedState`. Change `test external call invalidates heap aliases` for the directed mode only (§9.2, D2). Add the non-transitive tests (§10). | P3-P9, P13 |

### 8.3 Shared base class with Go (D6, decided by the user)

| Option | Shared-code change | JVM change | Go | Risk |
|---|---|---|---|---|
| (a) Extract an interface for the two queries. `LocalAliasAnalysis` implements it. The generic helpers of `AliasUtil.kt` take the interface as receiver. | Type level | `JIRLocalAliasAnalysis` is a facade over two backends. | No behaviour change | Low |
| (b) Copy. `JIRLocalAliasAnalysis` and the directed backend do not extend `LocalAliasAnalysis`. Copy the generic receiver helpers into `JIRAliasUtil.kt`. | None | Duplicate helpers. `JIRDsuAliasBackend` extends `LocalAliasAnalysis`, as on main. | No change | The two copies of the helper loops can become different. |

Decided by the user: (b). The shared alias code and Go code do not change. The copies call the shared `applyAlias` and `unapplyAlias` (plain functions, no receiver), so only the loops over the alias lists are duplicated. The mode switch (D7) selects the backend inside the facade, so it does not need a shared interface. A later Go migration is a separate design.

### 8.4 Must-alias (D5): future work

Decided by the user: must-alias is postponed. Main has no must analysis, and this design adds none. The facade has no `findMustAlias`, and the TDD plan has no must-alias step.

Notes for the later work:

- Derive must-alias from O, with no second fixpoint: `must(x, p)` at P if `val(x) == val(p) == singleton(o)` and `isUnique(o)`. Then `must ⊆ may`, because equal singleton sets meet.
- A must analysis must keep the alias drop at unresolved calls (D2). A callee can overwrite a cell, so a must relation through that cell ends at the call. This is the rule `invalidateOuterHeapAliases` of main. The may analysis does not use it (§7.6).
- A must answer depends on A1. Under entry aliasing a must-alias answer can be false, and a kill then drops taint (§3.3).
- The unmerged branch `origin/DanielELog/must_alias` has must consumers and the test `MayAndMustRelationTest`. It is on the old API (before #216 and #406). It is input for the later design, not a base for it.

### 8.5 The alias cache defect

Main caches `convertedAliases` by `(element, stateId)` without the depth (`CORE/ap/ifds/analysis/alias/LocalAliasAnalysis.kt:137-142`). Assume that the analysis first converts an element as a nested instance (depth greater than 0). Then the chain is cut at `HEAP_CHAIN_LIMIT`, and the cache stores the cut list. A later top-level query of the same element reuses it. So answers depend on query order and thread interleaving.

| Backend | Action |
|---|---|
| Directed | Not affected. The search has no nested conversion, and the cache holds full answers (§7.11). |
| DSU | Not fixed (D13, decided by the user). A fix exists: commit `deff91ca0` (branch `origin/DanielELog/alias_cache_fix`, not merged) stores the depth with each cached list. The user does not land it: with it, the alias analysis reports more alias chains, and the analysis explodes (R0). The cut also limits the alias answer volume by accident. Step P0c adds two counters and no answer change: `cutConversions` (conversions that stopped at `HEAP_CHAIN_LIMIT` inside a nested conversion and went into the cache) and `cutCacheHits` (later hits of such an entry by a query at a smaller depth). So the volume baseline shows how much the cut hides. The A/B baseline is main as it is, so the A/B difference of the directed engine also contains the effect of the cut. The shadow statistics separate it (§11.3). |

---

## 9. Behaviour changes to expect

### 9.1 For each consumer

The rows change the alias answer volume in both directions. R0 (§11.1) gives the net effect: it is not known, and it is the first gate (§11.2).

| Consumer | Change | Direction | Reason |
|---|---|---|---|
| CS1/CS2/CS3 store summary | Fewer alias paths at a store. No edge to a path that only a transitive merge related. | Precision gain. Fewer false taint edges. | PL1-PL4. Test `field write through an alias adds the value forward and keeps the alias path backward` needs `alias(y) = {a.box}` exactly; the directed answer gives it. |
| CS1/CS2/CS3 | New edges after unresolved calls (heap paths kept) and after static writes | Soundness gain. Possible new findings. | U2 (`b_unsound`, `b_local_unsound`); U3 (`static_unsound`) |
| CS1/CS2/CS3 | New edges where the unsound strong update of main dropped a path | Soundness gain | U1 (`a1_unsound` .. `a4_unsound`); U4 (`repr_unsound`) |
| CS1/CS2/CS3 | A store on one entry path (an argument path, `this`, a static path) is strong (D1). The old content of the cell is not kept. Under entry aliasing this can drop a taint edge. | Precision gain under A1. Accepted loss under entry aliasing. | §3.3 (`swap_strong`, `root_concept_more_precise`); probe row 30; `test swap fields` (§9.2) |
| CS1-CS6 | Two locals that hold the same string literal now alias (one `stringConst` origin for each value). Facts on one local are copied to the other. | More facts, possibly more findings | §7.5. Test in P6: `directed equal string literals in two locals alias`. |
| CS1-CS6 | Callee-made aliasing of existing objects (an unresolved `m(x, y) { x.f = y; }`) stays out of scope, as on main. | No change | §3.4. The IFDS analysis covers resolved callees through their summaries and library callees through pass-through rules (argued). Test in P6: `directed unresolved setter call does not alias the argument with the field`. |
| CS1-CS6 | Full heap chains up to D. The cut of the DSU cache (§8.5) does not occur. | More facts, longer access paths, more IFDS work | §8.5, D13. Measure in shadow mode (R0). |
| CS4/CS5 copy to aliases at calls | The after-call set keeps heap paths (weak havoc, no alias drop, D2). The intersection `before ∩ after` keeps them, so more facts are copied. | More facts, possibly more findings, more IFDS work | CK10, M5. Measure in shadow mode, then on thingsboard and Conductor (R0, R4). |
| CS1-CS6 after an unresolved call | The call rule CN (§4.11). A store through a cell below an object that the call reached is weak (L1). A value loaded from a cell after a call aliases the entry content of that cell and the objects of other calls in that cell (L2, L3). | More facts, possibly more findings: the three accepted losses (D2) | `losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`. The call-rule shadow counts them (§11.2). |
| CS1-CS6 after an unresolved call | A call changes only the objects that its arguments and the static roots reach. A strong update on another object stays strong. Two loads of different cells after a call do not alias. | Precision gain | `gain_answersCN`, `spread_goneCN` (§4.11) |
| CS4/CS5 | Pass-through models are directed. The receiver after the call no longer holds each member of the argument set. | Precision gain. Fewer copies. | PL6 |
| CS6 call precondition (trace) | Fewer false backward candidates | Precision gain. Shorter trace search. | The same relation as CS4 before the call |
| CS7 type constraints | `AliasAllocInfo` only from `pts(x)`. Fewer exact-type constraints. The accidental root widening of the DSU stops. | Precision gain, and possible new false negatives. The example `x = c ? new A() : foo()` gives `{A exact}` on main too, because the DSU converts `CallReturn` and `Unknown` to nothing. The new false negatives come from shapes where a DSU group had an `Argument`, `This` or static member by a transitive merge. That member added the default or context constraint. The directed answer removes the member. | Mitigation M6 / D9 |
| CS8 rule atoms (not vararg) | Smaller may-sets of constants, boxes and static paths | Not monotone: findings can appear or disappear. Each change moves toward the true answer. | Positive atoms become false more often. Negated atoms become true more often. |
| CS8 (vararg) | Uses `findArrayElementAliases` | Same answers in DSU mode; points-to answers in directed mode | M1 |
| Negated atoms | Same may-answer, negated | Not monotone | M7 |

Taint-level tests to watch: `field flow - may-alias field survives write through other alias` (stays reachable: `alias.field` holds the taint through the second origin); `test sample with alias` in `CustomTest.kt` (needs `this.two.three.data` chains through constructors; the directed constructor rule keeps them); `AnyField mark exclusions follow one alias ...` (no change).

### 9.2 Existing tests that change

| Test (`JTEST/alias/AliasSampleTest.kt`) | Main | Directed | Reason | Decision |
|---|---|---|---|---|
| `test swap fields` (`swapFields(Box a, Box b)`) | `a.value` read at the sink aliases `arg0.value` and `arg1.value`; the same for `b.value` (4 assertions) | Default `entryUnique = true`: both stores are strong. The value read from `a.value` aliases `arg0.value` and not `arg1.value`. The value read from `b.value` aliases `arg1.value` and not `arg0.value`. So 2 of the 4 assertions change: the second (`aValueAliases` has `Argument(1).value`) and the third (`bValueAliases` has `Argument(0).value`) become "has not". The first and the fourth stay. With `entryUnique = false`: no change. | The DSU store on an outer receiver is weak. The two removed aliases exist only if `a` and `b` are one object at entry. A1 excludes this, and the user accepts the loss (D1, `swap_strong`, §3.3). | D1 (decided) |
| `test external call invalidates heap aliases` (`arr[0] = src; System.arraycopy(arr, ...); dst = arr[0]`) | `alias(dst) ∌ arg0` | `pts(dst) ⊇ pts(src)`, so `alias(dst) ∋ arg0`. The assertion is inverted. | The may analysis has no alias drop at an unresolved call (D2). For may-alias the removal of main is unsound (`b_unsound`, probe row 27): the callee can keep the cell (`call_w_xf`). The removal is a must-side rule. A future must analysis keeps it and gets its own test (§8.4). | D2 (decided) |

In DSU mode both tests keep their assertions. In directed mode they get the new assertions (P9).

### 9.3 Probe tests that change

Counts for the default policy (`entryUnique = true` (D1), recency on). The counts were derived with per-cell havoc, before the user chose CN. They are not derived again for CN. At inlining depth 0 most samples have unresolved calls: `touch`, the `<init>` call of each `new`, and the `probe` call itself. So a row can change by a loss or a gain of §4.11 (argued). The groups are expected to stay; P5-P7 take the exact sets for CN from the oracle (§10.1). Appendix B gives each row.

| Group | Count | Probe rows |
|---|---|---|
| Flip: precision (transitive merge removed, or a strong store on `this`) | 11 | 1, 2, 3, 4, 8, 10, 11, 30, 37, 41, 42 (row 30: both stores on `this` in a method are strong) |
| Flip: soundness (lost alias restored) | 12 | 13, 14, 15, 16, 21, 22, 24, 25, 27, 28, 35, 36 (rows 35 and 36 also lose the false `x.next^k` chain) |
| Smaller sets with recency (precision) | 4 | 17, 18, 19, 20 |
| Precision loss against the DSU | 0 | — |
| Same answer | 15 | 5, 6, 7, 9, 12 (`null` becomes empty), 23, 26, 29, 31, 32, 33, 34, 38, 39, 40 |

Total: 42 rows. With the A/B value `entryUnique = false`, row 29 loses precision against the DSU (the store on `this` in a constructor is weak), and row 30 keeps its answer: 10 precision flips, 1 precision loss, 15 same answers.

The policy also changes the exact sets of rows 13-16 and 19: a store on one entry path or on `this` before the loop or the join becomes strong. Rows 13, 14 and 19 are "Rec" rows. The group of each row does not change (argued).

With recency on, the loop stores on `cur` become strong. Then the sets of rows 13, 14 and 17-20 get smaller. For example, `alias(seen)` loses `cur.value`. This is correct, because `seen` holds `pa` and `cur.value` holds `pw`. So the expected sets of the directed probes come from the naive oracle with the chosen policy (§10.1), not from a manual derivation.

---

## 10. TDD plan

### 10.1 Layers

| Layer | What | Where | How |
|---|---|---|---|
| L0 | Lean vectors as Kotlin tables | `formal/directed-alias/Export/Vectors.lean` (the library does not import it). Output committed as `JTEST/alias/directed/lean-vectors.txt`. | A small `#eval` exporter (below). `LeanVectorTest` parses the file and runs the engine through `MiniDriver`. |
| L1 | Core unit tests of O against a naive C oracle; differential and property tests | `JTEST/alias/directed/` | `NaiveConcept` is a direct Kotlin port of `astep` / `astepR` / `analyze` with explicit sets. Its call case is the call case of `astepCN` (§4.11). A seeded random generator makes structured programs. |
| L2 | JIR sample tests | `JTEST/alias/DirectedAliasProbeTest.kt`, `AliasSampleTest.kt` | Keep each `today ...` test in DSU mode. Add a `directed ...` test for each probe in directed mode. |
| L3 | Existing suites, both modes | jvm-dataflow, java-querylang, root `:test` | `-PaliasAnalysisMode=<DSU\|SHADOW\|DIRECTED>` and `-PaliasDepth=1` set the system properties `opentaint.test.aliasAnalysisMode` and `opentaint.test.aliasDepth`. Each test harness reads them (P1). |
| L4 | End to end | thingsboard first (the volume explosion reproduces there fast), then Conductor, tms, dataflowbench Java and Kotlin | §11.3 |

L0 exporter. For each example program of `Examples.lean`, `Sound/Boundary.lean` (CX1-CX7), `Sound/Recency/Examples.lean`, `Sound/StoreExamples.lean`, `Sound/EntryAlias.lean`, `Sound/Havoc/Examples.lean`, `Sound/HavocRecency/Examples.lean`, `Sound/CellNamed/Examples.lean`, `Sound/CellNamed/Scope.lean`, `Sound/CellNamed/Reference.lean`, `HavocNeed.lean`, `DSU/Probes.lean`, `Opt/QueryFam.lean`, `Opt/Recency.lean` and `Opt/CellNamed.lean`, print one line for each query:

```
V <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell|cellN|cn> | statics=<root>,... | frame=<var>:<root>,... | prog=<s-expression> | q=<x>.<path>~<y>.<path> | may=<true|false>
F <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell|cellN|cn> | statics=... | frame=... | prog=... | var=<x> | D=<d> | paths=<sorted list>
```

`may` comes from `mayProg`, `mayProgE eu` or `mayProgR eu` (`hv=shared`), from `mayProgH eu` or `mayProgHR eu` (`hv=cell`, generous reach), from `mayProgHRN eu K statics` (`hv=cellN`, the narrow reference), or from `mayProgCN eu K statics` (`hv=cn`, the default). `paths` comes from `findAlias` (Opt/Query.lean). Each `V` line has a `decide` theorem in the Lean library for the same program (for example `join_x_y`, `loop_bf_x_fixed`). So the exported value is also a proved value. P3 changes `check.sh` so that it regenerates the file and fails on a difference from the committed copy. `#eval` is data export, not a proof, so the axiom audit does not change.

L0 rule for calls. The engine answer must be equal to each `hv=cn` vector (for example `need_answersCN`, `spread_goneCN`, `dead_answerCN`, `gain_answersCN`, `losses_CN`, `other_answersCN`, `loop_bf_x_CN`, `precision_order_fails`). The `hv=shared`, `hv=cell` and `hv=cellN` vectors are Lean-only documentation of the earlier call rules. The exporter can export them, but no test reads them, because the engine has only the call rule CN (§7.6). Each Lean `*_witness` and `*_realN` alias must stay in the `hv=cn` answer. Allocation children deeper than K: the engine and Lean both have one `deep(@s.c)` for each site and first cell (§4.11), so these vectors also compare by equality. The comparison of CN with per-cell havoc (the losses L1-L3 and the nesting gain, `precision_order_fails`) is in the Lean examples only (§4.11).

L1 differential test.

1. Generate 10 000 programs with a fixed seed: variables 0..4, fields 0..1, sites 0..3, `seq` / `choice` / `loop` up to depth 3, random frames. Use only the statement kinds of the current step (§10.2).
2. Use each combination of `entryUnique` and recency, with the call rule CN (the only call rule of the engine).
3. Make `NaiveConcept` run on the same CFG with the same strategy as O (recursive WTO, §7.10). Run O with `MiniDriver` on that CFG.
4. Compare the answers for each pair of variables and each path of length 2 or less. Compare `findAlias` with enumeration. Equality is required.
5. Also run `NaiveConcept` with the structured `loopIter`. For a program whose CFG is the structured one, require equality. Else require inclusion (each structured answer is also an O answer), and record each strict difference.
6. A port of the Lean executor gives a soundness fuzz: each concrete alias of a random run must be in the O answer. For CN, the executor follows `runAliasBN` (Sound/CellNamed/Run.lean): each havoc write starts at an argument or a static root (A2-narrow), with a distinct tag for each write. `NaiveConcept` ports the CN call rule of §4.11 (`astepCN`).

### 10.2 Steps

Each step is one PR with scope `core, analyzer`, unless the table says otherwise. Each step starts with its failing test.

Gates:

```
G-JVM:   cd core && ./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:test --offline -x :opentaint-ir:go:buildGoServer
G-CORE:  cd core && ./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --offline -x :opentaint-ir:go:buildGoServer
G-QL:    cd core && ./gradlew :opentaint-java-querylang:test --offline -x :opentaint-ir:go:buildGoServer
G-ROOT:  cd core && ./gradlew :test --offline -x :opentaint-ir:go:buildGoServer
G-LEAN:  cd formal/directed-alias && ./check.sh
```

`G-ROOT` has 52 baseline failures (`org.opentaint.go.*`, `initializationError`, no `go-ssa-server`). Check each failed class in `build/test-results/**/TEST-*.xml`. A failure outside `org.opentaint.go.*` is a regression. A root `check` does not run `G-QL`; run it explicitly. For a filtered run, add `--tests '<class>'`. The local Go tests do not run, so a change of shared code also needs Go CI green.

| Step | Failing test first | Implementation | Green gate | Mode |
|---|---|---|---|---|
| P0 | — (characterization: each test asserts the answer of main) | Commit `DirectedAliasSample.java`, `DirectedAliasProbeTest` and the runtime Java witness program. Add four characterization probes. (1) A loop at the first instruction. (2) A catch after a throwing call. (3) A constructor call with no reference argument, then two loads of one field. (4) A static write, then a read, in a generic class and in a nested class. No fix. | `G-JVM` | — |
| P0a (scope `docs`) | — | This document and `formal/directed-alias/` (an ignored root for the scope check, so it can go in the same PR) | `G-LEAN` | — |
| P0c (volume baseline) | `dsu volume stats count answer paths and the maximum chain length` (answers of main unchanged); `dsu cost stats count statement evaluations and loop head iterations` (a loop sample: the counters are positive, and the answers equal main); `dsu volume stats count a cache hit of a cut chain`: query the top-level variable of a chain of 7 fields first (sample method in `HeapAliasSample.java`), then the variable that holds the inner element; the second answer stays cut, as on main, and `cutCacheHits` is 1 | `AliasVolumeStats` on the DSU path (§7.3): for each query the answer count, the maximum chain length and the accessor sum; totals for each method and each project; the fixpoint cost counters `dsuStmtEvals`, `dsuHeadIterations`, `dsuTimeMs`, `dsuStateEntries` (§11.2); `cutConversions` and `cutCacheHits` in the conversion cache (§8.5); the alias timer `aliasTimeMs`. No answer change. Then the volume baseline run (§11.3 step 1). | `G-JVM`, `G-CORE`, `G-QL`, Go CI; thingsboard, Conductor and tms findings equal to main | `DSU` only |
| P1 | `vararg element aliases equal the partition answer in dsu mode` (characterization, green before and after); `alias mode directed is accepted by params`; in each suite, a canary test that fails if the property is `DIRECTED` and the backend in use is DSU | Facade with no shared base class + `JIRDsuAliasBackend`; copies of the receiver helpers in `JIRAliasUtil.kt` (M3, D6); `Params.aliasAnalysisMode` (default `DSU`, D7; `SHADOW` works from P9a, `DIRECTED` from P5 in tests); `findArrayElementAliases` (M1, DSU implementation); `findHeapAlias` (M4, DSU implementation) and `heapAnswer` on it; delete M4 wrappers; generic `CallTreeNode<S>`; mode plumbing (list below). No change of shared code. | `G-JVM`, `G-QL`, `G-ROOT` | `DSU` only |
| P2 | `NodeTableTest`: `intern gives one id for each set`, `empty set has id zero`, `union is symmetric and memoized`, `second union of a pair is a memo hit`, `join chain grows content quadratically and nodes linearly` (numbers of `chain_table`), `rename is memoized` | `NodeTable`, `OriginTable`, `BaseTable`, `SiteTable`, `CellTable`, `VarTable` | `G-JVM` | not used yet |
| P3 | `LeanVectorTest` for `V` lines without a call and with `rec=0`; `DirectedStateLawTest` (list below); `RandomDifferentialTest` on the generator subset without calls and with recency off; `loop at the first instruction joins the back edge` | `DirectedState`, `DirectedTransfer` (copy, allocate, load, store, weak store, null), `isUnique` and the `entryUnique` policy (default `true`, D1), `simulateGraphWto`, `weakTopologicalOrder`, `onCycle`, synthetic entry node, `MiniDriver`, `NaiveConcept`, Lean exporter, `Export/Computed.lean`, the `check.sh` regeneration check | `G-JVM`, `G-CORE`, `G-LEAN` | not used yet |
| P4 | `LeanVectorTest` `F` lines; query tests (list below) | `ReverseIndex`, `DirectedAliasQuery` on mini programs; caches; freeze; virtual origins; `AliasVolumeStats` on the directed path; the path budget `maxQueryPaths` (D11 (c), default off): test `path budget keeps the shortest paths and counts the truncated query` | `G-JVM` | not used yet |
| P5 | Directed probes for PS1, PS2, PS6-PS9, PS12, PS13 (list below); expected sets from `NaiveConcept` | `DirectedAliasAnalysis` intra-procedural. Unresolved calls with the provisional rule: the fallback of CN (cover each origin, and the exposed key with the marker `EXPOSED_ALL`: §7.6 step 3; sound by `csoundCN`), return value `{sym(fresh(s), [])}`, and the `<init>` receiver rule (§7.6). `JIRDirectedAliasBackend`, base conversion, exceptional edges, catch origin, `collectGarbage`, exactness certificate (`exactMethods`) | `G-JVM` (DSU tests unchanged, new directed tests green) | `DIRECTED` in tests only |
| P6 | PS4 flips and call tests (list below); `LeanVectorTest` for `V` lines with `hv=cn` | The call rule CN (D2, decided by the user; no alias drop): the closure over written cells with its budget and fallback, the cell names, the exposed key `EXPOSED_VAR` with its markers, `isUnique` with the exposed test, the counters of §11.2 (§7.6). Also static writes with the static root key, directed models, `<rule-storage>` filter, constants (boxes, class literals, strings), multi-dimensional arrays, constant returns, the builder box list; the diagnostic flag `diagnosticCallDrop` (D11 (e), default off): test `diagnostic call drop gives the answer of main for an unknown call on the argument` (probe row 21) | `G-JVM` | tests only |
| P7 | PS3 directed probes (list below); Lean vectors with `rec=1` (`loop_bf_x_fixed`, `loop_bf_y` of Sound/Recency/Examples.lean; `o_loop_bf_x` of Opt/Recency.lean); `directed this field write in a method is a strong update under the default policy` (probe row 30, D1) | Recency (`retire`, loop sites), constructor `this` as root | `G-JVM`, `G-LEAN` | tests only |
| P8 | `AliasSampleTest` in directed mode with inlining depth 1: `test getter aliases this field`, `test setter then getter`, `test identity same-class call`, `HeaderValues addAll fixpoint must terminate`; `write enters flushBufferWithUserData and fixpoint must terminate` at depth 0; new `directed callee constructor makes a strong field write on the new object`; `type constraints add the default for an unknown origin` | Inlining depth 1 (§7.7) with new callee state arrays; `mayHoldUnknownObject`; M6 in `JIRCallResolver` (directed mode only, or both by D9) | `G-JVM`, `G-ROOT` | tests only |
| P9 | `AliasSampleTest` parameterized by mode; directed variant of `test external call invalidates heap aliases` with the inverted assertion `alias(dst) ∋ arg0` (D2: the may analysis has no alias drop at an unresolved call); `test swap fields` in directed mode with the second and the third assertion inverted (`aValueAliases` has no `Argument(1).value`, `bValueAliases` has no `Argument(0).value`). Reason: the default `entryUnique = true` (D1) makes both stores strong, and the two removed aliases need entry aliasing, which A1 excludes (§9.2). Non-transitive tests (`alias of x does not contain y after a join`, the field example, `alias alloc info comes from points-to only`) | Test changes only | `G-JVM` | tests only |
| P9a (shadow mode) | `shadow mode gives the DSU answers to the consumers`; `shadow mode records both answer sizes of each query`; `shadow mode records a query where the directed answer is not a subset of the DSU answer` (the shape of probe row 21, U2) | `aliasAnalysisMode = SHADOW` in the facade (§7.3), `AliasShadowStats`, the not-subset log (§11.3 steps 2-3); CLI option and the end-to-end plumbing (list below). Then the shadow runs on thingsboard, Conductor and tms (§11.3 steps 2-3). | `G-JVM`, `G-QL`, `G-ROOT`; findings in `SHADOW` equal to `DSU` on thingsboard, Conductor and tms; then the user sets the volume gate (§11.2) | `SHADOW` opt-in |
| P10 | the shadow volume gate passed (§11.2) | Full suites in directed mode: `G-JVM`, `G-QL`, `G-ROOT` with `-PaliasAnalysisMode=DIRECTED`, also with `-PaliasDepth=1` where the harness supports it. Fix each failure with a failing test first. Set `maxTableContent` from the shadow maxima (§7.11). Apply the volume control that the user chooses (D11). | `G-JVM`, `G-QL`, `G-ROOT` in both modes | CLI opt-in |
| P11 (no code) | — | L4 measurements in `DIRECTED` mode (§11.3 steps 4-8), report | — | opt-in |
| P12 | — | Default `DIRECTED` (separate PR) when each condition of §11.2 holds | all gates | default on |
| P13 | — | After one release: remove the JVM DSU backend, its JVM-only tests and `DSUAliasAnalysisInvalidateOuterHeapAliasesTest`. Keep the shared DSU and its tests for Go. | all gates | mode switch removed |

Step P0b (the DSU cache fix) is dropped (D13, decided by the user). The DSU of main stays as it is.

Volume order. Before P10, directed answers reach only the alias tests (L0-L2), never the taint analysis. P0c measures the volume of main. P9a measures the directed volume next to it, with the DSU answers still in use. P10 is the first step in which directed answers feed the taint analysis, and it starts only after the shadow volume gate passes (§11.2).

Test lists:

- P3 `DirectedStateLawTest`: `join is idempotent`, `join is commutative on content`, `join flag is false for equal content in a new object`, `join flag is true when one union id changes` (`joinO_flag`).
- P4 query tests: `field example findAlias of z gives x.f y.f` (`field_findAlias_z`), `forEachHeapAlias of x f gives z x.f y.f` (`field_heapAliases_x`), `search gives no duplicates` (`search_nodup`), `directed answers do not depend on query order`, `directed concurrent queries give equal answers`, `query at depth 6 on a new symbolic chain after freeze`, `search does not expand a deep self edge`.
- P5 probes: `directed join of two allocations keeps x apart from y`, `directed join of two arguments keeps x apart from y`, `directed field write through a join of allocations keeps x f and y f with z and keeps x apart from y`, `directed load into the live root of the instance group keeps the aliased load`, `directed no-argument constructor call makes the allocation fields havoc content`, `directed catch after a throwing call keeps the value before the call`, `directed catch variable fields alias the thrown object fields`.
- P6 call tests: `directed unknown call on the argument keeps the loaded field alias` and the other four PS4 flips; `directed jdk call on the argument keeps the loaded field alias`; `directed value loaded after a call does not alias unrelated outer paths` (`spread_goneCN`); `directed store through a field loaded after a call is weak` (`need_answersCN`, `strong_after_call_realN`); `directed two loads of a cell of a new object after a call alias` (`need_answersCN`, `empty_cell_realN`); `directed dead end case keeps b alias d` (`dead_answerCN`, `dead_realN`); `directed call without arguments keeps the strong update on this box value` and `directed call on this makes the update on this box value weak` (`gain_answersCN`); `directed unrelated static root does not expose this` (`gain_answersCN`); `directed loss one store after a call on the holder is weak`, `directed loss two value after a call aliases the entry field`, `directed loss three values of two calls in one cell alias` (`losses_CN`); `directed nested cells of two arguments after two calls do not alias` (`precision_order_fails`); `directed exposed set grows at a loop head and the loop runs again` (§4.11, requirement 1); `directed closure over budget covers and exposes all` (§7.6 step 3); `directed retire keeps the cell names of a loop allocation` (`renameO_childCN`); `directed static field write then read aliases the written value`; `directed static write then read in a generic class and in a nested class aliases the written value`; `directed pass-through models of two arguments keep x apart from y`; `directed equal string literals in two locals alias`; `directed constant return replaces the old value`; `directed unresolved setter call does not alias the argument with the field`; `directed one new object in two cells is out of scope under the narrow call semantics` (the shape of §3.1, `generous_havoc_breaks_CN`).
- P7 probes: `directed strong update on a loop allocation site keeps the previous object field after a call` (PS3.1) and the PS3.2-PS3.5 directed probes.

Mode plumbing (P1 and P9a). Each hop must pass the mode (`DSU`, `SHADOW` or `DIRECTED`) and the inlining depth:

1. CLI option `--experimental-alias-analysis-mode` in `ProjectAnalyzerRunner`.
2. The Go CLI builds the analyzer command line from a fixed list (`cli/cmd/command_builder.go`). It needs a passthrough for the new option (a `cli`-scoped PR).
3. `CommonAnalysisOptions`, then `TaintAnalyzerOptions`, then `JIRTaintAnalyzer.analysisParams`, then `JIRAnalysisManager.Params`.
4. The symbolic-execution engine: `SastSeAnalyzer.SeOptions` (`core/opentaint-jvm-sast-se-api/src/main/kotlin/org/opentaint/jvm/sast/se/api/SastSeAnalyzer.kt`), set in `JirProjectAnalyzer`.
5. Test harnesses that build `JIRAnalysisManager` or `TaintAnalyzerOptions` directly: `core/opentaint-java-querylang/src/test/kotlin/org/opentaint/semgrep/util/TestAnalysisRunner.kt`, `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/AnalysisTest.kt`, `core/src/test/kotlin/org/opentaint/jvm/sast/project/tester/ProjectAnalyzerTester.kt`, `core/src/main/kotlin/org/opentaint/jvm/sast/project/TestProjectAnalyzer.kt`, `JTEST/alias/AliasSampleTest.kt`, `JTEST/alias/DirectedAliasProbeTest.kt`. Each reads the system properties of L3.
6. The three `tasks.withType<Test>` blocks (`core/build.gradle.kts`, `core/opentaint-java-querylang/build.gradle.kts`, `core/opentaint-dataflow-core/opentaint-jvm-dataflow/build.gradle.kts`) forward `-PaliasAnalysisMode` and `-PaliasDepth` to `systemProperty(...)`.
7. Fallback for the A/B runs: `ProjectAnalyzerRunner` also reads the system property `opentaint.aliasAnalysisMode`. Set it through `JAVA_TOOL_OPTIONS` if the Go CLI passthrough is not merged.

---

## 11. Risks, performance budget, measurement, rollback

### 11.1 Risks

| Id | Risk | Evidence | Mitigation |
|---|---|---|---|
| R0 | Alias answer volume. The taint analysis turns each reported alias path into copied facts (CS1-CS6, §8). So the cost driver is the number and the length of the alias paths of each query, not the alias fixpoint. More paths, or longer paths, explode the fact count and the memory. | User report (D13): on main, a fix of the call drop or of the cache truncation makes the alias analysis report many more alias chains, and the analysis explodes. It reproduces fast on thingsboard: the number of taint facts (IFDS events) explodes, and the run ends with an out-of-memory error. The volume table below gives the effect of each design change. | First gate: the volume baseline of main (P0c), then shadow mode (P9a), then the shadow volume gate (§11.2). Only then do directed answers feed the taint analysis (P10). Volume control: D11. |
| R1 | The three accepted losses of CN add answers after calls: weak stores below an exposed origin (L1) and false aliases with the entry content of a cell or between the objects of two calls in one cell (L2, L3). A part of R0. (Site havoc, which made each value loaded after a call alias each outer path, is not in the engine.) | `losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN` (§4.11); `havoc_spread` (§4.9) | Accepted by the user (D2). The engine does not measure the losses: it has no per-cell reference (§7.6). The losses and the opposite case (`precision_order_fails`) are known only from the Lean examples (§4.11). The shadow runs measure the volume of CN against the DSU (§11.2). If the volume after calls is too large, a later refinement can separate the entry object from the callee objects. Tests `directed value loaded after a call does not alias unrelated outer paths` and the loss tests of P6. |
| R2 | Node table content grows as `m²/2` on join chains. | `chain_table` | `contentSize` counter and `maxTableContent` cap. Log the statistics. |
| R3 | Memo misses at loop tests | `test_miss` | Same order as a sorted merge. Count misses in L4. |
| R4 | Weak havoc keeps heap paths after calls, so CS4/CS5 copy more facts. IFDS work and memory grow. A part of R0. | CK10, M5. thingsboard and Conductor are already memory bound. | Measure the volume in shadow mode first (R0). Then measure IFDS events and heap on thingsboard and Conductor at 16 GB. If the growth is too large, keep weak havoc in the alias state. Then add a direct after-call query for CS4/CS5. This query excludes the cells that a call touched. |
| R5 | Entry aliasing is unsound for both policies. The default `entryUnique = true` also loses the aliases that `false` keeps on a swap. | `skip_unsound`, `write_read_unsound`, `swap_strong` (§3.3). The DSU is also unsound there. | Accepted by the user (D1): A1 is a precondition of the intra-procedural analysis. Keep `entryUnique = false` as a policy value for an A/B check. Caller information on the exact partition is a later option (§3.3). |
| R6 | `retire` scans the state for each loop allocation if no holder index exists. | `retireO_work` (§5.5) | Only loop sites retire. Keep a holder index for `alloc-new` of loop sites. Measure with a counter. |
| R7 | After a walk deeper than K, a variable holds `deep(b)`, and `deep(b)` holds itself in each cell. Without a rule, `findAlias` gives `\|cells\|^D` answers, most of them false aliases. The DSU gives only the accessed chain. | `adefault` (Concept.lean), §6.2 | K ≥ D + 1, and the search never expands a deep self edge (§6.2). Measure the output size in shadow mode on thingsboard and Conductor (R0, §11.3 step 2). |
| R8 | Parts of the engine are not in the O proof: the engine form of the CN call (closure over written cells only, the filtered exposed node with markers, the explicit cells of covered allocations over `CellTable`), the WTO strategy, exceptional edges, constants, garbage collection. | `mayProgCNO_eq` covers the CN concept with explicit writes over the universe; `mayProgOE_eq`, `mayProgRO_eq`, `mayProgHO_eq` and `mayProgHRO_eq` cover the Lean references, which are not in the engine. | L1 differential test against `NaiveConcept` on the same CFG with the same strategy. Lean follow-ups F3, F4, F5, F8. |
| R9 | The directed engine havocs at each unresolved call, also at the calls that the DSU exempts (`cantMutateAliasedHeap()`). | §7.6, D10 | Count `havocs` and compare alias time in L4. |
| R10 | CS7 precision exposes the unknown-origin gap of main. | §9.1 CS7 | M6 / D9 |
| R11 | CS8 and negated atoms change findings in both directions. | §9.1 CS8 | Review each changed finding in L4 by hand. P12 needs an explanation for each lost finding (§11.2). |
| R12 | Interned constants and boxes: one run-time object for many executions | JVM semantics, not in Lean (F4) | Box and class constants are keyed by type, strings by value. Never unique, never split by recency (§7.5). |
| R13 | States for each statement use memory `O(statements × entries)`. Each method result stays in memory for the whole run (`JIRAnalysisManager.contexts`). | Not measured. The DSU removes heap elements of removed groups; the directed heap needs garbage collection (§7.11). | The four measures of §7.11. `retainedEntries` budget (§11.2). D8 if the budget fails. |
| R14 | Exceptions: catch states and the catch origin are outside the Lean model. | §3.4, §7.10 | Catch edges join the states before and after the thrower (argued, F8). The DSU uses the state after only. |
| R15 | The cost of one call. The CN call visits each written cell of each covered origin, and each cell of each covered allocation. A call on an object with a large written subtree (`this` of a large method, many statics) touches many cells at each call. No theorem bounds the O call (F10). | §7.6 (cost of one call) | The values do not grow with the number of calls: a cell name is fixed, so a second call on a cell is a memo hit. Count `callClosureSize`, `callWrittenCellsTouched`, `callAllocCellsTouched`, `exposedSize` and `callFallbacks` (§11.2). The budget `maxCallClosure` bounds the closure; over it, the sound fallback applies. The shadow runs report these counters (§11.3 step 3). |
| R16 | The call rule is proved sound only under A2-narrow (`csoundCN`). With generous reach or with one object in two cells it misses aliases (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`). Completeness of recency and of calls is not proved (§4.7, F6). | §3.1, §4.11 | Both shapes are out of scope (§3.4), and the user accepted the scope with CN (D2). Under A1, a callee cannot reach an object outside the narrow closure (argued). The taint analysis covers resolved callees by their summaries. The engine has no A2-wide mode; the Lean site havoc rule (`csoundE`, `csoundR`) documents the cost of the wider scope. |

Volume table (R0). Main has two defects that limit the volume by accident: the order-dependent conversion cache cuts heap chains (§8.5), and the call drop removes heap aliases (U2). The user reports that a fix of either one explodes the analysis. The directed engine has both changes that increase the volume: no drop at calls (D2, decided) and a deterministic, depth-aware query that reports full chains up to D. It also has changes that decrease the volume: non-transitive answers (`alias(x) = {a}`, not `{a, y}`), and dominance where the DSU is sound (there, the directed answers are a subset of the DSU answers). The subset claim is proved only for the heap-free fragment (`dsu_dominates_heapFree`, with `dsu_sound_heapFree`, DSU/HeapFree.lean, §2.5). With loads and stores it is not proved (F6). So the net volume is not known. It is the first gate (§11.2).

| Change | Effect on volume | Evidence |
|---|---|---|
| Non-transitive answers: `alias(x) = {a}`, not `{a, y}` (PL1-PL4, PL7) | − | proved: `alias_not_transitive`, `join_precision_loss`, `field_precision_loss`; measured on main: probe rows 1-4, 8, 10, 37, 41, 42 (the expected directed flips, §9.3) |
| Directed pass-through models (PL6) | − | measured on main: probe row 11; argued for the directed answer (§7.8) |
| Dominance where the DSU is sound: the directed answer is a subset of the DSU answer | − | proved only for the heap-free fragment (`dsu_dominates_heapFree`); open with loads and stores (F6); known failures in §2.5 |
| No alias drop at unresolved calls (D2) | + | proved: `b_unsound`, `b_local_unsound`, `call_w_xf`; measured on main: probe rows 21, 22, 24, 25, 27; reported by the user: the fix of the drop on main explodes the analysis |
| No cache truncation: full chains up to D (§8.5, §7.11) | + | argued; reported by the user: the cache fix on main explodes the analysis; P0c counts the cut (`cutConversions`, `cutCacheHits`) |
| Other soundness fixes: U1, U3, U4 restore lost aliases | + | proved: `a1_unsound` .. `a4_unsound`, `static_unsound`, `repr_unsound`; measured on main: probe rows 13-16, 28, 35, 36. Rows 35 and 36 also lose a false `x.next^k` chain (−). |
| Strong updates on entry roots (D1): a strong store removes the old content of the cell | − | proved: `root_concept_more_precise`, `swap_strong`; measured on main: probe row 30 |
| Recency: strong stores on `alloc-new(s)` of loop sites | − | proved: `loop_bf_x_fixed`, `loop_bf_x_exact`; probe rows 17-20 get smaller sets (§9.3, argued from the oracle) |
| The call rule CN against site havoc and against per-cell havoc | − against site havoc: with site havoc, each value loaded after a call aliases each outer path (about `\|vars\|·\|cells\|^D` paths, §4.9). Against per-cell havoc: + for the losses L1-L3, − for the nesting gain and for the narrow reach (§4.11) | proved: `havoc_spread`, `spread_goneCN`, `spread_ab_noneN`; `losses_CN`, `losses_HR`; `precision_order_fails`; `gain_answersCN`. Not measured in the engine: the comparison is from the Lean examples only (§4.11). |
| Interned constants: one origin for each string value, box type and class literal (§7.5) | + | argued: two locals with one literal now alias (§9.1); not in Lean (F4) |
| Deep self edges are never expanded (§6.2) | − | argued (F7) |
| Query depth D | the main knob: the output can grow as `\|cells\|^D` on cyclic heaps | proved: `searchCost_le` bounds the query cost by the output; `qfam_sep`; D11 (b) |

### 11.2 Performance, precision and memory gates

Baseline: main as it is (D13, decided by the user). The DSU of main keeps its defects (U1-U4, the cache cut of §8.5); no DSU fix goes into the baseline. One jar that has all three modes runs both sides of each A/B (mode `DSU` against mode `SHADOW` or `DIRECTED`), so the alias timer and the counters are the same on both sides.

Volume gate (R0). It is the first gate. It has two parts: V1 in shadow mode (P9a), before any directed answer feeds the taint analysis, and V2 in directed mode (P11). This document sets no thresholds for it. The user: "measure after the implementation, then decide". So the user sets the thresholds after the shadow-mode measurement. This document defines only the metrics and the comparisons. Projects in this order: thingsboard first (the explosion of main reproduces there fast), then Conductor, then tms.

| Part | Metric | Comparison | Source |
|---|---|---|---|
| V1 (shadow, P9a) | For each query: answer count, accessor sum, maximum chain length, for each backend; the query kind (`BEFORE`, `AFTER`, `ARRAY_ELEMENT`, `HEAP`) | Directed against DSU for each query. Each query where the directed answer is not a subset of the DSU answer is logged and classified: U1-U4, the cache cut (§8.5: the DSU query had a `cutCacheHits` increment), an interned constant (§7.5), or a new bug. Unexplained queries: zero (a correctness rule, not a volume threshold). Each query where the DSU answer is not a subset of the directed answer is counted (precision gain). | `AliasShadowStats` |
| V1 | For each method and each project: number of queries, total paths, total accessors, p50 / p99 / max of the answer size and of the chain length, for each query kind; `truncatedQueries` (D11 (c)); `cutConversions` and `cutCacheHits` of the DSU | Directed total against DSU total, for each project | `AliasShadowStats`, `AliasVolumeStats` |
| V1 | Precision: mean and p99 of `\|alias(x)\|` | Directed against DSU | `AliasShadowStats` |
| V1 | Findings in `SHADOW` | Equal to the `DSU` findings (a check of the mode) | SARIF |
| V2 (directed, P11) | Taint facts: IFDS events before the memory guard (the `Progress: N/M` lines), IFDS time, peak heap, memory guard events, out-of-memory errors | `DIRECTED` against `DSU`, thingsboard first, then Conductor, at 16 GB | §11.3 step 5 |
| V2 | Alias timeouts ("exceed 10s" lines) and table-limit stops | `DIRECTED` against `DSU` on thingsboard, Conductor, tms | logs |

Other gates (directed against the baseline). The user sets each performance number after the measurement, as for the volume gate. The table gives the metric and the comparison only. The dataflowbench row is a correctness rule: no score may go down.

| Quantity | Comparison | Source |
|---|---|---|
| tms wall time | `DIRECTED` against `DSU`, median of 3 alternating rounds | §11.3 step 6 |
| Alias time for each method | log `aliasTimeMs`; the sum over tms against the DSU sum | `DirectedAliasStats` |
| Table | maximum `contentSize` for each method below `maxTableContent`; report p50 / p99 / max of `nodeCount`, `contentSize`, `memoMisses / (memoHits + memoMisses)` | `DirectedAliasStats` |
| Alias state memory | report p50 / p99 / max of `retainedEntries` for each method; the sum over thingsboard and Conductor against the DSU state entries | `DirectedAliasStats` |
| dataflowbench | Java at least 49/58, Kotlin at least 50/58; explain each changed case | §11.3 step 7 |
| Exactness | Report the share of methods with `exactMethods` true, for each project | `DirectedAliasStats` |
| Call cost | report p50 / p99 / max of `callClosureSize`, `callWrittenCellsTouched`, `callAllocCellsTouched`, `exposedSize` for each method, and the count of `callFallbacks` | `DirectedAliasStats` |

The DSU state entries come from the DSU path of the same jar (a counter of the `IntDisjointSets` size after the fixpoint).

Fixpoint cost gate (iterations, time, memory). The origin universe is finite, because the analysis can enumerate each path of at most K cells below each base. So the fixpoint cost has an upper bound, and the gate compares the measured cost with this bound and with the DSU. Both engines report the same counters in shadow mode (P9a), so one run gives both sides. The user sets the numbers after the measurement.

| Metric | Bound (argued) | Comparison | Source |
|---|---|---|---|
| Iterations of each loop head (`headIterations`, max and p99 for each method) | A head state only grows. Each iteration that changes it adds at least one origin to one key. So the iterations of one head are at most `1 + \|keys\|·\|U\|`. A list walk over one field needs about K + 2 iterations (example 6.5 of `directed-alias-analysis-spec.md`). | Directed against the DSU loop iterations of the same method | `DirectedAliasStats`, DSU counters of P0c |
| Statement evaluations (`stmtEvals`) for each method | iterations × statements of the loop body, summed over the weak topological order | Directed against DSU | the same |
| Origins created, for each kind and for each path depth (`symByDepth[0..K]`, `deepOrigins`, `allocChildOrigins`) | At most `Σ_{i≤K} \|cells\|^i` symbolic origins below each base. A walk over `w` fields gives up to `Σ_{i≤K} w^i`. | Measured value against the bound; the share of methods that reach `deep` | `DirectedAliasStats` |
| Fixpoint time for each method (`fixpointTimeMs`), and the share of methods at the time limit | — | Directed against DSU, for each project (thingsboard, Conductor, tms) | the same |
| Alias memory for each method: retained state entries, node table content (`contentSize`), memo size | Table content is at most `Θ(m²)` on a join chain of m allocations (§5.7) | Directed against the DSU state entries and the DSU element count | the same |

These counters are added in P0c (DSU side: `dsuStmtEvals`, `dsuHeadIterations`, `dsuTimeMs`, `dsuStateEntries`) and in P4 (directed side). The DSU counters do not change answers.

P10 start condition: V1 holds with the thresholds that the user set after the shadow-mode measurement, and the user decided D11.

P12 go/no-go. P12 needs all of these conditions:

1. V1 and V2 hold with the thresholds that the user set.
2. Each budget of the table "Other gates" holds.
3. No unexplained lost finding on thingsboard, Conductor or tms.
4. dataflowbench at or above the baseline.
5. The precision metric of V1 is better than the baseline.
6. A2-narrow is the call scope of the call rule CN (D2, decided by the user; §3.1, §4.11, R16).

`DirectedAliasStats` is a small counter object for each analysis, logged at DEBUG: `stmtEvals`, `headIterations`, `nodeCount`, `contentSize`, `memoHits`, `memoMisses`, `retires`, `havocs`, `callClosureSize`, `callWrittenCellsTouched`, `callAllocCellsTouched`, `exposedSize`, `callFallbacks`, `retainedEntries`, `exactMethods`, `queryCount`, `queryNodes`, `aliasTimeMs`, `fixpointTimeMs`, `symByDepth`, `deepOrigins`, `allocChildOrigins`. The call counters are the sum, the p99 and the maximum over the calls of the method: `callClosureSize` (origins in `R`), `callWrittenCellsTouched` (step 4 of §7.6), `callAllocCellsTouched` (step 5), `exposedSize` (members of the exposed node at the method exit), `callFallbacks` (calls over `maxCallClosure`). The DSU path of P0c has `dsuStmtEvals`, `dsuHeadIterations`, `dsuTimeMs`, `dsuStateEntries`. The volume counters are in `AliasVolumeStats` (§7.3).

### 11.3 Measurement plan

The sources of the baseline numbers: tms timing measured 2026-08-27 on this development machine; dataflowbench 49/58 and 50/58 reproduced 2026-09-01 with release `analyzer/2026.08.27.17eb0fe`; Conductor at 16 GB measured 2026-08-20.

Steps 1-3 are the volume phase (R0). They run before any directed answer feeds the taint analysis. The project order is thingsboard, Conductor, tms: the explosion of main reproduces fast on thingsboard (a fast out-of-memory error from the number of taint facts).

1. Volume baseline (P0c). Build the jar of main with the P0c counters (no answer change): `cd core && ./gradlew :projectAnalyzerJar --offline -x :opentaint-ir:go:buildGoServer`. Build the CLI one time: `cd cli && GOPROXY=off go build -o <out>/opentaint-cli .`. Run thingsboard, then Conductor, with the arguments of step 5, then tms with the command of step 6. Record the `AliasVolumeStats` totals of each project, `cutConversions`, `cutCacheHits`, the IFDS events (`Progress: N/M`), the peak heap and the memory guard events. Check that the findings equal the findings of main.
2. Shadow runs (P9a). The same projects in the same order, with `--experimental-alias-analysis-mode=shadow`. Check that the findings equal the `DSU` findings. Collect `AliasShadowStats`: the per-query comparison and the per-project totals of V1 (§11.2). Two engines run, so time and memory of this run are not budgets. If a shadow run does not fit in 16 GB, record it, and run again with more memory.
3. Shadow report. For each project: directed total against DSU total; the distributions of the answer size and the chain length for each query kind; the not-subset queries with their class (U1-U4, cache cut, interned constant, new). Optional diagnostic runs in shadow mode isolate the volume of single changes: `diagnosticCallDrop = true` (the volume of D2, D11 (e)), a smaller `maxAccessors` (D11 (b)), a `maxQueryPaths` budget (D11 (c)). Report the call counters of `DirectedAliasStats` (§11.2; input for R15). Then the user sets the thresholds of V1 and V2 and decides D11 (§11.2, §12).
3b. K sweep (input for D4). Run shadow mode on thingsboard and Conductor with K = 3, 5 and 7, with D unchanged. For each K, report the fixpoint cost gate (iterations, statement evaluations, origins for each depth, `deepOrigins`, fixpoint time, alias memory) and the V1 volume and precision metrics. The smallest K whose precision and volume equal those of K = 7 is the candidate for D4.

Steps 4-8 run in directed mode (P11), after the shadow volume gate.

4. Compare findings on `(ruleId, message, locations, codeFlows)`. Then key again on `(ruleId, path, startLine, startColumn)`, and report changes of the code-flow count separately. A changed flow count shows as one removed and one added finding in the first key.
5. thingsboard, then Conductor. Run the scan on the thingsboard project (`opentaint-test/opentaint-test-thingsboard`), then on `opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml`, with the CI arguments: `--passthrough-approximations`, `--java-dataflow-approximations`, the bundled ruleset plus the project rules, `--verbosity=DEBUG`, `--timeout 1080s`, and `--max-memory 16G` (at 8 GB every build reaches the memory guard). Alternate the modes `DSU` and `DIRECTED` over 3 rounds. Compare the events before the guard (the `Progress: N/M` lines), IFDS time, peak heap, guard events, out-of-memory errors and findings (V2).
6. tms. Run `<out>/opentaint-cli scan --debug --experimental --analyzer-jar <jar> --ruleset rules/ruleset --project-model ../opentaint-test/opentaint-test-tms/opentaint-project --output <out>.sarif --timeout 800s --max-memory 8G` in each mode (`--experimental-alias-analysis-mode=dsu` or `=directed`). Alternate the two modes over 3 rounds. The first run is cold: about 64 s, against about 37 s for a warm run. If you do not alternate the runs, the cold run can show a false slowdown of 70 %.
7. dataflowbench. Use JDK 21 and kotlinc 2.4.10. Run `dataflowbench run-opentaint-java-kernel --analyzer-jar <jar> --models-archive <models> --java <jdk21>/bin/java --javac <jdk21>/bin/javac` and `run-opentaint-kotlin-kernel` (with `--kotlinc` and `--kotlin-stdlib`) in each mode. Compare case outcomes.
8. For each new or lost finding: map it to a consumer (CS1-CS8) and to a probe shape. Add a probe if the shape is new.

### 11.4 Lean follow-ups

| Id | Item | Status |
|---|---|---|
| F1 | Per-cell havoc under A2-strict: concrete strict havoc, per-cell havoc origins, soundness, O equivalence, recency with per-cell havoc, and the shared key `alloc-old(s)`. Then the call rule CN under A2-narrow. | proved: `csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`, `keyOfR_alphaRS` (§4.9); `csoundCN`, `mayProgCNO_eq`, `csoundCNO` (§4.11, §5.5). Open part: the more precise rule for havoc-derived holders of per-cell havoc (§4.9). |
| F2 | O with recency: retire on node ids, equivalence with the recency concept, cost bound | proved: `retireO_rel`, `storeRO_rel`, `ostepR_rel`, `analyzeRO_rel`, `mayProgRO_eq` (both policies), `retireO_work` (Opt/Recency.lean) |
| F3 | The engine form of the CN call (closure over written cells only, the filtered exposed node with the markers `EXPOSED_STATICS` and `EXPOSED_ALL`, the cells of covered allocations over `CellTable`) gives the answers of `havocCNO`. | open |
| F4 | Multi-dimensional array defaults; interned constants (boxes, class literals, strings) | open |
| F5 | Prove that WTO iteration equals the structured `loopIter` for reducible CFGs. | open |
| F6 | Completeness for calls under A2-narrow (the three losses of CN bound the scope); "recency is at least as precise as C"; "the combination is at least as precise as each refinement alone" (the form "CN is at least as precise as per-cell havoc" is false: `precision_order_fails`); the finer key that removes the `cost_answers` alias; dominance over the DSU with loads and stores | open |
| F7 | The deep-self-edge search rule with K ≥ D + 1: it removes no path of length at most D from a root. | open |
| F8 | Exceptional flow: the catch-edge state and the catch origin are sound. | open |
| F9 | Small theorems: "recency equals C when each site is once" (`mayProgR eu = mayProgE eu`), which carries the completeness theorems to recency; a theorem `osoundE` for O without recency (for O with recency and per-cell havoc, `csoundHRO` exists). | open |
| F10 | A cost bound for the O call of CN (`havocCNO`), an analogue of `addSets_work`: the closure and the name unions as a function of the covered keys. | open |
| F11 | Soundness of the narrow per-cell reference `mayProgHRN` (Reference.lean) under A2-narrow. Model only, not needed by the engine: the engine has no per-cell mode (D2). It stays a follow-up of the formal precision reference (§4.11). | open (model only) |

### 11.5 Rollback

The mode switch is the rollback. Mode `SHADOW` gives the DSU answers to the consumers, so it needs no rollback. Set `aliasAnalysisMode = DSU` (CLI `--experimental-alias-analysis-mode=dsu`). The DSU backend stays in the code until P13. After P12 the rollback is a one-line default change.

---

## 12. Decisions for the user

The user decided D1, D2, D5, D6, D7, D12 and D13 on 2026-10-29. D3, D4, D8, D9, D10 and D11 are open: the user decides after the spec revisit. For an open decision, the row gives the options, a recommendation and the evidence.

| Id | Status | Decision | Options | Recommendation or decision | Evidence |
|---|---|---|---|---|---|
| D1 | Decided by the user | Strong updates on entry roots (`entryUnique`) | (a) `false`: weak on symbolic origins; only allocation origins can get strong updates. (b) `true`: strong store on `sym(root, q)` without `elem`, and on unique call results. | (b) `true` is the default. The user: "We may lose some aliases, but it is acceptable. We remain intra-proc." A1 is an accepted precondition of the intra-procedural analysis. (a) stays a policy value for an A/B check. | Under entry aliasing both policies are unsound (`skip_unsound`, `write_read_unsound`). (b) also loses aliases that (a) keeps: `swap_alias` with `swap_strong` false and `swap_weak` true. These theorems document the accepted loss (§3.3). No theorem orders the two policies. The completeness theorems use (b), so they cover the default (§4.7). Gain of (b): probe row 30 flips, row 29 keeps its answer, and `root_concept_more_precise`. Cost of (b): 2 of the 4 assertions of `test swap fields` change in directed mode (§9.2, P9). |
| D2 | Decided by the user (2026-10-29), with the call rule | Call model | (a) the heap-alias removal of main. (b) weak havoc with site havoc origins (A2-wide). (c) weak havoc with per-cell havoc origins (A2-strict). (d) weak havoc with no origin for an unknown object ("dead end"). (e) the call rule CN: weak havoc with cell names, narrow reach and the exposed set (A2-narrow). | No alias drop in the may analysis: (a) is out. The drop of main (`invalidateOuterHeapAliases`) is a must-side rule: a callee can overwrite a cell, so a must relation through it ends. A future must analysis keeps it (§8.4). Main has no must analysis enabled, so the directed analysis uses weak havoc. Call rule, decided by the user (2026-10-29): (e) CN, with its three precision losses. The engine has one call rule; the `SHARED` mode ((b)) and the `PER_CELL` mode ((c) with the closure of CN) were dropped by the user, 2026-10-29 (§7.6). (b) and (c) stay in the Lean model as formal references. History: the user first chose (c) and considered the call-result origin `⟨s⟩` as the havoc origin (rejected: `⟨s⟩` makes every post-call load alias every other one and the call result, and it removes strong updates on call results). Then the user found (c) too expensive: it adds a per-cell origin to each cell of each reachable origin at each call, and each symbolic object is reachable. The user rejected a lazy havoc log (it complicates state identity and the join). (d) is unsound. The user accepted (e) (CEGAR step 4, §1.8, §4.11). | (a) is unsound for may-alias (U2: probe rows 21, 24, 27; `b_unsound`, `b_local_unsound`, `call_w_xf`). (b) is sound under A2-wide (`csoundE`, `csoundR`, `mayProgOE_eq`, `mayProgRO_eq`), but a value loaded after a call may-aliases each outer path (`havoc_spread`, §4.9). (c) is sound under A2-strict (`csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`) and removes the spread (`strict_answers`, `strict_ab_none`), but its cost grows with the calls (§4.11). (d) misses a real alias: `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, `b ~ d` (`dead_realN`; CN answers true: `dead_answerCN`). (e) is sound under A2-narrow, for both policies, with recency, each K and each list of static roots (`csoundCN`); O equals C (`mayProgCNO_eq`, `csoundCNO`). Both parts of A2-narrow are necessary (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`). It keeps the HavocNeed cases (`need_answersCN`), removes the spread (`spread_goneCN`) and keeps strong updates on objects that a call does not reach (`gain_answersCN`, `gain_noneN`). Its three losses are real losses (`losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`; per-cell havoc answers false: `losses_HR`). (c) and (e) are incomparable (`precision_order_fails`, `nest_noneN`). No cost theorem for the O call (F10). Behaviour change for CS4/CS5 (§9.1) and for `test external call invalidates heap aliases` (§9.2). Volume: no drop increases the alias answer volume (R0); the diagnostic flag of D11 (e) measures this part (§11.2). The losses are known from the Lean examples only (§4.11). |
| D3 | Open: the user decides after the spec revisit | Recency | (a) on. (b) off. | (a) | §1.8 (CEGAR step 1). Cost: R6. |
| D4 | Open: the user decides after the spec revisit | Origin depth K and query depth D | K: 3, 7 or 9. D: 6 accessors, or less. | D = 6 (unchanged, `HEAP_CHAIN_LIMIT = 5`). K = 7 (K ≥ D + 1). | With K ≥ D + 1, a reported path from a root variable is its own origin, with no deep origin in the reported range (CX1 shows the merge). A path from a loaded variable can reach a deep origin in the reported range; the search rule of §6.2 then applies. Cost of K: origins and node sizes, up to `Σ_{i≤K} w^i` symbolic origins for each base on a walk over `w` fields (§6.2). Measure `nodeCount` and `contentSize` for K = 3 and K = 7 in L4 before the decision. Contract item CK3 needs an unchanged query depth D. D is also the main knob of the alias answer volume (R0, D11 (b)). |
| D5 | Decided by the user | Must-alias | (a) derive from O (§8.4). (b) take the branch `origin/DanielELog/must_alias` (second DSU with a meet join). (c) none now. | (c): must-alias is postponed. Later work can derive it from O (a). It must keep the alias drop at unresolved calls (D2). | Main has no must analysis enabled. A derivation from O needs no second fixpoint, and `must ⊆ may` holds. The branch is on the old API, and its unfinished part can lose may-aliases (not verified). §8.4. |
| D6 | Decided by the user | Shared base class with Go | (a) extract an interface for the two queries. (b) copy: the JVM facade and the directed backend do not extend `LocalAliasAnalysis`; copy the helpers into the JVM module. | (b). The shared alias code and Go code do not change. | §8.3. The copies are the generic receiver helpers of `AliasUtil.kt` (M3, §7.4). Risk: the two copies of the helper loops can become different. |
| D7 | Decided by the user | Rollout | (a) mode switch `aliasAnalysisMode = DSU \| SHADOW \| DIRECTED`, default `DSU`, opt-in CLI; `SHADOW` for the volume gate (P9a); default `DIRECTED` after the conditions of §11.2 (P12); remove the DSU after one release (P13). (b) switch in one step. | (a): add the mode switch, default `DSU`. The value `SHADOW` follows the user input of 2026-10-29 on the volume (R0, D13). | Rollback by the mode switch (§11.5). L4 noise needs interleaved runs. |
| D8 | Open: the user decides after the spec revisit | State container | (a) fastutil copy-on-write. (b) `kotlinx.collections.immutable` persistent maps. | (a). Measure (b) only if the memory gate fails. | §7.11: no boxing, `joinO_work` per key. Memory is to be measured (§11.2). |
| D9 | Open: the user decides after the spec revisit | Unknown-origin signal for CS7 (M6) | (a) add `defaultConstraint` when `mayHoldUnknownObject` (both modes). (b) directed mode only. (c) no change. | (b) first, then (a) after a separate tms A/B | It closes the unsoundness of main that the directed precision makes visible (§9.1 CS7). (a) changes DSU results too, so measure it alone. |
| D10 | Open: the user decides after the spec revisit | The `cantMutateAliasedHeap()` exemption | (a) no exemption in directed mode: each unresolved call havocs. (b) keep the exemption for static calls with only primitive arguments; never for the receiver of `<init>`. | (a) | The exemption is outside the Lean model: such a callee can write statics. For a constructor it removes the receiver havoc, and two loads of one field of the new object then do not alias (§7.6). Cost: more havocs (R9). |
| D11 | Open: the user decides after the spec revisit and the shadow-mode measurement | Volume control (R0) | (a) No control: rely on the precision gains (non-transitive answers, D1, recency). Sound; keeps CK3. (b) Query depth D as the knob (`maxAccessors`, D4). Each answer stays complete up to the chosen D. A D smaller than 6 changes CK3: paths longer than D are not reported, which is unsound against main. (c) A deterministic per-query path budget (`maxQueryPaths`): shortest paths first, then the fixed comparator, and a `truncated` counter (§7.12 step 7). Unsound like the cut of main, but deterministic and measured; the cut of main depends on query order (§8.5). Changes CK3. (d) Simple paths only: a reported path never visits an origin two times. It cuts cyclic unrolling such as `x.next.next...`. It is a deviation from the answer set of the concept (`findAlias_iff` then gives only inclusion), so it needs a consumer-level argument or a measurement. Unsound in general: on a list of one summary origin, `x.next.next` can be a real alias. (e) The call drop of main as an A/B-only diagnostic flag in the may analysis (`diagnosticCallDrop`). It isolates the volume effect of D2. Not a default; D2 stands. Unsound (U2). | (b) and (c) are ready in the engine (P4); the measurement chooses between them and their values (§11.3 step 3). (e) for diagnosis only. (a) if the shadow volume gate holds without control. (d) only with a consumer-level argument. | R0 and the volume table (§11.1). Thresholds: the user sets them after the shadow-mode measurement (§11.2). Query cost bound: `searchCost_le`; `\|cells\|^D` output on cyclic heaps (§6.2). |
| D12 | Decided by the user | Inlining | (a) Keep inlining depth 1 in production. (b) No inlining in the directed engine. | (a). The user: "Inlining — yes, we keep inlining." | §3.4, §7.7, CK12. Production uses `experimentalAAInterProcCallDepth = 1`. |
| D13 | Decided by the user | The DSU on main | (a) Fix the DSU on main: the cache depth fix (commit `deff91ca0`, §8.5) and the removal of the call drop. (b) Keep the DSU of main as it is; document its defects. | (b). The user: "The issues are known, but we don't land the fix. The problem is the analyzer itself: after any of the fixes the AA starts producing way more alias chains, resulting in analysis explosion." So the cache-fix step is dropped, the A/B baseline is main as it is, and U1-U4, LT1 and the cache cut stay documented (§2, §8.5), not fixed. | User report: the explosion reproduces fast on thingsboard (taint facts, out-of-memory error). R0. P0c counts the volume of main and the cut of the cache, with no answer change. |

---

## Appendix A. Lean file index

Build and audit:

```
cd formal/directed-alias && ./check.sh
```

`check.sh` builds the package with `lake build` (Lean `v4.35.0`, no Mathlib). It fails on `sorry`, `admit`, `native_decide` or an `axiom` declaration. It regenerates `AxiomAudit.lean` and fails if a theorem depends on `Classical.choice`, `sorryAx` or `ofReduceBool`. Output for the full package: 1070 public theorems; 83 depend on no axiom, 362 on `propext`, 624 on `propext` and `Quot.sound`, 1 on `Quot.sound`; about 22.9k lines of Lean in about 70 build jobs. The call rule CN added 157 of these theorems. Concrete checks use `decide`, or `decide +kernel` for large terms. The kernel checks both. No check uses `native_decide`.

Constructive claims. `propext` and `Quot.sound` are in the Lean core. Without `Classical.choice` they do not give the excluded middle, and they do not stop `decide` from reducing. So each proof is constructive. Each example witness is an explicit choice list. The executor `runFrom` runs it, and `decide` checks the result (`runAliasB_sound`). Each completeness theorem also has a computable witness search (`crossWitness`, `witness_core`, `witness_store`, Sound/Witness/Search.lean, §4.7). In the two scopes, a true answer yields a witness that a reader can run with `#eval`.

The body gives each theorem with its claim. This index gives the files. "Other lemmas" are the supporting theorems that the body does not cite.

| File | Content | Cited in | Other lemmas |
|---|---|---|---|
| `Syntax.lean` | The IR: statements, programs, sites | §2.1, §4 | — |
| `ListSet.lean` | Lists as sets, `single?` | §4.3 | — |
| `Concrete.lean` | Concrete semantics (A1-A3, A2-wide), the executor `runFrom`. A2-strict is in `Sound/Havoc/Concept.lean`, A2-narrow in `Sound/CellNamed/Concept.lean`. | §3.1, §4.7 | `run_sound`, `runAliasB_sound` |
| `Concept.lean` | Concept C: origins, `adefault`, `astep`, `join`, `loopIter`, `may`, `mayProg`, `CSound`, `CCompleteIn` | §4 | `alphaV_cdefault`, `closeIter_spec`, `loopIter_post`, `sub_loopIter`, `may_iff`, `may_comm` |
| `Examples.lean` | Task and field examples | §1, §4.4 | `join_a_x`, `join_a_y`, `join_x_y`, `join_a_x_witness`, `join_a_y_witness`, `strong_bf_x`, `strong_bf_y`, `call_w_xf_witness`, `call_w_xf_overwrite` |
| `Sound/Invariant.lean` | The invariant `Inv`, the once budget | §4.5 | `Exec.cnt_le` |
| `Sound/Step.lean` | Local soundness of each statement | §4.5 | `unique_obj`, `reachB_of_reach`, `Inv.havoc` |
| `Sound/Soundness.lean` | Soundness of C | §4.5 | `mayProgE_true`, `analyze_sound`, `loop_keeps`, `inv_init`, `evalPath_sound`, `ctxE_ok` |
| `Sound/Recency/*.lean` | Recency concept, soundness, examples | §4.2, §1.8, §4.8 | `analyze_soundR`, `step_soundR`, `loop_bf_y`, `loop_bf_y_witness`, `crossB_sound`, `list_may`, `list_cross` |
| `Sound/Complete.lean`, `Sound/NullSafe.lean`, `Sound/StoreScope.lean`, `Sound/StoreExamples.lean` | Completeness scopes and the certificate | §4.7 | `nsafe_sound`, `nullSafe_safe` |
| `Sound/Boundary.lean` | Counterexamples CX1-CX7, the decision procedure | §4.8 | `pJoin_in_scope`, `pJoin_exact` |
| `Sound/EntryAlias.lean` | Entry aliasing: the accepted loss of D1 | §3.3 | — |
| `Sound/Facts.lean` | Symmetry, non-transitivity, the partition theorem | §1.5, §1.7, §4.4 | — |
| `Order.lean` (namespace `DirectedAlias.Order`) | The directed relation as a congruent order: `Above`, reflexive, transitive, antisymmetric on nodes, congruent; stores write down the order; may-alias derived from it; `symm_antisymm_eq`; the task and field examples (`join_order`, `field_order`) | §0, §1.7, §5.1 | — |
| `HavocNeed.lean` (namespace `DirectedAlias.HavocNeed`) | Why an unresolved call needs a havoc origin: two programs where an analysis without it misses a real alias (a later strong update; an empty cell), each with a concrete witness, and the answers of C and of recency with per-cell havoc | §4.9, §4.11 | `strong_after_call_nohavoc`, `empty_cell_nohavoc` |
| `Sound/Havoc/*.lean` (`Concept`, `Soundness`, `Fresh`, `Examples`, `ExamplesK1`) | A2-strict (`HavocS`, `ExecS`), per-cell havoc concept (`mayProgH`), soundness `csoundH`, freshness, the `pHv` examples | §3.1, §4.9 | `HavocS.toHavoc`, `keyOf_alphaS`, `alphaS_head`, `InvS.havocH`, `reachB_of_reachS`, `ctxH_ok`, `fresh_head`, `ExecS.hinv`, `strict_answers_K1`, `havoc_spread_exact`, `new_answers`, `loop_answers` |
| `Sound/HavocRecency/*.lean` (`Inv`, `Concept`, `Soundness`, `Examples`, `ExamplesK1`) | Recency with per-cell havoc (the precise reference; CN reuses `InvG`): the generic invariant `InvG`, the key `keyOfR`, soundness `csoundHR`, the cost of the shared key | §4.9, §7.9 | `InvG.retire`, `alphaRS_bump`, `alphaRS_head`, `InvG.havocHR`, `ctxHR_ok`, `no_alias_of_mayProgHR`, `strict_answersHR_K1`, `spread_with_recency_only`, `havocS_distinct` |
| `Sound/CellNamed/Concept.lean` | A2-narrow (`ReachN`, `HavocN`, `SStepN`, `ExecN`, `CAliasN`) and the CN concept: cell names (`childCN`, `extendCN`), coverage (`descB`, `coveredB`), the exposed test (`expB`, `uniqueCN`), the closure (`callRoots`, `succsN`, `closeN`), the call (`havocWith`, `havocCN`), `astepCN`, `originsCN`, `ctxCN`, `mayProgCN` | §3.1, §4.11 | `ExecN.toExecS`, `ExecN.toExec`, `CAliasN.toCAliasS`, `closeN_spec`, `mem_succsN` |
| `Sound/CellNamed/Names.lean` | Properties of cell names, descendants and the exposed test | §4.11 | `uniqueR_name`, `childCN_name`, `descB_iff`, `expB_mono`, `expB_renameL` |
| `Sound/CellNamed/Inv.lean` | The ghost naming `Names`, the abstraction `alphaCN`, the invariant `InvCN` (`InvG`, `InvX`, `CntOK`), the uniqueness lemma | §4.11 | `unique_objCN`, `not_havoc_of_unique`, `renameO_childCN`, `InvX.retire`, `InvCN.mono` |
| `Sound/CellNamed/Call.lean` | Soundness of the CN call: the written object has the name of its cell, coverage, unreachable cells are kept | §4.11 | `havocCN_sound`, `InvG.havocCN`, `reach_cover`, `reach_facts`, `expOK_closure`, `junk_kept`, `written_reach`, `namesAfter` |
| `Sound/CellNamed/Soundness.lean` | Soundness of CN: `csoundCN`, `no_alias_of_mayProgCN` | §4.5, §4.11 | `step_soundCN`, `loop_keepsCN`, `analyze_soundCN`, `inv_initCN`, `ctxCN_ok`, `ctxCN_frame`, `ctxCN_stmts`, `ctxCN_budget` |
| `Sound/CellNamed/Run.lean` | A computable executor for A2-narrow witnesses (`runAliasBN`) | §4.11 | `runAliasBN_sound`, `runN_soundN`, `applyHavocN_spec` |
| `Sound/CellNamed/Examples.lean` | The CN examples: HavocNeed, the spread, the dead-end case, the narrow-reach gain, the three losses, the other examples | §4.11 | `strong_after_call_realN`, `empty_cell_realN`, `spread_ab_noneN`, `spread_axf_keepN` |
| `Sound/CellNamed/Reference.lean` | Formal reference for the precision comparison only (not in the engine): the narrow per-cell reference `mayProgHRN` (not proved sound, F11) and the precision order on the examples | §4.11 | `precision_need`, `precision_old`, `precision_new` |
| `Sound/CellNamed/Scope.lean` | Both parts of A2-narrow are necessary; the precision order fails | §3.1, §4.11 | `generous_reach_breaks_CN`, `touch_noneN`, `generous_havoc_breaks_CN`, `precision_order_fails`, `nest_noneN` |
| `Sound/Witness/*.lean` (`Rename`, `Compact`, `Search`, `Examples`) | Computable witnesses for the completeness theorems: `crossWitness`, `witness_core`, `witness_store`, `oneWitness` | §0, §4.7 | `run_completeA`, `run_r`, `compact`, `checkW_sound`, `crossWitness_sound`, `crossWitness_complete`, `crossWitness_none_iff`, `arr_of_core`, `arr_of_store` |
| `DSU/Model.lean`, `DSU/Lemmas.lean`, `DSU/Props.lean` | The DSU model and its invariants | §2.1, §1.5, §1.7 | `dsuMayD_iff`, `DMayL_iff_short` |
| `DSU/Examples.lean` | DSU defects and the dominance boundary | §2.3, §2.4, §2.5 | `field_x_y_none`, `a1_witness`, `a2_witness`, `a4_witness`, `static_as_field`, `loop_bf_x_none` |
| `DSU/HeapFree.lean` | Heap-free soundness and dominance | §2.5 | `inv_sim`, `rel_sim`, `alias_good`, `aOk_loopFree` |
| `DSU/ConcreteFacts.lean` | Generic execution invariants | — | `exec_preserve`, `exec_loop_inv`, `exec_env_keep` |
| `DSU/Probes.lean` | The model against the measured Kotlin answers | §2.1, §2.3 | `s31_witness`, `s33_witness`, `s34_witness`, `sound_on_pJoin`, `dominates_on_pJoin`, `dominates_on_s7` |
| `Opt/Table.lean` | Node table | §5.1, §5.2 | `Tbl.Below.mem_sub` |
| `Opt/Prim.lean`, `Opt/Machine.lean`, `Opt/Equiv.lean` | O operations and O ≡ C | §5.3, §5.5 | — |
| `Opt/Support.lean` | Support of C | §5.5 | `Supp.astep`, `Supp.join`, `Supp.top`, `Supp.loopIter`, `Supp.analyze`, `ctxClosed_ofProg`, `progOK_ofProg`, `supp_ainit` |
| `Opt/Recency.lean` | O with recency | §5.5 | `renameL_congr`, `renameL_of_not_mem`, `renameL_dflt`, `renameL_sub`, `cval_retire`, `supp_retire`, `supp_storeR`, `supp_astepR`, `supp_analyzeR`, `ctxClosed_R`, `recOK_R`, `progOKR_R`, `supp_ainitR` |
| `Opt/Havoc.lean`, `Opt/HavocExamples.lean` | O with per-cell havoc (`havocHO`), `mayProgHO_eq` | §4.9, §5.5 | `analyzeHO_rel`, `callHO_rel`, `addHv_spec`, `addHv_work`, `Supp.havocH`, `ctxClosed_H`, `o_new_answers` |
| `Opt/HavocRecency.lean` | O with recency and per-cell havoc (`havocHRO`), `mayProgHRO_eq`, `csoundHRO` | §4.9, §5.5 | `havocHRO_rel`, `analyzeHRO_rel`, `addSets_spec`, `addHv_eq_addSets`, `addSets_work`, `o_cost`, `o_pHv`, `o_both` |
| `Opt/CellNamed.lean` | O with the call rule CN (`havocCNO`, `storeCNO`, `ostepCN`), the exposed set as the node of one reserved key, `mayProgCNO_eq`, `csoundCNO` | §5.3, §5.5 | `havocCNO_rel`, `storeCNO_rel`, `ostepCN_rel`, `analyzeCNO_rel`, `analyzeProgCNO_rel`, `o_answersCN` |
| `Opt/Examples.lean` | O examples | §5.4 | `o_join_a_x`, `o_join_x_y`, `o_strong_bf_x`, `o_loop_bf_x`, `o_call_w_xf` |
| `Opt/Cost.lean`, `Opt/LoopCost.lean` | Cost separations | §5.6 | `Tbl.intern_work`, `Tbl.union_self_work`, `Tbl.union_work`, `getId_work`, `jfold_work` |
| `Opt/Findings.lean` | Table growth and the fixpoint-test miss | §5.7 | — |
| `Opt/Query.lean`, `Opt/QueryFam.lean` | Backward search | §6 | `mem_hidx`, `mem_pre`, `mem_holders`, `mem_live`, `pathsUpTo_length_ge` |

Some short names occur in two files. Cite them with the file:

| Name | Files |
|---|---|
| `deep_none` | Sound/Boundary.lean, DSU/Examples.lean |
| `o_loop_bf_x` | Opt/Examples.lean (without recency), Opt/Recency.lean (with recency, namespace `RExamples`), Opt/HavocRecency.lean (recency with per-cell havoc) |
| `o_field` | Opt/Examples.lean (without recency), Opt/Recency.lean (with recency, namespace `RExamples`) |
| `loop_none` | Sound/Boundary.lean (CX7, the loop no-alias fact of this document), Sound/Havoc/Examples.lean (`pLoopHv` under A2-strict) |
| loop no-alias fact of the DSU | `loop_bf_x_none` (DSU/Examples.lean) |

---

## Appendix B. Probe index

All tests are in `JTEST/alias/DirectedAliasProbeTest.kt`; the sample is `DirectedAliasSample.java`. "Today" is the measured verdict on main. "Directed" is the expected answer under the default policy (§9.3): `entryUnique = true` (D1), recency on. The column was derived with per-cell havoc; for CN the rows with a call can differ (§9.3). In this column, `new(x)` is the `AliasAllocInfo` of the allocation of `x`, and `arg:p` is the argument path `p`. "Rec" marks sets that also depend on recency (D3). "Lean" is the related theorem.

| # | Probe test | Scenario | Today | Directed | Rec | Lean |
|---|---|---|---|---|---|---|
| 1 | `today join of two allocations makes x alias y` | PS1 | precision loss | flip: `alias(x) = {a, new(x)}` | | `join_x_y`, `dsu_join_x_y` |
| 2 | `today join of two arguments makes x alias y` | PS1 | precision loss | flip: `alias(x) = {a, arg:px}` | | `join_precision_loss` |
| 3 | `today field write through a join of allocations keeps x and y merged after the join variable is reassigned` | PS2 | same on fields, loss on bases | flip on bases; fields same | | `field_precision_loss`, `field_xf_z`, `field_yf_z` |
| 4 | `today field write through a join of arguments keeps x and y merged after the join variable is reassigned` | PS2 | same | flip on bases | | same |
| 5 | `today store through a join of allocations is visible through the other variable` | PS9 | sound | same | | — |
| 6 | `today store through a join of arguments is visible through both argument paths` | PS9 | sound | same | | — |
| 7 | `today correlated branches make a alias b` | PS6 | same | same | | — |
| 8 | `today loop reassignment makes a alias b` | PS7 | precision loss | flip: `alias(a) = {cur, new(a)}` | | `dominates_on_s7`, `s7_matches` |
| 9 | `today heap chain load aliases the stored value` | PS8 | sound | same | | `s8_matches` |
| 10 | `today load through a join of two arguments makes p value alias q value` | PS8 | precision loss | flip: `alias(pv) = {arg:p.value, t}` | | — |
| 11 | `today pass-through models of two arguments into one result make x alias y` | PS5 | precision loss | flip: `alias(x) = {arg:px, r}` | | — |
| 12 | `today without pass-through models the call result is unrelated to the arguments` | PS5 | sound | same (`alias(r)`: `null` becomes empty) | | — |
| 13 | `today strong update on a loop allocation site drops the previous object field after an invalidated load` | PS3.1 | unsound | flip: `alias(seen) ∋ prev.value`, `alias(prev) ∋ arg:h.box` | yes | `a2_unsound`, `s31_matches` |
| 14 | `today strong update on a loop allocation site in a constructor drops this value and the previous object field` | PS3.2 | unsound | flip: `alias(seen) ∋ prev.value, this.value`; `alias(cur) ∌ this` | yes | `a4_unsound` |
| 15 | `today strong update on a join of constructor this and an allocation drops this value` | PS3.3 | unsound | flip: `alias(seen) ∋ this.value, n.value` | | `a3_unsound`, `s33_matches` |
| 16 | `today strong update on a join of an invalidated load and an allocation drops the load field` | PS3.4 | unsound | flip: `alias(seen) ∋ p.value, n.value` | | `a1_unsound`, `s34_matches` |
| 17 | `today allocated predecessor blocks the loop strong update` | PS3.5 | sound | same under C; smaller with recency | yes | `a2new_blocked` |
| 18 | `today null predecessor blocks the loop strong update` | PS3.5 | sound | same under C; smaller with recency | yes | `a2null_blocked` |
| 19 | `today argument predecessor blocks the loop strong update` | PS3.5 | sound | same under C; smaller with recency | yes | `a2arg_blocked` |
| 20 | `today call return predecessor blocks the loop strong update` | PS3.5 | sound | same under C; smaller with recency | yes | — |
| 21 | `today unknown call on the argument removes the loaded field alias` | PS4 | unsound | flip: `alias(w) = {arg:x.value}` | | `b_unsound`, `call_w_xf` |
| 22 | `today unknown call on the local allocation removes the loaded field alias` | PS4 | unsound | flip: `alias(w) ∋ x.value` | | `b_local_unsound` |
| 23 | `today unknown call on an unrelated argument keeps the field alias of an argument used directly` | PS4 | sound | same | | — |
| 24 | `today unknown call on an unrelated argument removes the field alias of an argument copied to a local` | PS4 | unsound | flip: `alias(w) ∋ x.value, arg:px.value` | | `s4copied_matches` |
| 25 | `today unknown call on the argument removes the loaded final field alias` | PS4 | unsound | flip: `alias(w) = {arg:x.value}` | | — |
| 26 | `today unknown call on the local allocation keeps the loaded final field alias` | PS4 | same on path | same on paths (depth 0) | | — |
| 27 | `today jdk call on the argument removes the loaded field alias` | PS4 | unsound | flip: `alias(w) = {arg:x.value}` | | `b_unsound` |
| 28 | `today static field write is ignored so the static read does not alias the written value` | PS10 | unsound | flip: `alias(t) ∋ v, new(v)` | | `static_unsound`, `static_as_field` |
| 29 | `today this field write in a constructor is a strong update` | PS11 | same | same (default `entryUnique = true`); weak with `false` (precision loss) | | — |
| 30 | `today this field write in a method is a weak update` | PS11 | precision loss | flip (default `entryUnique = true`): `alias(t) = {v2, arg:p2, this.value}`; same with `false` | | `root_concept_more_precise` |
| 31 | `today a source self assignment leaves no self copy in JIR and x keeps z` | PS12 | shape not produced | same | | `self_copy_unsound` (latent) |
| 32 | `today a source self assignment of an argument copy leaves no self copy in JIR and x keeps z` | PS12 | shape not produced | same | | same |
| 33 | `today a self cast gets a new JIR local and x keeps z` | PS12 | shape not produced | same | | — |
| 34 | `today JIR of jdk and sample classes has no self copy and no load into its own instance` | PS12, PS13 scan | 0 of 5914 | does not depend on the mode | | — |
| 35 | `today load into the live root of the instance group makes a self loop and drops the aliased load` | PS13.1 | unsound, and a false chain | flip: `alias(x) = {w, arg:p.next}` | | `repr_unsound`, `repr_self_loop` |
| 36 | `today load into the live root of the instance group without a prior load makes a self loop` | PS13.1 | unsound, and a false chain | flip: no `x.next^k` | | same |
| 37 | `today conditional load into the root merges p with its next chain` | PS13.2 | precision loss | flip: `alias(w) = {arg:p.next, x}` | | `repr_partition_ok` |
| 38 | `today load into a dead local after a copy keeps the aliased load` | PS13.3 | sound | same | | — |
| 39 | `today JIR splits a load into a live local through a temporary and the aliased load is kept` | PS13.3 | sound | same | | — |
| 40 | `today self load in source gets a JIR temporary and the aliased load is kept` | PS13.3 | sound | same | | — |
| 41 | `today linked list walk merges cur with head and every next chain` | PS13.4 | precision loss | flip: `alias(cur) ∋ arg:head.next^k`, no `cur.next^k` through `head` | | — |
| 42 | `today linked list walk merges cur with the second node` | PS13.4 | precision loss | flip: `second ∌ arg:head` | | — |

Totals under the default policy: §9.3. The six "Rec" rows need the oracle for their exact sets. The sets of rows 13-16 and 19 also depend on `entryUnique` (§9.3).
