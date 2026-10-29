# Directed alias analysis for the JVM: design proposal

Status: proposal. Base: main `f945f92c5`. The formal model `formal/directed-alias/` (Lean 4, constructive) and the probe suite `DirectedAliasProbeTest` are not committed yet. Step P0 commits the probe suite, and step P0a commits the model and this document (§10.2).

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
| site havoc origin `havoc(s)` | All objects that call site `s` writes, and all objects below them. Mode `SHARED` uses it. | `havoc s` | `HAVOC_SITE` |
| per-cell havoc origin `havocC(s, k, c, q)`, `havocDeep(s, k, c)` | The new object that call site `s` writes into cell `c` of a holder with key `k`, and the tree below it. Mode `PER_CELL` uses it (§4.9). | `hsym s k c q`, `hdeep s k c` | `SYM`, `DEEP` over a `HAVOC_CELL` base |
| constant origin | One origin for each box type, class literal or string value (§7.5). | none | `BOX_CONST`, `CLASS_CONST`, `STRING_CONST`, `SITE_CONST` |
| holder | A variable, or a heap cell `(o, c)` of origin `o` and cell `c`. | `Key` (`v x`, `h o c`) | `VarId`, `HeapKey` |
| points-to set `pts(p)` | The origins that the access path `p` may hold. | `aevalPath` | `valueOf`, `load` |
| may-alias, `p ~ q` | `pts(p) ∩ pts(q) ≠ ∅`. | `may` | `findAlias` |
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
| strong-update policy `entryUnique` | `true`: symbolic origins of entry paths and of once-site results are unique. `false`: only allocation origins of once sites (and `alloc-new`) are unique (§3.2). | `Ctx.entryUnique`, `eu` | `DirectedAliasPolicy.entryUnique` |
| entry root | `this`, an argument, or a static root at method entry. | `Base.root r` | `ROOT_THIS`, `ROOT_ARG`, `ROOT_STATIC` |
| unresolved call | A call that the analysis does not inline. | `call s args` | `Stmt.Call` without a resolved callee |
| A2-wide | Concrete call semantics: one call can write one new object into many cells (§3.1). | `Havoc`, `Exec` | — |
| A2-strict | Concrete call semantics: one call writes a distinct new object into each cell that it changes (§3.1). | `HavocS`, `ExecS` | — |
| havoc mode `SHARED`, `PER_CELL` | The abstract call rule: site havoc origins (sound for A2-wide), or per-cell havoc origins (sound for A2-strict). | `astep`, `astepH` (with recency: `astepR`, `astepHR`) | `HavocMode` |
| havoc layer | The record of unresolved calls in a state. It replaces explicit havoc writes (§7.6). | none | `havocOuter`, `havocAlloc`, call-site lists |
| origin depth K | The depth limit of symbolic origins. | `Ctx.K` | `symDepth` |
| query depth D | The maximum number of accessors of a reported path. | `findAlias D` | `maxAccessors` (main: `HEAP_CHAIN_LIMIT = 5`, which allows 6 accessors) |
| inlining depth | The number of call levels that the analysis inlines. | none | `aliasAnalysisInterProcCallDepth` |
| heap map | The map of the written cells of a state. | `OState` entries `h o c` | `DirectedState.heap` |
| universe | The finite set of origins, variables and cells of one analysis. | `ctx.origins`, `ctx.vars`, `ctx.cells` | the tables |
| once site, loop site | A site that occurs at most one time and not under a loop; a site on a cycle. | `Prog.onceB` | `SiteTable.isLoopSite` |
| change bit | The result bit of an O join: true if the state grew. | `joinO_flag` | `Joined.changed` |
| exactness certificate | A check on the abstract states that puts a program in the certified store scope (§4.7). | `bcert` | `DirectedAliasStats.exactMethods` |
| flip | The `directed` answer of a probe differs from its `today` answer. | — | — |

Technical verbs: **intern** (find the id of a set in the node table, or add the set); **memoize** (store a result under its inputs); **retire** (rename `alloc-new(s)` to `alloc-old(s)`, §4.2); **havoc** (apply the effect of an unresolved call).

### Identifier families

| Ids | Meaning | Section |
|---|---|---|
| A1-A3 | Scope assumptions | §3.1 |
| CK1-CK13 | Contract items of the alias API | §8.1 |
| CS1-CS8 | JVM consumers of the alias analysis | §8 |
| CX1-CX7 | Counterexamples at the completeness boundary | §4.8 |
| D1-D10 | Decisions for the user | §12 |
| F1-F9 | Lean follow-ups | §11.4 |
| G-JVM, G-CORE, G-QL, G-ROOT, G-LEAN | Test gates | §10.2 |
| L0-L4 | Test layers | §10.1 |
| M1-M8 | Consumer changes | §8.2 |
| P0-P13 | Implementation steps (one pull request each), with P0a and P0b | §10.2 |
| PL1-PL7, U1-U4, LT1 | DSU defects: precision losses, unsound defects (U1 has shapes U1.a1-U1.a4), one latent defect | §2.3 |
| PS1-PS13 | Probe scenarios | §2.2, Appendix B |
| R1-R16 | Risks | §11.1 |

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
| thingsboard | ThingsBoard, a large Java IoT platform in the end-to-end suite (`opentaint-test/opentaint-test-thingsboard`). Its scan is memory bound at 8 GB. |
| dataflowbench | `BrokkAi/dataflowbench`, a public data-flow benchmark with an OpenTaint adapter. It has 58 Java and 58 Kotlin assertions. |

---

## 0. Summary

**Problem.** Today, the JVM local alias analysis is a disjoint-set union (DSU) with congruence closure. A DSU state is a partition, so its alias relation is transitive. Assignments have a direction, and the DSU loses it (§1).

**Decision.**

1. Replace the DSU with concept C: points-to sets keyed by origin. May-alias is set intersection (§4).
2. Implement C as optimization O: hash-consed origin-set nodes with a union memo (§5).
3. Answer queries with a backward search over a lazy reverse index (§6).
4. Use two CEGAR steps: recency for allocation sites in loops, and per-cell havoc origins for unresolved calls (§1.7).
5. Ship the engine behind the mode switch `aliasAnalysisMode = DSU | DIRECTED`. The default stays `DSU` until the gates of §11.2 pass.

**Results.**

| Area | Result | Status |
|---|---|---|
| Soundness | Each one-execution alias is a may-alias of C, for each K and both policies, with and without recency, under A1-A3 (§4.5). This is mode `SHARED` under A2-wide. Mode `PER_CELL` is sound under A2-strict, without recency (`csoundH`) and with recency (`csoundHR`, the default policy) (§4.9). | proved |
| Completeness | C is exact in two checkable scopes without loops and calls: the store-free core and certified stores (§4.7). In both scopes, a computable search gives the witness pair of executions (`crossWitness`, `witness_core`, `witness_store`). | proved |
| Partition limit | No sound transitive relation separates `x` and `y` in the task example. No DSU can be exact (§1.5). | proved |
| DSU defects | 4 unsound defects (U1-U4), 1 latent defect (LT1), 7 precision losses (PL1-PL7) (§2.3). | proved, measured |
| O ≡ C | O and C give the same may-alias answers for the variables of the program and the frame: with and without recency, and with per-cell havoc with and without recency (§5.5, §4.9). | proved |
| Cost | On three program families, O is linear where C is a product or exponential (§5.6; state size counts map entries only). Cost relative to the DSU: §5.8. | proved; argued |
| Audit | No `Classical`, no `sorryAx`, no `ofReduceBool` (Appendix A). | checked |

**Limits.**

1. Entry aliasing breaks each local analysis that separates entry roots. The DSU has the same limit (§3.3).
2. Loops and calls are in no completeness scope (§4.8).
3. The default policy (recency with per-cell havoc) is proved sound only under A2-strict: a callee does not write one object into two cells (§4.9). Under A2-wide, mode `SHARED` is the proved mode.
4. The node table can hold Θ(m²) set elements on a join chain of m allocations (§5.7).

**Decisions.** §12 gives ten decisions for the user (D1-D10). For each decision, it gives the options, a recommendation and the evidence.

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

Concept C keeps a directed graph. An edge goes from a holder to each origin that the holder may hold. A copy `a = x` adds the edges of `x` to `a`. In the notation of the task, `a -> x` means `pts(a) ⊇ pts(x)` after the copy.

Task example, after the join:

```
  holders           origins
    x  ───────────►  ox
    a  ──┬────────►  ox
         └────────►  oy
    y  ───────────►  oy
```

`pts(x) ∩ pts(a) = {ox}`: alias. `pts(a) ∩ pts(y) = {oy}`: alias. `pts(x) ∩ pts(y) = ∅`: no alias. The relation is symmetric and not transitive.

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

Consequence: a better DSU cannot fix the task example. The relation must not be transitive.

### 1.6 Goal

| Goal | Measure |
|---|---|
| Precision | Non-transitive may-alias. Exact across executions in the largest checkable scope. |
| Soundness | Sound under A1-A3 (§3) for each program of the IR. |
| Efficiency | Join and fixpoint test by node ids. Query cost bounded by output size times depth. State size relative to the DSU: measured in L4 (§5.8, §11.2). |
| Separation | Concept C and optimization O are separate. O is proved equal to C. |

### 1.7 Method

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
| 2. Per-cell havoc | `pHv = m(x); a = x.f; b = y.g`, query `a ~ b` (§4.9). | One site havoc origin for each call. Under A2-wide the alias is real. | First, narrow the call semantics from A2-wide to A2-strict. The soundness claim then covers fewer callees. Second, refine the abstraction: per-cell havoc origins. Mode `SHARED` stays available for A2-wide. | A2-strict (§3.1) | `csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `strict_answers`, `strict_ab_none`, `generous_breaks_strict` (§4.9) |
| 3. Store certificate | CX4-CX6: correlated control and correlated values break "a strong store is exact" (§4.8). CX3: null blocking. | A per-variable domain has no correlation. | Completeness scopes with checks: the null-kind check (`nullSafeB`) and the certificate `bcert` (§4.7). | Completeness only; soundness does not change. | `ccomplete_coreB`, `ccomplete_store` |

Design bugs of the new design. The Lean model, a hand evaluation of its definitions, or a review of the design against the model found each bug before the implementation.

| First design | Counterexample | Change | Section |
|---|---|---|---|
| The fixpoint test is "state equal to the old state". | The transfer is not monotone (`astep`: a store with `pts(x) = ∅` against `{o}`). A copy-on-write add and remove gives a new object with equal content. | The change bit of the join is the signal (`joinO_flag`). | §7.10 |
| One site havoc origin for each call. | `pHv`: a value loaded after a call may-aliases each outer path. | Per-cell havoc origins under A2-strict. | §4.9 |
| `entryUnique = true` is sound. | Entry aliasing: `skip_unsound`, `write_read_unsound`, `swap_strong`. | Document A1. Default `entryUnique = false` (D1). | §3.3 |
| "Each strong store is exact." | CX4, CX5 (`corr_none`, `strongTwo_none`); null blocking CX3 (`block_none`). | Certified store scope with null kinds. | §4.7, §4.8 |
| K = D. | `deep(b)` holds itself in each cell. After a long list walk the query output is `\|cells\|^D`. | K ≥ D + 1, and the search never expands a self edge of a deep origin. | §6.2, §6.4 |
| A flat CFG worklist with accumulating loop heads. | Nested loops with strong stores: the inner head keeps stale entry states. | Recursive WTO iteration; new state arrays for each callee evaluation. | §7.10 |
| Keep the `cantMutateAliasedHeap()` exemption. | A constructor call with no reference argument does not havoc its receiver. Two loads of one field of the new object then do not alias. | An unresolved `<init>` always havocs its receiver. | §7.6 |
| The catch state is the state after the thrower. | A throwing instruction does not do its effect. | Catch edges use the join of the states before and after the thrower. | §7.10 |
| The catch variable is an allocation with null cells. | Fields of a caught exception read as null. | The catch variable gets a fresh symbolic origin. | §7.5 |

---

## 2. The DSU on main

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
- Main also has a query-order defect outside the analysis: the conversion cache key has no depth, so heap chains can be cut (§8.5).

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

On a root store, C with `entryUnique = true` is more precise than the DSU: `root_concept_more_precise`.

---

## 3. Scope and assumptions

### 3.1 Assumptions built into the concrete semantics

The concrete semantics (`Concrete.lean`) builds A1-A3 in. So the soundness theorems have no extra hypothesis.

| Id | Assumption | How `Concrete.lean` builds it in |
|---|---|---|
| A1 | No entry aliasing. Entry roots are distinct objects. The entry heap below them is a tree. Objects that unknown expressions and calls return are new, with a tree below them. | `Obj.sym (Base.root r) p`: distinct root ids give distinct objects. `cdefault`: cell `c` of `sym b p` holds `sym b (p ++ [c])`. `Base.fresh s n` for results. |
| A2 | An unresolved call returns a new object. It keeps each cell, or writes a new object into a cell of a reachable object. It never makes existing objects alias. Two forms exist: A2-wide and A2-strict (below). | A2-wide: `Havoc st args s n h'`: `h' o c = st.heap o c`, or `Reach st args o` and `h' o c = sym (havoc s n k) []`. A2-strict: §4.9. |
| A3 | Origin depth limit K for symbolic objects. The abstraction maps each deeper object to one origin `deep(b)`. | Only in the abstraction: `alpha K` maps paths longer than K to `deep b`. Concrete paths have no limit. |

The two forms of A2:

| Form | Rule | Abstract mode | Sound for |
|---|---|---|---|
| A2-wide | One call can write the same new object into several cells (free tag `k`). | `SHARED`: one site havoc origin `havoc(s)` | A2-wide and A2-strict |
| A2-strict | One call writes a distinct new object into each cell that it changes. | `PER_CELL`: per-cell havoc origins | A2-strict only (§4.9) |

A2-strict is narrower. Under it, the soundness claim covers fewer callees. Out of scope under A2-strict: a callee that writes one new object into two cells, for example `void m(A x, B y) { Object o = new Object(); x.f = o; y.g = o; }`. The DSU also misses this shape (§4.9). For such callees, only the taint analysis of the callee itself gives cover (§3.4).

Other properties of the concrete semantics:

| Property | Rule | Reason |
|---|---|---|
| Null dereference | A load or store through null **blocks** (no step). | Exceptions are out of the model (§3.4). |
| Array index | `aload`/`astore` take any index `i`. | Array cells are not separated. |
| Wide reach | `Reach` makes each symbolic object reachable by the callee. This includes entry objects that the method detached, and objects that a later unknown expression or call returns (the heap is total). | It matches the DSU idea "groups with outer elements". It makes A2-wide wider again. |
| Sites | Counter `cnt s` for each site. The n-th run of `new@s` makes `alloc s n`. | Distinct objects for each run. |

### 3.2 Parameters of the abstraction

| Parameter | Meaning | Lean |
|---|---|---|
| K | Origin depth: `sym(b, q)` with `\|q\| ≤ K`, else `deep(b)`. | `Ctx.K`, `symOrDeep` |
| `entryUnique` | Strong-update policy for symbolic origins. `true` (A1): unique entry paths and unique once-site results get strong updates. `false`: only allocations of once sites (and `alloc-new`) get strong updates. `false` is the intended policy of the DSU for outer bases. The measured DSU also strong-updates constructor `this` and summary sites (U1, §2.4). | `Ctx.entryUnique` (Concept.lean) |
| recency | Two origins for each allocation site: the most recent object and all older objects. | Sound/Recency/Concept.lean |
| D | Query depth: the number of accessors of a reported path. | `findAlias D` (Opt/Query.lean) |

K and D are different limits. K bounds the origin universe. D bounds the output paths. The design uses K ≥ D + 1 (§6.4).

### 3.3 Entry aliasing

A1 is a real restriction. The model shows that no local analysis can remove it.

| Claim | Status | Theorem (Sound/EntryAlias.lean) |
|---|---|---|
| The empty program aliases `x` and `y` if both are one root. Both policies answer no. | proved | `skip_unsound` |
| `x.f = z`: `y.f` aliases `z`. Both policies answer no. The missing alias is on the **read** side, so weak stores do not help. | proved | `write_read_unsound` |
| `swapFields(box, box)` aliases the two values. The policy `entryUnique = true` answers no (unsound). The policy `false` answers yes, because the kept old value is the entry value. | proved | `swap_alias`, `swap_strong`, `swap_weak` |
| On the exact concrete frame of the execution (`frC`), both policies answer yes. | proved | `write_read_quotient`, `swap_quotient` |

Result: without caller information, no local analysis that separates two entry roots is sound under entry aliasing. Both policies are unsound there. The policy `true` also loses aliases that the policy `false` keeps (`swap_strong`, `swap_weak`). No theorem orders the two policies in general.

The Lean quotient result needs the **exact** concrete root partition (`frC`). A caller partition that is only a may-partition (roots that are equal in some calls) makes a merged root denote two objects. Such a root is not unique. Use weak stores on merged roots, or analyze one time for each exact partition. This extension is not proved. The DSU has the same limit, because it also separates distinct arguments (argued).

### 3.4 Out of scope

| Item | Status | Reason |
|---|---|---|
| Exceptions | out of the Lean model | A null dereference blocks. The engine joins the states before and after each thrower on catch edges (§7.10), and gives the catch variable a fresh symbolic origin (§7.5). Both rules are argued. |
| Inlining of callees | out of the Lean model | Production uses inlining depth 1. An inlined callee body is ordinary IR, so C applies to it (argued). §7.7 gives the design. |
| Callee-made aliasing of existing objects | out | A2 allows only new havoc objects. Example: an unresolved `m(x, y) { x.f = y; }`. The IFDS taint analysis covers a resolved callee through its own summary, and a library callee through its pass-through rules (argued). §9.1 lists the effect. |
| One new object in two cells | out under A2-strict | §3.1. Mode `SHARED` covers it. |
| Entry aliasing | out | §3.3. |
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

Concept C makes only the first four kinds. The per-cell refinement (§4.9) makes the last two.

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
| `havoc(s)`, `havocC`, `havocDeep` | false |

Recency (Sound/Recency/Concept.lean): `alloc-new(s)` (Lean `rNew s`, encoded `alloc (2s)`) is the most recent object of site `s`. `alloc-old(s)` (Lean `rOld s`, encoded `alloc (2s+1)`) is all older objects.

| Origin | `uniqueR once entryUnique` |
|---|---|
| `alloc-new(s)` | true, for each site, also in a loop |
| `alloc-old(s)` | false |
| other | `uniqueB once entryUnique` |

`retire s X`: rename `alloc-new(s)` to `alloc-old(s)` in each value. Move the cells of `alloc-new(s)` into the cells of `alloc-old(s)` (union). Give `alloc-new(s)` empty cells.

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
| `x = call@s(args)` | havoc: `H(o, c) ∪= {havoc(s)}` for each universe cell `c` and each `o` with `reachB o`. Then `pts(x) := {sym(fresh s, [])}`. Mode `PER_CELL`: §4.9. | havoc, then `retire s`, then the same |

The strong-update condition, as in Lean (`AState.store`):

```lean
match single? (X.env x) with
| some o => if o.uniqueB once entryUnique then X.setCell o c S else X.weakStore (X.env x) c S
| none   => X.weakStore (X.env x) c S
```

`single? l = some o` if `l` is not empty and each element is `o`. So `[o, o]` counts as one origin. With `pts(x) = ∅` the store does nothing. This is sound, because the concrete store blocks.

Reach of a call (`reachB ctx X args`): `o` is reachable if `o` is outer, or if `o` is in the closure of `pts(args) ∪ {outer universe origins}` under all universe cells. If the closure does not converge within its fuel, each origin is reachable.

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
| `csound K` | `CSound K` for each K (`entryUnique = true`). | Sound/Soundness.lean |
| `csoundE eu K ...` | The same for both policies (`mayProgE eu`). | Sound/Soundness.lean |
| `csoundR eu K ...` | The same with recency, both policies (`mayProgR eu`). | Sound/Recency/Soundness.lean |
| `csoundH src eu K ...` | Mode `PER_CELL` without recency (`mayProgH eu`): each one-execution alias under A2-strict (`CAliasS src`), for each tag naming `src`, is a may-alias. Both policies. | Sound/Havoc/Soundness.lean |
| `csoundHR src eu K ...` | Mode `PER_CELL` with recency (`mayProgHR eu`), the default policy. The same statement. | Sound/HavocRecency/Soundness.lean |

The first three theorems use A2-wide (`CAlias`). `csoundH` and `csoundHR` use A2-strict, and they do not hold under A2-wide (`generous_breaks_strict`, §4.9).

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

Soundness has no hypothesis beyond the concrete semantics: A1-A3, one thread, no exceptional flow, and callees that write only new objects (A2-wide for `SHARED`, A2-strict for `PER_CELL`).

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

The completeness theorems use the policy `entryUnique = true`. Completeness of recency is not proved. With the default `entryUnique = false`, the store-free core does not depend on the policy, because it has no store (argued). The certified store scope then accepts only stores on unique allocation origins (argued).

Witnesses. Each example witness is an explicit choice list (the branch choices of one execution). The executor `runFrom` runs it, and `decide` checks the result (`runAliasB_sound`, Concrete.lean). For example, `field_xf_z_witness` is `runAliasB_sound (cs := [.left]) (by decide)`. Executable witnesses for the completeness theorems (Sound/Witness/). The theorems above conclude a Prop-level `∃`, which Lean cannot run. So the model adds a computable search `crossWitness fr p x px y py`. It tries every choice list of a loop-free, call-free program and every concrete path that abstracts to the query paths, with array indices below a fixed bound. It returns the first pair of executions that aliases the two paths. `crossWitness_sound`: each result is a cross-execution alias. `crossWitness_complete`: for each loop-free, call-free program, each cross-execution alias makes the search succeed, so `crossWitness_none_iff` decides `NoCrossAlias`. `witness_core` and `witness_store`: in the core scope and in the certified store scope, `mayProg = true` makes the search succeed. `coreWitness` and `storeWitness` return the witness as a value (`coreWitness_spec`, `storeWitness_spec`). `oneWitness` is the same search for one-execution aliases (`oneWitness_sound`, `oneWitness_complete`). Example: on `pJoin`, the search returns the choice lists `[left]`, `[left]` for `a ~ x`, and `none` for `x ~ y`. Loops and calls are outside the search; it then returns `none`, which stays sound.

Exactness certificate as an analysis output (argued). `bcert` reads only the abstract states and the null kinds. The engine can compute it in the same pass. Proposed uses:

- an exactness result for each method and query depth: true if the method has no loop and no call, and is in a scope for paths up to that depth;
- a test oracle: if the result is true, each reported may-alias must have a witness pair of executions;
- a precision metric: the share of methods (and of queries) with exact answers (`DirectedAliasStats.exactMethods`, §11.2).

The next scope to prove is "the core plus unresolved calls under A2-strict" (F6). Calls are the most common reason that a method is outside the proved scopes.

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

Calls are in no proved scope. No completeness counterexample for calls exists. Under A2-wide, any reachable cell can get a havoc object, so we expect that each abstract `havoc(s)` edge has a concrete execution. No proof exists. Status: open (F6). §4.9 shows that A2-wide is not the right target for calls.

### 4.9 CEGAR step 2: per-cell havoc origins

This step has two parts. First, it narrows the concrete call semantics from A2-wide to A2-strict. This is a scope change, not an abstraction error: under A2-wide, the aliases of the counterexample below are real. After the change, the soundness claim covers fewer callees. Second, it refines the abstraction, so that C keeps its precision under A2-strict. Mode `SHARED` stays in the engine, and it stays sound for A2-wide (§7.6).

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
| Recency with per-cell havoc (the default policy) is sound under A2-strict, both policies | `csoundHR` (shared invariant `InvG`; new step `InvG.havocHR`) | proved |
| The key does not depend on the site counter, so `retire` never renames a per-cell havoc origin | `keyOfR_alphaRS` | proved |
| O equals the concept, per-cell havoc | `mayProgHO_eq`; cost of one call `addHv_work` | proved |
| O equals the concept, recency with per-cell havoc; so O is sound | `mayProgHRO_eq`, `csoundHRO` | proved |
| On `pHv`, the spread is gone: `a ~ b`, `a ~ z.f`, `a ~ w.g` are false; `a ~ x.f` stays true | `strict_answers`, `strict_ab_none`, `strict_az_none`, `strict_axf_keep`, `strict_axf_new` | proved |
| Under A2-wide, the spread is real, so the refinement needs A2-strict | `spread_real_ab`, `spread_real_az`, `generous_breaks_strict` | proved |
| `loop_bf_x` stays exact with both refinements | `loop_bf_x_exactHR` | proved |
| The default needs both refinements: on `pBoth = loop { b = new@7; b.f = x; b.f = y }; m(x); a = x.f; c = y.g`, only the combination answers `b.f ~ x` and `a ~ c` false, and both are exact | `both_answers`, `both_bf_x_none`, `both_a_c_none` | proved |
| The shared key `alloc-old(s)` is sound, and it has a precision cost: `o = new@7; b = new@7; m(b, o); t = b.f; u = o.f` answers `t ~ u` true, but no strict execution aliases them. Recency alone and per-cell havoc alone also answer true, so this is no regression against a proved configuration | `keyOfR_alphaRS`, `csoundHR`; `cost_answers`, `cost_none` | proved |
| "The combination is at least as precise as each refinement alone" | none (evidence: all examples) | open (F6) |
| A finer key (the current recency origin of the holder) removes the `cost_answers` alias | none (`retire` must then rename and merge per-cell havoc origins) | open (F6) |
| A more precise rule for havoc-derived holders: the new object goes into the tree of its holder, with no new origin | none. The proved rule is the model rule of the Key row; §7.6 uses it. | open (F1) |
| Completeness for calls | none | open (F6) |

Effect: on `pHv`, `a ~ b`, `a ~ z.f` and `a ~ w.g` become false. The old content of each cell stays, so the fix of U2 stays. This is decision input to D2 (§12).

### 4.10 Precision relative to the DSU

| Program | C | DSU | Exact answer | Evidence |
|---|---|---|---|---|
| task example, `x ~ y` | no | yes | no | `join_precision_loss` |
| field example after `a = w`, `x ~ y` | no | yes | no | `field_precision_loss` |
| field example, `x.f ~ z`, `y.f ~ z` | yes | yes | yes | `dsu_field_xf_z`, `field_xf_z` |
| root store `x.f = y; x.f = z`, `x.f ~ y`, policy `entryUnique = true` | no | yes | no | `root_concept_more_precise` |
| loop strong update, `b.f ~ x` | yes (C), no (recency) | no | no | `loop_dsu_more_precise`, `loop_bf_x_exact` |
| K = 1, `x.f.f ~ x.f.f.f` | yes | no | no | `deep_concept_imprecise` |
| U1-U4 | yes (sound) | no (unsound) | yes | §2.3 |
| `pHv`, `a ~ b` after a call | yes (`SHARED`), no (`PER_CELL`) | no | no under A2-strict | §4.9 |

Recency keeps the other answers (`join_answers`, `field_answers`, `strong_answers`, `call_answer`, Sound/Recency/Examples.lean). Not proved: "recency is at least as precise as C" in general (F6).

---

## 5. Optimization O

### 5.1 Idea

O shares origin sets in the way that congruence closure shares classes, but it keeps the direction.

| Congruence closure (DSU) | O |
|---|---|
| A node is an equivalence class. | A node is a canonical origin set. |
| A union merges two classes in place. The operands are lost. | A union makes a **new** node. Its two children are the operands. The operands stay. |
| Holders in one class are one holder. | Each holder points to its own node. Holders never merge. |
| Congruence: the work on a class is shared by all its members. | O shares **sets** (hash-consing), but not **loads**. A load through a node is a memoized union over the cells of its member origins. It does not reuse the loads of the two children of the node. |
| State equality is partition equality. | State equality is node-id equality. |

DAG view: an edge `u -> v` means `L(u) ⊇ L(v)`. The denotation of a node is the set of leaves below it.

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
| call havoc | `havocO` (`SHARED`): `reachB` on the denotation, then add the node `{havoc(s)}` to each reachable universe cell. `havocHO` (`PER_CELL`): the same reach test, then add the interned node `{havocC(s, keyOf(o), c, [])}` to each reachable universe cell `(o, c)` (`addHv`). | one union for each cell |
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

The kid edges of O are the arrows of the task: `a -> x` is the edge `n3 → n1`.

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

O soundness without recency is a composition: `csoundE` and `mayProgOE_eq`. The two `mayProgE` definitions (`Sound.mayProgE`, `Opt.mayProgE`) are equal by unfolding. For this configuration, no single theorem states "a one-execution alias is an O may-alias" (F9). For the default configuration, `csoundHRO` states it (below).

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
| `mayProgHRO_eq`, `csoundHRO` | For both policies, `mayProgHRO eu = mayProgHR eu`. So O with the default configuration is sound under A2-strict. | Opt/HavocRecency.lean |
| `addSets_work` | One per-cell havoc with recency has the same cost bound as `addHv_work`. | Opt/HavocRecency.lean |

Cost note. `SHARED` adds one node `{havoc(s)}` to all cells, so equal unions give memo hits. `PER_CELL` interns up to `\|ks\|` new singleton nodes and up to `\|ks\|` new union nodes for each call. The engine avoids this work with the havoc layer (§7.6).

Limits of the equivalence:

- It holds on the universe only. `mayProgO_eq`, `mayProgRO_eq`, `mayProgHO_eq` and `mayProgHRO_eq` need `x, y ∈ p.vars ++ fr.vars`. Outside, C can differ only after a loop ran out of fuel (`top`) (argued). All queries are on such variables.
- O does not remove a cell entry whose node equals the default content. This has no effect on the equivalence and on the bounds. The Kotlin state must remove such entries (§7.10).
- Not in the O model: the havoc layer of §7.6, the iteration strategy of §7.10, exceptional edges.

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

`AliasAllocInfo` follows the points-to set of the queried local only, not "the allocations of a group". This fixes the transitive answer for `JIRCallResolver` (CK5). A symbolic, deep, havoc or catch origin in `pts(x)` means "an object that is not a local allocation". §8.2 (M6) uses it as an "unknown origin present" signal.

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
| Depths | D = 6 accessors (main: `HEAP_CHAIN_LIMIT = 5`, counted from 0). K = D + 1 = 7. | CK3, D4, §6.2 |
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
| `org.opentaint.dataflow.ap.ifds.analysis.alias` (`opentaint-dataflow`, shared with Go) | `LocalAliasQueries` (new interface) | The query contract that `AliasUtil` helpers and JVM consumers use (M3, §8.3) |
| same | `LocalAliasAnalysis` (changed: implements `LocalAliasQueries`) | Unchanged DSU base. Go and the JVM DSU backend use it. |
| `org.opentaint.dataflow.graph` (`opentaint-dataflow`) | `CompactGraphTopSort.weakTopologicalOrder`, `CompactGraphTopSort.onCycle` (new public functions) | The WTO of a graph (null for an irreducible graph), and the nodes on a cycle |
| same | `simulateGraphWto` (new) | Recursive WTO iteration with an accumulating join and a change bit at loop heads (§7.10) |
| `org.opentaint.dataflow.jvm.ap.ifds` (`opentaint-jvm-dataflow`) | `JIRLocalAliasAnalysis` (changed: facade) | Same constructor, same public queries. It selects a backend by `Params.aliasAnalysisMode`. |
| `org.opentaint.dataflow.jvm.ap.ifds.alias` | `JIRDsuAliasBackend` (the body of `JIRLocalAliasAnalysis` on main, renamed) | The DSU backend. Its behaviour does not change. |
| `org.opentaint.dataflow.jvm.ap.ifds.alias.directed` (new) | `NodeTable` | Interned origin sets (nodes), union memo |
| same | `OriginTable`, `BaseTable`, `SiteTable`, `CellTable`, `VarTable`, `SiteListTable` | Dense `Int` ids for origins, bases, sites, cells, variables, and sorted call-site lists |
| same | `DirectedState` | State for each statement: environment map, heap map, havoc layer |
| same | `DirectedTransfer` | The operations of O (copy, allocate, load, store, havoc, retire, join, garbage collection) |
| same | `DirectedAliasAnalysis` | JIR driver: maps `Stmt` (from `JIRDSUAABuilder`) to `DirectedTransfer` operations; inlining |
| same | `DirectedAliasResult` | Frozen tables and the states of each statement after the fixpoint |
| same | `DirectedAliasQuery`, `ReverseIndex` | Lazy reverse index, backward search, conversion to `AliasInfo` |
| same | `JIRDirectedAliasBackend` | Implements `LocalAliasQueries` on `DirectedAliasResult` |

The directed engine is in the JVM module. It does not change shared behaviour. The only shared-code changes are at the type level (`LocalAliasQueries`) and two additive graph functions. Go behaviour stays the same.

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
typealias SiteListId = Int
typealias HeapKey = Long
typealias HeapEntry = Long
typealias PairKey = Long

const val EMPTY_NODE: NodeId = 0
const val EMPTY_SITE_LIST: SiteListId = 0
const val ABSENT: Int = -1
const val ELEM_CELL: CellId = 0

inline fun heapKey(origin: OriginId, cell: CellId): HeapKey =
    (origin.toLong() shl 32) or (cell.toLong() and 0xFFFF_FFFFL)

inline fun heapKeyOrigin(key: HeapKey): OriginId = (key ushr 32).toInt()

inline fun heapKeyCell(key: HeapKey): CellId = key.toInt()

inline fun heapEntry(value: NodeId, calls: SiteListId): HeapEntry =
    (value.toLong() shl 32) or (calls.toLong() and 0xFFFF_FFFFL)

inline fun heapEntryValue(entry: HeapEntry): NodeId = (entry ushr 32).toInt()

inline fun heapEntryCalls(entry: HeapEntry): SiteListId = entry.toInt()

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
enum class OriginKind { SYM, DEEP, ALLOC, ALLOC_NEW, ALLOC_OLD, BOX_CONST, CLASS_CONST, STRING_CONST, SITE_CONST, HAVOC_SITE }

enum class BaseKind { ROOT_THIS, ROOT_ARG, ROOT_STATIC, FRESH, HAVOC_CELL }

class BaseTable {
    fun thisBase(): BaseId
    fun argBase(index: Int): BaseId
    fun staticBase(binaryClassName: String): BaseId
    fun freshBase(site: SiteId): BaseId
    fun havocCellBase(site: SiteId, key: OriginId, cell: CellId): BaseId
    fun kind(base: BaseId): BaseKind
    fun freeze()
}

class OriginTable(val symDepth: Int, val bases: BaseTable) {
    fun kind(origin: OriginId): OriginKind
    fun isOuter(origin: OriginId): Boolean
    fun isHavocDerived(origin: OriginId): Boolean
    fun keyOf(origin: OriginId): OriginId
    fun symRoot(base: BaseId): OriginId
    fun symChild(parent: OriginId, cell: CellId): OriginId
    fun alloc(site: SiteId, level: Int, kind: OriginKind): OriginId
    fun boxConst(boxType: String): OriginId
    fun classConst(binaryClassName: String): OriginId
    fun stringConst(value: String): OriginId
    fun siteConst(site: SiteId): OriginId
    fun havocSite(site: SiteId): OriginId
    fun freeze()
}

class SiteListTable {
    fun add(list: SiteListId, site: SiteId): SiteListId
    fun union(a: SiteListId, b: SiteListId): SiteListId
    fun sites(list: SiteListId): IntArray
}
```

Policy and parameters:

```kotlin
enum class AliasAnalysisMode { DSU, DIRECTED }

enum class HavocMode { SHARED, PER_CELL }

data class DirectedAliasPolicy(
    val entryUnique: Boolean = false,
    val recency: Boolean = true,
    val havocMode: HavocMode = HavocMode.PER_CELL,
    val symDepth: Int = 7,
    val maxAccessors: Int = 6,
    val maxTableContent: Long = 50_000_000L,
)

data class Params(
    val useAliasAnalysis: Boolean = true,
    val aliasAnalysisInterProcCallDepth: Int = 0,
    val aliasAnalysisTimeLimit: Duration = 10.seconds,
    val aliasAnalysisMode: AliasAnalysisMode = AliasAnalysisMode.DSU,
    val directedPolicy: DirectedAliasPolicy = DirectedAliasPolicy(),
)
```

State and transfer:

```kotlin
class DirectedState(
    val env: Int2IntOpenHashMap,
    val heap: Long2LongOpenHashMap,
    val havocOuter: SiteListId,
    val havocAlloc: Int2IntOpenHashMap,
) {
    override fun equals(other: Any?): Boolean
    override fun hashCode(): Int
}

class Joined<S>(val state: S, val changed: Boolean)

class DirectedTransfer(
    val nodes: NodeTable,
    val origins: OriginTable,
    val sites: SiteTable,
    val siteLists: SiteListTable,
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
    fun havoc(s: DirectedState, reachRoots: NodeId, site: SiteId): DirectedState
    fun retire(s: DirectedState, site: SiteId): DirectedState
    fun dropVars(s: DirectedState, keep: (VarId) -> Boolean): DirectedState
    fun collectGarbage(s: DirectedState): DirectedState
    fun isUnique(origin: OriginId): Boolean
    fun mergeAll(states: List<DirectedState>): DirectedState
    fun join(old: DirectedState?, incoming: DirectedState): Joined<DirectedState>
}
```

`env` and `heap` use `defaultReturnValue(ABSENT)`. `EMPTY_NODE` is a valid written value (`x.f = null`). It must stay different from "absent", because absent means default content.

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

Shared query interface (M3):

```kotlin
interface LocalAliasQueries<AliasInfo, AliasAccessor> {
    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
}

abstract class LocalAliasAnalysis<AliasInfo, AliasAccessor> : LocalAliasQueries<AliasInfo, AliasAccessor>
```

JVM facade additions:

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
) : LocalAliasQueries<AliasInfo, AliasAccessor> {
    fun findArrayElementAliases(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>?
    fun mayHoldUnknownObject(base: AccessPathBase.LocalVar, statement: CommonInst): Boolean
    fun findMustAlias(base: AccessPathBase, statement: CommonInst): List<AliasApInfo>?
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
| `sym(root, q)`, `q` without `ELEM_CELL` | `entryUnique` | `Origin.uniqueB` (Concept.lean) |
| `sym(fresh s, q)`, `q` without `ELEM_CELL` | `entryUnique` and not `isLoopSite(s)` | same |
| per-cell havoc origins | no | `Origin.uniqueB` (`hsym`, `hdeep`) |
| `deep(b)` | no | same |
| `alloc(s)` (recency off) | not `isLoopSite(s)` | same (`once s`) |
| `alloc-new(s)` | yes | `uniqueR` (Sound/Recency/Concept.lean) |
| `alloc-old(s)`, constants, `havoc(s)` | no | `uniqueR`, `uniqueB` |

`isLoopSite(s)` is true in two cases. Case 1: the statement of `s` is on a cycle of its graph (`onCycle`). Case 2: `s` is in a callee, and the call statement is on a cycle of the caller. Each JIR statement index occurs one time in each context. So "occurs at most one time" in `Prog.onceB` holds for each JIR site.

Constructor `this`. `this` is the root `sym(root this, [])` in each method, also in `<init>`. The builder flag `This(isOuter)` has no effect on the directed engine. This fixes shapes U1.a3 and U1.a4 (Lean `a3_unsound`, `a4_unsound`): `env n = {this, alloc}` has two origins, so the store is weak. With the default `entryUnique = false`, a store on `this` is weak in each method, also in a constructor (probe row 29 changes, §9.3). With `entryUnique = true`, it is strong in each method (probe row 30 flips).

### 7.6 Calls: havoc model

The engine has two havoc modes. Both keep the old content of each cell. This fixes U2.

| Mode | Origin that call `s` adds to cell `(o, c)` | Concrete call semantics | Proof state |
|---|---|---|---|
| `SHARED` | `havoc(s)`, one for each call site | A2-wide (§3.1) | proved: `csoundE`, `mayProgOE_eq`; with recency `csoundR`, `mayProgRO_eq` |
| `PER_CELL` | `havocC(s, keyOf(o), c, [])`, one for each call site, holder key and cell | A2-strict (§3.1) | proved: `csoundH`, `mayProgHO_eq`; with recency `csoundHR`, `mayProgHRO_eq`, `csoundHRO` (§4.9) |

`PER_CELL` is the production default (D2). Its soundness claim covers fewer callees than `SHARED` (§3.1). `SHARED` stays in the engine. The Lean vector tests use both modes (§10.1), and a user can select `SHARED` for A2-wide. For new content, the DSU also uses A2-strict. After a call removes a heap element, a later load makes a new heap element. No other cell shares this element. So `PER_CELL` keeps the DSU call semantics for new content and also keeps the old content.

Reach roots. The receiver is part of the reach roots. The DSU uses only `stmt.args`. The directed engine needs the receiver: after an unresolved `x.<init>(v)`, the cells of the allocation of `x` get havoc content. Without it they read as null, and later loads lose aliases.

Constructor calls. An unresolved `<init>` call always havocs its receiver, also with no reference argument. The directed engine does not use the `cantMutateAliasedHeap()` exemption of the DSU (D10). With `PER_CELL`, two loads of one field of the new object give the same origin `havocC(s, keyOf(o), f, [])`, so they alias, as in the DSU. Test: `directed no-argument constructor call makes the allocation fields havoc content`.

The havoc layer. A call does not write each (origin, cell) pair. It records the call in a layer of sorted call-site lists (`SiteListTable`):

- `havocOuter` is the list of the calls on some path to this point. It applies to each outer origin. `havocAlloc` maps each allocation origin that some call reached to such a list.
- Each heap entry is a pair `(value, calls)` packed in one `Long`. `value` is the node of the last store. `calls` is the list of the calls after that store that reached the cell. A strong store sets `calls := EMPTY_SITE_LIST`. A weak store keeps `calls`. Join is pointwise on both parts.
- `read(o, c)` is the value (or `default(o, c)` if the map has no entry) plus the layer content of each listed call `s`. In mode `SHARED` the layer content is `havoc(s)`. In mode `PER_CELL` it is `havocC(s, keyOf(o), c, [])`.
- In both modes the layer applies to each reachable origin, also to havoc-derived origins. This follows Lean (`AState.havoc`, `AState.havocH`): a havoc origin is outer, so a later call havocs it too. In mode `PER_CELL` the key of a havoc-derived holder is its site origin `havoc(s0)` (Lean `keyOf`). Do not use the more precise rule "no new origin for a havoc-derived holder": it is not proved (§4.9, F1).
- Keys (`OriginTable.keyOf`). The key of a holder is a function of the origin only. It never reads the recency state: the key of `alloc-new(s')` and of `alloc-old(s')` is `alloc-old(s')` (Lean `keyOfR`, proved by `keyOfR_alphaRS` and `csoundHR`). So `retire` never renames a per-cell havoc origin (§7.9). Cost: havoc objects in one cell of the most recent object and of the older objects of `s'` share one origin (`cost_answers`). Recency alone and per-cell havoc alone have the same answer, so this is no regression.
- `havoc(roots, s)`: compute the reached allocation origins (closure over written cells, from the argument and receiver origins and from the cells of outer origins). Add `s` to `havocOuter`, to `havocAlloc` of each reached allocation origin, and to `calls` of each written cell of each outer or reached origin. Cost: `O(|written cells of reached origins| + |reached|)` list adds for each call. No node is interned for a havoc union: the lists are shared by all cells with the same call history.
- A load interns the read set, as for any load. The memo key of such a read is (value node, call-site list, holder key, cell).

Lean has no layer. The Lean proofs use explicit havoc writes (`AState.havoc`, `AState.havocH`, `havocHO`, `havocHRO`). The layer is equal in denotation to these writes (argued; F3).

Return value: `env[l] := {sym(fresh(s), [])}` after the havoc (Lean `astep` call case).

### 7.7 Inlining, depth 1

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

Concept C without recency is weak on a loop allocation site. There it is less precise than the DSU (`loop_dsu_more_precise`, DSU/Examples.lean; `loop_bf_x`, Examples.lean). §1.7 gives the CEGAR step and its theorems.

Transfer rule (`astepR`, `retire` in Sound/Recency/Concept.lean; `retireO` in Opt/Recency.lean), for `x = new` at site `s`, with recency on:

1. `retire(s)`, with `n = alloc-new(s)` and `o = alloc-old(s)`:
   - each cell `c` of `n` (written, or with the havoc layer): `heap[o, c] := union(read(o, c), read(n, c))`. Then remove all entries `(n, c)`. After this, each cell of `n` is empty (`mergeCells`).
   - each environment entry and each heap entry whose node holds `n`: replace the node by `rename(node, n, o)` (`renameKeys`).
   - havoc layer: if `havocAlloc` has `n`, move its entry to `o` (union with the entry of `o`).
2. `env[x] := {n}`.

`NodeTable.rename` is memoized by `(node, from)`. A site that is not a loop site cannot hold `alloc-new(s)` before its own statement, because no path goes from the statement back to it. So only loop sites retire.

Per-cell havoc keys (proved: `keyOfR_alphaRS`, `csoundHR`; §4.9, §7.6). The key of an allocation holder is `alloc-old(s)` for both `alloc-new(s)` and `alloc-old(s)`. So `retire` never renames a key inside a per-cell havoc origin. A cell of `alloc-new(s)` and the same cell of `alloc-old(s)` read the same per-cell havoc origin, so the move of the `havocAlloc` entry in step 1 keeps the havoc content. The precision cost is `cost_answers` (§4.9).

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

Change test at other nodes. Propagate if the new state is not equal to the old state. Use content equality (`DirectedState.equals`). Node ids are canonical (`Tbl.id_inj`), so content equality is one `Int` comparison for each key. Content equality needs one canonical form: remove a heap entry whose node and call list equal the read value without the entry, and keep one form of the havoc layer. Otherwise equal states compare unequal. This costs only extra propagation, because each cycle has a head.

Do not use object identity as the change signal. A copy-on-write operation that adds and then removes an entry gives a new object with equal content. At a loop head, an identity test then makes the analysis run forever. `join` computes `changed` from the union ids: `changed` is true if some union id is not the old id for that key, or if a call-site list grows. This is `joinO_flag`.

Termination (argued): the heads only grow, and the universe is finite (symbolic paths up to K, deep origins, sites, cells, per-cell havoc bases with keys that never nest). So the heads become stable. Other nodes are functions of the heads.

### 7.11 Data structures

| Structure | Choice | Reason |
|---|---|---|
| Node | Sorted `IntArray` of origin ids. Id 0 is the empty set. | Union and meet are linear merges. `contains` is a binary search. `Tbl.id_inj`: one id for each set, so set equality is id equality. |
| Intern map | `Object2IntOpenCustomHashMap<IntArray>(IntArrays.HASH_STRATEGY)` | Content hash and content equality on the array |
| Singletons | `IntArrayList` indexed by origin id | `singleton(o)` is the most frequent intern (new, unknown, call result). |
| Union memo | `Long2IntOpenHashMap`, key `pairKey(a, b)`, default return `-1` | Symmetric key (`mkey`). `Tbl.union_again`: each pair is merged at most one time. Before the lookup, test three cases: `a == b`, `a == 0` and `b == 0`. In each case, the result is known without the memo. |
| Rename memo | `Long2IntOpenHashMap`, key `(node shl 32) or from` | `retire` renames the same nodes in each loop iteration. |
| Default content | By rule, not stored: `sym(b, q).c → {symOrDeep(b, q + c)}`; `deep(b) → {deep(b)}`; allocations and constants `→ {}`; catch and other fresh origins as `sym(fresh s, [])`; `havoc(s) → {havoc(s)}`; per-cell havoc origins as in §4.1; multi-dimensional arrays as in §7.5. During the analysis, a `Long2IntOpenHashMap` caches the default node for each heap key. | Lean `adefault`. The heap map holds only written cells (§5.5). |
| Environment | `Int2IntOpenHashMap` `VarId → NodeId`, live non-null variables only | Copy cost `O(live vars)`. Dead variables are removed at each statement, as on main. |
| Heap | `Long2LongOpenHashMap` `HeapKey → HeapEntry`, written or havoced cells only | `fam_osize`: the map part is linear in the program. |
| Havoc layer | `havocOuter: SiteListId`, `havocAlloc: Int2IntOpenHashMap` | One entry for all outer origins. No write for each (origin, cell) at a call. |
| Call-site lists | `SiteListTable`: interned sorted `IntArray`, memoized `add` and `union` | Lists are small and shared by all cells with the same call history. |
| State containers | fastutil maps, copy-on-write (copy, then change, for each statement that changes the state) | See below. |
| Reverse index | Lazy, one for each state that a query uses, cached in an `AtomicReferenceArray<ReverseIndex?>` | §5.7: the eager index costs more than enumeration on small programs. Default edges are computed by rule. |
| Answer cache | `ConcurrentHashMap<Long, List<AliasInfo>>`, key `(stmtIdx shl 33) or (after shl 32) or varId` | Full answers only. No depth in the key, because no outer call truncates an answer (fixes the cache-order defect, CK7). |

Memory (to be measured; gate in §11.2). The DSU removes heap elements of removed groups (`State.removeUnsafe`) and dead locals. The directed heap map has no such removal by itself. So the engine does four things:

1. Abstract garbage collection at each join and at the method exit of each inlined callee: drop each heap entry whose origin is not reachable from live variables, entry roots or statics, through written cells and default content. This is sound, because each query starts only from these roots.
2. `DirectedState` shares each component map (`env`, `heap`, `havocAlloc`) by reference when a statement does not change it.
3. For a node with one predecessor, `statesBefore[i]` is the same object as `statesAfter[pred]`.
4. After the fixpoint, intern equal states (one copy for each distinct content). `DirectedAliasStats.retainedEntries` counts the map entries after this step.

Container decision (D8): fastutil copy-on-write, not `kotlinx.collections.immutable` persistent maps. Reasons:

1. No boxing of `Int` and `Long` keys and values. A HAMT of boxed keys costs more for each entry.
2. The O join cost is per key (`joinO_work`: at most 5 units for a key with equal ids). A tight loop over two primitive maps is fast. The HAMT benefit (skip shared subtrees) needs access to internal nodes, which `kotlinx.collections.immutable` does not give.
3. The change signal is the explicit change bit. So the identity property of persistent sets is not necessary.

If the memory gate fails (§11.2), measure a persistent variant. The container is private to `DirectedState`, so the change is local.

Table growth (`chain_table`, §5.7): count `contentSize`. If it exceeds `maxTableContent`, stop the analysis of the method (§7.14). The initial value 50 000 000 is about 200 MB of `int` content for one method. P10 measures the maximum on Conductor and sets the cap from the 16 GB budget and the number of parallel method analyses. Memo misses (`test_miss`, §5.7): count `memoMisses` for the measurement plan.

### 7.12 Query implementation

`findAlias(x, P)` implements §6.2 (`findAlias_iff`, `search_mem`, `findAliasO_iff`):

1. Seeds: `members(val(x))` at state `P`.
2. Holders of an origin `o`: variables `v` with `o ∈ env[v]` (reverse environment index); static roots and argument roots by rule; heap holders `(p, c)` with `o ∈ read(p, c)`. Heap holders come from two sources:
   - the heap map: each written entry, with its call-site list;
   - default edges by rule:
     - `sym(b, q)` holds `sym(b, q + c)` at `c` if `(sym(b, q), c)` is not written;
     - `sym(b, q)` with `|q| = K` holds `deep(b)`;
     - `deep(b)` holds `deep(b)` at each cell, but the search never expands this self edge (§6.2);
     - the havoc layer gives `(p, c)` for each havoc origin that a listed call adds to `(p, c)`.
3. Backward search with suffixes, up to `maxAccessors = 6` heap accessors. Prune a child suffix if its preimage set does not meet the liveness layer of the remaining depth (`mem_live`).
4. Output: variable holders become `AliasApInfo(LocalVar | Argument | This, path)`. Static roots become `AliasApInfo(ClassStatic, [Static(T)] + path)`. Filter bases by `JIRLocalVariableReachability.isReachable(base, stmtIdx)`, as `compress` does. Drop `(x, [])` (CK4). Keep other paths with base `x`.
5. Allocation origins in `val(x)`: `AliasAllocInfo(instIdx)` for root-context `new`, `newarray` and catch sites, and for box, class and other non-string constants (CK5; both `alloc-new(s)` and `alloc-old(s)` map to `s`). String constants: `AliasApInfo(Constant("java.lang.String", v), [])` (CK6). No heap path on a `Constant` base. Never report `null`.
6. Sort the list with one fixed comparator (kind, base, accessors). The search gives no duplicates (`search_nodup`), so no deduplication pass is necessary.

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
| Frozen tables | `freeze()` on `NodeTable`, `OriginTable`, `BaseTable` and `SiteListTable` after the fixpoint. A write after `freeze()` throws. |
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
| Query cost | Bounded by `searchCost_le`. The query calls `parentCancellation.checkpoint()` for each 1024 expanded nodes. On main the query has no check. A per-query node budget (`maxQueryNodes`, "log and return the partial list") is a later decision, because it changes CK3. |

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

No JVM consumer needs symmetry. Only the CS8 vararg branch needs transitivity (it takes "the alias set that contains `lv[*]`"). No JVM main code calls `forEachHeapAlias`. Only Go and the untracked probe suite call it.

### 8.1 Contract CK1-CK13

| Item | Contract | How the proposal keeps it |
|---|---|---|
| CK1 | `findAlias` / `findAliasAfterStatement`; `null` or empty if no answer | The facade keeps both: `statesBefore[idx]` / `statesAfter[idx]`. `null` on timeout or for an unreachable statement. A variable with an empty value gives an empty list (main: `null` when the element is absent). Consumers treat both the same. |
| CK2 | Meaning of `AliasApInfo(base, accessors)` | The path may hold an object that `x` may hold at P: `pts(path) ∩ pts(x) ≠ ∅`. Same bases and accessors. |
| CK3 | Completeness up to the query depth | The backward search gives exactly the paths of the enumeration (`findAlias_iff`, `findAliasO_iff`), except paths through a deep self edge (§6.2). D is `maxAccessors = 6` (the effective value of main), a parameter. Soundness of C: `csoundE`, `csoundR` (scope A1-A3, mode `SHARED`); `csoundH`, `csoundHR` (mode `PER_CELL`, A2-strict). |
| CK4 | Exclude `(x, [])` | Step 4 of §7.12 |
| CK5 | `AliasAllocInfo(i)` if and only if `alloc(i) ∈ pts(x)` | Step 5 of §7.12. Only from `val(x)`, never from heap paths, and not from group members (the transitive set of main). |
| CK6 | String constants as `Constant`; never `null`; no heap path on a constant | `stringConst(value)` origin; step 5 |
| CK7 | Determinism | §7.13. Test `directed answers do not depend on query order`. |
| CK8 | Thread-safe shared instance | §7.13. Test `directed concurrent queries give equal answers`. |
| CK9 | Cost bounds, cancellation, `null` on timeout | §7.14 |
| CK10 | Before/after at calls with a documented model | Before = the state before the call. After = havoc (§7.6) + return + models (§7.8). Documented as a behaviour change (§9). |
| CK11 | Pass-through models after the call; `<rule-storage>` excluded | Directed weak copy (§7.8) |
| CK12 | Inlining depth 1 works; no callee elements in answers | §7.7 |
| CK13 | No symmetry or transitivity required | The relation is symmetric (`may_symm`) and not transitive (`alias_not_transitive`). No consumer needs more after M1. |

### 8.2 Changes M1-M8

| Item | Change | Step (§10.2) |
|---|---|---|
| M1 | `JIRBasicAtomEvaluator.resolveLocalVarValue`, vararg branch: replace `getAllAliasAtStatement` + "the set that contains `lv[*]`" with `findArrayElementAliases(lv)`. The DSU backend implements it with the partition logic of main, so DSU answers stay the same. | P1 |
| M2 | `getAllAliasAtStatement` leaves the JVM API. It stays in `LocalAliasAnalysis` for the DSU backend. | P1 |
| M3 | Base class: extract `LocalAliasQueries` (option a of D6). | P1 |
| M4 | Delete the unused JVM wrappers `forEachHeapAliasBeforeStatement` and `forEachAliasAtStatement(InitialFactAp)` in `JVM/analysis/JIRAliasUtil.kt`. Add `findHeapAlias` to the facade, with a DSU implementation over `forEachHeapAlias`. Change the probe helper `heapAnswer` to it, so the probe suite compiles after P1. | P1 |
| M5 | `forEachAliasAfterCallStatement`: no code change. The weak havoc keeps heap paths in the after set, so the intersection copies more facts (§9). A direct query is a later option. | — |
| M6 | `JIRCallResolver.resolveValueTypeConstraints`: if `mayHoldUnknownObject(x)`, add `defaultConstraint` (D9). | P8 |
| M7 | Negated atoms: no forced change. If D5 is accepted, use `findMustAlias` for `negated = true`. | P9 (optional) |
| M8 | Tests: keep `DSUAliasAnalysisStateTest` for the shared DSU. `DSUAliasAnalysisInvalidateOuterHeapAliasesTest` tests the JVM class `DSUAliasAnalysis`, so P13 removes it with that class. Add state-law tests for `DirectedState`. Change `test external call invalidates heap aliases` for the directed mode only (§9.2). Add the non-transitive tests (§10). | P3-P9, P13 |

### 8.3 Shared base class with Go (D6)

| Option | Shared-code change | JVM change | Go | Risk |
|---|---|---|---|---|
| (a) Extract `LocalAliasQueries` (two methods). `LocalAliasAnalysis` implements it. The generic helpers `forEachAliasAtStatement` and `forEachAliasAtStatementAmongBases` in `AliasUtil.kt` take `LocalAliasQueries` as receiver. `forEachHeapAliasBeforeStatement` stays on `LocalAliasAnalysis`. | Type level only | `JIRLocalAliasAnalysis` is a facade over two backends. | No behaviour change. The same call sites compile. | Low |
| (b) `JIRLocalAliasAnalysis` stops extending `LocalAliasAnalysis`. Copy the JVM helpers into `JIRAliasUtil.kt`. | None | Duplicate helpers | No change | The two copies of the `applyAlias` / `unapplyAlias` logic can become different. |

Recommendation: (a). It keeps one copy of the helpers. It lets the mode switch select a backend at run time. A later Go migration can implement the same interface.

### 8.4 Must-alias (D5)

Derive must-alias from O. No second fixpoint.

Definition: `must(x, p)` at P if `val(x) == val(p) == singleton(o)` and `isUnique(o)`. Node ids are canonical, so the test is one `Int` comparison for each holder.

Search: the same backward search, restricted to singleton edges. A variable `v` is a holder if `env[v] == singleton(o)`. A heap holder `(p, c)` counts if `read(p, c) == singleton(o)` and `p` itself is a must-holder (`val(prefix) == singleton(p)`, `p` unique).

| Property | Reason |
|---|---|
| `must ⊆ may` | Equal singleton sets meet. This keeps the invariant of `MayAndMustRelationTest` (branch `origin/DanielELog/must_alias`, not merged). |
| Sound under A1 | A unique origin denotes at most one object (`unique_obj`, `unique_objR`). Under entry aliasing a must-alias answer can be false, and a kill then drops taint. |
| "Must alias or null" | Null is not an origin. If one side may be null, `must` can still hold. A store through null throws. With the catch rule of §7.10, the catch path also gets the state before the store, so the old value of `p.f` stays there. Negated atoms (M7) need a non-null bit. Option: a non-null bit for each variable in `DirectedState`, as the Lean null kinds (`nsafe_sound`). |
| Cost | No second analysis. The `DanielELog` branch runs a second DSU with a meet join. |
| Query bases | `AccessPathBase` (locals, `Argument`, `This`), as the must consumers on that branch need. |

The branch `origin/DanielELog/must_alias` is on the old API (before #216 and #406). It has a second DSU run. Its unfinished "LValue alias" can lose may-aliases (not verified). Recommendation: do not rebase it. Port only its consumers onto `findMustAlias` and onto `StatementSummaryBuilder.write` (a strong kill on the must-alias path), in a later PR.

### 8.5 The alias cache defect

Main caches `convertedAliases` by `(element, stateId)` without the depth (`CORE/ap/ifds/analysis/alias/LocalAliasAnalysis.kt:137-142`). Assume that the analysis first converts an element as a nested instance (depth greater than 0). Then the chain is cut at `HEAP_CHAIN_LIMIT`, and the cache stores the cut list. A later top-level query of the same element reuses it. So answers depend on query order and thread interleaving.

| Backend | Action |
|---|---|
| Directed | Not affected. The search has no nested conversion, and the cache holds full answers (§7.11). |
| DSU | Fix the DSU cache before the A/B measurement. Use a separate small PR (P0b). Port commit `deff91ca0` (branch `origin/DanielELog/alias_cache_fix`, not merged). This commit stores the depth with each cached list. For a smaller depth, it computes the list again. Measure that PR alone on tms. The A/B baseline for the directed engine is then main plus this fix, so the A/B does not count the cache fix as a directed gain. The shared `LocalAliasAnalysis` is also the Go base, so this fix also changes Go answers. |

---

## 9. Behaviour changes to expect

### 9.1 For each consumer

| Consumer | Change | Direction | Reason |
|---|---|---|---|
| CS1/CS2/CS3 store summary | Fewer alias paths at a store. No edge to a path that only a transitive merge related. | Precision gain. Fewer false taint edges. | PL1-PL4. Test `field write through an alias adds the value forward and keeps the alias path backward` needs `alias(y) = {a.box}` exactly; the directed answer gives it. |
| CS1/CS2/CS3 | New edges after unresolved calls (heap paths kept) and after static writes | Soundness gain. Possible new findings. | U2 (`b_unsound`, `b_local_unsound`); U3 (`static_unsound`) |
| CS1/CS2/CS3 | New edges where the unsound strong update of main dropped a path | Soundness gain | U1 (`a1_unsound` .. `a4_unsound`); U4 (`repr_unsound`) |
| CS1-CS6 | Two locals that hold the same string literal now alias (one `stringConst` origin for each value). Facts on one local are copied to the other. | More facts, possibly more findings | §7.5. Test in P6: `directed equal string literals in two locals alias`. |
| CS1-CS6 | Callee-made aliasing of existing objects (an unresolved `m(x, y) { x.f = y; }`) stays out of scope, as on main. | No change | §3.4. The IFDS analysis covers resolved callees through their summaries and library callees through pass-through rules (argued). Test in P6: `directed unresolved setter call does not alias the argument with the field`. |
| CS4/CS5 copy to aliases at calls | The after-call set keeps heap paths (weak havoc). The intersection `before ∩ after` keeps them, so more facts are copied. | More facts, possibly more findings, more IFDS work | CK10, M5. Measure on Conductor (R4). |
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
| `test swap fields` (`swapFields(Box a, Box b)`) | `a.value` read at the sink aliases `arg0.value` and `arg1.value`; the same for `b.value` | Default `entryUnique = false`: no change. With `entryUnique = true`: both stores are strong, the value read from `a.value` aliases only `arg0.value`, and 2 of 4 assertions fail. | The DSU store on an outer receiver is weak. §3.3 gives the theorems. | D1 |
| `test external call invalidates heap aliases` (`arr[0] = src; System.arraycopy(arr, ...); dst = arr[0]`) | `alias(dst) ∌ arg0` | `pts(dst) ⊇ pts(src)`, so `alias(dst) ∋ arg0`. The assertion is inverted. | The removal of main is unsound (`b_unsound`, probe row 27). The callee can keep the cell (`call_w_xf`). | D2 |

In DSU mode both tests keep their assertions. In directed mode they get the new assertions (P9).

### 9.3 Probe tests that change

Counts for the default policy (`entryUnique = false`, recency on, `PER_CELL`). Appendix B gives each row.

| Group | Count | Probe rows |
|---|---|---|
| Flip: precision (transitive merge removed) | 10 | 1, 2, 3, 4, 8, 10, 11, 37, 41, 42 |
| Flip: soundness (lost alias restored) | 12 | 13, 14, 15, 16, 21, 22, 24, 25, 27, 28, 35, 36 (rows 35 and 36 also lose the false `x.next^k` chain) |
| Smaller sets with recency (precision) | 4 | 17, 18, 19, 20 |
| Precision loss against the DSU | 1 | 29: the store on `this` in a constructor is weak with `entryUnique = false` |
| Same answer | 15 | 5, 6, 7, 9, 12 (`null` becomes empty), 23, 26, 30, 31, 32, 33, 34, 38, 39, 40 |

With `entryUnique = true`, row 29 keeps its answer, and row 30 flips (precision).

With recency on, the loop stores on `cur` become strong. Then the sets of rows 13, 14 and 17-20 get smaller. For example, `alias(seen)` loses `cur.value`. This is correct, because `seen` holds `pa` and `cur.value` holds `pw`. So the expected sets of the directed probes come from the naive oracle with the chosen policy (§10.1), not from a manual derivation.

---

## 10. TDD plan

### 10.1 Layers

| Layer | What | Where | How |
|---|---|---|---|
| L0 | Lean vectors as Kotlin tables | `formal/directed-alias/Export/Vectors.lean` (the library does not import it). Output committed as `JTEST/alias/directed/lean-vectors.txt`. | A small `#eval` exporter (below). `LeanVectorTest` parses the file and runs the engine through `MiniDriver`. |
| L1 | Core unit tests of O against a naive C oracle; differential and property tests | `JTEST/alias/directed/` | `NaiveConcept` is a direct Kotlin port of `astep` / `astepR` / `analyze` with explicit sets. A seeded random generator makes structured programs. |
| L2 | JIR sample tests | `JTEST/alias/DirectedAliasProbeTest.kt`, `AliasSampleTest.kt` | Keep each `today ...` test in DSU mode. Add a `directed ...` test for each probe in directed mode. |
| L3 | Existing suites, both modes | jvm-dataflow, java-querylang, root `:test` | `-PaliasAnalysisMode=DIRECTED` and `-PaliasDepth=1` set the system properties `opentaint.test.aliasAnalysisMode` and `opentaint.test.aliasDepth`. Each test harness reads them (P1). |
| L4 | End to end | tms, dataflowbench Java and Kotlin, Conductor, thingsboard | §11.3 |

L0 exporter. For each example program of `Examples.lean`, `Sound/Boundary.lean` (CX1-CX7), `Sound/Recency/Examples.lean`, `Sound/StoreExamples.lean`, `Sound/EntryAlias.lean`, `Sound/Havoc/Examples.lean`, `Sound/HavocRecency/Examples.lean`, `DSU/Probes.lean`, `Opt/QueryFam.lean` and `Opt/Recency.lean`, print one line for each query:

```
V <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell> | frame=<var>:<root>,... | prog=<s-expression> | q=<x>.<path>~<y>.<path> | may=<true|false>
F <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell> | frame=... | prog=... | var=<x> | D=<d> | paths=<sorted list>
```

`may` comes from `mayProg`, `mayProgE eu` or `mayProgR eu` (`hv=shared`), or from `mayProgH eu` or `mayProgHR eu` (`hv=cell`). `paths` comes from `findAlias` (Opt/Query.lean). Each `V` line has a `decide` theorem in the Lean library for the same program (for example `join_x_y`, `loop_bf_x_fixed`). So the exported value is also a proved value. P3 changes `check.sh` so that it regenerates the file and fails on a difference from the committed copy. `#eval` is data export, not a proof, so the axiom audit does not change.

L0 rule for calls. Vectors with a call exist for both modes, and the engine answer must be equal to the vector in each mode: `hv=shared` from `mayProgE` and `mayProgR`, `hv=cell` from `mayProgH` and `mayProgHR` (for example `strict_answers`, `strict_answersHR`, `both_answers`, `cost_answers`). Add a vector with two calls and a load through a havoc object (the layer applies to `havoc(s1)` after the call `s2`). Also check that each `hv=cell` answer is a subset of the `hv=shared` answer of the same program, and that each Lean `*_witness` alias stays. No theorem states this subset relation (F6), so a failure is a finding, not a test bug.

L1 differential test.

1. Generate 10 000 programs with a fixed seed: variables 0..4, fields 0..1, sites 0..3, `seq` / `choice` / `loop` up to depth 3, random frames. Use only the statement kinds of the current step (§10.2).
2. Use each combination of `entryUnique`, recency and havoc mode.
3. Make `NaiveConcept` run on the same CFG with the same strategy as O (recursive WTO, §7.10). Run O with `MiniDriver` on that CFG.
4. Compare the answers for each pair of variables and each path of length 2 or less. Compare `findAlias` with enumeration. Equality is required.
5. Also run `NaiveConcept` with the structured `loopIter`. For a program whose CFG is the structured one, require equality. Else require inclusion (each structured answer is also an O answer), and record each strict difference.
6. A port of the Lean executor `runFrom` gives a soundness fuzz: each concrete alias of a random run must be in the O answer. For `PER_CELL`, the executor uses a distinct tag `k` for each havoc write (A2-strict), and `NaiveConcept` ports the per-cell call rule of §4.9 (`astepH`).

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
| P0b | `depth-aware cache keeps the full chain of an element first converted as a nested instance`. First, query the top-level variable. Its chain has at least 6 accessors, so the conversion of the inner element is cut. Then query the variable that holds the inner element directly. Expect its full chain. The sample method goes into `HeapAliasSample.java` (a chain of 7 fields). The test fails on main. | DSU cache depth fix (§8.5). Add the alias timer `aliasTimeMs` to the DSU path. | `G-JVM`, `G-CORE`, `G-QL`, Go CI, then the tms A/B alone | none (bug fix) |
| P1 | `vararg element aliases equal the partition answer in dsu mode` (characterization, green before and after); `alias mode directed is accepted by params`; in each suite, a canary test that fails if the property is `DIRECTED` and the backend in use is DSU | `LocalAliasQueries`; facade + `JIRDsuAliasBackend`; `Params.aliasAnalysisMode` (default `DSU`); `findArrayElementAliases` (M1, DSU implementation); `findHeapAlias` (M4, DSU implementation) and `heapAnswer` on it; delete M4 wrappers; generic `CallTreeNode<S>`; mode plumbing (list below) | `G-CORE`, `G-JVM`, `G-QL`, `G-ROOT` | `DSU` only |
| P2 | `NodeTableTest`: `intern gives one id for each set`, `empty set has id zero`, `union is symmetric and memoized`, `second union of a pair is a memo hit`, `join chain grows content quadratically and nodes linearly` (numbers of `chain_table`), `rename is memoized` | `NodeTable`, `OriginTable`, `BaseTable`, `SiteTable`, `CellTable`, `VarTable`, `SiteListTable` | `G-JVM` | not used yet |
| P3 | `LeanVectorTest` for `V` lines without a call and with `rec=0`; `DirectedStateLawTest` (list below); `RandomDifferentialTest` on the generator subset without calls and with recency off; `loop at the first instruction joins the back edge` | `DirectedState`, `DirectedTransfer` (copy, allocate, load, store, weak store, null), `isUnique` and the `entryUnique` policy, `simulateGraphWto`, `weakTopologicalOrder`, `onCycle`, synthetic entry node, `MiniDriver`, `NaiveConcept`, Lean exporter, `Export/Computed.lean`, the `check.sh` regeneration check | `G-JVM`, `G-CORE`, `G-LEAN` | not used yet |
| P4 | `LeanVectorTest` `F` lines; query tests (list below) | `ReverseIndex`, `DirectedAliasQuery` on mini programs; caches; freeze; virtual origins | `G-JVM` | not used yet |
| P5 | Directed probes for PS1, PS2, PS6-PS9, PS12, PS13 (list below); expected sets from `NaiveConcept` | `DirectedAliasAnalysis` intra-procedural. Unresolved calls with the provisional rule: return value `{sym(fresh(s), [])}`, `SHARED` havoc on the reach roots (arguments and receiver), and the `<init>` receiver rule (§7.6). `JIRDirectedAliasBackend`, base conversion, exceptional edges, catch origin, `collectGarbage`, exactness certificate (`exactMethods`) | `G-JVM` (DSU tests unchanged, new directed tests green) | `DIRECTED` in tests only |
| P6 | PS4 flips and call tests (list below); `LeanVectorTest` for `V` lines with `hv=cell` | `PER_CELL` havoc and the call-site lists, static writes with the static root key, directed models, `<rule-storage>` filter, constants (boxes, class literals, strings), multi-dimensional arrays, constant returns, the builder box list | `G-JVM` | tests only |
| P7 | PS3 directed probes (list below); Lean vectors with `rec=1` (`loop_bf_x_fixed`, `loop_bf_y` of Sound/Recency/Examples.lean; `o_loop_bf_x` of Opt/Recency.lean); `directed this field write in a method is a strong update with entryUnique true` | Recency (`retire`, loop sites), constructor `this` as root | `G-JVM`, `G-LEAN` | tests only |
| P8 | `AliasSampleTest` in directed mode with inlining depth 1: `test getter aliases this field`, `test setter then getter`, `test identity same-class call`, `HeaderValues addAll fixpoint must terminate`; `write enters flushBufferWithUserData and fixpoint must terminate` at depth 0; new `directed callee constructor makes a strong field write on the new object`; `type constraints add the default for an unknown origin` | Inlining depth 1 (§7.7) with new callee state arrays; `mayHoldUnknownObject`; M6 in `JIRCallResolver` (directed mode only, or both by D9) | `G-JVM`, `G-ROOT` | tests only |
| P9 | `AliasSampleTest` parameterized by mode; directed variant of `test external call invalidates heap aliases` with the new assertion; `test swap fields` with `entryUnique = true` and the new assertions; non-transitive tests (`alias of x does not contain y after a join`, the field example, `alias alloc info comes from points-to only`) | Test changes only; optional `findMustAlias` (D5) with `must alias is a subset of may alias` | `G-JVM` | tests only |
| P10 | — | Full suites in directed mode: `G-JVM`, `G-QL`, `G-ROOT` with `-PaliasAnalysisMode=DIRECTED`, also with `-PaliasDepth=1` where the harness supports it. Fix each failure with a failing test first. CLI option and the end-to-end plumbing (list below). The per-query differential mode (system property `opentaint.aliasDifferential`, §11.3 step 6). Set `maxTableContent` from the Conductor maximum (§7.11). | `G-JVM`, `G-QL`, `G-ROOT` in both modes | CLI opt-in |
| P11 (no code) | — | L4 measurements (§11.3), report | — | opt-in |
| P12 | — | Default `DIRECTED` (separate PR) when each condition of §11.2 holds | all gates | default on |
| P13 | — | After one release: remove the JVM DSU backend, its JVM-only tests and `DSUAliasAnalysisInvalidateOuterHeapAliasesTest`. Keep the shared DSU and its tests for Go. | all gates | mode switch removed |

Test lists:

- P3 `DirectedStateLawTest`: `join is idempotent`, `join is commutative on content`, `join flag is false for equal content in a new object`, `join flag is true when one union id changes` (`joinO_flag`).
- P4 query tests: `field example findAlias of z gives x.f y.f` (`field_findAlias_z`), `forEachHeapAlias of x f gives z x.f y.f` (`field_heapAliases_x`), `search gives no duplicates` (`search_nodup`), `directed answers do not depend on query order`, `directed concurrent queries give equal answers`, `query at depth 6 on a new symbolic chain after freeze`, `search does not expand a deep self edge`.
- P5 probes: `directed join of two allocations keeps x apart from y`, `directed join of two arguments keeps x apart from y`, `directed field write through a join of allocations keeps x f and y f with z and keeps x apart from y`, `directed load into the live root of the instance group keeps the aliased load`, `directed no-argument constructor call makes the allocation fields havoc content`, `directed catch after a throwing call keeps the value before the call`, `directed catch variable fields alias the thrown object fields`.
- P6 call tests: `directed unknown call on the argument keeps the loaded field alias` and the other four PS4 flips; `directed jdk call on the argument keeps the loaded field alias`; `directed value loaded after a call does not alias unrelated outer paths` (§4.9); `directed static field write then read aliases the written value`; `directed static write then read in a generic class and in a nested class aliases the written value`; `directed pass-through models of two arguments keep x apart from y`; `directed equal string literals in two locals alias`; `directed constant return replaces the old value`; `directed unresolved setter call does not alias the argument with the field`; `directed one new object in two cells is out of scope under per cell havoc` (the shape of §3.1).
- P7 probes: `directed strong update on a loop allocation site keeps the previous object field after a call` (PS3.1) and the PS3.2-PS3.5 directed probes.

Mode plumbing (P1 and P10). Each hop must pass the mode and the inlining depth:

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
| R1 | Mode `SHARED` makes each value loaded after a call alias each outer path (output and time growth). | §4.9 (`pHv`) | Default `PER_CELL` (D2). Test `directed value loaded after a call does not alias unrelated outer paths`. |
| R2 | Node table content grows as `m²/2` on join chains. | `chain_table` | `contentSize` counter and `maxTableContent` cap. Log the statistics. |
| R3 | Memo misses at loop tests | `test_miss` | Same order as a sorted merge. Count misses in L4. |
| R4 | Weak havoc keeps heap paths after calls, so CS4/CS5 copy more facts. IFDS work and memory grow. | CK10, M5. Conductor is already memory bound. | Measure IFDS events and heap on Conductor at 16 GB. If the growth is too large, keep weak havoc in the alias state. Then add a direct after-call query for CS4/CS5. This query excludes the cells that a call touched. |
| R5 | Entry aliasing is unsound for both policies. | `skip_unsound`, `write_read_unsound` (§3.3). The DSU is also unsound there. | Document A1. Caller information on the exact partition is a later option (§3.3). |
| R6 | `retire` scans the state for each loop allocation if no holder index exists. | `retireO_work` (§5.5) | Only loop sites retire. Keep a holder index for `alloc-new` of loop sites. Measure with a counter. |
| R7 | After a walk deeper than K, a variable holds `deep(b)`, and `deep(b)` holds itself in each cell. Without a rule, `findAlias` gives `\|cells\|^D` answers, most of them false aliases. The DSU gives only the accessed chain. | `adefault` (Concept.lean), §6.2 | K ≥ D + 1, and the search never expands a deep self edge (§6.2). Measure the output size on Conductor before P12. |
| R8 | Parts of the engine are not in the O proof: the havoc layer, the WTO strategy, exceptional edges, constants, garbage collection. | `mayProgOE_eq`, `mayProgRO_eq`, `mayProgHO_eq` and `mayProgHRO_eq` cover C with each combination of recency and havoc mode, with explicit havoc writes. | L1 differential test against `NaiveConcept` on the same CFG with the same strategy. Lean follow-ups F3, F4, F5, F8. |
| R9 | The directed engine havocs at each unresolved call, also at the calls that the DSU exempts (`cantMutateAliasedHeap()`). | §7.6, D10 | Count `havocs` and compare alias time in L4. |
| R10 | CS7 precision exposes the unknown-origin gap of main. | §9.1 CS7 | M6 / D9 |
| R11 | CS8 and negated atoms change findings in both directions. | §9.1 CS8 | Review each changed finding in L4 by hand. P12 needs an explanation for each lost finding (§11.2). |
| R12 | Interned constants and boxes: one run-time object for many executions | JVM semantics, not in Lean (F4) | Box and class constants are keyed by type, strings by value. Never unique, never split by recency (§7.5). |
| R13 | States for each statement use memory `O(statements × entries)`. Each method result stays in memory for the whole run (`JIRAnalysisManager.contexts`). | Not measured. The DSU removes heap elements of removed groups; the directed heap needs garbage collection (§7.11). | The four measures of §7.11. `retainedEntries` budget (§11.2). D8 if the budget fails. |
| R14 | Exceptions: catch states and the catch origin are outside the Lean model. | §3.4, §7.10 | Catch edges join the states before and after the thrower (argued, F8). The DSU uses the state after only. |
| R15 | Havoc content on written cells grows with the number of calls. | §7.6 | Call-site lists, shared by all cells with the same call history. No node for a havoc union. Count `siteLists` in `DirectedAliasStats`. |
| R16 | The default policy is proved sound only under A2-strict (`csoundHR`); under A2-wide it misses aliases (`generous_breaks_strict`). Completeness of recency and of calls is not proved (§4.7, F6). | §4.9 | A callee that writes one object into two cells is out of scope. Mode `SHARED` (A2-wide, proved by `csoundE` and `csoundR`) stays available for an A/B check (D2). |

### 11.2 Performance, precision and memory gates

Baseline: main + P0b. One jar that has both modes runs both sides of each A/B, so the alias timer is the same on both sides.

| Quantity | Budget (directed against baseline) | Source |
|---|---|---|
| tms wall time | at most +10 % (median of 3 alternating rounds) | §11.3 step 2 |
| Alias time for each method | log `aliasTimeMs`; sum over tms at most 1.5 × DSU | `DirectedAliasStats` |
| Alias timeouts ("exceed 10s" lines) and table-limit stops | not more than the baseline timeouts on tms, Conductor, thingsboard | logs |
| Table | maximum `contentSize` for each method below `maxTableContent`; report p50 / p99 / max of `nodeCount`, `contentSize`, `memoMisses / (memoHits + memoMisses)` | `DirectedAliasStats` |
| Memory | report p50 / p99 / max of `retainedEntries` for each method; the sum over Conductor at most 1.5 × the DSU state entries | `DirectedAliasStats` |
| Conductor at 16 GB | IFDS events before the memory guard and IFDS time within +10 %; no new memory guard event | §11.3 step 5 |
| thingsboard at 16 GB | the same | the same |
| dataflowbench | Java at least 49/58, Kotlin at least 50/58; explain each changed case | §11.3 step 4 |
| Precision (per-query differential) | Report mean and p99 of `\|alias(x)\|` in both modes on tms and Conductor. The mean in directed mode is smaller. Each query where the directed answer is not a subset of the DSU answer maps to a known class U1-U4, or it is a new bug. Unexplained queries: zero. | §11.3 step 6 |
| Exactness | Report the share of methods with `exactMethods` true, for each project | `DirectedAliasStats` |

The DSU state entries come from the DSU path of the same jar (a counter of the `IntDisjointSets` size after the fixpoint).

P12 go/no-go. P12 needs all of these conditions:

1. Each budget of the table above holds.
2. No unexplained lost finding on tms, Conductor or thingsboard.
3. dataflowbench at or above the baseline.
4. The precision metric is better than the baseline.
5. The user accepts A2-strict as the call scope of the default policy (§4.9, R16, D2).

`DirectedAliasStats` is a small counter object for each analysis, logged at DEBUG: `stmtEvals`, `headIterations`, `nodeCount`, `contentSize`, `memoHits`, `memoMisses`, `retires`, `havocs`, `siteLists`, `retainedEntries`, `exactMethods`, `queryCount`, `queryNodes`, `aliasTimeMs`.

### 11.3 Measurement plan

The sources of the baseline numbers: tms timing measured 2026-08-27 on this development machine; dataflowbench 49/58 and 50/58 reproduced 2026-09-01 with release `analyzer/2026.08.27.17eb0fe`; Conductor at 16 GB measured 2026-08-20.

1. Build two jars from one source tree: the baseline (main + P0b) and the directed build (P10, mode by option). Command: `cd core && ./gradlew :projectAnalyzerJar --offline -x :opentaint-ir:go:buildGoServer`. Build the CLI one time: `cd cli && GOPROXY=off go build -o <out>/opentaint-cli .`.
2. tms. Run `<out>/opentaint-cli scan --debug --experimental --analyzer-jar <jar> --ruleset rules/ruleset --project-model ../opentaint-test/opentaint-test-tms/opentaint-project --output <out>.sarif --timeout 800s --max-memory 8G` with each jar. Alternate the two jars over 3 rounds. The first run is cold: about 64 s, against about 37 s for a warm run. If you do not alternate the jars, the cold run can show a false slowdown of 70 %.
3. Compare findings on `(ruleId, message, locations, codeFlows)`. Then key again on `(ruleId, path, startLine, startColumn)`, and report changes of the code-flow count separately. A changed flow count shows as one removed and one added finding in the first key.
4. dataflowbench. Use JDK 21 and kotlinc 2.4.10. Run `dataflowbench run-opentaint-java-kernel --analyzer-jar <jar> --models-archive <models> --java <jdk21>/bin/java --javac <jdk21>/bin/javac` and `run-opentaint-kotlin-kernel` (with `--kotlinc` and `--kotlin-stdlib`) with each jar. Compare case outcomes.
5. Conductor and thingsboard. Run the scan on `opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml` (and the thingsboard project) with the CI arguments: `--passthrough-approximations`, `--java-dataflow-approximations`, the bundled ruleset plus the project rules, `--verbosity=DEBUG`, `--timeout 1080s`, and `--max-memory 16G` (at 8 GB every build reaches the memory guard). Alternate the jars over 3 rounds. Compare the events before the guard (the `Progress: N/M` lines), IFDS time, guard events and findings.
6. Per-query differential. In the directed build, set the system property `opentaint.aliasDifferential=true`. Then each query runs in both backends. The analyzer logs both answer sizes. It also logs each query where the directed answer is not a subset of the DSU answer. Run it on tms and Conductor. Classify each such query as U1-U4 or as a new bug.
7. For each new or lost finding: map it to a consumer (CS1-CS8) and to a probe shape. Add a probe if the shape is new.

### 11.4 Lean follow-ups

| Id | Item | Status |
|---|---|---|
| F1 | Per-cell havoc under A2-strict: concrete strict havoc, per-cell havoc origins, soundness, O equivalence, recency with per-cell havoc, and the shared key `alloc-old(s)`. | proved: `csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`, `keyOfR_alphaRS` (§4.9). Open part: the more precise rule for havoc-derived holders (§4.9, §7.6). |
| F2 | O with recency: retire on node ids, equivalence with the recency concept, cost bound | proved: `retireO_rel`, `storeRO_rel`, `ostepR_rel`, `analyzeRO_rel`, `mayProgRO_eq` (both policies), `retireO_work` (Opt/Recency.lean) |
| F3 | The havoc layer (call-site lists, `havocOuter`, `havocAlloc`) is equal in denotation to the explicit havoc writes. | open |
| F4 | Multi-dimensional array defaults; interned constants (boxes, class literals, strings) | open |
| F5 | Prove that WTO iteration equals the structured `loopIter` for reducible CFGs. | open |
| F6 | Completeness for calls under A2-strict; "recency is at least as precise as C"; "the combination is at least as precise as each refinement alone"; the finer key that removes the `cost_answers` alias; dominance over the DSU with loads and stores | open |
| F7 | The deep-self-edge search rule with K ≥ D + 1: it removes no path of length at most D from a root. | open |
| F8 | Exceptional flow: the catch-edge state and the catch origin are sound. | open |
| F9 | Small theorems: "recency equals C when each site is once" (`mayProgR eu = mayProgE eu`), which carries the completeness theorems to recency; a theorem `osoundE` for O without recency (for O with recency and per-cell havoc, `csoundHRO` exists). | open |

### 11.5 Rollback

The mode switch is the rollback. Set `aliasAnalysisMode = DSU` (CLI `--experimental-alias-analysis-mode=dsu`). The DSU backend stays in the code until P13. After P12 the rollback is a one-line default change.

---

## 12. Decisions for the user

| Id | Decision | Options | Recommendation | Evidence |
|---|---|---|---|---|
| D1 | Strong updates on entry roots (`entryUnique`) | (a) `false`: weak on symbolic origins; only allocation origins can get strong updates. (b) `true`: strong store on `sym(root, q)` without `elem`, and on unique call results. | (a) as the default for v1. Keep (b) as a policy value for A/B. | Soundness: under entry aliasing both policies are unsound (`skip_unsound`, `write_read_unsound`). (b) also loses aliases that (a) keeps: `swap_alias` with `swap_strong` false and `swap_weak` true. No theorem orders the two policies. The swap case is a real call shape (`test swap fields`). With (a), `test swap fields` keeps its assertions. Precision cost of (a): stores on `this` are weak, also in a constructor (probe row 29, a precision loss against the DSU). Gain of (b): probe row 30 flips, and `root_concept_more_precise`. |
| D2 | Call model | (a) the heap-alias removal of main. (b) weak havoc with site havoc origins (`SHARED`). (c) weak havoc with per-cell havoc origins (`PER_CELL`). | (c) `PER_CELL` as the default, under A2-strict (proved). Keep (b) `SHARED` as a mode for A2-wide (proved) and for A/B. | (a) is unsound (U2: probe rows 21, 24, 27; `b_unsound`, `b_local_unsound`, `call_w_xf`). (b) is sound under A2-wide, with and without recency (`csoundE`, `csoundR`, `mayProgOE_eq`, `mayProgRO_eq`). But a value loaded after a call may-aliases each outer path (`havoc_spread`, §4.9). (c) is sound under A2-strict, with and without recency (`csoundH`, `csoundHR`), and O equals C (`mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`). It removes the spread (`strict_answers`, `strict_ab_none`) and keeps the precision of the DSU for new content (`dsu_ab`). It is not sound under A2-wide (`generous_breaks_strict`), so the user must accept A2-strict (§3.1, R16, §11.2 condition 5). The shared key `alloc-old(s)` is sound (`keyOfR_alphaRS`). Its cost is `cost_answers` / `cost_none`, and recency alone and per-cell havoc alone have the same cost. Behaviour change for CS4/CS5 (§9.1) and for `test external call invalidates heap aliases` (§9.2). |
| D3 | Recency | (a) on. (b) off. | (a) | §1.7 (CEGAR step 1). Cost: R6. |
| D4 | Origin depth K and query depth D | K: 3, 7 or 9. D: 6 accessors, or less. | D = 6 (unchanged, `HEAP_CHAIN_LIMIT = 5`). K = 7 (K ≥ D + 1). | With K ≥ D + 1, a reported path from a root variable is its own origin, with no deep origin in the reported range (CX1 shows the merge). A path from a loaded variable can reach a deep origin in the reported range; the search rule of §6.2 then applies. Cost of K: origins and node sizes, up to `Σ_{i≤K} w^i` symbolic origins for each base on a walk over `w` fields (§6.2). Measure `nodeCount` and `contentSize` for K = 3 and K = 7 in L4 before the decision. Contract item CK3 needs an unchanged query depth D. |
| D5 | Must-alias | (a) derive from O (§8.4). (b) rebase `origin/DanielELog/must_alias` (second DSU with a meet join). (c) none now. | (a), as a later PR after P9 | No second fixpoint; `must ⊆ may`; ids make the test one comparison. (b) is on the old API, and its unfinished part can lose may-aliases (not verified). |
| D6 | Shared base class with Go | (a) extract `LocalAliasQueries`. (b) stop extending, copy the helpers. | (a) | §8.3. Type-level change only. Go does not change. |
| D7 | Rollout | (a) mode switch, default `DSU`, opt-in CLI; default `DIRECTED` after the conditions of §11.2 (P12); remove the DSU after one release (P13). (b) switch in one step. | (a) | Rollback by the mode switch (§11.5). L4 noise needs interleaved runs. |
| D8 | State container | (a) fastutil copy-on-write. (b) `kotlinx.collections.immutable` persistent maps. | (a). Measure (b) only if the memory gate fails. | §7.11: no boxing, `joinO_work` per key. Memory is to be measured (§11.2). |
| D9 | Unknown-origin signal for CS7 (M6) | (a) add `defaultConstraint` when `mayHoldUnknownObject` (both modes). (b) directed mode only. (c) no change. | (b) first, then (a) after a separate tms A/B | It closes the unsoundness of main that the directed precision makes visible (§9.1 CS7). (a) changes DSU results too, so measure it alone. |
| D10 | The `cantMutateAliasedHeap()` exemption | (a) no exemption in directed mode: each unresolved call havocs. (b) keep the exemption for static calls with only primitive arguments; never for the receiver of `<init>`. | (a) | The exemption is outside the Lean model: such a callee can write statics. For a constructor it removes the receiver havoc, and two loads of one field of the new object then do not alias (§7.6). Cost: more havocs (R9). |

---

## Appendix A. Lean file index

Build and audit:

```
cd formal/directed-alias && ./check.sh
```

`check.sh` builds the package with `lake build` (Lean `v4.35.0`, no Mathlib). It fails on `sorry`, `admit`, `native_decide` or an `axiom` declaration. It regenerates `AxiomAudit.lean` and fails if a theorem depends on `Classical.choice`, `sorryAx` or `ofReduceBool`. Output for the full package: 890 public theorems; 59 depend on no axiom, 309 on `propext`, 521 on `propext` and `Quot.sound`, 1 on `Quot.sound`; about 18.2k lines of Lean in 58 build jobs. Concrete checks use `decide`, or `decide +kernel` for large terms. The kernel checks both. No check uses `native_decide`.

Constructive claims. `propext` and `Quot.sound` are in the Lean core. Without `Classical.choice` they do not give the excluded middle, and they do not stop `decide` from reducing. So each proof is constructive. Each example witness is an explicit choice list. The executor `runFrom` runs it, and `decide` checks the result (`runAliasB_sound`). Each completeness theorem also has a computable witness search (`crossWitness`, `witness_core`, `witness_store`, Sound/Witness/Search.lean, §4.7). In the two scopes, a true answer yields a witness that a reader can run with `#eval`.

The body gives each theorem with its claim. This index gives the files. "Other lemmas" are the supporting theorems that the body does not cite.

| File | Content | Cited in | Other lemmas |
|---|---|---|---|
| `Syntax.lean` | The IR: statements, programs, sites | §2.1, §4 | — |
| `ListSet.lean` | Lists as sets, `single?` | §4.3 | — |
| `Concrete.lean` | Concrete semantics (A1-A3, A2-wide), the executor `runFrom`. A2-strict is in `Sound/Havoc/Concept.lean`. | §3.1, §4.7 | `run_sound`, `runAliasB_sound` |
| `Concept.lean` | Concept C: origins, `adefault`, `astep`, `join`, `loopIter`, `may`, `mayProg`, `CSound`, `CCompleteIn` | §4 | `alphaV_cdefault`, `closeIter_spec`, `loopIter_post`, `sub_loopIter`, `may_iff`, `may_comm` |
| `Examples.lean` | Task and field examples | §1, §4.4 | `join_a_x`, `join_a_y`, `join_x_y`, `join_a_x_witness`, `join_a_y_witness`, `strong_bf_x`, `strong_bf_y`, `call_w_xf_witness`, `call_w_xf_overwrite` |
| `Sound/Invariant.lean` | The invariant `Inv`, the once budget | §4.5 | `Exec.cnt_le` |
| `Sound/Step.lean` | Local soundness of each statement | §4.5 | `unique_obj`, `reachB_of_reach`, `Inv.havoc` |
| `Sound/Soundness.lean` | Soundness of C | §4.5 | `mayProgE_true`, `analyze_sound`, `loop_keeps`, `inv_init`, `evalPath_sound`, `ctxE_ok` |
| `Sound/Recency/*.lean` | Recency concept, soundness, examples | §4.2, §1.7, §4.8 | `analyze_soundR`, `step_soundR`, `loop_bf_y`, `loop_bf_y_witness`, `crossB_sound`, `list_may`, `list_cross` |
| `Sound/Complete.lean`, `Sound/NullSafe.lean`, `Sound/StoreScope.lean`, `Sound/StoreExamples.lean` | Completeness scopes and the certificate | §4.7 | `nsafe_sound`, `nullSafe_safe` |
| `Sound/Boundary.lean` | Counterexamples CX1-CX7, the decision procedure | §4.8 | `pJoin_in_scope`, `pJoin_exact` |
| `Sound/EntryAlias.lean` | Entry aliasing | §3.3 | — |
| `Sound/Facts.lean` | Symmetry, non-transitivity, the partition theorem | §1.5, §4.4 | — |
| `Sound/Havoc/*.lean` (`Concept`, `Soundness`, `Fresh`, `Examples`, `ExamplesK1`) | A2-strict (`HavocS`, `ExecS`), per-cell havoc concept (`mayProgH`), soundness `csoundH`, freshness, the `pHv` examples | §3.1, §4.9 | `HavocS.toHavoc`, `keyOf_alphaS`, `alphaS_head`, `InvS.havocH`, `reachB_of_reachS`, `ctxH_ok`, `fresh_head`, `ExecS.hinv`, `strict_answers_K1`, `havoc_spread_exact`, `new_answers`, `loop_answers` |
| `Sound/HavocRecency/*.lean` (`Inv`, `Concept`, `Soundness`, `Examples`, `ExamplesK1`) | Recency with per-cell havoc (the default policy): the generic invariant `InvG`, the key `keyOfR`, soundness `csoundHR`, the cost of the shared key | §4.9, §7.9 | `InvG.retire`, `alphaRS_bump`, `alphaRS_head`, `InvG.havocHR`, `ctxHR_ok`, `no_alias_of_mayProgHR`, `strict_answersHR_K1`, `spread_with_recency_only`, `havocS_distinct` |
| `Sound/Witness/*.lean` (`Rename`, `Compact`, `Search`, `Examples`) | Computable witnesses for the completeness theorems: `crossWitness`, `witness_core`, `witness_store`, `oneWitness` | §0, §4.7 | `run_completeA`, `run_r`, `compact`, `checkW_sound`, `crossWitness_sound`, `crossWitness_complete`, `crossWitness_none_iff`, `arr_of_core`, `arr_of_store` |
| `DSU/Model.lean`, `DSU/Lemmas.lean`, `DSU/Props.lean` | The DSU model and its invariants | §2.1, §1.5 | `dsuMayD_iff`, `DMayL_iff_short` |
| `DSU/Examples.lean` | DSU defects and the dominance boundary | §2.3, §2.4, §2.5 | `field_x_y_none`, `a1_witness`, `a2_witness`, `a4_witness`, `static_as_field`, `loop_bf_x_none` |
| `DSU/HeapFree.lean` | Heap-free soundness and dominance | §2.5 | `inv_sim`, `rel_sim`, `alias_good`, `aOk_loopFree` |
| `DSU/ConcreteFacts.lean` | Generic execution invariants | — | `exec_preserve`, `exec_loop_inv`, `exec_env_keep` |
| `DSU/Probes.lean` | The model against the measured Kotlin answers | §2.1, §2.3 | `s31_witness`, `s33_witness`, `s34_witness`, `sound_on_pJoin`, `dominates_on_pJoin`, `dominates_on_s7` |
| `Opt/Table.lean` | Node table | §5.2 | `Tbl.Below.mem_sub` |
| `Opt/Prim.lean`, `Opt/Machine.lean`, `Opt/Equiv.lean` | O operations and O ≡ C | §5.3, §5.5 | — |
| `Opt/Support.lean` | Support of C | §5.5 | `Supp.astep`, `Supp.join`, `Supp.top`, `Supp.loopIter`, `Supp.analyze`, `ctxClosed_ofProg`, `progOK_ofProg`, `supp_ainit` |
| `Opt/Recency.lean` | O with recency | §5.5 | `renameL_congr`, `renameL_of_not_mem`, `renameL_dflt`, `renameL_sub`, `cval_retire`, `supp_retire`, `supp_storeR`, `supp_astepR`, `supp_analyzeR`, `ctxClosed_R`, `recOK_R`, `progOKR_R`, `supp_ainitR` |
| `Opt/Havoc.lean`, `Opt/HavocExamples.lean` | O with per-cell havoc (`havocHO`), `mayProgHO_eq` | §4.9, §5.5 | `analyzeHO_rel`, `callHO_rel`, `addHv_spec`, `addHv_work`, `Supp.havocH`, `ctxClosed_H`, `o_new_answers` |
| `Opt/HavocRecency.lean` | O with recency and per-cell havoc (`havocHRO`), `mayProgHRO_eq`, `csoundHRO` | §4.9, §5.5 | `havocHRO_rel`, `analyzeHRO_rel`, `addSets_spec`, `addHv_eq_addSets`, `addSets_work`, `o_cost`, `o_pHv`, `o_both` |
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

All tests are in `JTEST/alias/DirectedAliasProbeTest.kt`; the sample is `DirectedAliasSample.java`. "Today" is the measured verdict on main. "Directed" is the expected answer under the default policy (§9.3). In this column, `new(x)` is the `AliasAllocInfo` of the allocation of `x`, and `arg:p` is the argument path `p`. "Rec" marks sets that also depend on recency (D3). "Lean" is the related theorem.

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
| 29 | `today this field write in a constructor is a strong update` | PS11 | same | weak with `entryUnique = false` (precision loss); same with `true` | | — |
| 30 | `today this field write in a method is a weak update` | PS11 | precision loss | same with `entryUnique = false`; flip with `true`: `alias(t) = {v2, arg:p2, this.value}` | | `root_concept_more_precise` |
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

Totals under the default policy: §9.3. The six "Rec" rows need the oracle for their exact sets.
