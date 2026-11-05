# Directed alias analysis for the JVM: design proposal

Status: proposal. Base: main `f945f92c5`. The formal model `formal/directed-alias/` (Lean 4, constructive) and the probe suite `DirectedAliasProbeTest` are not committed yet. Step P0 commits the probe suite, and step P0a commits the model and this document (§10.2). The user decided eight of the fifteen decisions between 2026-10-29 and 2026-11-05 (§12). The normative text of the analysis is the compact specification `directed-alias-analysis-spec.md`. This document must agree with it.

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
| value | An object, or a null with an identity. A null is the null of one run of a null site, the default null of one cell of an allocated object, or a null that a callee writes. The concrete semantics of design VS (§4.12) gives each null this identity, so "the same value" covers nulls. Concept C and the earlier steps know only objects. | `VVal` (`obj`, `nul`), `NTag` | — |
| origin | An abstract value. The kinds are the next nine rows. | `Origin` | `OriginId`, `OriginKind` |
| symbolic origin `sym(b, q)` | The entry object (or the result object of an unknown expression or call) at path `q` below base `b`, with `\|q\| ≤ K`. | `sym b q` | `SYM` |
| deep origin `deep(b)` | All objects below base `b` at a depth greater than K. | `deep b` | `DEEP` |
| allocation origin `alloc(s)` | All objects of allocation site `s`. | `alloc s` | `ALLOC` |
| `alloc-new(s)`, `alloc-old(s)` | With recency: the most recent object of site `s`, and all older objects of `s` (§4.2). | `rNew s`, `rOld s` | `ALLOC_NEW`, `ALLOC_OLD` |
| site havoc origin `havoc(s)` | All objects that call site `s` writes, and all objects below them. The Lean concept C uses it (A2-wide). The engine has no such origin (§7.6). | `havoc s` | none |
| per-cell havoc origin `havocC(s, k, c, q)`, `havocDeep(s, k, c)` | The new object that call site `s` writes into cell `c` of a holder with key `k`, and the tree below it. Only the Lean model has it: the per-cell reference (§4.9). The engine has no such origin (§7.6). | `hsym s k c q`, `hdeep s k c` | none |
| allocation child origin `⟨@s.c.q⟩`, `deep(@s.c)` | For `q` empty: the value in cell `c` of an object of allocation site `s`, that is the default null of the cell, or a value that a callee writes there. For `q` not empty: the value at path `q` (at most K cells) below it. `deep(@s.c)`: the values deeper than K there. Never unique. In design VS, `{⟨@s.c⟩}` is the default content of each allocation cell (§4.12). | `hsym 0 (rOld s) c q`, `hdeep 0 (rOld s) c` | `SYM`, `DEEP` over an `ALLOC_CHILD` base |
| null origin `null(i)` | The null of the null assignment at null site `i` (`x = null`, or `x.f = null` through a local). One origin for each null site. Never unique. Never an allocation (§4.12, §6.1). | `nullO i` (encoded `hsym 1 (havoc i) elem []`) | `NULL_SITE` |
| cell name `name(o, c)` | The origin that names the value in cell `c` of origin `o` when the method did not write the cell: the default child of a symbolic origin, or the allocation child `⟨@s.c⟩` of an allocation origin. In design VS it is the default content of each cell, so a value that a callee writes into the cell has the name of the cell content (§4.12). CN wrote it into the cells at a call (history, §4.11). | `childCN K o c`, `adefaultV` | `OriginTable.cellName` |
| reached set `Etree` | The origins that some unresolved call on some path to this point reached: the union of the call closures `R`. A symbolic origin with a proper prefix in `Etree` is not unique (§4.12). | `CtxN.xe`, `X.env xe`, `expB` | the reserved key `ETREE_VAR` of `env` |
| reached value set `Eval` | The origins that were in a cell of a covered origin at some unresolved call on some path to this point. An origin in `Eval` is not unique (§4.12). | `CtxB.xv`, `X.env xv`, `uniqueBO` | the reserved key `EVAL_VAR` of `env` |
| exposed set `E` (history) | The set of the call rule CN: the same set as `Etree` (§4.11). The engine uses the name `Etree`. | `CtxN.xe`, `expB` | none |
| covered origin, call closure | At a call: an origin of the closure `R`, or an origin below one (a symbolic descendant, or an allocation child of a covered allocation). `R` starts at the arguments and the static roots and adds the content of each cell of each covered origin (§4.11, §4.12). | `coveredB`, `callRoots`, `closeN` | `DirectedTransfer.callClosure` |
| upstream call | An unresolved call on some control-flow path from the method entry to a statement. In a loop, the later calls of the loop body are upstream too (§4.12). | `Prog.calls`, the list `up` of `analyzeBW` | `UpstreamCalls` |
| on-demand test | The strong-update test of design VS computed at the store from the closures of the upstream calls, in place of the stored sets `Etree` and `Eval` (§4.12, §7.6). | `analyzeBW`, `storeT`, `mayProgBW` | `CallClosureCache` |
| constant origin | One origin for each box type, class literal or string value (§7.5). | none | `BOX_CONST`, `CLASS_CONST`, `STRING_CONST`, `SITE_CONST` |
| holder | A variable, or a heap cell `(o, c)` of origin `o` and cell `c`. | `Key` (`v x`, `h o c`) | `VarId`, `HeapKey` |
| points-to set `pts(p)` | The origins that the access path `p` may hold. | `aevalPath` | `valueOf`, `load` |
| congruence `≡` | A reflexive, symmetric and transitive relation with `x ≡ y ⇒ x.f ≡ y.f`. The DSU keeps one (§1.7). | `DMay` | DSU partition |
| order `p ⊒ q` | `pts(p) ⊇ pts(q)`: `p` may hold each object that `q` may hold. The edge `p → q` of the task notation. A congruent order: reflexive, transitive, congruent (`p ⊒ q ⇒ p.f ⊒ q.f`), and antisymmetric on nodes (§1.7). | `Above`, `aboveB` | the node DAG of `NodeTable` |
| may-alias, `p ~ q` | `pts(p) ∩ pts(q) ≠ ∅`: one origin is below `p` and `q` in the order. Derived, not stored (§1.7). | `may` | `findAlias` |
| false alias | A may-alias that no execution (or pair of executions) has. | `NoCrossAlias` | — |
| one-execution alias | One execution makes `p` and `q` the same object. In design VS: the same value, that is the same object or the same null instance (§4.12). | `CAlias`; `CAliasV` | — |
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
| static root `⟨C⟩` | The entry root that holds the static fields of class `C`: one symbolic origin `sym(static C, [])` for each class. The compact specification calls it the static holder. Each unresolved call reaches each static root (A2-narrow). In the engine a static root never has a heap entry, because the engine ignores static writes (A5, §7.5). | `Base.root r` with `r ∈ statics` | `ROOT_STATIC`, `BaseTable.staticBase` |
| static field `C.f` | Cell `f` of the static root `⟨C⟩`. In the engine a read of it always gives its default content `{⟨C.f⟩}`, as if the method did not write the field (A5, §7.5). The Lean model has two forms: design VS treats a static write as an ordinary store into this cell, and design VSS applies the static rule. | cell `fld f` of a static root | `FieldLoad(Static(_), f)`, `WriteStatic` |
| static rule, design VSS | The rule of A5 (§3.1): a static write of the method does not change the state, and a static read gives `{⟨C.f⟩}`. Design VSS is design VS with the static rule. It equals design VS on the program with each static write replaced by `skip`. | `stripStatic`, `analyzeVSS`, `mayProgVSS`, `ExecA5` | `WriteStatic` (no change of state) |
| unresolved call | A call that the analysis does not inline. | `call s args` | `Stmt.Call` without a resolved callee |
| A2-wide | Concrete call semantics: one call can write one new object into many cells (§3.1). | `Havoc`, `Exec` | — |
| A2-strict | Concrete call semantics: one call writes a distinct new object into each cell that it changes. The callee can reach each symbolic object (§3.1). | `HavocS`, `ExecS` | — |
| A2-narrow | Concrete call semantics: A2-strict, and the callee reaches only the closure of its arguments (receiver included) and of the static roots (§3.1). The assumption of the call rule. With design VS, the callee can also write a new null into a reached cell (`HavocW`). | `ReachN`, `HavocN`, `ExecN`, `CAliasN`; `ExecV`, `HavocW`, `ExecW` | — |
| definite assignment | Each local is assigned before it is used (A4, §3.1). The JVM verifier guarantees it for bytecode. | `ExecV` | — |
| call rule VS | The abstract call rule of the engine (design VS, decided by the user 2026-11-03, §4.12). The call writes no heap entry. It adds its closure to `Etree` and the contents of the cells of the covered origins to `Eval`, so it only prohibits later strong updates. Sound for A2-narrow with callee nulls and A4. It is the only call rule of the engine. The engine has no mode switch for the call rule (D2). The Lean model keeps the earlier rules as recorded refinement steps: BO (§4.12), CN (§4.11), per-cell havoc origins (sound for A2-strict, the formal reference of the earlier steps, §4.9) and site havoc origins (sound for A2-wide). | `astepVS`; `astepBO`; `astepCN`; `astepH`, `astepHR`; `astep`, `astepR` | `DirectedTransfer.call` |
| reserved keys | The two environment keys that hold the nodes of `Etree` and `Eval`. Join, change bit, equality and `retire` treat them as each other key (§7.6). The on-demand test needs no reserved key. | `xe`, `xv` (`ctxVS`) | `ETREE_VAR`, `EVAL_VAR` |
| exposed key (history) | The one reserved key of CN (§4.11). | `xe` (`ctxCN`) | none |
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

Technical verbs: **intern** (find the id of a set in the node table, or add the set); **memoize** (store a result under its inputs); **retire** (rename `alloc-new(s)` to `alloc-old(s)`, and give `alloc-new(s)` its default cells, §4.2, §4.12); **havoc** (write the effect of an unresolved call into the heap: the call rules before design VS do it; design VS does not, §4.12).

### Identifier families

| Ids | Meaning | Section |
|---|---|---|
| A1-A5 | Scope assumptions | §3.1 |
| CK1-CK13 | Contract items of the alias API | §8.1 |
| CS1-CS8 | JVM consumers of the alias analysis | §8 |
| CX1-CX7 | Counterexamples at the completeness boundary | §4.8 |
| D1-D15 | Decisions for the user | §12 |
| F1-F15 | Lean follow-ups | §11.4 |
| G-JVM, G-CORE, G-QL, G-ROOT, G-LEAN | Test gates | §10.2 |
| L0-L4 | Test layers | §10.1 |
| loss L1-L4 | Precision losses of the call rules. Loss L1 and loss L4 are the accepted losses of design VS. Prose writes "loss L1" to keep them apart from the test layers. | §4.11, §4.12 |
| M1-M8 | Consumer changes | §8.2 |
| P0-P13 | Implementation steps (one pull request each), with P0a, P0c and P9a | §10.2 |
| PL1-PL7, U1-U4, LT1 | DSU defects: precision losses, unsound defects (U1 has shapes U1.a1-U1.a4), one latent defect | §2.3 |
| PS1-PS13 | Probe scenarios | §2.2, Appendix B |
| R0-R18 | Risks | §11.1 |

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
4. CEGAR steps (§1.8): recency for loop allocation sites (step 1); per-cell havoc origins for unresolved calls (step 2, now only a formal reference in the Lean model, §4.9); cell-named havoc with narrow reach, CN (step 4, §4.11); calls that only block strong updates, BO (steps 5 and 6, §4.12); value semantics and the passive call, design VS (step 7, decided by the user 2026-11-03, §4.12). CN and BO stay in the Lean model as recorded refinement steps. The engine does not implement them.
5. Design VS, the design of the engine (§4.12). A value is an object or a null with an identity. A field read makes the reader alias the cell, nulls included: `x = new X(); a = x.f` gives `findAlias(a) = {x.f}`, with or without calls. No reachable cell is empty: an allocation cell holds its cell name `⟨@s.c⟩` by default, and each null site has its own origin `null(i)`. So an unresolved call writes no heap entry and changes no alias. It only prohibits later strong updates: it adds its closure to the set `Etree` and the contents of the reached cells to the set `Eval`. An implementation can also compute both sets on demand at the store (D14). The engine has one call rule. The user dropped the havoc modes `SHARED` and `PER_CELL` from the engine (D2).
6. The mode switch `aliasAnalysisMode = DSU | SHADOW | DIRECTED`, default `DSU` (D7). In `SHADOW`, the taint analysis gets the DSU answers, and statistics compare both answers (§10.2).

**Results.**

| Area | Result | Status |
|---|---|---|
| Order | The stored relation is a congruent order; may-alias is derived (§1.5, §1.7). | proved |
| Soundness | Each one-execution alias is a may-alias under A1-A4. Design VS: each value alias (the same object or the same null instance) of an A2-narrow execution is a may-alias: `csoundVS` (both policies, recency, each K, each list of static roots). It stays sound if a callee also writes new nulls: `csoundVS_W`. The on-demand test is sound with loops for consistent final states: `csoundBW` (§4.12). The earlier steps: CN (`csoundCN`, §4.11), BO (`csoundBO`, §4.12); the references: site havoc under A2-wide, per-cell havoc under A2-strict (§4.5, §4.9). With the static rule of the engine (A5: the static writes of the method have no effect), design VSS is sound against the concrete semantics of A5: `csoundVSS` (`execA5_iff`, §3.1). A static read gives exactly `{⟨C.f⟩}` (`static_read`, `static_cells_default`). | proved |
| Completeness | Exact in two scopes without loops and calls, with computable witnesses (§4.7). | proved |
| DSU defects | U1-U4 (unsound), LT1 (latent), PL1-PL7 (precision) (§2.3). | proved, measured |
| O ≡ C | Equal answers for each combination of recency and call rule, design VS included (`mayProgVSO_eq`, `csoundVSO`); also CN and BO (`mayProgCNO_eq`, `mayProgBOO_eq`) (§5.5). On loop-free programs with different sites, the on-demand test gives the answers of the stored sets (`mayProgBW_eq`, §4.12). | proved |
| Cost | O is linear where C is a product or exponential on three families (§5.6, §5.8). The call of design VS writes zero heap entries in each state (`callVSO_heap_frame`); its work after the closure is two memoized unions (`callVSO_work`). On one family, BO writes at least n heap entries at its first call, CN at least m·n and per-cell havoc at least m²·n² (`separationVS`, §5.5). | proved; argued |
| Audit | No `Classical`, no `sorryAx`, no `ofReduceBool` (Appendix A). | checked |

**Limits.**

1. Alias answer volume (R0). The taint analysis copies one fact for each reported alias path. On main, the call drop and the cache truncation limit this volume by accident. A fix of either explodes the fact count, and thingsboard runs out of memory fast (user report). The directed engine removes both limits; its non-transitive answers are smaller. The net volume is unknown and is the first gate (§11.2, D11).
2. Entry aliasing: A1 is an accepted precondition, and strong updates on entry roots can lose aliases (D1, §3.3).
3. Loops and calls are in no completeness scope (§4.8). The call rule is proved sound only under A2-narrow; with generous reach or with one object in two cells it misses aliases (proved for CN: `generous_reach_breaks_CN`, `generous_havoc_breaks_CN`; design VS gives the same answers on these programs, argued, §3.1, §4.12).
4. The node table can hold Θ(m²) set elements on a join chain (§5.7).
5. Design VS has two accepted precision losses (D2): loss L1 (`t = x.f; m(x); t.g = z` is a weak update) and loss L4 (`this.box = b; touch(this); b.value = v` is a weak update). No execution has the kept aliases (`losses_VS`, `losses_noneV`, §4.12). The losses L2 and L3 of CN are gone: design VS is exact there (`losses_exactV`).
6. Design VS needs definite assignment (A4). A local that is used before it is assigned holds a null without a site, and a real alias is lost (`siteless_unsound`, §3.1, §4.12). JIR has definite assignment by the JVM verifier (argued, F13).
7. Null-valued aliases add answers. A read of an unwritten field of a new object, and a copy of a null, now give alias paths. On two small families design VS answers 4 of 9 queries true, and BO answers none (`added_answers`). Each added answer is a real value alias (`added_answers_real`), but none is an object alias (`added_answers_not_objects`). This adds alias answer volume (R0, R17).
8. The static gap (A5, D15). The engine ignores static writes: a static read always gives `{⟨C.f⟩}`. Design VSS is sound under A5 (`csoundVSS`), but A5 is a real restriction. (a) `C.f = v; t = C.f` does not give `t ~ v` (the DSU defect U3 stays, on purpose; `gapA`). (b) A value that the method stores only into a static field is not reached by later calls. In `C.f = a; e = a.h; d = e.g; m(); n = a.h; n.g = z`, the store `n.g = z` stays strong, so `e.g ~ d` is false. An execution without A5 has the alias: the callee follows `C.f` to `a` and writes a new object into `a.h`, so `n.g = z` does not write the cell of `e` (`gapB`). The taint analysis tracks static fields on its own (R18, §3.1).

**Decisions** (§12):

| Status | Decisions |
|---|---|
| Decided by the user (2026-10-29 to 2026-11-05) | D1 (`entryUnique = true`), D2 (no alias drop at unresolved calls; the call rule VS, decided 2026-11-03), D5 (must-alias postponed), D6 (copy the helpers), D7 (mode switch), D12 (inlining depth 1 stays), D13 (the DSU of main stays unchanged), D15 (static fields: the engine ignores static writes, and a static read gives `{⟨C.f⟩}`, decided 2026-11-05). |
| Open until the spec revisit | D3 (recency), D4 (depths K, D), D8 (state container), D9 (unknown-origin signal), D10 (`cantMutateAliasedHeap()`), D11 (volume control), D14 (the implementation of the strong-update test after calls: the stored sets `Etree` and `Eval`, or the on-demand test). |

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
| Soundness | Sound under A1-A5 (§3) for each program of the IR. The Lean model proves it under A1-A5: design VSS against the concrete semantics of A5 (`csoundVSS`, §3.1). |
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
| 4. Cell-named havoc with narrow reach (CN) | A cost problem, then a counterexample. Cost (user, 2026-10-29): per-cell havoc adds `havocC(s, key(o), c, [])` to each cell of each reachable origin at each call, and each symbolic object is reachable. So each call writes almost the whole heap map, and the values grow with the number of calls. Counterexample to the cheap "dead-end" rule (an unknown object gets no origin): `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, query `b ~ d`. The alias is real (`dead_realN`). | Per-cell havoc makes one origin for each call, holder and cell. The dead-end rule drops the object that the callee writes into `n.f`, so `b` and `d` share no origin. | First, narrow the concrete call semantics from A2-strict to A2-narrow: the callee reaches only the closure of its arguments and of the static roots. Second, refine the abstraction: name each unknown object by its cell (`name(o, c)`), keep the set `exposed` of the reached origins, and make each symbolic origin below an exposed origin not unique. No call creates an origin. The user rejected a lazy havoc log (it complicates state identity and the join) and accepted CN with its three precision losses (D2, 2026-10-29). Step 7 replaced CN (2026-11-03). | A2-narrow (§3.1) | `csoundCN`, `mayProgCNO_eq`, `csoundCNO`, `dead_answerCN`, `need_answersCN`, `spread_goneCN`, `gain_answersCN`; the losses `losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`; the scope `generous_reach_breaks_CN`, `generous_havoc_breaks_CN` (§4.11) |
| 5. Calls only block strong updates: a flag on origins | A cost problem, then a counterexample. Cost: at each call, CN writes a cell name into each written cell of each covered origin and into each cell of each covered allocation (R15). The user (2026-10-29) wants the cheapest call rule that does not touch the alias graph, is sound for the call policy A2-narrow, and keeps as many strong updates as possible: "the only thing we need to do after the unresolved call — prohibit some strong updates". A first form puts a flag "probably outer" on variables. Trace A: `w = x.f; e = w.g; m(x); t = x.f; t.g = z`, query `w.g ~ e`. The alias is real (`strong_after_call_realN`). `t` is read after the call, so it has no flag, and the store `t.g = z` is strong: the answer is false (`strong_after_call_nohavoc` gives the same strong store). Trace C: `t = x.f; m(x); t.g = null; u = x.f; a = u.g; b = u.g`, query `a ~ b`, is real (`traceC_realN`), and a flag on the variables must reach `u` too. | The name of a callee object is shared: each later reader of the cell gets the same origin. A flag on a variable does not reach the readers after the call. | Put the flag on origins: the set `Etree` of the reached origins (a symbolic origin with a proper prefix in `Etree` is not unique) and the set `Eval` of the origins in the reached cells (an origin in `Eval` is not unique). The call does not change `env` or `heap` (design BO). | A2-narrow (§3.1) | trace A: `strong_after_call_realN`, `strong_answersVS`; trace C: `traceC_realN`, `traceC_answerBO`, `traceC_answerVS` (§4.12) |
| 6. Block-only call (BO) | `BO0`, the first form of BO, has no heap write at a call, and a read of an empty covered cell returns its cell name. It is unsound: JOIN `x = new@5; if (*) { m(x); t = x.f } else { x.f = y }`, LOOP `x = new@5; m(x); t = x.f; while (*) { x.f = y }` and SYMBOLIC `x.f = null; if (*) { m(x); t = x.f } else { x.f = y }`, query `t ~ x.f`: `BO0` answers false, and the aliases are real (`joinBug_real`, `loopBug_real`, `symBug_real`, `bo0_unsound`). | The read rule is not monotone. A covered cell that is empty at the call can get content later without a strong update (the other branch of a join, a loop that runs zero times, a weak store, `retire`). Then a read gives only the new content, but the callee object is still in the cell. | The call writes the cell name into each reached cell that is empty, and there is no read rule (`fixed_answers`). Each other cell keeps its content. BO and CN are incomparable: BO is exact on the losses L2 and L3 of CN, and it has the new loss L4 (`bo_cn_incomparable`, `losses_BO`, `loss4_BO`, `loss4_noneN`). | A2-narrow (§3.1) | `csoundBO`, `mayProgBOO_eq`, `csoundBOO`, `eval_needed`, `bo_cn_incomparable` (§4.12) |
| 7. Value semantics of reads and the passive call (VS) | The user's correction (2026-11-03): `x = new X(); a = x.f` must give `findAlias(a) = {x.f}`, regardless of calls. A read aliases the cell, nulls included. CN and BO answer false (`user_answers`). With an identity for each null, the alias is real, also after a call (`user_real`, `user_call_real`). | This is the field-read rule, not a call rule. Concept C and the steps 1-6 have no origin for a null: a read of a null cell gives the empty set, and the reader aliases nothing. | Values carry an identity: a null is the same null for each reader of its cell. An allocation cell holds its cell name `⟨@s.c⟩` by default, and a null assignment at site `i` gives `null(i)`. So no reachable cell is empty, and the empty-cell writes of BO write nothing (`callBO_eq`). The call is fully passive: no heap write, only `Etree` and `Eval` (or the on-demand test). `retire` gives the cells of the new object their default content. Finding: definite assignment is necessary (`siteless_unsound`): new assumption A4. Finding: the on-demand test equals the stored sets only with different sites (`bw_needs_distinct_sites`); JIR has one site for each statement. Design VS is the design of the engine (D2, 2026-11-03). CN and BO stay as recorded steps. | A2-narrow with callee nulls, A4 (§3.1) | `csoundVS`, `csoundVS_W`, `mayProgVSO_eq`, `csoundVSO`, `csoundBW`, `mayProgBW_eq`, `callVSO_heap_frame`, `callVSO_frame`, `separationVS`, `added_answers`; the losses `losses_VS`, `losses_exactV`, `losses_noneV` (§4.12) |

Design bugs of the new design. The Lean model, a hand evaluation of its definitions, or a review of the design against the model found each bug before the implementation.

| First design | Counterexample | Change | Section |
|---|---|---|---|
| The fixpoint test is "state equal to the old state". | The transfer is not monotone (`astep`: a store with `pts(x) = ∅` against `{o}`). A copy-on-write add and remove gives a new object with equal content. | The change bit of the join is the signal (`joinO_flag`). | §7.10 |
| One site havoc origin for each call. | `pHv`: a value loaded after a call may-aliases each outer path. | Per-cell havoc origins under A2-strict. | §4.9 |
| Per-cell havoc origins at each call, with each symbolic object reachable. | Cost: each call writes almost the whole heap map, and the values grow with the number of calls (user, 2026-10-29). | CN under A2-narrow (step 4). Step 7 replaced CN by design VS. | §4.11 |
| An unknown object gets no origin ("dead end"): the call keeps the old content and adds nothing. | `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`: `b ~ d` is real (`dead_realN`). CN answers true (`dead_answerCN`). | The cell name: the object in `n.f` is `⟨@s.f⟩`. | §4.11 |
| The hypothesis "CN is at least as precise as per-cell havoc". | `precision_order_fails`: on `pNest` per-cell havoc answers true and CN answers false, and no execution has the alias (`nest_noneN`). The three losses go the other way. | The two rules are incomparable. The Lean examples give the losses and the nesting gain. The engine implements neither rule. | §4.11 |
| The CN call writes a cell name into each written cell of each covered origin. | Cost: each call writes many heap entries (R15); the user wants a call that only prohibits strong updates. | Design BO, then design VS: the call writes no heap entry. | §4.12 |
| A flag "probably outer" on variables blocks the strong updates after a call. | Trace A: `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. `t` has no flag, so the store is strong, and the real alias `w.g ~ e` is lost (`strong_after_call_realN`). | The flag is on origins: the sets `Etree` and `Eval`. | §4.12 |
| `BO0`: no heap write at a call; a read of an empty covered cell returns its cell name. | `joinBug_real`, `loopBug_real`, `symBug_real` (Sound/BlockOnly/Unsound.lean). | BO writes the cell name into each reached empty cell (`csoundBO`). Design VS has no empty cell, so it needs no write. | §4.12 |
| "BO is at least as precise as CN". | `bo_cn_incomparable`: BO is exact on L2 and L3, CN is exact on L4. | The two rules are incomparable. Design VS has the answers of BO on the four losses (`losses_VS`). | §4.12 |
| A read of a null cell gives no origin, because a null is no origin. | `x = new X(); a = x.f`: the user requires `a ~ x.f`; CN and BO answer false (`user_answers`); the value alias is real (`user_real`). | Design VS: values with identity, allocation cells hold their cell name by default, one origin `null(i)` for each null site. | §4.12 |
| One origin for all nulls. | Each null would alias each other null. `a = null; b = null` has no value alias (`nulls_exact`). | One origin for each null site (`nulls_answers`). | §4.12 |
| A local without an assignment holds a null. | `siteless_unsound`: `x = new@5; x.f = u; m(x); a = x.f; b = x.f` with `u` unassigned. The strong store empties the cell, and the real alias `a ~ b` is lost. | Assumption A4: definite assignment. With a null site for `u`, design VS answers true. | §3.1, §4.12 |
| "The on-demand test equals the stored sets on each loop-free program." | `bw_needs_distinct_sites`: `x = new@1; h.f = x; m(h); x = new@1; t = x.g; x.g = y`. The stored sets answer `t ~ x.g` false (exact), the on-demand test true. | The equality needs different sites (`mayProgBW_eq`). JIR has one site for each statement. The engine also ignores the calls before the allocation statement of the target (§7.6). | §4.12 |
| `entryUnique = true` is sound. | Entry aliasing: `skip_unsound`, `write_read_unsound`, `swap_strong`. | Document A1 as a precondition of the intra-procedural analysis. The user keeps the default `entryUnique = true` and accepts the loss (D1). | §3.3 |
| "Each strong store is exact." | CX4, CX5 (`corr_none`, `strongTwo_none`); null blocking CX3 (`block_none`). | Certified store scope with null kinds. | §4.7, §4.8 |
| K = D. | `deep(b)` holds itself in each cell. After a long list walk the query output is `\|cells\|^D`. | K ≥ D + 1, and the search never expands a self edge of a deep origin. | §6.2, §6.4 |
| A flat CFG worklist with accumulating loop heads. | Nested loops with strong stores: the inner head keeps stale entry states. | Recursive WTO iteration; new state arrays for each callee evaluation. | §7.10 |
| Keep the `cantMutateAliasedHeap()` exemption. | A constructor call with no reference argument does not havoc its receiver. Two loads of one field of the new object then do not alias (with the call rules before design VS). | An unresolved `<init>` always takes its receiver into the call closure. In design VS the two loads alias by the read rule, also without a call (`empty_answersVS`, `user_answers`). | §7.6 |
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
| PS10 | static field write | U3 (the directed engine keeps it on purpose, A5) |
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
- U3 is unsound against the concrete semantics: the read gets the written value. The directed engine keeps this behaviour on purpose. The user decided (D15, 2026-11-05): "ignore static writes. Always return reference to a static field on static field read (as if it was not initialized)." This is assumption A5 (§3.1). The taint analysis tracks static fields on its own. So the defect record stays, but the design does not fix U3, and probe row 28 keeps its answer in directed mode.
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
| The DSU is unsound | U1-U4, LT1 | `a1_concept`, `a2_concept`, `b_unsound`, `static_unsound` (DSU/Examples.lean): C keeps the alias | C is sound there. For U3 the engine keeps the DSU answer on purpose: it ignores static writes (A5, D15). C and design VS keep the alias because they treat a static write as an ordinary store. Design VSS, the Lean form of the static rule, does not keep it (`gapA`). |
| A sound DSU strong update in a loop | `loop { b = new; b.f = x; b.f = y }`, query `b.f ~ x` | `loop_dsu_more_precise` (DSU/Examples.lean) | Recency removes it: `loop_bf_x_exact` (Sound/Recency/Examples.lean). |
| The origin depth K of C | K = 1, `x.f.f ~ x.f.f.f` | `deep_concept_imprecise` (DSU/Examples.lean) | K ≥ D + 1 (D4). |
| The origin depth K of C, list walk | `cur = head; while (c) cur = cur.next;`, a walk longer than K | argued: `deep(head)` holds itself in each cell (`adefault`, Concept.lean) | The search rule of §6.2. |

On a root store, C with `entryUnique = true` (the default policy, D1) is more precise than the DSU: `root_concept_more_precise`.

Volume. Where dominance holds, each directed answer is a subset of the DSU answer, so it adds no alias volume (R0, §11.1). This is proved only for the heap-free fragment (`dsu_dominates_heapFree`).

---

## 3. Scope and assumptions

### 3.1 Assumptions built into the concrete semantics

The concrete semantics (`Concrete.lean`, and the instrumented semantics `ExecV` of Sound/ValueSem/Concept.lean for design VS) builds A1-A4 in. So the soundness theorems have no extra hypothesis. A5 is a decision of the user about the engine (D15). A separate concrete semantics builds it in: `ExecA5` (Sound/ValueSem/Statics.lean, row A5).

| Id | Assumption | How the concrete semantics builds it in |
|---|---|---|
| A1 | No entry aliasing. Entry roots are distinct objects. The entry heap below them is a tree. Objects that unknown expressions and calls return are new, with a tree below them. | `Obj.sym (Base.root r) p`: distinct root ids give distinct objects. `cdefault`: cell `c` of `sym b p` holds `sym b (p ++ [c])`. `Base.fresh s n` for results. |
| A2 | An unresolved call returns a new object. It keeps each cell, or writes a new value into a cell of a reachable object. Each overwritten cell gets its own new value: a new object, or (design VS) a new null. It never stores an existing value into a cell, so it never makes existing values alias. Three forms exist: A2-wide, A2-strict and A2-narrow (below). The call rule needs A2-narrow. | A2-wide: `Havoc st args s n h'`: `h' o c = st.heap o c`, or `Reach st args o` and `h' o c = sym (havoc s n k) []`. A2-strict: `HavocS` (Sound/Havoc/Concept.lean, §4.9). A2-narrow: `HavocN` (Sound/CellNamed/Concept.lean, §4.11); with callee nulls `HavocW` (Sound/ValueSem/CalleeNull.lean, §4.12). |
| A3 | Origin depth limit K for symbolic objects. The abstraction maps each deeper object to one origin `deep(b)`. | Only in the abstraction: `alpha K` maps paths longer than K to `deep b`. Concrete paths have no limit. |
| A4 | Definite assignment. Each local is assigned before it is used. The JVM verifier guarantees this for bytecode. Design VS needs it (`siteless_unsound`, §4.12). | `ExecV`: a variable that no statement assigned has no value. A copy or a store of it blocks. Frame variables are roots. So each null comes from a null site, from a default cell, or from a callee. |
| A5 | Static fields keep their initial value for the method. A read of a static field gives the value that the field had before the method. The method does not see its own static writes, and an unresolved call does not reach a value only because the method stored it in a static field. The taint analysis tracks static fields on its own. Decided by the user (D15, 2026-11-05). | `ExecA5`: as `ExecV`, but a static write of the method does not change the state, so it has no effect on the method or on its callees. A static write is a `store` (or an `astore`) through a static holder, that is a variable that the frame binds to a static root (`shB`). `execA5_iff`: `ExecA5` of `p` is `ExecV` of `stripStatic p`, the program with each static write replaced by `skip`. The callee still reaches the static roots and their entry cells (`HavocN`), but not a value that only a static write of the method put there. `ExecV` and design VS treat a static write as an ordinary store. |

A5 in the engine (§7.5). A static write `C.f = v` (`WriteStatic`) does not change the state. A static read `t = C.f` always gives `{⟨C.f⟩}`, the default content of cell `f` of the static root `⟨C⟩`. So a static root never has a heap entry.

A5 in the Lean model (Sound/ValueSem/Statics.lean). Design VSS is design VS with the static rule. A step of `analyzeVSS` does not change the state at a static write. It equals design VS on `stripStatic p` (`analyzeVSS_eq`, `mayProgVSS_eq`).

| Claim | Theorem | Status |
|---|---|---|
| Design VSS with recency is sound under A5: for each tag map `src`, each list of static roots, each K and both policies, each value alias of an `ExecA5` execution is a may-alias of `mayProgVSS`. It needs no well-formedness condition. | `csoundVSS`, `no_alias_of_mayProgVSS`, `CAliasA5_iff` | proved |
| O equals design VSS, and O is sound under A5 | `mayProgVSSO_eq`, `csoundVSSO` (§5.5) | proved |
| A static read gives exactly the default content of the cell: `{⟨C.f⟩}` for K ≥ 1 | `static_read`, `static_read_end`, `static_aread` | proved |
| For a well-formed program (`StaticWF`) in which no loop ran out of fuel (`noTopB`), each cell of each static root holds its default content at each program point | `SCInv_analyze`, `static_cells_default` | proved |

Well-formedness (`StaticWF`): a static holder is never assigned, never copied and never stored as a value. A program can give it to a call as an argument. An `astore` through a static holder is a static write, and an `aload` through it is a static read. `noTopB` is decidable, and it is true for each loop-free program (`noTopB_of_loopFree`). If a loop runs out of fuel, the analysis gives the top state, and then a static cell holds each origin. Soundness does not need `noTopB`.

Examples (Sound/ValueSem/StaticsExamples.lean, K = 1 or 2). "Exact" means that no `ExecA5` execution has the alias.

| Program | Query | VSS | Concrete fact under A5 | Theorem |
|---|---|---|---|---|
| example 6.8 of the compact specification: `C.f = v; t = C.f; u = C.f; t.g = z; m(); u.g = w` | `t ~ u` | true | real: both are the entry object `C.f` | `answers68`, `real68` |
| the same | `t ~ v` | false (design VS: true) | exact | `answers68`, `exact68` |
| the same | `pts(t)`, `pts(u)`, cell `f` of `⟨C⟩` | `{⟨C.f⟩}` exactly | — | `reads68`, `cells68` |
| the same, with `e = u.g` before `t.g = z` | `e ~ t.g` | false: `t.g = z` is strong | exact | `strong68`, `strong68_exact` |
| the same | `u.g ~ z`, `u.g ~ w` | true: `u.g = w` after the call is weak | if `u = C.f` is read after the call, a callee that writes a new object into `C.f` makes `t.g ~ z` real, so the weak update is necessary | `weak68`, `weak68_real` |

In example 6.8 itself, `u` is read before the call, so its weak update is the accepted loss L1 (§4.12).

A5 is a real restriction. Against the semantics without A5 (`ExecV` of the program itself), it has two consequences:

1. `C.f = v; t = C.f` does not give `t ~ v`. This is the DSU defect U3 (§2.3). Design VSS answers false, and an execution without A5 has the alias; design VS answers true (`gapA`). The design keeps U3 on purpose.
2. A value that the method stores only into a static field is not reached by later calls. Example: `C.f = a; e = a.h; d = e.g; m(); n = a.h; n.g = z`, query `e.g ~ d`. The call `m()` does not reach `a`, so `⟨a⟩` is not in `Etree`, and the store `n.g = z` on `⟨a.h⟩` is strong. Design VSS answers false (K = 1 and K = 2), and no `ExecA5` execution has the alias. An execution without A5 has it: the callee follows `C.f` to `a` and writes a new object into `a.h`, so `n` is the new object, `n.g = z` writes a cell of the new object, and `e.g` stays `d`. Design VS answers true (`gapB`). The gap needs a value that the method reads below the stored value after the call. A strong store through the stored variable itself loses no alias: that variable (an argument, or the object of a once allocation) denotes one object. The user accepted this consequence.

O of design VSS gives the answers of the concept on example 6.8 and on both gaps (`o_answersVSS`).

The static roots stay reach roots of each call (A2-narrow). They have no written cells, so they add only their symbolic descendants: after each call, `⟨C.f…⟩` has the reached prefix `⟨C⟩`. So with `t = C.f`, the store `t.g = z` is strong before the first call and weak after a call (example 6.8 of the compact specification, `strong68`, `weak68`).

Recorded option, not applied (`stripStaticG`): a static write `C.f = v` copies `v` into a ghost variable, and each later call gets the ghost variables as extra arguments. So `pts(v)` is in the start set of each later call, and its closure goes into `Etree` and `Eval`. The option changes no alias. It closes consequence 2 (`e.g ~ d` becomes true) and keeps the answers of example 6.8 (`t ~ u` true, `t ~ v` false). It does not close consequence 1 (`option_answers`). It is not proved sound. The first form of this option added `pts(v)` to `Etree` and `Eval` only at the static write. That form is probably weaker: it misses a write into a cell of `v` between the static write and the call, for example `C.f = a; a.h = w0; m(); t = a.h; t.k = z` (argued, not checked in Lean).

The three forms of A2:

| Form | Reach of the callee | Objects written | Abstract call rule | Sound for |
|---|---|---|---|---|
| A2-wide | each symbolic object (`Reach`) | one call can write the same new object into several cells (free tag `k`) | site havoc origin `havoc(s)` (Lean only) | A2-wide, A2-strict, A2-narrow |
| A2-strict | each symbolic object (`Reach`) | a distinct new object into each cell that the call changes (`HavocS`) | per-cell havoc origins (Lean only; the precise reference, §4.9) | A2-strict, A2-narrow |
| A2-narrow | the closure of the argument values (receiver included) and of the static roots, through cells (`ReachN`) | as A2-strict (`HavocN`); for design VS also a new null for each cell (`HavocW`) | design VS, the only call rule of the engine (§4.12); the recorded steps CN (§4.11) and BO (§4.12) | A2-narrow only |

A2-narrow is the assumption of the call rule. Statement: an unresolved callee reaches only the closure of its arguments (receiver included) and of the static roots. It keeps each reachable cell, or overwrites it with a distinct new value for each cell: a new object, or a new null. It makes no alias between existing values. Each A2-narrow execution (without callee nulls) is an A2-strict execution and an A2-wide execution (`ExecN.toExecS`, `ExecN.toExec`). Design VS is sound also with callee nulls (`csoundVS_W`). Under A1, the narrow reach is the faithful reach: an object that no argument and no static root reaches is reachable only through the locals of the method.

Both parts of A2-narrow are necessary for CN. Each part has a counterexample (Sound/CellNamed/Scope.lean). Design VS gives the CN answer on both programs (argued: on the first program `touch()` reaches only the static roots, so `⟨x⟩ ∉ Etree`, as in `gain_answersVS`; for the second program, `spread_goneVS`):

| Part removed | Program and query | CN and VS answer | Concrete fact | Theorem |
|---|---|---|---|---|
| narrow reach (the callee writes into a cell that no argument reaches) | `w = x.f; e = w.g; touch(); t = x.f; t.g = z`, query `w.g ~ e` | false: `x` is not reached (not in `Etree`; for CN: not exposed), so `t.g = z` is strong | an A2-strict execution with generous reach writes a new object into `x.f`; then `w.g` is still `e` | `generous_reach_breaks_CN` (`touch_noneN`: no A2-narrow execution has the alias) |
| strict havoc (one object in two cells) | `pHv = m(x); a = x.f; b = y.g`, query `a ~ b` | false: the names `⟨x.f⟩` and `⟨y.g⟩` differ | an A2-wide callee writes one object into `x.f` and `y.g` | `generous_havoc_breaks_CN` |

Out of scope under A2-narrow: (1) a callee that writes one new object into two cells, for example `void m(A x, B y) { Object o = new Object(); x.f = o; y.g = o; }`. The DSU also misses this shape (§4.9). (2) A callee that changes a cell of an object that its arguments and the static roots do not reach. Under A1 a Java callee cannot reach such an object: the entry trees are disjoint, and the method holds the other objects only in its locals (argued). A violation of (2) needs an entry alias, for example `this` of a singleton that a static field also holds, and §3.4 already puts that out of scope (argued). For such callees, only the taint analysis of the callee itself gives cover (§3.4).

Other properties of the concrete semantics:

| Property | Rule | Reason |
|---|---|---|
| Null dereference | A load or store through null **blocks** (no step). | Exceptions are out of the model (§3.4). |
| Values (design VS) | `VVal = obj o \| nul t`. The tag `t` of a null (`NTag`) is the default null of cell `c` of an allocated object, the n-th run of null site `i`, or (with `HavocW`) a callee null. A read and a store copy the value with its tag. | So "the same null" is observable, and `CAliasV` (the same value) is defined (§4.12). |
| Array index | `aload`/`astore` take any index `i`. | Array cells are not separated. |
| Wide reach (A2-wide, A2-strict) | `Reach` makes each symbolic object reachable by the callee. This includes entry objects that the method detached, and objects that a later unknown expression or call returns (the heap is total). | It matches the DSU idea "groups with outer elements". It makes A2-wide wider again. |
| Narrow reach (A2-narrow) | `ReachN st statics args`: the argument values, the entry objects `sym (root r) []` of the static roots `r ∈ statics`, and each object in a cell of a reachable object of the current heap. | The proofs of CN, BO and VS hold for each list `statics` (`csoundCN`, `csoundBO`, `csoundVS`). |
| Sites | Counter `cnt s` for each site. The n-th run of `new@s` makes `alloc s n`. | Distinct objects for each run. |
| Null sites (design VS) | The IR statement `null x` has no site. Design VS numbers the null statements in program order (`Prog.nulls`). The n-th run of null site `i` makes the null `nul (site i n)`. | Distinct nulls for each run. No change of the IR. |

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
| Callee-made aliasing of existing objects | out | A2 allows only new values (new objects, and new nulls in design VS). Example: an unresolved `m(x, y) { x.f = y; }`. The IFDS taint analysis covers a resolved callee through its own summary, and a library callee through its pass-through rules (argued). §9.1 lists the effect. |
| One new object in two cells | out under A2-narrow and A2-strict | §3.1 (`generous_havoc_breaks_CN`; design VS answers as CN, `spread_goneVS`). Only the Lean site havoc rule covers it; the engine has no such mode (§7.6). |
| A local that is used before it is assigned | out (A4) | `siteless_unsound` (§4.12). The JVM verifier rejects such bytecode. That JIR keeps definite assignment is argued (F13). |
| A callee that reaches an object that its arguments and the static roots do not reach | out under A2-narrow | §3.1 (`generous_reach_breaks_CN`). Under A1 a Java callee cannot reach such an object (argued). |
| Entry aliasing | out | §3.3. The user accepts the loss (D1). |
| Static roots and A1 | out | A static path and an argument (or `this` of a singleton) can be one object at entry. This breaks A1 more often than argument aliasing does. |
| Concurrency | out | Other threads can write shared cells between statements. Strong stores assume one thread. |
| Static initializers | out | A first static access can run `<clinit>`. It is not modelled as a call. |
| External pass-through models | not in the IR | §7.8 models `CopyAllMarks(from, to)` as a directed copy (`to ⊇ from`). |
| Static fields | not in the IR | The DSU model uses a static holder variable. The Lean model treats a static field as a cell of a static root, through a static holder variable. Design VS treats a static write as an ordinary store. Design VSS ignores it, as the engine does, and a static read gives `{⟨C.f⟩}` (`csoundVSS`, `static_read`, §3.1). The engine treats a static field as a cell of one static root for each class (A5, D15, §7.5). That the engine rule is the rule of design VSS is argued. |
| Static writes | out (A5) | The method does not see its own static writes, and later calls do not reach a value only through a static write (§3.1, `gapA`, `gapB`). The taint analysis tracks static fields on its own (R18). |

---

## 4. Concept C

### 4.1 Domain

Origins (`Origin`, Concept.lean):

| Origin | Denotes | Default cell content (`adefault K o c`) | Outer |
|---|---|---|---|
| `sym(b, q)`, `b = root r` or `fresh s`, `\|q\| ≤ K` | the entry object (or result object) at path `q` | `{symOrDeep K b (q ++ [c])}` | yes |
| `deep(b)` | all objects below `b` deeper than K | `{deep(b)}` | yes |
| `alloc(s)` | all objects of allocation site `s` | concept C: `∅` (null); design VS: `{⟨@s.c⟩}`, the default null of the cell, named by its cell (§4.12) | no |
| `havoc(s)` | all havoc objects of call site `s`, and all objects below them | `{havoc(s)}` | yes |
| `havocC(s, k, c, q)` | the object at path `q` below the new object that call `s` writes into cell `c` of a holder with key `k` (§4.9) | at cell `c'`: `{havocC(s, k, c, q ++ [c'])}` if `\|q\| + 1 ≤ K`, else `{havocDeep(s, k, c)}` | yes |
| `havocDeep(s, k, c)` | the objects of that tree deeper than K | `{havocDeep(s, k, c)}` | yes |
| `⟨@s.c.q⟩` (allocation child) | for `q` empty: the value in cell `c` of an object of allocation site `s`, with recency below `alloc-new(s)` or `alloc-old(s)`: in design VS the default null of the cell, or a value that a callee writes there (§4.12); in CN each object that a callee writes there (§4.11). For `q` not empty: the values at path `q` below it | at cell `c'`: `{⟨@s.c.q.c'⟩}` if `q.c'` has at most K cells, else `{deep(@s.c)}` | yes |
| `deep(@s.c)` | the values of the tree below `⟨@s.c⟩` deeper than K | `{deep(@s.c)}` | yes |
| `null(i)` (design VS) | the nulls of the null assignments at null site `i` | an own child origin (`nullKids`). A read through a null blocks, so this content is never observed. | no |

Concept C makes only the first four kinds. The per-cell refinement (§4.9) makes `havocC` and `havocDeep`. The call rule CN (§4.11) makes no call origin: it makes only allocation children, and it names every other unknown object by a symbolic or deep origin of the first rows. Design VS (§4.12) makes no call origin either. It uses the allocation children as the default content of the allocation cells, and one null origin for each null site.

Abstract state (`AState`): `env : Var → List Origin` and `heap : Origin → ACell → List Origin`. The entry heap is `adefault K`. The entry env maps each frame variable bound to root `r` to `{sym(root r, [])}`, and each other variable to `∅`. Abstract cells are `fld f` and `elem` (all array indices). In concept C and in the steps 1-6, null is no origin, and an empty set means "always null". In design VS a null is a value with an origin (`null(i)`, or the cell name of the cell that holds a default null), and in a reachable state no variable that a statement assigned and no cell holds the empty set (§4.12).

### 4.2 Uniqueness

`once s` (`Prog.onceB`): site `s` occurs at most one time in the program, and not under a loop.

`Origin.uniqueB once entryUnique` (Concept.lean):

| Origin | `uniqueB` |
|---|---|
| `sym(root r, q)` | `entryUnique` and `elem ∉ q` |
| `sym(fresh s, q)` | `entryUnique` and `once s` and `elem ∉ q` |
| `deep(b)` | false |
| `alloc(s)` | `once s` |
| `havoc(s)`, `havocC`, `havocDeep`, `⟨@s.c.q⟩`, `deep(@s.c)`, `null(i)` | false |

Recency (Sound/Recency/Concept.lean): `alloc-new(s)` (Lean `rNew s`, encoded `alloc (2s)`) is the most recent object of site `s`. `alloc-old(s)` (Lean `rOld s`, encoded `alloc (2s+1)`) is all older objects.

| Origin | `uniqueR once entryUnique` |
|---|---|
| `alloc-new(s)` | true, for each site, also in a loop |
| `alloc-old(s)` | false |
| other | `uniqueB once entryUnique` |

`retire s X`: rename `alloc-new(s)` to `alloc-old(s)` in each value. Move the cells of `alloc-new(s)` into the cells of `alloc-old(s)` (union). Give `alloc-new(s)` its default cells: empty cells in concept C, the cell names `{⟨@s.c⟩}` in design VS (`retireV`, §4.12).

With the call rule CN (Sound/CellNamed/Concept.lean), uniqueness also reads the exposed set `E` of the state: `uniqueCN = uniqueR && !expB E`. `expB E (sym(b, q))` is true if `E` holds `sym(b, p)` for a proper prefix `p` of `q`. So a symbolic origin below an exposed origin is not unique. The exposed origin itself keeps its uniqueness: a callee cannot change the value of a variable. Allocation origins and depth-0 origins (entry roots, results `sym(fresh s, [])`) keep the rules above. §4.11 gives the reason.

With design VS, the call rule of the engine (Sound/BlockOnly/Concept.lean, Sound/ValueSem/Concept.lean), uniqueness reads the two sets `Etree` and `Eval` of the state: `uniqueBO = uniqueR && !expB Etree && o ∉ Eval`. The prefix test is the test of CN with `E = Etree`. The second test also applies to allocation origins and to depth-0 origins: a call that reached a cell that held `o` can put a new value into that cell, and a later read of the cell names that value `o`. §4.12 gives the reason.

### 4.3 Transfer table

Notation: `H(o, c)` is the content of cell `c` of origin `o`. `S ∪= T` is a weak add.

| Statement | Rule of C (`astep`) | Rule with recency (`astepR`) |
|---|---|---|
| `x = new@s` | `pts(x) := {alloc(s)}` | `retire s`, then `pts(x) := {alloc-new(s)}` |
| `x = null` | `pts(x) := ∅` | same as C. Design VS: `pts(x) := {null(i)}` at null site `i` (§4.12). |
| `x = y` | `pts(x) := pts(y)` | same as C |
| `x = y.f` | `pts(x) := ⋃ { H(o, f) : o ∈ pts(y) }` | same as C |
| `x.f = y` | strong if `single? pts(x) = some o` and `o` is unique: `H(o, f) := pts(y)`. Else weak: `H(o, f) ∪= pts(y)` for each `o ∈ pts(x)`. | the same with `uniqueR` |
| `x = y[i]` | `pts(x) := ⋃ { H(o, elem) : o ∈ pts(y) }` | same as C |
| `x[i] = y` | always weak: `H(o, elem) ∪= pts(y)` for each `o ∈ pts(x)` | same as C |
| `x = unknown@s` | `pts(x) := {sym(fresh s, [])}` | `retire s`, then the same |
| `x = call@s(args)` | havoc: `H(o, c) ∪= {havoc(s)}` for each universe cell `c` and each `o` with `reachB o`. Then `pts(x) := {sym(fresh s, [])}`. Per-cell havoc: §4.9. CN: §4.11. Design VS, the call rule of the engine: no heap write, only `Etree` and `Eval` (§4.12). | havoc, then `retire s`, then the same |

The strong-update condition, as in Lean (`AState.store`):

```lean
match single? (X.env x) with
| some o => if o.uniqueB once entryUnique then X.setCell o c S else X.weakStore (X.env x) c S
| none   => X.weakStore (X.env x) c S
```

`single? l = some o` if `l` is not empty and each element is `o`. So `[o, o]` counts as one origin. With `pts(x) = ∅` the store does nothing. This is sound, because the concrete store blocks. In design VS, `pts(x)` of an assigned variable is never empty (§4.12).

Reach of a call (`reachB ctx X args`): `o` is reachable if `o` is outer, or if `o` is in the closure of `pts(args) ∪ {outer universe origins}` under all universe cells. If the closure does not converge within its fuel, each origin is reachable. This is the generous reach of A2-wide and A2-strict. CN, BO and VS use the narrow closure of §4.11 (`closeN`).

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

`CAlias fr p x px y py`: one execution of `p` from the entry state of frame `fr` ends with `x.px` and `y.py` the same object. In concept C, null is never an alias. Design VS uses the instrumented semantics `ExecV`, where the same null instance is an alias (`CAliasV`, §4.12).

| Theorem | Statement | File |
|---|---|---|
| `csound K` | `CSound K` for each K (`entryUnique = true`, the default policy). | Sound/Soundness.lean |
| `csoundE eu K ...` | The same for both policies (`mayProgE eu`). | Sound/Soundness.lean |
| `csoundR eu K ...` | The same with recency, both policies (`mayProgR eu`). | Sound/Recency/Soundness.lean |
| `csoundH src eu K ...` | Per-cell havoc without recency (`mayProgH eu`): each one-execution alias under A2-strict (`CAliasS src`), for each tag naming `src`, is a may-alias. Both policies. | Sound/Havoc/Soundness.lean |
| `csoundHR src eu K ...` | Per-cell havoc with recency (`mayProgHR eu`). The same statement, both policies. | Sound/HavocRecency/Soundness.lean |
| `csoundCN src statics eu K ...` | The call rule CN with recency (`mayProgCN eu K statics`): each one-execution alias under A2-narrow (`CAliasN src statics`) is a may-alias. For each tag naming `src`, each list of static roots, each K and both policies. | Sound/CellNamed/Soundness.lean |
| `csoundBO src statics eu K ...` | Design BO with recency (`mayProgBO`): the same statement as `csoundCN`. | Sound/BlockOnly/Soundness.lean |
| `csoundVS src statics eu K ...` | Design VS with recency (`mayProgVS`), the call rule of the engine: each one-execution value alias under A2-narrow with A4 (`CAliasV src statics`) is a may-alias. For each tag naming `src`, each list of static roots, each K and both policies. | Sound/ValueSem/Soundness.lean |
| `csoundVS_W ...` | The same, if a callee can also write a new null into a reached cell (`CAliasW`). | Sound/ValueSem/CalleeNull.lean |
| `csoundVSS src statics eu K ...` | Design VSS, design VS with the static rule (`mayProgVSS`): each one-execution value alias under A5 (`CAliasA5 src statics`) is a may-alias. The same quantifiers as `csoundVS`. | Sound/ValueSem/Statics.lean |
| `csoundBW ...` | Design VS with the on-demand test (`mayProgBW`), for each consistent oracle of the states before the calls (`ConsBW`), also with loops. | Sound/ValueSem/Backward.lean |

The first three theorems use A2-wide (`CAlias`). `csoundH` and `csoundHR` use A2-strict, and they do not hold under A2-wide (`generous_breaks_strict`, §4.9). `csoundCN` uses A2-narrow, and it holds neither with generous reach nor under A2-wide (`generous_reach_breaks_CN`, `generous_havoc_breaks_CN`, §3.1). `no_alias_of_mayProgCN` is the contrapositive: a false answer of CN excludes each A2-narrow execution with the alias. `csoundBO`, `csoundVS`, `csoundVS_W` and `csoundBW` also use A2-narrow. `csoundVS` also needs A4 (`siteless_unsound`, §4.12). `no_alias_of_mayProgVS` is its contrapositive. `csoundVSS` uses A2-narrow, A4 and A5 (`ExecA5`); `no_alias_of_mayProgVSS` is its contrapositive.

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
- With BO, the call keeps `InvBO` (`callBO_sound`, §4.12). With design VS, each statement keeps `InvVS`, the invariant of BO plus the null facts `InvN` (`step_soundVS`, §4.12).

Soundness has no hypothesis beyond the concrete semantics: A1-A4, one thread, no exceptional flow, and callees that write only new values (A2-wide for site havoc, A2-strict for per-cell havoc, A2-narrow for CN and BO, A2-narrow with callee nulls for design VS). In these theorems a static write is an ordinary store. The static rule of the engine (A5) has its own theorem: `csoundVSS` holds against the concrete semantics `ExecA5`, which builds A5 in (§3.1).

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

The completeness theorems are about concept C and object aliases. For design VS, which also reports null-valued aliases, no completeness theorem exists (F6). On the examples, each answer that design VS adds is a real value alias (`added_answers_real`, §4.12). The next scope to prove is "the core plus unresolved calls under A2-narrow" for design VS (F6). The two losses of design VS (§4.12) bound it: such a scope must exclude them. Calls are the most common reason that a method is outside the proved scopes.

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

Calls are in no proved scope. Under A2-wide, any reachable cell can get a havoc object, so we expect that each abstract `havoc(s)` edge has a concrete execution. No proof exists. Status: open (F6). §4.9 shows that A2-wide is not the right target for calls. Under the narrower call semantics, completeness counterexamples for calls exist: `cost_answers` with `cost_none` for per-cell havoc (§4.9), `precision_order_fails` with `nest_noneN` for per-cell havoc, the three losses `losses_CN` with `loss1_noneN`, `loss2_noneN`, `loss3_noneN` for CN (§4.11), and the two losses L1 and L4 of design VS: `losses_VS` with `losses_noneV` (§4.12).

### 4.9 CEGAR step 2: per-cell havoc origins (the precise reference)

Status. Per-cell havoc was the call rule until 2026-10-29. Then the user found it too expensive, and CEGAR step 4 replaced it by CN (§4.11). CEGAR step 7 replaced CN by design VS on 2026-11-03 (§4.12). Per-cell havoc stays in the Lean model only, as the formal reference of the earlier steps: it is proved sound under A2-strict. The engine does not implement it. The user dropped the engine mode `PER_CELL` on 2026-10-29 (§7.6, D2). CN and per-cell havoc are incomparable in precision (`precision_order_fails`, §4.11).

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

The second case is each constructor that the analysis does not inline (§7.6). CN answers both cases true (`need_answersCN`), and both aliases are real under A2-narrow (`strong_after_call_realN`, `empty_cell_realN`, §4.11). Design VS answers both cases true with no havoc origin (`strong_answersVS`, `empty_answersVS`, §4.12). In the first case, the call puts `⟨x⟩` into `Etree`, so the store is weak. In the second case, the cell `n.f` holds its cell name `⟨@s.f⟩` before the call, so both loads hold it, with or without the call.

Effect: on `pHv`, `a ~ b`, `a ~ z.f` and `a ~ w.g` become false. The old content of each cell stays, so the fix of U2 stays. The user decided that the may analysis keeps the old content (no alias drop, D2). Per-cell havoc was the first havoc-origin form of D2. The user replaced it by CN on 2026-10-29 (§4.11), and CN by design VS on 2026-11-03 (§4.12, §12).

### 4.10 Precision relative to the DSU

| Program | C | DSU | Exact answer | Evidence |
|---|---|---|---|---|
| task example, `x ~ y` | no | yes | no | `join_precision_loss` |
| field example after `a = w`, `x ~ y` | no | yes | no | `field_precision_loss` |
| field example, `x.f ~ z`, `y.f ~ z` | yes | yes | yes | `dsu_field_xf_z`, `field_xf_z` |
| root store `x.f = y; x.f = z`, `x.f ~ y`, policy `entryUnique = true` (the default) | no | yes | no | `root_concept_more_precise` |
| loop strong update, `b.f ~ x` | yes (C), no (recency) | no | no | `loop_dsu_more_precise`, `loop_bf_x_exact` |
| K = 1, `x.f.f ~ x.f.f.f` | yes | no | no | `deep_concept_imprecise` |
| U1, U2, U4 | yes (sound) | no (unsound) | yes | §2.3 |
| U3: `C.f = v; t = C.f`, `t ~ v` | yes in C and design VS (a static write is an ordinary store); no in design VSS and in the engine (A5, D15) | no (unsound) | yes without A5; no under A5 | `static_unsound`, `gapA` (§2.3, §3.1) |
| `pHv`, `a ~ b` after a call | yes (site havoc), no (per-cell havoc, CN, VS) | no | no under A2-strict and A2-narrow | §4.9, §4.11 (`spread_goneCN`), §4.12 (`spread_goneVS`, `spread_ab_noneV`) |
| `x = new X(); a = x.f`, `a ~ x.f` | no (C, CN, BO), yes (VS) | yes (argued: the load unions `a` with the heap element of the group of `x`) | yes, as a value alias (the same default null) | `user_answers`, `user_real` (§4.12) |

Recency keeps the other answers (`join_answers`, `field_answers`, `strong_answers`, `call_answer`, Sound/Recency/Examples.lean). Not proved: "recency is at least as precise as C" in general (F6).

The volume table of §11.1 (R0) gives the effect of each row on the alias answer volume.

### 4.11 CEGAR step 4: cell-named havoc with narrow reach (a recorded step)

Status: history. CN was the call rule of the design from 2026-10-29 (D2) to 2026-11-03. Then CEGAR steps 5-7 replaced it by design VS (§4.12). CN stays in the Lean model as a recorded refinement step. The engine does not implement it, and the compact specification does not state it. This section keeps the rule, its proof and its losses, because design VS reuses the closure, the cell names, the prefix test and the narrow semantics of CN. Short name: CN. Lean: Sound/CellNamed/ and Opt/CellNamed.lean.

History. The step started from a cost problem, not from a wrong answer:

| Order | Finding | Evidence |
|---|---|---|
| 1 | Per-cell havoc (§4.9) is too expensive (the user, 2026-10-29). At each call it adds `havocC(s, keyOf(o), c, [])` to each universe cell of each reachable origin, and each symbolic origin is reachable (§4.3). So each call writes almost the whole heap map. Each call site adds new origins, so the values grow with the number of calls. | the user; the cost of one call is linear in the number of keys (`addSets_work`, §5.5) |
| 2 | A lazy havoc log records the calls and applies them at a read. The havoc layer of the earlier engine design was such a log. The user rejected it: it complicates state identity and the join. | the user |
| 3 | A "dead-end" rule gives an unknown object no origin: the call keeps the old content and adds nothing. It is unsound. In `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, `m` can write a new object into `n.f`. Then the left branch makes `b == d`. With the dead-end rule, `pts(a) = ∅`, so `b ~ d` is false. | `dead_realN` (the alias is real); `dead_answerCN` (CN answers true) |
| 4 | CN. The user accepted it with its three precision losses (below), on 2026-10-29. | `csoundCN`, `mayProgCNO_eq` |
| 5 | The CN call writes many heap entries at each call. The user wants a call that only prohibits strong updates. Steps 5-7 lead to design VS (§4.12). | `separationVS` |

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
2. Covered origins (`coveredB R`): each origin of `R`; each `sym(b, q)` with `sym(b, p) ∈ R` and `p` a prefix of `q`; each `deep(b)` with some `sym(b, p) ∈ R`. Lean `descB` also counts the allocation children of a covered allocation. For CN this has no effect on the result: an allocation child is never unique, so its cells always keep the default child. For design VS it has an effect: the contents of the written cells of an allocation child go into `Eval` (§4.12).
3. Closure (`succsN`, `closeN`): add to `R` the content of each universe cell of each covered origin. Repeat until `R` does not grow. The closure is a checked closure with fuel, as `closeIter` of Concept.lean.
4. Fallback (`havocCN`): if the closure does not converge within its fuel, the call covers each origin and exposes each universe origin. This is sound.

Coverage includes the descendants for a reason. A callee can reach an object through a cell that the method never names. Such an object can come back to a universe name only as `deep(b)` (`reach_cover`, the `outside` part of the invariant). The model does not prove that a narrower coverage is sound. So design VS and the engine keep the rule as stated.

Call rule (`astepCN`, the call case):

1. Compute `R` (closure above).
2. Weak havoc by name (`havocWith`): for each covered origin `o` and each universe cell `c`: `H(o, c) ∪= {name(o, c)}`. The old content stays, because the callee can keep the cell. For an unwritten cell of a covered symbolic origin this changes nothing.
3. Exposure: `E := E ∪ R`.
4. Recency: `retire(s)`. Result: `pts(x) := {sym(fresh s, [])}`.

The store is `storeCN`: strong if `single? pts(x) = some o` and `uniqueCN o`, else weak. Each other statement is as in recency with per-cell havoc (`astepHR`): copy, `new` (with `retire`), null, load, array load, array store (weak), `unknown`, join, `loopIter`.

Origins of CN (Lean `originsCN`). Design VS has the same origins and adds one null origin for each null site (§4.12):

| Origin | Source |
|---|---|
| `sym(b, q)`, `deep(b)` | `b` an entry root, a static root, or the result of an unknown expression or call at site `s` (`sym(fresh s, [])`) |
| `alloc-new(s)`, `alloc-old(s)` | allocation sites (recency) |
| `⟨@s.c.q⟩`, `deep(@s.c)` | allocation sites (`heapKids`): the callee objects below allocations |

CN and design VS have no `havoc(s)`, no `havocC` and no `havocDeep`. The engine adds the constant origins of §7.5.

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
| A cost bound for the O call: at least two units, and at most `6 + 4\|U\|`, for each universe cell of each covered origin | `havocWithO_work`, `havocWithO_work_ge`, `mem_cnCells` (Opt/BlockOnlyCost.lean) | proved (F10) |
| Completeness for calls under A2-narrow | none; the three losses bound the scope | open (F6; for design VS) |

Precision losses of CN. A cell name stands for the entry object of the cell and for each object that a callee writes into the cell. So CN cannot tell these objects apart. The user accepted the three losses with CN (D2, 2026-10-29). Design VS keeps loss L1, is exact on L2 and L3, and has the new loss L4 (§4.12):

| Id | Program | Query | CN | Per-cell havoc | Concrete fact | Cause |
|---|---|---|---|---|---|---|
| L1 | `t = x.f; u = t.g; m(x); t.g = z` | `t.g ~ u` | true: `⟨x.f⟩` is below the exposed `⟨x⟩`, so `t.g = z` is weak | false | `t` holds one object, so the store is strong in each execution (`loss1_noneN`) | the old object and the new object of `m` have one name |
| L2 | `w = x.f; x.f = b; m(x); t = x.f` | `t ~ w` | true | false | `t` is `b` or a new object; never the old object in `w` (`loss2_noneN`) | the name of the new object is the entry content of `x.f` |
| L3 | `x.f = b1; m(x); a = x.f; x.f = b2; m(x); c = x.f` (two call sites; 9 and 8 in Lean) | `a ~ c` | true | false | the two calls write two different new objects (`loss3_noneN`) | the objects of two calls in one cell have one name |

`losses_CN` gives the CN answers (K = 0 and 1). `losses_HR` gives the answers of the proved per-cell analysis `mayProgHR` (generous reach), and `precision_new` gives those of the narrow reference.

Measurement status. The engine implements neither per-cell havoc nor CN. So the three losses and the opposite case (`precision_order_fails`, below) are known only from the Lean examples: `losses_CN`, `losses_HR`, `precision_new`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN` and `nest_noneN`. The shadow runs measure the alias answer volume and the call cost of design VS (§11.2), not these losses.

Comparison with per-cell havoc. The two rules are incomparable. Per-cell havoc is more precise on L1-L3. CN is more precise where per-cell havoc merges the objects of two holders that are callee objects of one call: `m(x, y)@9; m'(x, y)@8; t = x.f; a = t.g; u = y.f; b = u.g`, query `a ~ b`. The second call writes into `x.f.g` and into `y.f.g` two objects with the one origin `hsym 8 (havoc 9) g []`, because the key of a callee holder is only its call site. So per-cell havoc answers true (both `mayProgHRN` and `mayProgHR`). CN answers false (the names `⟨x.f.g⟩` and `⟨y.f.g⟩`), and no A2-narrow execution has the alias (`precision_order_fails`, `nest_noneN`). On each example query, each true answer of the narrow reference is also a true answer of CN (`precision_need`, `precision_old`, `precision_new`).

Requirements of the proof of CN. The proof depends on these rules. Design VS has the same rules for its two sets (§4.12, §7.6):

1. The exposed set takes part in each join (union) and in the loop test. In the model, `xe` is in `ctx.vars`, so `leOn` tests it. If the loop test ignores it, a loop can stop before `exposed` is stable.
2. `top` exposes each universe origin.
3. If the closure does not converge, cover each origin and expose each universe origin.
4. Coverage includes the descendants (step 2 of the closure).

### 4.12 CEGAR steps 5-7: the passive call and value semantics (the call rule)

Status: the call rule of the design (D2, decided by the user 2026-11-03). Short name: design VS. It is the only call rule of the engine (§7.6). The compact specification `directed-alias-analysis-spec.md` states it in its sections 3 to 5. Lean: Sound/ValueSem/, Opt/ValueSem.lean, Opt/ValueSemCost.lean. Design VS reuses the two sets, the store rule and the proof of design BO (Sound/BlockOnly/, Opt/BlockOnly.lean, Opt/BlockOnlyCost.lean). BO and CN (§4.11) stay in the Lean model and in this document as recorded refinement steps. The engine does not implement them.

History. The user decisions of 2026-10-29 to 2026-11-03, in order (§1.8 steps 5-7, §12):

| Order | Finding or decision | Evidence |
|---|---|---|
| 1 | The user wants the cheapest call rule that does not touch the alias graph, is sound for the call policy A2-narrow, and keeps as many strong updates as possible: "the only thing we need to do after the unresolved call — prohibit some strong updates". | the user; the heap writes of CN (`separationVS`, R15) |
| 2 | A flag "probably outer" on variables is unsound. The name of a callee object is shared by each reader of its cell, so the flag must be on origins (traces A and C, step 5). | `strong_after_call_realN`, `strong_after_call_nohavoc`, `traceC_realN` |
| 3 | Design BO: two sets `Etree` and `Eval` of origins, and no heap write at a call. Its first form `BO0`, with a read rule for empty cells, is unsound. The proved fix writes the cell name into each reached empty cell (step 6). BO and CN are incomparable. | `joinBug_real`, `loopBug_real`, `symBug_real` (Sound/BlockOnly/Unsound.lean); `csoundBO`, `bo_cn_incomparable` |
| 4 | The user's correction: `x = new X(); a = x.f` must give `findAlias(a) = {x.f}`, regardless of calls. A read aliases the cell, nulls included. This is the field-read rule, not the call rule (step 7). | `user_answers`, `user_real`, `user_call_real` |
| 5 | Design VS is the design. CN and BO stay only as recorded steps. Per-cell havoc stays the formal reference of the earlier steps (§4.9). The accepted losses are now two: loss L1 and loss L4. The losses L2 and L3 of CN are gone. | `losses_VS`, `losses_exactV`, `losses_noneV` |

**Domain.**

Values. A value is an object or a null with an identity. The null that a read finds in a cell is the same null for each reader of that cell. So `a = x.f` makes `a` alias `x.f`, also when `x.f` is null.

Origins. The origins of CN (§4.11), and one null origin `null(i)` for each null site `i`. A null site is a null assignment `x = null`, or a store `x.f = null` through a local. `null(i)` is never unique and never an allocation. One origin for all nulls would make each null alias each other null; two null sites have no value alias (`nulls_exact`). The Lean model encodes `null(i)` as `nullO i = hsym 1 (havoc i) elem []`: not unique, not an allocation origin, not symbolic.

Default content (`adefaultV K o c = [childCN K o c]`): each cell holds its cell name.

| Origin | Default content of cell `c` |
|---|---|
| `sym(b, q)` | `{symOrDeep(b, q ++ [c])}`, as in concept C |
| `deep(b)` | `{deep(b)}` |
| `alloc(s)`, `alloc-new(s)`, `alloc-old(s)` | `{⟨@s.c⟩}`: the field of a new object holds a null, and this null has the name of its cell. Concept C has `∅` here. |
| `⟨@s.c0.q⟩` | `{⟨@s.c0.q.c⟩}`, or `{deep(@s.c0)}` beyond K |
| `deep(@s.c0)` | `{deep(@s.c0)}` |
| `null(i)` | an own child origin (`nullKids`). A read through a null blocks, so this content is never observed. |

No empty cell. In a reachable state no abstract cell is empty, and each variable that a statement assigned has a non-empty set (Lean `NE`). The reasons: the entry state and `retire` give each cell its name; a null assignment gives `{null(i)}`; a strong store writes the set of an assigned variable, and that set holds the origin of its value (A4).

State. `env`, `heap`, and the two sets `Etree` and `Eval`. Both sets are empty at entry. Lean keeps them as the values of two reserved variables `xe` and `xv` (`CtxB`, `ctxVS`), so the join, the loop test and `top` treat them as each other variable.

**Transfer (`astepVS`).**

| Statement | Rule |
|---|---|
| `x = null` at null site `i` | `pts(x) := {null(i)}` |
| `x = new@s` | `retire(s)` (`retireV`): rename `alloc-new(s)` to `alloc-old(s)` in each value, `Etree` and `Eval` included; merge the cells of `alloc-new(s)` into the cells of `alloc-old(s)`; give the cells of `alloc-new(s)` their default content `{⟨@s.c⟩}`. Then `pts(x) := {alloc-new(s)}`. |
| `x = y`, `x = unknown@s` | as recency (§4.3) |
| `x = y.f`, `x = y[i]` | `pts(x) := ⋃ { H(o, f) : o ∈ pts(y) }`. The read rule of §4.3 does not change. Each cell is non-empty, so the reader holds an origin of the cell, also for a null. |
| `x.f = y` | Strong if `single? pts(x) = some o` and `uniqueBO o`: `uniqueR o` (§4.2), no proper prefix of `o` is in `Etree`, and `o ∉ Eval` (`storeBO`). Else weak. If `H(o, f) ⊆ pts(y)`, both updates give the same result. |
| `x[i] = y` | always weak |
| `x = call@s(args)` | (1) The closure `R` of CN (§4.11: `callRoots`, `coveredB`, `succsN`, `closeN`). (2) `Etree ∪= R`. (3) `Eval ∪= succsN R`: the contents of the universe cells of the covered origins, default contents included. (4) The heap and each other variable do not change. (5) `retire(s)`, then `pts(x) := {sym(fresh s, [])}`. Fallback: if the closure does not converge, both sets get each universe origin (`callVS`). |
| join | pointwise union, both sets included |
| loop | `loopIter` (§4.4). The loop test compares both sets. |

Why the passive call is enough:

- A callee can keep a cell, so the old content stays.
- A callee can write a new value into a reached cell. Each later reader of that value reads the same cell and gets its content. That content is never empty, so all readers share an origin, and they alias.
- The new value has the name of the cell content. The prefix test (`Etree`) and the `Eval` test stop a strong store through such a name from removing content that another value with the same name still holds.

Each test is necessary:

- The prefix test: trace A, `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. If `m` writes a new object into `x.f`, `t` is that object, and `w.g` is still `e`. `pts(t) = {⟨x.f⟩}` and `⟨x⟩ ∈ Etree`, so the store is weak, and `w.g ~ e` stays (`strong_answersVS`; real: `strong_realV`).
- The `Eval` test: `z = new Box(); z.g = e; x.f = z; m(x); t = x.f; t.g = v`. If `m` writes a new object into `x.f`, `t` is that object, and `z.g` is still `e`. `pts(t) = {alloc-new(s)}` and `alloc-new(s) ∈ Eval`, so the store is weak, and `z.g ~ e` stays (`eval_answerVS`; real: `eval_realV`). Without the `Eval` test the store is strong, and the real alias is lost (`eval_needed`, design BO).

Default contents in `Eval`. `Eval` includes the default contents of the covered cells. This costs no strong update: an origin of the default content of a covered cell fails the prefix test, or it is never unique (`eval_default_free`). So an implementation can leave the default contents out of `Eval` (§7.6).

**The on-demand test (Sound/ValueSem/Backward.lean, BackwardEq.lean).**

The two sets are unions over the upstream calls. So a store can compute them at the store. The contribution of an upstream call `c` is `contrib(c) = (R(c), succsN R(c))`: the closure on the state before `c`, and the contents of its covered cells (`contrib`, `callVS_contrib`). The store `x.f = y` with `pts(x) = {o}` is weak if a proper prefix of `o` is in some `R(c)`, or `o` is in some `succsN R(c)` (`storeT`, `upE`, `upV`). The call then does no work except the result (`astepBW_call`). In the structured model, the upstream calls are: in `p; q`, the calls of `p` for the points of `q`; in a choice, the calls of the same branch only; in `loop p`, each call of `p` for each point of `p` (the later calls of the body included) (`analyzeBW`).

| Claim | Theorem | Status |
|---|---|---|
| With loops: for each oracle of states before the calls that is consistent (`ConsBW`: at each call of the final pass of each loop, the oracle state dominates the analysis state outside the reserved keys), each value alias is a may-alias of the on-demand analysis | `csoundBW` (`InvBW`, `withSets`, `callOra_sound`, `InvVS.transfer`) | proved |
| The final states of the fixpoint of the engine are a consistent oracle | none | argued (F12): at the fixpoint, the state before a call is the join of all states that reach it. The dependency rule of §7.6 makes this hold in the worklist. |
| Loop-free programs with pairwise different sites: the on-demand test with the forward states before the calls (`oraOf`) gives the answers of the stored sets | `mayProgBW_eq` (`bw_eq`, `noHit_of_fresh`, `closeN_some`, `callSites_nodup`) | proved |
| With a repeated site the on-demand test is weaker: `x = new@1; h.f = x; m(h)@9; x = new@1; t = x.g; x.g = y`. The stored sets answer `t ~ x.g` false (exact); the on-demand test answers true. | `bw_needs_distinct_sites` | proved |
| `retire` does not rename the on-demand contributions. This is sound: a renamed name is `alloc-old(t)`, which is never unique. | `BlockedAll.unrename` | proved |
| The engine ignores, for a target `alloc-new(s)`, the calls before the allocation statement of `s`: the current object did not exist then (§7.6) | none | argued: a callee value of such a call is named by the earlier object, and `retire` renamed that name to `alloc-old(s)` |

JIR has one site for each statement, so `bw_needs_distinct_sites` is no problem for loop-free code. In loops the on-demand test is sound (`csoundBW`), but it can block more strong updates than the stored sets.

**Concrete semantics: values with identity (Sound/ValueSem/Concept.lean).**

The instrumented semantics `ExecV` extends the narrow semantics `ExecN` of CN:

- A value is `obj o` or `nul t` (`VVal`). The tag `t` (`NTag`) is `dflt O c` (the default null of cell `c` of the allocated object `O`), `site i n` (the n-th run of null site `i`) or `callee s n k` (a callee null; extension only).
- `VState` is the state of `Concrete.lean`, plus ghost null tags for the variables and the cells, and one counter for each null site.
- `null x` at site `i` gives `nul (site i n)`. A load copies the value of the cell, with its tag. A copy or a store needs an assigned variable (A4). A load or a store through a null blocks. The call is `HavocN`: it keeps each reached cell, or writes a new object into it.
- `CAliasV` (`AliasInV`): the two paths have the same value instance, that is the same object or the same null instance.
- Relation to `CAliasN`. An object alias is a value alias (`aliasInV_of_aliasIn`). A value alias of two objects is an object alias (`CAliasV.toN_obj`). So the value relation is wider only by null instances. On the user's program, no execution has an object alias, but a value alias exists (`user_wider`).
- Extension (Sound/ValueSem/CalleeNull.lean): `HavocW` also lets the callee write a new null `nul (callee s n k)` into a reached cell (`SStepW`, `ExecW`, `CAliasW`).

**Soundness.**

| Claim | Theorem | Status |
|---|---|---|
| Design VS with recency is sound: for each tag map `src`, each list of static roots, each K and both policies, each value alias of an `ExecV` execution is a may-alias of `mayProgVS` | `csoundVS`, `no_alias_of_mayProgVS` | proved |
| It stays sound if a callee also writes new nulls. Proof by simulation: replace each callee null by the callee object with the same tag. A load or a store through the null would block, so no step reads through the object. | `csoundVS_W` | proved |
| A4 is necessary | `siteless_unsound` | proved |
| O equals the concept, and O is sound | `mayProgVSO_eq`, `csoundVSO` (§5.5) | proved |
| With the static rule (design VSS), the analysis and O are sound under A5 | `csoundVSS`, `mayProgVSSO_eq`, `csoundVSSO` (§3.1) | proved |
| A computable executor gives value witnesses | `runAliasV`, `runAliasV_sound` (Run.lean) | proved |

Proof (Sound/ValueSem/Inv.lean, Sound/ValueSem/Soundness.lean):

- The invariant is `InvVS = ∃ G, InvG ∧ InvXB ∧ CntOKB ∧ InvN`. The first three parts are the invariant of design BO for the projected state. `InvN` adds: each null instance has its origin in the abstract set. A default null has the cell name of its object. A null of site `i` has `null(i)`.
- `NE`: no abstract cell is empty. Each step keeps it (`step_soundVS`).
- Naming. With `NE`, the call of BO equals the passive call (`callBO_eq`): the empty-cell writes of BO write nothing. So the call lemma of BO (`callBO_sound`) gives the invariant after the call. Its ghost naming: a callee object in cell `(O, c)` has the first origin of the abstract cell content as its name (`alphaBO`, `chainB`), so each reader of the object shares that origin. A callee writes only objects, so a null cell after the call was a null cell before it (`InvN.call`).
- Uniqueness. `BlockedAll` (Sound/BlockOnly/Inv.lean): each name of a callee value is in `Eval` or below `Etree`. So a unique origin denotes at most one live value (`unique_objBO`).
- Unreachable cells. A narrow call keeps each cell that the callee cannot reach (`HavocN`, `junk_keptB`).
- Queries. An alias of two objects uses the object case of the invariant. An alias of one null instance uses `InvVS.evalV_nul` (`InvVS.may_of_alias`).
- The main lemmas are `analyze_soundVS` and `inv_initVS`.

Finding: definite assignment (`siteless_unsound`). Program `x = new@5; x.f = u; m(x); a = x.f; b = x.f`, with `u` unassigned, query `a ~ b`. In the semantics of `Concrete.lean`, an unassigned variable holds a null without a site. Its abstract set is empty, so the strong store `x.f = u` makes the cell empty. If the callee writes one object into `x.f`, then `a` and `b` are the same object (real: a witness by `runAliasBN`). Design VS answers false: the call writes nothing, and the cell stays empty. With a null site (`u = null; x = new@5; ...`) design VS answers true, and the alias is real. The smallest sound fix is the assumption A4, and it needs no change of the abstract design. The JVM verifier guarantees A4 for bytecode; for JIR it is argued (F13). An alternative, not modelled: give the entry null of each unassigned local its own origin.

**Examples (Sound/ValueSem/Examples.lean).**

`x`, `y`, `z`, `w`, `h` are arguments. "Real" means that an instrumented execution has the alias, with a witness of `runAliasV`.

| Program | Query | VS | Concrete fact | Theorem |
|---|---|---|---|---|
| `x = new@5; a = x.f`, with or without `m(x)` after the allocation | `a ~ x.f` | true (CN and BO: false) | real: the same default null; with a callee write, the same object | `user_answers`, `user_real`, `user_call_real`, `user_wider` |
| `n = new N(); m(n); a = n.f; b = n.f` | `a ~ b` | true | real, with and without a callee write | `empty_answersVS`, `empty_realV` |
| JOIN, LOOP and SYMBOLIC cases of `BO0` (§1.8 step 6) | `t ~ x.f` | true | real, with and without a callee write | `bo0_cases_VS`, `bo0_cases_realV` |
| `n = null; x.f = n; m(x); a = x.f; b = x.f` | `a ~ b` | true | real: the same null of site 0, or the same object | `nullStore_answers`, `nullStore_real` |
| `a = null; b = null`; and `x = new@5; y = new@6; a = x.f; b = y.f` | `a ~ b` | false | exact: no instrumented execution | `nulls_answers`, `nulls_exact` |
| `a = null; b = a` | `a ~ b` | true | real | `nulls_answers`, `nulls_exact` |
| trace A: `w = x.f; e = w.g; m(x); t = x.f; t.g = z` | `w.g ~ e` | true (weak store) | real | `strong_answersVS`, `strong_realV` |
| `pHv = m(x); a = x.f; b = y.g` | `a ~ b`, `a ~ z.f`, `a ~ w.g` | false | `a ~ b`: exact | `spread_goneVS`, `spread_ab_noneV` |
| dead-end case (§1.8 step 4) | `b ~ d` | true | real | `dead_answerVS`, `dead_realV` |
| gain: `t = this.box; u = t.value; touch(); t.value = z` | `t.value ~ u` | false (strong store); true with `touch(this)` or with `this` as a static root | false is exact | `gain_answersVS`, `gain_noneV` |
| trace C: `t = x.f; m(x); t.g = null; u = x.f; a = u.g; b = u.g` | `a ~ b` | true | real | `traceC_answerVS`, `traceC_realV` |
| `Eval` case (above) | `z.g ~ e` | true | real | `eval_answerVS`, `eval_realV` |
| join, field, strong-update and call examples; `loop_bf_x` | as concept C with recency | unchanged | — | `other_answersVS`, `loop_bf_x_VS` |

**Precision losses.**

The strong-update test is coarse in two shapes. The user accepted both (D2, 2026-11-03):

| Id | Program | Query | VS | Concrete fact | Theorem |
|---|---|---|---|---|---|
| loss L1 | `t = x.f; u = t.g; m(x); t.g = z` | `t.g ~ u` | true: `⟨x.f⟩` has the proper prefix `⟨x⟩` in `Etree`, so `t.g = z` is weak | `t` was read before the call, so it holds one object, and the store is strong in each execution | `losses_VS`, `losses_noneV` |
| loss L4 | `u = b.value; this.box = b; touch(this); b.value = v` | `b.value ~ u` | true: the origin of `b` was in the reached cell `this.box`, so it is in `Eval`, and `b.value = v` is weak | `b` holds one object, and the store is strong in each execution | `losses_VS`, `losses_noneV` |
| L2 of CN | `w = x.f; x.f = b; m(x); t = x.f` | `t ~ w` | false | exact | `losses_VS`, `losses_exactV` |
| L3 of CN | `x.f = b1; m(x); a = x.f; x.f = b2; m'(x); c = x.f` | `a ~ c` | false | exact | `losses_VS`, `losses_exactV` |

The programs of L1 and L4 have no `null` and no `new`. So a value alias there is an object alias (`CAliasV.toN_of_nullFree`), and the no-alias facts of CN and BO apply (`loss1_noneN`, `loss4_noneN`).

**Design BO (a recorded step, Sound/BlockOnly/).**

Design BO has the two sets, the store rule and the call closure of design VS, and the domain of concept C: null is no origin, and an allocation cell is empty by default.

| Item | Result | Theorem |
|---|---|---|
| `BO0`: no heap write at a call, and a read of an empty covered cell returns its cell name | unsound: the JOIN, LOOP and SYMBOLIC programs of §1.8 step 6 | `bo0_answers`, `symBug_answers`, `joinBug_real`, `loopBug_real`, `symBug_real`, `bo0_unsound` |
| BO: the call writes the cell name into each covered cell whose content is empty, and there is no read rule | sound under A2-narrow; true on the three programs | `csoundBO`, `fixed_answers` |
| O equals the concept | proved | `mayProgBOO_eq`, `csoundBOO` (§5.5) |
| The `Eval` test is necessary | proved | `eval_needed` |
| BO and CN are incomparable: BO is exact on L2 and L3, CN is exact on L4 | proved | `bo_cn_incomparable`, `losses_BO`, `losses_exactBO`, `loss4_BO`, `loss4_noneN`, `precision_tableN` |

Design VS removes the empty-cell writes of BO: with `NE`, the BO call writes nothing (`callBO_eq`).

**Comparison of the call rules.**

| Item | CN (§4.11) | BO | VS (the engine) |
|---|---|---|---|
| Concrete semantics | A2-narrow, objects | A2-narrow, objects | A2-narrow with callee nulls, values with identity, A4 |
| Default content of an allocation cell | `∅` | `∅` | `{⟨@s.c⟩}` |
| `x = null` | `∅` | `∅` | `{null(i)}` |
| Heap writes at a call | the cell name into each cell of each covered origin | the cell name into each reached empty cell | none (`callVSO_heap_frame`) |
| Call state | the exposed set `E` | `Etree`, `Eval` | `Etree`, `Eval`, or none with the on-demand test |
| Strong-update test | recency, no proper prefix in `E` | recency, no proper prefix in `Etree`, not in `Eval` | as BO |
| `x = new X(); a = x.f`, `a ~ x.f` | false | false | true (`user_answers`) |
| loss L1 | true (loss) | true (loss) | true (loss) |
| L2, L3 | true (losses) | false (exact) | false (exact) |
| loss L4 | false (exact) | true (loss) | true (loss) |
| Heap writes on the family of `separationVS` | at least m·n | at least n at the first call | 0 |
| Soundness | `csoundCN` | `csoundBO` | `csoundVS`, `csoundVS_W`; with the static rule `csoundVSS` |
| O ≡ C | `mayProgCNO_eq` | `mayProgBOO_eq` | `mayProgVSO_eq` |

**Cost (Opt/ValueSemCost.lean, §5.5).**

| Item | Result | Theorem |
|---|---|---|
| Work of one call after the closure | at least 4, at most `(\|R\| + 5 + 4\|U\|) + (\|V\| + 5 + 4\|U\|)`, with `(R, V)` the contribution of the call and `U` the universe | `callVSO_work`, `callVSO_work_ge` |
| Heap entries that a call writes | 0, in each state | `callVSO_heap_frame`, `callVS_heap` |
| Other keys that a call changes | only the two reserved keys and the result | `callVSO_frame`, `callVSO_env_frame`, `ostepVS_call_frame`, `callVS_env_ne` |
| Work at a call with the on-demand test | none: the call is `x = unknown@s` | `astepBW_call`, `astepBW_call_args` |
| Store test | the recency test, at most K prefix lookups in `Etree` and one lookup in `Eval`; on demand, one cached test for each upstream call | `prefix_lookups_leVS`, `uniqueBO_up` |
| Read | the read of recency | `ostepVS_load` |
| Heap writes on a family, per call | VS 0; BO at least n at the first call; CN at least m·n; per-cell havoc at least m²·n² | `separationVS`, `famA_BO_first` |
| Answers that design VS adds | 4 of 9 queries on two small families (BO: 0). Each added answer is a real value alias and no object alias. | `added_answers`, `added_answers_real`, `added_answers_not_objects` |

Practical cost for each method (argued, F14). A call costs the closure and two unions, and no heap work (BO: plus one union for each covered empty cell; CN: one union for each cell of each covered origin). A store costs the recency test and at most K + 1 lookups (on demand: at most one cached test for each upstream call). A read does not change. An allocation of a loop site resets the cells of `alloc-new(s)` in `retire`: this is where BO paid at the call. The null sites add origins to the universe: one for each null site, and its child origins.

**Requirements for the engine.**

The proofs depend on these rules (§7.6):

1. Each cell has a non-empty named value. An allocation cell holds `{⟨@s.c⟩}` by default, also after `retire`. A null assignment and a null store give `{null(i)}`, with one origin for each null site. A store through a definitely assigned local never writes the empty set.
2. The call writes no heap entry. `Etree ∪= R`; `Eval ∪= ` the contents of the cells of the covered origins (the default contents can stay out: `eval_default_free`); the result is `{sym(fresh s, [])}`. Fallback: both sets get each origin.
3. Both sets take part in each join (union) and in the loop test. `top` gives both sets each origin. `retire` renames inside both sets. With the on-demand test there are no sets; then the states before the upstream calls must be consistent (`ConsBW`, F12).
4. A store is strong only for one origin that passes the recency test, has no proper prefix in `Etree`, and is not in `Eval`.
5. Coverage includes the symbolic descendants and the allocation children of a covered allocation.
6. `null(i)` is never unique, and it is never an allocation (`AliasAllocInfo`, §6.1).

One more rule of the engine (A5, D15): a static write does not change the state, and a static read gives `{⟨C.f⟩}`. The proofs above treat a static write as an ordinary store. Design VSS adds the rule, and it is sound under A5 (`csoundVSS`, `execA5_iff`); the static cells keep their default content (`static_read`, `static_cells_default`, §3.1).

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
| `x := null` | `oerase`. Design VS: `setKey` with the interned node `{null(i)}`. | none; design VS: one intern |
| `x := y.c` | `loadO`: memoized union over cells `c` of the members of the node of `y` | one union for each member |
| `x.c := y` | `storeO`: `single?` on the members of the node of `x`, and the `uniqueB` test with `ctx.entryUnique`. Strong: set `(o, c)` to the node of `y`. Weak: `addAll`. | one union for each member (weak) |
| `x[*] := y` | `weakO` | one union for each member |
| call havoc | `havocO` (site havoc): `reachB` on the denotation, then add the node `{havoc(s)}` to each reachable universe cell. `havocHO` (per-cell havoc): the same reach test, then add the interned node `{havocC(s, keyOf(o), c, [])}` to each reachable universe cell `(o, c)` (`addHv`). `havocCNO` (CN, a recorded step): `closeN` on the denotation, then one `addSets`: the exposed key gets the closure, and each universe cell of each covered origin gets its cell name. `callBOO` (BO, a recorded step): the same closure, then one `addSets` on the two reserved keys and on the covered empty cells. `callVSO` (design VS, the default): the same closure, then one `addSets` on the two reserved keys `.v xe` (`Etree`) and `.v xv` (`Eval`) only. | one union for each cell; design VS: two unions, no heap key |
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

O soundness without recency is a composition: `csoundE` and `mayProgOE_eq`. The two `mayProgE` definitions (`Sound.mayProgE`, `Opt.mayProgE`) are equal by unfolding. For this configuration, no single theorem states "a one-execution alias is an O may-alias" (F9). For the default configuration (recency with design VS), `csoundVSO` states it (below). For the recorded steps, `csoundCNO` (CN) and `csoundBOO` (BO) state it, and for recency with per-cell havoc, `csoundHRO`.

With recency (Opt/Recency.lean). The O retire `retireO ctx s T st` has two steps:

1. `mergeCells`: for each universe cell `c`, the key `(alloc-old(s), c)` gets the memoized union of the nodes of `(alloc-new(s), c)` and `(alloc-old(s), c)`. The key `(alloc-new(s), c)` is removed; its default content is null in this model. Design VS adds the cell names (`retireVO`, below). The step reads the input map and writes a second map, so the order of the cells has no effect.
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

With CN (Opt/CellNamed.lean; a recorded step). The O state is the map of Opt/Prim.lean. The exposed set is the node of one reserved variable key `.v xe`, so the O join, the change bit, the loop test and `retireO` apply to it without change. The O call `havocCNO` has four steps: `closeN` on the denotation of the state; one `addSets` (the reserved key gets the closure, and each universe cell of each covered origin gets the interned singleton of its cell name, by one memoized union); `retireO`; the result. A cell name depends only on `(o, c)`, so the second call on the same cell gives a memo hit, and the values do not grow with the number of calls (argued). The O store is the O recency store with `uniqueCN` on the node of the reserved key (`storeCNO`).

| Theorem | Statement | File |
|---|---|---|
| `havocCNO_rel`, `storeCNO_rel`, `ostepCN_rel` | The O call, the O store and each O statement represent the CN concept on every universe key. | Opt/CellNamed.lean |
| `analyzeCNO_rel`, `analyzeProgCNO_rel` | The analysis and the final O state represent the CN concept. | Opt/CellNamed.lean |
| `mayProgCNO_eq` | For both policies, each list of static roots and each program, `mayProgCNO = mayProgCN` on the variables of the program and the frame. | Opt/CellNamed.lean |
| `csoundCNO` | O with CN is sound under A2-narrow. | Opt/CellNamed.lean |
| `o_answersCN` | O gives the concept answers on the gain, loss and dead-end examples. | Opt/CellNamed.lean |

The cost of the O call of CN is bounded in Opt/BlockOnlyCost.lean: at least two units and at most `6 + 4|U|` for each universe cell of each covered origin (`havocWithO_work`, `havocWithO_work_ge`; F10).

With BO (Opt/BlockOnly.lean; a recorded step). The two sets are the nodes of two reserved keys `.v xe` and `.v xv`. `callBOO` runs `closeN` on the denotation, then one `addSets` on the two reserved keys and on the covered universe cells whose value is empty (computed before the call). `storeBOO` reads both reserved keys. `callWithO_rel`, `callBOO_rel`, `storeBOO_rel`, `ostepBO_rel`, `analyzeBOO_rel`, `analyzeProgBOO_rel`, `mayProgBOO_eq` (O equals the concept, both policies, each list of static roots), `csoundBOO`, `o_answersBO`. Cost (Opt/BlockOnlyCost.lean): `callWithO_work` (the BO call costs two interns and two unions on the reserved keys, and `6 + 4|U|` for each covered empty cell); `callBOO_frame`, `callBOO_zero_writes` (no heap write if no covered cell is empty); `emptyCells_le` (BO writes no more heap keys than CN at the same state).

With design VS (Opt/ValueSem.lean, Opt/ValueSemCost.lean; the default). The O state is the map of Opt/Prim.lean. `Etree` is the node of the reserved key `.v xe`, and `Eval` is the node of `.v xv`. So the O join, the change bit, the loop test and `retireO` apply to both sets without change. The O operations:

- `callVSO`: `closeN` on the denotation, then one `addSets` on the two reserved keys. No heap key changes.
- `retireVO`: `retireO`, then `addSets` of the cell names on the cells of `alloc-new(s)`. In this model a missing allocation cell denotes `∅`. So the model writes the default content `{⟨@s.c⟩}` explicitly. The engine computes it by rule and writes nothing (§7.9).
- `initVO`: `initO`, then the cell names on the allocation cells.
- The store is `storeBOO`. `x = null` is `setKey` with `{null(i)}`.

| Theorem | Statement | File |
|---|---|---|
| `retireVO_rel`, `setSetsO_rel`, `callVSO_rel`, `ostepVS_rel`, `analyzeVSO_rel`, `initVO_rel`, `analyzeProgVSO_rel` | Each O operation, the analysis and the final O state represent the concept of design VS on every universe key. | Opt/ValueSem.lean |
| `mayProgVSO_eq` | For both policies, each list of static roots and each program, `mayProgVSO = mayProgVS` on the variables of the program and the frame. | Opt/ValueSem.lean |
| `csoundVSO` | O with design VS is sound under A2-narrow with A4. | Opt/ValueSem.lean |
| `o_answersVS` | O gives the concept answers on the examples. | Opt/ValueSem.lean |
| `mayProgVSSO_eq`, `csoundVSSO` | O of design VSS (`mayProgVSSO`, O of design VS on `stripStatic p`) equals `mayProgVSS` on the variables of the stripped program and the frame, and it is sound under A5. | Opt/ValueSemStatics.lean |
| `o_answersVSS` | O of design VSS gives the concept answers on example 6.8 of the compact specification and on both gaps of A5 (§3.1). | Sound/ValueSem/StaticsExamples.lean |
| `callVSO_work`, `callVSO_work_ge` | One call costs, after the closure, at least 4 and at most `(\|R\| + 5 + 4\|U\|) + (\|V\| + 5 + 4\|U\|)` for the contribution `(R, V)`. | Opt/ValueSemCost.lean |
| `callVSO_heap_frame`, `callVSO_frame`, `callVSO_env_frame`, `ostepVS_call_frame` | A call changes no heap key, in each state, and no variable key except the two reserved keys and the result. | Opt/ValueSemCost.lean |
| `separationVS` | (1) A call of design VS writes no heap key, in each state. (2) On the allocation family, the first call of BO writes at least `n` heap keys (`famA_BO_first`). (3) On the family of Opt/BlockOnlyCost.lean, CN writes at least `m·n` and per-cell havoc at least `m²·n²` heap keys. | Opt/ValueSemCost.lean |
| `prefix_lookups_leVS` | The prefix test of a symbolic origin of the universe of design VS is at most K lookups. A null origin is not symbolic. | Opt/ValueSemCost.lean |
| `uniqueBO_up` | The on-demand test is the recency test and, for each upstream call, one prefix test in its closure and one membership test in its contents. | Opt/ValueSemCost.lean |
| `astepBW_call`, `astepBW_call_args` | With the on-demand test, a call is `x = unknown@s`: it computes no closure and no union, and it does not read its arguments. | Opt/ValueSemCost.lean |
| `ostepVS_load` | A read of design VS is the read of recency. | Opt/ValueSemCost.lean |
| `added_answers`, `added_answers_real`, `added_answers_not_objects` | The precision cost: on the read family `x = new; a = x.f; b = x.g; c = x.h` (6 queries) and the null family `a = null; b = a; c = null` (3 queries), design VS answers 4 of 9 true, and BO answers none. Each added answer is a real value alias and no object alias. | Opt/ValueSemCost.lean |

Limits of the equivalence:

- It holds on the universe only. `mayProgO_eq`, `mayProgRO_eq`, `mayProgHO_eq`, `mayProgHRO_eq`, `mayProgCNO_eq`, `mayProgBOO_eq` and `mayProgVSO_eq` need `x, y ∈ p.vars ++ fr.vars` (`mayProgVSSO_eq`: `x, y ∈ (stripStatic sh p).vars ++ fr.vars`). Outside, C can differ only after a loop ran out of fuel (`top`) (argued). All queries are on such variables.
- O does not remove a cell entry whose node equals the default content. This has no effect on the equivalence and on the bounds. The Kotlin state must remove such entries (§7.10).
- Not in the O model: the engine form of the call of design VS (§7.6: the closure over written cells only, the filtered nodes of `Etree` and `Eval` with their markers, `Eval` without the default contents), the default content of allocation cells by rule (§7.9, §7.11), the on-demand test with the stop at the allocation statement, its cache and its dependency rule (§7.6), the iteration strategy of §7.10, exceptional edges.

### 5.6 Cost separations

Cost models: C uses explicit sets with the sorted-merge cost `|A| + |B|` for each union or inclusion test. This is the cheapest list model for C. O counts the table `work`. Map lookups are free in the model.

| Separation | Family | C cost (lower bound) | O cost (upper bound) | Theorem (file) |
|---|---|---|---|---|
| State size | `fam n m`: `a := new 0 \| ... \| new m`, then `b := a` for `b = 1..n` | `(n+1)(m+1)` set elements | `(n+1) + (m+1)` map entries. The shared table of the same family has Θ(m²) elements (`chain_table`, Opt/Findings.lean). | `fam_csize`, `fam_osize` (Opt/Cost.lean) |
| Loop test and join | `loopFam n m`: `fam n m`, then `loop { t := 0 }` | `(n+1)(m+1)` | `20(n+m+3) + 4(6 + 4(m+1))`. Both bounds count the loop only (tests and joins), not the prefix `fam n m`. | `loopFam_sep` (Opt/LoopCost.lean) |
| Query | `qfam n`: `i := new i` for `i = 0..n`, query fields `0..c-1`, query `findAlias(0)` | enumeration `≥ (n+1)(c+1)^D` | search `≤ (n+1)((D+2)(c+2)+D)` | `qfam_sep` (Opt/QueryFam.lean) |
| Call rule | the families of `separationVS`: `n` written fields and `m` calls on one object | heap keys written: CN `≥ m·n`, per-cell havoc `≥ m²·n²`, BO `≥ n` at the first call | design VS: 0 heap keys, in each state | `separationVS`, `famA_BO_first` (Opt/ValueSemCost.lean) |

The table has two concept/optimization pairs and one comparison of call rules (row 4: all four rules run in O). C/O is the pair for the state (rows 1 and 2). Enumeration/search is the pair for the query (row 3). The search also runs on C states.

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

The proved separations compare O with C, and the call rules with each other. No theorem compares O with the DSU. This table gives the cost of each operation (argued, except the cited theorems). `|p|` is the size of a points-to set. α is the inverse Ackermann function.

| Operation | DSU | O | O worst case |
|---|---|---|---|
| copy `x = y` | one union, O(α) | share the node id, O(1) | O(1) |
| load `x = y.f` | one union with one heap element | one memo union for each member of `pts(y)`: O(`\|pts(y)\|`) memo operations | a memo miss merges two sets (`Tbl.union_work`) |
| store `x.f = y` | removal and union | strong: O(1). Weak: one memo union for each member of `pts(x)`. The strong-update test: the recency test, at most K prefix lookups in `Etree` and one lookup in `Eval` (`prefix_lookups_leVS`); on demand, one cached test for each upstream call (`uniqueBO_up`) | as load; on demand, the closures of the upstream calls on a cache miss |
| unresolved call | `invalidateOuterHeapAliases`: remove the heap elements of outer groups | design VS: the closure over the written cells of the covered origins, then two memo unions for `Etree` and `Eval`; no heap write (`callVSO_work`, `callVSO_heap_frame`, §7.6). On demand: no work at the call (`astepBW_call`) | the closure visits each written cell of a covered origin |
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
| `AliasAllocInfo(s)` in `alias(x)` | `alloc(s) ∈ pts(x)`. With recency: `alloc-new(s) ∈ pts(x)` or `alloc-old(s) ∈ pts(x)`. Never inside a heap path. A null origin `null(i)` and an allocation child `⟨@s.c.q⟩` are never allocations. |

Query for a heap path `x.π`. The seed is `T = aevalPath(x, π)`: read the cells of `π` from `pts(x)`, with default content for unwritten cells. Then run the same backward search from `T` (`heapAliases_iff`). Rules:

- The answer is every path `v.ρ` (`|ρ| ≤ D`) with `pts(v.ρ) ∩ T ≠ ∅`, except `x.π` itself. The query path `π` can be longer than D. The answer paths cannot.
- The answer cannot be derived from `findAlias(x)`. Congruence gives `v.π` for each `v` that shares an origin with `x`, if the cell is not empty. But a path can also reach the content of the cell by a write: after `x.f = z`, `z ~ x.f`, and `z` is not an alias of `x` (`field_heapAliases_x`).
- If `T` is empty, the answer is empty. In concept C this means "`x.π` is always null". In design VS, `T` is never empty in a reachable state: a null on the path has an origin (`null(i)`, or the cell name of its cell), and the answer holds the paths that may hold the same null.
- If `π` passes depth K, `T` holds `deep(b)`. Its holders are the variables that hold it and the symbolic parents at depth K. The search does not follow its self cells (§6.2). So the answer is the paths that may reach the deep summary, not all paths over all cells.
- An unwritten cell on `π` gives a default origin, for example `⟨x.f.g⟩`, or `⟨@s.c⟩` for a cell of an allocation (design VS). The query computes it by rule and does not intern it (§7.12). Its holders are the default parent cell and the variables that loaded it.
- After a strong update of `x.f`, the old holders of the cell content are no longer in the answer.

Null-valued aliases (design VS). A value is an object or a null with an identity (§4.12). So the answer also holds the paths that may hold the same null as `x`. Examples: after `x = new X(); a = x.f`, `alias(a) = {x.f}` (`user_answers`); after `p = null; r = p`, `alias(r) = {p}`; after `p = null; q = null`, `alias(q)` does not hold `p` (`nulls_answers`). The DSU of main also relates a read with its cell, null or not (argued: `x = y.f` unions `x` with the heap element, §2.1). These answers add volume (`added_answers`, R17). Each added answer is a real value alias (`added_answers_real`), but no object alias (`added_answers_not_objects`).

`AliasAllocInfo` follows the points-to set of the queried local only, not "the allocations of a group". This fixes the transitive answer for `JIRCallResolver` (CK5). A symbolic, deep, allocation child or catch origin in `pts(x)` means "a value that is not a local allocation". §8.2 (M6) uses it as an "unknown origin present" signal. A null origin `null(i)` gives no `AliasAllocInfo`, and it is not an unknown origin. An allocation child counts as an unknown origin, because it can name a callee object.

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
| Roots | Arguments and `this` are holder variables that never change. A static field is a cell of a static root origin. The engine never writes this cell (A5), so it always holds its default `⟨C.f⟩`, and its holders come by rule. | argued |

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
| same | `DirectedState` | State for each statement: environment map (with the two reserved keys `ETREE_VAR` and `EVAL_VAR` in the forward-set variant), heap map |
| same | `DirectedTransfer` | The operations of O (copy, allocate, null, load, store, the call rule, retire, join, garbage collection) |
| same | `UpstreamCalls`, `CallClosureCache` | The on-demand strong-update test (D14, §7.6): the upstream calls of each statement, and the cached call closures |
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
const val ETREE_VAR: VarId = 0
const val EVAL_VAR: VarId = 1

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
enum class OriginKind { SYM, DEEP, ALLOC, ALLOC_NEW, ALLOC_OLD, NULL_SITE, BOX_CONST, CLASS_CONST, STRING_CONST, SITE_CONST, REACHED_STATICS, REACHED_ALL }

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
    fun nullSite(site: SiteId): OriginId
    fun boxConst(boxType: String): OriginId
    fun classConst(binaryClassName: String): OriginId
    fun stringConst(value: String): OriginId
    fun siteConst(site: SiteId): OriginId
    fun reachedStatics(): OriginId
    fun reachedAll(): OriginId
    fun freeze()
}
```

`cellName(origin, cell)` is the default content of a cell by rule (§7.11): the default child of a `SYM` origin, `⟨@s.c⟩` for an allocation origin. `nullSite(site)` is `null(i)` for the null site of one JIR statement. `SiteTable` numbers the null sites of each method analysis: one site for each statement (with its context) that assigns or stores the constant `null` (§7.5). `reachedStatics()` and `reachedAll()` are the two marker origins of `Etree` and `Eval` (§7.6).

Policy and parameters:

```kotlin
enum class AliasAnalysisMode { DSU, SHADOW, DIRECTED }

enum class StrongUpdateTest { FORWARD_SETS, ON_DEMAND }

data class DirectedAliasPolicy(
    val entryUnique: Boolean = true,
    val recency: Boolean = true,
    val strongUpdateTest: StrongUpdateTest = StrongUpdateTest.ON_DEMAND,
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

Status of the defaults: `aliasAnalysisMode = DSU` (D7) and `entryUnique = true` (D1) are decided by the user. The call rule VS (D2) is decided by the user (2026-11-03). It is the only call rule, so the policy has no havoc mode field (§7.6). `strongUpdateTest` (D14) is open: the default is the recommendation `ON_DEMAND`, and `FORWARD_SETS` stays for the differential test and an A/B check. `maxCallClosure` (the closure budget of §7.6) is open until the measurement. `recency` (D3), `symDepth` and `maxAccessors` (D4), `maxQueryPaths` and `diagnosticCallDrop` (D11), and `maxTableContent` (§7.11) are open until the spec revisit. The defaults of the two D11 fields mean "no volume control" (D11 (a)).

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
    val nullOnlyPaths: Long
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

`accessorSum` is the sum of the accessor counts of the reported paths. `nullOnlyPaths` exists only on the directed path (§7.12 step 8). `cutConversions` and `cutCacheHits` exist only on the DSU path (§8.5). `AliasQueryKind` tells the facade query: `BEFORE` is `findAlias` (CS1-CS3, CS6-CS8), `AFTER` is `findAliasAfterStatement` (CS4/CS5). One `AliasVolumeStats` exists for each method analysis, and one total for each project run. Both are logged at DEBUG; the project total is also logged at INFO at the end of the run.

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
    fun assignNull(s: DirectedState, target: VarId, nullSite: SiteId): DirectedState
    fun store(s: DirectedState, stmt: Int, base: NodeId, cell: CellId, value: NodeId): DirectedState
    fun storeWeak(s: DirectedState, base: NodeId, cell: CellId, value: NodeId): DirectedState
    fun callClosure(s: DirectedState, roots: NodeId): CallContribution
    fun call(s: DirectedState, roots: NodeId, site: SiteId): DirectedState
    fun retire(s: DirectedState, site: SiteId): DirectedState
    fun dropVars(s: DirectedState, keep: (VarId) -> Boolean): DirectedState
    fun collectGarbage(s: DirectedState): DirectedState
    fun isUnique(s: DirectedState, stmt: Int, origin: OriginId): Boolean
    fun mergeAll(states: List<DirectedState>): DirectedState
    fun join(old: DirectedState?, incoming: DirectedState): Joined<DirectedState>
}

class CallContribution(val reached: NodeId, val values: NodeId)

class UpstreamCalls(val callStmts: IntArray) {
    fun upstreamOf(stmt: Int): BitSet
    fun sinceAllocation(stmt: Int, allocStmt: Int): BitSet
}

class CallClosureCache(val transfer: DirectedTransfer, val statesBefore: Array<DirectedState?>) {
    val searches: Long
    val cachedClosures: Int
    fun contribution(call: Int): CallContribution
    fun blocks(store: Int, origin: OriginId, calls: BitSet): Boolean
    fun invalidate(call: Int): IntArray
}
```

`env` and `heap` use `defaultReturnValue(ABSENT)`. Absent means default content. In design VS no reachable variable or cell holds `EMPTY_NODE`: `x.f = null` writes the node `{null(i)}` (§4.12). `EMPTY_NODE` stays the empty set of the node table. `VarTable` reserves the ids `ETREE_VAR` and `EVAL_VAR` for the two reserved keys of the forward-set variant. `isUnique` reads the two reserved nodes, or it asks `CallClosureCache` with the upstream calls of `stmt` (§7.5, §7.6).

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
| `Assign(l, Alloc(JIRNewExpr))`, `Assign(l, Alloc(JIRNewArrayExpr))` | Recency on and loop site: `retire(s)`, then `env[l] := {alloc-new(s)}`. Otherwise `env[l] := {alloc(s)}` (§7.9). Each cell of the new object holds its default content `{⟨@s.c⟩}` by rule; no heap entry is written (§4.12, §7.11). |
| `Assign(l, Alloc(JIRCatchInst))` | `env[l] := {sym(fresh(s), [])} ∪ val(v)` for each `Throw(v)` of this method or of an inlined callee with an edge to this handler. The fresh origin is outer, has the symbolic default content (as Lean `unknown`), and is never unique. No recency. |
| `Assign(l, Alloc(box valueOf call))` | `env[l] := {boxConst(T)}`: one origin for each box class `T`, for all sites. Never unique. No recency. `Boolean.valueOf` can also return the static fields `Boolean.TRUE` and `Boolean.FALSE`. The engine does not relate them (accepted loss; boxes have no reference fields). |
| `Assign(l, Alloc(inst))`, any other `inst` | `env[l] := {sym(fresh(s), [])}`. Never unique. |
| `Assign(l, RefConst(null))` | `assignNull`: `env[l] := {null(i)}`, with `i` the null site of this statement (`nullSite`, §7.3). Each JIR statement with the constant `null` has its own null site. |
| `Assign(l, RefConst(string v))` | `env[l] := {stringConst(v)}`. Keyed by value, not by site: equal literals are one object at run time. This adds aliases between locals that hold the same literal (§9.1). |
| `Assign(l, RefConst(class literal C))` | `env[l] := {classConst(C)}`, keyed by the binary name of `C`. |
| `Assign(l, RefConst(other))` | `env[l] := {siteConst(s)}` |
| `Assign(l, Primitive)` | no origin: erase the entry of `l`. |
| `Assign(l, FieldLoad(i, f))` | `env[l] := load(val(i), f)`. |
| `Assign(l, FieldLoad(Static(type), f))` | `env[l] := {⟨C.f⟩}`, that is `{symChild(symRoot(staticBase(C)), f)}`, the default content of cell `f` of the static root (key below). A static root never has a heap entry, so this is `load({symRoot(staticBase(C))}, f)` too (A5, D15). Before the first call, `⟨C.f⟩` can be unique (the `sym(root, q)` row of the uniqueness table below). After a call, `REACHED_STATICS` gives it the reached prefix `⟨C⟩`, so a store through it is weak (§7.6). |
| `Assign(l, ArrayLoad(i))` | `env[l] := load(val(i), ELEM_CELL)` |
| `Assign(l, Unknown)` | `env[l] := {sym(fresh(s), [])}` |
| `FieldStore(i, f, v)` | `store(val(i), f, val(v))`. Strong if `size(val(i)) == 1` and `isUnique(o)`, with the call test of §7.6. Else weak (`storeO_rel`, `storeRO_rel`; design VS: `storeBOO`, `ostepVS_rel`). If the cell content is a subset of `val(v)`, the store skips the test: both updates give the same result. A primitive `v` is skipped. |
| `ArrayStore(i, v)` | `storeWeak(val(i), ELEM_CELL, val(v))`. Always weak. A primitive `v` is skipped. |
| `WriteStatic(f, v)` | No change of state, as on main (A5, D15). The design keeps U3 on purpose (probe row 28 keeps its answer, Lean `static_unsound`). |
| `Call`, unresolved | `call(args + receiver, s)` (§7.6): no heap write; `Etree` and `Eval` grow (forward-set variant) or nothing happens (on-demand variant). Then `env[l] := {sym(fresh(s), [])}`. Then the pass-through models (§7.8). |
| `Call`, resolved (inlining depth 1) | Inline the callees (§7.7). |
| `Return`, `Throw` | No state change. A callee `Return` gives the value for the caller (§7.7). |

Static root key. Key the static root origin of `FieldLoad(Static(_), field)` by the binary class name `field.enclosingClass.name` of the `JIRField`. So two reads of one static field give one origin `⟨C.f⟩`, also in a generic class and in a nested class. Do not use `RefValue.Static.type` as the key: it adds `<T>` for a generic class and uses `Outer.Inner` for a nested class. Keep `AliasAccessor.Static(type)` only for the output. `BaseTable` records the mapping.

A store value can be an `Expr` (for example `x.f = "s"` or `x.f = null`). First evaluate it to a node with the `Assign` rules. Then store that node. So `x.f = null` stores `{null(i)}`, with the null site of the store statement.

Definite assignment (A4). The JVM verifier rejects bytecode that reads a local before it assigns it. So each JIR local that a statement reads holds a value (argued, F13). A root variable has its default value. A local without an entry in `env` (for example, a primitive) has no origin, and the engine never stores it as a reference.

Order inside a statement: evaluate the right side first, then write the left side. This removes the U4 cause. A self copy `x = x` is `assign(x, val(x))`, which does nothing (LT1 does not apply).

Builder notes. `Character.valueOf` is an unresolved call, because the builder list has `java.lang.Char`, not `java.lang.Character`. P6 fixes the list. A `JIRFieldRef` of an instance field without an instance gives `Expr.Alloc`; it takes the "any other `inst`" row.

Multi-dimensional arrays. `new T[n][m]` makes non-null inner arrays. For a `JIRNewArrayExpr` with `k > 1` dimensions, the default content of `ELEM_CELL` of the level-`j` array origin is `{alloc(s, j + 1)}` for `j < k`. Without this rule, `a[0]` reads as the cell name of the cell, a null. The read rule keeps the aliases of `a[0]` (§4.12), but `a[0]` then gives no `AliasAllocInfo`, and it counts as an unknown origin (M6). The cells of the innermost level hold their cell names. The Lean model has no such case.

Mixed encoding (argued). With recency on, a site that is not a loop site uses `alloc(s)`. It equals `alloc-new(s)` of Lean recency, because `alloc-old(s)` stays empty for such a site.

Uniqueness (`isUnique`), with `entryUnique = policy.entryUnique`:

| Origin | Unique | Lean source |
|---|---|---|
| `sym(root, q)`, `q` without `ELEM_CELL` | `entryUnique`, no proper prefix of the origin is in `Etree`, and the origin is not in `Eval` | `Origin.uniqueB` (Concept.lean), `uniqueBO` (Sound/BlockOnly/Concept.lean) |
| `sym(fresh s, q)`, `q` without `ELEM_CELL` | `entryUnique` and not `isLoopSite(s)`, no proper prefix in `Etree`, and not in `Eval` | same |
| allocation children `⟨@s.c.q⟩`, `deep(@s.c)` | no | `uniqueR_name`; `hsym`, `hdeep` |
| `deep(b)` | no | same |
| `alloc(s)` (recency off) | not `isLoopSite(s)`, and not in `Eval` | same (`once s`) |
| `alloc-new(s)` | not in `Eval` | `uniqueR` (Sound/Recency/Concept.lean), `uniqueBO` |
| `alloc-old(s)`, constants, `null(i)` | no | `uniqueR`, `uniqueB`, `nullO` |

With the on-demand test, "in `Etree`" and "in `Eval`" mean "in the closure, or in the contents, of an upstream call" (§7.6).

`isLoopSite(s)` is true in two cases. Case 1: the statement of `s` is on a cycle of its graph (`onCycle`). Case 2: `s` is in a callee, and the call statement is on a cycle of the caller. Each JIR statement index occurs one time in each context. So "occurs at most one time" in `Prog.onceB` holds for each JIR site.

Constructor `this`. `this` is the root `sym(root this, [])` in each method, also in `<init>`. The builder flag `This(isOuter)` has no effect on the directed engine. This fixes shapes U1.a3 and U1.a4 (Lean `a3_unsound`, `a4_unsound`): `env n = {this, alloc}` has two origins, so the store is weak. With the default `entryUnique = true` (D1), a store on `this` alone is strong in each method, also in a constructor, if no upstream call blocks it (probe row 29 keeps its answer, and probe row 30 flips, §9.3). With `entryUnique = false`, it is weak in each method (probe row 29 then loses precision against the DSU).

### 7.6 Calls: the passive call

No alias drop (D2, decided by the user). The may analysis does not drop aliases at an unresolved call. The drop of main (`invalidateOuterHeapAliases`) is a must-side rule: a callee can overwrite a cell, so a must relation through that cell ends. A future must analysis keeps the drop (§8.4). Main has no must analysis, so the directed (may) analysis removes the drop and keeps the old content of each cell.

Volume effect. On main the drop removes heap aliases after each unresolved call, so it also limits the alias answer volume. The user reports that a fix of the drop on main explodes the analysis (R0). D2 stands. The flag `diagnosticCallDrop` (D11 (e), default `false`) applies the drop of main in the directed engine, for an A/B diagnosis only: it isolates the volume effect of D2. It is unsound (U2) and never a default.

The engine has one call rule: design VS (D2, decided by the user 2026-11-03, §4.12). The call does not change the alias graph. It writes no heap entry, and it changes no variable except the result and the two reserved keys. It only prohibits later strong updates. It keeps the old content of each cell, so it fixes U2. Concrete call semantics: A2-narrow with callee nulls (§3.1). Proof state: proved (`csoundVS`, `csoundVS_W`, `mayProgVSO_eq`, `csoundVSO`, `callVSO_heap_frame`, §4.12). The engine has no switch for the call rule. The policy field `strongUpdateTest` (D14) selects how the engine computes the strong-update test: with the stored sets (`FORWARD_SETS`) or on demand (`ON_DEMAND`). On loop-free code with different sites both give the same answers (`mayProgBW_eq`).

Dropped rules. On 2026-10-29 the user dropped two call rules from the engine, and on 2026-11-03 two more (D2):

- `SHARED` (site havoc origins). As a call rule it makes each value loaded after a call alias each outer path (`havoc_spread`, R1). As a diagnostic it gives no clear signal: almost each answer after a call differs from the answer of the call rule, so a comparison cannot isolate one cause. Its only gain is the cover of a callee that writes one object into two cells (A2-wide), and that shape stays out of scope (§3.4). The site havoc rule stays in the Lean model as the proof for A2-wide (`csoundE`, `csoundR`).
- `PER_CELL` (per-cell havoc origins with the closure of CN), dropped for simplicity. It was only a diagnostic reference. It needed a separate havoc layer in the state, it had the cost that CN removes, and its narrow form is not proved sound (F11). Per-cell havoc stays in the Lean model only, as the formal reference of the earlier steps (§4.9). The losses of CN and the opposite case (`precision_order_fails`) are known from the Lean examples, not measured in the engine (§4.11).
- CN (§4.11) and BO (§4.12): recorded steps in the Lean model only. The engine writes no cell name at a call (CN) and no cell name into an empty cell (BO). Design VS makes these writes unnecessary, because no reachable cell is empty.

Reach roots. The receiver is part of the reach roots. The DSU uses only `stmt.args`. The directed engine needs the receiver: after an unresolved `x.<init>(v)`, the callee can write into the cells of the object of `x`. So the contents of these cells must go into `Eval`, and the strong updates through the names of these cells must be blocked. The static roots are reach roots of each call (A2-narrow). So each call reaches each static root. A static root has no written cell, because the engine ignores static writes (A5, §3.1). So it adds only its symbolic descendants to the closure: after each call, `⟨C.f…⟩` has the reached prefix `⟨C⟩`. A value that the method stored only into a static field is not reached (the second consequence of A5).

Constructor calls. An unresolved `<init>` call always takes its receiver into the closure, also with no reference argument. The directed engine does not use the `cantMutateAliasedHeap()` exemption of the DSU (D10). Two loads of one field of the new object alias by the read rule: both read `⟨@s.f⟩`, with or without the call (`empty_answersVS`, `empty_realV`, `user_answers`). Test: `directed two loads of a field of a new object alias with and without a constructor call`.

The closure (`callClosure`; the closure of `callVS` and `callVSO`):

1. Start set. `R := members(roots)`. `roots` is the union of the nodes of the arguments and of the receiver. Add the marker origin `REACHED_STATICS`. It stands for each static root `sym(static C, [])`, also for a class that `BaseTable` does not have yet.
2. Closure over the written heap entries only. An unwritten cell of a covered origin holds its default content, and that content is below a covered origin (the default child of a `SYM` origin, the allocation child `⟨@s.c⟩` of an allocation origin, a deep origin). So it adds no covered origin. A worklist visits each written entry `(o, c)` with `o` covered, and adds the members of its node to `R`. `o` is covered if one of these is true: `o ∈ R`; `o` is `SYM` and an ancestor of `o` (the `parent` chain, at most K steps) is in `R`; `o` is `DEEP` over base `b` and `R` has a `SYM` origin over `b`; `o` is an allocation child `⟨@t.c.q⟩` or `deep(@t.c)`, and `R` has `alloc(t)`, `alloc-new(t)`, `alloc-old(t)` or an ancestor allocation child; the base of `o` is a static root and `R` has `REACHED_STATICS`. The allocation children must be covered: the contents of their written cells go into `Eval` (§4.11, closure step 2). The worklist uses an index from a base to its written origins, and an allocation site counts as the base of its allocation children. The retire of §7.9 needs the heap grouped by origin too. `CellTable` is fixed before the fixpoint: a pre-pass collects `ELEM_CELL` and the fields of the method and of its inlined callees. A cell outside `CellTable` is not an analysis cell, and the engine never reports a path over it (§4.5). The Lean closure reads each universe cell (`succsN`). The engine closure has the same covered origins and the same test answers: the extra Lean members are default contents, which are below members of `R` (argued; F3).
3. Budget. If `R` has more than `maxCallClosure` origins, stop the closure and use the fallback: both sets get the marker `REACHED_ALL`. This is the fallback branch of `callVS`, so it is sound (`csoundVS`). On a finite heap the closure always ends. The budget only bounds its cost.
4. Contribution (`CallContribution`). `reached := intern(filterTree(R))`: the markers and the `SYM` origins with a path shorter than K. Only these can be a proper prefix of a unique origin. `values := intern(filterVal(V))`, with `V` the members of the written entries of the covered origins: the markers and the origins that can be unique (`SYM` without `ELEM_CELL`, `ALLOC`, `ALLOC_NEW`). The default contents stay out of `values`: such an origin fails the prefix test, or it is never unique (`eval_default_free`). So the filters do not change answers (argued; F3).

The call (`call`; Lean `callVSO`):

- Forward-set variant (`FORWARD_SETS`): run the closure; `env[ETREE_VAR] := union(env[ETREE_VAR], reached)`; `env[EVAL_VAR] := union(env[EVAL_VAR], values)`. These are the only two unions.
- On-demand variant (`ON_DEMAND`): no closure and no union (`astepBW_call`).
- Both: `env[l] := {sym(fresh(s), [])}` (Lean `astepVS`, call case). Then the pass-through models (§7.8). No heap entry changes (`callVSO_heap_frame`).

Uniqueness in the forward-set variant. `isUnique(s, stmt, o)` applies the table of §7.5. For a `SYM` origin with a non-empty path, it tests each proper prefix (the `parent` chain, at most K steps): the node of `ETREE_VAR` must not contain it (binary search). Then it tests `o` against the node of `EVAL_VAR`. If a node has `REACHED_ALL`, no origin that it tests is unique. If the `Etree` node has `REACHED_STATICS`, no `SYM` origin with a non-empty path over a static root is unique. Cost: at most K + 1 binary searches for each strong-store candidate (`prefix_lookups_leVS`).

The reserved keys (forward-set variant). The proof of `csoundVS` needs these rules (§4.12):

- The join makes the union of each reserved key as of each other key, and the change bit includes them. So a loop does not stop before both sets are stable.
- `dropVars` and `collectGarbage` never remove `ETREE_VAR` and `EVAL_VAR`. The garbage collection does not use their origins as roots.
- `retire` renames inside both nodes as inside each environment entry. The `Eval` node can hold `alloc-new(s)`, so the rename has an effect there.
- At method entry both keys are absent (the empty set). `top` sets both to `{REACHED_ALL}`.

The on-demand test (`ON_DEMAND`, the recommendation of D14). The state has no reserved key, and the call does no work. A store `x.f = y` computes the test only if it can be strong: `val(x)` has one origin `o`, `o` passes the recency test of §7.5, and the cell content is not a subset of `val(y)`. Then:

1. Upstream calls. A pre-pass computes, for each statement, the set of the unresolved calls on some CFG path from the entry to the statement (`UpstreamCalls.upstreamOf`, a `BitSet` over the call statements). With a loop, the later calls of the loop body are upstream too. An inlined call statement counts as one upstream call (§7.7).
2. Stop at the allocation. For a target `alloc-new(s)` (or `alloc(s)`), the engine uses only the calls on a path from the allocation statement of `s` to the store that does not pass that statement again (`UpstreamCalls.sinceAllocation`, a backward search from the store that stops at the allocation statement). The current object did not exist at the earlier calls (argued, §4.12). This also removes the repeated-site effect of `bw_needs_distinct_sites`.
3. Cached closures. For each remaining upstream call `c`, `CallClosureCache.contribution(c)` gives `(reached, values)` of the closure of `c` on the stored state before `c` (`statesBefore[c]`). The cache key is `(c, version of statesBefore[c])`. The version grows each time the stored state before `c` changes.
4. Test (`CallClosureCache.blocks`). The store is weak if a proper prefix of `o` is in some `reached` (or a marker of the node covers it), or `o` is in some `values` (`uniqueBO_up`). Else it is strong.
5. Dependency. The cache records, for each call `c`, the stores that read its contribution. When `statesBefore[c]` changes, `invalidate(c)` drops the entry and returns these stores, and the worklist evaluates them again. A change of such a state usually flows down to the store anyway (section 5.8 of the compact specification); the engine does not depend on that. With this rule, the last test of each store reads the final states before its upstream calls. So the final states form a consistent oracle for `csoundBW` (argued, F12).
6. A state before an upstream call that the worklist has not computed yet gives no contribution, and the store can be strong at first. When the state appears, step 5 evaluates the store again. The heads only grow, so the stale result is at most joined with the new result at a head, never kept alone (argued).

Why the on-demand test is the recommendation (D14). The user observes that strong updates matter mainly for reassigned fields, and such fields are rare. So few stores need the test, the closure runs only for them, and the cache shares it between the stores. The forward-set variant runs the closure at each call, also when no later store needs it, and it adds two keys to each state and to each join. With loops, the on-demand test can block more strong updates than the stored sets (sound: `csoundBW`).

Cost of one call (proved in O, §4.12). Forward sets: the closure costs `O(|W| · K)` for the written entries `W` of the covered origins, then two interns and two memoized unions (`callVSO_work`). On demand: no work at the call (`astepBW_call`). A store that needs the test does one cache lookup for each upstream call, and one closure for each cache miss (`uniqueBO_up`). In both variants no heap entry is written (`callVSO_heap_frame`), and the values of the state do not grow with the number of calls. A call on an object with a large written subtree still costs a large closure (R15). Counters: `callClosureSize`, `etreeSize`, `evalSize`, `callFallbacks`; on demand: `onDemandSearches`, `cachedClosures`, `upstreamCallsPerStore` (§11.2).

The Lean model has no written-cells-only closure, no filters, no stop at the allocation and no cache. The Lean proofs use the closure over the universe (`callVS`, `callVSO`, `analyzeBW`) (F3, F12).

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
| Callee statics | As in the caller (A5): a callee `WriteStatic` does not change the state, and a callee static read gives `{⟨C.f⟩}`. The caller and the callee share the static root origins. |
| Return | For each `JIRReturnInst` with a state after it: a reference value `v` gives `env[l] := val(v)`. A constant gives the `Assign(l, RefConst)` rule (§7.5) with the callee site. `null` gives `env[l] := {null(i)}`, with the null site of the return statement in the callee context. Never keep the old value of `l`. Then `dropVars` removes all variables with `context.level > callerLevel`. Then `collectGarbage`. |
| Join | `mergeAll` over all return states of all overrides |
| No return state | Use the unresolved model (§7.6), as on main. |
| Exceptions in the callee | A caller catch edge from the call gets `join(statesBefore[call], statesAfter[call])` (v1 rule, §7.10). |
| Calls in the callee | Unresolved (level 1 ≥ depth 1): the passive call of §7.6 on the shared state. Forward-set variant: the callee calls add to the reserved keys of the shared state, so the caller sees them. On-demand variant: the callee stores use the upstream calls of the callee body and the upstream calls of the call statement in the caller. For a caller store, the inlined call statement is one upstream call. Its contribution is the union of the contributions of the unresolved calls of the callee bodies, on the callee states of the last evaluation of the call (argued). |
| Answers | Callee variables never appear. A callee allocation origin has no root instruction index, so it gives no `AliasAllocInfo`. `mayHoldUnknownObject` is true for it (M6). A string constant from a callee is reported by value. |

A callee constructor at depth 1 writes `this.f = v` through the caller receiver. If the receiver is `{alloc-new(s)}` and no upstream call blocks it, the store is strong. So `x = new Box(v); w = x.value` gives `w ~ v` at depth 1, and `w` does not alias the default null `⟨@s.value⟩`.

### 7.8 External pass-through models (directed)

On main, `ExternalAssign(from, to)` becomes `mergeWith(from, to)`, an undirected union (PL6). The directed rule is a weak copy `to := from`:

| `to` | Rule |
|---|---|
| `RetVal`, no accessors | `env[l] := env[l] ∪ pts(from)`. The fresh return origin stays. |
| `Arg(i)` or `This`, no accessors | `env[v] := env[v] ∪ pts(from)` for the variable `v` of that call operand |
| any base with accessors `a1..ak` | `storeWeak(post(base.a1..a(k-1)), ak, pts(from))` |
| a path with `<rule-storage>` or `AnyFieldAccessor` | skip the model (CK11; main also skips `AnyFieldAccessor`) |

`pts(from)`: for a `from` with base `RetVal`, the value in the state after the return assignment (`{sym(fresh(s), [])}` plus the path). For other bases, the value in the state before the call. `post` evaluates a path in the state after the call and the return assignment. The models apply after the call, as on main. A model store `storeWeak` is a weak update, so it needs no strong-update test.

Expected answer for the sample `passThroughOfTwoArgs`: `env r = {fresh, px, py}`, `alias(x) = {arg:px, r}`, `alias(r) = {x, y, arg:px, arg:py}`.

### 7.9 Recency (`alloc-new` / `alloc-old`)

Concept C without recency is weak on a loop allocation site. There it is less precise than the DSU (`loop_dsu_more_precise`, DSU/Examples.lean; `loop_bf_x`, Examples.lean). §1.8 gives the CEGAR step and its theorems.

Transfer rule (`astepR`, `retire` in Sound/Recency/Concept.lean; `retireO` in Opt/Recency.lean), for `x = new` at site `s`, with recency on:

1. `retire(s)`, with `n = alloc-new(s)` and `o = alloc-old(s)`:
   - each written cell `c` of `n`: `heap[o, c] := union(read(o, c), read(n, c))`. Then remove all entries `(n, c)`. After this, each cell of `n` holds its default content `{⟨@s.c⟩}` by rule, with no entry (`mergeCells`; design VS: `retireV`, `retireVO`). An unwritten cell of `o` also holds `{⟨@s.c⟩}`, so the union keeps the default null of the older objects.
   - each environment entry and each heap entry whose node holds `n`: replace the node by `rename(node, n, o)` (`renameKeys`).
   - the reserved keys `ETREE_VAR` and `EVAL_VAR` are environment entries, so this step renames inside them too. The on-demand test needs no rename (`BlockedAll.unrename`, §4.12).
2. `env[x] := {n}`.

`NodeTable.rename` is memoized by `(node, from)`. A site that is not a loop site cannot hold `alloc-new(s)` before its own statement, because no path goes from the statement back to it. So only loop sites retire.

Cell names (proved: `renameO_childCN`; `csoundVS` with `retireV`; §4.11, §4.12). The cell name of `alloc-new(s)` and of `alloc-old(s)` is the same allocation child `⟨@s.c⟩`. So `retire` never renames a cell name, and the merge of step 1 keeps the names.

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

Change test at other nodes. Propagate if the new state is not equal to the old state. Use content equality (`DirectedState.equals`). Node ids are canonical (`Tbl.id_inj`), so content equality is one `Int` comparison for each key. Content equality needs one canonical form: remove a heap entry whose node equals the default content of its cell (for example after a strong store of `⟨@s.c⟩` into an allocation cell; a call writes no heap entry, §7.6). Otherwise equal states compare unequal. This costs only extra propagation, because each cycle has a head.

Do not use object identity as the change signal. A copy-on-write operation that adds and then removes an entry gives a new object with equal content. At a loop head, an identity test then makes the analysis run forever. `join` computes `changed` from the union ids: `changed` is true if some union id is not the old id for that key. The reserved keys are keys, so a growth of `Etree` or `Eval` sets the bit. This is `joinO_flag`.

On-demand variant. A store also depends on the stored states before its upstream calls. The dependency rule of §7.6 (step 5) puts the store back on the worklist when one of these states changes. The number of such changes is finite, because the states only grow at the heads (argued).

Termination (argued): the heads only grow, and the universe is finite (symbolic paths up to K, deep origins, sites, null sites, cells, allocation children up to K below each allocation site). So the heads become stable. Other nodes are functions of the heads and, in the on-demand variant, of the states before the upstream calls.

### 7.11 Data structures

| Structure | Choice | Reason |
|---|---|---|
| Node | Sorted `IntArray` of origin ids. Id 0 is the empty set. | Union and meet are linear merges. `contains` is a binary search. `Tbl.id_inj`: one id for each set, so set equality is id equality. |
| Intern map | `Object2IntOpenCustomHashMap<IntArray>(IntArrays.HASH_STRATEGY)` | Content hash and content equality on the array |
| Singletons | `IntArrayList` indexed by origin id | `singleton(o)` is the most frequent intern (new, unknown, call result). |
| Union memo | `Long2IntOpenHashMap`, key `pairKey(a, b)`, default return `-1` | Symmetric key (`mkey`). `Tbl.union_again`: each pair is merged at most one time. Before the lookup, test three cases: `a == b`, `a == 0` and `b == 0`. In each case, the result is known without the memo. |
| Rename memo | `Long2IntOpenHashMap`, key `(node shl 32) or from` | `retire` renames the same nodes in each loop iteration. |
| Default content | By rule, not stored (`OriginTable.cellName`): `sym(b, q).c → {symOrDeep(b, q + c)}`; `deep(b) → {deep(b)}`; allocations `alloc(s)`, `alloc-new(s)`, `alloc-old(s)` `.c → {⟨@s.c⟩}`; `null(i)` and constants `→` an own child origin, never observed; catch and other fresh origins as `sym(fresh s, [])`; allocation children `⟨@s.c.q⟩.c' → {⟨@s.c.q.c'⟩}`, `deep(@s.c)` beyond K (§4.1, §4.12); multi-dimensional arrays as in §7.5. No reachable cell has the empty set as its default. During the analysis, a `Long2IntOpenHashMap` caches the default node for each heap key. | Lean `adefaultV` (design VS). The heap map holds only written cells (§5.5). |
| Environment | `Int2IntOpenHashMap` `VarId → NodeId`, live reference variables only (a null variable holds `{null(i)}`), plus the reserved keys `ETREE_VAR` and `EVAL_VAR` in the forward-set variant | Copy cost `O(live vars)`. Dead variables are removed at each statement, as on main. The reserved keys are never removed. |
| Heap | `Long2IntOpenHashMap` `HeapKey → NodeId`, written cells only (a call writes no cell, §7.6) | `fam_osize`: the map part is linear in the program. |
| Heap index | written origins grouped by origin and by base (an allocation site is the base of its allocation children) | the call closure (§7.6, closure step 2) and `retire` (§7.9) |
| `Etree`, `Eval` (forward-set variant) | the nodes of `ETREE_VAR` and `EVAL_VAR`: the filtered origins of §7.6 (closure step 4) and the markers `REACHED_STATICS`, `REACHED_ALL` | no own join, comparison or copy (§7.6) |
| Upstream calls (on-demand variant) | `UpstreamCalls`: one `BitSet` over the call statements for each statement, computed one time before the fixpoint | §7.6, on-demand step 1 |
| Closure cache (on-demand variant) | `CallClosureCache`: key `(call statement, version of statesBefore[call])`, value `CallContribution` (two node ids); for each call, the list of the stores that read it | §7.6, on-demand steps 3 and 5 |
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
     - an allocation origin `alloc(s)`, `alloc-new(s)` or `alloc-old(s)` holds `⟨@s.c⟩` at `c` if the cell is not written (design VS);
     - an allocation child `⟨@s.c.q⟩` holds `⟨@s.c.q.c'⟩` at `c'` if `(⟨@s.c.q⟩, c')` is not written.
3. Backward search with suffixes, up to `maxAccessors = 6` heap accessors. Prune a child suffix if its preimage set does not meet the liveness layer of the remaining depth (`mem_live`).
4. Output: variable holders become `AliasApInfo(LocalVar | Argument | This, path)`. Static roots become `AliasApInfo(ClassStatic, [Static(T)] + path)`. Filter bases by `JIRLocalVariableReachability.isReachable(base, stmtIdx)`, as `compress` does. Drop `(x, [])` (CK4). Keep other paths with base `x`.
5. Allocation origins in `val(x)`: `AliasAllocInfo(instIdx)` for root-context `new`, `newarray` and catch sites, and for box, class and other non-string constants (CK5; both `alloc-new(s)` and `alloc-old(s)` map to `s`). String constants: `AliasApInfo(Constant("java.lang.String", v), [])` (CK6). No heap path on a `Constant` base. Never report `null`: a null origin `null(i)` and an allocation child give no `AliasAllocInfo`. The paths that hold the same null are ordinary `AliasApInfo` answers (§6.1).
6. Sort the list with one fixed comparator (kind, base, accessors). The search gives no duplicates (`search_nodup`), so no deduplication pass is necessary.
7. Path budget (D11 (c), only if `maxQueryPaths` is less than `Int.MAX_VALUE`). The search runs by suffix length: all paths with `j` accessors before the paths with `j + 1` accessors. Inside one length, the order is the comparator of step 6. The query stops after `maxQueryPaths` paths, increments `truncatedQueries`, and returns the paths so far. The cut is unsound like the cut of main, but it is a function of (state, `x`, D, budget), so it does not depend on query order. It changes CK3.
8. Volume statistics: `AliasVolumeStats.record` for each answer (§7.3). `nullOnlyPaths` counts the reported paths that share with the seed only null origins and allocation children (the null-valued aliases of §6.1, R17).

Cost: `searchCost_le`. Enumeration is exponential in D (`qfam_sep`).

| Query | Implementation |
|---|---|
| `findHeapAlias(x, π)` | The same search, seeded by `aevalPath(x, prefix)` for each prefix of `π` (`heapAliases_iff`). The JVM has no consumer (M4). Tests use it in place of `forEachHeapAlias` (probe helper `heapAnswer`). |
| `findArrayElementAliases(x)` | The search seeded by `load(val(x), ELEM_CELL)`, plus the allocation and constant origins of that node. It replaces `getAllAliasAtStatement` in the vararg branch of CS8 (M1). |
| `mayHoldUnknownObject(x)` | `val(x)` holds an origin that is not a root-context allocation, not an entry root `sym(This \| Arg, [])` and not a null origin `null(i)` (M6). An allocation child counts as unknown, because it can name a callee object. |

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
| Checkpoints | One for each evaluated statement (as `DSUAliasAnalysis.eval`), and one for each 1024 entries inside `join`, the call closure, `retire`, the on-demand search of the upstream calls and `collectGarbage`. |
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
| CK2 | Meaning of `AliasApInfo(base, accessors)` | The path may hold a value that `x` may hold at P: `pts(path) ∩ pts(x) ≠ ∅`. A value is an object or the same null (design VS, §4.12, §6.1). Same bases and accessors. |
| CK3 | Completeness up to the query depth | The backward search gives exactly the paths of the enumeration (`findAlias_iff`, `findAliasO_iff`), except paths through a deep self edge (§6.2). D is `maxAccessors = 6` (the effective value of main), a parameter. Volume controls (b), (c) and (d) of D11 change this item: a smaller D, a path budget, or simple paths only. Soundness: `csoundVS`, `csoundVS_W` (design VS, A2-narrow with callee nulls, A4), `csoundBW` (the on-demand test); the recorded steps `csoundCN`, `csoundBO`; the references `csoundE`, `csoundR` (site havoc, A2-wide) and `csoundH`, `csoundHR` (per-cell havoc, A2-strict). |
| CK4 | Exclude `(x, [])` | Step 4 of §7.12 |
| CK5 | `AliasAllocInfo(i)` if and only if `alloc(i) ∈ pts(x)` | Step 5 of §7.12. Only from `val(x)`, never from heap paths, and not from group members (the transitive set of main). Never for `null(i)` or an allocation child. |
| CK6 | String constants as `Constant`; never `null`; no heap path on a constant | `stringConst(value)` origin; step 5. A null origin gives no answer item of its own; the paths that hold the same null are reported as paths (§6.1). |
| CK7 | Determinism | §7.13. Test `directed answers do not depend on query order`. |
| CK8 | Thread-safe shared instance | §7.13. Test `directed concurrent queries give equal answers`. |
| CK9 | Cost bounds, cancellation, `null` on timeout | §7.14 |
| CK10 | Before/after at calls with a documented model | Before = the state before the call. After = the passive call (§7.6) + return + models (§7.8). Documented as a behaviour change (§9). |
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
| M5 | `forEachAliasAfterCallStatement`: no code change. The passive call (no alias drop, D2) keeps heap paths in the after set, so the intersection copies more facts (§9). A direct query is a later option. | — |
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

- Derive must-alias from O, with no second fixpoint: `must(x, p)` at P if `val(x) == val(p) == singleton(o)` and `isUnique(o)`. Then `must ⊆ may`, because equal singleton sets meet. A null origin `null(i)` is never unique, so it gives no must answer.
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
| CS1/CS2/CS3 | New edges after unresolved calls (heap paths kept) | Soundness gain. Possible new findings. | U2 (`b_unsound`, `b_local_unsound`) |
| CS1-CS6 | Static writes: no change against main. A static write does not change the state, and a static read gives `{⟨C.f⟩}`, so it does not alias the written value. A value that the method stores only into a static field is not reached by later calls. | No change (U3 stays) | A5, D15 (§3.1); `static_unsound`, `gapA`, `gapB`; probe row 28. The taint analysis tracks static fields on its own (R18). |
| CS1/CS2/CS3 | New edges where the unsound strong update of main dropped a path | Soundness gain | U1 (`a1_unsound` .. `a4_unsound`); U4 (`repr_unsound`) |
| CS1/CS2/CS3 | A store on one entry path (an argument path, `this`, a static path) is strong (D1). The old content of the cell is not kept. Under entry aliasing this can drop a taint edge. | Precision gain under A1. Accepted loss under entry aliasing. | §3.3 (`swap_strong`, `root_concept_more_precise`); probe row 30; `test swap fields` (§9.2) |
| CS1-CS6 | Two locals that hold the same string literal now alias (one `stringConst` origin for each value). Facts on one local are copied to the other. | More facts, possibly more findings | §7.5. Test in P6: `directed equal string literals in two locals alias`. |
| CS1-CS6 | Callee-made aliasing of existing objects (an unresolved `m(x, y) { x.f = y; }`) stays out of scope, as on main. | No change | §3.4. The IFDS analysis covers resolved callees through their summaries and library callees through pass-through rules (argued). Test in P6: `directed unresolved setter call does not alias the argument with the field`. |
| CS1-CS6 | Full heap chains up to D. The cut of the DSU cache (§8.5) does not occur. | More facts, longer access paths, more IFDS work | §8.5, D13. Measure in shadow mode (R0). |
| CS4/CS5 copy to aliases at calls | The after-call set keeps heap paths (the passive call, no alias drop, D2). The intersection `before ∩ after` keeps them, so more facts are copied. | More facts, possibly more findings, more IFDS work | CK10, M5. Measure in shadow mode, then on thingsboard and Conductor (R0, R4). |
| CS1-CS6 after an unresolved call | The call rule VS (§4.12). A store through a value below an object that the call reached is weak (loss L1). A store through a value that the call found in a reached cell is weak (loss L4). The old content of the cell stays. | More facts, possibly more findings: the two accepted losses (D2) | `losses_VS`, `losses_noneV` |
| CS1-CS6 after an unresolved call | A call changes only the objects that its arguments and the static roots reach. A strong update on another object stays strong. Two loads of different cells after a call do not alias. A value read after a call from a cell that a store set before the call aliases only the stored value and the values of the callee, not the entry content (L2 of CN); the values of two calls in one cell do not alias (L3 of CN). | Precision gain | `gain_answersVS`, `spread_goneVS`, `losses_exactV` (§4.12) |
| CS1-CS6 | Null-valued aliases (design VS). A local that reads an unwritten field of a new object aliases that field path (`x = new X(); a = x.f` gives `a ~ x.f`). A copy of a null aliases its source. Two null assignments do not alias. | More facts on the alias paths of a null value (volume). The effect on findings is small (argued): the shared value is a null, so no real flow goes through it, and the DSU of main also relates a read with its cell. | `user_answers`, `nulls_answers`, `added_answers` (§4.12, §6.1, R17) |
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

Counts for the default policy (`entryUnique = true` (D1), recency on). The counts were derived with per-cell havoc, before the user chose CN and then design VS. They are not derived again for design VS. At inlining depth 0 most samples have unresolved calls: `touch`, the `<init>` call of each `new`, and the `probe` call itself. So a row can change by a loss or a gain of §4.12 (argued). With design VS, a row can also get null-valued alias paths: a read of an unwritten field of a new object, or a copy of a null (§6.1). The groups are expected to stay; P5-P7 take the exact sets for design VS from the oracle (§10.1). Appendix B gives each row.

| Group | Count | Probe rows |
|---|---|---|
| Flip: precision (transitive merge removed, or a strong store on `this`) | 11 | 1, 2, 3, 4, 8, 10, 11, 30, 37, 41, 42 (row 30: both stores on `this` in a method are strong) |
| Flip: soundness (lost alias restored) | 11 | 13, 14, 15, 16, 21, 22, 24, 25, 27, 35, 36 (rows 35 and 36 also lose the false `x.next^k` chain) |
| Smaller sets with recency (precision) | 4 | 17, 18, 19, 20 |
| Precision loss against the DSU | 0 | — |
| Same answer | 16 | 5, 6, 7, 9, 12 (`null` becomes empty), 23, 26, 28 (the static write is ignored on purpose: A5, D15), 29, 31, 32, 33, 34, 38, 39, 40 |

Total: 42 rows. With the A/B value `entryUnique = false`, row 29 loses precision against the DSU (the store on `this` in a constructor is weak), and row 30 keeps its answer: 10 precision flips, 1 precision loss, 16 same answers.

The policy also changes the exact sets of rows 13-16 and 19: a store on one entry path or on `this` before the loop or the join becomes strong. Rows 13, 14 and 19 are "Rec" rows. The group of each row does not change (argued).

With recency on, the loop stores on `cur` become strong. Then the sets of rows 13, 14 and 17-20 get smaller. For example, `alias(seen)` loses `cur.value`. This is correct, because `seen` holds `pa` and `cur.value` holds `pw`. So the expected sets of the directed probes come from the naive oracle with the chosen policy (§10.1), not from a manual derivation.

---

## 10. TDD plan

### 10.1 Layers

| Layer | What | Where | How |
|---|---|---|---|
| L0 | Lean vectors as Kotlin tables | `formal/directed-alias/Export/Vectors.lean` (the library does not import it). Output committed as `JTEST/alias/directed/lean-vectors.txt`. | A small `#eval` exporter (below). `LeanVectorTest` parses the file and runs the engine through `MiniDriver`. |
| L1 | Core unit tests of O against a naive C oracle; differential and property tests | `JTEST/alias/directed/` | `NaiveConcept` is a direct Kotlin port of `astep` / `astepR` / `analyze` with explicit sets, with the null sites and the default contents of design VS. Its call case is the call case of `astepVS` (§4.12). It has both strong-update tests: the stored sets, and the on-demand test of `analyzeBW`. A seeded random generator makes structured programs. |
| L2 | JIR sample tests | `JTEST/alias/DirectedAliasProbeTest.kt`, `AliasSampleTest.kt` | Keep each `today ...` test in DSU mode. Add a `directed ...` test for each probe in directed mode. |
| L3 | Existing suites, both modes | jvm-dataflow, java-querylang, root `:test` | `-PaliasAnalysisMode=<DSU\|SHADOW\|DIRECTED>` and `-PaliasDepth=1` set the system properties `opentaint.test.aliasAnalysisMode` and `opentaint.test.aliasDepth`. Each test harness reads them (P1). |
| L4 | End to end | thingsboard first (the volume explosion reproduces there fast), then Conductor, tms, dataflowbench Java and Kotlin | §11.3 |

L0 exporter. For each example program of `Examples.lean`, `Sound/Boundary.lean` (CX1-CX7), `Sound/Recency/Examples.lean`, `Sound/StoreExamples.lean`, `Sound/EntryAlias.lean`, `Sound/Havoc/Examples.lean`, `Sound/HavocRecency/Examples.lean`, `Sound/CellNamed/Examples.lean`, `Sound/CellNamed/Scope.lean`, `Sound/CellNamed/Reference.lean`, `Sound/BlockOnly/Examples.lean`, `Sound/BlockOnly/Unsound.lean`, `Sound/ValueSem/Examples.lean`, `Sound/ValueSem/BackwardEq.lean`, `HavocNeed.lean`, `DSU/Probes.lean`, `Opt/QueryFam.lean`, `Opt/Recency.lean`, `Opt/CellNamed.lean`, `Opt/ValueSem.lean` and `Opt/ValueSemCost.lean`, print one line for each query:

```
V <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell|cellN|cn|bo|vs|vsbw> | statics=<root>,... | frame=<var>:<root>,... | prog=<s-expression> | q=<x>.<path>~<y>.<path> | may=<true|false>
F <name> | K=<k> eu=<0|1> rec=<0|1> hv=<shared|cell|cellN|cn|bo|vs|vsbw> | statics=... | frame=... | prog=... | var=<x> | D=<d> | paths=<sorted list>
```

`may` comes from `mayProg`, `mayProgE eu` or `mayProgR eu` (`hv=shared`), from `mayProgH eu` or `mayProgHR eu` (`hv=cell`, generous reach), from `mayProgHRN eu K statics` (`hv=cellN`, the narrow reference), from `mayProgCN eu K statics` (`hv=cn`), from `mayProgBO eu K statics` (`hv=bo`), from `mayProgVS eu K statics` (`hv=vs`, the default), or from `mayProgBW` with the oracle `oraOf` (`hv=vsbw`, the on-demand test). The programs of `prog` have the null statements in program order, so the exporter can print the null site of each `null` statement (`Prog.nulls`). `paths` comes from `findAlias` (Opt/Query.lean). Each `V` line has a `decide` theorem in the Lean library for the same program (for example `join_x_y`, `loop_bf_x_fixed`). So the exported value is also a proved value. P3 changes `check.sh` so that it regenerates the file and fails on a difference from the committed copy. `#eval` is data export, not a proof, so the axiom audit does not change.

L0 rule for calls. The engine answer with `strongUpdateTest = FORWARD_SETS` must be equal to each `hv=vs` vector (for example `user_answers`, `empty_answersVS`, `bo0_cases_VS`, `nullStore_answers`, `nulls_answers`, `strong_answersVS`, `spread_goneVS`, `dead_answerVS`, `gain_answersVS`, `traceC_answerVS`, `eval_answerVS`, `losses_VS`, `other_answersVS`, `loop_bf_x_VS`). The engine answer with `ON_DEMAND` must be equal to each `hv=vsbw` vector of a loop-free program with different sites (`mayProgBW_eq`), and must include each `hv=vs` answer otherwise (`csoundBW`). The `hv=shared`, `hv=cell`, `hv=cellN`, `hv=cn` and `hv=bo` vectors are Lean-only documentation of the earlier call rules. The exporter can export them, but no test reads them, because the engine has only the call rule VS (§7.6). Each Lean `*_witness`, `*_realN` and `*_realV` alias must stay in the `hv=vs` answer. Allocation children deeper than K: the engine and Lean both have one `deep(@s.c)` for each site and first cell (§4.11), so these vectors also compare by equality. The comparison of design VS with CN and with per-cell havoc (the losses L1-L4 and the nesting gain, `precision_order_fails`) is in the Lean examples only (§4.11, §4.12).

L1 differential test.

1. Generate 10 000 programs with a fixed seed: variables 0..4, fields 0..1, sites 0..3, `seq` / `choice` / `loop` up to depth 3, random frames. Use only the statement kinds of the current step (§10.2).
2. Use each combination of `entryUnique`, recency and `strongUpdateTest`, with the call rule VS (the only call rule of the engine).
3. Make `NaiveConcept` run on the same CFG with the same strategy as O (recursive WTO, §7.10). Run O with `MiniDriver` on that CFG.
4. Compare the answers for each pair of variables and each path of length 2 or less. Compare `findAlias` with enumeration. Equality is required.
5. Also run `NaiveConcept` with the structured `loopIter`. For a program whose CFG is the structured one, require equality. Else require inclusion (each structured answer is also an O answer), and record each strict difference.
6. A port of the Lean executor gives a soundness fuzz: each concrete value alias of a random run must be in the O answer. The executor follows `runAliasV` (Sound/ValueSem/Run.lean): values with identity (a null of a null site run, a default null of a cell, a callee null), each havoc write starts at an argument or a static root (A2-narrow) and writes a new object or a new null, with a distinct tag for each write. The generator assigns each local before its use (A4). `NaiveConcept` ports the call rule of §4.12 (`astepVS`).
7. Compare the two strong-update tests: on loop-free programs with different sites, the answers must be equal (`mayProgBW_eq`); with loops, each `FORWARD_SETS` answer must be an `ON_DEMAND` answer (argued: the on-demand test reads the joined states before the calls, and it can only block more), and each strict difference is recorded.

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
| P0 | — (characterization: each test asserts the answer of main) | Commit `DirectedAliasSample.java`, `DirectedAliasProbeTest` and the runtime Java witness program. Add four characterization probes. (1) A loop at the first instruction. (2) A catch after a throwing call. (3) A constructor call with no reference argument, then two loads of one field. (4) A static write, then a read, in a generic class and in a nested class (in directed mode, too, the read does not alias the written value: A5, D15). No fix. | `G-JVM` | — |
| P0a (scope `docs`) | — | This document and `formal/directed-alias/` (an ignored root for the scope check, so it can go in the same PR) | `G-LEAN` | — |
| P0c (volume baseline) | `dsu volume stats count answer paths and the maximum chain length` (answers of main unchanged); `dsu cost stats count statement evaluations and loop head iterations` (a loop sample: the counters are positive, and the answers equal main); `dsu volume stats count a cache hit of a cut chain`: query the top-level variable of a chain of 7 fields first (sample method in `HeapAliasSample.java`), then the variable that holds the inner element; the second answer stays cut, as on main, and `cutCacheHits` is 1 | `AliasVolumeStats` on the DSU path (§7.3): for each query the answer count, the maximum chain length and the accessor sum; totals for each method and each project; the fixpoint cost counters `dsuStmtEvals`, `dsuHeadIterations`, `dsuTimeMs`, `dsuStateEntries` (§11.2); `cutConversions` and `cutCacheHits` in the conversion cache (§8.5); the alias timer `aliasTimeMs`. No answer change. Then the volume baseline run (§11.3 step 1). | `G-JVM`, `G-CORE`, `G-QL`, Go CI; thingsboard, Conductor and tms findings equal to main | `DSU` only |
| P1 | `vararg element aliases equal the partition answer in dsu mode` (characterization, green before and after); `alias mode directed is accepted by params`; in each suite, a canary test that fails if the property is `DIRECTED` and the backend in use is DSU | Facade with no shared base class + `JIRDsuAliasBackend`; copies of the receiver helpers in `JIRAliasUtil.kt` (M3, D6); `Params.aliasAnalysisMode` (default `DSU`, D7; `SHADOW` works from P9a, `DIRECTED` from P5 in tests); `findArrayElementAliases` (M1, DSU implementation); `findHeapAlias` (M4, DSU implementation) and `heapAnswer` on it; delete M4 wrappers; generic `CallTreeNode<S>`; mode plumbing (list below). No change of shared code. | `G-JVM`, `G-QL`, `G-ROOT` | `DSU` only |
| P2 | `NodeTableTest`: `intern gives one id for each set`, `empty set has id zero`, `union is symmetric and memoized`, `second union of a pair is a memo hit`, `join chain grows content quadratically and nodes linearly` (numbers of `chain_table`), `rename is memoized` | `NodeTable`, `OriginTable`, `BaseTable`, `SiteTable`, `CellTable`, `VarTable` | `G-JVM` | not used yet |
| P3 | `LeanVectorTest` for `V` lines without a call and with `rec=0`; `DirectedStateLawTest` (list below); `RandomDifferentialTest` on the generator subset without calls and with recency off; `loop at the first instruction joins the back edge` | `DirectedState`, `DirectedTransfer` (copy, allocate, load, store, weak store, null with null sites), the default content by rule with `{⟨@s.c⟩}` for allocation cells (§7.11), `isUnique` and the `entryUnique` policy (default `true`, D1), `simulateGraphWto`, `weakTopologicalOrder`, `onCycle`, synthetic entry node, `MiniDriver`, `NaiveConcept`, Lean exporter, `Export/Computed.lean`, the `check.sh` regeneration check | `G-JVM`, `G-CORE`, `G-LEAN` | not used yet |
| P4 | `LeanVectorTest` `F` lines; query tests (list below) | `ReverseIndex`, `DirectedAliasQuery` on mini programs; caches; freeze; virtual origins; `AliasVolumeStats` on the directed path; the path budget `maxQueryPaths` (D11 (c), default off): test `path budget keeps the shortest paths and counts the truncated query` | `G-JVM` | not used yet |
| P5 | Directed probes for PS1, PS2, PS6-PS9, PS12, PS13 and the read-rule tests of design VS (list below); expected sets from `NaiveConcept` | `DirectedAliasAnalysis` intra-procedural, with the domain of design VS (§4.12): the null sites of JIR (`assignNull`, null stores, null returns), the allocation default content, the read rule, `null(i)` excluded from `AliasAllocInfo`. Unresolved calls with the provisional rule: the fallback of design VS (both reserved keys `{REACHED_ALL}`, §7.6 closure step 3; sound by `csoundVS`), return value `{sym(fresh(s), [])}`, and the `<init>` receiver rule (§7.6). `JIRDirectedAliasBackend`, base conversion, exceptional edges, catch origin, `collectGarbage`, exactness certificate (`exactMethods`) | `G-JVM` (DSU tests unchanged, new directed tests green) | `DIRECTED` in tests only |
| P6 | PS4 flips and call tests (list below); `LeanVectorTest` for `V` lines with `hv=vs` and `hv=vsbw` | The call rule VS (D2, decided by the user 2026-11-03; no alias drop, no heap write): the closure over written cells with its budget, fallback and filters; the forward-set variant with `ETREE_VAR`, `EVAL_VAR` and the markers; the on-demand variant (D14) with `UpstreamCalls`, the stop at the allocation statement, `CallClosureCache` and the dependency rule; `isUnique` with the call test; the counters of §11.2 (§7.6). Also static reads with the static root key (`WriteStatic` stays a no-op, A5, D15), directed models, `<rule-storage>` filter, constants (boxes, class literals, strings), multi-dimensional arrays, constant returns, the builder box list; the diagnostic flag `diagnosticCallDrop` (D11 (e), default off): test `diagnostic call drop gives the answer of main for an unknown call on the argument` (probe row 21) | `G-JVM` | tests only |
| P7 | PS3 directed probes (list below); Lean vectors with `rec=1` (`loop_bf_x_fixed`, `loop_bf_y` of Sound/Recency/Examples.lean; `o_loop_bf_x` of Opt/Recency.lean); `directed this field write in a method is a strong update under the default policy` (probe row 30, D1) | Recency (`retire` with the default cells of `alloc-new(s)` and the rename inside the reserved keys, loop sites), constructor `this` as root | `G-JVM`, `G-LEAN` | tests only |
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
- P5 probes: `directed join of two allocations keeps x apart from y`, `directed join of two arguments keeps x apart from y`, `directed field write through a join of allocations keeps x f and y f with z and keeps x apart from y`, `directed load into the live root of the instance group keeps the aliased load`, `directed two loads of a field of a new object alias with and without a constructor call` (`empty_answersVS`, `user_answers`), `directed catch after a throwing call keeps the value before the call`, `directed catch variable fields alias the thrown object fields`; the read rule of design VS: `directed read of an unwritten field of a new object aliases the field` (`user_answers`, `user_real`), `directed two null assignments do not alias` (`nulls_answers`, `nulls_exact`), `directed copy of a null aliases its source` (`nulls_answers`), `directed unwritten fields of two allocations do not alias` (`nulls_answers`), `directed null is never an allocation info` (§6.1), `directed retire gives the new object its cell names` (`retireV`).
- P6 call tests: `directed unknown call on the argument keeps the loaded field alias` and the other four PS4 flips; `directed jdk call on the argument keeps the loaded field alias`; `directed call writes no heap entry` (`callVSO_heap_frame`); `directed value loaded after a call does not alias unrelated outer paths` (`spread_goneVS`); `directed store through a field loaded after a call is weak` (`strong_answersVS`, `strong_realV`); `directed two loads of a cell of a new object after a call alias` (`empty_answersVS`, `empty_realV`); `directed join and loop cases of an empty cell keep the alias` (`bo0_cases_VS`, `bo0_cases_realV`); `directed null store then call keeps the two reads aliased` (`nullStore_answers`, `nullStore_real`); `directed dead end case keeps b alias d` (`dead_answerVS`, `dead_realV`); `directed call without arguments keeps the strong update on this box value` and `directed call on this makes the update on this box value weak` (`gain_answersVS`); `directed unrelated static root does not reach this` (`gain_answersVS`); `directed trace c keeps a alias b` (`traceC_answerVS`, `traceC_realV`); `directed store on a value found in a reached cell is weak` (`eval_answerVS`, `eval_realV`); `directed loss one store after a call on the holder is weak` and `directed loss four store on a value of a reached cell is weak` (`losses_VS`, `losses_noneV`); `directed value after a call does not alias the entry field after a store` and `directed values of two calls in one cell do not alias` (L2 and L3 of CN, `losses_exactV`); `directed reached sets grow at a loop head and the loop runs again` (§4.12, requirement 3); `directed closure over budget blocks all strong updates` (§7.6, closure step 3); `directed closure covers the allocation children of a reached allocation` (§7.6, closure step 2); `directed retire keeps the cell names of a loop allocation` (`renameO_childCN`); `directed on demand test equals the forward sets on a loop free method` (`mayProgBW_eq`); `directed on demand test ignores the calls before the allocation of the target` (§7.6, on-demand step 2; the shape of `bw_needs_distinct_sites`); `directed on demand test evaluates a store again when the state before an upstream call changes` (§7.6, on-demand step 5); `directed on demand test reuses a cached closure` (`cachedClosures`); `directed static field write is ignored so the static read does not alias the written value` (probe row 28, A5); `directed two static reads in a generic class and in a nested class alias each other` (the static root key); `directed store through a static read is strong before a call and weak after a call` (example 6.8 of the compact specification); `directed pass-through models of two arguments keep x apart from y`; `directed equal string literals in two locals alias`; `directed constant return replaces the old value`; `directed unresolved setter call does not alias the argument with the field`; `directed one new object in two cells is out of scope under the narrow call semantics` (the shape of §3.1, `generous_havoc_breaks_CN`, `spread_goneVS`).
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
| R1 | The two accepted losses of design VS keep answers after calls: a weak store below an object that a call reached (loss L1), and a weak store on a value that a call found in a reached cell (loss L4). The old content of the cell stays. A part of R0. (Site havoc, which made each value loaded after a call alias each outer path, is not in the engine.) | `losses_VS`, `losses_noneV` (§4.12); `havoc_spread` (§4.9) | Accepted by the user (D2, 2026-11-03). The losses are known from the Lean examples (§4.12); the engine does not count them. The shadow runs measure the volume of design VS against the DSU (§11.2). The on-demand test can block more strong updates in loops than the stored sets (`csoundBW`); the L1 differential test records the differences (§10.1). If the volume after calls is too large, a later refinement can test the read order of loss L1. Tests: the loss tests of P6. |
| R2 | Node table content grows as `m²/2` on join chains. | `chain_table` | `contentSize` counter and `maxTableContent` cap. Log the statistics. |
| R3 | Memo misses at loop tests | `test_miss` | Same order as a sorted merge. Count misses in L4. |
| R4 | The passive call keeps heap paths after calls, so CS4/CS5 copy more facts. IFDS work and memory grow. A part of R0. | CK10, M5. thingsboard and Conductor are already memory bound. | Measure the volume in shadow mode first (R0). Then measure IFDS events and heap on thingsboard and Conductor at 16 GB. If the growth is too large, keep the passive call in the alias state. Then add a direct after-call query for CS4/CS5. This query excludes the cells that a call reached. |
| R5 | Entry aliasing is unsound for both policies. The default `entryUnique = true` also loses the aliases that `false` keeps on a swap. | `skip_unsound`, `write_read_unsound`, `swap_strong` (§3.3). The DSU is also unsound there. | Accepted by the user (D1): A1 is a precondition of the intra-procedural analysis. Keep `entryUnique = false` as a policy value for an A/B check. Caller information on the exact partition is a later option (§3.3). |
| R6 | `retire` scans the state for each loop allocation if no holder index exists. | `retireO_work` (§5.5) | Only loop sites retire. Keep a holder index for `alloc-new` of loop sites. Measure with a counter. |
| R7 | After a walk deeper than K, a variable holds `deep(b)`, and `deep(b)` holds itself in each cell. Without a rule, `findAlias` gives `\|cells\|^D` answers, most of them false aliases. The DSU gives only the accessed chain. | `adefault` (Concept.lean), §6.2 | K ≥ D + 1, and the search never expands a deep self edge (§6.2). Measure the output size in shadow mode on thingsboard and Conductor (R0, §11.3 step 2). |
| R8 | Parts of the engine are not in the O proof: the engine form of the call of design VS (closure over written cells only, the filtered nodes of `Etree` and `Eval` with markers, `Eval` without default contents), the default contents by rule, the on-demand test (stop at the allocation statement, cache, dependency rule, inlined calls), the WTO strategy, exceptional edges, constants, garbage collection. | `mayProgVSO_eq` covers the concept of design VS with the closure over the universe; `csoundBW` needs consistent states before the calls (F12); `mayProgOE_eq`, `mayProgRO_eq`, `mayProgHO_eq`, `mayProgHRO_eq`, `mayProgCNO_eq` and `mayProgBOO_eq` cover the Lean references and the recorded steps, which are not in the engine. | L1 differential test against `NaiveConcept` on the same CFG with the same strategy, with both strong-update tests. Lean follow-ups F3, F4, F5, F8, F12. |
| R9 | The directed engine takes each unresolved call into the strong-update test, also the calls that the DSU exempts (`cantMutateAliasedHeap()`). | §7.6, D10 | Count `calls` and compare alias time in L4. |
| R10 | CS7 precision exposes the unknown-origin gap of main. | §9.1 CS7 | M6 / D9 |
| R11 | CS8 and negated atoms change findings in both directions. | §9.1 CS8 | Review each changed finding in L4 by hand. P12 needs an explanation for each lost finding (§11.2). |
| R12 | Interned constants and boxes: one run-time object for many executions | JVM semantics, not in Lean (F4) | Box and class constants are keyed by type, strings by value. Never unique, never split by recency (§7.5). |
| R13 | States for each statement use memory `O(statements × entries)`. Each method result stays in memory for the whole run (`JIRAnalysisManager.contexts`). | Not measured. The DSU removes heap elements of removed groups; the directed heap needs garbage collection (§7.11). | The four measures of §7.11. `retainedEntries` budget (§11.2). D8 if the budget fails. |
| R14 | Exceptions: catch states and the catch origin are outside the Lean model. | §3.4, §7.10 | Catch edges join the states before and after the thrower (argued, F8). The DSU uses the state after only. |
| R15 | The cost of the call closure. The closure visits each written cell of each covered origin. A call on an object with a large written subtree (`this` of a large method, many statics) costs a large closure. With the forward sets, each call runs it. With the on-demand test, only a store that can be strong runs it, once for each upstream call and state version (cached). | §7.6 (cost of one call); `callVSO_work`, `uniqueBO_up` | No heap write at a call (`callVSO_heap_frame`), so the values do not grow with the number of calls. Count `callClosureSize`, `etreeSize`, `evalSize`, `callFallbacks`, `onDemandSearches`, `cachedClosures` and `upstreamCallsPerStore` (§11.2). The budget `maxCallClosure` bounds the closure; over it, the sound fallback applies. The shadow runs report these counters (§11.3 step 3). D14 chooses the variant. |
| R16 | The call rule is proved sound only under A2-narrow (`csoundVS`, `csoundVS_W`) and A4 (`siteless_unsound`). With generous reach or with one object in two cells it misses aliases (proved for CN: `generous_reach_breaks_CN`, `generous_havoc_breaks_CN`; design VS answers as CN, argued). Completeness of recency and of calls is not proved (§4.7, F6). | §3.1, §4.11, §4.12 | Both shapes are out of scope (§3.4), and the user accepted the scope with design VS (D2). Under A1, a callee cannot reach an object outside the narrow closure (argued). A4 holds for verified bytecode (F13). The taint analysis covers resolved callees by their summaries. The engine has no A2-wide mode; the Lean site havoc rule (`csoundE`, `csoundR`) documents the cost of the wider scope. |
| R17 | Null-valued aliases add answers: a read of an unwritten field of a new object aliases the field path, and a copy of a null aliases its source (§6.1). A part of R0. | `added_answers` (4 of 9 queries added on two small families), `added_answers_real`, `added_answers_not_objects` | The user requires the read rule (D2, 2026-11-03). Measure `nullOnlyPaths` in the shadow runs (§11.2). The DSU of main also relates a read with its cell, so the change against main is expected to be small (argued). |
| R18 | The static gap (A5). The engine ignores static writes. So `C.f = v; t = C.f` gives no `t ~ v` (U3 stays), and a value that the method stores only into a static field is not reached by later calls. In `C.f = a; e = a.h; d = e.g; m(); n = a.h; n.g = z` the store `n.g = z` stays strong, and `e.g ~ d` is false, also if `m` follows `C.f` to `a` and writes a new object into `a.h`. The alias answers miss these aliases, and the taint analysis does not get them from the alias analysis. | `static_unsound` (§2.3); `gapA`, `gapB` (VSS false, an execution without A5 has the alias); design VSS is sound under A5 (`csoundVSS`, §3.1) | Accepted by the user (D15, 2026-11-05): the taint analysis tracks static fields globally, on its own. Main has the same behaviour (probe row 28), so the A/B difference has no static part. Recorded option, not applied: a static write `C.f = v` copies `v` into a ghost variable, and each later call gets the ghost variables as extra arguments (`stripStaticG`). It changes no alias, closes the second gap (`gapB`) and keeps the answers of example 6.8 of the compact specification (`option_answers`). It is not proved sound (§3.1). |

Volume table (R0). Main has two defects that limit the volume by accident: the order-dependent conversion cache cuts heap chains (§8.5), and the call drop removes heap aliases (U2). The user reports that a fix of either one explodes the analysis. The directed engine has both changes that increase the volume: no drop at calls (D2, decided) and a deterministic, depth-aware query that reports full chains up to D. It also has changes that decrease the volume: non-transitive answers (`alias(x) = {a}`, not `{a, y}`), and dominance where the DSU is sound (there, the directed answers are a subset of the DSU answers). The subset claim is proved only for the heap-free fragment (`dsu_dominates_heapFree`, with `dsu_sound_heapFree`, DSU/HeapFree.lean, §2.5). With loads and stores it is not proved (F6). So the net volume is not known. It is the first gate (§11.2).

| Change | Effect on volume | Evidence |
|---|---|---|
| Non-transitive answers: `alias(x) = {a}`, not `{a, y}` (PL1-PL4, PL7) | − | proved: `alias_not_transitive`, `join_precision_loss`, `field_precision_loss`; measured on main: probe rows 1-4, 8, 10, 37, 41, 42 (the expected directed flips, §9.3) |
| Directed pass-through models (PL6) | − | measured on main: probe row 11; argued for the directed answer (§7.8) |
| Dominance where the DSU is sound: the directed answer is a subset of the DSU answer | − | proved only for the heap-free fragment (`dsu_dominates_heapFree`); open with loads and stores (F6); known failures in §2.5 |
| No alias drop at unresolved calls (D2) | + | proved: `b_unsound`, `b_local_unsound`, `call_w_xf`; measured on main: probe rows 21, 22, 24, 25, 27; reported by the user: the fix of the drop on main explodes the analysis |
| No cache truncation: full chains up to D (§8.5, §7.11) | + | argued; reported by the user: the cache fix on main explodes the analysis; P0c counts the cut (`cutConversions`, `cutCacheHits`) |
| Other soundness fixes: U1, U4 restore lost aliases | + | proved: `a1_unsound` .. `a4_unsound`, `repr_unsound`; measured on main: probe rows 13-16, 35, 36. Rows 35 and 36 also lose a false `x.next^k` chain (−). |
| Static writes ignored, as on main (A5, D15): U3 stays | none | `static_unsound`; probe row 28 keeps its answer |
| Strong updates on entry roots (D1): a strong store removes the old content of the cell | − | proved: `root_concept_more_precise`, `swap_strong`; measured on main: probe row 30 |
| Recency: strong stores on `alloc-new(s)` of loop sites | − | proved: `loop_bf_x_fixed`, `loop_bf_x_exact`; probe rows 17-20 get smaller sets (§9.3, argued from the oracle) |
| The call rule VS against site havoc, per-cell havoc and CN | − against site havoc: with site havoc, each value loaded after a call aliases each outer path (about `\|vars\|·\|cells\|^D` paths, §4.9). Against CN: − for L2 and L3 (exact in design VS), + for loss L4 (§4.12). Against per-cell havoc: + for the losses L1 and L4, − for the narrow reach | proved: `havoc_spread`, `spread_goneVS`, `spread_ab_noneV`; `losses_VS`, `losses_exactV`, `losses_CN`, `losses_HR`; `bo_cn_incomparable`; `gain_answersVS`. Not measured in the engine: the comparison is from the Lean examples only (§4.11, §4.12). |
| Value semantics of reads: null-valued aliases (§6.1) | + | proved: `added_answers` (design VS answers 4 of 9 queries true on two small families; BO none), `added_answers_real`, `added_answers_not_objects`; argued: the DSU of main also relates a read with its cell; measured in the shadow runs by `nullOnlyPaths` (R17) |
| Interned constants: one origin for each string value, box type and class literal (§7.5) | + | argued: two locals with one literal now alias (§9.1); not in Lean (F4) |
| Deep self edges are never expanded (§6.2) | − | argued (F7) |
| Query depth D | the main knob: the output can grow as `\|cells\|^D` on cyclic heaps | proved: `searchCost_le` bounds the query cost by the output; `qfam_sep`; D11 (b) |

### 11.2 Performance, precision and memory gates

Baseline: main as it is (D13, decided by the user). The DSU of main keeps its defects (U1-U4, the cache cut of §8.5); no DSU fix goes into the baseline. One jar that has all three modes runs both sides of each A/B (mode `DSU` against mode `SHADOW` or `DIRECTED`), so the alias timer and the counters are the same on both sides.

Volume gate (R0). It is the first gate. It has two parts: V1 in shadow mode (P9a), before any directed answer feeds the taint analysis, and V2 in directed mode (P11). This document sets no thresholds for it. The user: "measure after the implementation, then decide". So the user sets the thresholds after the shadow-mode measurement. This document defines only the metrics and the comparisons. Projects in this order: thingsboard first (the explosion of main reproduces there fast), then Conductor, then tms.

| Part | Metric | Comparison | Source |
|---|---|---|---|
| V1 (shadow, P9a) | For each query: answer count, accessor sum, maximum chain length, for each backend; the query kind (`BEFORE`, `AFTER`, `ARRAY_ELEMENT`, `HEAP`) | Directed against DSU for each query. Each query where the directed answer is not a subset of the DSU answer is logged and classified: U1, U2, U4, the cache cut (§8.5: the DSU query had a `cutCacheHits` increment), an interned constant (§7.5), or a new bug. Unexplained queries: zero (a correctness rule, not a volume threshold). Each query where the DSU answer is not a subset of the directed answer is counted (precision gain). | `AliasShadowStats` |
| V1 | For each method and each project: number of queries, total paths, total accessors, p50 / p99 / max of the answer size and of the chain length, for each query kind; `truncatedQueries` (D11 (c)); `cutConversions` and `cutCacheHits` of the DSU | Directed total against DSU total, for each project | `AliasShadowStats`, `AliasVolumeStats` |
| V1 | Precision: mean and p99 of `\|alias(x)\|` | Directed against DSU | `AliasShadowStats` |
| V1 | Null-valued aliases: `nullOnlyPaths` for each query kind, method and project, and its share of the total paths (R17) | Directed share; the DSU has no such counter | `AliasVolumeStats` |
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
| Call cost | report p50 / p99 / max of `callClosureSize`, `etreeSize`, `evalSize` for each method, and the count of `callFallbacks`; on demand also `onDemandSearches`, `cachedClosures` and `upstreamCallsPerStore` (input for D14) | `DirectedAliasStats` |

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
6. A2-narrow and A4 are the scope of the call rule VS (D2, decided by the user 2026-11-03; §3.1, §4.12, R16).

`DirectedAliasStats` is a small counter object for each analysis, logged at DEBUG: `stmtEvals`, `headIterations`, `nodeCount`, `contentSize`, `memoHits`, `memoMisses`, `retires`, `calls`, `callClosureSize`, `etreeSize`, `evalSize`, `callFallbacks`, `onDemandSearches`, `cachedClosures`, `upstreamCallsPerStore`, `nullSites`, `retainedEntries`, `exactMethods`, `queryCount`, `queryNodes`, `aliasTimeMs`, `fixpointTimeMs`, `symByDepth`, `deepOrigins`, `allocChildOrigins`. The call counters are the sum, the p99 and the maximum over the calls of the method: `callClosureSize` (origins in `R`), `etreeSize` and `evalSize` (members of the two reserved nodes at the method exit; forward-set variant), `callFallbacks` (closures over `maxCallClosure`). The on-demand counters: `onDemandSearches` (stores that ran the test), `cachedClosures` (closures computed, one for each cache miss), `upstreamCallsPerStore` (upstream calls that a test visited, after the stop at the allocation). `nullSites` counts the null sites of the method. The DSU path of P0c has `dsuStmtEvals`, `dsuHeadIterations`, `dsuTimeMs`, `dsuStateEntries`. The volume counters, `nullOnlyPaths` included, are in `AliasVolumeStats` (§7.3).

### 11.3 Measurement plan

The sources of the baseline numbers: tms timing measured 2026-08-27 on this development machine; dataflowbench 49/58 and 50/58 reproduced 2026-09-01 with release `analyzer/2026.08.27.17eb0fe`; Conductor at 16 GB measured 2026-08-20.

Steps 1-3 are the volume phase (R0). They run before any directed answer feeds the taint analysis. The project order is thingsboard, Conductor, tms: the explosion of main reproduces fast on thingsboard (a fast out-of-memory error from the number of taint facts).

1. Volume baseline (P0c). Build the jar of main with the P0c counters (no answer change): `cd core && ./gradlew :projectAnalyzerJar --offline -x :opentaint-ir:go:buildGoServer`. Build the CLI one time: `cd cli && GOPROXY=off go build -o <out>/opentaint-cli .`. Run thingsboard, then Conductor, with the arguments of step 5, then tms with the command of step 6. Record the `AliasVolumeStats` totals of each project, `cutConversions`, `cutCacheHits`, the IFDS events (`Progress: N/M`), the peak heap and the memory guard events. Check that the findings equal the findings of main.
2. Shadow runs (P9a). The same projects in the same order, with `--experimental-alias-analysis-mode=shadow`. Check that the findings equal the `DSU` findings. Collect `AliasShadowStats`: the per-query comparison and the per-project totals of V1 (§11.2). Two engines run, so time and memory of this run are not budgets. If a shadow run does not fit in 16 GB, record it, and run again with more memory.
3. Shadow report. For each project: directed total against DSU total; the distributions of the answer size and the chain length for each query kind; the not-subset queries with their class (U1, U2, U4, cache cut, interned constant, new; U3 gives no difference, because both engines ignore static writes, A5). Optional diagnostic runs in shadow mode isolate the volume of single changes: `diagnosticCallDrop = true` (the volume of D2, D11 (e)), a smaller `maxAccessors` (D11 (b)), a `maxQueryPaths` budget (D11 (c)). Report the call counters and the on-demand counters of `DirectedAliasStats` (§11.2; input for R15 and D14), and the share of `nullOnlyPaths` (R17). Then the user sets the thresholds of V1 and V2 and decides D11 (§11.2, §12).
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
| F1 | Per-cell havoc under A2-strict: concrete strict havoc, per-cell havoc origins, soundness, O equivalence, recency with per-cell havoc, and the shared key `alloc-old(s)`. Then CN under A2-narrow, BO, and design VS with values with identity. | proved: `csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`, `keyOfR_alphaRS` (§4.9); `csoundCN`, `mayProgCNO_eq`, `csoundCNO` (§4.11); `csoundBO`, `mayProgBOO_eq`, `csoundVS`, `csoundVS_W`, `mayProgVSO_eq`, `csoundVSO`, `csoundBW`, `mayProgBW_eq` (§4.12, §5.5). Open part: the more precise rule for havoc-derived holders of per-cell havoc (§4.9). |
| F2 | O with recency: retire on node ids, equivalence with the recency concept, cost bound | proved: `retireO_rel`, `storeRO_rel`, `ostepR_rel`, `analyzeRO_rel`, `mayProgRO_eq` (both policies), `retireO_work` (Opt/Recency.lean) |
| F3 | The engine form of the call of design VS (closure over written cells only; the filtered nodes of `Etree` and `Eval` with the markers `REACHED_STATICS` and `REACHED_ALL`; `Eval` without the default contents, which `eval_default_free` justifies; coverage of the allocation children through the base index) gives the answers of `callVSO`. | open |
| F4 | Multi-dimensional array defaults; interned constants (boxes, class literals, strings) | open |
| F5 | Prove that WTO iteration equals the structured `loopIter` for reducible CFGs. | open |
| F6 | Completeness for calls under A2-narrow for design VS (the two losses L1 and L4 bound the scope); completeness of the value semantics (the null-valued answers; `added_answers_real` on examples only); "recency is at least as precise as C"; "the combination is at least as precise as each refinement alone" (the form "CN is at least as precise as per-cell havoc" is false: `precision_order_fails`; BO and CN are incomparable: `bo_cn_incomparable`); the finer key that removes the `cost_answers` alias; dominance over the DSU with loads and stores | open |
| F7 | The deep-self-edge search rule with K ≥ D + 1: it removes no path of length at most D from a root. | open |
| F8 | Exceptional flow: the catch-edge state and the catch origin are sound. | open |
| F9 | Small theorems: "recency equals C when each site is once" (`mayProgR eu = mayProgE eu`), which carries the completeness theorems to recency; a theorem `osoundE` for O without recency (for O with recency and per-cell havoc, `csoundHRO` exists). | open |
| F10 | A cost bound for the O call: design VS (`callVSO_work`, `callVSO_work_ge`, `callVSO_heap_frame`), BO (`callWithO_work`), CN (`havocWithO_work`, `havocWithO_work_ge`), per-cell havoc (`havocHRO_work`), and the separation `separationVS`. | proved |
| F11 | Soundness of the narrow per-cell reference `mayProgHRN` (Reference.lean) under A2-narrow. Model only, not needed by the engine: the engine has no per-cell mode (D2). It stays a follow-up of the formal reference of the earlier steps (§4.11). | open (model only) |
| F12 | The on-demand test in the engine: the final states of the worklist fixpoint, with the dependency rule of §7.6, form a consistent oracle (`ConsBW`) for `csoundBW`; the stop at the allocation statement is sound in loops; the contribution of an inlined call statement (§7.7). | argued (§4.12, §7.6) |
| F13 | Definite assignment (A4) in the JIR form of the bytecode: each JIR local that a statement reads was assigned on each path, also after the JIR transformations of the bytecode. | argued (the JVM verifier) |
| F14 | The practical cost of design VS for each method (calls, stores, reads, allocations, null sites; §4.12) as a theorem over the O cost model. | argued |
| F15 | The static rule of the engine (A5, D15): a static write does not change the state, and a static read gives `{⟨C.f⟩}`. A5 is in the concrete semantics (`ExecA5`, `execA5_iff`); design VSS is sound under A5 (`csoundVSS`, `csoundVSSO`, `mayProgVSSO_eq`); a static read gives exactly `{⟨C.f⟩}` (`static_read`, `static_read_end`, `SCInv_analyze`); the two gaps against the semantics without A5 are proved (`gapA`, `gapB`). Remaining note: `static_cells_default` needs `noTopB` (no loop ran out of fuel). `noTopB` is true for loop-free programs (`noTopB_of_loopFree`); for programs with loops it needs a fuel-sufficiency theorem, which the package does not have. Soundness does not need `noTopB`. The recorded option (`stripStaticG`) is not proved sound. | proved (§3.1) |

### 11.5 Rollback

The mode switch is the rollback. Mode `SHADOW` gives the DSU answers to the consumers, so it needs no rollback. Set `aliasAnalysisMode = DSU` (CLI `--experimental-alias-analysis-mode=dsu`). The DSU backend stays in the code until P13. After P12 the rollback is a one-line default change.

---

## 12. Decisions for the user

The user decided D1, D2, D5, D6, D7, D12 and D13 on 2026-10-29, decided D2 again (the call rule VS) on 2026-11-03, and decided D15 (static fields) on 2026-11-05. D3, D4, D8, D9, D10, D11 and D14 are open: the user decides after the spec revisit. For an open decision, the row gives the options, a recommendation and the evidence.

| Id | Status | Decision | Options | Recommendation or decision | Evidence |
|---|---|---|---|---|---|
| D1 | Decided by the user | Strong updates on entry roots (`entryUnique`) | (a) `false`: weak on symbolic origins; only allocation origins can get strong updates. (b) `true`: strong store on `sym(root, q)` without `elem`, and on unique call results. | (b) `true` is the default. The user: "We may lose some aliases, but it is acceptable. We remain intra-proc." A1 is an accepted precondition of the intra-procedural analysis. (a) stays a policy value for an A/B check. | Under entry aliasing both policies are unsound (`skip_unsound`, `write_read_unsound`). (b) also loses aliases that (a) keeps: `swap_alias` with `swap_strong` false and `swap_weak` true. These theorems document the accepted loss (§3.3). No theorem orders the two policies. The completeness theorems use (b), so they cover the default (§4.7). Gain of (b): probe row 30 flips, row 29 keeps its answer, and `root_concept_more_precise`. Cost of (b): 2 of the 4 assertions of `test swap fields` change in directed mode (§9.2, P9). |
| D2 | Decided by the user (2026-10-29; the call rule decided again 2026-11-03) | Call model | (a) the heap-alias removal of main. (b) weak havoc with site havoc origins (A2-wide). (c) weak havoc with per-cell havoc origins (A2-strict). (d) weak havoc with no origin for an unknown object ("dead end"). (e) CN: weak havoc with cell names, narrow reach and the exposed set (A2-narrow). (f) a flag "probably outer" on variables. (g) BO: no alias change at a call; the sets `Etree` and `Eval` of origins block later strong updates; the cell name goes into each reached empty cell. (h) design VS: values with identity, so a read aliases the cell, nulls included; each cell is non-empty; the call writes no heap entry and only blocks later strong updates (A2-narrow with callee nulls, A4). | No alias drop in the may analysis: (a) is out. The drop of main (`invalidateOuterHeapAliases`) is a must-side rule: a callee can overwrite a cell, so a must relation through it ends. A future must analysis keeps it (§8.4). Main has no must analysis enabled, so the directed analysis keeps the old content of each cell. Call rule, decided by the user (2026-11-03): (h) design VS, with its two precision losses L1 and L4. The engine has one call rule. The `SHARED` mode ((b)) and the `PER_CELL` mode ((c) with the closure of CN) were dropped by the user, 2026-10-29 (§7.6). (b) and (c) stay in the Lean model as formal references, and (e) and (g) as recorded refinement steps. History (CEGAR steps 2-7, §1.8): the user first chose (c) and considered the call-result origin `⟨s⟩` as the havoc origin (rejected: `⟨s⟩` makes every post-call load alias every other one and the call result, and it removes strong updates on call results). Then the user found (c) too expensive: it adds a per-cell origin to each cell of each reachable origin at each call, and each symbolic object is reachable. The user rejected a lazy havoc log (it complicates state identity and the join). (d) is unsound. The user accepted (e) on 2026-10-29 (step 4, §4.11). Then, in order (§4.12): (1) the user asked for the cheapest call handling that does not touch the alias graph, is sound for the call policy and keeps as many strong updates as possible: "the only thing we need to do after the unresolved call — prohibit some strong updates"; (2) (f) is unsound: the name of a callee object is shared, so the flag must be on origins (traces A and C, step 5); (3) (g) was modeled: its first form with a read rule for empty cells is unsound, and the proved fix writes names into the reached empty cells (step 6); (4) the user's correction (2026-11-03): `x = new X(); a = x.f` must give `findAlias(a) = {x.f}` regardless of calls; this is the field-read rule, not call handling, and it gives (h) (step 7); (5) (h) is the design; CN and BO stay only as recorded steps, and per-cell havoc stays the formal reference of the earlier steps. | (a) is unsound for may-alias (U2: probe rows 21, 24, 27; `b_unsound`, `b_local_unsound`, `call_w_xf`). (b) is sound under A2-wide (`csoundE`, `csoundR`, `mayProgOE_eq`, `mayProgRO_eq`), but a value loaded after a call may-aliases each outer path (`havoc_spread`, §4.9). (c) is sound under A2-strict (`csoundH`, `csoundHR`, `mayProgHO_eq`, `mayProgHRO_eq`, `csoundHRO`) and removes the spread (`strict_answers`, `strict_ab_none`), but its cost grows with the calls (§4.11). (d) misses a real alias: `n = new N(); m(n); a = n.f; if (*) { b = a; d = a } else { b = y; d = z }`, `b ~ d` (`dead_realN`). (e) is sound under A2-narrow (`csoundCN`, `mayProgCNO_eq`), with three losses (`losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN`), and it writes at least m·n heap keys on the family of `separationVS`. (f) misses the real alias of trace A (`strong_after_call_realN`). (g) in its first form misses real aliases (`joinBug_real`, `loopBug_real`, `symBug_real`); the fixed form is sound (`csoundBO`, `mayProgBOO_eq`) and incomparable with (e) (`bo_cn_incomparable`). (h) is sound under A2-narrow with A4, for both policies, with recency, each K and each list of static roots (`csoundVS`), also with callee nulls (`csoundVS_W`); O equals C (`mayProgVSO_eq`, `csoundVSO`). A4 is necessary (`siteless_unsound`). The call writes no heap entry (`callVSO_heap_frame`, `separationVS`). It answers the user's rule (`user_answers`, `user_real`, `user_call_real`), keeps the HavocNeed cases (`strong_answersVS`, `empty_answersVS`), removes the spread (`spread_goneVS`) and keeps strong updates on objects that a call does not reach (`gain_answersVS`, `gain_noneV`). Its two losses are real losses (`losses_VS`, `losses_noneV`); L2 and L3 of CN are exact (`losses_exactV`). It adds null-valued answers (`added_answers`, R17). Behaviour change for CS4/CS5 (§9.1) and for `test external call invalidates heap aliases` (§9.2). Volume: no drop increases the alias answer volume (R0); the diagnostic flag of D11 (e) measures this part (§11.2). The losses are known from the Lean examples only (§4.12). |
| D3 | Open: the user decides after the spec revisit | Recency | (a) on. (b) off. | (a) | §1.8 (CEGAR step 1). Cost: R6. |
| D4 | Open: the user decides after the spec revisit | Origin depth K and query depth D | K: 3, 7 or 9. D: 6 accessors, or less. | D = 6 (unchanged, `HEAP_CHAIN_LIMIT = 5`). K = 7 (K ≥ D + 1). | With K ≥ D + 1, a reported path from a root variable is its own origin, with no deep origin in the reported range (CX1 shows the merge). A path from a loaded variable can reach a deep origin in the reported range; the search rule of §6.2 then applies. Cost of K: origins and node sizes, up to `Σ_{i≤K} w^i` symbolic origins for each base on a walk over `w` fields (§6.2). Measure `nodeCount` and `contentSize` for K = 3 and K = 7 in L4 before the decision. Contract item CK3 needs an unchanged query depth D. D is also the main knob of the alias answer volume (R0, D11 (b)). |
| D5 | Decided by the user | Must-alias | (a) derive from O (§8.4). (b) take the branch `origin/DanielELog/must_alias` (second DSU with a meet join). (c) none now. | (c): must-alias is postponed. Later work can derive it from O (a). It must keep the alias drop at unresolved calls (D2). | Main has no must analysis enabled. A derivation from O needs no second fixpoint, and `must ⊆ may` holds. The branch is on the old API, and its unfinished part can lose may-aliases (not verified). §8.4. |
| D6 | Decided by the user | Shared base class with Go | (a) extract an interface for the two queries. (b) copy: the JVM facade and the directed backend do not extend `LocalAliasAnalysis`; copy the helpers into the JVM module. | (b). The shared alias code and Go code do not change. | §8.3. The copies are the generic receiver helpers of `AliasUtil.kt` (M3, §7.4). Risk: the two copies of the helper loops can become different. |
| D7 | Decided by the user | Rollout | (a) mode switch `aliasAnalysisMode = DSU \| SHADOW \| DIRECTED`, default `DSU`, opt-in CLI; `SHADOW` for the volume gate (P9a); default `DIRECTED` after the conditions of §11.2 (P12); remove the DSU after one release (P13). (b) switch in one step. | (a): add the mode switch, default `DSU`. The value `SHADOW` follows the user input of 2026-10-29 on the volume (R0, D13). | Rollback by the mode switch (§11.5). L4 noise needs interleaved runs. |
| D8 | Open: the user decides after the spec revisit | State container | (a) fastutil copy-on-write. (b) `kotlinx.collections.immutable` persistent maps. | (a). Measure (b) only if the memory gate fails. | §7.11: no boxing, `joinO_work` per key. Memory is to be measured (§11.2). |
| D9 | Open: the user decides after the spec revisit | Unknown-origin signal for CS7 (M6) | (a) add `defaultConstraint` when `mayHoldUnknownObject` (both modes). (b) directed mode only. (c) no change. | (b) first, then (a) after a separate tms A/B | It closes the unsoundness of main that the directed precision makes visible (§9.1 CS7). (a) changes DSU results too, so measure it alone. |
| D10 | Open: the user decides after the spec revisit | The `cantMutateAliasedHeap()` exemption | (a) no exemption in directed mode: each unresolved call takes part in the strong-update test. (b) keep the exemption for static calls with only primitive arguments; never for the receiver of `<init>`. | (a) | The exemption is outside the Lean model: such a callee can write statics. In design VS the call only blocks strong updates, so the exemption gains only strong updates below the static roots and through the cells of the receiver. Two loads of one field of a new object alias with or without the exemption (`empty_answersVS`, §7.6). Cost of (a): more calls in the strong-update test (R9). |
| D11 | Open: the user decides after the spec revisit and the shadow-mode measurement | Volume control (R0) | (a) No control: rely on the precision gains (non-transitive answers, D1, recency). Sound; keeps CK3. (b) Query depth D as the knob (`maxAccessors`, D4). Each answer stays complete up to the chosen D. A D smaller than 6 changes CK3: paths longer than D are not reported, which is unsound against main. (c) A deterministic per-query path budget (`maxQueryPaths`): shortest paths first, then the fixed comparator, and a `truncated` counter (§7.12 step 7). Unsound like the cut of main, but deterministic and measured; the cut of main depends on query order (§8.5). Changes CK3. (d) Simple paths only: a reported path never visits an origin two times. It cuts cyclic unrolling such as `x.next.next...`. It is a deviation from the answer set of the concept (`findAlias_iff` then gives only inclusion), so it needs a consumer-level argument or a measurement. Unsound in general: on a list of one summary origin, `x.next.next` can be a real alias. (e) The call drop of main as an A/B-only diagnostic flag in the may analysis (`diagnosticCallDrop`). It isolates the volume effect of D2. Not a default; D2 stands. Unsound (U2). | (b) and (c) are ready in the engine (P4); the measurement chooses between them and their values (§11.3 step 3). (e) for diagnosis only. (a) if the shadow volume gate holds without control. (d) only with a consumer-level argument. | R0 and the volume table (§11.1). Thresholds: the user sets them after the shadow-mode measurement (§11.2). Query cost bound: `searchCost_le`; `\|cells\|^D` output on cyclic heaps (§6.2). |
| D12 | Decided by the user | Inlining | (a) Keep inlining depth 1 in production. (b) No inlining in the directed engine. | (a). The user: "Inlining — yes, we keep inlining." | §3.4, §7.7, CK12. Production uses `experimentalAAInterProcCallDepth = 1`. |
| D13 | Decided by the user | The DSU on main | (a) Fix the DSU on main: the cache depth fix (commit `deff91ca0`, §8.5) and the removal of the call drop. (b) Keep the DSU of main as it is; document its defects. | (b). The user: "The issues are known, but we don't land the fix. The problem is the analyzer itself: after any of the fixes the AA starts producing way more alias chains, resulting in analysis explosion." So the cache-fix step is dropped, the A/B baseline is main as it is, and U1-U4, LT1 and the cache cut stay documented (§2, §8.5), not fixed. | User report: the explosion reproduces fast on thingsboard (taint facts, out-of-memory error). R0. P0c counts the volume of main and the cut of the cache, with no answer change. |
| D14 | Open: the user decides after the spec revisit and the shadow-mode measurement | The implementation of the strong-update test after calls | (a) Forward sets: the two reserved keys `ETREE_VAR` and `EVAL_VAR` in each state; each call runs its closure and two unions. (b) On demand: no state for calls; a store that can be strong computes the closures of its upstream calls on the stored states before them, with a cache keyed by (call, state version), a stop at the allocation statement of the target, and a dependency rule (§7.6). | (b), with the cache. The user observes that strong updates matter mainly for reassigned fields, and these are rare. So few stores need the test, and (b) runs the closure only for them; (a) runs it at each call and adds two keys to each state and join. Keep (a) as a policy value (`strongUpdateTest = FORWARD_SETS`) for the differential test (§10.1) and an A/B check. | Both are sound: (a) by `csoundVS`, (b) by `csoundBW` for consistent states before the calls (argued for the engine, F12). They give the same answers on loop-free code with different sites (`mayProgBW_eq`); with a repeated site (b) is weaker (`bw_needs_distinct_sites`), and the stop at the allocation removes this case (§7.6). With loops (b) can block more strong updates. Cost: (a) `callVSO_work` at each call; (b) no work at the call (`astepBW_call`) and one cached test for each upstream call at a store (`uniqueBO_up`). The counters `onDemandSearches`, `cachedClosures`, `upstreamCallsPerStore` measure (b) (§11.2). |
| D15 | Decided by the user (2026-11-05) | Static fields | (a) A static write is an ordinary store into a cell of the static root (design VS of the Lean model; it fixes U3). (b) Ignore static writes: a static read always gives `{⟨C.f⟩}` (design VSS of the Lean model). (c) As (b), and a static write `C.f = v` also copies `v` into a ghost variable that each later call gets as an extra argument, so `pts(v)` is in the start set of each later call, with no change of an alias (`stripStaticG`). | (b). The user: "ignore static writes. Always return reference to a static field on static field read (as if it was not initialized)." This is assumption A5 (§3.1). The taint analysis tracks static fields on its own. `WriteStatic` does not change the state, as on main, and a static root never has a heap entry (§7.5). (c) is a recorded option, not applied: it closes the second consequence of A5 (a value stored only into a static field is not reached by later calls). A form of (c) that adds `pts(v)` to `Etree` and `Eval` only at the static write is probably weaker: it misses a write into a cell of `v` between the static write and the call (argued). | Design VSS is sound under A5 (`csoundVSS`, `execA5_iff`, `csoundVSSO`), and a static read gives exactly `{⟨C.f⟩}` (`static_read`, `static_cells_default`). U3 stays: `static_unsound`, `gapA`, probe row 28 keeps its answer (§2.3, §9.3). The user accepted both consequences of A5, also the second gap: in `C.f = a; e = a.h; d = e.g; m(); n = a.h; n.g = z` the store `n.g = z` stays strong, and `e.g ~ d` is false, but an execution without A5 has the alias (`gapB`, §3.1, R18). Option (c) closes `gapB` and keeps the answers of example 6.8 of the compact specification (`option_answers`); it is not proved sound. |

---

## Appendix A. Lean file index

Build and audit:

```
cd formal/directed-alias && ./check.sh
```

`check.sh` builds the package with `lake build` (Lean `v4.35.0`, no Mathlib). It fails on `sorry`, `admit`, `native_decide` or an `axiom` declaration. It regenerates `AxiomAudit.lean` and fails if a theorem depends on `Classical.choice`, `sorryAx` or `ofReduceBool`. Output for the full package: 1615 public theorems; 125 depend on no axiom, 593 on `propext`, 896 on `propext` and `Quot.sound`, 1 on `Quot.sound`; about 35.0k lines of Lean in about 93 build jobs. The call rules CN, BO and VS added 157, 217 and 273 of these theorems, and the static rule (design VSS) added 55. Concrete checks use `decide`, or `decide +kernel` for large terms. The kernel checks both. No check uses `native_decide`.

Constructive claims. `propext` and `Quot.sound` are in the Lean core. Without `Classical.choice` they do not give the excluded middle, and they do not stop `decide` from reducing. So each proof is constructive. Each example witness is an explicit choice list. The executor `runFrom` runs it, and `decide` checks the result (`runAliasB_sound`). Each completeness theorem also has a computable witness search (`crossWitness`, `witness_core`, `witness_store`, Sound/Witness/Search.lean, §4.7). In the two scopes, a true answer yields a witness that a reader can run with `#eval`.

The body gives each theorem with its claim. This index gives the files. "Other lemmas" are the supporting theorems that the body does not cite.

| File | Content | Cited in | Other lemmas |
|---|---|---|---|
| `Syntax.lean` | The IR: statements, programs, sites | §2.1, §4 | — |
| `ListSet.lean` | Lists as sets, `single?` | §4.3 | — |
| `Concrete.lean` | Concrete semantics (A1-A3, A2-wide), the executor `runFrom`. A2-strict is in `Sound/Havoc/Concept.lean`, A2-narrow in `Sound/CellNamed/Concept.lean`, the values with identity and A4 in `Sound/ValueSem/Concept.lean`. | §3.1, §4.7 | `run_sound`, `runAliasB_sound` |
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
| `Sound/BlockOnly/Concept.lean` | Design BO (a recorded step): the context `CtxB` with the reserved variable of `Eval`, the test `uniqueBO`, the store `storeBO`, the call `callWith`, `callBO`, `astepBO`, `ctxBO`, `mayProgBO` | §4.2, §4.12 | — |
| `Sound/BlockOnly/Unsound.lean` | `BO0`, the first form of BO with a read rule for empty cells, is unsound: the JOIN, LOOP and SYMBOLIC counterexamples with witnesses; the fixed answers | §1.8, §4.12 | `bo0_answers`, `symBug_answers`, `joinBug_real`, `loopBug_real`, `symBug_real`, `bo0_unsound`, `fixed_answers` |
| `Sound/BlockOnly/Ghost.lean` | The ghost naming by content: a callee object has the first origin of its abstract cell as its name (`alphaBO`, `chainB`, `stepB`), and the recency rename of names | §4.12 | `renB_bump`, `renameO_childCN'` |
| `Sound/BlockOnly/Inv.lean` | The invariant `InvBO` (`InvG`, `InvXB`, `CntOKB`), `BlockedAll`, the uniqueness lemma | §4.12 | `unique_objBO` |
| `Sound/BlockOnly/Call.lean` | Soundness of the BO call: naming, blocked names, unreachable cells | §4.12 | `InvG.callW`, `callWith_heap_ne`, `reach_coverB`, `cov_chainB`, `blocked_stepB`, `junk_keptB`, `ghostsAfter` |
| `Sound/BlockOnly/Soundness.lean` | Soundness of BO: `csoundBO`; default contents in `Eval` cost no strong update | §4.5, §4.12 | `callBO_sound`, `eval_default_free` |
| `Sound/BlockOnly/Examples.lean` | The BO examples: HavocNeed, the spread, the dead-end case, the gain, trace C, the `Eval` case and its necessity, the losses, loss L4 | §1.8, §4.12 | `need_answersBO`, `spread_goneBO`, `dead_answerBO`, `gain_answersBO`, `traceC_answerBO`, `traceC_realN`, `eval_answerBO`, `eval_realN`, `eval_needed`, `losses_BO`, `losses_exactBO`, `loss4_BO`, `loss4_noneN` |
| `Sound/BlockOnly/Precision.lean` | BO against CN on all examples; the two rules are incomparable | §4.12 | `precision_tableN`, `precision_tableNeed`, `bo_cn_incomparable` |
| `Sound/ValueSem/Concept.lean` | Design VS: null sites (`Prog.nulls`), `nullO`, `nullKids`, `adefaultV`, `ainitV`, `retireV`, `astepVS`, `ctxVS`, `mayProgVS`; the instrumented semantics with values with identity and A4 (`VVal`, `NTag`, `VState`, `SStepV`, `ExecV`, `CAliasV`) | §3.1, §4.12 | `aliasInV_of_aliasIn`, `CAliasV.toN_obj` |
| `Sound/ValueSem/Inv.lean` | The invariant `InvVS` (the BO invariant and the null facts `InvN`), no empty cell (`NE`), the passive call equals the BO call under `NE`, the query lemma | §4.12 | `callBO_eq`, `callVS_heap`, `InvN.call`, `InvVS.evalV_nul`, `InvVS.may_of_alias` |
| `Sound/ValueSem/Soundness.lean` | Soundness of design VS: `csoundVS`, `no_alias_of_mayProgVS` | §4.5, §4.12 | `step_soundVS`, `analyze_soundVS`, `inv_initVS`, `ctxVS_ok`, `ctxVS_frame`, `supp_analyzeVS` |
| `Sound/ValueSem/Run.lean` | A computable executor for value witnesses (`runAliasV`); a value alias without nulls is an object alias | §4.12 | `runAliasV_sound`, `CAliasV.toN_of_nullFree`, `not_CAliasV_of_nullFree` |
| `Sound/ValueSem/Examples.lean` | The VS examples: the user's rule, the empty cell, the BO0 cases, the null store, two null sites, HavocNeed, the spread, the dead-end case, the gain, trace C, the `Eval` case, the four losses, the other examples, A4 | §1.8, §4.12 | `user_answers`, `user_real`, `user_call_real`, `user_wider`, `empty_answersVS`, `empty_realV`, `bo0_cases_VS`, `bo0_cases_realV`, `nullStore_answers`, `nullStore_real`, `nulls_answers`, `nulls_exact`, `strong_answersVS`, `strong_realV`, `spread_goneVS`, `spread_ab_noneV`, `dead_answerVS`, `dead_realV`, `gain_answersVS`, `gain_noneV`, `traceC_answerVS`, `traceC_realV`, `eval_answerVS`, `eval_realV`, `losses_VS`, `losses_exactV`, `losses_noneV`, `other_answersVS`, `loop_bf_x_VS`, `siteless_unsound` |
| `Sound/ValueSem/Statics.lean` | The static rule (A5): static holders (`shB`), static writes and reads, well-formedness `StaticWF`, `stripStatic`, design VSS (`analyzeVSS`, `mayProgVSS`, `analyzeVSS_eq`, `mayProgVSS_eq`), the concrete semantics of A5 (`ExecA5`, `CAliasA5`, `execA5_iff`, `CAliasA5_iff`), soundness `csoundVSS`, `no_alias_of_mayProgVSS`, the static invariant (`SCInv`, `SCInv_analyze`, `noTopB`, `noTopB_of_loopFree`), `static_read`, `static_read_end`, `static_aread`, `static_cells_default` | §3.1, §4.5, §4.12 | `analyzeProgVSS_eq` |
| `Sound/ValueSem/StaticsExamples.lean` | The examples of design VSS: example 6.8 of the compact specification, the two gaps of A5, the recorded option (`stripStaticG`), O on the examples | §3.1, §5.5 | `answers68`, `real68`, `exact68`, `reads68`, `cells68`, `strong68`, `strong68_exact`, `weak68`, `weak68_real`, `gapA`, `gapB`, `option_answers`, `o_answersVSS` |
| `Sound/ValueSem/CalleeNull.lean` | The extension with callee nulls (`HavocW`, `SStepW`, `ExecW`, `CAliasW`) and its soundness `csoundVS_W` | §3.1, §4.12 | — |
| `Sound/ValueSem/Backward.lean` | The on-demand test: contributions (`contrib`), upstream calls (`Prog.calls`, `analyzeBW`), the store test (`storeT`, `upE`, `upV`), consistent oracles (`ConsBW`), soundness with loops `csoundBW` | §4.12 | `callVS_contrib`, `InvBW`, `withSets`, `callOra_sound`, `InvVS.transfer`, `BlockedAll.unrename` |
| `Sound/ValueSem/BackwardEq.lean` | The on-demand test equals the stored sets on loop-free programs with different sites (`mayProgBW_eq`); the repeated-site counterexample | §4.12 | `bw_eq`, `noHit_of_fresh`, `Fresh`, `fresh_analyzeVS`, `closeN_some`, `oraOf`, `oraEq_oraOf`, `callSites_nodup`, `bw_needs_distinct_sites` |
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
| `Opt/CellNamed.lean` | O with CN (`havocCNO`, `storeCNO`, `ostepCN`), the exposed set as the node of one reserved key, `mayProgCNO_eq`, `csoundCNO` | §5.3, §5.5 | `havocCNO_rel`, `storeCNO_rel`, `ostepCN_rel`, `analyzeCNO_rel`, `analyzeProgCNO_rel`, `o_answersCN` |
| `Opt/BlockOnly.lean` | O with BO (`callBOO`, `storeBOO`), the two sets as the nodes of two reserved keys, `mayProgBOO_eq`, `csoundBOO` | §5.3, §5.5 | `callWithO_rel`, `callBOO_rel`, `storeBOO_rel`, `ostepBO_rel`, `analyzeBOO_rel`, `analyzeProgBOO_rel`, `o_answersBO` |
| `Opt/BlockOnlyCost.lean` | The cost of the calls of BO, CN and per-cell havoc in O; frames; the separation family; the store test; the set sizes; the fixpoint facts of the two sets | §4.11, §5.5 | `callWithO_work`, `callBOO_frame`, `callBOO_zero_writes`, `callBOO_writes`, `callBOO_writes_zero`, `emptyCells_le`, `havocWithO_work`, `havocWithO_work_ge`, `mem_cnCells`, `havocHRO_work`, `uniqueBO_prefixes`, `ostepBO_load`, `sets_in_universe`, `callWith_xe_length`, `astepBO_xe_grow`, `join_sets`, `sets_in_loop_test` |
| `Opt/ValueSem.lean` | O with design VS (`callVSO`, `retireVO`, `initVO`), `mayProgVSO_eq`, `csoundVSO` | §5.3, §5.5 | `retireVO_rel`, `setSetsO_rel`, `callVSO_rel`, `ostepVS_rel`, `analyzeVSO_rel`, `initVO_rel`, `analyzeProgVSO_rel`, `o_answersVS` |
| `Opt/ValueSemStatics.lean` | O of design VSS (`mayProgVSSO`), `mayProgVSSO_eq`, `csoundVSSO` | §3.1, §5.5 | — |
| `Opt/ValueSemCost.lean` | The cost of design VS: the passive call, its frame, zero heap writes, the on-demand call, the store tests, the separation against BO, CN and per-cell havoc, the answers that VS adds | §4.12, §5.5 | `callVSO_work`, `callVSO_work_ge`, `callVSO_frame`, `callVSO_heap_frame`, `callVSO_env_frame`, `ostepVS_call_frame`, `callVS_env_ne`, `astepBW_call`, `astepBW_call_args`, `prefix_lookups_leVS`, `uniqueBO_up`, `expB_upE`, `ostepVS_load`, `famA_BO_first`, `separationVS`, `added_answers`, `added_answers_real`, `added_answers_not_objects` |
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
| `retireV`, `callVS`, `storeBO` | the definitions: Sound/ValueSem/Concept.lean (`retireV`, `callVS`), Sound/BlockOnly/Concept.lean (`storeBO`); lemmas with the same last name part: `NE.retireV`, `NE.callVS`, `NE.storeBO` (Sound/ValueSem/Inv.lean), `Fresh.retireV`, `Fresh.callVS`, `Fresh.storeBO`, `Corr.retireV` (Sound/ValueSem/BackwardEq.lean) |
| `renameO_childCN` | Sound/CellNamed/Inv.lean; the variant `renameO_childCN'` is in Sound/BlockOnly/Ghost.lean |

---

## Appendix B. Probe index

All tests are in `JTEST/alias/DirectedAliasProbeTest.kt`; the sample is `DirectedAliasSample.java`. "Today" is the measured verdict on main. "Directed" is the expected answer under the default policy (§9.3): `entryUnique = true` (D1), recency on. The column was derived with per-cell havoc; for design VS the rows with a call, and the rows that read an unwritten field of a new object, can differ (§9.3). In this column, `new(x)` is the `AliasAllocInfo` of the allocation of `x`, and `arg:p` is the argument path `p`. "Rec" marks sets that also depend on recency (D3). "Lean" is the related theorem.

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
| 28 | `today static field write is ignored so the static read does not alias the written value` | PS10 | unsound | same: `alias(t) ∌ v`, no `new(v)` (the static write is ignored on purpose: A5, D15) | | `static_unsound`, `static_as_field` |
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
