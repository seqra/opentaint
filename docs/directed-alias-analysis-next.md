# Directed local alias analysis — next-iteration proposal

This document collects the deviations from `directed-alias-analysis-impl.md` (IMPL) and the proposals for the next iteration. The spec (`directed-alias-analysis-spec.md`) and IMPL stay normative. No change of this document is in the code. The user decides each item, and then the item goes into the next iteration. Section numbers `§I n` refer to IMPL, `§S n` to the spec. The full measured numbers are in `directed-alias-analysis-measurement.md`. This document cites only the numbers of the implementation reports.

Ids: `DV` deviation or ruling, `PA` answer-preserving proposal, `PB` semantic proposal (user decision), `PC` test or tooling proposal, `Q` open question. `A1`-`A6` are the assumptions of §S 3, `L` and `G` the losses and gaps of §I 1.4.

## 1. Status and semantic scope

### 1.1 Status

The branch `saloed/directed-alias-impl` has the steps T0-T9 of §I 9: the facade with the mode switch, the tables, the state and the transfer, the alias CFG with the WTO fixpoint and the liveness, the call closure and the models, the queries, the inlining at depth 1, the oracles (Lean vectors, naive concept, post-fixpoint checker, concrete fuzz), SHADOW mode and the statistics. `DSU` stays the default, and its answers do not change (D13). `SHADOW` and `DIRECTED` are experimental (hidden CLI option `--experimental-alias-analysis-mode`). Gates at `8ebf62f53`: G-JVM 785 tests, 0 failures in DSU and in SHADOW mode; G-QL 207 tests, 0 failures in DSU mode; G-ROOT only the 52 Go baseline failures. In DIRECTED mode, 33 G-JVM tests fail: each one pins a DSU answer that the spec changes (Task 10 report). T10 (default `DIRECTED`) is not done. The main problem is memory and answer volume on real projects (investigation D1). On tms, SHADOW mode runs out of memory at each K/D at 8 GB, and K = 7, D = 6 also at 16 GB. Main analyzes tms in 38 s. The cause is the growth that the rules give, not an engine defect: string-building code reads about 30 `<rule-storage>` model cells, so each base gets up to `|cells|^K` origins, and a query can give more than 2 million paths. Two G-QL tests (`StrConcatTest`) time out in SHADOW and in DIRECTED mode for the same reason.

### 1.2 Semantic scope of the proposals

| Group | Items | Answers change | User decision |
|---|---|---|---|
| Deviations already in the code | DV1-DV14 (§2) | DV1, DV2, DV3, DV7 change answers against IMPL or the Lean model; the others do not | Confirm or reverse |
| (A) Engine changes | PA1-PA10 (§3.1) | No. Each item names its theorem or argument | Priority only |
| (B) Semantic changes | PB1-PB6 (§3.2) | Yes | Option and value |
| (C) Tests and tooling | PC1-PC6 (§3.3) | No | Priority only |

## 2. Deviations and rulings

The controller took these rulings during the implementation (ledger `progress.md`). Each row gives the reason and the cost if the ruling is wrong.

### 2.1 Rulings that change answers against IMPL or the Lean model

| Id | Ruling | Reason | Cost if wrong |
|---|---|---|---|
| DV1 | Query search universe = the origins of the table (Task 5). The default parents of `Deep(b)` are only the depth-K `Sym` origins of `b` that the table has (plus the query-local origins of a heap-path query). The Lean `findAlias` takes all `Sym(b, q)` with `|q| = K`. | A dropped path goes through a depth-K entry path origin that no state holds. Under A1 it is a different object from each object that `deep(b)` stands for in this method. The full enumeration adds up to `|cells|^K` paths. | Missed aliases through deep summaries under entry aliasing. This is inside gap G2. Side effect: the naive oracle uses the engine table for this rule (not independent, PC2), and the `nullOnly` statistic differs on 24 random-program answers (0 on the samples). |
| DV2 | Deep-summary element paths (Task 8, F1). A local that holds a depth-K origin `⟨b.q⟩` and `deep(b)` aliases `x.q'[*]` for each depth-K holder, also when the holder is not an array. Proposed new loss **L5** for §I 1.4. | It is the specified answer: the cells have no type, and the unwritten element cell of `⟨b.q⟩` holds `deep(b)` by default (§S 3). Engine = naive concept on all probes. | Precision loss against the DSU on probe rows 41 and 42: `listWalk` gives the 13 DSU paths and 6 more (`cur.next^k[*]`, k = 0..5). Fix options: PB3. |
| DV3 | A pass-through model whose `to` is `this`, a method argument or a constant, without accessors, is skipped (Task 4). A model `from`/`to` on the result of a call without a result variable is dropped, as on main. | §I 4.5 row 1 is for caller locals. A callee cannot rebind a caller variable, and a root has a fixed value by rule. | Fewer model aliases. Example: `void f(A p, A q) { link(p, q); }` with the model `arg0 -> arg1`: the DSU merges `p` and `q`, the directed engine gives no alias. With a local `l` in place of `q`, the engine adds `pts(p)` to `l`. |
| DV7 | A resolved call with an override that has no body (native, no graph) also applies the unresolved call rule (final fix, item 2). `after = join(returns, unresolved rule with models)`, and the exceptional exit also gets the call closure. | §I 5.5 covers only "no return state". Main drops such an override silently, so its call effect is lost (unsound). | More weak stores after such calls. Example: `e = x.f; m(x); t = x.f; t.g = v; w = e.g` with one Java and one native override of `m`: before the fix `w = {v}`, now `w = {v, x.f.g}`. Cost: a second `resolveMethodCall` for each resolved call statement (PA6). |

### 2.2 Rulings without an answer change

| Id | Ruling | Reason | Cost if wrong |
|---|---|---|---|
| DV4 | `Eval` keeps only the origins that are unique by kind. Lean uses `canU`, which is wider. `Etree` uses `isSym`, Lean uses `isSymB` (see PA8). | An origin that is not unique by kind fails `uniqueByKind` first. So the `isUnique` answers are the same (`uniqueBO_comp`). | None. The KDoc must name the difference (PC6). |
| DV5 | The liveness `use(v)` has each JIR read of a local (for example an `if` operand), not only the reads of alias statements. | A query at that statement must see the aliases of the local. Example: a query at `if (x == null)` gives the aliases of `x`; with alias reads only, `x` is dead there and the answer is `[]`. More live variables never lose soundness. | Slightly larger states. |
| DV6 | `PostFixChecker` also checks the Lean `liveOKB`. | The engine computes its own kills. Without the check, a wrong kill rule passes. `csoundKill` needs `LiveOK`. | None. |
| DV8 | Statistics are off on the default DSU path (final fix, item 1; it replaces the Task 9 ruling "statistics always on"). Only the per-method compute timing stays. The hidden flag `--experimental-alias-stats` turns on the full statistics in DSU mode. SHADOW and DIRECTED always record them. | §I 8 asks for `AliasVolumeStats` on both backends. The per-query bookkeeping had a cost on the default path. | The DSU volume baseline needs the flag. §I 8 does not list the flag (PC6). |
| DV9 | Hidden CLI options for K and D: `--experimental-alias-symbolic-depth` (default 7) and `--experimental-alias-max-accessors` (default 6), minimum 0. | §I 8 makes K and D parameters, and the design plans a K sweep. Without the options the sweep cannot run. | Two more hidden options. The CLI accepts K < D + 1 (see PB5). |
| DV10 | SHADOW `StrConcatTest` time-outs are accepted (2 G-QL tests). | The consumers get the DSU answers, but the directed query runs in the IFDS worker thread and has no time limit. A budget is a volume control (D11), so the user decides (PB4). | SHADOW mode is not usable on string-heavy inputs until PB4. |
| DV11 | Statistics output: `ALIAS-STATS` INFO log lines for each project; a summary at the end of the taint analysis, or by a shutdown hook after an out-of-memory error or a time-out. The lines need `--verbosity info`. | §I 8 names the counters but no output channel. A log line is the smallest channel that a CLI run can measure. | Change of the sink later. |
| DV12 | Edges into a catch handler come only from `JIRCatchInst.throwers` (the raw JIR list, §I 5.1). | IMPL requires it. | A handler input is missed if the JIR thrower list is not complete. No test covers it (PC3). |
| DV13 | Query details: the fixed order `AliasInfoOrder` (paths before items); a local that the analysis never saw gives `null`, a known local with no value gives `[]`; the heap-path query gives paths only, no items (§S 5.7); the reachability filter of main also on the after states; the engine callee context is keyed on the identity of the `CallTreeNode` (main's `ContextInfo` collides at 1000 or more overrides, Task 10 fix). | §I 1.5, §I 6.2, §S 5.7; the context collision made two bodies share sites (unsound). | None known. The heap answers of the probes are not like-for-like with the DSU. |
| DV14 | Process rulings: `TaintRulesCallModelProvider` moved out of `JIRDsuAliasAnalysis` (logic identical); production inlining depth = `experimentalAAInterProcCallDepth` (default 1, as main); the measurement runs replay the jar command of the Go CLI with the jar flag (the Go CLI has no pass-through); the D1 optimizations and D11 are not implemented (task: no change that is not proposed); T10 is not done; the T3 test of a loop at the first instruction uses the JIR-free driver (JIR always puts a `goto` at index 0); a nested static type name is the string of main (`Outer.Outer$Inner`). | D13, D6, D12; the task rule; T10 needs the acceptance of the user. | None for answers. |

### 2.3 Done in the final fix wave

These ideas are in the code (commits `05f495506`..`8ebf62f53`). They are not proposals.

- `nullOnly` statistic: computed in the search, with no second pass (D1: 25.2 s of a 25.8 s query before).
- `ALIAS-SHADOW-DIFF` lines: at most 20 items of each list and at most 8000 characters.
- DSU path: no per-query statistics state (DV8).
- K/D CLI values: negative values are refused.
- `BaseTable.static` refuses a new type name after `freeze()`.
- SHADOW mode gives a directed cancellation or interrupt to the caller.

## 3. Proposals

### 3.1 (A) Answer-preserving engine changes

The node of a set is unique (`Tbl.id_inj`), and the engine state is equal to the set state (`mayProgVSO_eq`, `den_*`). So a change that gives the same sets in the same states gives the same answers.

| Id | Problem | Evidence | Change | Why the answers stay equal | Priority |
|---|---|---|---|---|---|
| PA1 | `load` (§I 4.2) folds `union(acc, read(o, c))`. Each step interns an intermediate node, so a base of m origins makes m nodes of sizes 1..m: Θ(m²) content that no state holds. | Probe K = 7, 15 appends: 112.6M ints, 0.24M (0.2 %) held by states. Merged: 1.65M ints, fixpoint 668 ms -> 65 ms. tms `GroupMember#toString()`: 264M -> 151M ints. | Concatenate the member arrays of `read(o, c)`, sort, dedupe, intern one time. Keep the fold for small bases if the union memo hit rate matters. | The result is the same set, so the same node (`Tbl.id_inj`). The union memo gets fewer entries. | 1 |
| PA2 | `AliasQuery` keeps one `ReverseIndex` for each queried state slot for the life of the method context. | tms SHADOW K = 0, D = 0, 8 GB: 10 521 indexes, 606M longs (4.85 GB); only 6 438 distinct heap maps. | (1) Key the heap part of the index on the identity of the heap map. (2) Index by node: origin -> nodes, node -> heap keys. (3) Drop the index of a state when its answers are cached. | The index is a function of the state. The holders do not change (`holders_iff`). | 1 |
| PA3 | §I 5.2 has checkpoints only at nodes, joins, closures and retires. `load`, `storeWeak` and `applyModel` have none. | One `toString()` node (32 models) runs more than 5 s between two checkpoints. Smoke `aliasTimeUsMax` 11.2 s with a 10 s limit. `HtmlUtil#summary` stops only after 258M ints. | Call `step()` in `load`, `storeWeak` and `applyModel`. | The time-out answer is `null`, as now (§I 1.3). Only the time when the engine sees the time-out changes. Note: the heap fills in about 5 s, so this does not stop the memory growth. | 1 |
| PA4 | A weak store of v into cell c of m origins gives m nodes `{child(o, c)} ∪ v`: Θ(m·|v|) real state content. | `GroupMember#toString()` with PA1: 81.6M ints held by states (326 MB for 29 instructions). | Keep a union node as a pair of child nodes (a DAG, §S 4), and get the members on demand. Or keep a heap entry as (default child present, shared node). | Same sets. Proof obligation: `den_*` and `nf_mapEq_iff` for the new node form. A design task, not a code task. | 2 (design) |
| PA5 | The search expands each cell with a non-empty preimage, also when no variable reaches it within the remaining depth. Lean `kid` expands a child only if `live`. | Builder-chain probe (K 3/5/7, D 2/4/6, up to 6.6M expanded nodes): 0 nodes prunable. | Compute the `live` layers of the queried state and skip a child set that does not meet the layer of the remaining depth. | `search_mem`, `search_nodes` (`Opt/Query.lean`). | 4 |
| PA6 | The lowering resolves each call when it builds the CFG, also a call that the fixpoint never reaches. DV7 calls `resolveMethodCall` a second time. | Not measured. | Emit `ResolvedCall` for each call within the depth. `CalleeBodies.build` resolves at the first evaluation and also sets the bodiless-override flag. An empty list falls back to the unresolved rule. | Same resolver, same result for each reached call. An unreached call has no state, so no answer reads it. | 3 |
| PA7 | `AliasCfg.callees` and the `CalleeBodies` closures (JIR graphs) stay in memory for the life of the result. Queries never read them. | Not measured. A method with 40 resolved calls keeps 40 or more callee CFGs. | After `DirectedFixpoint.run` and its check, drop the callee CFGs. Keep only the data that the queries read. | Queries read only the root states and the frozen tables. | 3 |
| PA8 | `Etree` keeps each `Sym` origin, also of `NULL`, `CONST`, `BOX` and `ALLOC_CHILD` bases. These origins are never unique. | Not measured. `x.f = "s"; x.g = null; m(x)` puts `const("s")` and `null(i)` into `Etree`. | Filter `Etree` by `isSym(o)` and base kind in `{THIS, ARG, STATIC, FRESH}`, plus the markers (Lean `isSymB`). | `uniqueBO_comp`. | 4 |
| PA9 | Each evaluation of an unresolved call builds a `HeapIndex` of the whole written heap: O((K + 2)·written keys). In a loop the same call runs again with the same heap map. | Not measured. | Cache the last `HeapIndex` by the identity of the heap map. | The index is a function of the heap map. | 4 |
| PA10 | `AliasCfg` keeps one `BitSet` of global `VarId`s for each node. A callee with 3 locals in a caller with 2000 locals has bit sets of more than 2000 bits. | Not measured. | Give the locals of one CFG a dense index; keep the live sets over it. | Same live sets, another encoding. | 5 |

### 3.2 (B) Semantic changes that need a user decision

#### PB1. Volume control (D11)

Problem. The taint analysis copies one fact for each reported path (R0). The directed answers can be very large: up to 2 114 360 paths in `StrConcatTest` (DSU: 9-212 answers for the same queries), and 85 950 paths in the tms smoke run (DSU maximum: 21).

Options (design D11):

| Option | Effect | Measured |
|---|---|---|
| (a) No control | Sound; keeps CK3 | Not viable: tms out of memory, 2 G-QL time-outs |
| (b) Smaller D | Complete up to the new D; unsound against main for longer paths | Probe K = 7, 15 appends, result query: D = 2: 1 831, D = 4: 69 129, D = 6: 914 544 paths. tms K = 7, D = 2 still runs out of memory (the tables, not the queries) |
| (c) Path budget `maxQueryPaths`: shortest paths first, fixed order, `truncated` counter | Deterministic; unsound like the cache cut of main | Not implemented |
| (d) Simple paths only | Unsound in general (`x.next.next` on one summary origin) | Not implemented |
| (e) Call drop of main, diagnostic only | Unsound (U2); A/B only | Not implemented |

Note. D11 controls the answers only. At K ≥ 3 the memory is in the fixpoint tables (PA1, PA4, PB2). At K ≤ 1 it is in the reverse indexes (PA2).

Recommendation: (c) as a safety net, with the value from the SHADOW distribution after PA1-PA3 and PB2. Keep D = 6.

#### PB2. Model reads through many `<rule-storage>` cells

Problem. `Object#toString()`, `StringBuilder#toString()` and `Throwable#toString()` get 32 pass-through models. 24-30 of them are `this.<C>.<rule-storage> -> result`, one for each class `C` of the model base that overrides `toString` (`File`, `JobID`, `HttpRequestBase`, ...). `StringBuilder#append` reads 2 such cells. A model read of an unwritten cell gives each receiver origin a new default child (§S 5.2). An append chain feeds the result back into the receiver, so each base gets up to `Σ_{d≤K} |cells|^d` origins.

Example. tms `GroupMember#toString()` is `"GroupMember [id=" + id + ... + "]"`: `new StringBuilder()`, 15 appends, `toString`. It has 29 instructions and no loop, and it makes 99 344 origins (46 480 at depth 7) and 264.5M ints of node content.

| Option | Change | Effect on answers | Measured |
|---|---|---|---|
| (a) One alias cell | Map all `<rule-storage>` cells of the models to one alias cell | A path `x.<C>.<rule-storage>` and `x.<D>.<rule-storage>` become one path; more aliases between these cells | Prototype (with PA1 and no index cache), tms SHADOW K = 7, D = 6, 8 GB: 181 methods before the memory guard (82 without the prototypes, 74 with PA1 and no index cache only). Still out of memory; one answer of `WsChannelInterceptor#postSend` has 2 434 262 paths (73 s) |
| (b) Ignore unwritten model cells | A model read of a cell that the method never writes gives nothing | The result loses the aliases to the default content of these cells; the taint analysis tracks marks on these cells itself | Not measured |
| (c) Static type filter | Keep the model cell `C.<rule-storage>` only if `C` and the static type of the receiver are related by subtyping | Removes only cells that the receiver cannot have, if the model base is typed correctly | Not measured |
| (d) No change | — | — | as §1.1 |

Recommendation: (c) first, then measure. Then (a) if (c) is not sufficient.

#### PB3. Deep summaries and element paths (L5)

Problem. DV2. The default parents of `Deep(b)` are each cell of each depth-K holder in the table, also `ELEM_CELL` on a non-array, and also cells that the method never touches. The 85 950-path smoke answer has this shape: about `|vars| × 42 × 2^5`.

Example. `cur = head; while (cur.next != null) cur = cur.next; probe(cur)`: `alias(cur)` has the 13 DSU paths and `cur[*]`, `cur.next[*]`, ..., `cur.next^5[*]`.

| Option | Change | Soundness | Effect |
|---|---|---|---|
| (a) Keep | Add L5 to §I 1.4 | As now | 6 extra paths on rows 41 and 42 |
| (b) Touched cells | Default parent cells of `Deep(b)`: only the cells that the method reads or writes below an origin of `b` | Not sound in general: on a cyclic heap `x.next^7.f` can be `x.next^8` | Smaller answers; cut not measured |
| (c) Type filter | Drop a default parent cell that the static type of the holder cannot have: `ELEM_CELL` when the field type of the last cell is not an array type and not `Object`, `Cloneable` or `Serializable`; a field of class `C` when the holder type and `C` are not related | Sound under Java typing | Rows 41 and 42 give the 13 DSU paths |

Each option other than (a) also changes `NaiveAliasOracle`, the Lean `findAlias` universe and `holders_iff`. Recommendation: (c). Until then, add L5 to §I 1.4.

#### PB4. Query time limit and SHADOW budget

Problem. A query has no checkpoint and no time limit (§I 5.2). In SHADOW mode the directed query runs in the IFDS worker thread before the facade returns the DSU answer. So it uses the IFDS time, and the IFDS analysis loses findings.

Example. `StrConcatTest` `test rule with ellipsis concat` and `test rule with multiple metavar concat`: 133 s and 225 s against a 60 s test limit (99 s and 208 s without the `nullOnly` statistic). DSU mode: 0.1 s and 1.2 s. DIRECTED G-QL: 392 s against 28 s.

| Option | Change | Effect on consumer answers |
|---|---|---|
| (a) SHADOW budget | In SHADOW mode, skip the directed query when the directed answer or the query time goes over a budget; count it as `skipped`. Or run the comparison on a separate executor with its own limit. | None: the consumers get the DSU answers. The statistics miss the largest queries, but the counter shows them. |
| (b) Query time limit | Give a query the remaining time of the per-method limit, with a checkpoint each 1024 expanded nodes (design §7.12). On a time-out, answer `null`. | `null` in place of a large answer, as on a fixpoint time-out (§I 1.3). Unsound like each time-out. |
| (c) Path budget | PB1 (c) | See PB1 |

Recommendation: (a) now, so that SHADOW measurements end. (b) for DIRECTED mode, with the same 10 s limit.

#### PB5. K and D defaults

Problem. K = 7 and D = 6 are open (§S 7). Spec rule: K ≥ D + 1.

| Measurement (D1) | Result |
|---|---|
| Probe, 15 appends, K = 3 / 5 / 7 | Content 0.87M / 9.98M / 112.6M ints; origins 5 828 / 22 905 / 80 470 |
| Probe, 15 appends, D = 6, result query, K = 3 / 5 / 7 | 6 689 113 (149 s) / 985 009 (31 s) / 914 544 (111 s) paths |
| tms SHADOW, 8 GB | Out of memory or memory guard stop at each K/D from K = 7, D = 6 to K = 0, D = 0. Directed methods before the stop: 82 (K7 D6), 144 (K3 D2), 1 361 (K0 D0) |

A small K moves `Deep(b)` inside D, and the answers explode. A large K keeps the answers smaller, but the tables explode. K = 3, D = 6 is the worst cell.

Options: (a) keep K = 7, D = 6 and refuse K < D + 1 in the CLI; (b) keep K = 7, D = 6, and only warn for K < D + 1 (the D1 runs with K = 0, D = 0 are diagnostic runs); (c) other values after PB2.

Recommendation: (b), and a new K sweep after PA1, PA2 and PB2.

#### PB6. Model target base for `x = m(x)`

Problem. The base of a model `to argK.f` is read after `env[result] := {FRESH(s)}`. For `x = m(x, v)` with the model `arg1 -> arg0.data`, the engine stores `v` into `FRESH(s).data`, not into the old object of `x`. A local `y` that holds the old object gets no alias `y.data ~ v`. Main does the same.

Options: (a) as main (now); (b) read the root of the target in the state before the call, and the cell loads in the current state.

Effect: (b) adds aliases only for calls whose result local is also an argument local. Recommendation: (b).

### 3.3 (C) Tests and tooling

| Id | Item | Source |
|---|---|---|
| PC1 | Oracle gaps of the Task 7 review: the `F` lines have an empty lower bound on 16 of 20 deep-summary lines (upper bound only); the random generator has no `Box`, no `ResolvedCall`, no models, and no shared `new`/call site, so the retire-at-call path never runs; the vector parser ignores the Lean kills and accepts `paths=none`; `pathValue` is duplicated; the fuzz does not find the statics mutant (M4) and the deep-coverage mutant (M8) | Task 7 |
| PC2 | Independence of the oracles: the differential test and `NaiveAliasOracle` share the lowering (CFG, ids, kills, WTO, loop sites, throwers), `AliasInfoOrder` and the reachability filter with the engine; the naive `findAlias` uses the engine table for the DV1 rule. Add a lowering check that does not use `JIRAliasLowering`, or document the shared parts as trusted | Task 7, Task 8 |
| PC3 | Missing tests: a call on a caller cycle only through an exceptional edge; a callee strong update with a grown input; `Return(null)` with a non-null result variable (now an empty set with no check: add a check); `⟨@s.c.q⟩ -> deep(@s.c)` at K and an `ALLOC_CHILD` chain below K; a catch handler with a non-thrower predecessor (DV12) | Tasks 2, 3, 6 |
| PC4 | `ALIAS-SHADOW-DIFF` classification: a script over the log or a counter for each class (U1, U2, U4, cache cut, interned constant, new). The 300-line limit of each process hides classes (the samples alone have more than 300 `notSubset` queries) | Task 9 |
| PC5 | DSU work counters for the cost gate of design §11.2: statement evaluations, loop iterations and the `IntDisjointSets` size in `DSUAliasAnalysis`. Counters only; the DSU logic does not change (D13). Also: split the per-method volume by query kind; fix the key collision at index 2^30 and the non-atomic snapshot/reset of the statistics | Task 9 |
| PC6 | Text and cleanup: update §I 1.4 (L5), §I 4.5 (DV3), §I 5.2 (PA3 checkpoints), §I 5.5 (DV7), §I 6.1 (DV1), §I 8 (DV8, DV9) after the decisions; KDoc of `Eval`/`Etree` (DV4); make the new types internal (§I 1.5); remove the dead `Accessor.aliasAccessor()`; move `AliasAnalysisMode.TEST_PROPERTY` to tests; replace the `api` dependency on all of `opentaint-jvm-dataflow` by the mode name | Tasks 1, 4, 5, final fix |

### 3.4 Suggested order

1. PA1, PA2, PA3 and PB4 (a). They do not change consumer answers. They remove the waste of the load fold and of the index cache, and they let SHADOW runs end.
2. PB2 and PB3 (user decision), then a SHADOW run on tms with the K sweep of PB5.
3. PB1 with the value from that run. Then thingsboard and Conductor.
4. PA4 as a design task if the real state content still fills the heap. PA5-PA10 and PC1-PC6 when they are cheap.

## 4. Open questions

1. **DV1, search universe.** Do you accept that the default parents of `Deep(b)` are only the depth-K origins of the table? Example: K = 2, `t = x.f`, and `y` holds `deep(x)` after a `next` loop. Lean `findAlias(y)` has `t.g.c` through `⟨x.f.g⟩`; the engine has `x` and `y.next`, and no path that starts with `t.`. Recommended: accept, and record it in §I 6.1 as a part of G2.
2. **DV2 and PB3, element paths through deep summaries.** Do you accept L5, or do you choose a filter? Example: `listWalk` reports `cur.next^k[*]` (k = 0..5) on a `Box` list. Recommended: PB3 (c), the type filter; until then add L5 to §I 1.4.
3. **DV3 and PB6, model targets.** Do you confirm that a model `to` on `this`, a method argument or a constant without accessors is skipped? Do you want the before-call root for `x = m(x)`? Example: `x = m(x, v)` with `arg1 -> arg0.data` and `y = x` before the call: today `y.data` does not alias `v`. Recommended: confirm the skip; take PB6 (b).
4. **PB2, `<rule-storage>` cells.** Which option? Example: `GroupMember#toString()` makes 99 344 origins from 15 appends and about 30 `toString` model cells. Recommended: (c) the static type filter, then measure; (a) only if (c) is not sufficient.
5. **PB1, volume control (D11).** Which option, and which value? Example: one `StrConcatTest` query gives 2 114 360 paths, the DSU gives at most 212. Recommended: (c) a path budget, value from the SHADOW distribution after step 2 of §3.4; D stays 6.
6. **PB4, query time.** Do you accept a SHADOW budget with a `skipped` counter, and a query time limit with the answer `null` in DIRECTED mode? Example: `StrConcatTest` takes 133 s and 225 s in SHADOW mode, and it finds nothing. Recommended: yes to both, with the 10 s limit of the fixpoint.
7. **PB5, K and D.** Keep K = 7, D = 6? Refuse or warn for K < D + 1? Example: K = 3, D = 6 gives 6 689 113 paths for one probe query; K = 7, D = 6 gives 914 544. Recommended: keep 7 and 6; warn only.
8. **DV7, bodiless overrides.** Do you confirm that the directed engine applies the unresolved rule for an override without a body, while the DSU drops it? Example: `e = x.f; m(x); t = x.f; t.g = v; w = e.g` with a native override: `w = {v, x.f.g}`. Recommended: confirm (the drop of main is unsound).
9. **DV4-DV6 and DV8-DV14.** Do you confirm these rulings? Example: DV8 means that a DSU volume baseline needs `--experimental-alias-stats`. Recommended: confirm all.
10. **Order.** Do you accept the order of §3.4, with PA1-PA3 and PB4 (a) before the next measurement runs? Recommended: yes.
