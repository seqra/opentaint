# Mark-set shallow scan: specification

Status: design. Formal model in `formal/markset-scan` (Lean 4.33.1, constructive).
Branch base: `saloed/staged-analysis-clean`.

## 1. Summary

The staged analysis runs prescan → shallow scan → full scan. The shallow scan
selects `(statement, rule, actions)` triples (`ActionableRules`), and the full
scan runs only with those. Today the shallow scan is a second IFDS run with the
BaseOnly access-path domain, followed by per-finding trace resolution and a
trace walk (`TraceActionSearcher`).

This document specifies a replacement that plugs into the same integration
point. It does not run IFDS a second time. After the prescan, the call graph and
the residual rule conditions are available. The replacement then runs three
steps:

1. **Forward step: mark sets.** Compute which taint marks can exist in the part
   of the program reachable from each root, with positions and access paths
   erased. A rule is *applicable* if its mark-only residual condition can be
   satisfied.
2. **Backward step: relevance.** Start from the applicable sinks and walk back
   through their automaton edges. The result is the set of marks the full scan
   needs. Any `AssignMark` action whose mark is not needed is removed.
3. **Selection.** Install applicable sinks, and applicable sources restricted to
   their needed actions. Everything else keeps its baseline behaviour.

The cost is roughly linear in the size of the call graph times the number of
distinct rule signatures. There are no fact sets, no traces, and no
per-finding budgets.

The design was modelled in Lean before this text was written. The model has
priority over this text, and §12 indexes its theorems. The model found five
design bugs in the original idea and one extra well-formedness obligation
(§5). The fixes are part of this specification. The end-to-end result is
`Integration.markset_exact_coarse`: on the implemented configuration, the
restricted full scan reports exactly the baseline findings. Of the 297
theorems, every one depends only on `propext` and `Quot.sound`.

## 2. Scope

| Item | In scope |
|---|---|
| JVM (`JIRAnalysisManager` + `SelectedTaintRulesProvider`) | yes |
| Go | no. Go has no statement-level selection provider, so the phase is skipped and the full scan uses the baseline, which is the current behaviour. The Lean model is language-agnostic, so a Go provider can reuse it later. |
| Flow-insensitive mode (default) | yes, proved |
| Option 3*: flow-sensitive, context-insensitive within a root | behind a flag, proved (§9) |
| Option 3*, context-sensitive (per call-site IN) | gated: implemented only once O-FS-1 and O-FS-2 (§9) are proved |
| Option 4*: relaxed conditions | behind a flag, proved |
| Backward relevance pass | yes, default on |
| Per-root relevance, escape-aware returns, context-sensitive 3* | future refinements (§11) |

**Soundness scope.** The full scan restricted by the mark-set selection
reports the *same set of findings* as the baseline full scan, which uses the
prescan rule-id filter only. A finding here is a `(statement, sink rule)` pair.
This holds for completed runs, under the engine assumptions E0–E9 (§7). If any
precondition fails, the runner fails open to the baseline.

Two differences from the baseline are allowed:

- Code-flow traces may differ. A needed fact may be re-derived in the zero
  context instead of an unneeded caller context (§6.4).
- A run that times out under the baseline may complete under the selection.

## 3. Background: what exists

Facts established from the code on `saloed/staged-analysis-clean`:

- **Selection type.** `ActionableRules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>`.
  Sinks carry an empty action set. Sources carry the subset of `AssignMark`
  actions to keep. When installed, `SelectedTaintRulesProvider` acts as a
  whitelist for six rule kinds: entry-point sources, method sources, exit
  sources, method sinks, entry sinks and exit sinks. Cleaners, pass-throughs,
  static-field sources and every `allRelevant = true` query (the implicit kills)
  always go to the delegate.
- **Residual conditions.** At a statement, `JIRMarkAwareConditionRewriter`
  folds every non-mark atom to a constant. What remains is a
  `TaintMarkAwareConditionExpr`: an And/Or tree over `ContainsMark` and
  `ContainsMarkOnAnyAccessor` literals, each with a `negated` flag. Rules whose
  residual is `false` are dropped. During the prescan, `handlePhase()` records
  every surviving rule's `serializedId` into `relevantRuleIds`.
- **Negation.** The engine treats a negated mark literal as satisfied
  (`TaintFactAwareConditionEvaluator`, `RulePreconditionUtils`).
- **Cross-context joins.** When a condition needs marks from several facts, the
  engine joins them through `RuleAssumptionsManager`. The assumptions are stored
  by `TaintSinkTracker`, keyed by `(rule, statement)`. That key has no method
  context and no root, so facts reaching the statement under different contexts
  and different entry points are joined.
- **Cleaners.** A cleaner condition is evaluated on the single flowing fact
  (`applyCleanersOrCallToStart`).
- **Where marks come from.** Only `AssignMark` creates marks: in sources,
  entry-point sources, exit sources, static-field sources, and a sink's
  `trackFactsReachAnalysisEnd`. Pass-throughs (`CopyMark`, `CopyAllMarks`,
  `StringConcat`, `JIRMethodGetDefault`) preserve mark identity. Semgrep
  automata compile their edges into sources of the form
  `And(Or(stateMark_i checks), edgeCond) ⇒ AssignMark(stateMark_j)`. These are
  the mark *transformers*.
- **Entry-point sources.** Only unconditional ones fire, and they fire in every
  method that receives the zero fact. A static-field source must have a `True`
  condition.
- **No call graph survives the prescan.** Edges exist only as zero-fact summary
  subscriptions, which `resetApManager` discards. The zero fact explores every
  CFG-reachable call site. Virtual resolution is class-hierarchy analysis
  narrowed by method-context types and local allocation types, and does not
  depend on facts. Lambda and closure trackers are registered only in the
  prescan, so full-scan lambda edges are a subset of the prescan's.
- **Unresolved calls.** The fact passes through unchanged, and pass-through
  rules are applied on top.
- **Static fields.** They are `ClassStatic` bases, passed into every callee and
  returned through summaries. They are not a global store.
- **Stored summaries.** With `storeSummaries`, callee bodies are not traversed.

## 4. Inputs: the mark-set program

The mark-set program is recorded during the prescan. It needs no extra engine
run. It corresponds to `Program` in `MarkScan/Basic.lean`.

**Nodes.** Methods; see §6.1 for why the method contexts of one method are
merged. The roots are the prescan entry points in the prescan's known units.

**Call edges.** Recorded while the phase is `Prescan`, whenever a call is
resolved for the zero fact: `MethodAnalyzer.handleResolvedMethodCall` with a
`ZeroToZeroHandler`, lambda and closure subscriptions included. Each edge is
`(caller method, call statement) → callee method`. Unresolved calls produce no
edge. That is sound because marks are preserved across them (E3).

**Sites.** One site per `(statement, rule)` whose residual survived at that
statement: the output of `prepare*Rules` before `handlePhase()` filters it.
This covers:

- call statements: method sources and sinks, recorded in the caller;
- method entry: entry-point sources in *every* reached method, and entry sinks;
- return statements: exit sources and exit sinks;
- static-field reads: static-field sources.

Each site records:
- `kind`: source, sink or pass-through. Cleaners are not sites (E4).
- `cond`: the abstract residual, a `Cond` tree (§4.1).
- `gens`: the marks of its `AssignMark` actions. For a sink, these are the
  `trackFactsReachAnalysisEnd` marks.
- The original `(CommonInst, TaintConfigurationItem, AssignMark)` objects, used
  to build the `ActionableRules` output.

### 4.1 Condition abstraction α

The abstraction maps a residual expression to a mark-only condition as
follows:

| Residual | α |
|---|---|
| true / false constant | `tt` / `ff` |
| `ContainsMarkLiteral(pos, m, negated = false)`, and the `OnAnyAccessor` variant | `atom m`, position erased |
| any literal with `negated = true` | `tt` (E5) |
| `And(xs)` / `Or(xs)` | `and` / `or` |

The *joined-ness* of a cube (DNF conjunct) is its number of distinct
`(position, mark)` positive literals. The cube is *joined* when that number is
2 or more. Joined-ness is decided **before** erasure: `A@arg0 ∧ A@arg1` is a
joined cube even though it mentions only one mark. The implementation
evaluates the tree form, never an expanded DNF. See `tree_vs_dnf_cost`: the
DNF has 2^k cubes for a tree of size 4k+1.

## 5. What the formal model found in the original design

| # | Original idea | Finding | Resolution | Lean evidence |
|---|---|---|---|---|
| D1 | "Analyze B with A.OUT as B.IN", i.e. one mark set per root (what D5 reduces the concept to) | **Unsound.** The engine joins condition facts across contexts, and so across roots, at one statement. `(A@0 ∧ B@1)` in method B fires when root E1 passes A and root E2 passes B, but neither root's set contains both. | Evaluate joined cubes on `U(n) = ⋃ {S_E : E reaches n}`. Their gens flow into every root that reaches n. | `d1_fires`, `d1_not_applicableNoJoin`; the fix: `pe_sound`, `d1_applicable` |
| D2 | Option 4*: "satisfiable if any mark is in the set" | **Unsound** for conditions with a constant-true disjunct: `[[], [A]]` holds on ∅, but "any mark" is false. | `relax` keeps constant-true cubes. | `naiveAny_unsound`, `Dnf.relax_sound`, `naiveAny_sound_of_no_empty_cube` |
| D3 | Option 3*: "resolve rules and calls in CFG order" | **Unsound** if it is read as a single pass in statement order: a loop back edge carries a later source's mark to an earlier sink. | 3* is a CFG fixpoint. | `linear_order_unsound`, `exLoop_fs_applicable` |
| D4 | Forward applicability alone decides the selection | **Ineffective.** A reachable source with a satisfiable condition is always applicable, so no source work is saved. | Add the backward relevance pass (§6.3). The transformer closure it needs is shown necessary by a counterexample. | `backward_closure_necessary`, `needSinkOnly_unsound` |
| D5 | Context-sensitive IN/OUT tabulation per (method, IN set) | **Unnecessary** in flow-insensitive mode. The least solution collapses to one set per root, and every context in root E's call tree has IN = ∅ at the root and `S_E` elsewhere. | Compute one closure per root. Tabulation is only relevant with 3* (§9). | `collapse_is_solution`, `collapse_least`, `collapse_context_tree`, `conceptContexts_collapse` |

**D6: well-formedness (PcWF).** The engine can use a call or a rule at any
statement it reaches, while the scan sees only a node's recorded statement
list. If a statement with a call or site is missing from that list, the scan
misses reachability (`pcwf_needed`). So the recorder must keep this
invariant: every recorded call edge and site belongs to a recorded statement
of its node. It is checked when the recorder is sealed. If the check fails,
the runner fails open.

The model also records five precision losses. None is a soundness issue, and
each is accepted:

| Loss | Witness | Refinement |
|---|---|---|
| Erasing positions | `erasure_precision_loss` | base-kind tracking |
| Relaxation (4*) | `relax_precision_loss` | none: this is the price of the option |
| Non-escaping marks | `pw_applicable` + `pw_not_fires` | escape-aware returns |
| Merging contexts | `coarsening_loses_precision` | selective context retention |
| Flow-insensitivity | `fs_strict` | option 3* |

## 6. Semantics and algorithm

### 6.1 Mark sets (flow-insensitive, default)

The definitions below correspond to `InS`, `CubeSat` and `Applicable` in
Basic. For a root E, `S_E` is the least set such that, for every site σ at a
node n reachable from E and every cube c of σ.cond:

- if c has at most 1 literal and `c ⊆ S_E`, then `σ.gens ⊆ S_E`;
- if c has 2 or more literals and `c ⊆ U(n)`, then `σ.gens ⊆ S_E`,

where `U(n) = ⋃ {S_E' : E' root, E' reaches n}`.

A site σ at n is **applicable** iff some cube c of σ.cond satisfies one of:

- `|c| ≤ 1` and `c ⊆ S_E` for some root E that reaches n;
- `|c| ≥ 2` and `c ⊆ U(n)`.

The model proves this collapse from the literal concept of per-(method, IN)
tabulation with OUT ⊇ IN, callee IN := caller OUT and callee OUT flowing back to
the caller (D5, `Collapse`). The joined clause is the D1 correction.

**Node granularity.** Merging all method contexts of a method into one node,
and keying the selection by statement, only adds reachability, sites and
selections. It is therefore sound (`inS_hom`, `applicable_hom`, `needed_hom`, `merge_hom`, `coarse_keyed_overapprox`).
The price is precision, with a documented witness. This avoids the context
explosion seen on ThingsBoard.

### 6.2 Option 4*: relaxed conditions

`relax φ` is `tt` if φ has a constant-true cube. Otherwise it is the
disjunction of all of φ's atoms, each as its own cube.

What is proved about it:

- `relax` is sound (`Dnf.relax_sound`).
- Every relaxed cube has at most one literal (`relax_cubes_small`). So under 4*
  the D1 join disappears: the per-root closure alone is sound, and `U(n)` is
  never needed.
- Relaxed satisfaction is join-distributive (`relax_union`). This is what
  makes a per-mark IFDS exact for 4* combined with 3* (§9).

In flow-insensitive mode the gain from 4* is small: it removes the joined-site
pass and the second fixpoint round. Its main value is enabling the
context-sensitive 3* at polynomial cost.

### 6.3 Relevance: removing unneeded actions

`Needed` is the least set of marks such that:

1. every atom of an applicable sink's condition is needed;
2. every mark of an applicable sink's `trackFactsReachAnalysisEnd` is needed;
3. if an applicable site generates a needed mark, every atom of that site's
   condition is needed. This is the backward walk over the automaton edges.

Two things are deliberately not in this definition:

- **Negated atoms.** They are already absent from α, because the engine treats
  them as true. Pruning them cannot change any evaluation.
- **Cleaner and pass-through conditions.** Cleaners are evaluated on the fact
  they clean (E4), so pruning other marks cannot change whether a cleaner
  fires. Pass-through conditions are mark-free in all shipped models and
  Semgrep output (E8). As a guard, the atoms of any pass-through residual that
  does contain a mark literal are added to `Needed`.

### 6.4 Selection

The installed selection is `Sel.ofScan app need`:

- a sink `(stmt, rule)` is selected iff it is applicable at some node whose
  statement is `stmt`. Its action set is ∅, and `trackFactsReachAnalysisEnd`
  stays intact;
- a source `(stmt, rule)` is selected with the actions
  `{ a ∈ actionsAfter | applicable ∧ a.mark ∈ Needed }`. If that set is empty
  the rule is dropped, which is the existing `relevantActions` behaviour.

Exactness:

- **`T-SEL`** (`sel_pe_iff`, `sel_fires_iff`). Selecting every applicable site
  with all its actions gives exactly the baseline engine derivations, and so
  the same findings.
- **`T-REL`** (`rel_preserves_needed_strong`, `rel_fires_iff`,
  `rel_sound_subset`). With the actions also pruned to `Needed`, every fact
  that carries a needed mark is still derived. It is derived in its original
  context if that context's mark is needed, otherwise in the zero context. The
  set of findings is identical, and nothing new is derived.
- **Hypothesis.** Both are stated under "everything the engine fires is
  applicable" (`hApp`). That hypothesis is discharged by `ecube_applicable`
  under `PcWF`.
- **Composition.** `markset_exact` and `markset_exact_coarse` combine the
  pieces.

The re-derivation in the zero context is why code flows may differ (§2).

### 6.5 The algorithm

The optimized algorithm is signature propagation. The `Algorithm` module
proves:

- `opt_eq_ref`, `optApplicable_eq`, `optNeeded_eq`: the optimized algorithm
  equals the reference algorithm, with the same answers and the same number of
  rounds.
- `refInS_iff`, `refApplicable_iff`, `refNeeded_iff`: the reference algorithm
  equals the specification.
- `refFuel_suffices`: the reference algorithm terminates within
  |roots|·|gen universe| rounds.

The Lean optimized algorithm deduplicates signatures per root directly. The SCC
condensation below is an implementation detail with the same output, and it is
covered by the Layer 1 oracle tests.

1. **Intern.**
   - Marks become dense ints.
   - Each site's abstract `(cond, gens)` becomes a *signature id*.
   - The number of distinct signatures, |Σ|, is bounded by the rule
     configuration, not by program size.
   - Bitsets are indexed by mark and by signature.
2. **Condense.** Compute strongly connected components of the method call
   graph with an iterative Tarjan. Recursion then needs no special handling.
3. **Signatures per root.** Compute the union over reachable nodes by a
   bottom-up bitset union on the condensation DAG:
   `sig(scc) = local(scc) ∪ ⋃ sig(succ)`. Each root gets `Σ(E) = sig(scc(E))`.
   Roots with equal `Σ(E)` share one closure; deduplicate by bitset hash.
4. **Closure per distinct Σ(E).**
   - Iterate over the non-joined cubes of the signatures in `Σ(E)` until no new
     mark appears. Each round is O(|Σ(E)|·cubeWork), and there are at most
     |marks| + 1 rounds.
   - `closure_dedup`, `closure_sig_congr`: the closure depends only on the set
     of signatures.
5. **Joined pass (D1).** Skip this step when there are no joined cubes, which
   is always the case under 4*.
   - `U(n)` is the top-down bitset union of `S_E` over the DAG.
   - For each node n holding a joined site σ: if some cube of σ is contained in
     `U(n)`, add σ.gens to the forced set `X(n)`.
   - `X` propagates bottom-up into every root that reaches n.
   - Repeat steps 4–5 until `X` is stable. There are at most |joined
     signatures| + 1 outer rounds.
6. **Applicability.** Compute `Active(n)`, the signatures satisfied under some
   root that reaches n. It is a top-down union of per-root satisfied-signature
   bitsets, plus the joined sites that fired. A site at n is applicable iff its
   signature is in `Active(n)`.
7. **Relevance.** Run a backward least fixpoint over applicable signatures:
   seed with the atoms and gens of applicable sinks, and add the atoms of any
   applicable signature that generates a needed mark.
8. **Emit** `ActionableRules`: a union over nodes, keyed by `CommonInst`.

**Cost.** Let V and E be the call-graph nodes and edges, R the number of roots
and M the number of marks.

| Algorithm | Cost |
|---|---|
| Optimized | O((V + E)·\|Σ\|/w + R_distinct·\|Σ\|·M·cubeWork + J·\|marks\|/w) per outer round |
| Reference: per-root closure over all reachable sites | Θ(R·\|reachable sites\|·rounds) |
| Literal concept (per-(method, IN) tabulation) | up to V·2^M table entries |

In the optimized cost, w is the word size and J is the number of joined sites.
Proved about the costs:

- `optRoundCost_le` and `optSteps_le` bound the optimized cost.
- `refSteps_eq` gives the reference cost exactly.
- The family `famProg r k` has k statements that share one signature and are
  reached by r roots. On it the reference costs ≥ r·k cube evaluations per
  round and the optimized algorithm ≤ r (`fam_ref_round_ge`,
  `fam_opt_round_le`, `fam_speedup`).
- D5 shows the per-(method, IN) tabulation is unnecessary in this mode.

### 6.6 Budgets and fail-open

The runner produces `null` (the baseline) when any of the following holds:

- the prescan did not finish with status `OK`, so E1 cannot be relied on;
- stored summaries were preloaded (E7);
- the recorder exceeded its size cap (default 50M sites and edges);
- the mark-set phase exceeded `markSetTimeLimit` (default 30 s) or its memory
  cap;
- the language has no statement-level provider (Go);
- an internal consistency check failed. For example, a selected sink is
  missing from the recorded sites, or a mark is not interned.

An empty selection (no applicable sink) is **not** a fail-open trigger. By
`T-REL` the baseline would report no findings either, so the full scan runs
with an empty whitelist.

## 7. Engine assumptions (the model's trusted base)

The theorems are about `PE`, the engine model. Each assumption below states why
the real engine is covered by `PE`, and how that is checked.

| Id | Assumption | Evidence | Guard |
|---|---|---|---|
| E0 | The recorded program is well-formed (`PcWF`; `Algorithm.WF`): roots ⊆ nodes, callees ⊆ nodes, and every call and site sits at a recorded statement of its node. | Holds by construction of the recorder. | Checked when the recorder is sealed; fail open if it does not hold. `pcwf_needed` shows it is necessary. |
| E1 | Every call edge the full scan traverses is in the recorded prescan graph, if the prescan completed. | The zero fact reaches every CFG-reachable call. Resolution does not depend on facts, except lambdas, which are registered only in the prescan. Callee contexts are derived from call-site types. | A debug-mode check in the full scan asserts that every resolved `(caller stmt, callee)` is recorded. The test suite runs with it on. |
| E2 | Every rule the full scan evaluates at a statement was recorded at that statement, with the same residual. | Residuals come from static atom evaluation (`JIRBasicAtomEvaluator`, alias and type info), independent of phase and fact. | A debug check compares full-scan `prepare*Rules` output with the recorded residuals. |
| E3 | Marks are created only by `AssignMark`. Copies and unresolved calls preserve marks. Facts cross methods only along call edges and `ClassStatic` bases. | `Propagator`, `JIRMethodCallFlowFunction`, `JIRMethodCallFactMapper`. | Covered by the model (`PE` constructors). Recorder tests cover each site kind. |
| E4 | Kills do not depend on the selection. Cleaners and implicit kills go to the delegate, and cleaner conditions see only the flowing fact. | `SelectedTaintRulesProvider` delegates cleaners and `allRelevant`. `applyCleanersOrCallToStart` uses a single-fact reader. | A unit test on the provider. A regression test pins single-fact cleaner evaluation. |
| E5 | Negated mark literals are treated as true. | `TaintFactAwareConditionEvaluator:37` | A unit test fails if that changes. The abstraction would then need atoms under negation. |
| E6 | Multi-fact conditions are joined only at one statement, over facts present there under any context (`PE.genJoined`). A joined result is visible to the callers of that method. | `TaintSinkTracker` assumption keys, `applyRuleWithAssumptions`. | Covered by the model. The D1 regression sample (§8). |
| E7 | No summaries are preloaded. | Preloaded summaries skip callee bodies, so their marks would be invisible to the scan. | Fail open. |
| E8 | Pass-through residuals are mark-free, or their atoms are added to `Needed`. | Shipped models have type-only conditions, and Semgrep emits no pass-throughs. | The recorder checks this and adds the atoms. |
| E9 | Findings are sink firings. Traces are derived afterwards and may differ (§2). | `StagedAnalysisRunner.fullScan` | Regression diff keyed without code-flow count. See the note on the e2e harness below. |

**Note on the e2e harness.** The existing e2e regression diff counts code flows
inside the finding key. That inflates "missing findings", so the soundness gate
must compare `(rule, location)` keys.

## 8. Test-driven development plan

Proof comes first. A module's Kotlin code is written only after its Lean
theorems are proved. Each theorem gets one Kotlin test that mirrors it.

**Layer 0: the model.** `lake build` succeeds, and an axiom audit script fails
if any theorem depends on anything other than `propext` or `Quot.sound`.
Wire both into CI through `formal/markset-scan/check.sh`.

**Layer 1: pure core (`opentaint-dataflow`, package
`org.opentaint.dataflow.ap.ifds.markset`).** The core has no engine
dependencies. Its types mirror Basic: `MarkSetProgram`, `MarkCond`, `Site`,
`MarkSetScan`, `MarkSetResult`.

- *Oracle tests.* A Lean executable (`lake exe markset-oracle`) uses
  `Algorithm.ref*` to generate seeded random programs with their expected
  `InS`/`Applicable`/`Needed`. The programs cover joins, recursion, shared
  callees and many roots. They are checked into test resources as JSON, and the
  Kotlin core must match them exactly.
- *Law tests*, one per theorem:
  - monotonicity;
  - `relax` ⊇ exact;
  - coarsening only adds;
  - the optimized algorithm equals the reference on generated inputs;
  - the naive "any mark" witness is rejected;
  - DNF expansion is never needed.
- *Witness tests.* Every Lean counterexample (D1–D4, D6 and the precision witnesses)
  becomes a named Kotlin test with the same program.

**Layer 2: recorder (`opentaint-jvm-dataflow`).** Samples in
`core/samples` cover the recorded edges and sites for:

- virtual dispatch, lambdas and constructors;
- static-field reads;
- entry-point sources in non-entry methods;
- exit sources and sinks;
- negated conditions;
- `OnAnyField` conditions.

This layer also holds the E1/E2 debug checks, run over the whole existing
sample suite.

**Layer 3: differential.** Every existing JVM taint sample test is run twice,
once with the baseline and once with `shallowScanMode = MARK_SET`, and the
finding sets must be identical. New samples:

- **D1:** two entry points and a conjunctive sink in a shared callee.
- **D4:** a Semgrep chain `source → transformer → sink`, plus an unrelated rule
  whose sources must be deselected.
- **Loop / D3.**
- **Relevance:** a rule whose sink never becomes applicable, so all its
  sources' actions are removed. Assert that the selection has no action for
  them.
- **Fail-open:** an incomplete prescan and preloaded summaries. Assert that the
  plan is the baseline.

**Layer 4: real-world quality gate.** Run on ThingsBoard, Conductor and the
`known-projects` corpus. Each project must pass all of:

1. The finding set, keyed by `(ruleId, location)`, is identical to the baseline.
2. The mark-set phase (recorder overhead plus computation) takes ≤ 10% of
   prescan time and ≤ 30 s. Its peak heap increase is ≤ 10% of the prescan's.
3. The full scan is no slower than the baseline.
4. Report these metrics:
   - selected actions / baseline actions;
   - selected sinks / baseline sinks;
   - full-scan time vs the baseline and vs the TRACE shallow mode;
   - how often the phase fails open.

   The feature is useful when, on the corpus median, selected actions ≤ 60% of
   the baseline.

The Spring dispatcher is a single root, so on Spring projects the per-root sets
degenerate to one global set (§11). Report Spring and non-Spring projects
separately.

## 9. Option 3*: flow-sensitive mode

The flow-sensitive mode (`InFS`) works per root and per program point
`(n, pc)`. Within a root it is context-insensitive: a callee's entry set is the
union over its call sites. Joins are handled as in D1. The model proves:

- **Sound against `PE`:** `fs_sound`, `fs_fires_applicable`. The per-root claim
  needs the callee's context to be valid for that root (`CtxOkFS`), and
  `fs_ctx_needed` shows this condition cannot be dropped.
- **Never less precise than the default mode:** `fs_refines_fi`,
  `applicableFS_implies_applicable`.
- **Strictly more precise:** `fs_strict`, a witness where the sink comes before
  the source.
- **The single statement-order pass is unsound:** `linear_order_unsound` (D3).
- **Point count:** `fsPoints_length` gives the number of (root, point) pairs.

The cost is O(R·points·M/w) per fixpoint. This is only viable where R is small
or roots can be deduplicated.

Before the context-sensitive variant (the user's "analyze B with A.OUT at the
call site") is implemented, two obligations must be proved:

- **O-FS-1:** functional tabulation per `(node, IN)` is sound against `PE`,
  including joins evaluated on the union over contexts at a point.
- **O-FS-2:** under 4*, functional tabulation equals per-mark IFDS, where the
  facts are the marks plus zero. The proof uses `relax_union` and
  `relax_cubes_small`. The cost drops from up to V·2^M table entries to
  O(E·(M+1)³).

The flag exists from the start, but its implementation is gated on these
proofs.

## 10. Integration

- **`TaintAnalyzerOptions`:**
  - `shallowScanMode: TRACE | MARK_SET`. The default stays `TRACE` until the
    Layer 4 gate passes; then it becomes `MARK_SET`.
  - `markSetFlowSensitive = false`
  - `markSetRelaxed = false`
  - `markSetRelevance = true`
  - `markSetTimeLimit = 30.seconds`
- **`StagedAnalysisRunner.shallowScan`.** In `MARK_SET` mode there is no
  `selectPhase(ShallowScan)`, no `resetApManager` and no IFDS run. The runner
  reads the `MarkSetProgram` the recorder built during the prescan, runs
  `MarkSetScan`, and returns `ActionableRules?`. The fail-open checks in §6.6
  apply.
- **Recorder.**
  - `TaintAnalysisManager` gains
    `markSetRecorder(): MarkSetRecorder?`, which returns `null` unless the mode
    is `MARK_SET` and the language is JVM.
  - Edges are recorded in `MethodAnalyzer.handleMethodCall` for zero handlers
    while the phase is `Prescan`.
  - Sites are recorded in `JIRTaintAnalysisContext.handlePhase()` before the
    pass-through filter.
  - Recording is deduplicated per `(statement, rule)`.
  - The recorder is thread-safe: it uses concurrent sets and interns marks
    through the existing `TaintMarkManager` ids.
- **Output.** A `MarkSetResult` is converted to `ActionableRules`: sinks map to
  ∅, sources to their needed `AssignMark` subset. `SelectedTaintRulesProvider`
  is unchanged.
- **Logging.** Log per-phase counts: nodes, edges, sites, signatures, distinct
  roots, marks, applicable sinks, needed marks, and selected vs baseline
  actions.

## 11. Known limitations and the refinement ladder (CEGAR)

Each refinement below needs its own formal obligations before it is
implemented. Each is prompted by a checked precision witness.

1. **Single-root projects (Spring dispatcher).** `S_E` is global. Precision
   then comes only from automaton-chain feasibility and relevance.
   Refinement: per-root `Needed`, then escape-aware returns (callee marks
   return only when they can sit on an escaping base). The witness is
   `EngineSoundness` precision witness: the mark is dropped by `mapOut`.
2. **Context merging (§6.1).** Refinement: keep contexts for methods below a
   fan-in threshold. The witness is `Coarsening` precision witness.
3. **Position erasure.** Refinement: track the base kind (argument, this,
   return, static) per mark. The witness is `erasure_precision_loss`.
4. **Context-sensitive 3*.** See §9.

## 12. Formal model: module map and theorem index

Build and audit with `formal/markset-scan/check.sh`. It runs `lake build`,
rejects `sorry`, `admit`, `native_decide` and `axiom`, and prints the axioms
of every theorem through `AxiomAudit.lean`. At present:

- 297 theorems;
- 46 use no axioms, 48 use only `propext`, and 203 use `propext` and
  `Quot.sound`;
- none uses `Classical.choice`.

Some core `List` lemmas silently depend on `Classical.choice`
(`List.filter_eq_nil_iff`, `List.Nodup.length_le_of_subset`,
`List.all_eq_false`, `List.length_erase_of_mem`, `List.mem_erase_of_ne`,
`beq_self_eq_true`). The model reproves the parts it needs constructively.
The audit is what enforces this, so it must stay in CI.

| Module | Role | Key results |
|---|---|---|
| `Basic` | Vocabulary: `Cond`/`Dnf`, `ESite`, `Program`, `InS`, `CubeSat`, `Applicable`, `Needed`, the engine model `PE`/`ECubeHolds`/`Fires`, `Sel`, `Sel.ofScan` | definitions only |
| `Cond` | Condition layer and option 4* | `Cond.sat_toDnf`, `Dnf.sat_mono`, `Dnf.relax_sound`, `Dnf.relax_cubes_small`, `Dnf.relax_union`, `Dnf.relax_sat_iff`, `Dnf.sat_not_join_distributive`, `naiveAny_unsound` (D2), `ECube.abstract_sound`, `ECube.positive_ignores_negated`, `erasure_precision_loss`, `relax_precision_loss`, `tree_vs_dnf_cost` |
| `Collapse` | The literal IN/OUT concept equals one closure per root (D5) | `closure_{extensive,closed,least,mono,idem}`, `collapse_is_solution`, `collapse_least`, `collapse_context_tree`, `inS_iff_closure` (join-free fragment), `conceptContexts_collapse`, `feedIn_collapse` |
| `EngineSoundness` | The scan over-approximates the engine; D1; D6 | `pe_sound`, `ecube_applicable`, `fires_applicable`, `pcwf_needed`, `d1_fires`, `d1_not_applicableNoJoin`, `d1_applicable`, `pw_applicable`, `pw_not_fires` |
| `Selection` | Restricting the full scan is exact; relevance; D4 | `pe_mono`, `fires_mono`, `pe_zero_reach`, `sel_pe_iff`, `sel_fires_iff`, `rel_preserves_needed_strong`, `rel_fires_iff`, `rel_sound_subset`, `backward_closure_necessary`, `needSinkOnly_unsound`, `cex_needed_one` |
| `Coarsening` | Merging contexts and keying by statement only add selections | `merge_hom`, `reaches_hom`, `inS_hom`, `applicable_hom`, `needed_hom`, `keyed_overapprox`, `coarse_keyed_overapprox`, `coarse_needed_overapprox`, `coarsening_loses_precision` |
| `Algorithm` | Executable reference and optimized algorithms: the concept vs. the optimization | `Algorithm.mem_reachList`, `refInS_iff`, `refApplicable_iff`, `refNeeded_iff`, `refFuel_suffices`, `opt_eq_ref`, `optApplicable_eq`, `optNeeded_eq`, `closure_dedup`, `optSteps_le`, `fam_speedup` |
| `FlowSensitive` | Option 3*; D3 | `fs_sound`, `fs_ctx_needed`, `fs_fires_applicable`, `fs_refines_fi`, `applicableFS_implies_applicable`, `fs_strict`, `linear_order_unsound`, `exLoop_fs_applicable`, `fsPoints_length` |
| `Integration` | End-to-end contract | `markset_exact`, `markset_exact_coarse` |

**Rules for changing the model.** Kotlin types mirror `Basic`. A change to the
implementation's semantics starts with a change to `Basic` and to the affected
theorems. `check.sh` must pass before the Kotlin change is reviewed. Every
counterexample theorem has a Kotlin twin test with the same program (§8,
Layer 1).
