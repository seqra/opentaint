# Mark-set shallow scan: specification

- **Status:** design, model v2.
- **Formal model:** `formal/markset-scan` (Lean 4.33.1, constructive). It is
  checked by `formal/markset-scan/check.sh`.
- **Branch base:** `origin/main` (`ce24bbbb9`).

## 1. Summary

**What main does today.** `TaintAnalyzer.analyzeStaged` runs a prescan and
then the full scan. The only selection the prescan produces is a global set of
rule ids (`relevantRuleIds`), applied through `taintConfig.selectRules`.

**The staged branch.** The unmerged branch `saloed/staged-analysis-clean`
inserts a shallow scan between the two phases. That scan is a second IFDS run
in the BaseOnly access-path domain, followed by trace-based rule discovery.
Its output is a statement-level selection (`ActionableRules`).

**What this document adds, directly on main.**

- **A statement-level selection mechanism** (§10): the `ActionableRules`
  type, with the same shape as on the staged branch, and a provider that
  *filters* the delegate's rules.
- **A mark-set shallow phase that computes the selection.** It does not run
  IFDS a second time. The prescan records the call graph and every rule's
  residual (mark-only) condition. The phase then runs three steps:

1. **Forward step: mark sets.** Compute which taint marks can exist in the part
   of the program reachable from each root, with access-path bases erased. A
   rule instance is *applicable* if its residual condition can be satisfied
   there.
2. **Backward step: relevance.** Start from the applicable sinks, walk back
   over the automaton edges (sources that transform marks), and compute the
   marks the full scan needs. Every `AssignMark` action that assigns an
   unneeded mark is removed.
3. **Selection.** Keep the applicable sinks, and the applicable sources with
   only their needed actions.

The cost is near-linear in the size of the call graph times the number of
distinct rule signatures. There are no fact sets, no traces, and no
per-finding budgets.

**How the design was checked.** The design was modelled in Lean before this
text was written, and the model has priority over this text (§12). It was then
refined in two rounds:

- **Round 1** modelled the original idea. It found five design bugs, D1–D5, and
  a well-formedness obligation, D6 (§5).
- **Round 2** came from an adversarial review of round 1 against the code. It
  found six gaps between the model and the engine, G1–G6. They were fixed in
  model v2 and in this document (§5.2).

**End-to-end result.** `markset_exact_coarse`: in the implemented
configuration, a full scan restricted by the selection reports exactly the
same sink firings as the baseline. The implemented configuration is the graph
with method contexts merged, with applicability keyed by statement.
`markset_exact_relaxed` is the same result for option 4*.

**Audit.** The model has 411 public theorems. Each depends only on `propext`
and `Quot.sound`: 80 use no axioms, 74 use `propext` alone, and 257 use both.
The audit is transitive, so private lemmas are covered too.

## 2. Scope

| Item | Status |
|---|---|
| Statement-level selection mechanism on main (`ActionableRules`, filtering `SelectedTaintRulesProvider`, phase wiring) | in scope (§10) |
| JVM (`JIRAnalysisManager`) | in scope |
| Go | Out. No statement-level provider exists, so the phase is skipped and the full scan uses the baseline, which is the current behaviour. The model is language-agnostic. |
| Flow-insensitive mode (default) | in scope, proved |
| Relevance pass (default on) | in scope, proved |
| Option 4*: relaxed conditions, corrected (§6.2) | behind a flag, proved |
| Option 3*: flow-sensitive, context-insensitive within a root | behind a flag, proved including relevance (O-FS-3, `markset_exact_fs`) |
| Option 3*: context-sensitive | gated on O-FS-1 and O-FS-2 (§9) |
| Per-root relevance, escape-aware returns, context retention | future refinements (§11) |

**Soundness contract.** The reference is the baseline: the full scan with the
prescan rule-id filter only. Let `F` be the set of findings after
confirmation and before the trace filter, keyed by `(sink statement, sink
rule)`. Then `F` under the mark-set selection equals `F` under the baseline.
This holds for completed runs, under assumptions E0–E11 (§7). If any
precondition fails, the runner fails open and the full scan uses the
baseline.

Two kinds of difference are allowed:

- **Code-flow traces.** A needed fact can be derived in the zero context instead
  of a caller context whose mark is not needed (§6.4). As a result, trace
  generation can succeed or fail differently.
- **Budgets.** A run that times out under the baseline can complete under the
  selection.

## 3. Background: what exists

Facts from the code on `origin/main` (`ce24bbbb9`), with references. Engine
files the staged branch does not modify are identical on both branches.

**Phases and selection**
- *Phases.* `TaintAnalysisManager.Phase` is `Prescan | FullScan`, both data
  objects. `TaintAnalyzer.analyzeStaged` runs `prescan` (Tree AP,
  `ifdsTimeout·0.3`, failures only logged) and then `fullScan`.
- *Selection on main.* It is the rule-id set only.
  `JIRAnalysisManager.selectPhase(FullScan)` calls
  `taintConfig.selectRules(relevantRuleIds)`. There is no statement-level
  selection.
- *The staged branch's selection.* `ActionableRules =
  Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>`,
  installed by `SelectedTaintRulesProvider`. That provider *replaces* the
  delegate's answer instead of filtering it. `sinkRulesForMethodExit` then
  drops the delegate's `initialFacts` filter (`JIRMethodExitRuleProvider`,
  "Apply method exit rules on Z2F edges only").
  - This spec reuses the type, so the two branches stay mergeable.
  - It requires filter semantics (§10), which is what the model's `Sel`
    assumes.
  - Anyone merging the staged branch must take the §10 provider.
- *Always delegated.* Cleaners, pass-throughs, static-field sources, and every
  `allRelevant = true` query (the implicit kills in the summary rewriter)
  must go to the delegate. §10 keeps this.

**Residuals and how the engine evaluates them**
- *Residuals.* `JIRMarkAwareConditionRewriter` folds every non-mark atom at a
  statement. What remains is a `TaintMarkAwareConditionExpr`: an And/Or tree
  over `ContainsMark` and `ContainsMarkOnAnyAccessor` literals, each with a
  `negated` flag. In the prescan, `handlePhase()` sees every surviving rule
  and records its `serializedId`. The providers in the chain do not filter by
  `fact`. The only fact-dependent filter is the exit-sink `initialFacts`
  filter, and the prescan's null query returns a superset of it.
- *Negation.* The engine treats a negated mark literal as satisfied
  (`TaintFactAwareConditionEvaluator:37`). A residual made only of negated
  literals therefore behaves as `true`.
- *Joins.* Conditions that need several facts are joined through
  `RuleAssumptionsManager`. The assumptions live in `TaintSinkTracker`, keyed
  by `(rule, statement)`, with no method context and no root. ND summaries
  applied at callers are a second place where facts are combined.
- *Engine facts.* An engine fact is an access-path tree per base, and it can
  hold several marks (`CommonZ2FSet`, `MethodEdgesFinalTreeApSet`).
- *Cleaners.* A cleaner condition is evaluated on the flowing fact, that is, on
  that base's tree (`applyCleanersOrCallToStart`).

**Where facts and marks come from**
- *Mark creation.* Only `AssignMark` creates marks. This covers sources,
  transformers (Semgrep automaton edges compile to
  `And(Or(stateMark checks), edgeCond) ⇒ AssignMark(stateMark')`), entry-point
  and exit sources, static-field sources, and sink
  `trackFactsReachAnalysisEnd`. Pass-throughs (`CopyMark`, `CopyAllMarks`,
  `StringConcat`, `JIRMethodGetDefault`) preserve marks.
- *Sink end facts.* A call sink's `trackFactsReachAnalysisEnd` facts are
  emitted as zero-context facts (`CallToReturnZFact`), whatever context the
  sink fired in.
- *Entry-point sources.* Only unconditional ones fire, and they fire in every
  method that receives the zero fact.
- *Static-field sources* must be `True`.
- *Exit rules.* Exit sources and sinks are evaluated at `JIRReturnInst` and at
  `JIRThrowInst` in the full scan. The prescan queries them only at returns.
- *Unresolved calls.* The fact is propagated, subject to the summary rewriter's
  kills, and pass-through and `defaultGetModel` rules are applied on top.

**Call graph**
- *No call graph survives the prescan.* Zero-fact edges live in summary
  subscriptions, and `resetApManager` discards them.
- The zero fact explores every CFG-reachable call. Resolution is class-hierarchy
  analysis narrowed by method-context and allocation types, and does not depend
  on facts.
- Lambda trackers are registered only in the prescan, so full-scan lambda edges
  are a subset of the prescan's.
- Callee contexts come from call-site types. The full scan creates no method
  entry point that the prescan did not create.
- *Static fields* are `ClassStatic` bases passed through calls, not a global
  store.

**Prescan status and stored summaries**
- *Prescan status.* The prescan swallows its exceptions (`runCatching`), but
  the engine status survives it. `TaintAnalysisUnitRunnerManager.status` is set
  by `updateFailureStatus`, and main's `resetApManager` does not reset it. So
  the phase can read `ifdsEngine.status.get()` right after the prescan's
  `runAnalysis`. The staged branch resets the status in `resetApManager`; do
  not carry that change over.
  - Because the status is not reset, a prescan failure also shows up in the
    full scan's reported status. This is existing behaviour and is left
    unchanged.
- *Stored summaries.* When summaries are preloaded, the prescan skips those
  bodies. The full scan does not skip them, because `resetApManager` clears the
  loaded flag.

## 4. Inputs: the mark-set program

The recorder builds this during the prescan. It corresponds to `Program` in
`MarkScan/Basic.lean`.

**Nodes** are methods. Contexts are merged, which is sound by `Coarsening`
(§6.1). The roots are the entry points in known units.

**Edges.** A call edge `(caller method, call statement) → callee method` is
recorded while the phase is `Prescan`, at the one place where a zero-to-zero
callee subscription is made:
`TaintAnalysisUnitRunner.subscribeOnMethodSummaries(ZeroToZero)`. That call
covers `handleResolvedMethodCall` (both overloads), cross-unit calls and lambda
resolutions (`LambdaResolvedEvent`). Unresolved calls produce no edge.

**Sites.** One site is recorded per `(statement, rule, residual)`, from the
output of `prepare*Rules` before `handlePhase()` filters it. Sites are
deduplicated on the triple. If the same rule gets different residuals at the
same statement under different contexts, all of them are kept (M8).

Covered statements:
- call statements: method sources and sinks, in the caller;
- method entry: entry-point sources in *every* reached method, and entry sinks;
- **return and throw** statements: exit sources and sinks. Throws are added to
  the prescan's query, closing the B2 gap;
- static-field reads: static-field sources.

What is recorded about each site:
- `kind`: source, sink or pass-through;
- `cond`: the abstract residual (§4.1);
- `gens`: the marks of its `AssignMark` actions;
- the ids needed to build the output: `stmtId`, `ruleId` and the action index.
  Objects are interned at record time, and no IR objects are held per site.

**Cleaner atoms.** The positive mark atoms of every cleaner residual recorded
at a statement (`Program.cleanerAtoms`).

**Recorded statements.** For every method, the set of statements at which the
prescan queried any rule. The provider uses this set for its fallback (§10).

### 4.1 Condition abstraction α

| Residual | α |
|---|---|
| true / false constant | `tt` / `ff` |
| `ContainsMarkLiteral(base·access, m, negated = false)`, and the `OnAnyAccessor` variant | `atom m`; the base and access path are erased |
| literal with `negated = true` | `tt` (E5) |
| `And(xs)` / `Or(xs)` | `and` / `or` |

**Joined cubes.** A cube (DNF conjunct) is *joined* when it has two or more
distinct positive `(base·access, mark)` literals. This is decided **before**
erasure. For example, `A@arg0 ∧ A@arg1` is joined even though it names only one
mark. Counting by the full access path over-approximates counting by base, so
it is sound.

**Tree evaluation.** The implementation evaluates the tree form and never
expands to DNF. `tree_vs_dnf_cost` shows a tree of size 4k+1 has 2^k cubes.

## 5. What the formal model found

### 5.1 Round 1: bugs in the original idea

| # | Original idea | Finding | Resolution | Lean evidence |
|---|---|---|---|---|
| D1 | One mark set per root. This is what the literal idea reduces to; see D5. | **Unsound.** The engine joins condition facts across contexts, and so across roots, at one statement. `(A@0 ∧ B@1)` in a shared callee fires when root E1 passes A and E2 passes B, yet neither root's set holds both. | Evaluate joined cubes on the method-level union `U(method n)`. Their gens go to every root that reaches n. | `d1_fires`, `d1_not_applicableNoJoin`; fix `pe_sound`, `d1_applicable` |
| D2 | 4*: "the rule is satisfiable if any of its marks is in the set" | **Unsound** when a disjunct is constant-true. `[[], [A]]` holds on ∅, yet it mentions only A. | `relax` keeps constant-true cubes. | `naiveAny_unsound`, `Dnf.relax_sound` |
| D3 | 3*: "resolve rules and calls in CFG order" | **Unsound** if read as one pass in statement order. A loop back edge carries a later source's mark to an earlier sink. | 3* is a fixpoint over the CFG. | `linear_order_unsound`, `exLoop_fs_applicable` |
| D4 | Forward applicability alone decides the selection | **Ineffective.** A reachable source whose condition can be satisfied is always applicable. | Add the backward relevance pass. Its closure over transformers is necessary. | `backward_closure_necessary`, `needSinkOnly_unsound` |
| D5 | Context-sensitive IN/OUT tabulation per (method, IN) | **Unnecessary** without 3*. The least solution is one closure per root. Every context in root E's tree gets IN = ∅ at the root and `S_E` elsewhere. | One closure per root. | `collapse_is_solution`, `collapse_least`, `collapse_context_tree`, `conceptContexts_collapse` |
| D6 | (implicit) Every statement is visible to the scan | **Required.** The engine can use a call or a site at any statement it reaches. The scan only sees recorded statements. | Recorder invariant `PcWF` (E0), plus the provider fallback for unrecorded statements. | `pcwf_needed` |

### 5.2 Round 2: gaps between model v1 and the engine

These come from an adversarial review. Each was either fixed in the model or
made an explicit assumption.

| # | Gap | Fix |
|---|---|---|
| G1 (B3) | Sink `trackFactsReachAnalysisEnd` facts are zero-context facts in the engine. v1 kept the sink's context, so it did not over-approximate the engine. | `ESite.genCtx`: sink gens land in the zero context. `InS.sinkGen` places them in every root that reaches n. Necessity: `sinkgen_zero_ctx_needed`. The engine fires a sink in root E2 on an end mark produced under E1, and the semantics without `sinkGen` does not select it. |
| G2 (M3) | The engine joins across method *contexts* at a statement. v1 joined only within one node. | `Program.method`. Joined premises can come from any node of the same method (`PE.genJoined`, `InS.joined`, `CubeSat`). |
| G3 (B4) | (The JVM engine cannot exhibit this with premises that come from callers, because it builds an ND summary edge (E6). The Layer 3 G3 sample therefore checks equality with a control root that supplies both premises.) The old §6.2 claimed that under 4* the per-root closure alone is sound. It is **false**. Relaxing `(A@0 ∧ B@1) ⇒ C` to `A ∨ B` per root loses the zero-context placement of C. A third root that passes neither A nor B, but calls n and has a sink on C, loses its finding (`naive_relax_unsound`). | 4* relaxes only the *test* of joined cubes. Their placement is unchanged (`InSRelax`, `markset_exact_relaxed`). |
| G4 (M2) | An engine fact is a per-base tree with several marks. A cleaner conditioned on mark B also fires on a tree holding a needed mark A. If B were pruned, A would survive, and the restricted run would report more findings. | Every recorded cleaner atom is `Needed` (`Needed.cleanerAtom`). The model keeps kills as a fixed predicate, justified by E4. |
| G5 (B1) | The provider replaces the delegate's rules instead of filtering them, so exit sinks lose their `initialFacts` filter. It is found in the staged branch's provider. On main the provider is new. | The provider filters the delegate's answer (§10). This is the semantics `Sel` assumes. |
| G6 (B2) | Exit rules at throw statements are never recorded. | Record at throws, and fall back to the delegate at unrecorded statements (§10). |

### 5.3 Accepted precision losses

These are sound over-approximations, each with a witness:

| Loss | Witness | Refinement (§11) |
|---|---|---|
| Base erasure | `erasure_precision_loss` | base-kind tracking |
| Relaxation (4*) | `relax_precision_loss`, `relax_strictly_coarser` | none; this is the option's trade-off |
| Non-escaping marks | `pw_applicable` + `pw_not_fires` | escape-aware returns |
| Context merging | `coarsening_loses_precision` | selective context retention |
| Flow-insensitivity | `fs_strict` | option 3* |

## 6. Semantics and algorithm

### 6.1 Mark sets (flow-insensitive, default)

This section corresponds to `InS`, `CubeSat` and `Applicable` in Basic. For
each root E, `S_E` is the least set such that, for every site σ at a node n
that E reaches, and every cube c of σ:

- **single:** if `|c| ≤ 1` and `c ⊆ S_E`, then `σ.gens ⊆ S_E`;
- **joined:** if `|c| ≥ 2` and `c ⊆ U(method n)`, then `σ.gens ⊆ S_E`;
- **sinkGen:** if σ is a sink and `c ⊆ U(method n)`, then `σ.gens ⊆ S_E`.

Here `U(method n)` is the union of `S_E'` over all roots E' that reach any
context of n's method.

A site σ at n is **applicable** iff some cube c satisfies one of:

- `|c| ≤ 1` and `c ⊆ S_E` for some root E that reaches n;
- `|c| ≥ 2` and `c ⊆ U(method n)`.

**Per-node unions suffice for applicability** (`applicable_iff_union`). For a
reachable n, a cube with at most one literal is satisfied by some root iff it
is contained in the node-level union `U(n)`. So applicability needs only
per-node mark unions, never per-root satisfied-signature sets. This is the
memory-critical fact for §6.5.

**The literal concept collapses (D5).** Take per-(method, IN) tabulation with
OUT ⊇ IN, callee IN := caller OUT, and callee OUT flowing back to the caller.
Its least solution is exactly one closure per root (`Collapse`). In the
fragment with no joins and no sink gens, that closure equals `InS`
(`inS_iff_closure`, hypotheses `JoinFree` and `SinkGenFree`). The joined and
sinkGen clauses are the D1 and G1 corrections, and without them the link
fails (`sinkGen_breaks_link`).

**Merging contexts** (nodes = methods) and keying by statement only add
reachability, sites and selections. Both are therefore sound: `merge_hom`,
`inS_hom`, `applicable_hom`, `needed_hom`, `coarse_keyed_overapprox`,
`coarse_needed_overapprox`.

### 6.2 Option 4*: relaxed conditions

**What 4* changes.** A cube with at most one literal already means "this mark
is present", so it is unchanged. For a joined cube c, 4* changes only the
**test**: `c ⊆ U(method n)` becomes `c ∩ U(method n) ≠ ∅`. The placement is
unchanged: the gens still go to every root that reaches n (G3).

What is proved:
- `inS_relax`, `applicable_relax`, `needed_relax`: the relaxed semantics
  over-approximates the exact one. The relaxed selection therefore satisfies
  the hypotheses of `markset_exact`, and stays exact.
- `joined_relax_single_mark`: under 4*, a joined test needs only one mark and
  never a combination. This is the stated motivation for 4*.
- `naive_relax_unsound`: the per-root reading of 4* is unsound. This is the G3
  counterexample.
- At the DNF level: `Dnf.relax_sound`, `Dnf.relax_cubes_small`, and
  `Dnf.relax_union` (join-distributivity).

**Value.** In flow-insensitive mode, 4* only simplifies the joined test. Its
real value is making the context-sensitive 3* cost polynomial (O-FS-2, §9).

### 6.3 Relevance: removing unneeded actions

`Needed` (Basic) is the least set of marks containing:

1. the atoms of every applicable sink's condition;
2. every applicable sink's `trackFactsReachAnalysisEnd` marks;
3. the atoms of every applicable site that generates a needed mark (the
   backward walk over automaton edges);
4. every recorded cleaner atom (G4, E4);
5. the atoms of every applicable pass-through (E8).

Negated atoms are not in α. The engine treats them as true, so pruning cannot
change how they evaluate.

### 6.4 Selection and exactness

The installed selection is `Sel.ofScan app need`. The provider filters the
delegate's answer (§10):

- **sinks:** kept iff applicable at the statement; actions ∅;
  `trackFactsReachAnalysisEnd` intact;
- **sources:** kept with the actions
  `{ a ∈ actionsAfter | applicable ∧ a.mark ∈ Needed }`. A rule whose set is
  empty is dropped;
- **pass-throughs, cleaners, static-field sources, `allRelevant`
  queries:** never restricted.

What is proved:

- **`T-SEL`** (`sel_pe_iff`, `sel_fires_iff`). Selecting every applicable site
  with all its actions reproduces the baseline's engine derivations exactly.
- **`T-REL`** (`rel_preserves_needed_strong`, `rel_fires_iff`,
  `rel_sound_subset`). Pruning actions to `Needed` keeps every fact that
  carries a needed mark. Each such fact is derived under the restricted
  selection **either** in the zero context **or** in its original context, and
  in the latter case that context's mark is needed. Sink firings are identical,
  and the restricted run derives nothing the baseline does not.
  - **Contexts.** The context is kept exactly for zero-context facts
    (`rel_preserves_needed_zero`). A fact whose context mark is not needed is
    re-derived in the zero context (`rel_unneeded_ctx_zero`).
  - **The disjunction cannot be strengthened.** `rel_ctx_not_preserved`
    exhibits a needed fact that loses its needed-mark context, because the only
    fact keeping that context alive carries an unneeded mark. This is why
    traces may differ (§2).
- **Hypothesis `hApp`.** Both are stated under "anything the engine fires is
  applicable", which is discharged by `ecube_applicable` (needs `PcWF`).
- **Composition:** `markset_exact`, `markset_exact_coarse`.

### 6.5 The algorithm

The `Algorithm` module proves these relations:

- the optimized algorithm equals the reference algorithm, with the same answers
  and rounds (`opt_eq_ref`, `optApplicable_eq`, `optNeeded_eq`);
- the reference algorithm equals the specification (`refInS_iff`,
  `refApplicable_iff`, `refNeeded_iff`);
- the reference algorithm terminates within |roots|·|gen universe| rounds
  (`refFuel_suffices`).

The Kotlin algorithm below refines the Lean optimized algorithm with
engineering structure: SCC condensation, bitset hash-consing and
deduplication of roots. These have the same outputs, but that equality is
checked by oracle tests (Layer 1), not by proof.

1. **Intern.**
   - Marks become dense ints.
   - Each site's abstract `(cond, gens, joined-flags)` becomes a signature id.
   - The number of distinct signatures, |Σ|, is bounded by the rule
     configuration, not by program size.
2. **Condense.** Compute strongly connected components of the method call graph
   with an iterative Tarjan.
3. **Signatures per root.** `sig(scc) = local(scc) ∪ ⋃ sig(succ)`, computed
   bottom-up with **hash-consed** bitsets, so that equal sets are shared. Roots
   with the same `sig` share one closure.
4. **Closure per distinct `sig`** over its non-joined cubes: iterate until no new
   mark appears. The closure depends only on the signature set (`closure_dedup`,
   `closure_sig_congr`).
5. **Unions.**
   - `U(n)` is the top-down union of `S_E` over the DAG, with hash-consed
     bitsets.
   - `U(method)` is the same, taken per method.
   - When nodes are methods, `U(n) = U(method n)`.
6. **Joined and sinkGen pass.** Skip it when there are no joined cubes and no
   sink gens.
   - For every node holding a joined site or a sink with gens, test its cubes
     against `U`.
   - Forced gens go into `X(n)`.
   - `X` is added into every root that reaches n.
   - Repeat 4–6 until `X` is stable.
7. **Applicability** of a site at n is `cond.sat(U(n))` by tree evaluation, with
   joined cubes tested on `U(method n)` (`applicable_iff_union`). No per-root
   sets are kept after step 5.
8. **Relevance.** A backward least fixpoint over the applicable signatures,
   seeded as in §6.3.
9. **Emit** `ActionableRules`, keyed by `CommonInst`.

**Proved cost facts:**
- `optRoundCost_le` / `optSteps_le` give the optimized cost bound;
- `refSteps_eq` gives the reference cost exactly;
- on `famProg r k` (k sites sharing one signature, reached by r roots), the
  reference costs ≥ r·k cube evaluations per round and the optimized algorithm
  ≤ r (`fam_speedup`).

**Engineering targets (checked by benchmarks, not proved):**
- time O((V + E)·|Σ|/w + R_distinct·|Σ|·M·cubeWork + J·M/w) per outer round;
- memory O(distinct bitsets), not O(V·|Σ|).

### 6.6 Fail-open and budgets

The runner returns `null`, meaning the full scan uses the baseline, when any
of these holds:

1. the prescan did not complete with status `OK`. The status is captured right
   after the prescan's run (§10, M7);
2. `storeSummaries` is set, or any precalculated summary was loaded (E7, M6);
3. the recorder exceeded its caps (defaults: 20M sites, 20M edges, 512 MB);
4. the mark-set phase exceeded `markSetTimeLimit` (default 30 s) or its memory
   cap;
5. the language is Go;
6. the recorder's seal-time `PcWF` check failed (E0);
7. a debug check failed (E1, E2; enabled in tests);
8. any other exception during seal or scan (`error: <e>`);
9. option 3* only: the per-root reachable statement count exceeds 50M
   (`flow-sensitive size`).

Trigger 2 covers preloaded summaries, because the engine can load
precalculated summaries only when `storeSummaries` is set.

An empty selection (no applicable sink) is not a fail-open trigger. By
`T-REL`, the baseline also reports no findings.

## 7. Engine assumptions (the trusted base)

The theorems are about `PE`, the engine model. The table below covers two
things: why `PE` covers the real engine for soundness, and why the real
restricted run behaves like `PE`'s for exactness.

| Id | Assumption | Evidence | Guard |
|---|---|---|---|
| E0 | The recorded program is well-formed. Roots ⊆ nodes, callees ⊆ nodes, and every call, site and cleaner atom is at a recorded statement of its node (`PcWF`, `Algorithm.WF`, which also requires every site's node and every cleaner atom's statement to be recorded). | By construction of the recorder. | Checked when the recorder is sealed (fail-open trigger 6). `pcwf_needed` shows the check is necessary. |
| E1 | The full scan creates no method entry point and resolves no call edge that the prescan did not, once the prescan completed. | The zero fact reaches every CFG-reachable call. Resolution does not depend on facts. Lambdas are registered only in the prescan. Callee contexts come from call-site types. Cross-unit calls, constructors, `EmptyMethodAnalyzer` and `<clinit>` were checked. | Debug check: the full scan asserts every `(caller statement, callee)` and every new `MethodEntryPoint` is recorded. The whole sample suite runs with it on. |
| E2 | Every rule the full scan evaluates at a *recorded* statement was recorded there with the same residual. Unrecorded statements fall back to the delegate. | Residuals come from static atom evaluation: types and alias analysis, shared across contexts. The prescan's rule queries return a superset of the full scan's, since providers ignore `fact` and the `initialFacts` filter only removes rules. | Debug check: compare the full scan's `prepare*Rules` output with the recording. |
| E3 | Marks are created only by `AssignMark`. Copies and unresolved calls preserve or kill marks. Facts cross methods only along call edges, through argument, `this`, return and `ClassStatic` bases. | `Propagator`, `JIRMethodCallFlowFunction`, `JIRMethodCallFactMapper`, `JIRMethodGetDefault`, `StringConcatRuleProvider` | Covered by the model's `PE` constructors, plus recorder tests per site kind. |
| E4 | Kills of needed-mark facts do not depend on the selection. Cleaners and implicit kills go to the delegate. A cleaner condition sees only the flowing base's tree, and all its atoms are `Needed`. `dropArgumentsLocalTaintMarks` and exit-sink `ClassStatic` drops depend only on selected rules applied to needed-mark facts. | `SelectedTaintRulesProvider` delegation; `applyCleanersOrCallToStart` | Provider unit test. Regression test pinning cleaner evaluation to the flowing fact. |
| E5 | Negated mark literals are treated as true. | `TaintFactAwareConditionEvaluator:37` | A unit test fails if this changes; the abstraction would then need the atoms under negation. |
| E6 | Multi-fact conditions are joined only at one statement, over facts present there under any context of the method. The model places the joined result in the zero context. That over-approximates the engine, which is less generous in two ways. A joined source whose premises come from callers yields an ND summary edge, which reaches a caller only when that caller supplies every premise at one call site. That was observed in the Task 7 G3 sample. A joined sink's end facts are zero-context facts. ND summaries applied at callers combine only facts already present at the call. | `TaintSinkTracker` assumption keys; `applyRuleWithAssumptions`; `matchNDInitial` | Covered by the model (`PE.genJoined`). D1 regression sample (§8). |
| E7 | No summaries are preloaded. | Preloaded summaries hide callee bodies from the prescan. | Fail-open trigger 2. |
| E8 | Pass-through residuals contribute their atoms to `Needed`. They are mark-free in shipped models and in Semgrep output. | `model/**/config/*.yaml`; Semgrep emits no pass-throughs. | `Needed.passAtom`. |
| E9 | The gate compares the finding set after confirmation and before the trace filter. | `TaintAnalyzer.fullScan`: `confirmVulnerabilities`, then the trace filter. | The harness compares `(ruleId, location)` keys at that point. Code-flow counts are excluded, because the existing e2e diff inflates "missing findings" when it counts code flows. |
| E10 | The engine has the derivation locality `T-REL` relies on: a needed-mark fact's derivation uses only needed-mark facts, zero reachability, and needed-mark initial facts or preconditions (including abstract initial facts in `matchNDInitial`). | Traced by the review. There is no negative dependence on facts other than kills (E4). | Layer 3 debug diff: per statement, the needed-mark facts of the baseline and of the restricted run must be equal (§8). |
| E11 | Confirmation (`VulnerabilityChecker`) of a finding depends only on the sink's end facts and the caller walk. Those are needed marks (`Needed.sinkGen`) and the call graph. | `VulnerabilityChecker` | Covered by the Layer 3 differential. |

**Known engine nondeterminism (M5).** When a joined *exit* source fires, the
result lands in whichever context's fact arrives second (`TaintUtil`), so it
depends on scheduling. Two baseline runs can therefore differ. The Layer 3 and
Layer 4 gates run the baseline twice. They compare only findings that are
stable across both runs, and report the unstable ones separately.

## 8. Test-driven development plan

**The ordering rule.** A module's Kotlin code is written only after its Lean
theorems are proved. The named theorems in §12 each get one mirroring Kotlin
test. Every Lean counterexample (D1–D4, D6, G1, G3) and every precision
witness gets a Kotlin twin with the same program.

**Layer 0: the model.**
- `check.sh`: `lake build` passes; `sorry`, `admit`, `native_decide` and
  `axiom` are rejected.
- An axiom audit of every public theorem, regenerated on each run. Only
  `propext` and `Quot.sound` are allowed. `#print axioms` is transitive, so
  private lemmas are covered.
- Runs in CI.

**Layer 1: pure core** (`opentaint-dataflow`, package
`org.opentaint.dataflow.ap.ifds.markset`, no engine dependencies).
- *Types.* They mirror Basic: `MarkSetProgram`, `MarkCond`, `MarkSite`,
  `MarkSetScan`, `MarkSetResult`.
- *Oracle tests.*
  - `lake exe markset-oracle` generates seeded random programs covering joins
    across contexts, sink gens, recursion, shared callees, many roots and
    cleaner atoms.
  - It records `refInS`, `refApplicable` and `refNeeded` for each.
  - The results are checked in as JSON, and the Kotlin core must match them
    exactly in the default mode.
  - Under 4* the core must return a superset of the oracle's answers.
    `applicable_relax` and `needed_relax` prove relaxed ⊇ exact, and the Kotlin
    relaxed test is a further sound over-approximation (§6.2).
- *Law tests.*
  - monotonicity;
  - relaxed ⊇ exact;
  - coarsening only adds;
  - `applicable_iff_union`;
  - the SCC/hash-consed implementation equals the reference.

**Layer 2: recorder** (`opentaint-jvm-dataflow`). Samples in `core/samples`
check recorded edges and sites for these cases:
- virtual dispatch, lambdas, constructors, `<clinit>` and cross-unit calls;
- static-field reads;
- entry-point sources in non-entry methods;
- exit rules at return **and throw**;
- negated and `OnAnyField` conditions;
- different residuals per context.

This layer also runs the E1 and E2 debug checks over the whole sample suite.

**Layer 3: differential.** Every existing JVM taint sample runs under both the
baseline and with `markSetScan` on. The finding sets must be equal (E9), with the E10
per-statement needed-fact diff enabled.

New samples:

| Sample | What it checks |
|---|---|
| D1 | Two entry points and a conjunctive sink in a shared callee. |
| G1 | A sink's end fact used across roots. |
| G3 | The three-root joined source used with 4*. |
| G4 | A mark-conditioned cleaner on a tree that holds a needed mark. |
| G5 | An exit sink on a fact-to-fact edge. The baseline must not fire. |
| G6 | An exit source at a throw. |
| D4 | A Semgrep chain source → transformer → sink, plus an unrelated rule whose actions must be deselected. |
| D3 | A loop (under 3*). |
| Fail-open | Prescan timeout, preloaded summaries, recorder cap. |

**Layer 4: real-world gate.** Run on ThingsBoard, Conductor and the
`known-projects` corpus. Pass criteria, per project:

1. The set of stable findings equals the baseline's (E9, M5).
2. The mark-set phase takes ≤ 10% of prescan time and ≤ 30 s, and adds ≤ 10% of
   the prescan's peak heap.
3. The full scan is no slower than the baseline.

**Metrics reported per project:**
- the prescan completion rate (the mode fails open on incomplete prescans);
- selected actions / baseline actions;
- selected sinks / baseline sinks;
- full-scan time vs. the baseline and, where available, vs. the staged branch's BaseOnly shallow scan;
- how often the phase fails open.

**Usefulness bar:** the corpus median of selected actions is ≤ 60% of the
baseline. Spring (single dispatcher root) and non-Spring projects are reported
separately.

## 9. Option 3*: flow-sensitive mode

`InFS` works per root and per program point, and is context-insensitive within
a root. It uses the same join and sinkGen placement as v2. Proved:

- **Soundness against `PE`:** `fs_sound`, `fs_fires_applicable`. The
  `CtxOkFS` condition is necessary (`fs_ctx_needed`).
- **Refines the default mode:** `fs_refines_fi`,
  `applicableFS_implies_applicable`.
- **Strictly finer:** `fs_strict`.
- **The single pass is unsound:** `linear_order_unsound`.
- **Size:** `fsPoints_length`.

**Additional recorder input.** 3* needs the engine CFG (`succ`, exits) of every
recorded method. It is recorded at seal time from the method's graph, with
normal edges only, matching the engine.

**Obligations before a 3* flag may be enabled:**
- **O-FS-3:** relevance under 3*. **Proved** in `Relevance`:
  - `NeededOver` parameterizes `Needed` by the applicability predicate.
  - `relOver_fires_iff` is `T-REL` over any `App` that covers what the
    engine fires.
  - `ecube_applicableFS` shows the engine fires only `ApplicableFS` sites.
  - `markset_exact_fs` is the end-to-end result for 3*.
  - `neededFS_implies_needed`: 3* never needs more marks than the default
    mode.
- **O-FS-1:** the context-sensitive variant, where a callee is analyzed with the
  caller's set at the call site. Functional tabulation per `(node, IN)` must be
  sound against `PE`, including joins over the method-level union at a point.
- **O-FS-2:** under 4*, O-FS-1's tabulation must equal a per-mark IFDS (facts
  are marks plus zero) with a global joined-placement table. This uses
  `Dnf.relax_union` and `joined_relax_single_mark`. The cost drops from up to
  V·2^M table entries to polynomial.

## 10. Integration

**The selection mechanism** (new on main):
- *The type.* `ActionableRules` goes in `org.opentaint.dataflow.ap.ifds.taint`,
  defined exactly as on the staged branch.
- *The hook.* `TaintAnalysisManager.selectStatementRules(rules:
  ActionableRules?)` gets a default no-op, which is what Go uses.
- *JVM.* `JIRAnalysisManager` wraps `taintConfig` in `SelectedTaintRulesProvider`
  for the taint analysis contexts, and only there. Local alias analysis keeps
  the raw config. The wrapper has the filter semantics below.
- *Setting and clearing.* `selectPhase(FullScan)` keeps
  `selectRules(relevantRuleIds)`. The selection is installed by
  `selectStatementRules`, which the runner calls just before
  `selectPhase(FullScan)`. It is cleared when the phase is `Prescan`.

**`TaintAnalyzerOptions`.**
- `markSetScan: Boolean = false`. It becomes the default only once Layer 4
  passes.
- `markSetFlowSensitive = false`
- `markSetRelaxed = false`
- `markSetRelevance = true`
- `markSetTimeLimit = 30.seconds`
- the recorder caps.

**`TaintAnalyzer.analyzeStaged`.** Order: `prescan` → `markSetPhase` →
`fullScan`.
- `markSetPhase` records `prescanOk = runCatching succeeded &&
  ifdsEngine.status.get() == OK` immediately after the prescan's
  `runAnalysis`.
- It then seals the recorder, runs `MarkSetScan`, and returns
  `ActionableRules?` (`null` means fail open, §6.6).
- It runs no IFDS and changes no AP manager.
- A Layer 2 test checks that an OOM or exception in the prescan leaves a non-OK
  status. This covers the handler ordering the review flagged (M7).
- `fullScan` calls `analysisManager.selectStatementRules(rules)` before
  `selectPhase(FullScan)`.

**Recorder.**
- `TaintAnalysisManager.markSetRecorder(): MarkSetRecorder?` returns non-null
  only for JVM with `markSetScan` on.
- Edges are recorded at `subscribeOnMethodSummaries(ZeroToZero)` while the
  phase is `Prescan`. Sites and cleaner atoms are recorded in
  `JIRTaintAnalysisContext.handlePhase()`. The prescan also queries exit rules
  at throw statements.
- Concurrency: sharded concurrent interning; marks use `TaintMarkManager` ids.

**`SelectedTaintRulesProvider`** is new on main, with filter semantics (G5,
G6). Every restricted query does the following:
1. Call `delegate.<query>(…)` with the original arguments (`fact`,
   `initialFacts`).
2. If the statement is not a recorded statement, return the delegate's result
   unchanged.
3. Otherwise keep only the rules selected at that statement, and replace
   sources with their action-restricted copies.

A unit test covers the exit-sink `initialFacts` case (the staged branch's G5
bug).

**Output conversion:** `MarkSetResult` becomes `ActionableRules`. Sinks map to
∅, and sources map to their needed `AssignMark` subset.

**Logging:** one line of counts per phase: nodes, edges, sites, signatures,
distinct root signature sets, marks, joined sites, applicable sinks, needed
marks, selected vs baseline actions, and elapsed time and memory.

## 11. Limitations and the refinement ladder

Each refinement is prompted by a checked precision witness. Each needs its own
formal obligations before it is implemented.

1. **Single-root projects (the Spring dispatcher).** `S_E` is global, so
   precision comes from automaton-chain feasibility and relevance only.
   - Next: per-root `Needed`.
   - Then escape-aware returns: a callee's marks return only if they can sit on
     an escaping base. Witness: `pw_*`.
2. **Context merging.** Keep contexts for methods below a fan-in threshold.
   Witness: `coarsening_loses_precision`.
3. **Base erasure.** Track the base kind (argument, `this`, return, static) per
   mark. Witness: `erasure_precision_loss`.
4. **3* variants.** See §9.
5. **Tightening the v2 model.** Both items are precision-only, and each has a
   checked witness.
   - **T1.** `InS.sinkGen` evaluates single-literal sink cubes on the method
     union. `Applicable` evaluates them per root. So an end mark can enter a
     set while its sink is never selected (`ex2_sinkGen_not_applicable`).
     Fix: require `CubeSat` in `sinkGen`.
   - **T2.** The joined case of `CubeSat` does not require a root to reach n,
     so a joined site in an unreached context is applicable
     (`ex2_unreached_applicable`). Fix: add that premise. The engine's join
     needs the zero fact at n, so the premise is sound.
6. **Many roots (R ≈ V).** When every public method is an entry point, rely on
   hash-consing and root deduplication. If the memory cap is hit, fall back to a
   single virtual root: sound, since it is a coarsening that adds reachability,
   but less precise.

## 12. Formal model: module map and theorem index

Build and audit with `formal/markset-scan/check.sh`. It prints how many
theorems depend on which axioms, and fails on anything beyond `propext` and
`Quot.sound`.

Several core `List` lemmas silently use `Classical.choice`:
`List.filter_eq_nil_iff`, `List.Nodup.length_le_of_subset`,
`List.all_eq_false`, `List.length_erase_of_mem`, `List.mem_erase_of_ne` and
`beq_self_eq_true`. The model reproves what it needs constructively. The audit
enforces this.

| Module | Role | Key results |
|---|---|---|
| `Basic` | Vocabulary: `Cond`/`Dnf`, `ESite`, `Program` (with `method`, `cleanerAtoms`), `InS`, `CubeSat`, `Applicable`, `Needed`; the engine model `PE`/`ECubeHolds`/`Fires`; `Sel`, `Sel.ofScan` | definitions only |
| `Cond` | The condition layer | `Cond.sat_toDnf`, `Dnf.sat_mono`, `Dnf.relax_sound`, `Dnf.relax_cubes_small`, `Dnf.relax_union`, `Dnf.relax_sat_iff`, `Dnf.sat_not_join_distributive`, `naiveAny_unsound` (D2), `ECube.abstract_sound`, `ECube.positive_ignores_negated`, `erasure_precision_loss`, `relax_precision_loss`, `tree_vs_dnf_cost` |
| `Collapse` | The literal concept is one closure per root (D5) | `closure_{extensive,closed,least,mono,idem}`, `collapse_is_solution`, `collapse_least`, `collapse_context_tree`, `inS_iff_closure`, `sinkGen_breaks_link`, `conceptContexts_collapse`, `feedIn_collapse` |
| `EngineSoundness` | The scan over-approximates the engine; D1, D6, G1 | `pe_sound`, `ecube_applicable`, `fires_applicable`, `pcwf_needed`, `d1_fires`, `d1_not_applicableNoJoin`, `d1_applicable`, `sinkgen_zero_ctx_needed`, `sg_applicable`, `pw_applicable`, `pw_not_fires` |
| `Selection` | Restriction and relevance are exact; D4 | `pe_mono`, `fires_mono`, `pe_zero_reach`, `sel_pe_iff`, `sel_fires_iff`, `rel_preserves_needed_strong`, `rel_preserves_needed_zero`, `rel_unneeded_ctx_zero`, `rel_ctx_not_preserved`, `rel_fires_iff`, `rel_sound_subset`, `backward_closure_necessary`, `needSinkOnly_unsound` |
| `Coarsening` | Merging contexts and keying by statement are sound | `merge_hom`, `reaches_hom`, `inS_hom`, `applicable_hom`, `needed_hom`, `keyed_overapprox`, `coarse_keyed_overapprox`, `coarse_needed_overapprox`, `coarsening_loses_precision` |
| `Algorithm` | Executable concept vs optimization, with costs | `Algorithm.mem_reachList`, `refInS_iff`, `refApplicable_iff`, `refNeeded_iff`, `refFuel_suffices`, `opt_eq_ref`, `optApplicable_eq`, `optNeeded_eq`, `closure_dedup`, `applicable_iff_union`, `optApplicableU_eq`, `optSteps_le`, `fam_speedup`, `ex2_sinkGen_not_applicable`, `ex2_unreached_applicable` |
| `Relaxed` | The corrected option 4*; G3 | `inS_relax`, `cubeSat_relax`, `applicable_relax`, `needed_relax`, `joined_relax_single_mark`, `joined_relax_decide`, `naive_relax_unsound`, `relax_strictly_coarser` |
| `FlowSensitive` | Option 3*; D3 | `fs_sound`, `fs_ctx_needed`, `fs_fires_applicable`, `fs_refines_fi`, `applicableFS_implies_applicable`, `fs_strict`, `linear_order_unsound`, `exLoop_fs_applicable`, `fsPoints_length` |
| `Relevance` | `T-REL` over any applicability predicate; O-FS-3 | `needed_eq_neededOver`, `relOver_fires_iff`, `ecube_applicableFS`, `markset_exact_fs`, `neededFS_implies_needed` |
| `Integration` | The end-to-end contract | `markset_exact`, `markset_exact_coarse`, `markset_exact_relaxed` |

**Changing the model.** Kotlin types mirror `Basic`. A semantic change starts in
`Basic` and in the affected theorems. `check.sh` must pass before the Kotlin
change is reviewed.
