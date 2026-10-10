# Access paths and storages — specification

Status: design spec of the new access path with all its storages, for
[bidirectional-task.md](../bidirectional-task.md). This document is normative. The design decisions and their reasons
are in [`ap-history.md`](ap-history.md). The spec has two parts:

* this document (`ap.md`) defines the access path (AP): the fact, the edge, the operations and the primitives (micro
  edge, summary edge, mark request, mark conjunction, cleaner, type filter, emission), the runs and the storages;
* [`interpreter.md`](interpreter.md) defines how the analyzer interprets the IR with the AP: the micro edges of the
  statements and of the calls, the aliases, and the order of the rules.

[`analyzer-core.md`](analyzer-core.md) uses both: it defines the analyzer entities, the communication pipeline between
the methods, the end of a run and the iteration driver with the hand-offs.

The formal model is in [`spec/lean`](lean). Every theorem named here is machine-checked and constructive (§10 defines
the term, §12 gives the audit). The claims that are argued and not proved are listed in §11.2. This spec states every
rule in words. A Lean name is only a reference to the model.

THE RULES OF DECISION F72 ARE NORMATIVE, AND THEIR PROOFS ARE PENDING (`ap-history.md` F72). A restricted run can
analyse with the abstract mark `*` (§6.3): a `*` demand pattern gives a FLOW premise, and the restricted runs have no
request rules (§4.5). The theorems that this spec names for the restricted runs and for the iteration (§0.1, §6.1,
§6.6, §10.7, the restricted part of §10.11, §10.12) are proved for the CONCRETE restricted runs of F70 and F71 (the
emission `emitM`, the closures with request rules that never fire, `RExact.DR_concrete`). For the rules of F72 they
are NOT YET PROVED. The task is §11.2, PENDING: THE LEAN MODEL OF F72. The theorem names stay in this spec: they hold
for the concrete design. Run 1 does not change, so its theorems hold as they are.

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

This spec defines:

* the fact representation for the forward and the backward analysis;
* the operations on facts: delta-concat, micro edge application, summary edge application, summary restriction, field
  limit, mark gate and mark request, mark conjunction (ND edges), cleaner, type filter, emission, reversal;
* the storages that the analyzer uses in one run and across runs;
* the soundness theorems for these operations and the scope in which they hold.

This spec does not define the IR interpretation (`interpreter.md`), the analyzer scheduling, the iteration driver (§6.6
gives only its general requirement and its stop rules; `analyzer-core.md` §7 defines the driver) or the trace
resolution (out of scope; §8.10 gives the traces of the report). It defines the contracts that these parts use. The
contract of the backward run (contract B) is in §6.6.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | The interpreter describes a statement by its statement summary: the bases that it touches and its micro edges (`interpreter.md` §2). Every micro edge (a statement edge or a call binding edge) is PRECISE AND COMPLETE: the micro edges of a statement give exactly its flows. The flows of a rule are read in the reference semantics (§3.5): every negated mark literal is true. With this reading a source or a sink edge is precise. A pass rule has no mark literal, so its edge is precise too. (A pass rule with a mark literal is a rule error that is not rejected (`interpreter.md` §1.3); its edge without the literals is an over-approximation, §11.1. Every other rule error rejects the whole rule: it gives no edge.) | The interpreter. |
| S2 | Extra micro edges describe the aliasing: gen edges to the alias paths of the aliases that hold. Each alias edge is precise. The write at an alias is WEAK: the alias base is not touched, so it keeps its old content (`interpreter.md` A3, gap G7). This keeps soundness when an alias does not hold. It is an expected false-positive source (§11.1). The model itself is alias-free. | The alias analysis. |
| S3 | A method does not reassign its formal parameters. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. A JVM method has two exits, the normal exit and the exceptional exit. They are one VIRTUAL EXIT of the model: the exit rules act at both exits, the backward run starts at both exits, and only the normal exit makes a summary edge (argued, §11.2). | The CFG normalisation. |
| S5 | A type filter accepts every path that a real value of the static type can have, and it is prefix-closed (§4.8). | The type checker. |
| S6 | The result of run 1 is the least fixed point of the rules of run 1 (§6.1; Lean: `D`). The result of a later run is the least fixed point of the rules of a restricted run (§6.1; Lean: `DR`, and `Backward.DB` for a backward run). With the `[any-taint]` tail and its exclusion (§2.3 W8) the forward closures are `AnyTaintEx.D6X` (run 1) and `AnyTaintEx.DRX` with the spec rules `emitX`, `satX` and `HandoffX.restrictIX` (a forward restricted run; `AnyTaintEx.DRXs` has the earlier restriction) (§10.11, §10.12); the backward run stays `Backward.DB` (it has no `[any-taint]`, W8 (d)). These restricted closures are the CONCRETE design of F70 and F71: they have the request rules, and with the emission `emitM` (`emitX`) no request rule fires. The restricted closures of F72 (no request rules, the emission of §6.3 with the FLOW form, the satisfaction of §4.3; Lean, PENDING: `DRA`, `DBA`) are not modelled yet (§11.2). The worklist may compute it in any order. | The analyzer. |
| S7 | Mark well-formedness: no micro edge or call binding has a `*∖X` premise, and a micro edge with a concrete target mark has a concrete premise mark (`Exact.MarkWF`; §4.1 asserts both). Without it a normal edge can claim a cleaned mark (`Exact.CexMark`; necessary in the model: the counterexample program breaks S8). | The interpreter (sources have the premise mark `zeroMark`, conditional sources `T`). |
| S8 | No `*/Universe` edge (§1, Universe): a micro edge with a `$` premise has a concrete premise mark, and no micro edge, binding or initial fact has the tail kind `*/Universe` (`Invariant.no_univ_star`; each hypothesis is necessary: `no_univ_needs_*`). Also (an interpreter duty; §4.1 asserts it): no micro edge has a `$` premise and a `*` target, and every micro edge with a `$` target has a concrete premise mark (`Kinds.ExactTargetConc`; the conclusion kinds of §7.2 use it). | The interpreter (`interpreter.md` I7). |
| S9 | A conjunction literal has a concrete mark (`NDExact.LitConc`). Without it the ND exactness is false (`NDExact.CexLit.cex_lit`). | The interpreter (a mark literal names its mark). |
| S10 | Program well-formedness: every micro edge of a statement reads from a base that the statement touches, and every call binding has the premise mark `*` (it passes every mark). With conjunctions, also: the target of a conjunctive micro edge has a concrete mark and no `*` tail (W7). Every call binding has the `*` tail on both sides, so no call binding has an `[any]` or an `[any-taint]` target (Lean: `AnyTaint.BindNoAny`, the part "no `[any]` target"; a hypothesis of the kinds invariant of run 1 only: `AnyTaintExKinds.D6X_any_conc` for the spec closure `AnyTaintEx.D6X`, and round 1 `AnyTaintSim.D6T_any_conc` for `AnyTaint.D6T`; it is necessary, `AnyTaintSim.CexKinds.cex_bindNoAny`). (Lean: `Program.WF`, its type-filter part is S5; with conjunctions `ND.NProg.WF`, its part `target`.) | The interpreter (`interpreter.md` §2, §3.1, §5.3; the `*` tail of a binding: `interpreter.md` I11 (a)). |
| S11 | The backward contracts (the backward run and contract B, §6.6, need them; (d) is also a hypothesis of the zero-drop theorems of `NDZeroThms` (§4.6, §10.10), with `NDZero.ZeroCalls` (§3.5: the zero binding), `NDZero.ConjAdj` and the policy condition `NDZeroBase.AlphaZero` (`policy1_alphaZero`); (g) only for §8.7 R3): (a) every call binding has the target mark `*` (`Reverse.BindTargetsStar`); (b) every statement micro edge is mark-reversible (§1; `Backward.StmtsMarkRev`); (c) no FORWARD call binds the zero base back (`Backward.NoZeroBack`); the backward binding back has the reversed zero binding `zero.* → zero.*` (§9.2); (d) every instruction that is not a call keeps the zero fact: a statement that touches the zero base has the micro edge from the zero fact to the zero fact, no cleaner is on the zero base, and a type filter on the zero base accepts the empty path (`Backward.ZeroKept`); (e) for every method that is a root or the callee of a call, every node on a CFG path from the method entry has a CFG path to the method exit (the virtual exit of S4; `Backward.ExitReach`); (f) every sink pattern has the tail `$` or `[any]` (§4.9; for the seeds: `Kinds.SeedTails`); (g) every statement micro edge and every call binding has an EXACT SHAPE (§1; `Reverse.RevStmts`, `RevCalls`): a micro edge with a `*` premise and a `$` or `[any]` target has the Empty premise exclusion. Only the exactness of the reversed records (§8.7 R3) needs (g). | The interpreter (`interpreter.md` I11); for (e) the CFG normalisation (it wires the code that never returns to the exit). |
| S12 | The static construction rules (run 1, §4.10). A STATIC POSITION is the premise path of a statement micro edge on the static base `S`, or the path of a sink pattern on `S`, CUT to at most two accessors (the class and the field: `[<C>, f]`, `[<C>]`, Go `[<G>]`). So a path above a static position is the root path `[]` or a class `[<C>]`. (a) A statement micro edge from `S` to `S` is an identity restriction `S.q.* →_{E} S.q.*` (the keep edges of a write), or a FIELD-TO-FIELD edge: its premise path and its target path are both at or below a static field (a pass rule between static fields). (b) A statement micro edge from another base into `S` whose target path lies strictly above a static position has a `$` target and a `$` premise with a concrete mark: a mark on a class position, `zero.$ (zeroMark) → S.<C>.$ (T)` or `Q.$ (T') → S.<C>.$ (T)`. A conjunctive micro edge into such a target has a `$` premise with a concrete mark for each literal (`interpreter.md` §1.4, §5.3; the Lean `Statics.SWF.write` has single-premise edges only, so this clause is argued, §11.2). So no rule makes a `*` or an any-tail (`[any]`, `[any-taint]`) fact on a bare class position, and no pass rule reads or writes a bare class position. (c) A call binds `S` only by `S.* → S.*`, in both directions. (d) The class accessor is not counted, and `L ≥ 1`, so the field limit never cuts a path to a path above a static position. (e) A cleaner on `S` names its mark. (`RemoveAllMarks` on a position of `S`, at any depth, is not a cleaner: it is the kill of a strong write, `interpreter.md` §1.4.) One exception: the WHOLE-BASE CLEANER `(S, atAndBelow, all)` with the empty path (the JVM rule position `AnyClassStatic`, `interpreter.md` §1.4, I12 (e)). Every fact on `S` lies inside it, so it drops each fact whole and never cleans a fact in part (no `part` row and no request, §4.7). Its effect is that of a statement that touches `S` and has no micro edge on `S` (argued, §11.2). (f) `S` is not the zero base. (g) The abstraction of run 1 is the policy of §6.2. A rule position can be deeper than a static field: below the static field the ordinary rules apply. (Lean: `Statics.SWF`, its parts `ss`, `write`, `toC`, `fromC`, `cut`, `clean`, `base`, `alpha`; `PosIn`, `AbovePos`, `abovePos_len`.) A restricted run needs only (a) to (d), with its own field limit in (d) (`StaticsIter.SWFR`), and persisted records that keep the static invariant (§4.10). | The interpreter (`interpreter.md` I12). |
| S13 | Validity. The exactness and confirmation theorems read a VALIDITY predicate on locations (§4.8). Every type filter accepts every valid location of its base (`Exact.FiltValid`). The validity goes back along every statement micro edge and along every call binding, into the callee and back: a valid end location of the edge comes only from a valid start location (`Exact.BackOK`). With conjunctions, the validity also goes back from the target of a conjunctive micro edge to each literal: every location of a literal is valid if a location of the target is valid (`NDExact.ConjOK`). Without these conditions the valid forms are false (`Exact.CexFilt`, in the model: its program breaks W6; `NDExact.CexConjOK.cex_conjOK`). | The type-filter placement (`interpreter.md` §5.1). |
| S14 | Persisted records are exact: every pair of a persisted record whose end location is valid (S13) is a concrete flow (`RExact.RecsExact`; the valid form `RExact.RecsExactV`). The records of one forward run are exact if the records that the run reads are exact (run 1 reads none): run 1 (`RExact.recs_of_D`, `recs_of_D_valid`), a forward restricted run (`recs_of_DR`, `recs_of_DR_valid`); the union of two exact record sets is exact (`recs_union`). Over a run sequence in which every record is an exit edge of an earlier FORWARD run, the records stay exact (`BExact.recsSeq_exact`, `recsSeq_exactV`; `BExact.RecsFromRuns`). The reversed records of §8.7 R3 are proved only for a program without type filters (`Exact.FiltUp`) under S11 (c) and (g): a normal backward summary with a non-zero premise reverses into an exact forward record if the records that its backward run reads are exact (`BExact.rev_record_exact`, `revRecs_exact`), and an exact forward record reverses into an exact record of the reversed program (`Reverse.backward_reuse_precise`). The sequence in which each direction reads the reversed records of the other is argued (§11.2). So S14 is a theorem for the forward records of a program without conjunctions. It is not a theorem for a reversed backward record on a program with type filters, or for a record through an end fact (expected false-positive sources, §11.1), or for a one-member conjunction record (exact for the support semantics, `NDZeroThms.nd_edge_exact_z`; its reuse is argued, §11.2). A backward summary through the reversal of a conjunctive micro edge is in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION), so it is never a record. The soundness does not use S14: it needs the crossable records of §8.7 R5 to be PRESENT in the record sets, not to be exact (`HandoffBackward.NextRecs`, `HandoffMain.iteration_generalN`; with the earlier hand-off the record sets are free, `Backward.iteration_general`). With the `[any-taint]` tail and its exclusion (§2.3 W8) "exact" reads the ADMITTED locations: an exclusion `E` of an `[any-taint]/E` conclusion or of a must-premise removes locations. A record of an `[any-taint]` premise (a MUST RECORD, §1) is not exact pair by pair: it is END-EXACT (§1; `AnyTaintEx.RecsExactX`; `AnyTaintExact.CexApp.record_not_pair_exact`); its conclusion has a concrete mark (`AnyTaintExExact.RecsConcX`; necessary: `AnyTaintExact.CexRecConc.cex_rec_conc`); and every record conclusion is in the normal form of W8 (`AnyTaintExExact.RecsWFX`). The records of a forward restricted run are such (`AnyTaintExExact.recs_of_DRX_valid`, `recsConc_of_DRX`, `recsWF_of_DRX`; the records of run 1 are not must records, `liftRecsX_exact`, `liftRecsX_conc`, `liftRecsX_wf`), also over a run sequence in which every record is an exit edge of an earlier forward run (`AnyTaintExExact.recsSeq_exactX_valid`, `RecsFromRunsX`). | The record store (§8.7). It persists only the normal summary edges of the forward runs and the normal backward summary edges whose premise is not the zero fact (§8.7 R1). |
| S15 | The taint annotation (§2.3 W8). The interpreter gives the target tail `[any-taint]` only to a SOURCE micro edge with an `[any]` target (an unconditional or a conditional source, also a conjunctive one: `AssignMarkOnAnyAccessor`, Go `AnyAccessor`, `AssignMark` on an `AnyField` position; also an end-fact action on an `AnyField` position, `interpreter.md` I14, §4.1, END FACTS, and §4.9 here), with a concrete target mark and a concrete premise mark (`zeroMark` or the literal mark `T'`). Such an edge is a TAINT EDGE (§1). A pass rule with an `AnyField` target keeps the target `[any]` (a may). A pass rule with an `AnyField` position on its premise side is a rule error: the interpreter rejects the whole rule (`interpreter.md` D33). So no micro edge has the premise tail `[any-taint]`, and the only forward micro edge with an `[any]` premise is a source with an `[any]` literal (`ContainsMarkOnAnyField`). The backward run has no `[any-taint]` (W8 (d)): a seed of an `[any]` sink pattern and the reversed edge of an `[any]` literal give `[any]`, and the reversal of a micro edge whose FORWARD target is `[any]` gives every result in the demand layer (§9.1). The forward target tail tells the two kinds of micro edge apart; no other rule-kind flag is needed. (Lean: the parameter `AnyTaint.TaintEdges` of the runs; the forward part is `AnyTaint.TaintConc`, a hypothesis of the kinds invariant of run 1 only, `AnyTaintExKinds.D6X_any_conc`, `kinds_D6X`, and round 1 `AnyTaintSim.D6T_any_conc`, `kinds_D6T`; it is necessary, `AnyTaintSim.CexKinds.cex_taintConc`.) The soundness, the exactness and the confirmation theorems hold for every choice of the taint edges (the closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX` have the taint edges as a free parameter): the reference semantics reads every `[any]` target as every location (§3.5), and S15 keeps a may `[any]` out of the normal layer. | The interpreter (`interpreter.md` I14, D33). |

Inside this scope:

* Run 1 is SOUND: an edge covers every concrete flow (§3.5), and the run reports every real vulnerability (§10.1).
* THE SCOPE OF THE ITEMS BELOW (F72). Each claim below about a later run (a restricted run, forward or backward) and
  about the iteration is PROVED FOR THE CONCRETE RESTRICTED RUNS of F70 and F71, in which every fact has a concrete
  mark. Since F72 a restricted run can have FLOW premises, `*` facts and no request rules (§4.5, §6.3). For these
  rules the claims are the claim R6 of F72 (§6.6, CONTRACT B WITH MODES), and their proof is PENDING (§11.2). Run 1
  and its theorems do not change.
* A later run is SOUND RELATIVE TO ITS DEMAND AND ITS RECORDS: it reports every real vulnerability whose witness the
  demand and the records cover (at each call that returns, a demand pattern or a crossable record, §1), and it
  justifies the same witness, which the backward run after it passes on to the next forward run as demand patterns and
  records (§6.6; `Handoff.coversN_DR`, §10.12).
* The backward run of §9.2, with the hand-off of the DEMAND EDGES only (§9.2) and the sink seeds of the DEMAND
  vulnerabilities, satisfies contract B (§6.6; `HandoffBackward.B_generalN`). So at EVERY COMPLETE FORWARD run, every
  real vulnerability is REPORTED by that run or was CONFIRMED by an earlier complete forward run
  (`HandoffMain.iteration_generalN`; if every reported vulnerability is seeded, every complete forward run reports it,
  `HandoffMain.iteration_generalN_all`). A run reports it in some layer: CONFIRMED or DEMAND (§4.9). The CONFIRMED
  state is final, and the report holds every confirmed vulnerability and the DEMAND entries of the latest complete
  forward run; the output holds every entry of the report (§8.10; `ap-history.md` F68). So the analysis can stop at any
  complete forward run (§6.6), also for the output, and a vulnerability that a complete forward run does not report and
  that no earlier complete forward run confirmed is not real. (The earlier hand-off of every summary edge, with every
  reported vulnerability seeded, has the same theorem: `Backward.B_general`, `Backward.iteration_general`; for any
  backward step that satisfies its contract B, `Backward.iteration_sound_M_D`. These theorems stay in the model as the
  record of the earlier design, §10.7; `ap-history.md` F70.)
* Inside the smaller scope of NORMAL edges the analysis is also EXACT. An end location is VALID if every type filter
  accepts it (S13); real values have only valid locations. Every pair of a normal edge whose end location is valid is a
  concrete flow: in run 1 under S7 and S13 (`Exact.edge_exact_valid`), in a restricted run also under S14
  (`RExact.edge_exactR_valid`; §10.3, §10.7). With the `[any-taint]` tail and its exclusion (W8) the pairs are those
  of the ADMITTED locations (an exclusion `E` removes locations, §3.2). Then this holds for every normal edge of run 1,
  also an edge with the `[any-taint]/E` tail, under S7 and S13 (`AnyTaintExExact.edge_exact_valid6X`), and for every
  normal edge of a forward restricted run whose premise does not have the `[any-taint]` tail. A normal edge of an
  `[any-taint]` premise (a must-premise, §1) is END-EXACT: every valid admitted location of its conclusion is reached
  from some valid admitted location of the premise. Both restricted forms are `AnyTaintExExact.edge_exactX_valid`,
  under S7, S13, the records of S14 (`AnyTaintEx.RecsExactX`, `AnyTaintExExact.RecsConcX`, `RecsWFX`) and three
  properties of the rules of §4.3, §6.3 and §6.4 (`AnyTaintEx.SatInsideX`, `EmitCopiesMarkX`,
  `AnyTaintExExact.RestrictOKX`), which the spec rules have (`AnyTaintEx.satX_inside`, `emitX_copies`,
  `HandoffX.restrictIX_ok`; with the earlier restriction `AnyTaintExExact.specX_rules`; §10.11, §10.12).
* Exactness is against the path-insensitive reference semantics (§3.5). A conjunction (§4.6) and a rule condition that
  one fact does not decide (§4.2) are expected over-approximations. They do not move an edge to the demand layer. A
  normal edge with conjunctions is exact against the support semantics `ND.TaintN`, under S7, S9, S10 and S13
  (`NDExact.nd_edge_exact`; the valid form `nd_edge_exact_valid`; for the spec closure `NDZ.DNz`:
  `NDZeroThms.nd_edge_exact_z`, `nd_edge_exact_valid_z`, also under S11 (d), `NDZero.ZeroCalls` and `ConjAdj`).
* A CONFIRMED vulnerability (§4.9) whose sink pattern covers only valid locations is real for the reference semantics
  (§3.5), modulo the expected false-positive sources of §11.1. In run 1 this holds under S7, S10 and S13
  (`Confirmed.confirmed_real_valid`), in a restricted run also under S14 (`RExact.confirmed_realM_gen_valid`, for every
  restriction that only removes pairs: the restriction of §6.4 by `Handoff.restrictI_sub`; the instance with the
  earlier restriction `restrictU` is `RMain.confirmed_real_M_valid`). For a program without type filters the same holds
  with no validity condition (`Confirmed.confirmed_real`, `RExact.confirmed_realM_gen`, `RMain.confirmed_real_M`).
  These theorems are for programs without conjunctions and without the static rule.
* WITH THE `[any-taint]` TAIL (§2.3 W8; §10.11). The rules of this spec are the closures `AnyTaintEx.D6X` (run 1 with
  the rule W6T: only the result of a may `[any]` target goes to the demand layer; an `[any-taint]` conclusion carries
  its exclusion `E`) and `AnyTaintEx.DRX` with the spec rules of §4.3, §6.3 and §6.4: `emitX`, `satX` and the
  intersection `HandoffX.restrictIX` (a forward restricted run with must-premises and the exclusion). (The closure
  `AnyTaintEx.DRXs` is `AnyTaintEx.DRX` with the earlier restriction `AnyTaintEx.restrictX`, §6.4.) The backward run is
  `Backward.DB`: it has no `[any-taint]` (W8 (d)). The soundness above holds, with the hand-off of the demand edges read
  from the refined runs without their exclusions (§9.2): at every complete forward run, every real vulnerability is
  reported by that run, in some layer, or was confirmed by an earlier complete forward run
  (`HandoffXIter.iteration_generalNX`, under the hypotheses of `HandoffMain.iteration_generalN`; with every reported
  vulnerability seeded `HandoffXIter.iteration_generalNX_all`, and for a driver that hands off more
  `iteration_reportsNX`; with the source seeds `HandoffSrc.iteration_srcNX`; for a sequence that stops after forward
  run `K` `HandoffUpto.iteration_generalNX_upto`). For the pipeline driver with the seeds of §6.6 (the DEMAND entries
  only, and `C k` = confirmed by a complete forward run up to `k`, §4.9) this is
  `PipelineHandoffDriverExt.driver_iterationNX_demand`, for a driver that stops after forward run `K`
  `PipelineHandoffDriverExt.driver_iterationNX_upto`, and with the source seeds `driver_iteration_srcNX`; with every
  reported vulnerability seeded it is `PipelineHandoffDriver.driver_iterationNX` (§6.6, §10.12). Each refined run gives
  the witnesses of its own summaries: run 1 (`AnyTaintExCov.vuln_found6X`, `reach_strong6X`, with C1 from
  `policy_applicable`; the report alone: `AnyTaintExCov.vuln_found_policy6X`; the justified witness
  `HandoffX.run0X_contract`) and a forward restricted run (`HandoffX.coversN_DRXI`), under S10 only.
  (The earlier hand-off with `AnyTaintEx.restrictX`: `AnyTaintExCov.iteration_reportsX`, with the source seeds
  `AnyTaintExCov.iteration_srcX`, for the driver `PipelineAnyTaintExDriver.driver_iterationX`, `driver_iteration_srcX`,
  and the restricted run `AnyTaintExCov.vuln_foundRXs`; §10.11. The proofs do not go through the round-1 closures
  `AnyTaint.D6T`, `AnyTaint.DRT`: the exclusion removes summaries, so the hand-off of a refined run can be smaller,
  `AnyTaintExCov.CexRoute.route_a_false`.) A
  vulnerability whose taint comes from an `[any]`-target source (the `[any-taint]` tail, S15) can be CONFIRMED (§4.9):
  in run 1 when the sink reads the tainted object in the method of the source, also after a setter of one field
  (program S, `AnyTaintExCases.S.run1_email_confirmed`), or after a callee whose FLOW summary keeps the whole object
  (§6.2; the sink in the method of the source: `AnyTaintExCases2.PassRule.source_confirmed`; the callee: program I,
  `AnyTaintExCases2.I.run1_confirmed`); in a restricted run also through a callee (a getter, program G:
  `AnyTaintExCases2.G.run3_confirmed`, `run3_confirmed_handoff`; a sink in the callee, program C:
  `AnyTaintExCases2.C.run3_confirmed`, through the must branch of `AnyTaintEx.SupLinkX`,
  `AnyTaintExCases2.C.run3_supported`; the round-1 programs re-derived in the refined closures;
  `AnyTaintExCases.B.run3_anyE_confirmed`). These restricted runs use the earlier restriction `AnyTaintEx.restrictX`
  and the earlier hand-off; with the intersection and the hand-off of the demand edges the same results are checked by
  hand (§11.2). A confirmed vulnerability is real: in run 1 under S7 and S13
  (`AnyTaintExExact.confirmed_real_valid6X`); in a forward restricted run also under the records of S14 and the rules
  of §4.3, §6.3 and §6.4 (`AnyTaintExExact.confirmed_realX_valid`; the restriction of §6.4 has the property
  `AnyTaintExExact.RestrictOKX` that it needs, `HandoffX.restrictIX_ok`; the instance with the earlier
  restriction `AnyTaintEx.restrictX`: `AnyTaintExExact.confirmed_realXs`); over the run
  sequence when every record is an exit edge of an earlier forward run of the same program
  (`AnyTaintExExact.RecsFromRunsX`), with no exactness hypothesis on the records (`seq_confirmed_realX_valid`); with
  the reversed backward records and with the source seeds this is argued (§8.7 R4, §11.2). With conjunctions:
  `AnyTaintND.confirmed_real_NzT_valid`, under the hypotheses of `NDZeroThms.confirmed_real_Nz_valid`, for run 1 with
  the conjunction rule of §4.6 (`AnyTaintND.DNzT` has no W6T and no exclusion: both are argued, §11.2). Only a MAY
  `[any]` (the target of a pass rule) and the other demotions of §2.2 stay in the demand layer, and a vulnerability
  that rests on them stays a DEMAND entry (§8.10).
* With conjunctions, a vulnerability that run 1 confirms with the joint support of §4.9 is real for the support
  semantics, under S7, S9, S10 and S13 (`NDConfirmed.confirmed_real_N`; the valid form `confirmed_real_N_valid`;
  for `NDZ.DNz`: `NDZeroThms.confirmed_real_Nz`, `confirmed_real_Nz_valid`, also under S11 (d), `NDZero.ZeroCalls` and
  `ConjAdj`).
* With the static rule of §4.10, a vulnerability that run 1 confirms is real, under S7 and S13 (`StaticsConfirmed.confirmed_realS`;
  the valid form `confirmed_realS_valid`).

---

## 1. Terms

| Term | Meaning |
|---|---|
| base | A local, an argument, `this`, the return value (`ret`), the exception, a constant, the static base `S` (`ClassStatic`), or the zero base. |
| static base `S` | The base that holds every static field (JVM) and every global (Go) at a static path (§4.10). |
| accessor | A field, an array element, or a class accessor `<C>`. Not a mark, not `[any]` or `[any-taint]`, not `$`, not a type-info or value accessor (the prescan only, W5). The set of accessors is unbounded: for each finite set of accessors there is an accessor outside it. So a `*/E` tail always admits a continuation other than `[]`, and `*/E` is never `$`. |
| counted accessor | A field or an element accessor. The field limit counts only these. |
| path | A finite list of accessors. |
| chain | The base and the concrete path of a fact or of a pattern, without its tail and its mark. |
| location | A concrete triple (base, path, mark): the value at `base.path` carries `mark`. |
| zero location | The location `(zero, [], zeroMark)`: the one location of the zero fact (§2.4). |
| tail | The end of a fact path: `*` (abstract), `[any]` (any continuation, a MAY), `[any-taint]` (every admitted continuation, a MUST; forward runs only), or `$` (exact). |
| any tail | The tail `[any]` or the tail `[any-taint]`. With the Empty exclusion both have the same location set (§3.1); the layer, the exclusion and the meaning differ (§2.3 W6, W8). |
| `[any-taint]` | The MUST any tail of a FORWARD run (§2.3 W8). A normal edge `i → (x, p, [any-taint], E, T)` says: EVERY location `(x, p ++ τ, T)` with `τ` admitted by `E` carries the taint. The EXCLUSION `E` of an `[any-taint]` fact (written `[any-taint]/E`; `[any-taint]` alone has `E = {}`) is a finite set of first accessors: an accessor of `E` is not the first accessor after `p`, so `E` removes locations (§3.1). A forward conclusion `[any]` says: some locations below `x.p` MAY carry it (an over-approximation); it never has an exclusion. `[any-taint]` has a concrete mark only. The backward run has no `[any-taint]` (W8 (d)). Lean (§11.2): the model tail `.any` in the normal layer, with the exclusion `ex` of `AnyTaintEx.XFact`. |
| taint edge | A source micro edge with an `[any]` target (S15). Its target is `[any-taint]` with the Empty exclusion. Lean: `AnyTaint.TaintEdges`. |
| must-premise, must record | An initial fact with the `[any-taint]` tail (a MUST-PREMISE), with its exclusion: its edges hold when EVERY admitted location of the premise carries its mark, as if a source fired at the method entry. It occurs only in a forward restricted run (§6.5). A MUST RECORD is a record of a must-premise (§8.7). Lean: the flag `must` of `AnyTaint.TObj` and of `AnyTaintEx.XObj` (with the premise exclusion `jex`). |
| end-exact | A property of a normal edge of a must-premise: every admitted end location of the edge comes from SOME admitted location of the premise (Lean: `AnyTaint.EndExact`; with the exclusions `AnyTaintEx.EndExactX`). It is weaker than exact (2): the start fact of a must-premise relates every premise continuation to every conclusion continuation, so its pairs are not all concrete flows (`AnyTaintExact.CexApp.record_not_pair_exact`). |
| exclusion | A finite set of first accessors that a `*` continuation, or the continuation of an `[any-taint]` fact, must not start with. |
| Universe | The exclusion of every accessor. A `*/Universe` tail admits only the empty continuation `[]`. The AP has no `*/Universe` fact, edge or initial fact (S8). The model keeps it only to encode a `$` premise (§11.2). |
| tail kind | The tail with its exclusion: `*/E`, `[any]`, `[any-taint]/E` or `$` (Lean: `Kind`; the model has one kind `.any` for both any tails, and the exclusion of `[any-taint]/E` is the field `ex` of `AnyTaintEx.XFact`, §11.2). For a fact `i` it is written `i.kind`. |
| conclusion kind | REACH, FLOW or TAINT: the kind of the conclusions of one edge group (§7.2). The word KIND alone means the conclusion kind. |
| mark | `*` (abstract: the mark of the premise passes), `T` (concrete), or `*∖X` (abstract except the marks of `X`; conclusions only). The set of marks is unbounded, so two abstract marks always have a common mark. |
| zero mark | The concrete mark of the zero fact (Lean: `zeroMark`). No rule names it. |
| effective mark | The mark that a sink reads on an edge `i → f`: `f.mark` if it is concrete, else `i.mark` if it is concrete, else abstract (§4.9). |
| fact | A tuple (base, path, tail, exclusion, mark). §2. |
| premise | An initial fact of an edge: a fact that the edge depends on, at the method entry (forward run) or at the method exit (backward run). Every edge has a PREMISE SET. The zero fact is a premise like every other initial fact: a zero-to-fact edge has the premise set `{zero}` (§2.4). |
| conclusion | The final fact of an edge: the fact at a statement. |
| edge | (premise set, layer, statement, conclusion), with one exclusion. §4.6 names the edge by the number of its premises that are not the zero fact: none, a ZERO-TO-FACT edge (the premise set `{zero}`); one, a FACT-TO-FACT edge (the premise set `{i}`); two or more, an ND edge. A premise set with two or more members never contains the zero fact (§4.6). |
| propagation edge | An edge that the analysis derives and propagates inside a method. Not a micro edge. |
| caller edge | The propagation edge `(i, layer) → c` of the caller at a call statement (`i` is its premise set). The call binds its conclusion `c` into the callee (§5.3). |
| caller fact | The conclusion `c` of a caller edge, in caller coordinates. After a binding edge it is a bound fact, and after the cleaners an added fact. A summary edge of the callee applies to the added fact, not to the caller fact (§4.3). |
| layer | `normal` or `demand`. |
| normal edge | An edge in the normal layer, also called a COMPLETE edge: in a forward run also an edge with the `[any-taint]` tail; the backward run has no `[any-taint]` (§2.3 W8). Lean: the normal layer (`demand = false`); the predicate `AFact.complete` also excludes a normal `.any` conclusion, so it is the reading of the backward run only (§11.2). Only a normal summary edge can become a record. |
| demand-layer edge | An edge in the demand layer. The analysis uses it in its own run like every edge. It never persists it and never reverses it. |
| exact | (1) The `$` tail. (2) A property of an edge or a record: every pair of it is a concrete flow (no false pair). (The cleaner reach `exact` of §4.7 is a third, local meaning.) |
| mark-reversible | An edge `i → f` is mark-reversible if `f.mark` is abstract (`*` or `*∖X`), or if `i.mark` is concrete (§9.1; Lean: `Reverse.MarkRev`). |
| exact shape | An edge has an exact shape unless it is `*/E → $` or `*/E →` an any tail, with a premise exclusion `E ≠ {}` (§9.1; Lean: `Reverse.ExactShape`). |
| touched base | A base that a statement or a call can change. A fact on an untouched base passes the statement unchanged. A fact on a touched base keeps only what a micro edge gives (§4.2). |
| statement summary | What the interpreter gives for one statement: the touched bases, the micro edges and the type filters (`interpreter.md` I1). Not a summary edge. |
| micro edge | One edge of a statement summary, or one call binding edge, that the interpreter makes. A callee summary edge is NOT a micro edge (§4.3). |
| summary edge | An edge whose statement is the method exit (forward run) or the method entry (backward run). |
| record | A complete summary edge with one premise that the analysis persists for later runs (§8.7 R1). A crossable leaf of a record (below) replaces the analysis of its callee in the later runs (§8.7 R5). |
| summary rewriter | A rule-guided override of the callee flow at a call (§4.7; `interpreter.md` §5.2): for the selected user-defined rules of the call, it cleans their marks at their positions on the summary results and the unresolved results. Not a summary edge, and not a cleaner placement. |
| bound fact | A caller fact after a binding edge into the callee, in callee coordinates. The sinks of the call check it (`interpreter.md` §4.5 step 3). |
| added fact | A bound fact after the cleaners of the call (`interpreter.md` §4.5 step 5.1). The callee gets it. |
| link | One (added fact, caller edge) pair in the added fact store of the callee (§8.3). A standing request checks every link (§4.5, §4.10). |
| abstraction, emission | The function that selects the initial facts for an added fact. §6. |
| policy, policy fact | The run-1 abstraction (§6.2; Lean: `policy1`). A policy fact is an initial fact that it gives: `(x, [], *, {}, *)` for an added fact on the base `x`. In this spec the word "policy" alone always means this abstraction. The MARK POLICY of the interpreter is a different rule: it drops a concrete mark on a primitive value (`interpreter.md` §5.1). |
| request | Run 1 only (also since F72: a restricted run has no request rule, §4.5). A MARK request asks for a concrete mark on an initial fact (§4.5). A POSITION request asks for a static position: it comes from a statement micro edge whose premise lies strictly below an identity static `*` edge at the root path `[]` or at a class `[<C>]`, and it asks for that premise path cut to at most two accessors (§4.10). |
| chain answer, request chain | The REQUEST CHAIN is the base and the path of the premise of a mark request. The CHAIN ANSWER `answer(i, a, T)` is the answer of §4.5 at the request chain (Lean: `answerInit`). |
| static position | The premise path of a statement micro edge on `S`, or the path of a sink pattern on `S`, cut to at most two accessors: a static field `[<C>, f]` or a class `[<C>]` (S12). |
| standing | A standing request, subscription or conjunction fact stays active until the end of its run: it also acts on every matching event that comes later. |
| root | An entry method of the analysis (a ROOT METHOD). Every run starts with the zero fact as an initial fact of each root (Lean: `roots`). Not the same as the ROOT PATH: the empty path `[]` of a base. "At the root `[]`" and "the static root" (the position `(S, [])`) name the root path. |
| run | One analysis pass in one direction with one field limit `L`. The runs are numbered in order: run 1 (forward), run 2 (backward), run 3 (forward), and so on (§6.6). |
| complete run, incomplete run | A run is COMPLETE if it reached the fixed point of its rules (S6): it ended at quiescence. A run that a timeout, its memory guard or an exception ends is INCOMPLETE. An exception is every `Throwable` of the run, a JVM `Error` too (the status FAILED; the status OOM comes only from a memory guard). The status is set before every cancel, so every cancel has a known cause: the timeout, a memory guard (of a run or of the barrier), or a runner failure (`analyzer-core.md` §6.3). |
| restricted run | Every run after run 1, forward or backward. It strictly follows its demand (§6.1). Since F72 it analyses with the mark `*` under a `*` demand pattern and with a concrete mark under a concrete demand pattern (§6.3), and it has no request rule (§4.5). |
| demand pattern | A pair of patterns that a restricted run gets from the run before it, in the orientation of the restricted run: the entry pattern `D-c` and the exit pattern `D-p` (or none, if the demand does not reach the method exit). Lean: `DemandEdge` (`din`, `dout`). The letters come from the run that made the pattern: `D-c` is a CONCLUSION of that run, and `D-p` is a PREMISE of that run (§9.2). |
| demand (of a run) | The set of demand patterns that a restricted run gets (§9.2 states the hand-off; §8.6 stores it). Not the same as the demand layer. |
| demand edge (of a run) | A PUBLISHED summary piece of a run (§8.5: an edge of run 1 as it is, or a result of the restriction of §6.4 in a later run) that the next run in the other direction cannot reuse as a record: a piece of a summary leaf that is not crossable (below). Each demand edge of a run gives the next run one demand pattern per member of its premise set (§9.2): forward to backward `(D-c = g', D-p = j)`, backward to forward `(D-c = gb', D-p = jb)`. The run stores its demand edges at each summary delta (§8.5). A crossable leaf is never a demand edge. Not the same as a demand-layer edge: a normal leaf that is not crossable gives demand edges too, and every leaf of a demand-layer edge does. Not the same as the Lean structure `DemandEdge`, which is a demand pattern. Lean: `Handoff.handF`, `Handoff.demOfN` (`ap-history.md` F70). |
| crossable | A summary leaf `j → g` (one premise, one conclusion leaf) is CROSSABLE if (1) it is normal; (2) its premise `j` has the tail `$` or `*` with the Empty exclusion (not an any tail, so not a must-premise); (3) it is mark-reversible; and (4) its reversal (§9.1) has a premise with the tail `$` or `*` with the Empty exclusion, so `g` has no any tail (no `[any]` and no `[any-taint]` leaf, with or without an exclusion). A backward leaf is crossable if it is normal and its reversal is a crossable forward leaf (Lean `Handoff.CrossB`; a demand-layer backward leaf is never a record, §8.7 R1). The record of a crossable leaf applies to EVERY concrete added fact (forward) or requirement (backward) that has a common location with its premise, by `inside` or by `applicable` (§4.3). Since F72 an added fact or a requirement can have an abstract mark (§6.3): the record of a crossable leaf with a `*` premise applies to it too, and the record of a concrete premise does not (its mark is not a subset of the premise mark: no request, §4.5). Its reversal is exact (§9.1; `Reverse.rev_exact_of_empty_premise`: the converse pairs; as a record, S14). So the next run of each direction crosses it by the record (§8.7 R4) or by its reversal (R3), with no analysis of the callee (R5). The leaves of a summary with several premises and the zero-premise backward leaves are never crossable (they are never records, R1). A backward leaf through the reversal of a conjunctive micro edge is never crossable: it is in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION). Lean: `Handoff.Cross`, `CrossK`, `revRec`; `Handoff.cross_applies`. |
| demanded flow, demanded witness | A concrete flow is DEMANDED if at every call in it that returns, ONE demand pattern of the callee has a `D-c` that covers the entry location of the callee WITH ITS MARK, and a `D-p` that covers the exit location WITH ITS MARK (the restriction tests the marks, §6.4; `ap-history.md` F71). A witness is DEMANDED if its flows are demanded and, at every call down, one demand pattern of the callee has a `D-c` that covers the entry location with its mark (§6.6). A flow or a witness is DEMANDED OR RECORDED if at every call in it that returns, the call is demanded as above, or a crossable record of the callee (§8.7 R5) has a premise that covers the entry location and has the pair of the entry location and the exit location (Lean: `Handoff.FlowRR`, `Handoff.ReachRR`; the demanded call of `FlowRR` has `p.covers l2`, the exit location with its mark; §6.6). The backward run gives this witness: its emitted premise covers the exit location with its mark (§6.6, contract B). The earlier model `FlowR`, `ReachR` (§10.7, with the earlier restriction `restrictU`, which ignores the marks) reads the `D-p` part as a location only (`PFact.coversLoc`). Since F72 a demanded call also has a MODE: ABSTRACT if a `*` pattern demands it, CONCRETE if a concrete pattern demands it (§6.6, CONTRACT B WITH MODES; PENDING, §11.2). |
| frontier | The method keys with a non-zero initial fact in a run, and the demand edges that the run hands off per method key. The FRONTIER LOG of the iteration driver adds, after each complete run, the counts of `analyzer-core.md` §7.8: the crossable summary leaves, the record crossings, for a forward run its DEMAND and CONFIRMED vulnerabilities and the seeds, and the work of the zero fact. The demand patterns with an exit pattern only shrink, in their locations and their marks (§6.6, THE NARROWING); the zero demand and the patterns of the seed paths are not narrowed. |
| vulnerability | A vulnerability key `(rule, method, statement)` with its sink witnesses (§8.10). |
| demand vulnerability of a run | A vulnerability that a run reports with no confirmed sink witness in that run (§4.9). Not the same as a demand-layer edge, and not the same as a DEMAND vulnerability (below). |
| DEMAND vulnerability, DEMAND entry | A vulnerability whose state in the REPORT is DEMAND after a complete forward run: the latest complete forward run reports it, and no complete forward run so far confirmed it (§8.10; `analyzer-core.md` §1). A key that an earlier run confirmed is CONFIRMED, also when a later run reports it only as a demand vulnerability of that run. The seeds and the stop rule `STOP_RULE` read this state (§6.6). |
| concrete flow | A chain of concrete steps (§3.5; Lean: `Flow`). |
| witness | The concrete flow of a vulnerability: from the zero location of a root, through a chain of calls down, to a location that the sink pattern covers (§3.5; Lean: `Reach`). |
| sink alternative | One alternative of the sink condition of a rule at a statement: one disjunct of the condition (a conjunction of literals), with one choice of the array-element patterns (`interpreter.md` §4.2). The interpreter numbers the alternatives of a rule at a statement. The number is the same in every run and in every context (`interpreter.md` I5). |
| sink witness | One sink edge, or one sink edge set of a conjunctive sink (§4.9), of one sink alternative in one method key, in one run (Kotlin: `SinkWitness`). The vulnerability store keeps it (§8.10). Not the same as a witness. |
| reference semantics, real | The concrete semantics of §3.5, with the rules read as §3.5 says. A flow or a vulnerability is REAL if it exists in the reference semantics. |
| support, supported | A property of a PREMISE SET, not of one premise. A premise set is SUPPORTED if one call statement supplies every premise of it exactly, through normal caller edges whose own premise sets are supported, down from the zero fact of a root. The support is a tree (§4.9 condition 3; Lean: `Confirmed.Sup`, `RExact.SupM`, `NDConfirmed.SupN`). |
| strong enough | A fact `a` is strong enough for a premise `j` if `applicable(j, a)` (§4.3): `j` covers `a`, and a premise with an any tail needs a fact with an any tail. Such a fact is at or below the premise (§4.1 case `below`). |
| not strong enough | The fact is not strong enough. A fact above the premise (§4.1 case `above`) is never strong enough: the result loses the correlation. |
| satisfies | A fact satisfies a premise if the caller may apply the summary edges of that premise to it: `applicable` in run 1, `inside` in a restricted run (§4.3). Since F72 a FLOW premise of a restricted run is also satisfied by `applicable` (§4.3). A must-premise needs `inside` (§4.3). |
| concrete run | A run in which every fact has a concrete mark. Before F72 every restricted run was concrete: a forward one (§6.3) and a backward one, whose seeds have concrete marks (`RExact.DR_concrete`, `BExact.DB_concrete`, for the emission `emitM` that copies the mark of the added fact). SINCE F72 A RESTRICTED RUN IS NOT CONCRETE: a `*` demand pattern gives a FLOW premise (§6.3), and its facts have abstract marks (`ap-history.md` F35, F72). |
| FLOW form, FLOW premise | The FLOW FORM of a demand entry pattern `D-c = (b, p, t, *)` with the mark `*` is the fact `(b, p, flowK(t), *)`, with `flowK(*/E) = */E`, `flowK([any]) = */{}` and `flowK($) = $`: the WEAKEST fact inside `D-c` (§6.3; F72; Lean, PENDING: `flowForm`, `flowK`). A FLOW PREMISE is an initial fact with the mark `*`: in run 1 a policy fact or a position answer, in a restricted run the FLOW form of a `*` pattern. Its edges are FLOW (§7.2), and its start fact is the identity, in the normal layer (§6.5). |
| sharing | One initial fact serves every added fact under one demand pattern, with every mark. A `*` pattern shares: its FLOW premise does not depend on the added fact (§6.3, F72). A concrete pattern does not share: one initial fact per distinct added fact (path, tail, mark). Before F72 no pattern shared (`ap-history.md` F35, F72). |
| ND edge | A NON-DISTRIBUTIVE edge: an edge whose premise set has two or more premises that are not the zero fact. A conjunction makes it (§4.6). |
| prescan | A pass of the current analyzer core that runs before the new analysis. It resolves the lambdas and the closures and gives their type info (§7.6, `interpreter.md` §3.9). The new AP only reads its result. |
| method key | `MethodEntryPoint` (context plus entry statement), as today (Kotlin: `MethodKey`). The method key of a method is the same in every run. |

NOTATION. `ap.md` and `interpreter.md` use these forms. The interpreter-only forms are in `interpreter.md` §0.

| Form | Meaning |
|---|---|
| `(x, p, t, E, m)` | A fact or a pattern: the base `x`, the path `p`, the tail `t`, the exclusion `E`, the mark `m` (§2.1). |
| `(x, p, t, m)` | The same. The exclusion is Empty, or the tail kind `t = */E` or `t = [any-taint]/E` carries it. |
| `(x, p, t)` | A pattern whose mark is not relevant (for example a pattern read as locations, §3.2). |
| `.`, `[]`, `.f.g`, `[f, g]` | A path. `.` and `[]` are the empty path. `.f.g` and `[f, g]` are the path of the accessors `f` and `g`. |
| `p ++ r`, `p·r` | The path `p` followed by the path `r`. |
| `x.p.*` | A micro-edge side or a fact `(x, p, *, {}, *)`: the `*` tail with the mark `*`. |
| `x.p.$ (T)`, `x.p.[any] (T)`, `x.p.[any-taint] (T)` | The tail `$`, `[any]` or `[any-taint]` (with the Empty exclusion) with the concrete mark `T`. Without `(T)` the mark is `*` (never for `[any-taint]`, W8). |
| `i → f` | An edge with the premise `i` and the conclusion `f`. `j → g` is a summary edge. `{j1, …, jk} → g` is an ND edge. |
| `a →_{f} b`, `i →_{E} f` | A micro edge or an edge with the exclusion `{f}` or `E`. With no subscript the exclusion is Empty. |
| `Zero → (layer, statement, fact)`, `Zero → (statement, fact)` | A zero-to-fact edge: an edge with the premise set `{zero}`. In the second form the text names the layer. |
| `[e]`, `<C>`, `<G>` | The element accessor; the class accessor of the class `C`; the accessor of the Go global `G`. |
| `S`, `zero`, `ret`, `this`, `argi` or `arg(i)` | The static base, the zero base, the return value, the receiver, the argument `i`. |
| `{x, y}` | The touched bases of a statement. |
| `*∖X` | The abstract mark except the marks of the set `X` (§2.2). |
| `(m, i, T)`, `(m, i, p)` | A mark request for the mark `T`, and a position request for the path `p`, on the premise `i` in the method `m` (§4.5, §4.10). |
| §4.2; `interpreter.md` §2.1 | A section of this spec; a section of `interpreter.md`. A list of sections after `interpreter.md` (for example `interpreter.md` §4.4, §4.7) is a list of sections of `interpreter.md`. |

---

## 2. The fact and the edge (the concept)

### 2.1 The tuple

A fact is `(base, path, tail, exclusion, mark)`:

* `path` — the concrete accessors. It never contains `[any]`, `[any-taint]`, a mark or `$`.
* `tail ∈ {*, [any], [any-taint], $}`. The `[any-taint]` tail has a concrete mark, and it occurs only in a forward
  run (W8).
* `exclusion` — a finite set of accessors, only with the `*` tail or the `[any-taint]` tail (W8).
* `mark ∈ {*, T}` for a premise; `mark ∈ {*, T, *∖X}` for a conclusion.

### 2.2 Edges, layers, the edge exclusion and the mark exclusion

An edge is `(premise set, layer) → (statement, conclusion)`. A fact-to-fact edge is also written
`(premise, layer) → (statement, conclusion)`. The zero-to-fact edge is `Zero → (layer, statement, fact)`: its premise
set is `{zero}`. An ND edge is `({premise1, …, premisek}, layer) → (statement, conclusion)` with `k ≥ 2` premises that
are not the zero fact (§4.6).

* An edge has ONE exclusion `E`. In a CORRELATED edge (`*` premise, `*` conclusion) the premise and the conclusion
  share it: for `(x, p, *) →_E (y, q, *)`, the value at `x.p.σ` flows to `y.q.σ` for every `σ` that `E` admits. The
  model stores `E` on the conclusion (the tail kind `*/E` of the target). If the premise also stores an exclusion, the
  edge exclusion is the union of the two (`SharedExcl.applyEdge_shared_excl`, `den_shared_excl`). An implementation
  stores `E` once, on the edge.
* An UNCORRELATED edge (the conclusion is `$` or has an any tail) has no shared exclusion. Its conclusion has the
  Empty exclusion, except an `[any-taint]/E` conclusion (W8): there `E` restricts the continuation of the conclusion
  only (§3.1). Every operation of §4 gives an uncorrelated result the Empty exclusion, except the rows of §4.1, §4.7
  and §6.3 that give an `[any-taint]` result its exclusion; if the result loses a restriction, it goes to the demand
  layer instead (`lostCorr`, §4.1). A `*/E` premise of an uncorrelated edge (before F72 a restricted run could emit
  one with a concrete mark, §6.3) keeps `E` in its premise: `E` restricts the premise continuation only. The
  exclusion of a must-premise (§6.3) does the same.
* The MARK EXCLUSION `X` of a conclusion `*∖X` stops the marks of `X`: the value at the premise location flows to the
  conclusion location only if its mark is not in `X`. It belongs to the edge, as the exclusion does; a cleaner makes it
  (§4.7). A premise never has one.
* The policy facts and the chain answers of run 1 have the Empty exclusion (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`). A position answer `(S, p, *, {}, *)` has the Empty exclusion by its definition
  (§4.10 item 2). The mark answer on a static premise is the added fact itself (§4.10 item 4). It has a concrete
  mark, so by W2 it has the `$` or the `[any]` tail and the Empty exclusion (an `[any-taint]/E` added fact gives the
  `[any]` answer, with no exclusion: W8 (c)). (The Lean theorems above do not cover these two static answers; the
  statements follow from their definitions.) In a restricted run an emitted fact can have the exclusion of the demand.
  Before F72 it was the meet with a `*/E` entry pattern (§6.3), with a concrete mark, so it started in the demand
  layer (§6.5) and made no record. Since F72 a `*/E` entry pattern has the mark `*` (W2), so it gives its FLOW form
  `(x, p, */E, *)` (§6.3): it starts with the identity in the normal layer (§6.5), as a policy fact does, and its
  exclusion is the shared exclusion of its correlated edges (above). (In the spec runs no demand pattern has the tail
  `*/E`: every `*` pattern has the entry tail `[any]`, and its FLOW form `*/{}` has the Empty exclusion, §6.3.) A
  must-premise of a forward restricted run can
  have the exclusion of its `[any-taint]/E` added fact (§6.3); it starts in the normal layer with it (§6.5). So the
  exclusion of a normal edge is a property of its conclusion (and of a must-premise). Only a strong field write makes
  it larger (by its keep edge, or through a `*/E` summary or record), and, on an `[any-taint]` fact, a cleaner one
  accessor below it (§4.7).
* The LAYER is part of the edge identity. A micro edge has no layer (§4.2): the layer belongs to the propagation edge.
  Only these AP operations put a propagation edge in the demand layer:
  * the start fact of an initial fact with the `[any]` tail, or with the `*` tail and a concrete mark (§6.5). An
    `[any-taint]` start fact (a must-premise, forward restricted runs only) is normal;
  * the case `above` of §4.1 for a fact that is not `[any-taint]`, and a lost correlation (`lostCorr`, §4.1);
  * an `[any]` result (W6: a may), and the normal form W2 of a `*` result (§4.1 step 6);
  * in the backward run, every result of the reversal of a micro edge whose forward target is `[any]` (a pass rule
    with an `AnyField` target, a may), also a `$` result (§9.1);
  * the cut of the field limit (§4.4);
  * a conjunction with an input that is in the demand layer, or that its literal does not cover and that is not
    `[any-taint]` (§4.6);
  * the application of a demand-layer summary edge (§4.3), also of a summary with several premises (§4.6); the
    application of a must record by `applicable` only (§4.3);
  * the `part` rows of the cleaner that give a demand-layer result (§4.7);
  * the END FACTS of a sink (§4.9): an end-fact edge takes no input fact. When a sink edge triggers, or a conjunctive
    sink completes a combination, it applies to the zero fact in the layer of that sink edge or of that combination
    (a combination is in the demand layer if one of its edges is).

  A demand-layer input gives a demand-layer result. The layer of an edge never goes back to normal
  (`Invariant.applyEdge_demand_monotone` and the related lemmas). On an `[any-taint]` fact only these operations give
  a demand-layer result, which W8 (b) names `[any]`, with no exclusion (THE DEMOTIONS; the other lists of this spec
  refer to this one): the field-limit cut (§4.4); a cleaner `part` row of §4.7 other than the `atAndBelow` and `below`
  rows one accessor below the fact (so the `exact` cleaner at the path of the fact or one accessor below it, and every
  cleaner two or more accessors below it); a may target (an `[any]` target of a pass rule, W6); a demand input (a
  demand fact, summary edge or record: another input of a conjunction in the demand layer, §4.6, a demand-layer
  summary edge or record, §4.3, or a demand link, an `[any]` added fact, §4.3); and the must-record demotion
  (§4.3; Lean `AnyTaint.recLayer`, `AnyTaintEx.recLayerX`). An exclusion that meets an `[any-taint]` fact (the keep
  edge of a strong write, a `*/E` summary or record) does NOT give a demand result: the result keeps the layer and
  carries the exclusion (W8 (a); §4.1).

Lean: `PFact` (a premise or a conclusion; the conclusion `*/E` carries the exclusion of the edge; the mark is `MarkA`
with `star`, `conc t`, `starEx x`) and `AFact` (a conclusion plus `demand : Bool`, the layer); with the exclusion of
`[any-taint]`, `AnyTaintEx.XFact` (an `AFact` plus its exclusion `ex`).

### 2.3 Well-formedness rules

| Rule | Text |
|---|---|
| W1 | An edge with no `*` side has the Empty exclusion. |
| W2 | A conclusion with the `*` tail has the mark `*` or `*∖X` and is in the normal layer. A premise may have the `*` tail with a concrete mark (a request answer in run 1; before F72 also, in a restricted run, the meet of an added fact with a `*/E` entry pattern, which F72 replaces by the FLOW form, §6.3). |
| W3 | In a run with the field limit `L`, every result of an operation has at most `L` counted accessors (§4.4). This holds if the field limit does not decrease from run to run (§6.6): then a premise emitted from a demand chain (§6.3) and a fact that passes an untouched base are also in the bound. A micro edge (§4.2) has no bound. W3 is argued, not proved (§11.2). |
| W4 | `[any]` and `[any-taint]` are tails only. A path has no inner `[any]` or `[any-taint]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. `TypeInfoAccessor`, `TypeInfoGroupAccessor` and `ValueAccessor` do not occur either: the type-info accessors serve only the lambda analysis of the prescan, and no statement and no rule makes a value accessor. |
| W6 | A conclusion with the `[any]` tail is in the demand layer. |
| W7 | Only a conclusion has a mark exclusion. An edge whose premise set has two or more members (an ND edge, §4.6) has no `*` tail. |
| W8 | THE `[any-taint]` RULE. (a) `[any-taint]` has a concrete mark only (never `*` or `*∖X`). It is a TAINT conclusion (§7.2). It can carry an EXCLUSION `E` of first accessors (`[any-taint]/E`, §1). Only a normal `[any-taint]` conclusion and a must-premise have one; an `[any]` fact, a `$` fact and every demand-layer fact have the Empty exclusion (Lean: `AnyTaintEx.carriesB`, `normX`). (b) THE NORMAL FORM: a conclusion with the `[any-taint]` tail is in the normal layer. A demand-layer result with the `[any-taint]` tail becomes `[any]`, with the same path and mark and with the Empty exclusion (a normal form, as W2; §4.1 step 6). So in a forward run the layer gives the any tail of a conclusion: `[any-taint]` in the normal layer, `[any]` in the demand layer (§7.2). (c) An `[any-taint]` PREMISE (a must-premise) occurs only in a forward restricted run, never in run 1 (§6.5). (d) `[any-taint]` is a FORWARD tail. The backward run has no fact, premise, edge or demand pattern with the `[any-taint]` tail: its seeds and its reversed `[any]` literals give `[any]` (§9.1, §9.2), and the hand-off reads a forward `[any-taint]/E` conclusion as the pattern `[any]` (§9.2). A normal edge with the `[any-taint]` tail is complete (§1). |

W2 holds for every derived fact, in run 1 without the static rule and the conjunctions (the closure `D`:
`Invariant.final_star_legal`) and in every forward restricted run (`RExact.final_star_legalR`). For run 1 with the
static rule (`Statics.DS`) it is argued (§11.2); with the conjunctions (`ND.DN`) it holds by W7 (a conjunction target
has no `*` tail). The backward run is concrete (`BExact.DB_concrete`), and it satisfies W2 when its seeds have
concrete marks and no `*` tail (`HandoffNoStar.DB_legal`), so no backward conclusion has a `*` tail
(`HandoffNoStar.DB_edge_nonstar`); every seed is a sink pattern with the tail `$` or `[any]`, cut by the field limit
(S11 (f), §9.2; `HandoffNoStar.nonstar_of_sinkK`). These are theorems of the concrete restricted runs (the emission
`emitM`). SINCE F72 a restricted run, forward or backward, has `*` conclusions: the edges of a FLOW premise (§6.3).
They have the mark `*` or `*∖X` and are in the normal layer, so W2 holds for them for the same reason as in run 1
(S7: a concrete target mark needs a concrete premise mark; argued, PENDING §11.2). The claims "the backward run is
concrete" and "no backward conclusion has a `*` tail" are false for the F72 runs.

W6 only moves edges from the normal layer to the demand layer, and W8 (b) only renames the tail of a demand-layer
result and drops its exclusion, which enlarges its location set (§11.2 gives the difference to the model). The
interpreter has two types of micro edge with an any target (`interpreter.md` §4.1, I14):

* a SOURCE with an `[any]` target (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`, `AssignMark` on an `AnyField`
  position; unconditional, conditional or conjunctive) has the target `[any-taint]`, with the Empty exclusion: a
  MUST, every location at or below the target position gets the mark (S15). It is a taint edge (§1). An end-fact
  action on an `AnyField` position gives the same target, `zero.$ (zeroMark) → P.[any-taint] (T)` (§4.9;
  `interpreter.md` I14);
* a PASS RULE with an `AnyField` target has the target `[any]`: a MAY. The rule does not know the field (`Map.put`
  writes one element, not every element).

A pass rule with an `AnyField` position on its PREMISE side is a rule error (S15; `interpreter.md` D33), so no forward
pass rule reads an `[any]` premise.

Under W6 every `[any]` result is in the demand layer: a may result never makes a record, and a vulnerability that rests
only on it is not confirmed (it stays a DEMAND entry, §8.10). In the backward run the reversal of a pass rule with an
`AnyField` target gives every result in the demand layer (§9.1), so no record goes through a may either. A result of a
taint edge is `[any-taint]`: it keeps the layer of its input, so a normal one is complete (§1), it can make a record
(§8.7 R1), and a vulnerability whose taint comes from an `[any]`-target source can be CONFIRMED (§4.9). A demotion
of §2.2 makes it `[any]` (W8 (b)): the field-limit cut, a cleaner `part` row other than the `atAndBelow` and `below`
rows one accessor below the fact, a may target, a demand input, and the must-record demotion (the list of §2.2). An
exclusion does not: the result carries it (W8 (a); §4.1).
Lean: the rule W6T (`AnyTaint.w6t`; with the exclusion `AnyTaintEx.w6tX`, which also drops the exclusion of a demoted
result): only the result of a statement micro edge with an `[any]` target that is not a taint edge goes to the demand
layer (§10.11). The text before F69 said that every `[any]` result is demand, so that no `[any]`-target source finding
is ever confirmed; F69 replaces it by W8 (`ap-history.md` F69).

W8 (a) holds for every normal any-tail conclusion of the spec closure `AnyTaintEx.D6X` (run 1 with the exclusion), for
every abstraction, under S15 and S10 (`AnyTaintExKinds.D6X_any_conc`; both hypotheses are necessary,
`AnyTaintSim.CexKinds.cex_taintConc`, `cex_bindNoAny`), so a FLOW edge has no `[any-taint]` conclusion
(`AnyTaintExKinds.D6X_flow_no_any_taint`, under S7, S10 and S15; no `W6.SummaryStar`) and no exclusion
(`AnyTaintExKinds.D6X_flow_no_excl`); with the hypotheses of `Kinds.kinds_D` this is the partition of run 1
(`AnyTaintExKinds.kinds_D6X`, `kinds_D6X_gen`). (Round 1, for `AnyTaint.D6T`: `AnyTaintSim.D6T_any_conc`, and
`D6T_flow_no_any_taint` also under `W6.SummaryStar`, which the run-1 policy has.)
Every edge conclusion of the refined runs is in the normal form of W8 (`AnyTaintExExact.D6X_wf`, `DRX_wf`). In the
concrete design every forward restricted run is concrete (`AnyTaintExExact.DRX_conc`, under C3;
`AnyTaintExCov.concX_all`), and so is the backward run (`BExact.DB_concrete`); every must-premise has an any tail
(`AnyTaintExExact.DRX_mustAny`) and a concrete mark (`AnyTaintExKinds.DRX_must_premise`, under C3, which
`AnyTaintEx.emitX_copies` gives). Since F72 the restricted runs are not concrete (§6.3). A must-premise still has an
any tail and a concrete mark: the F72 emission gives a must-premise only under a concrete pattern, and the FLOW form
of a `*` pattern has the `*` tail (argued, PENDING §11.2).

No exclusion is Universe (§1). A `*/Universe` conclusion needs a `$`-premise edge that acts on a `*`-tail fact. Every
`$`-premise micro edge has a concrete premise mark (S8: `zeroMark` for sources, `T` for conditional sources). A `*`-tail
fact has the mark `*` or `*∖X` (W2). So the mark gate never lets such a fact through (§4.1 step 4).
`Invariant.no_univ_star` proves it under S8, and `Invariant.final_star_legal` proves W2 for every derived fact.

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. Its one location is the zero location. An unconditional source rule
is a micro edge from the zero fact (a conditional source reads another fact, `interpreter.md` §4.1). The zero fact is
a premise like every other initial fact: a zero-to-fact edge is an edge with the premise set `{zero}`, in the normal or
the demand layer. A conjunction drops the zero fact from the union of its premise sets (§4.6). The cases where an
operation treats the zero fact in a special way:

* the statement transfer (§4.2) and the call (§3.5, §5.3): the zero fact passes, and it enters every resolved callee;
* the conjunction (§4.6): the union of the premise sets drops the zero fact;
* the cleaner (§4.7) and the type filter (§4.8): no cleaner is on the zero base, and a type filter on the zero base
  accepts the empty path (S11 (d));
* the sink check (§4.9): an unconditional sink triggers on the zero fact; the premise set `{zero}` is supported at a
  root and through the zero edges of the callers;
* the run-1 abstraction (§6.2), the emission (§6.3) and the start fact (§6.5): the zero fact gives the zero fact;
* the backward run (§9.2): the zero rules.

---

## 3. Denotation

### 3.1 Admitted continuations

`E.admits σ` is true if `σ = []`, or if the first accessor of `σ` is not in `E`.

| Tail | As a premise, the continuations `σ` that it covers | As a conclusion, the relation of the premise continuation `σ` to its own continuation `τ` |
|---|---|---|
| `*/E` | all `σ` that `E` admits | `τ = σ` and `E` admits `σ` (CORRELATED) |
| `[any]` | all `σ` | any `τ` (not correlated) |
| `[any-taint]/E` | all `σ` that `E` admits | any `τ` that `E` admits (not correlated) |
| `$` | `σ = []` | `τ = []` |

`[any-taint]` with the Empty exclusion has the denotation of `[any]`. Its exclusion `E` removes the continuations that
start with an accessor of `E`: on a premise it restricts `σ`, on a conclusion `τ`. It is not shared: the edge stays
uncorrelated. The layer gives the reading (W6, W8): a normal `[any-taint]/E` conclusion is exact (end-exact for a
must-premise, §1), so EVERY admitted location at or below its path carries the mark (a must); a demand `[any]`
conclusion over-approximates (a may). An `[any-taint]/E` premise covers the `σ` that `E` admits: its edges hold when
every admitted location of it carries the mark (a must-premise, §1). Lean: `AnyTaintEx.coversX` (a premise),
`coversFX` (a conclusion), `denX` (an edge).

### 3.2 Location set and edge relation

```
covers(i, l)  ⇔  l.base = i.base ∧ l.path = i.path ++ σ ∧ σ admitted by i.tail ∧ i.mark admits l.mark

den(i, f)(l0, l1)  ⇔  l0.base = i.base ∧ l1.base = f.base
                    ∧ i.mark admits l0.mark ∧ l1.mark = out(f.mark, l0.mark) ∧ f.mark passes l0.mark
                    ∧ ∃ σ τ. l0.path = i.path ++ σ ∧ l1.path = f.path ++ τ
                             ∧ σ admitted by i.tail ∧ (σ, τ) related by f.tail
```

with `admits(*, m)`, `admits(T, m) ⇔ m = T`, `admits(*∖X, m) ⇔ m ∉ X`, `out(*, m) = out(*∖X, m) = m`,
`out(T, m) = T`, and `passes(*∖X, m) ⇔ m ∉ X` (true for the other marks).

`den(i, f)(l0, l1)` reads: "the value at `l0` on method entry flows to `l1` at the statement of the edge". Lean:
`PFact.covers`, `den`, `MarkA.admits`, `MarkA.passes`. The tail of an `[any-taint]/E` side admits only what `E`
admits (§3.1; Lean: `AnyTaintEx.coversX`, `denX`).

Derived relations:

* `i` COVERS the fact `c` if every location of `c` is a location of `i` (Lean: `coversB`). It compares the marks: the
  marks of `c` must be a subset of the marks of `i` (Lean: `markSubB`).
* Two facts OVERLAP if they have a common location with the marks ignored (Lean: `overlapB`; with the exclusion of an
  `[any-taint]/E` fact, `AnyTaintEx.overlapX`). Every overlap test of this spec ignores the marks: the request match
  (§4.5), the conjunction store (§4.6), the sink check (§4.9) and the restriction (§6.4). Each of these places tests
  the marks separately. Each one reads the exclusion of an `[any-taint]/E` fact as part of its location set: an
  excluded location overlaps nothing.
* The restriction reads a demand pattern WITH ITS MARKS (§6.4; `ap-history.md` F71): the premise must lie inside `D-c`
  in its locations and in its marks (Lean: `Handoff.insideB`), and the mark of the conclusion must meet the mark of
  `D-p` (`Handoff.concMarkB`). The emission reads the entry pattern with its mark (`markMatchB`, §6.3; a `*∖X` entry
  pattern does not admit a mark of `X`; since F72 no pattern has the mark `*∖X`: the hand-off replaces it by `*`,
  §9.2). The demanded flows read both patterns with their marks (`PFact.covers`, §1).

### 3.3 Exclusion algebra and merge rules

* The edge exclusion is the union of what the model stores on the two sides (`SharedExcl.applyEdge_shared_excl`).
* MERGE RULE 1: two edges with the same premise, the same layer, the same exclusion and the same mark exclusion merge
  their conclusions (union).
* MERGE RULE 2: two edges with the same premise, the same layer and the same conclusion merge their exclusions by
  INTERSECTION: `admits(E1 ∩ E2, σ) = admits(E1, σ) ∨ admits(E2, σ)`. The union of the two relations is exact
  (`Subsume.merge_inter`). Two `[any-taint]/E1` and `[any-taint]/E2` conclusions with the same premise, layer, path
  and mark merge in the same way, into `[any-taint]/(E1 ∩ E2)` (argued, §11.2: the model has no merge rule for the
  exclusion of `[any-taint]`).
* MERGE RULE 2 FOR MARKS: two edges with the same premise, layer, exclusion and conclusion but mark exclusions `X1`, `X2`
  merge into one with `X1 ∩ X2`: a mark passes the merged edge if and only if it passes one of them
  (`Tree.rule2_mark`).
* A UNION of exclusions happens only along one derivation (a field write after another, a cleaner after another). A
  union across two different edges is FORBIDDEN: it removes pairs that one of the two edges has
  (`Subsume.union_loses_pairs`).

### 3.4 Reference types and tests

The reference forms of §4 and §6 use these types. A premise, a pattern and an added fact are a `Pattern`: a path fact
with the exclusion of its `*` tail or of its `[any-taint]` tail (W8). The implementation interns a premise as an
`InitialAp` (§7.1).

```kotlin
/** ANY is `[any]` (a may), ANY_TAINT is `[any-taint]` (a must, W8; forward runs only). ANY_TAINT can carry an
 *  exclusion; with the Empty exclusion the two have the same location set (§3.1). */
enum class Tail { STAR, ANY, ANY_TAINT, EXACT }

/** An any tail: `[any]` or `[any-taint]`. */
val Tail.isAny: Boolean get() = this == Tail.ANY || this == Tail.ANY_TAINT

/** A canonical (sorted, de-duplicated) set of concrete marks: the X of *∖X. Operations: `in`, `isSubsetOf`, `+`. */
class MarkSet(val ids: IntArray) {
    companion object { val EMPTY = MarkSet(IntArray(0)) }
}

/** A finite set of accessors: the exclusion E. Empty, or Concrete with a canonical non-empty set. No Universe (§1). */
sealed interface ExclusionSet {
    data object Empty : ExclusionSet
    class Concrete(val ids: IntArray) : ExclusionSet            // sorted, de-duplicated AccessorIdx, never empty
    fun admits(r: List<Accessor>): Boolean                     // r = [] or the first accessor of r is not in the set
    fun union(other: ExclusionSet): ExclusionSet
    fun isSubsetOf(other: ExclusionSet): Boolean
}

/** `p` is a prefix of this list. */
fun <T> List<T>.startsWith(p: List<T>): Boolean = size >= p.size && subList(0, p.size) == p

/** The static base S (`ClassStatic`, §4.10). */
val STATIC: AccessPathBase = AccessPathBase.ClassStatic

/** `*` is Star(MarkSet.EMPTY). A premise never has excluded marks. Since F72 a demand pattern never has them either:
 *  the hand-off replaces `*∖X` by `*` (§9.2). (Under F71 an entry pattern from a run-1 summary conclusion kept them,
 *  and the emission and the restriction read them exactly, §6.3, §6.4.) An added fact and a conclusion can have
 *  them. */
sealed interface MarkSlot {
    data class Star(val excluded: MarkSet) : MarkSlot     // *  or  *∖X
    data class Concrete(val mark: TaintMark) : MarkSlot   // T; the zero mark is a concrete mark
}

data class PathFact(val base: AccessPathBase, val path: List<Accessor>, val tail: Tail, val mark: MarkSlot)

/** A premise, a demand pattern or an added fact: a fact with its own exclusion (Empty unless the tail is STAR, or
 *  ANY_TAINT in a forward run: the exclusion of `[any-taint]/E`, W8). */
data class Pattern(val fact: PathFact, val exclusion: ExclusionSet)

/** A demand pattern (§1): the entry pattern D-c and the exit pattern D-p (null: the demand does not reach the exit). */
data class DemandPattern(val entry: Pattern, val exit: Pattern?)

/** §3.1: the tail admits the continuation r. */
fun tailAdmits(tail: Tail, exclusion: ExclusionSet, r: List<Accessor>): Boolean = when (tail) {
    Tail.STAR, Tail.ANY_TAINT -> exclusion.admits(r)   // r = [] or the first accessor of r is not excluded
    Tail.ANY -> true
    Tail.EXACT -> r.isEmpty()
}
fun Pattern.tailAdmits(r: List<Accessor>) = tailAdmits(fact.tail, exclusion, r)

/** The marks of `c` are a subset of the marks of `i` (Lean: markSubB). */
fun markSub(i: MarkSlot, c: MarkSlot): Boolean = when (i) {
    is MarkSlot.Star -> when (c) {
        is MarkSlot.Star -> i.excluded.isSubsetOf(c.excluded)   // *∖X ⊇ *∖Y if and only if X ⊆ Y; * ⊇ every abstract mark
        is MarkSlot.Concrete -> c.mark !in i.excluded
    }
    is MarkSlot.Concrete -> c is MarkSlot.Concrete && c.mark == i.mark
}

/** Tail inclusion at the same path: every continuation of c is a continuation of i (Lean: tailSubB). */
private fun tailSub(i: Pattern, c: Pattern): Boolean = when (i.fact.tail) {
    Tail.ANY -> true
    Tail.EXACT -> c.fact.tail == Tail.EXACT
    Tail.STAR, Tail.ANY_TAINT -> when (c.fact.tail) {       // the exclusion of i must exclude only what c excludes
        Tail.EXACT -> true
        Tail.ANY -> i.exclusion == ExclusionSet.Empty
        Tail.STAR, Tail.ANY_TAINT -> i.exclusion.isSubsetOf(c.exclusion)
    }
}

/** `i` covers every location of `c`, marks included (Lean: coversB). */
fun covers(i: Pattern, c: Pattern): Boolean {
    if (i.fact.base != c.fact.base || !markSub(i.fact.mark, c.fact.mark)) return false
    val p = i.fact.path
    val q = c.fact.path
    if (!q.startsWith(p)) return false
    return if (q.size == p.size) tailSub(i, c) else i.tailAdmits(q.drop(p.size))
}

/** A common location, marks ignored (Lean: overlapB). */
fun overlap(a: Pattern, b: Pattern): Boolean {
    if (a.fact.base != b.fact.base) return false
    val p = a.fact.path
    val q = b.fact.path
    return when {
        q.startsWith(p) -> a.tailAdmits(q.drop(p.size))
        p.startsWith(q) -> b.tailAdmits(p.drop(q.size))
        else -> false
    }
}

/** §4.3, run 1; a record also in every later run (with inside, R4): the premise j covers the added fact a
 *  (Lean: applicable). A premise with an any tail needs a fact with an any tail. Run 1 has no `[any-taint]`
 *  premise; a must record that applies by applicable only gives a demand result (§4.3). */
fun applicable(j: Pattern, a: Pattern): Boolean =
    covers(j, a) && (!j.fact.tail.isAny || a.fact.tail.isAny)

/** §4.3, the summaries of a restricted run: j lies inside a as locations, and markSub(j, a) (Lean: satI; with the
 *  exclusions of `[any-taint]/E` facts and premises AnyTaintEx.satX). A normal result of a must-premise (an
 *  `[any-taint]` j) needs this test (Lean: SatInsideX). Since F72 a FLOW premise (the mark `*`) also applies by
 *  applicable (§4.3; `satisfies` of §6.3). */
fun inside(j: Pattern, a: Pattern): Boolean =
    covers(a.copy(fact = a.fact.copy(mark = MarkSlot.Star(MarkSet.EMPTY))), j) && markSub(j.fact.mark, a.fact.mark)
```

An empty Concrete `ExclusionSet` must not exist (return `Empty`). `Accessor` is an interned accessor, and
`AccessorIdx` is its intern id (the accessor interning of today, §7.6): `admits(r)` reads the `AccessorIdx` of the
first accessor of `r` and tests it against `ids`. Keep the excluded accessors as a CANONICAL (sorted, de-duplicated)
`IntArray` of `AccessorIdx`; the same for `MarkSet`. The edge trees are keyed by both, so two equal sets
must be equal values. Because the sets of accessors and marks are unbounded (§1), these tests are exact: `covers`,
`overlap` and `cleanPos` (§4.7) need no "all accessors" or "all marks" case. The tests read `ANY_TAINT` with its
exclusion as a location set, as `*/E` reads its exclusion: with the Empty exclusion it is `ANY` (§3.1). So `covers`,
`overlap`, `applicable` and `inside` read the exclusion of an `[any-taint]/E` fact or premise (Lean:
`AnyTaintEx.coversX`, `overlapX`, `satX`). The operations that read the difference of the two any tails (the layer)
say so (§4.1, §4.3, §4.6, §4.9, §6.3).

### 3.5 Concrete semantics

The theorems compare the analysis with this semantics. It is the program that the micro edges describe (S1). It is
alias-free and location-level. Lean: `Basic.lean` (`Stmt.step`, `Flow`, `Reach`). `Flow` is this semantics without
the override of the summary rewriter (REFERENCE SEMANTICS OF RULES, below).

* STATEMENT STEP. A statement with the touched bases `B` and the micro edges `M` moves the location `l` to `l'` if
  `l.base` is not in `B` and `l' = l`, or if a micro edge `e` of `M` relates them: `den(e)(l, l')` (§3.2). So an
  untouched base keeps its locations, and a touched base keeps only what a micro edge gives.
* CLEANER STEP. A cleaner `(x, p, reach, mark)` (§4.7) removes the location `l` if `l.base = x`, the cleaner removes
  the mark of `l` (its own mark, or every mark), and `l.path = p ++ σ` with `σ` in the reach: `exact`: `σ = []`;
  `below`: `σ ≠ []`; `atAndBelow`: every `σ`. Every other location passes unchanged (Lean: `Cleaner.cleansB`).
* FILTER STEP. A type filter `filter(b, may)` (§4.8) removes a location on the base `b` whose path `may` rejects. Every
  other location passes unchanged.
* CALL STEP. A call has the touched caller bases, the binding edges into the callee and the binding edges back. A
  caller location on an untouched base passes over the call. A location `l` on a touched base goes into the callee
  through a binding edge `e1` (`den(e1)(l, l1)`), flows in the callee from the entry location `l1` to an exit location
  `l2`, and comes back through a binding edge back `e2` (`den(e2)(l2, l3)`) as `l3`. For the call `r = m(a1..an)` the
  touched caller bases are the arguments, the result and the static base; the bindings into the callee are
  `ai.* → argi.*`, `S.* → S.*` and `zero.* → zero.*`; the bindings back are `argi.* → ai.*`, `ret.* → r.*` and
  `S.* → S.*`. The interpreter gives the bindings of each call kind (`interpreter.md` §3). The zero base is never a
  touched base of a call: the zero location passes over every call, and it also enters the callee through
  `zero.* → zero.*`. A binding has the premise mark `*` (S10), so the zero binding has the `*` form, and the zero fact
  is at or below its premise. Lean: `Call`, `Flow.pass`, `Flow.call`.
* FLOW. A flow of the method `M` from the entry location `l0` is a chain of these steps from the entry node of `M` to a
  node `n`. It ends at the location `l`: the value at `l0` on method entry is at `l` at `n` (Lean: `Flow`). A call step
  contains the flow of the callee.
* VULNERABILITY AND WITNESS. A sink pattern `s` with the concrete mark `T` at the node `n` is REACHED if the zero
  location of a root flows to a location at `n` that `s` covers. The flow can go down into callees: from a location at a
  call node, through a binding edge into the callee, then a flow in the callee (Lean: `Reach`). Such a chain is a
  WITNESS of the vulnerability. A vulnerability is REAL if it has a witness.
* REFERENCE SEMANTICS OF RULES. The interpreter rules are read in this semantics as follows (S1). A source or a sink
  fires with every negated mark literal true. A pass rule has no mark literal (a pass rule with a mark literal is a
  rule error that is not rejected, `interpreter.md` §1.3: it fires without its mark literals, §11.1). A user-defined
  rule that the summary rewriter selects REPLACES the callee flow for its marks at its positions (§4.7). The override
  is not in `Flow`. The theorems read the program in which each call with selected rules is wrapped: the callee flow,
  then the cleaner `(P, exact, T)` for each selected rule, mark and position (for an `AnyField` position
  `(P, atAndBelow, T)` for a source, `(P, below, T)` for a cleaner, §4.7), on the callee results; the source
  results and the end facts of the call bypass the wrapper (argued, §11.2). An end-fact action is a source at its
  sink statement that fires when its sink fires (§4.9). The model has none (§11.2). A micro edge with an any target
  gives the value of its premise location to EVERY location at or below its target path (§3.2). For a source with an
  `[any]` target this is the rule itself (a must, S15). For a pass rule with an `AnyField` target it over-approximates
  the callee, which writes some field: W6 keeps its results in the demand layer (§2.3), and the backward run keeps
  every result of its reversal in the demand layer (§9.1). A conjunction of literals on
  different facts is path-insensitive: each literal can hold on its own path. Its semantics is the SUPPORT semantics: a location is tainted
  at a node together with the list of entry locations that its derivation needs, and a vulnerability witness is a tree
  (§4.6; Lean: `ND.TaintN`, `ND.ReachAll`). "Real" in this spec always means real in this reference semantics.

---

## 4. Operations and primitives

### 4.1 The core computation: delta-concat

`concat(c, from →_E to)` computes the result of an edge `from → to` with the edge exclusion `E` on the conclusion `c` of
a current edge. `Ec` is the exclusion of the edge of `c`. `E` is the one exclusion of the edge (§2.2): the shared
exclusion of a correlated edge, or the exclusion of a `*` premise of an uncorrelated edge, else Empty. Every edge
application of the analysis uses `concat`: a micro edge (a statement edge or a call binding, §4.2), a summary edge
(§4.3), a summary with several premises (§4.6), a record and a reversed record (§8.7 R3, R4). Lean: `applyEdge`.

The special cases of `concat`:

* run 1 only: the mark request (step 4) and the static exception (after step 2);
* a restricted run: the request row of step 4 gives NO fact and NO request (F72; §4.5). A fact with an abstract mark
  (a fact of a FLOW premise, §6.3) can meet a concrete premise mark; the flow of a concrete mark comes from a concrete
  demand pattern. (Before F72 the row never occurred, because every fact of a restricted run was concrete, and the
  implementation asserted it.);
* `concat` does not apply the field limit. The operation that calls it does (§4.4).

Preconditions. `concat` ASSERTS them; an edge that breaks one is a bug of the interpreter or of the analyzer:

* the premise mark is `*` or `T`, never `*∖X` (S7);
* a concrete target mark needs a concrete premise mark (S7);
* a `$` premise has a concrete mark (S8);
* a `$` premise has no `*` target (S8);
* a `$` target needs a concrete premise mark (S8, `Kinds.ExactTargetConc`);
* an `[any-taint]` target or premise has a concrete mark (W8, S15). (With S7 an `[any-taint]` target then has a
  concrete premise mark.)

So a `$` premise meets only facts with a concrete mark: on a `*`-tail fact (mark `*` or `*∖X`, W2) the mark gate gives
a request or nothing (step 4). A summary edge meets the preconditions too: an initial fact never has `*∖X` (§2.2); a
`$` initial fact is the zero fact, an answer or an emission, all with a concrete mark (the FLOW form of a `*` pattern
never has the `$` tail, §6.3); a concrete premise has only
concrete conclusions (`Coverage.edge_conc`), which have no `*` tail (W2); and a `*` premise has only FLOW conclusions,
with an abstract mark and no `$` or `[any-taint]` tail (§7.2). The conclusion kinds of §7.2 rest on the second, the
fifth and the last precondition.

A micro edge with an `[any]` target is a may (a pass rule); a micro edge with an `[any-taint]` target is a must (a
taint edge, with the Empty exclusion). The interpreter gives the `[any-taint]` target only to the sources (S15). An
`[any-taint]` premise is the premise of a summary edge or a record of a forward restricted run (a must-premise, §1),
with its exclusion; no micro edge has one (S15), and the backward run has none (W8 (d)). An `[any-taint]` target with
a non-empty exclusion is the conclusion of a summary edge or a record (§4.3).

Step 1 — base. If `c.base ≠ from.base`, the result is empty.

Step 2 — position:

* `below r`: `c.path = from.path ++ r`. The fact is AT OR BELOW the premise.
* `above r`: `from.path = c.path ++ r`, `r ≠ []`. The fact is ABOVE the premise: NOT STRONG ENOUGH.
* `apart`: neither. The result is empty.

A fact in the case `below` is strong enough only if `applicable(premise, fact)` holds (§1, §4.3). Example: an `[any]`
fact at a `*/E` premise with `E ≠ {}` is in the case `below r = []`, but the premise does not cover it.

STATIC EXCEPTION (run 1 only, statement micro edges only; the rule is §4.10 item 1). The exception applies if all
these conditions are true:

1. The edge `i → c` in the method `m` is an IDENTITY STATIC `*` EDGE (§4.10): its premise is `i = (S, q, */E0, *)`,
   and `c` is `(S, q, */Ec, *)` or `(S, q, */Ec, *∖X)` at the same path `q`, in the normal layer.
2. `q` is the root path `[]` or a class `[<C>]`.
3. The premise `from` of the micro edge is on `S`, in the case `above r` (`from.path = q ++ r`, `r ≠ []`).
4. `Ec` admits `r`.

Then the result is no fact and no mark request. The step raises the position request `(m, i, p')`, where `p'` is
`from.path` cut to at most two accessors. A restricted run, a call binding and a summary edge have no exception. A
statement micro edge at a call (a source of the rule statement of the call, a pass rule of an unresolved callee, the
`RemoveAllMarks` kill on `S`) acts on the bound fact or on the added fact. Its edge is then the caller edge, so `m` is
the caller (§5.3 steps 3 and 4).

Step 3 — overlap and result shape.

Case `below r`. The premise must admit `r`: a `*` premise if `E` admits `r`; a `$` premise if `r = []`; an `[any]`
premise for every `r`; an `[any-taint]/Ej` premise (a must-premise of a summary or a record) if `Ej` admits `r`. For a
`*` target and `r ≠ []`, `E` must also admit `r` (row 1). `Et` is the exclusion of an `[any-taint]` target (a
summary conclusion `[any-taint]/Et`; Empty for a micro edge). Then:

| `to.tail` | `r` | `c.tail` | result path | result tail | to the demand layer |
|---|---|---|---|---|---|
| `*` | `≠ []` (`E` admits `r`) | any | `to.path ++ r` | `c.tail` (with `Ec`; an `[any-taint]/Ec` fact keeps `Ec` at the new path end) | no |
| `*` | `[]` | `$` | `to.path` | `$` | no |
| `*` | `[]` | `*/Ec` | `to.path` | `*/(Ec ∪ E)` | no |
| `*` | `[]` | `[any]` | `to.path` | `[any]` | yes (W6) |
| `*` | `[]` | `[any-taint]/Ec` | `to.path` | `[any-taint]/(Ec ∪ E)` (the EXCLUSION EDGE, W8) | no |
| `[any]` | any | any | `to.path` | `[any]` | yes (W6: a may) |
| `[any-taint]/Et` | any | any | `to.path` | `[any-taint]/Et`; `[any]` in the demand layer (W8) | if `lostCorr` |
| `$` | any | `*/Ec` | `to.path` | `$` | if the correlation of `c` restricts the premise (`lostCorr`) |
| `$` | any | an any tail or `$` | `to.path` | `$` | no (an `[any]` `c` is in the demand layer already, W6) |

`lostCorr` (for a `*/Ec` fact `c` only) is true if `Ec ∪ E ≠ {}` for `r = []`, or `Ec ≠ {}` for `r ≠ []`. Otherwise
the premise admits every continuation, and the uncorrelated result is exact (`Exact.applyEdge_exact`). An
`[any-taint]` target is a taint edge or the conclusion of a summary of a concrete premise: its premise mark is
concrete (S15, §7.2), so `c` has a concrete mark, no `*` tail (W2), and `lostCorr` is false. The exclusion edge (the
keep edge `x.* →_{f} x.*` of a strong write, a `*/E` summary or record with `E ≠ {}`) gives an `[any-taint]` fact its
exclusion: the result is `[any-taint]/(Ec ∪ E)` in the layer of `c`, not `[any]` (W8; Lean `AnyTaintEx.Vec.setter_keep`;
the round-1 rule demoted it, `setter_keep_base`). In the row `*`, `≠ []`, the exclusion `Ec` restricts the
continuation after `c.path`, not `r`, so the case `below` does not test `r` against `Ec`
(`AnyTaintEx.Vec.below_keeps_loc`: such a test would lose a real flow).

Case `above r`. The premise decides WHETHER the edge applies: the tail of `c` must admit `r` (`*/Ec` and
`[any-taint]/Ec`: `Ec` admits `r`; `[any]`: yes; `$`: no overlap). If it does not, the edge gives no result and no
request. The target decides WHAT comes out. For a `*` or an `[any]` fact `c`: `(to.path, $)` if `to.tail = $`, else
`(to.path, [any])`, always in the demand layer: a `*` fact loses its correlation, and an `[any]` fact is in the demand
layer already (W6). For an `[any-taint]/Ec` fact `c` whose `Ec` admits `r`, EVERY location at or below
`c.path ++ r` carries the mark, so every premise location carries it and nothing is lost. The result is in the layer
of `c`, unless the table says demand:

| `to.tail` | result | to the demand layer |
|---|---|---|
| `$` | `(to.path, $)` | no |
| `[any-taint]/Et` | `(to.path, [any-taint]/Et)` | no |
| `*` | `(to.path, [any-taint]/E)`: the exclusion `E` of the EDGE (§2.2), not `Ec` | no |
| `[any]` | `(to.path, [any])` | yes (W6: a may) |

So a read `y = c.P.g` (the micro edge `x.P.g.* → y.*`) on `(x, P, [any-taint], Ec, T)` gives `(y, ., [any-taint], {},
T)` if `g ∉ Ec`, and nothing if `g ∈ Ec` (`AnyTaintEx.Vec.read_admitted`, `read_excluded`; the check is necessary:
`AnyTaintExExact.CexAbove.cex_above`, a setter and then a read of the written field). (Lean:
`AnyTaintEx.applyEdgeX`: the base `belowCase` and `aboveCase` for a fact of the kind `.any` in the normal layer, the
exclusion rules `annX` and the layer rule `layerX`, then `AnyTaintEx.w6tX` for a may target. The rows of the
exclusion are exact: `AnyTaintExExact.keep_row_exact`, `above_row_exact`, `below_row_exact`. §11.2 gives the
correspondence.)

Step 4 — mark gate. The premise mark `from.mark` (never `*∖X`) against the fact mark `c.mark`:

| `from.mark` | `c.mark` | result |
|---|---|---|
| `*` | any | apply |
| `T` | `T` | apply |
| `T` | `T' ≠ T` | empty |
| `T` | `*∖X`, `T ∈ X` | empty (the mark was cleaned) |
| `T` | `*` or `*∖X` with `T ∉ X` | NO fact; in run 1 the request `T` on the premise of `c` (§4.5). A restricted run: NO fact and NO request (F72, §4.5) |

The gate comes after step 3: an apart fact, or a fact that the premise or `E` does not admit, gives no request. Lean:
`markGate`.

Step 5 — result mark `comp(to.mark, c.mark)`:

| `to.mark` | `c.mark` | result mark |
|---|---|---|
| `*` | `m` | `m` |
| `T` | any | `T` |
| `*∖X` | `*` | `*∖X` |
| `*∖X` | `*∖Y` | `*∖(X ∪ Y)` |
| `*∖X` | `T` | `T` if `T ∉ X`; NO fact if `T ∈ X` |

A `*∖X` target occurs only on a summary conclusion (a callee with a cleaner). Lean: `markComp`.

Step 6 — layer and normal form. The result is in the demand layer if `c` is, if the applied edge is (a summary edge,
§4.3), or if step 3 says so. Then:

* W6: a result with the `[any]` tail is in the demand layer. Every result of a may `[any]` target has the `[any]`
  tail (step 3).
* W8: a result with the `[any-taint]` tail in the demand layer becomes `[any]`, with the same path and mark and the
  Empty exclusion. A result with the `[any-taint]` tail in the normal layer stays `[any-taint]`, with its exclusion.
* W2: a result with the `*` tail and (a concrete mark, or the demand layer) becomes uncorrelated: `[any]` with the
  Empty exclusion, in the demand layer.

The step only enlarges the fact (`CoreAux.norm_sound`, `Invariant.demand_of_any_ok`); W8 changes the name of the
tail and drops the exclusion, so it only enlarges the location set (§3.1). The step does not apply the field limit
(§4.4). Lean: W6 and W8 together are the rule W6T (`AnyTaint.w6t`, `transferT`; with the exclusion `AnyTaintEx.w6tX`,
`transferX` and the normal form `normX`): the model keeps the kind `.any` and raises only the layer of a may result
(§11.2).

Theorem `Core.applyEdge_sound` (THE CORE LEMMA): `concat` covers the composition of the fact relation and the edge
relation, or raises the request for the premise mark. This holds in both cases: at or below the premise, and above it.
With the exclusion of `[any-taint]` (W8): `AnyTaintExCov.applyEdgeX_sound` (the result
exclusion admits every reached end location, `annX_admits`), and a normal result is exact on the admitted locations
(`AnyTaintExExact.applyEdgeX_exact`; its side conditions are necessary, `CexSideConditions.cex_htx`, `cex_hfx`).

Reference form (the vector tests of §13 compare the tree implementation with it). It uses the types of §3.4. The edge
carries its one exclusion:

```kotlin
/** A path edge `from → to` with its ONE exclusion (W1: Empty if no side has the STAR tail). `fromExclusion` and
 *  `toExclusion` are the own exclusions of an ANY_TAINT side (W8): a must-premise `[any-taint]/Ej` and a summary
 *  conclusion `[any-taint]/Et`. They are Empty for a micro edge and for every other tail. */
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet,
                    val fromExclusion: ExclusionSet = ExclusionSet.Empty,
                    val toExclusion: ExclusionSet = ExclusionSet.Empty)

/** The current conclusion: the fact, the exclusion of its edge (`*`: the shared exclusion; ANY_TAINT: its own
 *  exclusion E of `[any-taint]/E`, W8; Empty otherwise), the layer of its edge. */
data class Conclusion(val fact: PathFact, val exclusion: ExclusionSet, val demand: Boolean)

private fun PathEdge.premiseAdmits(r: List<Accessor>): Boolean = when (from.tail) {
    Tail.EXACT -> r.isEmpty()
    Tail.ANY_TAINT -> fromExclusion.admits(r)   // a must-premise: Ej
    else -> exclusion.admits(r)        // `*`: E; `[any]`: E is Empty unless the target is `*` (row 1)
}

private class Shape(val path: List<Accessor>, val tail: Tail, val exclusion: ExclusionSet, val demand: Boolean)

private fun below(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    if (!edge.premiseAdmits(r)) return null
    val to = edge.to
    return when (to.tail) {
        Tail.STAR -> when {
            r.isNotEmpty() -> Shape(to.path + r, c.fact.tail, c.exclusion, demand = false)   // keeps Ec (W8)
            c.fact.tail == Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, false)
            c.fact.tail == Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)   // W6
            else -> Shape(to.path, c.fact.tail, c.exclusion.union(edge.exclusion), false)  // `*/Ec`, or the exclusion
        }                                                                                 // edge on `[any-taint]/Ec` (W8)
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6: a may
        Tail.ANY_TAINT, Tail.EXACT -> Shape(to.path, to.tail,                                  // a must, or `$`
            if (to.tail == Tail.ANY_TAINT) edge.toExclusion else ExclusionSet.Empty,           // Et (W8)
            demand = c.fact.tail == Tail.STAR &&                                               // lostCorr
                (if (r.isEmpty()) c.exclusion.union(edge.exclusion) else c.exclusion) != ExclusionSet.Empty)
    }
}

private fun above(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    val admitted = when (c.fact.tail) {
        Tail.STAR, Tail.ANY_TAINT -> c.exclusion.admits(r); Tail.ANY -> true; Tail.EXACT -> false
    }
    if (!admitted) return null                     // no common location: no result and no request
    val to = edge.to
    if (c.fact.tail != Tail.ANY_TAINT) {           // a `*` fact loses its correlation; an `[any]` fact is demand (W6)
        val tail = if (to.tail == Tail.EXACT) Tail.EXACT else Tail.ANY
        return Shape(to.path, tail, ExclusionSet.Empty, demand = true)
    }
    return when (to.tail) {                        // every admitted location of c carries its mark: nothing is lost
        Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, demand = false)
        Tail.ANY_TAINT -> Shape(to.path, Tail.ANY_TAINT, edge.toExclusion, demand = false)    // Et
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6: a may
        Tail.STAR -> Shape(to.path, Tail.ANY_TAINT, edge.exclusion, demand = false)          // the edge exclusion (W8)
    }
}

sealed interface EdgeOutcome {
    data object None : EdgeOutcome
    data class Fact(val conclusion: Conclusion) : EdgeOutcome
    data class Request(val mark: TaintMark) : EdgeOutcome                  // run 1 only (§4.5)
    data class PositionRequest(val path: List<Accessor>) : EdgeOutcome     // run 1 only (§4.10 item 1)
}

/** The path `q` is the root path `[]` or a JVM class position `[<C>]`. `isClass` is true only for the class accessor
 *  `<C>` of a JVM class. A Go global `[<G>]` is a static FIELD, not a class (§4.10). */
fun rootOrClass(q: List<Accessor>): Boolean = q.isEmpty() || (q.size == 1 && q[0].isClass)

/** `edgeDemand`: the layer of the applied edge; true for a demand-layer summary edge (§4.3), false for a micro edge.
 *  `staticIdentity`: true only in run 1, for a statement micro edge, when the edge of `c` is an identity static `*`
 *  edge (the static exception after step 2). For a statement micro edge at a call, `c` is the bound or the added
 *  fact, and its edge is the caller edge (§5.3). `restricted`: true in a restricted run. */
fun concat(c: Conclusion, edge: PathEdge, edgeDemand: Boolean = false,
           staticIdentity: Boolean = false, restricted: Boolean = false): EdgeOutcome {
    val from = edge.from
    check(from.mark !is MarkSlot.Star || from.mark.excluded == MarkSet.EMPTY)          // S7
    check(edge.to.mark !is MarkSlot.Concrete || from.mark is MarkSlot.Concrete)          // S7
    check(from.tail != Tail.EXACT || from.mark is MarkSlot.Concrete)                    // S8
    check(from.tail != Tail.EXACT || edge.to.tail != Tail.STAR)                         // S8
    check(edge.to.tail != Tail.EXACT || from.mark is MarkSlot.Concrete)                 // S8 (ExactTargetConc)
    check(edge.to.tail != Tail.ANY_TAINT || edge.to.mark is MarkSlot.Concrete)          // W8, S15
    check(from.tail != Tail.ANY_TAINT || from.mark is MarkSlot.Concrete)                // W8
    if (c.fact.base != from.base) return EdgeOutcome.None
    val p = from.path
    val q = c.fact.path
    val isAbove = p.size > q.size && p.startsWith(q)
    val shape = when {
        q.startsWith(p) -> below(c, edge, q.drop(p.size))
        isAbove -> above(c, edge, p.drop(q.size))
        else -> null
    } ?: return EdgeOutcome.None
    if (staticIdentity && from.base == STATIC && isAbove && rootOrClass(q)) {   // the static exception (§4.10)
        check(!restricted)
        return EdgeOutcome.PositionRequest(p.take(2))                          // cut to the static field or class
    }
    val premiseMark = from.mark
    if (premiseMark is MarkSlot.Concrete) {                                   // step 4: the mark gate
        when (val cm = c.fact.mark) {
            is MarkSlot.Concrete -> if (cm.mark != premiseMark.mark) return EdgeOutcome.None
            is MarkSlot.Star -> {
                if (premiseMark.mark in cm.excluded) return EdgeOutcome.None
                if (restricted) return EdgeOutcome.None                       // F72: no request after run 1 (§4.5)
                return EdgeOutcome.Request(premiseMark.mark)
            }
        }
    }
    val mark = compose(edge.to.mark, c.fact.mark) ?: return EdgeOutcome.None  // step 5
    return EdgeOutcome.Fact(normalize(PathFact(edge.to.base, shape.path, shape.tail, mark),
        shape.exclusion, c.demand || edgeDemand || shape.demand))
}

fun compose(to: MarkSlot, c: MarkSlot): MarkSlot? = when (to) {
    is MarkSlot.Concrete -> to
    is MarkSlot.Star -> when (c) {
        is MarkSlot.Star -> MarkSlot.Star(to.excluded + c.excluded)
        is MarkSlot.Concrete -> if (c.mark in to.excluded) null else c
    }
}

/** Step 6: W6, W8, then the normal form W2. */
fun normalize(f: PathFact, exclusion: ExclusionSet, demand: Boolean): Conclusion = when {
    f.tail == Tail.ANY -> Conclusion(f, ExclusionSet.Empty, demand = true)                                  // W6
    f.tail == Tail.ANY_TAINT -> {
        check(f.mark is MarkSlot.Concrete)                                                                  // W8 (a)
        if (demand) Conclusion(f.copy(tail = Tail.ANY), ExclusionSet.Empty, demand = true)                // W8 (b)
        else Conclusion(f, exclusion, demand = false)                                    // keeps E (W8 (a))
    }
    f.tail != Tail.STAR || (f.mark is MarkSlot.Star && !demand) -> Conclusion(f, exclusion, demand)
    else -> Conclusion(f.copy(tail = Tail.ANY), ExclusionSet.Empty, demand = true)                         // W2
}
```

### 4.2 Apply a micro edge

A micro edge is an edge of a statement summary or a call binding edge (caller base to callee base, callee exit base to
caller base; `interpreter.md` §2, §3). A callee summary edge is not a micro edge: it applies only to an added fact that
satisfies its premise (§4.3). A micro edge applies to EVERY fact on a touched base that overlaps its premise: both cases
of §4.1. Example: the fact `(a, ., *, {}, *)` and the micro edge `(a, .f, *) → (b, ., *)` of `b = a.f` give
`(b, ., [any], {}, *)` in the demand layer (`Cases.lean`). Exceptions: the static rule of run 1 (§4.1 static exception,
§4.10 item 1), and the alias edges of a call result (this spec §5.3 step 5; `interpreter.md` §3.8 AC3 to AC5).

The statement transfer of one conclusion `c` of the edge `(i, layer) → c` in the method `m` (Lean: `transfer`;
`interpreter.md` §2.1 gives the same steps for the IR):

1. No liveness drop. A fact on a local that is dead at the statement goes on (`interpreter.md` §2.1). It reaches no
   use, so it costs work only.
2. If `c.base` is not touched: the result is `c` (`Sequent.Unchanged`).
3. Apply the operand type filters of `c.base` (§4.8; `interpreter.md` §2.1 step 3). A rejected fact is dropped.
4. Apply `concat(c, e)` (§4.1) for every micro edge `e` of the statement that is not conjunctive. The result is the
   union of the outcomes. A `Fact` outcome is a result fact. A `Request` outcome gives no fact; it raises the request
   `(m, i, T)` (run 1, §4.5). A `PositionRequest` outcome gives no fact; it raises the position request `(m, i, p)`
   (run 1, §4.10). A touched base keeps only what an edge gives again. That is the KILL.
5. Apply the lhs type filter to the results on the lhs (§4.8; `interpreter.md` §2.1 step 5).
6. Apply the field limit to each result (§4.4).

A conjunctive micro edge (§4.6) does not go through step 4: the conjunction store (§4.6, §8.9) applies it.

The special cases of the transfer:

* RUN 1 ON THE STATIC BASE (the rule is §4.10 item 1; the test is §4.1, static exception). Run 1 only, statement micro
  edges only: when the edge of `c` is an identity static `*` edge at the root `[]` or at a class `[<C>]`, a micro edge
  whose premise path `p` lies strictly below `c` (the exclusion of `c` admits the rest) gives no fact and no mark
  request; it raises the position request for `p` cut to at most two accessors. Below a static field the ordinary rules
  apply. The kill stays: the touched bases keep only what the other micro edges give. See the last two rows of the
  table below.
* THE ZERO FACT. A statement that does not touch the zero base passes the zero fact unchanged (step 2). A statement
  that touches it has the micro edge from the zero fact to the zero fact (S11 (d)), so the zero fact passes. The read
  sources and the exit sources of the interpreter fire on the zero fact (`interpreter.md` §4.4, §4.7).
* A RESTRICTED RUN has no request and no position request (§6.1). Since F72 a `Request` outcome of step 4 does not
  occur there: where run 1 raises a mark request, a restricted run gives nothing (§4.1 step 4, §4.5).
* THE BACKWARD RUN applies the reversed statement (§9.2) with steps 2, 4 and 6 only: no type filter. (Without a filter
  the backward run only keeps more requirements, so this is sound.)

Every micro edge (a statement edge, with its alias edges, or a call binding edge) is precise and complete (S1, S2).
The field limit never applies to a micro edge: a micro edge keeps its full paths, of any length. The analyzer applies
the limit to the RESULT, after it applies the micro edge to the propagated edge (§4.4; Lean: `transfer` limits the
results, and `Program.WF` puts no bound on a micro edge).

A micro edge has NO LAYER. The layer belongs to the propagation edge, and only the AP operations of §2.2 change it. The
interpreter sets no layer. A negated mark literal counts as true for a source and a sink (the reference semantics,
§3.5). This is the expected over-approximation of a path-insensitive engine, as the conjunction is (§4.6). Positive
literals on different facts make a conjunction for a source (§4.6) and a conjunctive sink (§4.9). A pass rule has no
mark literal (`interpreter.md` §4.2). Only an unconditional cleaner applies (§4.7, `interpreter.md` §4.2).

The cases below are checked by `decide` in `Cases.lean`. The two static rows follow §4.10. The model checks the read
row (`Statics.gen_read_DS`, `gen_read_sreq`); the write row follows from §4.10 item 1 and is not checked separately:

| Statement | Input fact | Result | Layer |
|---|---|---|---|
| `a = b.f` | `(b, .f, *, E, *)` | `(a, ., *, E, *)` | normal |
| `a = b.f` | `(b, ., *, E, *)`, `f ∉ E` | `(a, ., [any], {}, *)` | demand |
| `a = b.f` | `(b, ., *, {f}, *)` | nothing for `a` | |
| `a = b.f` | `(b, ., [any], {}, *)` | `(a, ., [any], {}, *)` | demand (the input is demand by W6; the model copies the layer) |
| `a = b.f` | `(b, ., $, {}, T)` | nothing for `a` | |
| `a = b.f` | `(b, ., [any-taint], E, T)`, `f ∉ E` | `(a, ., [any-taint], {}, T)` | normal (the case `above` of an `[any-taint]` fact, §4.1) |
| `a = b.f` | `(b, ., [any-taint], E, T)`, `f ∈ E` | nothing for `a` | |
| `a = b.f` | `(b, .f, [any-taint], E, T)` | `(a, ., [any-taint], E, T)` | normal |
| `a.f = b` | `(a, ., [any-taint], E, T)` | `(a, ., [any-taint], E ∪ {f}, T)`, by the keep edge `a.* →_{f} a.*` | normal (the exclusion edge, W8) |
| `a.f.g = b` | `(a, ., [any-taint], {}, T)` | `(a, ., [any-taint], {f}, T)` and `(a, .f, [any-taint], {g}, T)`, by the keep edges `a.* →_{f} a.*` and `a.f.* →_{g} a.f.*` | normal |
| `a.f = b` | `(b, .g, *, E, *)` | `(a, .f.g, *, E, *)`; under `L = 1`: `(a, .f, [any], {}, *)` | normal; under the cut: demand |
| `a.f = b` | `(a, .f, *, E, *)` | nothing (strong update) | |
| `a.f = b` | `(a, ., *, E, *)` | `(a, ., *, E ∪ {f}, *)`, no request | normal |
| `x = C.s` (run 1) | the identity static `*` edge to `(S, ., *, E, *)`, `<C> ∉ E` | `(S, ., *, E, *)`; nothing for `x`; the position request `[<C>, s]` | normal |
| `C.s = x` (run 1) | the identity static `*` edge to `(S, ., *, E, *)`, `<C> ∉ E` | `(S, ., *, E ∪ {<C>}, *)`; the class keep edge gives the position request `[<C>]` | normal |

The premise of the edge does not change in any case. Only its layer can change, from normal to demand. (`Cases.lean`
checks the fifth row with the mark `*`, which no `$` fact of the AP has, §7.2; with a concrete mark the result is the
same: no overlap.) The `[any-taint]` rows are not in `Cases.lean`. `AnyTaintEx.Vec.setter_keep` checks the keep row
by `decide` (the round-1 rule gave `(a, ., [any], {}, T)` in the demand layer: `setter_keep_base`,
`AnyTaintCases.W.keep_demand`); `AnyTaintEx.Vec.read_admitted` and `read_excluded` check the two read rows above the
fact; `AnyTaintExCases.X.two_results` checks the two-level write (together its two results cover exactly the
locations that are not at or below `a.f.g`, `locations_exact`; a write in one statement: on the JVM `a.f.g = b` is
`t = a.f; t.g = b`, a weak alias write, §11.1); `AnyTaintExCases2.G.r3_eJ1` derives the row
`(b, .f, [any-taint], {}, T)` in `AnyTaintEx.DRXs` (the getter `ret = p.f` of a must-premise; round 1
`AnyTaintCases.G.t3_eJ1`).

### 4.3 Apply a summary edge

`applySummary(a, j, g) = concat(a, j → g, edgeDemand = the layer of the summary edge)` (§4.1; Lean: `applySummary`).
The input `a` is the ADDED FACT of a link (§1), in callee coordinates; the result has the layer of `a` on that link
(§8.3) or a higher one. PRECONDITION: `a` SATISFIES the premise `j`. The caller tests it before it applies the
summary (§5.3 events E2 and E4); `applySummary` does not test it again.

* RUN 1: `j` covers `a` (strong enough):

  ```
  applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j has an any tail ⇒ a has an any tail)
  ```

  The application is the case `below`, and the mark gate passes (`applicable_mark`). The abstraction of run 1 covers
  every added fact (C1, §6.1). Lean: `coversB`, `applicable`, `applicable_sound`; reference form `applicable` (§3.4).
  Run 1 has no `[any-taint]` premise (W8 (c)). An `[any-taint]/E` added fact gives the policy fact (§6.2), and the
  result of a FLOW summary on it follows §4.1 (an `[any-taint]/E` fact `c`): for example the FLOW summary
  `(this, ., *) → (this, ., */{name})` of a setter `this.name = n` gives `(this, ., [any-taint], E ∪ {name}, T)`,
  normal (`AnyTaintExCases.S.record_app`, `run1_dto_ann`). (The model tests `applicable` without the exclusion of the
  added fact; a policy fact has the Empty exclusion, so the test gives the same result.)
* RESTRICTED RUN: the premise lies INSIDE the fact as LOCATIONS (the location part of `a` covers every location of
  `j`, marks ignored), and the marks of `a` are a subset of the marks of `j` (Lean: `satI`, `RCore.satI_markSub`,
  `satI_conc_record`; reference form `inside`, §3.4). So a concrete fact satisfies a `*` premise, and a cleaned fact
  `*∖X` satisfies a `*` premise. This is the reverse of run 1: the emitted fact of a concrete pattern is `a ∩ D-c`
  (§6.3), so it always lies inside its added fact (`RCore.emitM_satI`), and it can be smaller than `a` at the same
  path. The application is the
  case `below` if `a` is at or below `j`. It is the case `above` if `a` is above `j` (for example `a = (x, ., [any], T)`
  and `j = (x, .f, [any], T)`); then the result is in the demand layer (§4.1 step 3), unless `a` is `[any-taint]/E`:
  every admitted location of an `[any-taint]/E` fact carries its mark, so the case `above` loses nothing (§4.1).
  `inside` reads the exclusions of an `[any-taint]/E` added fact and of a must-premise as part of the location sets
  (§3.4): a premise `j` at the path of `a` needs the exclusion of `a` to be a subset of the exclusion of `j`; a premise
  strictly below `a`, at `a.path ++ r`, needs the exclusion of `a` to admit `r` (Lean: `AnyTaintEx.satX`, the base
  `satI` with `insideExB`; `satX_inside`).
* A FLOW PREMISE OF A RESTRICTED RUN (the mark `*`: the FLOW form of a `*` pattern, §6.3; F72) is satisfied by
  `inside` OR by `applicable` (Lean, PENDING: `satW`). The FLOW form does not depend on the added fact, so it can lie
  inside `a` (`a` at or above it), cover `a` (`a` at or below it, as a policy fact of run 1 covers its added fact),
  or neither. Both tests read the marks: a `*` premise admits every mark of `a`, also `*` and `*∖X`. A concrete
  premise is satisfied by `inside` only, as before F72. A fact with an abstract mark never satisfies a concrete
  premise: its marks are not a subset of `{T}`, so it gives nothing and raises no request (§4.5). A FLOW premise with
  the Empty exclusion covers the added fact or lies inside it at every common location (as a crossable `*` premise
  does, §8.7 R4), so one of the two tests holds. With an exclusion `E ≠ {}` this is false: the FLOW premise
  `(x, ., */{f}, *)` and the added fact `(x, ., */{g}, *)` have common locations, but neither test holds. Such a
  premise needs a `*` pattern with the tail `*/E`, and the hand-off gives none: a normal leaf with a `*` conclusion and
  a premise `$` or `*/{}` is crossable (§1), and every normal backward leaf with a `*` conclusion is crossable, so
  neither is a demand edge. So every `*` pattern has the entry tail `[any]`, and every FLOW premise has the Empty
  exclusion (§6.3; argued, PENDING §11.2).
* AN `[any-taint]` PREMISE (a must-premise; forward restricted runs only, §6.3) is satisfied only by `inside`: the
  added fact covers EVERY admitted location of the premise, so it has an any tail (a concrete fact has no `*` tail, W2) and lies at or
  above the premise. A summary of a must-premise is end-exact, not exact pair by pair (§1), so it needs every
  admitted location of the premise. A NORMAL result also needs a normal `[any-taint]` link: an `[any]` added fact (a
  demand link, §8.3) gives a demand result. (Lean: `AnyTaintEx.DRX`, rule `ret`, with the satisfaction `satX`; the
  exactness needs a satisfaction that reads `inside` with the exclusions, `AnyTaintEx.SatInsideX`, which `satX` has,
  `AnyTaintEx.satX_inside`; the summary closure form `AnyTaintExExact.summaryX_end`. Round 1, without the exclusion:
  `AnyTaint.SatInside`, `satI_inside`.)
* A RECORD `j → g` (§8.7) applies in the direction in which it was derived when `applicable(j, a)`, or when `a`
  satisfies `j` by `inside` (restricted runs), in every run after the run that made it (R4). In the other direction it
  applies through its reversal (R3, §9.1). A record is exact (S14; a must record is end-exact), so the result adds no
  false pair (a must record, applied by `inside`: no false end location), modulo the expected false-positive sources
  of §11.1 (a record through an end fact; a reversed backward record on a program with type filters). A record is not
  restricted.
  THE RECORD DEMOTION. A must record (an `[any-taint]` premise, §8.7) that applies by `applicable` only (the added fact
  lies inside the premise, and `inside` is false) gives its result in the DEMAND layer: the record needs every
  location of its premise, and the added fact has only some of them. By `inside` it gives the result of the
  application. The fact does not change, only the layer, and W8 (b) drops its exclusion (Lean: `AnyTaint.recLayer`,
  after the binding back and before the field limit (the two commute: both only raise the layer and drop the
  exclusion); `recLayer_fact`; with the exclusion `AnyTaintEx.recLayerX`). The
  demotion stays with the exclusion (it is not the demotion that the exclusion replaces), and it is necessary
  (`AnyTaintExact.CexApp.cex_app`): the must record
  `(p, ., [any-taint], T) → (ret, ., [any-taint], T)` of `get(p) { ret = p.g }`, applied at `x = get(dto)` to the
  added fact `(p, .f, [any-taint], T)` (the source `dto.f.[any-taint] (T)`), would give the normal
  `(x, ., [any-taint], T)`, but `p.g`, and so `x`, carries no taint.

The mark condition makes the mark gate pass: a summary application never raises a request (`Coverage.summary_step`,
`RCov.sat_step`, `RCore.summary_stepR`). A summary conclusion `*∖X` stops an added fact whose concrete mark is in `X`
(§4.1 step 5). In a restricted run the CALLEE restricts the summary by its demand patterns before it publishes it
(§6.4).

The special cases of the summary application:

* SEVERAL PREMISES. A summary with one premise, applied to a caller edge with a premise set, keeps the premise set of
  the caller edge. A summary whose premise set has two or more members (an ND summary `{j1, …, jk} → g`) applies
  through event E6: one added fact per member (§4.6, §5.3).
* THE BACKWARD RUN. The zero-premise summary of a callee applies to the zero fact of each caller with no restriction
  and no satisfaction test (§9.2, the balanced return).
* STATICS. A static initial fact is an ordinary premise: run 1 applies its summaries by `applicable`. An added fact
  above a static initial fact does not read its summaries; the position request (§4.10) makes the precise initial fact
  instead.
* FIELD LIMIT. The caller applies it after the binding back (§5.3 step 5, §4.4).

* The exclusion of a summary edge FILTERS the delta: the summary `(arg0, ., *) → (ret, ., */{f})` applied to the
  added fact `(arg0, ., */{})` gives `(ret, ., */{f})` (bound back to the lhs `r`), and applied to
  `(arg0, .f.g, $, T)` gives nothing. Applied to `(arg0, ., [any-taint], E, T)` it gives `(ret, ., [any-taint],
  E ∪ {f}, T)` in the layer of the added fact (the exclusion edge of §4.1).
* Run 1 never applies a summary to a fact that only overlaps its premise. Another initial fact of run 1 serves that
  fact.

### 4.4 The field limit

A run has the field limit `L`. The analyzer applies `limit_L` to every result of an operation that can make a path
longer. It never applies it to a micro edge or a summary edge before the application. The cut points:

* the statement transfer, after the micro edges and the lhs type filter (§4.2 step 6); this covers the read sources
  (`interpreter.md` §4.4);
* the call return, after the summary rewriter, the binding back and the aliases (§5.3 step 5); this covers the
  summary application, the record application and the unresolved callee;
* the source results and the end facts of a sink at a call, after their binding back and the aliases (§5.3 step 3);
* the results of the entry rules at the method start: the entry-point sources and the end facts of an entry sink
  (`interpreter.md` §4.3);
* the results of the exit rules at an exit (normal or exceptional), before the summary edge of the normal exit: the
  exit sources (also the conjunction result of a conjunctive exit source, §4.6) and the end facts of an exit sink
  (`interpreter.md` §4.7);
* the conjunction result (§4.6) and the application of a summary with several premises (§4.6, event E6);
* the backward seed (§9.2).

The cut:

* If the path has at most `L` counted accessors, the fact does not change.
* Otherwise, cut the path before the `(L+1)`-th counted accessor. Uncounted accessors before that point stay in the
  prefix. The tail becomes `[any]`, the exclusion Empty, the mark stays (also `*∖X`), and the edge goes to the demand
  layer. `L = 0` keeps the empty path. An `[any-taint]/E` fact over the limit becomes `[any]` too, and the cut drops
  its exclusion: the cut path is above the fact, so not every location below it carries the mark (W8;
  `AnyTaintEx.limitFX`, `AnyTaintEx.Vec.cut_drops`; the program `AnyTaintExCases.CUT.cut_reports`; round 1:
  `AnyTaintCases.Cut.cut_transfer`, `limitF_cut_demand`).

Run 1 needs `L ≥ 1` (S12 (d), §4.10). The class accessor
`<C>` is not counted, so a cut never stops strictly above a static position.

Lean: `cutPath`, `limitF`; `limitF_sound` (the cut only enlarges). The field limit is the only depth bound of the
analysis. Each run may have its own limit (`RCov.iteration_sound`). The bound W3 needs a limit that does not decrease
from run to run (§6.6).

### 4.5 Mark gate and mark request (run 1 only)

Some rules need a concrete mark `T`: a sink, a conditional source, a mark-specific pass rule, a literal of a
conjunction, and a cleaner on a partly cleaned fact. Such a rule can meet a fact with the mark `*`, or `*∖X` with
`T ∉ X`. Then the rule gives no fact for `T`. It raises the REQUEST `(m, i, T)` on the premise `i` of the fact, in its
method `m`. A rule that drops the fact without a request loses the flow. A rule that applies to such a fact lets
every mark through.

A request is always on a premise with an abstract mark (`Coverage.req_initial_star`). In run 1 the policy (§6.2) and
the position answers (§4.10 item 2) make such premises. So a request premise of run 1 is a policy fact
`(x, [], *, {}, *)` or a static position answer `(S, p, *, {}, *)`.

A request STANDS for the whole run. The callee `m` checks it against every LINK (added fact `a`, caller edge) of its
added fact store (§8.3) where `a` overlaps `i` (§3.2). It checks the links that exist when the request arrives, and
every link that arrives later. A new caller edge of an existing added fact is a new link too (§5.3, events E2 and E5).
For each link:

* If `a.mark = T`: ANSWER. Emit the initial fact `answer(i, a, T)`, the CHAIN ANSWER. It has the base and the path
  of the request premise `i` (the REQUEST CHAIN):
  * `(i.base, i.path, $, {}, T)` if `a` has the `$` tail and `a.path = i.path`;
  * otherwise `(i.base, i.path, i.kind, T)`: the request premise with the mark `T` (it keeps the exclusion of `i`).

  For a policy premise `(x, [], *, {}, *)` the answer is `(x, [], $, {}, T)` for the added fact `(x, [], $, T)`, and
  `(x, [], *, {}, T)` for every other added fact. The answer starts per §6.5: a `*` tail starts as `[any]` in the
  demand layer; a `$` tail stays `$` in the normal layer. The chain answer is never deeper than the request.
  The special case of a static premise is §4.10 item 4: if `i` is on `S` and `a` is at or below `i`, the answer is `a`
  itself with the mark `T`, not the chain answer.
* If `a.mark` is `*`, or `*∖X` with `T ∉ X`: PROPAGATE the request through the caller edge `(ic → c)` of the link:
  raise the request `(caller, ic, T)` (Lean: `climbsB`).
* Otherwise (`a.mark = T' ≠ T`, or `*∖X` with `T ∈ X`): do nothing.

One answer does not stop the request. The answered initial facts are initial facts like every other: callers read their
summaries (§5). Lean: `answerInit`, rules `answer`, `reqUp`; `answerInit_covers`, `answerInit_applicable`.

The check is per caller edge, not per added fact. Example (the sink needs `T`):

```
m(p)    { sink(p); }
B(v)    { m(v); }               A(u)    { m(u); }
main1() { s = srcU(); B(s); }   main2() { t = srcT(); A(t); }
```

`B` calls `m` first and gives the added fact `(p, [], *, {}, *)`. The sink raises the request `T` on the premise of `m`.
The request climbs to `B`, but `main1` has only the mark `U`, so nobody answers. Then `A` gives the SAME added fact
through a new caller edge. A request that checks only new added facts never climbs to `A`, and it loses the
vulnerability `main2 → A → m → sink`.

Requests exist ONLY in run 1. NO REQUEST AFTER RUN 1 (decision F72, rule R4; `ap-history.md` F72). A restricted
run, forward or backward, has NO REQUEST RULE: no raise, no answer and no climb (and no position request, §4.10). It
is not concrete (§6.3): a `*` demand pattern gives a FLOW premise, and the facts of a FLOW premise have abstract
marks. On a fact with the mark `*`, or `*∖X` with `T ∉ X`, an operation that needs the concrete mark `T` gives
NOTHING, with no request:

* the mark gate of a micro edge with the concrete premise mark `T` (§4.1 step 4);
* the literal of a conjunction (§4.6): the store keeps nothing;
* the `part` row of a cleaner of `T` (§4.7): the fact continues as `*∖(X ∪ {T})`;
* the sink check (§4.9): no effect;
* the emission under a concrete pattern (§6.3), and the satisfaction of a concrete premise, of a summary or of a
  record (§4.3, §8.7 R4).

THE RULE: ANALYSE WITH A CONCRETE MARK ONLY IF A CONCRETE-MARK DEMAND EXISTS. Run 1 keeps its requests. Their answers
make the concrete-mark summaries where the marks matter, and the hand-off gives them to the next run as concrete
demand patterns (or the crossable ones as records, §8.7 R5). The backward run keeps the concrete mark of such a
demand, so every later run has its concrete demand patterns too. The claim that this loses no flow (R6: every flow
that needs a concrete mark is demanded by a concrete pattern or crossed by a concrete record, and every flow that a
`*` pattern demands needs no concrete mark) is PENDING proof (§6.6, CONTRACT B WITH MODES; §11.2). BEFORE F72 a
restricted run was concrete, so no request rule could fire: `RCov.no_reqR`, `RExact.DR_no_request`,
`RMain.no_request_M`, and for the backward run, whose seeds have concrete marks, `BExact.DB_no_request`
(`BExact.CexSeed.cex_seed`: a seed with the mark `*` would raise one). These theorems are about the concrete design
(the emission `emitM` that copies the mark); the implementation asserted the absence of a request. F72 replaces this
reason (decision F35; `ap-history.md` F35, F72).

A position request (§4.10) works in the same way: it stands, it uses the request store (§8.8), and the events E2 and
E7 of §5.3 check it per link. Its answer and its climb are §4.10 items 2 and 3.

### 4.6 Mark conjunction: ND edges

A CONJUNCTIVE micro edge `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)` gives the mark `T` at `z.π` if every literal holds
at the statement. A literal tail `tj` is `$` (`ContainsMark`) or `[any]` (`ContainsMarkOnAnyField`). The target tail
`t` is `$` or `[any-taint]` (W7: no `*` tail): a conjunctive micro edge is a source (a pass rule has no mark literal,
`interpreter.md` §4.2), so an `[any]` target is a taint edge (S15). The interpreter makes the edge for a rule with
several mark literals (`interpreter.md` §4.2,
§5.3): at a call (its rule statement) and at an exit (the exit rule statement). An exit source whose condition
alternative has two or more positive literals is a conjunctive micro edge of the exit rule statement (`interpreter.md`
§4.7, D31), not a rule error.

* The CONJUNCTION STORE (§8.9) keeps, STANDING for the run, per (conjunctive micro edge, statement, literal index),
  each fact `c` at the statement (for a conjunctive exit source: at the exit) that:
  * OVERLAPS the literal pattern `xj.ρj.tj` (§3.2, marks ignored), and
  * passes the mark gate of the literal mark `Tj` (§4.1 step 4, so `c.mark = Tj`).

  It keeps the fact with the premise set of its edge (`{zero}` for a zero-to-fact edge, `{i}`, or a larger set). Lean:
  rule `conj` of `ND.DN`. The literal index is the place of the literal in its conjunctive micro edge. Each conjunctive
  micro edge has its own entries: two alternatives of one rule (two disjuncts of its condition, `interpreter.md`
  §4.2) are two conjunctive micro edges, and they never share an entry, also not for an equal literal pattern.
* If the mark gate gives the request `Tj` (a fact with the mark `*`, or `*∖X` with `Tj ∉ X`), the store keeps nothing
  and raises the request (run 1, §4.5; Lean: rule `reqConj`). In a restricted run the store keeps nothing and raises
  no request (F72, §4.5; before F72 every fact was concrete, so this never occurred). A literal has no static
  exception: on the static base it uses the mark request (§4.10 covers
  only the statement micro edges and the sinks).
* When a fact arrives, the store combines it with the stored facts of the other literals: one fact per literal, every
  combination. The result `z.π.t(T)` has the UNION of the premise sets WITHOUT THE ZERO FACT; if every input has the
  premise set `{zero}`, the result has `{zero}`. The zero fact adds no condition: it is at every node that an edge
  reaches (it passes every statement and enters every callee with every other added fact, §5.3), so `{zero, i}` and
  `{i}` hold at the same points (`NDZero.zero_everywhere`). The number of the members names the edge: `{zero}` a
  zero-to-fact edge, one member a fact-to-fact edge, two or more an ND edge. Then the field limit applies to the result
  (§4.4). Lean: the closure `NDZ.DNz` (`ND.DN` with the zero-drop) corresponds to the list model `ND.DN` edge by edge
  (`NDZero.dnz_to_dn`, `dn_to_dnz`), so its coverage, exactness and confirmation are the theorems of §10.10.
* The target of a conjunctive micro edge is not on the zero base (`NDZeroBase.NoZeroGen` item (d); `interpreter.md`
  §5.3).
* The result is in the demand layer if one input is in the demand layer, or if its literal does not COVER it
  (`!coversB lit c`: the input has a location that is not a location of the literal, for example an `[any]` input for a
  `$` literal, or an input above the literal) and the input is not `[any-taint]`. An `[any-taint]/E` input (normal)
  that overlaps its literal and passes its mark gate gives a NORMAL result also if the literal does not cover it:
  every admitted location of the input carries the mark, and the overlap reads `E` (§3.2: an excluded location
  overlaps nothing), so the literal holds at a common location (Lean: `AnyTaintND.conjLayerT`, `lit_loc`, for an input
  with the Empty exclusion; with `E` the rule is argued, §11.2). An `[any-taint]` target gives an `[any-taint]` result,
  with the Empty exclusion, in the layer of the conjunction (a must, S15; in the demand layer it is `[any]`, W8). Lean:
  `ND.conjLayer`, `ND.Example.c3_normal`; with the `[any-taint]` rule `AnyTaintND.DNzT` (`NDZ.DNz` with
  `AnyTaintND.conjLayerT`), its example `AnyTaintND.Example.layer_new`, `layer_old`, `confirmed`. A normal result is
  exact against the support semantics, under S7, S9, S10 and S13 (`NDExact.nd_edge_exact`; the valid form `nd_edge_exact_valid`; for
  the spec closure `NDZ.DNz`: `NDZeroThms.nd_edge_exact_z`, `nd_edge_exact_valid_z`; with the `[any-taint]` rule
  `AnyTaintND.nd_edge_exact_zT`, `nd_edge_exact_valid_zT`, under the same hypotheses).
* The engine is path-insensitive: the stored facts are per statement, not per execution path, so the literals can hold
  on paths that exclude each other (`if c then a := srcA else b := srcB; r := f(a, b)`). This is the EXPECTED
  over-approximation; it does not move the result to the demand layer. The reference semantics of a conjunction
  (`ND.TaintN`, below) is path-insensitive in the same way.
* An ND edge propagates through micro edges with its premise set unchanged. Its conclusion is uncorrelated (`$` or an
  any tail; W7): a `*` tail is the correlation with ONE premise.
* An edge whose premise set has two or more members (an ND edge) is ALWAYS a TAINT edge (§7.2), never REACH or FLOW.
  No member is the zero fact (above), and every member has a concrete mark: an input of a conjunction
  passes the mark gate of its literal (a concrete mark, S9), and a fact with a concrete mark has a premise with a
  concrete mark or the zero premise (`Kinds.flow_abstract`, S7; directly `Kinds.nd_taint`, `ndz_taint`). The members
  of a summary with several premises applied at a call (event E6) are concrete for the same reason (§4.3: a concrete premise is satisfied only by a concrete added
  fact). The conclusion has a concrete mark and no `*` tail (W7). Lean: `Kinds.nd_taint` (`ND.DN`), `Kinds.ndz_taint`
  (`NDZ.DNz`: also no zero member).
* At a call, the callee sees an ordinary added fact. A callee summary `j → g` with one premise, applied to a caller
  edge with a larger premise set, keeps the premise set of the caller edge. A callee SUMMARY WITH SEVERAL PREMISES (its
  premise set has two or more members: an ND summary `{j1, …, jk} → g`) needs one link at the call statement per
  member `jm`: an added fact that satisfies `jm` (§4.3), with its caller edge. The rule is standing: the link that
  arrives last completes it (event E6 of §5.3; the store of §8.9). The result has the union of the premise sets of the
  caller edges, without the zero fact. It is in the demand layer if the
  summary is, or if one added fact of the combination is in the demand layer on its link (§8.3; Lean: `ND.DN.ndBind`).
  Then the caller binds it back and applies the field limit (§5.3 step 5). In a restricted run the callee restricts
  such a summary before it publishes it (§6.4). A conjunctive exit source (above) makes such a summary too: a full
  combination at the exit is an exit item with the union of the premise sets, after the field limit; it takes the
  rest of the exit order and becomes a summary at the normal exit (`interpreter.md` §4.7, D31); with two or more
  members it is an ND summary, which the callers apply by event E6.
* An edge whose premise set has two or more members is never a record: the analysis never persists it and never
  reverses it (§8.7 R1). The backward run reverses a conjunctive micro edge into one micro edge per literal, with every
  result in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION; §9.2).
* The model has binary conjunctions (`ND.Conj`: two literals). A conjunction of `k` literals is argued by chaining
  (§11.2).
* A conjunctive sink (positive literals on several positions) uses the same store (§4.9, §8.9). The model has no
  conjunctive sink; it is argued (§11.2).
* The concrete semantics of a conjunction is the SUPPORT semantics of §3.5 (`ND.TaintN`); a vulnerability witness is a
  tree.

Lean: `ND.lean` (§10.6).

### 4.7 The cleaner

A cleaner `clean(position, reach, mark)` at a statement removes the mark `T` (or every mark) from the locations of its
position `x.p`. The reach is `exact` (`x.p` only), `below` (everything strictly below `x.p`, the position `x.p.*`) or
`atAndBelow`. (The reach `below` excludes `x.p` itself; the case `below r` of §4.1 includes `r = []`.) In the
concrete semantics (§3.5) a location keeps its value unless the cleaner cleans it (Lean: `Cleaner`, `Cleaner.cleansB`,
`Flow.clean`).

The cleaner compares the location set of a fact `c` with the cleaned locations, marks ignored: `inside` (every location
is cleaned), `disjoint` (no location is) or `part` (some locations are). The test is exact (Lean: `cleanPos`):

| `c` against the position `x.p` | `exact` | `below` | `atAndBelow` |
|---|---|---|---|
| another base, or apart | `disjoint` | `disjoint` | `disjoint` |
| strictly below (`c.path = p ++ r`, `r ≠ []`) | `disjoint` | `inside` | `inside` |
| at (`c.path = p`), tail `$` | `inside` | `disjoint` | `inside` |
| at, tail `*/E` or an any tail | `part` | `part` | `inside` |
| strictly above (`p = c.path ++ r`), tail `$` | `disjoint` | `disjoint` | `disjoint` |
| strictly above, tail `*/E` or `[any-taint]/E` | `part` if `E` admits `r`, else `disjoint` | the same | the same |
| strictly above, tail `[any]` | `part` | `part` | `part` |

The result:

| `c.mark` | cleaner mark | `inside` | `disjoint` | `part` |
|---|---|---|---|---|
| `*` or `*∖X` | `T` | `c` with `*∖(X ∪ {T})` | `c` | `c` with `*∖(X ∪ {T})`; if `T ∉ X`, also the request `T` on the premise of `c` (run 1; a restricted run raises no request, F72) |
| `*` or `*∖X` | every mark | dropped | `c` | `c` in the demand layer, normalised: a `*` tail becomes `[any]` (W2) |
| `T` (cleaned) | `T` or every mark | dropped | `c` | the part that the cleaner does not surely clean: a fact with an any tail at `x.p` under a `below` cleaner becomes `(x, p, $, T)`, in the layer of `c` (an `[any-taint]` fact keeps the normal layer); a normal `[any-taint]/E` fact at `x.q` under a cleaner ONE ACCESSOR BELOW it, at `x.q.f` (so `p = q ++ [f]`, and `E` admits `f`): `atAndBelow` gives `(x, q, [any-taint], E ∪ {f}, T)`, and `below` gives `(x, q, [any-taint], E ∪ {f}, T)` and `(x, q.f, $, T)`, both in the layer of `c`; any other `c` goes to the demand layer (it has a concrete mark, so it has no `*` tail, W2; an `[any-taint]/E` fact becomes `[any]` with the Empty exclusion, W8: under the `exact` cleaner at `x.q` or at `x.q.f`, which has no shape for "every location but one", and under every cleaner two or more accessors below `x.q`; the cleaner demotions of §2.2) |
| `T'` (not cleaned) | `T` | `c` | `c` | `c` |

Lean: `cleanRes`, `addEx`, `concPart` (§11.2 gives the difference to the model in the first row). With the exclusion:
`AnyTaintEx.cleanPosX`, `partX`, `cleanResX`; the vectors `AnyTaintEx.Vec.clean_atAndBelow`, `clean_below`,
`clean_exact`, `clean_excluded`; the program CL (`AnyTaintExCases.CL.atAndBelow_result`, `below_result`,
`exact_result`); the rows are exact (`AnyTaintExExact.cleanResX_exact`, `clean_rows_exact`; the new `$` fact of the
`below` cleaner is real, `below_new_fact_real`), and the `exact` cleaner must demote
(`AnyTaintExExact.CexExactCleaner.cex_exact_cleaner`: `[any-taint]/{f}` would miss the real `x.f.g`, a soundness
loss, and a normal `[any-taint]/{}` would claim the cleaned `x.f`).

So the cleaner SPLITS a `*`-mark fact by the mark. The edge `*∖{T}` propagates every mark except `T`, exactly, in the
normal layer. The mark `T` goes through the cleaner only on the concrete answer of the request, which the cleaner cleans
exactly (except on `[any]`, which is in the demand layer already). After run 1 it goes through only on a fact of a
concrete demand pattern (F72, §4.5). The union of the two covers every real flow
(`Core.cleanRes_sound`, `Coverage.coverage`); a normal result denotes only real flows (`Exact.cleanRes_exact`).

* A summary conclusion `*∖X` stops an added fact with a concrete mark in `X` (§4.1 step 5). A sink for `T ∈ X` on a
  `*∖X` fact neither triggers nor requests (§4.9). A request for `T ∈ X` does not climb through a `*∖X` fact (§4.5).
* The mark exclusion is not tied to a position, so a field write, a field read or a cut does not change it.
* A fact that the cleaner surely cleans (`inside`) needs no request: the `T` path can only make a fact that the
  cleaner drops.
* IN A RESTRICTED RUN (F72) a fact can have an abstract mark: a fact of a FLOW premise (§6.3). The rows with an
  abstract mark apply WITH NO REQUEST: a cleaner of `T` gives `c` with `*∖(X ∪ {T})` (`inside` and `part`), and the
  mark `T` through the part that the cleaner does not clean comes only from a concrete demand pattern (§4.5). The
  all-marks rows do not change (they raise no request). Before F72 every fact of a restricted run was concrete
  (`RExact.DR_concrete`, for the emission that copies the mark, for any records): only the rows with a concrete mark
  applied, and no `*∖X` fact occurred. A reused run-1 record with a `*∖X` conclusion gives a concrete mark on a
  concrete fact, or nothing, and `*∖(X ∪ Y)` on a fact with the mark `*` or `*∖Y` (§4.1 step 5).
* THE STATIC BASE (run 1). A request that the cleaner raises on a static premise is answered as §4.10 item 4 says. A
  cleaner on `S` names its mark (S12 (e)): the all-marks `part` row makes an `[any]` static fact above a static
  position. A `RemoveAllMarks` rule on a position of `S` is not a cleaner: it is the kill of a strong write, a
  statement summary with keep edges (`interpreter.md` §1.4). One exception: the WHOLE-BASE CLEANER `(S, atAndBelow,
  all)` with the empty path (`AnyClassStatic`, S12 (e)). Every fact on `S` lies inside it (the `inside` row), so it
  drops the fact whole: it raises no request and makes no `[any]` static fact.
* THE ZERO BASE. No cleaner is on the zero base (S11 (d)).
* The interpreter places the cleaner (`interpreter.md` §5.2): at a call to a cleaner method, on the bound facts before
  they enter the callee, and on the facts of an unresolved call before its pass rules. The model has no cleaner inside
  a call (a cleaner is an instruction of the CFG, `Instr.clean`), so the call cleaners are argued (§11.2).
* THE SUMMARY REWRITER (`interpreter.md` §5.2) is not a cleaner placement. It is a RULE-GUIDED OVERRIDE of the callee
  flow: a user-defined rule replaces the real data flow of the callee for its marks at its positions. It acts for the
  calls that user-defined rules cover. It selects:
  * every user-defined SOURCE rule of the call whose condition is not statically false;
  * every user-defined CLEANER rule of the call only if it is UNCONDITIONAL: its condition is statically true.

  It never selects a rule that a rule error rejected (`interpreter.md` §1.3, §5.2): such a rule has no form at all.
  For each selected rule, each relevant mark `T` of the rule and each action position `P` of the rule, it applies
  `clean(P, exact, T)` for a position with no `AnyField`. For an `AnyField` position `P.[any]` it applies
  `clean(P, atAndBelow, T)` if the rule is a source (`interpreter.md` D34: today's code gives `(P, below, T)`, the
  spec text before F69 gave `exact`), and the cleaner of its row of `interpreter.md` §5.2, `clean(P, below, T)`, if
  the rule is a cleaner (`RemoveMark(T, P.AnyField, …)`; as today, `JIRMethodCallRuleBasedSummaryRewriter.kt:105`).
  It applies them to the summary results and to the unresolved results of the call, before the binding back (§5.3
  step 5). The source writes every location at or below `P` (an `[any-taint]` result, S15), so the rewriter cleans
  them all; `exact` would keep the callee results below `P`. The override is by design:
  it is part of the reference semantics of the rule (§3.5). So the cleaner rule of the last item of this list does not
  govern it, but the rewriter agrees with it: a conditional user-defined cleaner does not act through the rewriter, as
  it does not act at the call. The rewriter is argued with the call cleaners (§11.2).
* THE BACKWARD RUN. A cleaner is its own reversal (§9.2). `interpreter.md` §4.9 places it on the requirement at the
  callee start.
* `clean` is unconditional. Only an unconditional cleaner acts. A cleaner rule whose condition keeps a mark literal
  after the static evaluation does not act (`interpreter.md` §4.2): the fact does not decide such a condition, and
  cleaning there is unsound. The summary rewriter (above) selects a cleaner rule only if the rule is unconditional.

### 4.8 The type filter

A type filter `filter(b, may)` at a statement drops a fact on the base `b` whose path cannot exist on a value of the
static type of `b`. `may` is a predicate on paths. Contract (S5):

* `may` accepts every path that a real value of the static type can have;
* `may` is PREFIX-CLOSED: `may(p ++ q) ⇒ may(p)`.

Then a fact that covers a real location has a path that `may` accepts (its path is a prefix of the path of the
location), and the filter never drops it (`Core.filt_keeps`). Lean: `Instr.filt`, `Flow.filt`, rule `filt`;
`Program.WF.filtPrefix`.

The filter checks the concrete path of the fact only. It keeps a `*`, an `[any]` or an `[any-taint]` tail whole. The
analysis does not store a filter in a fact or an edge, and it does not propagate a filter to later statements. So a
`*`, `[any]` or `[any-taint]` fact that passes a filter can still denote locations below its path that the filter
rejects (`Exact.CexFilt`). Those
locations do not exist on a real value. On the JVM this is an expected false-positive source (§11.1).

So the exactness theorem holds for VALID locations only: the end locations that every filter accepts
(`Exact.edge_exact_valid`, `closed_exact_valid`, `Closed.closed_records_exact_valid`). The validity predicate is the
assumption S13 (§0.1), with three parts:

1. every type filter accepts every valid location of its base (`Exact.FiltValid`);
2. the validity goes back along every statement micro edge and along every call binding, into the callee and back: a
   valid end location of the edge comes only from a valid start location (`Exact.BackOK`);
3. with conjunctions, the validity goes back from the target of a conjunctive micro edge (§4.6) to each literal: if a
   location of the target is valid, every location of each literal is valid (`NDExact.ConjOK`; without it the valid
   form of the ND exactness is false, `NDExact.CexConjOK.cex_conjOK`).

The type-filter placement of the interpreter makes S13 true (`interpreter.md` §5.1). A confirmation (§4.9) needs a
sink pattern whose locations are valid (`Confirmed.confirmed_real_valid`; `Confirmed.CexConfFilt` shows that the
condition is necessary in the model: its program breaks W6 and S8).

The interpreter places the filters (`interpreter.md` §5.1 gives the table). The mark policy (a concrete mark on a
primitive value) is NOT a type filter: it reads the mark, the model has no mark filter, and it can drop a real flow, so
it is outside S5 (`interpreter.md` G6). The AP has no summary-side filter (`interpreter.md` D13, D14). Without a
filter the analysis only adds facts, so this is sound and costs precision (`interpreter.md` Q3).

The special cases: the backward run applies no type filter (§9.2; §11.2 gives the difference to the model); a type
filter on the zero base accepts the empty path (S11 (d)); Go has no type filter (`interpreter.md` §2.3).

### 4.9 Sink check and confirmation

A sink checks the pattern `s = (v, ρ, t, T)` with the tail `t = $` (`ContainsMark`) or `t = [any]`
(`ContainsMarkOnAnyField`). For an edge `(i, layer) → f` in the method `m`:

* If `f` and `s` do not overlap (§3.2, marks ignored): no effect.
* If `f.mark = *∖X` with `T ∈ X`: no effect (the mark was cleaned).
* If `f.mark = T'`: the sink is TRIGGERED if `T' = T`; otherwise no effect.
* If `f.mark` is `*`, or `*∖X` with `T ∉ X`: in run 1 raise the REQUEST `(m, i, T)`. Here `i.mark` is abstract too:
  a concrete premise has only concrete conclusions (`Coverage.edge_conc`). The implementation asserts it (§11.2 gives
  the difference to the model). IN A RESTRICTED RUN (F72): no effect and no request (§4.5). Such a fact is a fact of a
  FLOW premise (§6.3). So a sink fires only on a fact with a concrete mark, under a concrete premise or the zero
  fact. The method of a sink gets a concrete demand pattern from its seed (§9.2), and the chain of calls down to it
  stays concrete, so the confirmation does not change (R6; PENDING, §6.6, §11.2). (Before F72 a restricted run had
  no such fact, and the implementation asserted it.)

Examples: `(x,.,$,T)` triggers, `(x,.f,$,T)` does not, `(x,.,[any],T)` triggers, `(x,.,[any-taint],T)` triggers (as
`[any]`: the same location set), `(x,.,*,{},*)` raises the request `T`. For the pattern `(x, .f, $, T)`: the fact
`(x, ., [any-taint], {f}, T)` does not trigger (an excluded location overlaps nothing, §3.2), and
`(x, ., [any-taint], {g}, T)` triggers. Lean: `check`, `check_sound`, `check_request_star`; with the exclusion
`AnyTaintEx.checkX`, `AnyTaintEx.Vec.check_vectors`. An `[any-taint]` sink fact is normal, so its sink edge can be
confirmed (below): a common ADMITTED location of the sink fact and the sink pattern is reached
(`AnyTaintExExact.sink_denX`; round 1 `AnyTaintExact.sink_den`). A sink on the static base `S`
uses this check too: in run 1 the request on a static premise is answered by the added fact itself (§4.10 item 4).

An UNCONDITIONAL SINK has no positive mark literal: it has no literal, or every literal is negated (a negated literal
counts as true, §3.5). Its sink pattern is the zero fact `(zero, [], $, {}, zeroMark)`, so it triggers on the zero fact
at the sink statement. Its sink edge is the edge of the zero fact there: the premise set `{zero}`, the conclusion the
zero fact, in the normal layer. The three conditions below confirm it if the premise set `{zero}` is supported
(condition 3): at a root, or through a chain of calls whose caller edges are the zero edges of the callers.

A CONJUNCTIVE SINK has positive mark literals on several positions (`interpreter.md` §4.2). Each literal is a sink
pattern. The conjunction store (§8.9) keeps, standing for the run, per (sink alternative, statement, literal index),
each sink edge whose check of that literal triggers. The literal index is the place of the literal in its sink
alternative (§1). Two alternatives of one rule never share an entry. A check that gives the request raises it (run 1).
When every literal of one alternative has a stored edge, each combination (one edge per literal) is a SINK EDGE SET of
the vulnerability, with the set of the sink facts. The vulnerability store keeps every sink edge set as a sink witness
(§1) under the one key of the vulnerability (§8.10). A sink edge set is in the demand layer if one of its edges is.

END FACTS. A sink rule can have end-fact actions (`interpreter.md` §4.1, END FACTS). An end-fact action gives the
zero-to-fact edge `Zero → (sink statement, P.$ (T))` (`P.[any-taint] (T)` for an `AnyField` position, `interpreter.md` I14). It takes no input fact: when a sink edge triggers, or when a
conjunctive sink completes a combination, it applies to the zero fact in the layer of that sink edge or of that
combination (§2.2). Its premise set is `{zero}`, whatever the premise set of the sink edge: an end fact is
context-insensitive (§11.1).

THE BACKWARD RUN has no sink check. Its sink rule is the seed (§9.2). An end fact exists only after its sink
triggers, so the reversed end-fact edge of a sink alternative also fires the sink seeds of that alternative (§9.2, THE
TRIGGER OF AN END FACT).

A sink witness (§1) is CONFIRMED only if all three conditions hold:

1. Each sink edge of the witness is a normal edge (also with the `[any-taint]/E` tail: the test reads the layer only;
   Lean: `AnyTaintEx.Confirmed6X`, `ConfirmedX`; round 1 `AnyTaint.ConfirmedT6`, `ConfirmedT`,
   `AnyTaintND.ConfirmedNzT`).
2. Each member of the premise set of the sink edge (§4.6; the zero fact is a member like every other) is the zero fact,
   an EXACT concrete fact `(x, p, $, T)` (a request answer in run 1, an emitted fact in a restricted run), or, in a
   forward restricted run, a must-premise `(x, p, [any-taint], E, T)` (an emitted fact, §6.3).
3. The premise set is SUPPORTED JOINTLY (Lean: `Confirmed.Sup` in run 1, `RExact.SupM` in a restricted run,
   `NDConfirmed.SupN` with conjunctions). Support is a property of the premise SET (§1):
   1. At a root, the premise set is supported if every premise is the zero fact.
   2. In a callee, the premise set `{j1, …, jk}` is supported if ONE call statement to the callee supplies every
      premise. For each member `jm` there is a normal caller edge `(Pm, normal) → cm` at that call statement with these
      properties:
      1. its own premise set `Pm` is supported (the rule applies again in the caller);
      2. the binding of `cm` gives the added fact `a`, and `a` is in the normal layer on that link (§8.3);
      3. `jm = a`: the same base, path, tail and mark. So `jm` and `a` are the zero fact, or `a` is exact with a
         concrete mark: `jm` is the answer of `a` in run 1 (the chain answer of §4.5, or, on a static premise, the
         added fact itself, §4.10 item 4), or the emission `a ∩ D-c = a` in a restricted run. OR (a restricted run)
         `a` has the `[any-taint]` tail (so it is normal on the link) and `jm` lies inside `a` (`inside`, §4.3, with
         the exclusions) with the SAME concrete mark, and `jm` is an exact fact `$` or a must-premise `[any-taint]`.
         This branch also holds for `jm = a`, the emission `a ∩ D-c = a` of an `[any-taint]/E` added fact. Every
         admitted location of `a` carries its mark, so every location of `jm` is supplied. (Lean:
         `AnyTaintEx.SupLinkX`, `SupX`; round 1 `AnyTaint.SupLink`, `SupT`. The same mark makes the condition
         explicit: for a concrete premise, as in a restricted run, `inside` already implies it,
         `AnyTaintExact.markSub_conc`; without it `AnyTaint.SupLink` would accept a premise with the mark `*`
         inside `a`, whose locations with other marks `a` does not carry, `AnyTaintExact.CexSupMark.cex_sup_mark`.)

      Different premises can use different caller edges at that one call, and those caller edges can be supported
      through different calls of the caller. So the support is a tree.
   3. No other premise set is supported.

   For one premise this is the chain of supported caller edges. The weaker condition "the premise is exact" is not
   enough (`Confirmed.Weak.weak_support_gap`, a proved counter-example). For two or more premises, "each premise is
   supported at some call" is not enough: two premises supplied at two different calls never meet at one execution
   (`NDConfirmed.CexSites.cex_sites`).

A conjunctive sink is a conjunction to a fresh target with a sink on it: it is confirmed if every sink edge of its set
is normal and the UNION of their premise sets (without the zero fact, §4.6; `{zero}` if every edge has `{zero}`)
is supported jointly (condition 3). A conjunction is the expected
over-approximation of a path-insensitive engine (§4.6), so a vulnerability through a normal conjunction result can be
confirmed: it is real for the path-insensitive support semantics `ND.TaintN` (`NDConfirmed.confirmed_real_N`,
`confirmed_real_N_valid`; for a program without conjunctions the rule is the one of `Confirmed.confirmed_real`,
`NDConfirmed.confirmedN_iff`).

The analyzer computes the support and the confirmation only for a COMPLETE run (§1), at its fixed point (S6), after
the last event: condition 3 is a least fixed point over the caller edges, and it can change until the run ends. An
incomplete run confirms nothing (§8.10).

A vulnerability (§1) is confirmed in a run if one of its sink witnesses of that run is confirmed; otherwise it is a
demand vulnerability of that run (§1). Its state in the report is DEMAND (a DEMAND vulnerability, §1) if no complete
forward run confirmed it so far (§8.10). A result of an `[any]`-target source is `[any-taint]` (W8), so a
vulnerability whose taint comes from such a source CAN be confirmed. In run 1: when the sink reads the tainted object
in the method of the source (`AnyTaintExCases2.PassRule.source_confirmed`); also after a setter of one field (program S:
`root() { dto = srcAny(); dto.setName(c); sink(dto.name); sink(dto.email); }`, `setName(n) { this.name = n; }`; the
setter gives `(dto, ., [any-taint], {name}, T)`, normal, so `sink(dto.email)` is confirmed,
`AnyTaintExCases.S.run1_email_confirmed`, and `sink(dto.name)` is not reported at all, `run1_name_not_reported`: it
is not real, `name_not_real`); or after a callee whose FLOW summary keeps the whole object (program I,
`AnyTaintExCases2.I.run1_confirmed`). In a restricted run also through a callee: a getter (program G,
`AnyTaintExCases2.G.run3_confirmed`, also with the hand-off of the backward run, `run3_confirmed_handoff`) or a sink in
the callee (program C, `AnyTaintExCases2.C.run3_confirmed`: the must-premise is supported through the must branch of
`AnyTaintEx.SupLinkX`, `AnyTaintExCases2.C.run3_supported`). Run 1 does not confirm program G: the FLOW summary of the
getter is the case `above` of a policy fact, a demand edge (`AnyTaintExCases2.G.run1_flow_above`,
`run1_not_confirmed`); the must-premise that the demand gives in run 3 confirms it (`AnyTaintExCases2.G.run3_must`).
(These are the round-1 programs G, C, I and P, re-derived in `AnyTaintEx.D6X` and `AnyTaintEx.DRXs`; §10.11. Run 3
uses the earlier restriction `AnyTaintEx.restrictX` and the earlier hand-off; with the intersection and the hand-off
of the demand edges the same results are checked by hand, §11.2.) A
strong write into the object does not demote it: the exclusion removes only the written field (`AnyTaintExCases.X.fh_confirmed`,
`fg_not_reported`); without the exclusion a normal result would confirm the overwritten field, which is not real
(`AnyTaintCases.W.keep_normal_confirms_unreal`). A vulnerability that rests only on a may `[any]` (a pass rule with an
`AnyField` target, `AnyTaintExCases2.PassRule.pass_not_confirmed`) or on another demotion of §2.2 (the list is there;
for example the field limit cut, `AnyTaintExCases.CUT.cut_reports`; the `exact` cleaner below the object,
`AnyTaintExCases.CL.exact_result`) stays a
demand vulnerability, and the output holds it as a DEMAND entry (§8.10).

`Confirmed.confirmed_real_valid` (run 1, under S7, S10 and S13) and `RExact.confirmed_realM_gen_valid` (every forward
restricted run, also under S14; the support `RExact.SupM`; the satisfaction `satI`; the restriction of §6.4 by
`Handoff.restrictI_sub`; the instance with the earlier restriction is `RMain.confirmed_real_M_valid`) prove that a confirmed
vulnerability is real for the reference semantics (§3.5), for a sink pattern whose locations are valid (§4.8). The
forms without the validity condition (`Confirmed.confirmed_real`, `RMain.confirmed_real_M`) are for programs without
type filters (`Exact.FiltUp`). On the real program, a confirmed vulnerability is real modulo the expected
false-positive sources of §11.1. These theorems are about the closures `D` and `DR`, which have no static rule.
With the static rule of §4.10, `StaticsConfirmed.confirmed_realS` and `confirmed_realS_valid` prove it for run 1: the
support of condition 3 then also accepts the mark answer on a static premise (§4.10 item 4: the added fact itself).
With the `[any-taint]` tail and its exclusion (the closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX`, §10.11): run 1,
under S7 and S13 (`AnyTaintExExact.confirmed_real_valid6X`; for `Exact.FiltUp` `AnyTaintExExact.confirmed_real6X`);
a forward restricted run, under S7, S13, the records of S14 (`AnyTaintEx.RecsExactX`, `AnyTaintExExact.RecsConcX`,
`RecsWFX`) and the three properties of the rules `AnyTaintEx.SatInsideX`, `EmitCopiesMarkX` and
`AnyTaintExExact.RestrictOKX` (`AnyTaintExExact.confirmed_realX_valid`; for `Exact.FiltUp`
`AnyTaintExExact.confirmed_realX`; the spec rules have the three properties, the restriction by
`HandoffX.restrictIX_ok`; the instance with the earlier restriction is `AnyTaintExExact.confirmed_realXs`); every
restricted run of the run sequence when every record is an exit edge of an earlier forward run of the same program
(`AnyTaintExExact.RecsFromRunsX`), with no exactness hypothesis on the records (`seq_confirmed_realX_valid`); with
the reversed backward records and with the source seeds this is argued (§8.7 R4,
§11.2). With conjunctions: `AnyTaintND.confirmed_real_NzT_valid` (run 1; `AnyTaintND.DNzT` has no W6T and no
exclusion: both are argued, §11.2). The sink edge can be `[any-taint]/E`: the sink pattern must meet an ADMITTED
location of it (`AnyTaintEx.checkX`), and a supported must-premise has all its admitted locations entry-reachable
(`AnyTaintExExact.sup_entryX`).

### 4.10 Statics in run 1: the position request

The static base `S` holds every static field at the path `[<C>, f]`: the class accessor `<C>` (not counted by the field
limit) and the field `f`. A Go global `G` is at the path `[<G>]`. A rule can also put a concrete mark on a class
position `[<C>]` with no field, for example `(S, <C>, $, {}, T)`. The run-1 static fact is abstract: the policy fact
`(S, ., *, {}, *)` (§6.2). An operation whose premise is below an abstract static fact is the case `above` of §4.1, and
the ordinary result is `[any]` in the demand layer. In run 1 the static base uses a POSITION REQUEST instead. So no
static fact with the `[any]` tail occurs above a static position (`Statics.no_any_above`). The same holds for the
`[any-taint]` tail: the model has one kind `.any` for both any tails, and a source with an `[any]` target on a bare
class is a rule error (S12 (b); `interpreter.md` §1.4). (This is proved for `Statics.DS`, which has no W6T and no
exclusion; with them it is argued, §11.2.) The rule needs the construction rules S12.

IDENTITY STATIC `*` EDGE. A propagation edge `i → f` with the premise `i = (S, q, */E0, *)` and the conclusion
`f = (S, q, */E, *)` or `f = (S, q, */E, *∖X)` at the same path `q`, in the normal layer (Lean: `Statics.idEdgeB`).
The rule fires only at the root path `q = []` or at a CLASS `q = [<C>]` (a position answer of item 2 at a class).
Below a static field the ordinary rules apply, as for an instance field. A Go global `[<G>]` is a static field, not a
class. (No Go statement micro edge reads below `[<G>]`, `interpreter.md` §2.3, so this case never occurs. The model
test `Statics.genFireB` reads "at most one accessor"; for these programs it gives the same result.)

1. RAISE (Lean: rule `sreqStmt`; `Statics.genFireB`). This is the one place of the rule; §4.1 (static exception),
   §4.2 and `interpreter.md` §2.1 step 4 point to it. Let `i → f` be an identity static `*` edge at the root path `[]`
   or at a class `[<C>]`, in the method `m`. Every STATEMENT MICRO EDGE whose premise is on `S` at the path
   `p = q ++ r`, with `r ≠ []` and `E` admitting `r`, gives NO fact and NO mark request on this edge. It raises the
   position request `(m, i, p')`, where `p'` is `p` cut to at most two accessors: the static field `[<C>, f]` or the
   class `[<C>]`. This holds for every such micro edge, for every target base, premise tail and premise mark: a read
   `S.<C>.f.* → x.*` (`x = C.f`, `p' = [<C>, f]`), a Go read `S.<G>.* → x.*` (`x = G`, `p' = [<G>]`), the class keep
   edge `S.<C>.* →_{f} S.<C>.*` of a write `C.f = v` or of a `RemoveAllMarks` kill (`p' = [<C>]`), a pass rule or a
   conditional source whose premise is on a static field (at a statement, at a call or at an exit).
   * A statement micro edge AT A CALL acts on a fact of the caller edge `(i → c)`: a source of the rule statement of
     the call and a `RemoveAllMarks` kill on `S` act on the bound fact, a pass rule of an unresolved callee on the
     added fact (§5.3 steps 3 and 4). The binding `S.* → S.*` does not change the path, so the test reads the caller
     edge `(i → c)` in the caller `m`, and the position request is `(m, i, p')`.
   * The RULE STATEMENTS OF THE METHOD BOUNDARIES are statement micro edges too: the entry rules at the method start
     (`interpreter.md` §4.3) and the exit rules at an exit (`interpreter.md` §4.7). They act on a fact `c` of an edge
     `(i → c)` of `m`, so a conditional exit source whose premise is on `S` strictly below an identity static `*` edge
     raises the position request `(m, i, p')`. (The entry-point sources are unconditional: they read only the zero
     fact. The touched bases and the keep edges of these rule statements: `interpreter.md` §4.3, §4.7. A conjunctive exit
     source is a conjunctive micro edge: its literals use the conjunction store and, on `S`, the mark request, §4.6.)
   * The other micro edges of the statement apply as usual, so the kill stays (§4.2). The root keep edge
     `S.* →_{<C>} S.*` of a write (Go: `S.* →_{<G>} S.*`) is at `q = []`, not strictly below it: it applies and adds the
     class accessor to the exclusion (§4.2, the static rows of the table).
   * A SINK on `S` raises no position request: it uses the ordinary sink check and mark request (§4.9, §4.5), and item
     4 answers the request.
   * Below a static field (an identity edge at `[<C>, f]` or deeper, or a static fact that is not an identity edge) the
     ordinary rules apply: a deep read is the case `above` of §4.1 and gives `[any]` in the demand layer, as for an
     instance field (on an `[any-taint]/E` static fact it follows the `[any-taint]` table of the case `above`).
2. ANSWER (rule `sanswer`). The position request stands for the run. An added fact `a` of `m` that overlaps `(S, p)`
   and is AT OR BELOW `p` answers it: the answer is the initial fact `(S, p, *, {}, *)` of `m`, with the identity start
   edge in the normal layer (§6.5). An added fact above `p` does not answer. Callers read the summaries of the answer
   as usual (§4.3).
3. CLIMB (rule `sreqUp`). For every link of `m` (existing or later) whose caller edge `ic → c` has its premise `ic` on
   `S`, and whose added fact overlaps `(S, p)` and is ABOVE `p`: raise the position request `(caller, ic, p)`. The
   first caller that has an added fact at or below `p` answers, and the precise fact goes down the calls.
4. MARK ANSWER ON A STATIC PREMISE (Lean: `Statics.SCtx.ansInit`). For a mark request `(m, i, T)` (§4.5) whose premise
   `i` is on `S`, and an added fact `a` of `m` that overlaps `i`:
   * if `a.mark = T` and `a` is AT OR BELOW `i`: the answer is `a` itself with the mark `T`,
     `(a.base, a.path, a.kind, T)`, not the chain answer (an `[any-taint]/E` `a` gives the tail `[any]` with the Empty
     exclusion: run 1 has no `[any-taint]` premise, W8 (c));
   * if `a.mark = T` and `a` is above `i`: the answer is the chain answer `answer(i, a, T)` of §4.5;
   * if `a.mark` is abstract and does not exclude `T`: the request climbs (§4.5).

   The reason for the first case: do not use the chain answer when `a` is at or below a static premise. At the static
   root the chain answer is `(S, ., *, {}, T)`, and it starts as `(S, ., [any], T)` in the demand layer (§6.5). A cleaner on the static root then turns a precise caller
   fact into this fact, and the vulnerability is lost (`Statics.CexClean.shallow_misses`).

Every other operation on `S` is the ordinary one: the call bindings `S.* → S.*` (S12 (c)), the summary application
(§4.3), the cleaner (§4.7; its request uses item 4), and the conjunction literal (§4.6).

AFTER RUN 1 NO STATIC RULE IS NEEDED. A restricted run has no position request, no mark request and no other static
rule: the demand alone handles the statics. For the forward restricted runs this is proved under two hypotheses:
S12 (a) to (d), with the field limit of the run, and persisted records that keep the static invariant (a static
record conclusion with a `*` or an any tail above a static position is an identity static `*` record; Lean
`StaticsIter.RecOK`, with the model kind `.any` for both any tails). The proof has four steps:

1. For EVERY demand, no static fact of the run with a `*` or an any tail lies above a static position.
2. The reason: the emission gives the added fact, its meet at the same path, or the demand pattern below it; the
   restriction only moves a conclusion down; and a fact above a position is exact.
3. So every static read, write keep edge and sink of the run at most two accessors deep is the case at or below of
   §4.1, and none of them makes an any-tail result by the case `above`. A deeper static read or sink follows the
   ordinary rules of an instance field, and it can meet an `[any]` fact above it
   (`StaticsIter.DeepReadIter.deep_read_above`).
4. The run raises no request.

§10.8 lists the theorems (`StaticsIter.rinv_all`, `static_step_below`, `no_request`, `no_static_rule_after_run1`,
`iteration_general_DS`). The backward run satisfies the same invariant and raises no request
(`BExact.binv_all`, `no_static_rule_backward`) if the reversed program satisfies the construction rules S12 (a) to (d)
and its seeds and records keep the invariant (`BExact.SeedsOK`, `StaticsIter.RecOK`); an `[any]` sink on a class
position is outside it (precision only). That the interpreter's reversed program satisfies them is argued (§11.2).
That the persisted records keep the static invariant over the run sequence is argued (§11.2).

These theorems are about the CONCRETE restricted runs (the emission `emitM`; step 2 reads only its rows). Since F72 a
restricted run, forward or backward, can have a FLOW premise on `S`: the FLOW form of a `*` pattern (§6.3), with the
`*` tail. Step 4 still holds: the F72 runs have no request rule (§4.5). That no FLOW premise lies above a static
position, or that the ordinary case `above` of §4.1 then loses no flow that a concrete pattern does not give, is part
of the pending model of F72 (§11.2).

Lean: `Statics.lean`, the run-1 closure `DS` with the rules `sreqStmt`, `sanswer`, `sreqUp` and the answer
`Statics.SCtx.ansInit`; the final rule is `Statics.Design`. §10.8 lists its theorems and the worked programs.

---

## 5. Calls and ownership

### 5.1 Concrete semantics of a call

The concrete call step (the touched bases, the bindings, the zero binding) is in §3.5. The interpreter gives the
bindings of each call kind (`interpreter.md` §3).

### 5.2 Who owns what

| Side | Owns | Does |
|---|---|---|
| CALLER (the method that contains the call) | the subscriptions: (caller edge, call statement, added fact) | binds each caller fact into the callee (micro edges); applies every published summary edge of the callee whose premise its added fact satisfies, and every record that applies to it (§8.7 R4); binds back; applies the field limit |
| CALLEE (the called method) | the added facts (with the caller edges that made each added fact), the demand patterns of the method, the emission, its initial facts, its edges and summaries, its requests (run 1) | emits the initial facts for each added fact (§6); analyses them; restricts each new summary edge by its demand patterns (restricted runs, §6.4) and then PUBLISHES it to the subscribers; answers and propagates its mark requests (§4.5) and its position requests (§4.10) |

### 5.3 Call processing

The interpreter gives the order of the steps at a call (`interpreter.md` §4.5). For the caller edge `(i, layer) → c`
at the call statement:

1. RELEVANCE. If `c.base` is not a touched base of the call, the edge passes over the call (call-to-return). The
   touched bases are those of §3.5 (`interpreter.md` §3.1 lists them for each call kind), with one special case: the
   zero base is never touched (THE ZERO FACT below). `S` is touched at every call, in every run (`interpreter.md`
   §3.3).
2. BIND. Apply the caller-side type filter of each binding into the callee (`interpreter.md` §3.1, §5.1). For each
   binding edge `e` into the callee: the bound fact `b = concat(c, e)` (a micro edge, §4.2).
3. SINKS AND SOURCES. The sinks of the call check `b` (§4.9); a triggered sink can add end facts: zero-to-fact edges in
   the layer of the sink edge or of the completed combination (§2.2, §4.9; `interpreter.md` §4.1, END FACTS). The
   sources of the call apply to `b`: they are the rule statement of the call (`interpreter.md` §4.1), with statement
   micro edges (§4.2) and conjunctions (§4.6). The fact `b` has the premise set and the layer of
   the caller edge `(i → c)`, so in run 1 the static exception (§4.1, §4.10 item 1) tests the caller edge, and a
   position request goes to `(caller, i, p')`. A source result goes back to the caller through the binding back and
   the aliases, with NO summary rewriter (the rewriter removes the mark of a user-defined source at its own
   position), then the field limit (§4.4; `interpreter.md` §4.5 step 4). The end facts go the same way.
4. PER CALLEE POSITION. The cleaners of the call clean `b` (§4.7), chained in the rule order. A `RemoveAllMarks` rule on
   a position of `S` is not a cleaner: at its place in the rule order it applies to `b` as a statement summary, the
   kill of a strong write (`interpreter.md` §1.4), with the static exception as in step 3. (The whole-base cleaner of
   `AnyClassStatic` is a cleaner, S12 (e).) Each result `a` is an ADDED FACT (§1), with
   its own layer on the link (§8.3). Then:
   * for each resolved callee: the CALLEE PROCESSING below, for the link (`a`, caller edge);
   * at a JVM constructor call: `a` also passes over the call (`interpreter.md` §3.5);
   * for an unresolved callee or a resolution failure: the statement summary of the unresolved callee applies to `a`
     (`interpreter.md` §3.7), as statement micro edges (§4.2 step 4), with the static exception as in step 3. It is
     never restricted. A method with no instruction (native, abstract, no body) is never a resolved callee: the call
     resolver drops it, and a call with no other callee is unresolved (`interpreter.md` §3.7). A call with an empty
     and a non-empty target enters only the non-empty one, so a flow through the empty target is lost, as today on
     the JVM (`interpreter.md` G12).
5. RETURN. For each result of step 4 (a summary result or an unresolved result), in callee coordinates: apply the
   summary rewriter (§4.7; `interpreter.md` §5.2). Then bind the result back, with the binding-back type filters
   (`interpreter.md` §3.1). Then apply the aliases (`interpreter.md` §3.8: they apply to the results that its alias
   rule AC3 names). Among the summary results, only a COMPLETE identity result does not go to the aliases: a
   normal-layer result that equals the start fact of its premise (§6.5; `interpreter.md` AC4). A demand-layer summary
   result always goes to the aliases. The default identity and the constructor pass-over never go to the aliases
   (`interpreter.md` AC3, AC4).
   Then apply the field limit (§4.4). A constructor pass-over result skips the rewriter. This order is the order of
   `interpreter.md` §4.5 step 6.

THE ZERO FACT at a call (`interpreter.md` §4.6). The zero fact does not use steps 1 to 5; it uses this order:

1. The call does not touch the zero base, so the zero fact passes over the call.
2. The unconditional sinks and sources of the call fire on the zero fact, in the order of `interpreter.md` §4.6, and
   the stored facts of a conjunction can complete it (§4.6). The source rules form the rule statement of the call: a
   call stage (`interpreter.md` §4.1) with the micro edge from the zero fact to itself (S11 (d)). Their results go
   back as in step 3. In a forward restricted run, only the source seeds fire (§6.1 rule 6).
3. The zero fact enters every resolved callee through the binding `zero.* → zero.*` (§3.5), with no cleaner: it is an
   added fact of the callee, and the callee emits the zero fact for it (§6.2, §6.3). The results of the callee
   summaries that this added fact satisfies are summary results: they return by step 5.

The zero fact itself takes no cleaner, no pass rule and no rewriter. An unresolved call only passes the zero fact over.
In the backward run the zero fact enters the callees by the rule of §9.2.

The callee processing is a set of STANDING rules. Each event triggers its actions; the actions can make new events.
The order of the events does not change the fixed point (S6). An implementation can process them in any order.

| # | Event | Actions |
|---|---|---|
| E1 | A new added fact `a` of the callee | The callee adds `a` to its added fact store (§8.3). It EMITS the initial facts for `a` (§6): in run 1 the policy fact (§6.2), in a restricted run the emission for each demand pattern of the callee (§6.3): `a ∩ D-c` for a concrete pattern, the FLOW form of `D-c` for a `*` pattern (F72; one initial fact for every added fact under it). Each new initial fact is event E3. |
| E2 | A new link (added fact `a`, caller edge), also a new caller edge of an existing added fact | The callee stores the caller edge with `a` (§8.3). It checks every standing mark request and position request that overlaps `a`, and answers it or propagates it through THIS caller edge (§4.5; §4.10 items 2 and 3). The caller SUBSCRIBES `(caller edge, call statement, a)` (§8.4). It applies every published summary edge with one premise whose premise `a` satisfies (§4.3), and every record that applies to `a` (§8.7 R4), then step 5. For a summary with several premises the new link is event E6. |
| E3 | A new initial fact `j` of the callee (an emission, an answer or a position answer) | The callee analyses `j` from its start fact (§6.5). (The interpreter filters the start fact by the context type, `interpreter.md` §4.3.) Each summary edge of `j` is event E4. |
| E4 | A new summary delta `j → g` of the callee: an exit fact after the exit order of `interpreter.md` §4.7 (exit sources, exit sinks, the removals of that section; no summary for a local base) | In a restricted run the callee restricts it by each demand pattern of the callee (§6.4); a zero-premise summary of the backward run is not restricted (§9.2, the balanced return). It PUBLISHES each result. For a summary with one premise: for each subscription whose added fact satisfies `j`, the caller applies the result (§4.3), then step 5. A summary with several premises goes to event E6. |
| E5 | A new mark request `(m, i, T)` in the callee `m` (run 1) | The callee stores it (§8.8). For each added fact `a` of `m` that overlaps `i`, and each caller edge of `a`: answer or propagate, as in E2 (§4.5). |
| E6 | A new link at the call statement whose added fact satisfies one premise of a callee summary with several premises (§4.6), or a new such summary | The caller combines the link with the stored links of the other premises of that summary (§4.6, §8.9). A full combination (one link per premise) applies the summary, then step 5. |
| E7 | A new position request `(m, i, p)` in the callee `m` (run 1) | The callee stores it (§8.8). For each added fact `a` of `m` that overlaps `(S, p)`, and each caller edge of `a`: answer it if `a` is at or below `p`, or climb through the caller edge if `a` is above `p` and the caller premise is on `S` (§4.10 items 2 and 3). |

The result of a summary application is in the demand layer if the added fact is in the demand layer on its link
(§8.3), if the summary edge is, or if the application itself moves it there (§4.1). The result of a must record that
applies by `applicable` only is in the demand layer too (the record demotion, §4.3).

---

## 6. Runs and abstraction

### 6.1 Rules of a run and their contracts

RUN 1. The result of run 1 is the least fixed point (S6) of these rules (Lean: `D`; with W6, W8 and the exclusion of
`[any-taint]`, `AnyTaintEx.D6X`, and without the exclusion the round-1 closure `AnyTaint.D6T`, §10.11; with the static
rule `Statics.DS`; with the conjunctions `NDZ.DNz`, which corresponds to the list model `ND.DN`, §10.10):

* the zero fact is an initial fact of every root;
* each initial fact starts with its start fact (§6.5);
* at a statement: the statement transfer (§4.2), the conjunction (§4.6), the cleaner (§4.7), the type filter (§4.8)
  and the sink check (§4.9);
* at a call: the call processing of §5.3, with the summary application by `applicable` (§4.3);
* for each added fact: the abstraction of §6.2;
* the mark requests: raise, answer and climb (§4.5);
* the static rule: the position requests and the mark answer on a static premise (§4.10).

Run 1 is the first run, so it has no records.

A RESTRICTED RUN (every run after run 1, forward or backward) uses the rules of run 1 with these changes (Lean: `DR`
with the rules `initR`, `ret`, `retRec`, and the spec rules `emitM`, `satI` and `Handoff.restrictI`; with the
must-premises and the exclusion of the `[any-taint]` tail `AnyTaintEx.DRX` with the spec rules `emitX`, `satX` and
`HandoffX.restrictIX` (`AnyTaintEx.DRXs` is the instance with the earlier restriction `restrictX`), and without the
exclusion the round-1 closure `AnyTaint.DRT`, §10.11, §10.12; for the backward run `Backward.DB` with `emitM`, `satI`
and `Handoff.restrictI`, §9.2). These Lean closures are the CONCRETE design of F70 and F71: they keep the request
rules, which never fire with `emitM`. The F72 closures (Lean, PENDING: `DRA`, `DBA`, with the emission `emitW` and the
satisfaction `satW`) have no request rules; they are not modelled yet (§11.2):

1. An initial fact comes only from the emission (§6.3), for an added fact and a demand pattern of its method: the
   FLOW form of a `*` pattern, or `a ∩ D-c` of a concrete pattern (F72). The zero fact of a root is an initial fact
   too. (The backward run adds the zero rules of §9.2.)
2. A callee summary edge applies only after the restriction by a demand pattern of the callee (§6.4), and only to an
   added fact that satisfies its premise (§4.3): by `inside`, and for a FLOW premise also by `applicable` (F72). (The
   backward run has one exception: the balanced return of §9.2.)
3. A record applies when its premise covers the added fact (`applicable`) or lies inside it (`inside`) (§8.7 R4). A
   must record that applies by `applicable` only gives a demand result (§4.3).
4. There is no mark request, no position request and no static rule (§4.5, §4.10): THE RUN HAS NO REQUEST RULE (F72,
   R4). The run is NOT concrete (§6.3). On a fact with an abstract mark an operation that needs a concrete mark gives
   nothing (§4.5), and the flow of a concrete mark comes from a concrete demand pattern (R6, PENDING, §6.6). The same
   holds for the backward run. (Before F72 the run was concrete, so no rule needed a request, and the implementation
   asserted it: `RExact.DR_no_request`, `BExact.DB_concrete`, `DB_no_request`, theorems of the concrete design.)
5. The run has its own field limit (§4.4) and its own demand (§9.2 gives the hand-off: the demand edges of the run
   before it).
6. A FORWARD restricted run fires an UNCONDITIONAL SOURCE only if it is a SOURCE SEED: a source that the backward run
   before it reached (§9.2). An unconditional source is a micro edge from the zero fact to another base: at a statement
   (a read source, an exit source), at a call, or at the method start (`interpreter.md` §4.1). Run 1 fires every
   source. The zero keep edge, the conditional sources (a premise that is not the zero fact) and the end facts of a
   sink (they need the trigger of their sink, §4.9) are not restricted. Lean: the forward run on
   `FSeeds.keepSources P σ` (the statement sources; the others are argued, §11.2).

THE CONTRACTS. The abstraction selects the initial facts for an added fact `a` of the method `m`. It is a function of
`m`, `a` and constants of the run (the field limit, the demand). It must not depend on the order of events. `α(m, a)`
is the initial fact that the run-1 abstraction selects (§6.2). The spec rules satisfy the contracts below; the coverage
theorems need only the contracts.

```
(C1)  run 1:            applicable(α(m, a), a)
(C2)  restricted run:   for every demand pattern d of m, every added fact a (a CONCRETE a if the mark of D-c is
                        concrete) and every location l (with its mark) that D-c and a both cover, the emission
                        emit(D-c, a) gives an initial fact j that covers l, and a satisfies j; and every emitted
                        fact lies INSIDE the D-c that emitted it, in its locations AND its marks
(C3)  restricted run:   under a D-c with a concrete mark the emitted fact has the mark of the added fact; under a
                        D-c with the mark * it is the FLOW form of D-c, with the mark * (F72)
(C4)  satisfaction:     if a satisfies j, the marks of a are a subset of the marks of j (so the mark gate raises no
                        request); and if a satisfies j and a has the concrete mark T, a satisfies answer(j, a, T) (§4.5)
(C5)  restriction:      for every summary edge j → g whose premise j lies INSIDE D-c, in its locations AND its
                        marks, and every pair (l1, l2) of j → g (§3.2) such that D-p covers l2 WITH ITS MARK, the
                        restriction by d gives an edge j → g' that has the pair (l1, l2), in the layer of g
```

An abstract added fact under a concrete pattern gets NOTHING (§6.3; the user, F72: "If an added fact is * and the
demand is T -- nothing is emitted. That is OK. The added fact can't satisfy the demand."). So C2 does not ask for it
(`RCore.emitM_not_full_any`: no emission and no satisfaction can serve it). The flow of the mark `T` then comes from
the concrete pattern of the caller (R6; PENDING, §6.6).

Lean (THE CONCRETE DESIGN of F70 and F71, where every added fact is concrete and C3 reads "the emitted fact has the
mark of the added fact"; the F72 forms of C2, C3 and C4, for the FLOW form and `satW`, are the lemma L6 of the pending
model, §11.2): C1 `policy_applicable`; C2 `EmitContractOn`, proved for the emission of §6.3 as `RCore.emitM_contract_I` (also
with the exact test of a `*∖X` entry mark, §6.3), and its inside part `Handoff.emitM_insideB` (for a concrete added
fact; the location part `Handoff.emitM_inside`, the location form `Handoff.insideLoc_coversLoc`, the form with the
marks `Handoff.insideB_covers`, `emitM_covers`); C3 `EmitCopiesMark`, `RCore.emitM_copies`; C4 `SatContract`,
`RCore.satI_contract`; C5 for the restriction of §6.4 (the mark-aware intersection `Handoff.restrictI`):
`Handoff.restrictI_contract`, for every conclusion, also a `*` conclusion, and for every mark cell. The mark test of
the conclusion follows from the pair: if `D-p` covers `l2` with its mark, the conclusion mark meets the mark of `D-p`
(`Handoff.RAux.concMarkB_of_den`). The LOCATION FORM of C5 (the premise inside `D-c` as locations, `l2` in `D-p` as a
location, the marks ignored) is FALSE for the mark-aware restriction (`Handoff.restrictI_contract_loc_false`: the
example of §6.4, a pair whose exit location has the mark `T` against a `D-p` with the mark `U`). So C5 needs the exit
location with its mark: the demanded witness gives it (§1), and the backward run gives the demanded witness (contract
B, §6.6). The restriction keeps the layer and only removes pairs (`Handoff.restrictI_sub`). C5 reads only premises
inside `D-c`, and that is enough: every premise of a restricted run lies inside the `D-c` that emitted it, with its
mark (C2): a concrete premise is emitted from a concrete added fact (C3), and a FLOW premise is the FLOW form of its
`*` pattern (F72, R5: it lies inside that pattern and inside no concrete pattern). The earlier form of
C5 for a premise that only OVERLAPS `D-c` (Lean `RestrictContract`: `D-c` covers `l1`) is FALSE for the intersection
(`Handoff.restrictI_not_RestrictContract`): a premise that sticks out of `D-c` has a pair whose entry location `D-c`
covers, and the intersection gives no result for it (vectors `Handoff.RVec.vOverlap_*`). (History: the earlier
restriction `restrictU` kept a premise that overlaps `D-c` and did not satisfy C5 as a function either,
`RCore.restrictU_fails`; its coverage went through the auxiliary restriction `restrictS`, `RCore.restrictS_contract`,
`RExact.restrict_U_eq_S`. The intersection satisfies C5 directly. `ap-history.md` F70.)

The coverage theorem of run 1 needs only C1. The coverage theorem of a restricted run needs C2 (with its inside part)
for the added facts of the run, C4 and C5 (`Handoff.coverageRN`; with the earlier restriction `RCov.coverageR`).
In the concrete design C3 makes every added fact of a restricted run concrete (`RCov.concInvR_all`,
`RExact.DR_concrete`), so C2 covers all of them (`RCov.emitOn_of_conc`). With the records the coverage theorem also
needs that a crossable record applies to every concrete added fact that has a common location with its premise
(`Handoff.cross_applies`, §8.7 R4). SINCE F72 a restricted run has abstract added facts (the facts of a FLOW premise
of the caller). C2 covers them under a `*` pattern; under a concrete pattern they get nothing (above), and a
crossable record of a concrete premise does not apply to them. The coverage of a restricted run of F72 is then the
coverage with modes (L1, L4 of §11.2; PENDING).

WITH THE `[any-taint]` TAIL AND ITS EXCLUSION the contracts read the exclusions as part of the location sets (Lean:
`AnyTaintEx.EmitContractX`, `AnyTaintExCov.SatContractX`; the inside part of C2 `HandoffX.EmitInsideX`, for a
concrete added fact, with the marks; C5 `HandoffX.RestrictInsideX`, with the marks; the record application
`HandoffX.CrossSatX`). The emission of §6.3
(`AnyTaintEx.emitX`) satisfies C2 (`AnyTaintExCov.emitX_contract`; the emitted premise lies inside its `D-c` with its
exclusion, `HandoffX.emitX_inside`, and of a concrete added fact also with its mark, `HandoffX.emitX_insideXB`) and C3
(`AnyTaintEx.emitX_copies`): the emitted fact is exactly `a ∩ D-c`
with the exclusions. The satisfaction `AnyTaintEx.satX` satisfies C4 (`AnyTaintExCov.satX_contract`), and a crossable
record applies by it or by `applicable` (`HandoffX.cross_appliesX`). The restriction of §6.4 with the
exclusion (`HandoffX.restrictIX`) satisfies C5 for every conclusion, also a `*` conclusion
(`HandoffX.restrictIX_contract`; its premise test reads the exclusion and the mark of the premise, `HandoffX.insideXB`,
and its conclusion test is the mark test `Handoff.concMarkB` of the base restriction);
the overlap form of C5 is false for it (`HandoffX.restrictIX_not_RestrictContractX`), and so is the location form
(`HandoffX.XVec.restrictIX_contract_loc_false`). So run 1 and a forward
restricted run are sound (`AnyTaintExCov.coverage6X`, `vuln_found_policy6X`; `HandoffX.coverageRXI`,
`coversN_DRXI`, under S10 only). The exactness of a forward restricted run needs three more properties of the rules:
the satisfaction reads `inside` with the exclusions (`AnyTaintEx.SatInsideX`, §4.3), C3 (`EmitCopiesMarkX`: the run is
concrete; the C3 of the concrete design, which the F72 emission does not have under a `*` pattern, so the exactness of
the F72 X runs is PENDING, §11.2), and the restriction of a conclusion in the normal form of W8 gives a conclusion in
the normal form, in the same layer, with fewer pairs (`AnyTaintExExact.RestrictOKX`; the form without the normal form,
`AnyTaintEx.RestrictSubX`, is false for the earlier restriction `restrictX`,
`AnyTaintExExact.CexRestrictSub.cex_restrict_sub`). The spec rules have all three (`AnyTaintEx.satX_inside`,
`emitX_copies`, `HandoffX.restrictIX_ok`). (The earlier restriction `AnyTaintEx.restrictX` satisfied C5 only
for a conclusion without the `*` tail: `AnyTaintExCov.RestrictContractNSX`, `restrictX_contractNS`,
`restrictX_not_contract`; its runs: `AnyTaintExCov.coverageRX`, `vuln_foundRX`, `coverageRXs`, `vuln_foundRXs`;
`AnyTaintExExact.specX_rules`. Round 1, without the exclusion: `AnyTaint.emitT`, `emitT_eq`, `AnyTaint.SatInside`,
`AnyTaintExact.spec_rules`.)

### 6.2 Run 1

The run-1 abstraction gives:

* for the zero fact: the zero fact;
* for every other added fact `a`: the most abstract fact `(a.base, [], *, {}, *)`.

Lean: `policy1`, `policy_applicable` (C1). The caller gets the marks back through the summary application: a `*`-mark
premise passes the mark of the added fact through. A sink, a mark-specific rule or a cleaner inside the callee gets the
mark through a request (§4.5). A statement micro edge below the policy fact `(S, [], *, {}, *)` gets the precise
static fact through a position request (§4.10 items 1 to 3); a sink, a cleaner or a literal uses the mark request with
the answer of §4.10 item 4. Run 1 is the ONLY run with requests. The answers of the requests (§4.5, §4.10)
are the other initial facts of run 1.

An `[any-taint]/E` added fact gets the policy fact too: run 1 has no `[any-taint]` premise (W8 (c)). Its chain answer
is `(i.base, i.path, i.kind, T)` (§4.5), which starts as `[any]` in the demand layer (§6.5). So run 1 confirms an
`[any-taint]` finding only through a premise set `{zero}` or an exact answer, for example when the sink reads the
tainted object in the method of the source (`AnyTaintExCases2.PassRule.source_confirmed`), or through a callee whose
FLOW summary keeps the whole object (§4.1, row 1 or row `*`, `[]`, `[any-taint]/Ec`; program I,
`AnyTaintExCases2.I.run1_flow`, `app_normal`, `run1_confirmed`), also a callee that overwrites a field of it: the
field goes into the exclusion (the setter of program S, `AnyTaintExCases.S.run1_email_confirmed`; a setter one call
deeper, program SD, `AnyTaintExCases.SD.run1_email_confirmed`, `same_result`). Through a callee that reads below the
object (a getter `ret = p.f`) it does not: the FLOW summary of the policy fact is the case `above`, a demand edge
(`AnyTaintExCases2.G.run1_flow_above`, `run1_not_confirmed`). The demand of a later run gives the must-premise that
confirms it (§6.3).

### 6.3 Restricted run: the emission

THE RULE (decision F72, rule R2; `ap-history.md` F72). For the added fact `a` of method `m`, for each demand pattern
of `m` with the entry pattern `D-c = (b, p, t, M)`, the emission gives THE WEAKEST FACT INSIDE `D-c` THAT COVERS THE
COMMON PART OF `a` AND `D-c` (the user: "1) we should select the added fact, which is included into the D-c, then 2)
weaken it as much as possible, preserving the D-c inclusion"). If `a` and `D-c` have no common part (no common
location, or the mark of `a` is not a mark of `D-c`: the tables below), the emission gives nothing. Else:

* `M = *` (a `*` PATTERN): the FLOW FORM of `D-c` (§1), `(b, p, flowK(t), *)`, with `flowK(*/E) = */E`,
  `flowK([any]) = */{}` and `flowK($) = $`: a FLOW PREMISE. It does not depend on `a`: ONE initial fact per pattern
  serves every added fact under it, with every mark (SHARING). It starts with the identity, in the normal layer (§6.5),
  and its edges are FLOW (§7.2). In the spec runs a `*` pattern has the entry tail `[any]` (a demand-layer leaf with
  an abstract mark, for example the getter below): a normal leaf with a `*` conclusion is crossable, so it is never a
  demand edge (§4.3, §1; argued, PENDING §11.2). So the FLOW premise is `(b, p, */{}, *)`. The cells `*/E` and `$` of
  `flowK` only make the function total: a `*` pattern never has the `$` tail, because every `$` fact has a concrete
  mark (S8, §7.2). Lean, PENDING: `flowK`, `flowForm`, the emission `emitW` (`emitW d a` is nothing if `emitM d a`
  is nothing; else the FLOW form if `d.mark = *`, else `emitM d a`).
* `M = T` (a CONCRETE pattern): `a ∩ D-c`, the part of `a` that `D-c` covers, with the mark of `a` (the tables
  below; as before F72; Lean `emitM`, with the exclusion `AnyTaintEx.emitX`). No weaker NORMAL premise exists inside
  a concrete pattern: a `*` tail with a concrete mark starts as `[any]` in the demand layer (W2, §6.5), and a
  must-premise is a stronger assumption, not a weaker one.

The backward run uses the same rule, with the requirement as the added fact (§9.2): a `*` pattern gives a `*`
requirement. A concrete `M` is a demand for that mark. A pattern never has the mark `*∖X`: the hand-off replaces it by
`*` (R1, §9.2). (Under F71 the entry pattern of a backward demand pattern could have the mark `*∖X`, a run-1 summary
conclusion after a cleaner, and the emission read it EXACTLY: it admitted every mark that is not in `X`; Lean
`markMatchB`, the cell `*∖X` against a concrete mark; `ap-history.md` F71. Before F71 `*∖X` counted as `*`.) Since F72
an added fact of a restricted run can have an abstract mark (a fact of a FLOW premise of the caller, §6.5). (Before
F72 every added fact of a restricted run had a concrete mark, C3 of the concrete design.) THE MARK TEST:

| `D-c` mark | `a` mark | result |
|---|---|---|
| `T` | `T` | emit `a ∩ D-c` |
| `T` | `T' ≠ T` | nothing |
| `T` | `*` or `*∖X` | NOTHING (the user, F72: "If an added fact is * and the demand is T -- nothing is emitted. That is OK. The added fact can't satisfy the demand."; Lean `markMatchB (conc t) star = false`, `RCore.emitM_not_full_any`). No request (§4.5): the flow of `T` comes from the concrete pattern of the caller (R6, PENDING) |
| `*` | every mark | emit the FLOW form of `D-c` (F72), if `a` and `D-c` have a common location |
| `*∖X` (F71 only; no pattern has it since F72) | `T`, `T ∉ X` | emit, with the mark `T` of `a` |
| `*∖X` (F71 only; no pattern has it since F72) | `T`, `T ∈ X` | nothing: the summary of `D-c` does not pass `T` |

So the mark test is "the marks of `a` are a subset of the marks of `D-c`" (`markSub` of §3.4; for a concrete `a`
Lean: `Handoff.RAux.markMatchB_conc`; with no `*∖X` pattern also for an abstract `a`), and an emitted premise lies
inside `D-c` with its mark (C2; `Handoff.emitM_insideB` for a concrete pattern; for the FLOW form by its definition,
R5). The vectors of the F71 cells (`decide`; they stay as the record of F71): the entry pattern `(x, ., $, *∖{T})`
and the added fact `(x, ., $, T)` give nothing (`Handoff.RVec.vEmit_starEx_T`; the emission before F71,
`Handoff.RVec.emitM70` with the test `markMatchB70` where `*∖X` counts as `*`, gave the premise `(x, ., $, T)`: `vEmit_starEx_T_pre70`); the added fact `(x, ., $, U)` gives the
premise `(x, ., $, U)`, which lies inside the entry pattern with its mark (`vEmit_starEx_U`); with the exclusion
`HandoffX.XVec.vM_emit`.

THE COMMON PART `a ∩ D-c`. Under a concrete pattern it is the emitted fact. Under a `*` pattern every row that is not
"nothing" emits the FLOW form of `D-c` instead (F72):

| `a` against `p` | emitted fact (a concrete pattern) |
|---|---|
| another base, or apart | nothing |
| below (`a.path = p·r`, `r ≠ []`), `t` admits `r` | `a` itself (with its tail and its exclusion: an `[any-taint]/E` `a` gives the must-premise `[any-taint]/E`) |
| below, `t` does not admit `r` | nothing |
| at `p` | `(b, p, meet(a.tail, t))`: the table below; `*/E1` with `*/E2` gives `*/(E1 ∪ E2)` |
| above (`p = a.path·r`), the tail of `a` admits `r` (`[any-taint]/E`: `E` admits `r`) | `(b, p, meet(a.tail, t))`: the demand chain, with the meet of the tails and the Empty exclusion (here `a` has an any tail: a concrete fact has no `*` tail, W2) |
| above, the tail of `a` does not admit `r` | nothing: no common location |

THE MEET OF THE TAILS (the deeper of the two chains; "everything is guided by the intersection with the demand"). The
added fact `a` is `[any-taint]` if it has an any tail and is normal on its link (§8.3), else `[any]`. No entry
pattern has the tail `[any-taint]` (W8 (d)): a forward entry pattern is a backward conclusion (`$` or `[any]`, and
since F72 also `*/E` with the mark `*`), and a backward entry pattern is a forward summary conclusion, which the
hand-off reads as `$`, `*/E` or `[any]` (§9.2). A `*/E` entry pattern has an abstract mark (W2), so since F72 it is a
`*` pattern, and it gives its FLOW form: the column `*/E` below is the meet of the concrete design (before F72), and
it does not occur since F72:

| added fact `a` \ entry pattern tail `t` | `$` | `*/E` (backward only; before F72) | `[any]` |
|---|---|---|---|
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `*/E` | `[any]` |
| `[any-taint]/E` (forward only) | `$` | (does not occur) | `[any-taint]`: with `E` at the path of `a`, with the Empty exclusion at the deeper demand chain |

For two any tails the result keeps the tail of the ADDED FACT: `[any-taint]` is more precise than `[any]`, and the
entry pattern reads only locations. So an `[any-taint]/E` added fact gives an `[any-taint]` premise, a MUST-PREMISE
(§1). At the path of `a` it keeps `E`. At the deeper demand chain (the row `above`) every location below the chain is
admitted, so it has the Empty exclusion. If `E` does not admit the step down, nothing is emitted. The same table holds
in the backward run, with the requirement as the added fact and the forward summary conclusion as the entry pattern
(§9.2); there the added fact is never `[any-taint]`. Before F72 a `*/E` entry pattern occurred only in the backward
run (a forward summary conclusion), and an `[any]` added fact gave a `*/E` premise with a concrete mark, which starts
in the demand layer (§6.5): a precision loss only. Since F72 a `*/E` entry pattern (in both directions) gives its FLOW
form `(b, p, */E, *)`, which starts in the normal layer. Lean: `AnyTaintEx.emitX` (the base `emitM` with the
exclusion of the added fact) and `AnyTaintEx.emitTX` (the must flag `am && j.kind.isAny`); the vectors `AnyTaintEx.Vec.emit_at`,
`emit_above_excluded`, `emit_above_exact`, `emit_below`; without the exclusion every cell and the rows `below` and
`above`: `AnyTaint.EmitVec` (round 1).

Properties:

* UNDER A `*` PATTERN (F72) the emitted fact is the FLOW form of `D-c`. It covers every location of `D-c` with every
  mark, so it covers every location of `a ∩ D-c` (C2), and it lies inside `D-c` in its locations and its marks (R5).
  It does not lie inside `a` in general, so its summaries apply by `inside` or by `applicable` (§4.3). Its premise key
  is the same for every added fact under the pattern (§7.1): one analysis serves all of them.
* UNDER A CONCRETE PATTERN the emitted fact is EXACTLY `a ∩ D-c` as locations (`RCore.emitM_inter`), with the mark of
  `a` (`emitM_mark`, `emitM_copies`). Nothing is lost when the marks match (`emitM_complete`). Its chain is the chain of `a` or, above `a`,
  the demand chain (`emitM_shape`): never a chain that neither the fact nor the demand has. With the exclusion the
  emitted fact is exactly `a ∩ D-c` too: C2 holds (`AnyTaintExCov.emitX_contract`), and an emitted premise, a
  must-premise too, lies inside its added fact by `inside` with the exclusions (`AnyTaintEx.satX`); C3:
  `AnyTaintEx.emitX_copies`.
* No entry pattern has the `[any-taint]` tail (W8 (d), §9.2). The meet would not read it anyway: two any tails keep
  the tail of the added fact. The emission reads no pattern layer (`AnyTaint.EmitVec`: the columns `[any]` and
  `[any-taint]` are the same model pattern; `AnyTaintEx.emitTX`: the must flag is `am && j.kind.isAny`, from the added
  fact only).
* C2 under a concrete pattern holds for concrete added facts (`RCore.emitM_contract_I`; with a `*∖X` entry mark of
  F71 a covered location has a mark that is not in `X`, so the exact test emits for it); it fails for a `*`-mark added
  fact under a `T` demand (`emitM_not_full_any`, for every satisfaction). Since F72 such an added fact occurs (a fact
  of a FLOW premise of the caller), and the emission gives NOTHING for it (the mark table above: "The added fact can't
  satisfy the demand"); the flow of `T` comes from the concrete pattern of the caller (R6, PENDING). Under a `*`
  pattern C2 holds for every added fact by the FLOW form (the bullet above; Lean, PENDING: lemma L6, §11.2). The
  inside part with the marks also needs a concrete added fact under a `*∖X` pattern of F71: on an abstract added fact
  the emission test is looser than `markSub` (`Handoff.RVec.vEmit_abstract`: `(x, ., $, *)` passes the test of
  `*∖{T}`, but its marks are not a subset of `*∖{T}`). Since F72 no pattern has `*∖X`, so this case does not occur.
  (Before F72 a restricted run had no abstract added fact: `RExact.DR_concrete`, `BExact.DB_concrete`, theorems of
  the concrete design.)
* NO REQUEST (F72, R4; §4.5). A restricted run has no request rule. On a fact with an abstract mark an operation that
  needs a concrete mark gives nothing. BEFORE F72 the reason was the concreteness: the root starts from the zero fact,
  every emitted fact copies a concrete mark, a concrete-mark premise has only concrete-mark conclusions, and a
  `*`-premise record applied to a concrete fact gives a concrete result. So every fact of a forward restricted run had
  a concrete mark, no final fact had the `*` tail (`RExact.final_not_star`), and no request rule could fire
  (`RExact.DR_no_request`); the backward run was concrete and raised no request too (`BExact.DB_concrete`,
  `DB_no_request`). Since F72 a restricted run has FLOW premises, `*` facts and `*` final tails, so these claims are
  false for it (the theorems describe the concrete design). The only callee summaries with a `*` premise in a
  restricted run were then the persisted run-1 records and, in a backward run, their reversals (§9.1); since F72 the
  FLOW premises of the run have `*`-premise summaries too. The interpreter makes no precomputed `*`-premise summary
  (`interpreter.md` §3.7, I8).
* THE ZERO FACT. A demand that covers the zero location with the zero mark emits the zero fact itself. Every forward
  demand has the zero demand `(zero, none)` in every method (§9.2), so every forward callee that gets the zero fact
  emits it. In the backward run the zero fact needs no emission: it enters every callee as an initial fact directly
  (§9.2; Lean: rule `zin`).
* Precision. An exact added fact gives an exact concrete initial fact; its edges are in the normal layer, and a
  vulnerability under it can be confirmed (§4.9). An `[any-taint]/E` added fact gives an `[any-taint]` premise (or a
  `$` premise under a `$` entry pattern); a must-premise starts in the normal layer, with its exclusion (§6.5), and a
  vulnerability under it can be confirmed (§4.9; a sink in the callee: `AnyTaintExCases2.C.run3_supported`,
  `run3_confirmed`). The summary of a must-premise also confirms a sink in the caller (the getter:
  `AnyTaintExCases2.G.run3_must`, `run3_confirmed`; a setter under the broad demand `(this, ., [any], T)`: the summary
  `(this, ., [any-taint]) → (this, ., [any-taint], {name}, T)` is normal, `AnyTaintExCases.B.run3_must`,
  `run3_summary`, `run3_anyE_confirmed`). A fact cut to `[any]` gives an `[any]` premise in the demand
  layer. One path can have two premises: the must-premise `(x, p, [any-taint], E, T)` and the `[any]` premise
  `(x, p, [any], T)` (from a may added fact). They are two premise keys (§7.1); two must-premises with different
  exclusions are two premise keys too. A FLOW premise (F72) starts in the normal layer (§6.5): its normal summaries
  can be records (§8.7 R1), and a crossable leaf of it is not a demand edge (§1). A sink never fires under it (§4.9).
* Cost. A `*` pattern SHARES: its one FLOW premise serves every added fact under it, with every mark (F72). A concrete
  pattern has NO SHARING: one initial fact per distinct added fact (path, tail, mark). (Before F72 no pattern shared:
  the cost of decision F35, a product of the marks in the premises; `ap-history.md` F35, F72.) The price of the
  sharing is a coarser backward demand: the FLOW form of the pattern in place of the requirement (§9.2). The demand
  bounds which methods the run analyses and the chain prefix, but NOT the number of contexts below an `[any]` demand
  chain; the spec sets no cap. Nothing below a forward field-limit cut can be confirmed until a later forward run has
  a larger limit; the driver must grow the forward limit as well as the backward one (§6.6).

THE GETTER (F72; the first CEGAR program of the pending model, §11.2). `get(p) { ret = p.name; }`, called at
`x = get(dto)` with the DTO fact `(p, ., [any-taint], T)` and at a second call with a fact of the mark `U`. Run 1
gives the FLOW summary `(p, ., *) → (ret, ., [any], *)` in the demand layer (the case `above`), so it is a demand
edge (§9.2), with the backward pattern `D-c = (ret, ., [any], *)`, `D-p = (p, ., *, {}, *)`. Backward run 2 meets the
requirement `(ret, ., $, T)` under this `*` pattern: the emission gives the `*` requirement `(ret, ., *, {}, *)`, its
FLOW form, ONE requirement for both marks. Its backward summary is `(ret, ., *, {}, *) → (p, .name, *, {}, *)`. This
leaf is normal and its reversal `(p, .name, *, {}, *) → (ret, ., *, {}, *)` is crossable (§1), so forward run 3
crosses the getter by the reversed record, ONE record for every mark (§8.7 R3), with no analysis of the getter
(except the zero fact). The record applies to the DTO fact by `inside`, and the case `above` of an `[any-taint]` fact
gives the normal `(x, ., [any-taint], T)` in the caller (§4.1), so a sink on `x` can be confirmed. Where such a
backward leaf is a demand edge (it is not crossable), forward run 3 emits ONE FLOW premise `(p, .name, *, {}, *)` in
the getter for both added facts, and its summary applies to the DTO fact by `inside`. (Before F72 the requirement
stayed `(ret, ., $, T)`, and each mark had its own requirement and its own record.)

Program 1 (`RestrictedCases.lean`) is the worked example of the emission: the added fact of `c` is below the demand
chain, so the emission gives the fact itself; the added fact of `m` is above the demand chain, so the emission gives
the chain. Run 3 (forward) reports the vulnerability (`RCases.p1_found_M`, with the earlier restriction; with the
intersection `HandoffRCases.p1_found_I`, and through the hand-off of the demand edges from run 1 `HandoffRCases.p1_chain`).
The demand of `c` is `D-c = (x, .g.h, [any], T)` and the demand of `m` is `D-c = (arg, .f.k, [any], T)`, both with no
`D-p` (`RCases.dem1M`; so the restriction gives no result, `HandoffRCases.p1_no_exit`). Program 2 is the example of the
restriction (§6.4).

```java
root():  x.g.h.f.k.z = source();  c(x);      // (x, .g.h.f, [any], T) after the cut
c(x):    y = x.g.h;  m(y);                    // c gets (x, .g.h.f, [any], T); then (y, .f, [any], T)
m(arg):  sink(arg.f.k.z);                     // m gets (arg, .f, [any], T) ∩ (arg, .f.k, [any], T)
                                              //       = (arg, .f.k, [any], T): the sink triggers
```

Reference form (types and tests of §3.4):

```kotlin
/** §6.3, the `at` and `above` rows: the meet of two tails (Lean: meetK, with the must flag of AnyTaintEx.emitTX). Two
 *  any tails keep the tail of the added fact `a` (ANY_TAINT if `a` is normal on its link, §8.3) and its exclusion (the
 *  E of `[any-taint]/E`; the row `above` replaces it by Empty). No entry pattern has the tail ANY_TAINT (W8 (d)). */
fun meet(a: Pattern, d: Pattern): Pair<Tail, ExclusionSet> {
    // a */E pattern is backward only; the backward run has no [any-taint] (W8 (d)): the cell does not occur
    check(!(a.fact.tail == Tail.ANY_TAINT && d.fact.tail == Tail.STAR))
    return when {
        a.fact.tail.isAny && d.fact.tail.isAny -> a.fact.tail to a.exclusion
        a.fact.tail.isAny -> d.fact.tail to d.exclusion
        d.fact.tail.isAny -> a.fact.tail to a.exclusion
        a.fact.tail == Tail.EXACT || d.fact.tail == Tail.EXACT -> Tail.EXACT to ExclusionSet.Empty
        else -> Tail.STAR to a.exclusion.union(d.exclusion)
    }
}

/** §6.3, F72. The emission: the FLOW form of a `*` pattern (SHARING: it does not depend on `a`), or the common part
 *  `a ∩ D-c` of a concrete pattern; nothing if `a` and `d` have no common part (Lean, PENDING: emitW). */
fun emit(d: Pattern, a: Pattern): Pattern? {
    val j = commonPart(d, a) ?: return null
    return if (d.fact.mark is MarkSlot.Star) flowForm(d) else j    // no pattern has `*∖X` (R1, §9.2): Star is `*`
}

/** §6.3, F72. The FLOW form of a `*` pattern: its chain, flowK of its tail, the mark `*` (flowK(*/E) = */E,
 *  flowK([any]) = */{}, flowK($) = $; a `*` pattern never has the `$` tail). Lean, PENDING: flowForm, flowK. */
fun flowForm(d: Pattern): Pattern {
    val star = MarkSlot.Star(MarkSet.EMPTY)
    return if (d.fact.tail == Tail.ANY) Pattern(d.fact.copy(tail = Tail.STAR, mark = star), ExclusionSet.Empty)
    else Pattern(d.fact.copy(mark = star), d.exclusion)                // `*/E` keeps E
}

/** §6.3. The part of the added fact `a` that the entry pattern `d` covers, with the mark of `a`: the emission of a
 *  concrete pattern. The caller gives `a` the tail ANY_TAINT (with its exclusion) if it has an any tail and is normal
 *  on its link, else ANY (§8.3). An `[any-taint]/E` added fact gives the must-premise `[any-taint]/E` at or below its
 *  path, and `[any-taint]` with the Empty exclusion at a deeper demand chain if E admits the step down (Lean:
 *  emitM, AnyTaintEx.emitX). Since F72 `a` can have an abstract mark (a fact of a FLOW premise of the caller). */
fun commonPart(d: Pattern, a: Pattern): Pattern? {
    if (d.fact.base != a.fact.base) return null
    // a T demand needs the mark T: an abstract `a` gives nothing ("the added fact can't satisfy the demand", F72);
    // `*` admits every mark (Lean: markMatchB; with no `*∖X` pattern it is markSub)
    if (!markSub(d.fact.mark, a.fact.mark)) return null
    val p = d.fact.path
    val q = a.fact.path
    return when {
        q.size > p.size && q.startsWith(p) ->                                   // below: the fact itself
            if (d.tailAdmits(q.drop(p.size))) a else null
        q == p -> {                                                              // at: the meet of the tails
            val (tail, excl) = meet(a, d)
            Pattern(a.fact.copy(tail = tail), excl)
        }
        p.startsWith(q) ->                                    // above: the demand chain, the meet of the tails
            if (a.tailAdmits(p.drop(q.size))) {      // a concrete `a` has an any tail here (W2); reads E of `[any-taint]/E`
                val (tail, excl) = meet(a, d)
                Pattern(d.fact.copy(tail = tail, mark = a.fact.mark),
                    if (tail.isAny) ExclusionSet.Empty else excl)    // every location below the chain is admitted
            } else null
        else -> null
    }
}

/** §4.3. The added fact `a` satisfies the premise `j` of a summary edge (a record: applicable or inside in every
 *  later run, R4; a must record by applicable only gives a demand result). F72: a FLOW premise (the mark `*`) of a
 *  restricted run also by applicable (Lean, PENDING: satW). */
fun satisfies(j: Pattern, a: Pattern, restricted: Boolean): Boolean =
    if (!restricted) applicable(j, a)       // run 1: a inside j (run 1 has no `[any-taint]` premise)
    else inside(j, a) ||                    // restricted run: j inside a (the only test of a must-premise)
        (j.fact.mark is MarkSlot.Star && applicable(j, a))   // F72: a FLOW premise also covers a

/** §4.3. The layer of a record application in a forward run: a must record (an `[any-taint]` premise) that applies by
 *  applicable only gives a demand result; the fact does not change, and W8 (b) drops its exclusion (Lean:
 *  AnyTaint.recLayer, AnyTaintEx.recLayerX). The backward run has no must record (W8 (d), §8.7 R3). */
fun recordDemand(j: Pattern, a: Pattern, resultDemand: Boolean): Boolean =
    resultDemand || (j.fact.tail == Tail.ANY_TAINT && !inside(j, a))
```

### 6.4 Summary restriction (restricted runs, in the callee)

The CALLEE restricts each summary edge `j → g` by each of its demand patterns `d` (entry pattern `D-c`, exit pattern
`D-p`) BEFORE it publishes the result `j → g'` to the subscribers. THE RESTRICTION IS THE INTERSECTION of the edge with
the demand pattern: the premise must lie inside `D-c`, and the conclusion is met with `D-p` (`ap-history.md` F70).
THE RESTRICTION TESTS THE MARKS (`ap-history.md` F71): a demand pattern with the concrete mark `T` asks for `T`, so a
summary edge that does not have `T` does not satisfy it. Lean: `Handoff.restrictI` (the premise test `Handoff.insideB`:
the location part `Handoff.insideLocB` and the mark part `markSubB`; the mark test of the conclusion
`Handoff.concMarkB`; the conclusion `Handoff.restrictConcI` with the meet `Handoff.meetConcK`); with the exclusion of
`[any-taint]` `HandoffX.restrictIX` (the premise test `HandoffX.insideXB`: the location part `HandoffX.insideLocXB`
and the same mark part; the same mark test `Handoff.concMarkB`; `restrictConcIX`, the exclusion of the meet
`meetExX`, the exclusion of the chain `chainExX`).

* No `D-p` (the demand does not reach the method exit): no result.
* THE PREMISE. `j` must lie INSIDE `D-c`, in its locations AND its marks: every location of `j`, with its mark, is a
  location of `D-c` (Lean: `Handoff.insideB`; `insideB_covers`). THE LOCATIONS: the exclusion of a must-premise is read:
  at the path of `D-c`, the exclusion of `D-c` must be a subset of the exclusion of `j`; strictly below the path of
  `D-c`, the tail of `D-c` must admit the step. THE MARKS: the marks of `j` must be a subset of the marks of `D-c`
  (`markSub` of §3.4): a `*` entry pattern admits every mark, a concrete `T` only `T`, and a `*∖X` entry pattern
  (backward only, §6.3) every mark that is not in `X`. Else no result: a premise that only overlaps `D-c`, or that has
  a mark that `D-c` does not admit, gives no result. This loses nothing that the coverage needs: every concrete
  premise of a restricted run is an emitted fact `a ∩ D-c` of a concrete added fact (§6.3), so it lies inside the
  `D-c` that emitted it, with its mark (C2; `Handoff.emitM_insideB`, with the exclusions `HandoffX.emitX_insideXB`),
  and that demand pattern restricts its summaries. A FLOW premise (F72, rule R5) is the FLOW form of its `*` pattern,
  so it lies inside that pattern; it lies inside no concrete pattern (the mark `*` is not a subset of `{T}`:
  `markSubB T * = false`), so only the `*` patterns restrict its summaries. The premise of the result is `j` itself,
  with its tail, its exclusion and its mark (a must-premise stays a must-premise).
* THE MARK OF THE CONCLUSION. The mark of `g` must MEET the mark of `D-p` (Lean: `Handoff.concMarkB`): two concrete
  marks must be the same; a `*∖X` side does not admit a concrete mark in `X`; a `*` side meets every mark. Else no
  result. Under a concrete pattern the mark of `g` is concrete (§6.3), and so is the mark of `D-p`, except in backward
  run 2: there `D-p` is a premise of run 1 and can be a policy fact with the mark `*` (§6.2), which meets every mark.
  So the test is "the same mark" in every other case. Under a `*` pattern (F72) `g` is a conclusion of a FLOW premise,
  with an abstract mark, and `D-p` has the mark `*` (the exit pattern of a `*` pattern is a premise with the mark `*`:
  a FLOW premise, or a policy fact in backward run 2), so the test keeps it. (Before F72 the mark of `g` in a
  restricted run was always concrete.)

| `D-p` mark \ `g` mark | `U` | `*` | `*∖Y` |
|---|---|---|---|
| `T` | keep if `U = T` | keep | keep if `T ∉ Y` |
| `*` | keep | keep | keep |
| `*∖X` | keep if `U ∉ X` | keep | keep |

  The test does not change the mark of `g`: a conclusion with an abstract mark (before F72 it never occurred in a
  restricted run; since F72 it is a conclusion of a FLOW premise) that the test keeps stays as it is, because the
  intersection of a pass-through mark with `T` has no form (an over-approximation, no lost pair; the exception (c) below). A `*∖X` exit pattern does not occur in the spec runs (a
  `D-p` is a premise of the run before, and a premise never has the mark `*∖X`, §2.2); the cells are for the
  completeness of the test.
* THE CONCLUSION. `g'` follows the position of `g` against `D-p`:

| `g` against `D-p` | `g` tail | `g'` |
|---|---|---|
| at (`g.path = D-p.path`) | any | `(g.path, meet(g.tail, D-p.tail))`: THE MEET below |
| below (`g.path = D-p.path ++ r`, `r ≠ []`), the tail of `D-p` admits `r` | any | `g` (with its exclusion) |
| below, the tail of `D-p` does not admit `r` | any | no result |
| above (`D-p.path = g.path ++ r`, `r ≠ []`) | `[any]` | `(D-p.path, $)` if `D-p` has the `$` tail, else `(D-p.path, [any])` |
| above | `[any-taint]/E`, `E` admits `r` | `(D-p.path, $)` if `D-p` has the `$` tail; `(D-p.path, [any-taint], E2)` if `D-p` is `*/E2`; `(D-p.path, [any-taint])` with the Empty exclusion if `D-p` is `[any]` (every location below `D-p` carries the mark) |
| above | `[any-taint]/E`, `E` does not admit `r` | no result: no common location |
| above | `*/E` | `g` if `E` admits `r`, else no result; before F72 it never occurred in a restricted run (no `*` final tail); since F72 a conclusion of a FLOW premise |
| above | `$` | no result |
| apart, or another base | | no result |

THE MEET of the conclusion tail with the tail of `D-p`, at the same path. No `D-p` has the `[any-taint]` tail
(W8 (d)): a forward `D-p` is a backward premise (`$`, `*/E2` or `[any]`), and a backward `D-p` is a forward premise.

| `g` tail \ `D-p` tail | `$` | `*/E2` | `[any]` |
|---|---|---|---|
| `$` | `$` | `$` | `$` |
| `[any]` (demand) | `$` | `[any]`: THE EXCEPTION (a) below | `[any]` |
| `[any-taint]/E` (normal; forward runs only) | `$` | `[any-taint]/(E ∪ E2)` | `[any-taint]/E` |
| `*/E` | `*/E` | `*/E` | `*/E` |

Only the any tails narrow: `[any] ∩ $ = $`, `[any-taint]/E ∩ $ = $`, and `[any-taint]/E ∩ */E2 = [any-taint]/(E ∪ E2)`.
A `$` conclusion lies inside every pattern at its path. The cell `[any] ∩ */E2` keeps `[any]`: a demand `[any]` has no
exclusion (W8 (a)), and a concrete mark has no `*` tail (W2), so no fact is the exact intersection. A `*` conclusion
stays as it is: a cut to `$` relates more pairs, not fewer. Before F72 a restricted run had no `*` conclusion
(`Handoff.DR_exit_not_star`; the backward run by W2, for concrete seeds with no `*` tail: `HandoffNoStar.DB_legal`,
`DB_edge_nonstar`; theorems of the concrete design). Since F72 a conclusion of a FLOW premise can have the `*` tail,
and its `*` pattern has the exit pattern `*/{}` (§6.3: the FLOW form, or a policy fact in backward run 2). At the path
of `D-p` the cell `*/E` against `*/{}` keeps `*/E`, which is the intersection. Above `D-p` the row `above`, `*/E`
keeps the whole conclusion, which also has locations outside `D-p`: there the exception (b) below occurs, a precision
point (§11.2). (The exact meet `*/(E ∪ E2)` at one path is representable, `Handoff.star_meet_exact`.)

* `j → g'` has the layer and the mark of `j → g`. The restriction only removes pairs (`Handoff.restrictI_sub`; with
  the exclusions `HandoffX.restrictIX_ok`: in the normal form of W8, in the same layer, with fewer pairs;
  `restrictIX_sub_base` for the facts without the exclusions). It keeps every pair `(l1, l2)` of a premise inside
  `D-c` (in its locations and its marks) whose exit location `D-p` covers with its mark: contract C5 (§6.1;
  `Handoff.restrictI_contract`, `HandoffX.restrictIX_contract`). The mark tests remove no pair of C5: if `D-p` covers
  `l2` with its mark, the mark of `g` meets the mark of `D-p` (`Handoff.RAux.concMarkB_of_den`).
* IT IS THE INTERSECTION, in the locations and in the marks, with three exceptions (on the locations: Lean
  `Handoff.RExc`, with the exclusions `HandoffX.RExcX`; on the marks: an abstract conclusion mark, `Invariant.AbsMark`):
  every pair of a result has its entry location, with its mark, in `D-c` and its exit location, with its mark, in
  `D-p` (`Handoff.restrictI_interM`; `HandoffX.restrictIX_interM`; the location forms `Handoff.restrictI_inter`,
  `HandoffX.restrictIX_inter`), except (a) an `[any]` conclusion at or above a `*/E2` exit pattern: the result
  is the chain of `D-p` with the tail `[any]`, which also has the locations below `D-p.path` that `E2` excludes (with
  `E2 = {}` it adds no location); (b) a `*` conclusion, which stays whole; and (c) a conclusion with an abstract mark:
  the exit mark of a pair is then its entry mark, and the mark test keeps the edge. Each exception is real
  (`Handoff.RVec.inter_exc_any`, `inter_exc_star`, `inter_exc_star_at`; `HandoffX.XVec.inter_exc_any`,
  `inter_exc_star`; (c): `Handoff.RVec.inter_exc_absmark`, the edge `(x, ., $, *) → (ret, ., $, *)` against
  `D-p = (ret, ., $, U)` keeps the pair from `(x, [], T)` to `(ret, [], T)`). For a concrete conclusion mark, (c) does
  not occur, and in the cells (a) and (b) the exit mark is still a mark of `D-p` (`Handoff.restrictI_inter_conc`,
  `HandoffX.restrictIX_inter_conc`). Every conclusion of a restricted run has a concrete mark, so (c) never occurs in
  it. In a restricted forward run only (a) occurs (`Handoff.handF_narrow_DR`;
  `HandoffX.handF_narrowX_DRX`: only on a demand-layer piece), and only when a demand pattern has a `*/E2` exit
  pattern (`Handoff.handF_narrow_DR_exact`). A forward `D-p` is a backward premise; it has a `*` tail only if the
  backward run emitted it under a `*/E` entry pattern (§6.3), that is, a forward summary conclusion with a `*` tail
  that a forward run handed off. With the hand-off of the demand edges, run 1 hands off no pattern with a `*` entry
  tail: every exit edge of run 1 with a `*` conclusion is normal, has an abstract mark (W2) and a premise `$` or `*`
  with the Empty exclusion, so it is crossable (§1, §9.1), and a demand-layer leaf has no `*` tail (W2)
  (`HandoffNoStar.run1_exit_star_cross`, `handF_run1_nonstar`; its exit patterns, the premises of run 1, have the tail
  `$` or `*/{}`). A restricted forward run has no `*` exit edge (`Handoff.DR_exit_not_star`), and with no `*` entry
  pattern in its demand it hands off no `*` pattern (`Handoff.handF_DR_nonstar`). The backward run emits no `*`
  premise under a demand with no `*` entry pattern (`HandoffNoStar.DB_init_nonstar`), and it has no `*` conclusion
  (W2 of the backward run, for concrete seeds with no `*` tail: `HandoffNoStar.DB_legal`, `DB_edge_nonstar`), so its
  hand-off has no `*` pattern (`HandoffNoStar.demOfN_nonstar`). So no demand pattern of a forward run has a `*` tail
  (`HandoffNoStar.canon_dem_nonstar`), the exception (a) with `E2 ≠ {}` does not occur, and the forward narrowing is
  exact from forward run 3 on (`HandoffNoStar.narrowing_canon_fwd_exact`, by `Handoff.handF_narrow_DR_exact`). On the
  backward side the exception (b) does not occur, and the cell (a) occurs only after run 1, at a `*/{}` exit pattern,
  where it adds no location (`HandoffNoStar.narrowing_canon_back_exact`, `narrowing_canon_back_loc`,
  `rexc_empty_loc`). THESE STATEMENTS ARE ABOUT THE CONCRETE RESTRICTED RUNS of F70 and F71. Since F72 a restricted
  run has FLOW premises: their conclusions have abstract marks (the exception (c)) and `*` tails (the exception (b)),
  and the hand-offs give `*` patterns (a `*` entry tail from a backward `*` conclusion, a `*` exit tail from a FLOW
  premise; backward run 2 already emits the FLOW form `*/{}` of an `[any]` pattern with the mark `*`). So the claims
  "(c) never occurs", "only (a) occurs" and "no demand pattern of a forward run has a `*` tail" are FALSE for the F72
  runs: `Handoff.DR_exit_not_star`, `handF_DR_nonstar`, `HandoffNoStar.DB_init_nonstar`, `DB_edge_nonstar`,
  `demOfN_nonstar`, `canon_dem_nonstar`, `canon_handF_nonstar` (and the X forms `DRX_init_nonstar`,
  `handF_DRX_nonstar`, `canonX_dem_nonstar`, `canonX_handF_nonstar`) describe the concrete design.
  `HandoffNoStar.run1_exit_star_cross` and `handF_run1_nonstar` still hold: they read run 1 only, which F72 does not
  change (the hand-off normalization changes only marks). The exceptions of the intersection in the F72 runs are part
  of the pending model (§11.2).
* The restriction of `[any-taint]` reads the exclusions as locations (§3.4): the premise test reads the exclusion of a
  must-premise; below `D-p` the conclusion keeps `E`; above `D-p` it needs `E` to admit the step down; at a `*/E2`
  exit pattern the result gets `E ∪ E2`, and above it `E2` (the exact intersection; `HandoffX.XVec.v_taint_star`,
  `v_above_rows`; the earlier restriction gave `[any-taint]` with the Empty exclusion above `D-p`, which is not the
  intersection, `v_old_above_not_inter`).
* One summary edge can have results for several demand patterns. The subscribers get every result (the union).
* The earlier restriction (Lean `restrictU`, `restrictWith`, `restrictConcU`; with the exclusions
  `AnyTaintEx.restrictX`, `restrictConcX`) kept the premise `j` whole if `j` only overlaps `D-c`, and kept the whole
  conclusion at or below `D-p`, also the locations that `D-p` does not cover (`g = (y, ., [any])` against
  `D-p = (y, ., $)` gave `g`). It was not an intersection, it was wrong for an any-tail premise, and it handed the
  locations outside the demand on to the next run (`ap-history.md` F70). Its theorems stay in the model as the record
  of the earlier design (§10.7, §10.11). Every theorem of the model that takes a restriction that only removes pairs
  (`RestrictSub`, for example `RExact.edge_exactR_valid`, `recs_of_DR_valid`, `confirmed_realM_gen_valid`) holds for
  the intersection by `Handoff.restrictI_sub`, and every theorem that takes `AnyTaintExExact.RestrictOKX` (for example
  `AnyTaintExExact.edge_exactX_valid`, `recs_of_DRX_valid`, `confirmed_realX_valid`, `seq_confirmed_realX_valid`)
  holds for it by `HandoffX.restrictIX_ok`.

The special cases of the restriction:

* A SUMMARY WITH SEVERAL PREMISES `{j1, …, jk} → g` (§4.6). The restriction by `d` keeps the whole premise set if
  every member `jm` lies inside the `D-c` of a demand pattern of the method, in its locations and its marks (each
  member is an emitted fact, so it lies inside the `D-c` that emitted it) and one member lies inside the `D-c` of `d`;
  else no result. `g'` follows the mark test and the table with the `D-p` of `d`. The restriction only removes pairs
  from the conclusion. (Argued, not modelled, §11.2:
  the backward run reverses a conjunction into one edge per literal, §9.2, so the demand of each member has a pattern
  with the same `D-p`.)
* A RECORD is not restricted (§4.3, §8.7 R4).
* THE BACKWARD RUN. A zero-premise summary of a callee is not restricted: every caller applies it to its own zero fact,
  with no satisfaction test (§9.2, the balanced return; Lean: rule `zret`). With the restriction of this section,
  no backward demand pattern keeps it, and the seeds never reach the callers.
* An unresolved callee has no summary edge: its statement summary is never restricted (`interpreter.md` §3.7).

Program 2 (`RestrictedCases.lean`, `RCases.P2`) is the worked example of the restriction, with the forward field limit
`L = 3`:

```java
root():  x.h.i.f.k.z = source();  r = c(x);  sink(r.f.k.z);   // (x, .h.i.f, [any], T) after the cut
c(arg):  ret = arg.h.i;  return ret;                           // D-c = (arg, .h.i, [any], T), D-p = (ret, .f.k, [any], T)
```

The added fact of `c` is `(arg, .h.i.f, [any], T)`. It is below the demand chain, so the emission gives the fact
itself (§6.3), and this premise lies inside `D-c` (the `[any]` tail of `D-c` admits the step `f`). The exit fact of `c`
is `(ret, .f, [any], T)`, in the demand layer. It is above `D-p`, so the restriction gives `(ret, .f.k, [any], T)` (the
row `above`, `[any]`, under the `[any]` tail of `D-p`). The added fact satisfies the premise (`inside`, §4.3). The
summary application and the binding back give `(r, .f.k, [any], T)`, and the sink triggers on it. Run 3 (forward)
reports the vulnerability. The Lean run of program 2 with the intersection is `HandoffRCases.p2_found_I`: the premise
lies inside `D-c` (`HandoffRCases.f3_inside`), also with its mark (`f3_insideB`), the conclusion mark `T` is the mark
of `D-p` (`f3_concMark`), and the restriction gives `(ret, .f.k, [any], T)`, the result of the
earlier restriction (`HandoffRCases.f3_restrictI`, `f3_restrictI_eq_U`; the earlier run `RCases.p2_found_M`, with
`restrictU`). The hand-off of backward run 2 contains this demand pattern of `c` (`HandoffRCases.p2_handoff`; the
backward premise lies inside its `D-c`, also with its mark, `b2_inside`, `b2_insideB`; its conclusion mark `T` meets
the mark `*` of its `D-p`, `b2_concMark`; `b2_restrictI_eq_U`), and run 1, backward run 2 and forward run 3
with the hand-off of the demand edges report the vulnerability (`HandoffRCases.p2_chain`). That the hand-off is
exactly this demand pattern of `c`, the zero demand of every method, and the pattern `((x, .h.i, [any], T), none)` of
the root is `Backward.dem2_exact` for the earlier hand-off; for the hand-off of the demand edges it is checked by hand
(the run-1 summary of `c` is in the demand layer, so it is a demand edge, §9.2).

The vectors of the restriction (`decide`; test data, §13): the example above, `g = (y, ., [any])` against
`D-p = (y, ., $)` gives `(y, ., $)` (`Handoff.RVec.v64_restrictI`; the earlier restriction kept `[any]`,
`v64_restrictU`); a premise that only overlaps `D-c` gives no result (`vOverlap_overlapB`, `vOverlap_inside`,
`vOverlap_restrictI`; the earlier restriction gave one, `vOverlap_restrictU`); no `D-p`, no result (`vNoExit`); every
row of the conclusion restriction (`Handoff.RVec.row_base`, the nine meet cells `row_at_*`, `row_below_*`,
`row_above_*`, `row_apart`); with the exclusions (`HandoffX.XVec.v64_demand`, `v64_taint`, `v_taint_star`,
`v_at_rows`, `v_above_rows`, `v_below_rows`, `v_overlap`, `v_inside_only_with_excl`, `v_old_above_not_inter`).

The vectors of the mark tests (`decide`; the bases `x`, `ret`, the accessor `f`, the marks `T`, `U`):

* THE EXAMPLE OF F71 (the user): the edge `(x, ., $, T) → (ret, .f, $, T)` and the demand pattern
  `D-c = (x, ., $, T)`, `D-p = (ret, .f, $, U)`. The premise lies inside `D-c` (`Handoff.RVec.vMark_user_inside`), but
  the conclusion `(ret, .f, $, T)` against `D-p = (ret, .f, $, U)` fails the mark test (`vMark_user_concMark`), so the
  restriction gives NOTHING (`vMark_user_restrictI`). The locations alone match (`vMark_user_loc`), so the
  location-only test before F71 kept the edge, and so does the earlier restriction (`vMark_user_restrictU`). With
  `D-p = (ret, .f, $, T)` the edge is kept (`vMark_user_same`). The location form of C5 is false by this example
  (`Handoff.restrictI_contract_loc_false`).
* A PREMISE MARK THAT `D-c` DOES NOT ADMIT: the premise `(x, ., $, T)` and `D-c = (x, ., $, U)`: inside as locations
  (`vMark_prem_loc`), not in its marks (`vMark_prem_inside`), so nothing (`vMark_prem_restrictI`).
* THE `*∖X` CELLS. The entry side, `D-c = (x, ., $, *∖{T})`: a premise with the mark `T` gives nothing, a premise with
  the mark `U` is kept (`vMark_inStarEx_T`, `vMark_inStarEx_U`). The exit side, `D-p = (ret, .f, $, *∖{T})`: a
  conclusion with the mark `T` gives nothing, a conclusion with the mark `U` is kept (`vMark_outStarEx_T`,
  `vMark_outStarEx_U`).
* THE EXCEPTION (c): `Handoff.RVec.inter_exc_absmark` (above).
* WITH THE EXCLUSIONS: `HandoffX.XVec.vM_user` (the example of F71: `HandoffX.restrictIX` gives nothing, the earlier
  `AnyTaintEx.restrictX` keeps the edge), `vM_prem`, `vM_inStarEx`, `vM_outStarEx` (the conclusion
  `(ret, ., [any-taint], {f}, T)` against `D-p = (ret, ., $, *∖{T})` gives nothing; with the mark `U` it gives the meet
  `(ret, ., $, U)`), and the location form of C5 is false (`HandoffX.XVec.restrictIX_contract_loc_false`).

Reference form (types and tests of §3.4):

```kotlin
/** §6.4. The premise `j` lies inside the pattern `d` as LOCATIONS, marks ignored; the exclusion of a must-premise
 *  is read (Lean: insideLocB; with the exclusions HandoffX.insideLocXB). The location part of `insideDemand`. */
fun insideLoc(j: Pattern, d: Pattern): Boolean {
    val star = MarkSlot.Star(MarkSet.EMPTY)
    return covers(d.copy(fact = d.fact.copy(mark = star)), j.copy(fact = j.fact.copy(mark = star)))
}

/** §6.4, THE PREMISE: `j` lies inside the entry pattern `d` in its locations AND its marks: the marks of `j` are a
 *  subset of the marks of `d` (`*` admits every mark, `T` only `T`, `*∖X` every mark not in X). It is covers(d, j).
 *  (Lean: insideB; with the exclusions HandoffX.insideXB.) */
fun insideDemand(j: Pattern, d: Pattern): Boolean = insideLoc(j, d) && markSub(d.fact.mark, j.fact.mark)

/** §6.4, THE MARK OF THE CONCLUSION: the mark `c` of the conclusion meets the mark `dp` of D-p (Lean: concMarkB).
 *  Two concrete marks are the same; a `*∖X` side does not admit a concrete mark of X; a `*` side meets every mark;
 *  two abstract marks always meet (§1). The mark of the conclusion does not change. */
fun marksMeet(dp: MarkSlot, c: MarkSlot): Boolean = when {
    dp is MarkSlot.Concrete && c is MarkSlot.Concrete -> dp.mark == c.mark   // a restricted run: the same mark
    dp is MarkSlot.Concrete -> dp.mark !in (c as MarkSlot.Star).excluded      // an abstract conclusion stays as it is
    c is MarkSlot.Concrete -> c.mark !in (dp as MarkSlot.Star).excluded
    else -> true
}

/** §6.4, THE MEET at the path of D-p (Lean: meetConcK; with the exclusions meetExX and the normal form normX). Only
 *  the any tails narrow: `[any] ∩ $ = $`, `[any-taint]/E ∩ $ = $`, `[any-taint]/E ∩ */E2 = [any-taint]/(E ∪ E2)`.
 *  `[any] ∩ */E2` keeps `[any]` (W2: a demand `[any]` has no exclusion, a concrete mark no `*` tail). `$` and `*`
 *  stay. The layer stays. */
fun meetConclusion(sc: Conclusion, dp: Pattern): Conclusion = when {
    !sc.fact.tail.isAny -> sc                                     // `$`; `*` stays whole (a FLOW conclusion, F72)
    dp.fact.tail == Tail.EXACT -> sc.copy(fact = sc.fact.copy(tail = Tail.EXACT), exclusion = ExclusionSet.Empty)
    sc.fact.tail == Tail.ANY_TAINT && dp.fact.tail == Tail.STAR -> sc.copy(exclusion = sc.exclusion.union(dp.exclusion))
    else -> sc                                                    // `[any] ∩ */E2` (the exception), `∩ [any]`
}

/** §6.4. Restrict the summary conclusion `sc` (the `g` of `j → g`) of the premise `sp` (the `j`) by the demand
 *  pattern `d` (in the callee): the intersection, mark-aware. The result is `g'`, in the layer and with the mark of
 *  `sc`. */
fun restrict(sp: Pattern, sc: Conclusion, d: DemandPattern): Conclusion? {
    val dp = d.exit ?: return null                           // the demand does not reach the exit
    if (!insideDemand(sp, d.entry)) return null              // the premise lies inside D-c: locations (reads Ej, §3.4)
                                                             // and marks
    if (!marksMeet(dp.fact.mark, sc.fact.mark)) return null  // the mark of the conclusion meets the mark of D-p
    if (sc.fact.base != dp.fact.base) return null
    val p = dp.fact.path
    val q = sc.fact.path
    return when {
        q == p -> meetConclusion(sc, dp)                                         // at D-p: the meet
        q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null     // below D-p: keeps E
        p.startsWith(q) -> when (sc.fact.tail) {                                // above D-p
            Tail.ANY, Tail.ANY_TAINT ->
                if (!sc.exclusion.admits(p.drop(q.size))) null                   // E of `[any-taint]/E` (W8)
                else if (dp.fact.tail == Tail.EXACT)                             // the chain of D-p, the layer stays
                    sc.copy(fact = sc.fact.copy(path = p, tail = Tail.EXACT), exclusion = ExclusionSet.Empty)
                else sc.copy(fact = sc.fact.copy(path = p),
                    exclusion = if (sc.fact.tail == Tail.ANY_TAINT && dp.fact.tail == Tail.STAR) dp.exclusion
                                else ExclusionSet.Empty)                         // [any-taint]/E2 under */E2 (W8)
            Tail.STAR -> if (sc.exclusion.admits(p.drop(q.size))) sc else null   // a FLOW conclusion (F72)
            else -> null                                                         // `$`: no common location
        }
        else -> null
    }
}
```

### 6.5 The start fact

| initial fact `i` | start conclusion | layer |
|---|---|---|
| `(x, p, */E, *)` | `(x, p, */E, *)` (identity) | normal |
| `(x, p, */E, T)` | `(x, p, [any], {}, T)` (W2) | demand |
| `(x, p, [any], m)` | `(x, p, [any], {}, m)` | demand |
| `(x, p, [any-taint], E, T)` (a must-premise; forward restricted runs only) | `(x, p, [any-taint], E, T)` (itself, with its exclusion) | normal |
| `(x, p, $, m)` | `(x, p, $, {}, m)` | normal |

A premise never has the mark `*∖X` (§2.2). The row `(x, p, */E, *)` is the policy fact and the position answer of run 1
and, since F72, the FLOW premise of a restricted run (the FLOW form of a `*` pattern, §6.3): it starts with the
identity, in the normal layer, so its edges are FLOW (§7.2) and its normal summaries can be records (§8.7 R1). Before
F72 a restricted run had no such premise. Lean: `startFact`, `startFact_sound`; the must-premise with its exclusion:
`AnyTaintEx.startX` (`AnyTaintEx.Vec.start_must`; its edge is END-EXACT, `AnyTaintExExact.startX_must_end`; round 1
`AnyTaint.startT`). An `[any-taint]` premise occurs only in a forward restricted run: the emission of an
`[any-taint]/E` added fact (§6.3). The backward run has none (W8 (d)): its any-tail premises are `[any]`, and every
edge of them is a demand edge (`AnyTaintSim.DB_any_premise_demand`, under C3 of the concrete design and
`BExact.SeedsConc`; since F72 an `[any]` premise comes only from a concrete pattern, and a `*` pattern with the tail
`[any]` gives the FLOW form `*/{}` instead, §6.3). Run 1 has
none: the policy fact, the chain
answers and the mark answer on a static premise are not `[any-taint]` (§4.5, §4.10 item 4, §6.2). The start fact of a
must-premise relates every admitted premise continuation to every admitted continuation of the conclusion, as if a
source fired at the method entry: its edges are end-exact, not exact pair by pair (§1). The zero fact starts as
itself, in the normal layer. A position answer `(S, p, *, {}, *)` starts with the identity, in the normal layer
(§4.10). The interpreter adds the start rules of a method: the filter of the start fact by the context type, and the JVM entry rules
of the zero fact (`interpreter.md` §4.3).

### 6.6 The run sequence

* The analysis ALTERNATES forward and backward runs: run 1 (forward), run 2 (backward), run 3 (forward), and so on. The
  field limit INCREASES from run to run (W3 needs at least that it does not decrease). The iteration driver and its
  budget are out of scope of this spec (`analyzer-core.md` §7: one budget for the whole analysis, and each run gets
  the rest of it); the stop rules that it applies are below (THE STOP RULES). The fact domain grows with the field
  limit, so the iteration does not stop by itself. But after run 1 the DEMAND only shrinks: each run hands off only its
  demand edges (§9.2); a method key of which a forward run hands off no demand edge (for example: all its summary
  leaves are crossable), and with no seed of the next backward run in its call subtree, is analysed only from the zero
  fact in the next forward run (THE EXCLUSION, below); and every demand pattern of forward run `n + 4` with an exit
  pattern lies inside a demand pattern of forward run `n + 2` of the same method key, in the locations and the marks
  (THE NARROWING, below; the zero demand and the patterns of the seed paths are not narrowed). (These are theorems of
  the concrete design; for F72 they are PENDING, §11.2.)
* The theorems of this section are about complete runs: a complete run reached the fixed point of its rules (S6). An
  INCOMPLETE run is not that fixed point, so no theorem applies to it or to a run after it. An incomplete run (forward
  or backward) adds nothing to the report and refutes nothing (§8.10). So if run 1 is incomplete, the report has no
  entry and the output is empty (§8.10).
* Run 1 uses the rules of run 1 (§6.1). Each later run uses the rules of a restricted run (§6.1) with the demand that
  the run before it gives (§9.2), its own field limit and the persisted records (§8.7). Lean `RCov.runSeq` and
  `HandoffMain.canonState` number only the forward runs: `runSeq k` and `canonState k` are run `2k + 1`, and the
  demand of run `2k + 3` comes from the backward run `2k + 2` (`HandoffMain.backOf`; with the source seeds:
  `FSeeds.runSeqSrc`, the same numbering). Below, forward run `n + 2` is the forward run after forward run `n`.
* CONTRACT B. The backward run `n + 1` between the forward runs `n` and `n + 2` must satisfy contract B. Let forward
  run `n` report a vulnerability at the sink pattern `s` (with the concrete mark `T`) at the node `x` of the method `M`,
  and let backward run `n + 1` seed it (THE SEEDS, below). Let `W` be a witness of it (§3.5) that run `n` JUSTIFIES:
  1. at each call down in `W`, run `n` has an initial fact of the callee that covers the entry location of the callee,
     with its mark;
  2. at each call in `W` that returns, run `n` has a PUBLISHED summary piece `j → g'` of the callee (§8.5: the summary
     edge `j → g` as run `n` published it) such that `j` is an initial fact that covers the entry location of the
     callee (with its mark), and the pair (entry location, exit location) is a pair of `j → g'` (§3.2); or run `n`
     read a crossable record `j → g` of the callee (§8.7 R5) whose premise covers the entry location and that has the
     pair.

  Then the hand-off of backward run `n + 1` to forward run `n + 2` DEMANDS OR RECORDS `W` (§1):
  1. at each call down in `W`, a demand pattern of the callee has a `D-c` that covers the entry location of the
     callee, with its mark;
  2. at each call in `W` that returns, ONE demand pattern of the callee has both parts: a `D-c` that covers the entry
     location of the callee, with its mark, and a `D-p` that covers the exit location, WITH ITS MARK (the restriction
     tests the marks, §6.4; the backward run gives it: its emitted premise at the forward exit covers the exit location
     with its mark, `HandoffBackward.seg_genN`: it has the concrete mark of its requirement under a concrete pattern,
     and since F72 it is the FLOW form, with every mark, under a `*` pattern); or forward run
     `n + 2` has a crossable record of the callee (a record that run `n` read, a crossable summary leaf of run `n`, or
     the reversal of a crossable backward summary leaf of run `n + 1`, §8.7 R3) whose premise covers the entry
     location and that has the pair;
  3. every unconditional source step of `W` outside the recorded calls is a source seed of forward run `n + 2` (§9.2),
     so `W` is a witness of the program that forward run `n + 2` analyzes.

  Lean: `Handoff.BackwardContractN` (with `Handoff.ReachRDN`, `FlowRDN` for the justified witness, `Handoff.ReachRR`,
  `FlowRR` for the demanded-or-recorded witness, and `HandoffBackward.NextRecs` for the records of forward run
  `n + 2`). Item 3 is proved for the hand-off of the demand edges: `HandoffSrc.B_srcN` gives the contract into the
  seeded program `FSeeds.keepSources P σ` for every `σ` that contains the source hits of the backward run
  (`HandoffSrc.seg_genN_src`, `reach_of_db_genN_src`, `demanded_genN_src`; a recorded call reads no seed). For the
  earlier hand-off it is `FSeeds.B_src` (with `Backward.BackwardContractD`). The model has the statement sources only
  (§11.2).
* CONTRACT B WITH MODES (F72; PENDING, §11.2). These theorems are about the concrete restricted runs. Since F72 a
  demanded call has a MODE: ABSTRACT if a `*` pattern demands it, CONCRETE if a concrete pattern demands it. In the
  abstract mode the inner flow of the callee must be MARK-AGNOSTIC: every statement step uses a micro edge with a `*`
  premise mark; every cleaner step has a cleaner whose mark is not the mark of the location (or the all-marks
  cleaner); every nested call is in the abstract mode, or is crossed by a record with a `*` premise. In the concrete
  mode the inner flow is as before, and the nested calls have either mode. Contract B with modes: an abstract-mode
  call that a FLOW summary justifies meets a `*` pattern in forward run `n + 2` (the backward run weakens the
  requirement to `*`, its `*` analysis covers the reversed mark-agnostic flow, and the hand-off gives a `*` pattern);
  a concrete-mode call that a concrete summary justifies meets a concrete pattern (the backward run keeps the concrete
  mark). Run 1 picks the right mode: it justifies every real witness, at each call by a FLOW premise (then the inner
  flow is mark-agnostic: the coverage followed it with no request) or by an answer (a concrete premise). THE CLAIM R6
  OF F72: every flow that needs a concrete mark is demanded by a concrete pattern or crossed by a concrete record, and
  every flow that a `*` pattern demands needs no concrete mark. So no request is needed after run 1, and every forward
  run still reports every real vulnerability that no earlier run confirmed. A sink fires only under a concrete premise
  (§4.9), so the confirmation does not change. The proof is the pending task of §11.2 (lemmas L1 to L6;
  `ap-history.md` F72).
* Every forward run justifies a witness of each real vulnerability that it reports: run 1 every real witness
  (`Handoff.run1_justifies`), a restricted forward run every demanded-or-recorded witness (`Handoff.reach_strongRN`;
  the forward contract `Handoff.CoversN`, `coversN_DR`). The backward run of §9.2 satisfies contract B under S11
  (`HandoffBackward.B_generalN`; for the canonical demand and records `B_generalN_canon`). The iteration driver must
  give the backward run at least the demand edges of the forward run, the reversals of its crossable records and the
  sink seeds of §9.2, and give the next forward run at least the demand of §9.2, the records of
  `HandoffBackward.NextRecs` and the source seeds of §9.2. More demand and more records keep the theorems
  (`HandoffMain.iteration_generalN_incl`). (The concrete design. For F72: CONTRACT B WITH MODES above, PENDING.)
* THE SEEDS. The backward run after forward run `n` seeds the sink witnesses of the DEMAND vulnerabilities (§1): the
  vulnerabilities whose state in the report is DEMAND after run `n`, reported by run `n` and confirmed by no complete
  forward run so far (§8.10, §9.2). A CONFIRMED vulnerability is final (§8.10; it is real, §4.9), so the backward run
  does not seed it, also when run `n` reports it only as a demand vulnerability of that run. One more rule gives sink
  seeds: THE TRIGGER OF AN END FACT (§9.2). When the reversed end-fact edge of a sink alternative applies to a
  requirement, the backward run fires the sink seeds of that alternative at its method key and statement, also when
  its vulnerability is CONFIRMED: an end fact exists only after its sink triggers, so the next forward run must have
  the witness of the trigger (argued, §11.2).
* THE ITERATION THEOREM. Let `C k` say that a vulnerability is confirmed by some forward run up to forward run `k`.
  By THE SEEDS, every vulnerability that forward run `k` reports is confirmed (`C k`) or seeded. So at every complete
  forward run, every real vulnerability (a sink pattern with a concrete mark and the tail `$` or `[any]`) is REPORTED
  by that run, in some layer (CONFIRMED or DEMAND), or was CONFIRMED by an earlier complete forward run
  (`HandoffMain.iteration_generalN`, on the canonical run sequence of the spec rules `HandoffMain.canonState`; the
  abstract form `HandoffIter.iteration_abstract_or`; if every reported vulnerability is seeded, every complete forward
  run reports it, `HandoffMain.iteration_generalN_all`; for a driver that hands off more demand and more records,
  `HandoffMain.iteration_generalN_incl`). The hypotheses are S10 with S5 (`Program.WF`) and S11 (a) to (f), as for the
  earlier theorem. These forms run every source; with the source seeds of §6.1 rule 6 (the statement sources):
  `HandoffSrc.iteration_srcN`, on the canonical sequence `HandoffSrc.iteration_srcN_canon`. For a sequence that stops
  after forward run `K` (the hypotheses only for the runs before `K`): `HandoffUpto.iteration_generalN_upto`,
  `iteration_generalN_canon_upto`, with the source seeds `HandoffSrc.iteration_srcN_upto`. With the
  `[any-taint]` tail and its exclusion (run 1 `AnyTaintEx.D6X`, the forward restricted runs `AnyTaintEx.DRX` with
  `emitX`, `satX` and `HandoffX.restrictIX`, the backward runs `Backward.DB`, which read each forward run with its
  exclusions dropped, §9.2): `HandoffXIter.iteration_generalNX` (with every reported vulnerability seeded
  `iteration_generalNX_all`, `iteration_reportsNX_canon`; for a driver that hands off more `iteration_generalNX_incl`,
  `iteration_reportsNX`; with the source seeds `HandoffSrc.iteration_srcNX`; finite `HandoffUpto.iteration_generalNX_upto`,
  `iteration_generalNX_canon_upto`, `HandoffSrc.iteration_srcNX_upto`), with no hypothesis on the
  taint edges or on the exactness of the records. THE PIPELINE DRIVER (`analyzer-core.md` §7): with the seeds of THE
  SEEDS (the DEMAND entries only; `C k` = confirmed by a complete forward run up to `k`, in the sense of §4.9)
  `PipelineHandoffDriverExt.driver_iterationNX_demand` (on the final states `driver_iterationNX_demand_known`); for a
  driver that stops after forward run `K` `driver_iterationNX_upto`; with the source seeds `driver_iteration_srcNX`,
  `driver_iteration_srcNX_upto`; with every reported vulnerability seeded `PipelineHandoffDriver.driver_iterationNX`.
  (`PipelineHandoffDriverExt.driver_iterationNX_confirmed` is the instance with `C k` = "a forward run up to `k`
  reports it in the normal layer". That test is weaker than CONFIRMED, which also needs the support (§4.9), so it is
  not the confirmation of this spec.) So the analysis can stop at any complete forward run. The report
  reads the complete forward runs only, it holds every confirmed vulnerability and the DEMAND entries of the latest
  complete forward run, and the output holds every entry of the report (§8.10; `ap-history.md` F68), so the output
  holds every real vulnerability. (The earlier hand-off, with every reported vulnerability seeded:
  `Backward.iteration_general`, with the source seeds `FSeeds.iteration_src`, for any backward step that satisfies its
  contract B `Backward.iteration_sound_M_D`; with the `[any-taint]` tail `AnyTaintExCov.iteration_reportsX`,
  `iteration_srcX`, for the driver `PipelineAnyTaintExDriver.driver_iterationX`, `driver_iteration_uptoX`,
  `driver_iteration_srcX`; §10.7, §10.11.) THESE ITERATION THEOREMS ARE PROVED FOR THE CONCRETE RESTRICTED RUNS of F70
  and F71. For the rules of F72 the iteration theorem is the claim R6 with CONTRACT B WITH MODES (above), and its
  proof is PENDING (§11.2): as `HandoffMain.iteration_generalN`, with the F72 closures and the modes.
* THE EXCLUSION (a method key leaves the analysis). Let complete forward run `n` hand off no demand edge of the method
  key `M` (§9.2; the frontier counts the demand edges per method key, §1), and let no seed of backward run `n + 1` lie
  in a method that `M` reaches through calls (`M` included). Then backward run `n + 1` has only zero-premise edges with
  the zero fact in `M`, its hand-off gives `M` only the zero demand, and forward run `n + 2` has only the zero fact as
  an initial fact of `M`, and every edge of `M` there has the zero premise: it analyses `M` only from the zero fact,
  and the callers cross `M` by its records (`HandoffExclusion.exclusion_theorem`, for every backward demand that has
  no demand edge of `M`; its parts `HandoffExclusion.exclusion_backward_nodem`, `exclusion_demand`,
  `forward_zero_init`, `forward_zero_edges`). A SUFFICIENT CONDITION: every summary leaf of `M` in run `n` is crossable
  (§1), so run `n` hands off no demand edge of `M` (`HandoffExclusion.exclusion_round`, for every backward demand
  inside the forward hand-off; on the canonical sequence `HandoffMain.exclusion_canon`). With the `[any-taint]`
  exclusion (the forward runs `AnyTaintEx.DRX`, read by the hand-off without the exclusions): the backward parts are
  the base theorems, the forward parts are `HandoffXMain.forward_zero_initX`, `forward_zero_edgesX`, the round
  `HandoffXMain.exclusion_roundX`, and on the canonical X sequence `HandoffXMain.exclusion_canonX`. THE NEXT ROUNDS. In forward
  run `n + 2` the method key `M` has only the zero demand `(zero, none)`. In a restricted run a zero-premise summary is
  published only through a demand pattern `(zero, jb)` with an exit pattern (§6.4: no `D-p`, no result;
  `HandoffCases.restrictI_none`), so `M` publishes nothing, and forward run `n + 2` hands off no demand edge of `M`.
  So the hypothesis holds again, and `M` stays out while no seed lies in its call subtree. Over several rounds this is
  the one-round theorem applied again (argued, §11.2). Hypotheses: the only micro edge into the
  zero base is the zero keep edge, the only binding into the zero base of the callee is the zero binding, and no
  binding back targets the zero base (`HandoffExclusion.NoZeroGenP`; `interpreter.md` I11 (c), (d)); no cleaner is on
  the zero base (S11 (d)); the seeds have concrete marks (`BExact.SeedsConc`). (The theorems read the concrete runs.
  F72 does not add an emission without a demand pattern, so the argument is the same; the theorem for the F72 closures
  is PENDING, §11.2.) Program WRAP (`HandoffCases.lean`; the
  field limits 1, 2 and 3):

  ```java
  root():    x.a.b.c = source();  r = wrap(x);  sink(r.f.a.b.c);
  wrap(arg): z = new Z();  z.f = arg;  return z;               // the model: ret.f = arg
  ```

  Run 1 gives `wrap` only the complete summary `(arg, ., *) → (ret, .f, *)`, and it is crossable
  (`HandoffCases.Wrap.inv_w1`, `w1_exit_cross`, `w1_wrap_exits_cross`). With the EARLIER hand-off, backward run 2
  enters `wrap` with the premise `(ret, .f.a, [any], T)` (`old_b2_wrap_init`) and hands off the pattern
  `((arg, .a, [any], T), (ret, .f.a, [any], T))` (`old_demOf_exact`); forward run 3 emits `(arg, .a.b.c, $, T)` into `wrap`
  and cuts inside `wrap`: a demand-layer edge in `wrap`, which had none in run 1 (`old_f3_wrap_init`,
  `old_f3_wrap_cut`, `w1_wrap_normal`). With the hand-off of the demand edges, run 1 hands off no demand edge of
  `wrap` (`handF_w1_exact`); backward run 2 crosses `wrap` by the reversed record (`bn_cross`) and has only the zero
  fact in `wrap` (`bn_wrap_zero_only`); its hand-off gives `wrap` only the zero demand (`demN_exact`); forward run 3
  analyses `wrap` only from the zero fact (`fn_wrap_zero_only`, `fn_wrap_edges_zero`), and it still reports the
  vulnerability (`fn_found`): the record of `wrap` applies in `root` by `applicable` (`fn_record_applicable`), and the
  cut is in `root` (`fn_cut_in_root`). Together: `wrap_old_vs_new`.
* THE NARROWING (the search space only shrinks). Every demand pattern that forward run `n + 2` hands off lies inside
  the reversal of the demand pattern of run `n + 2` that published it, in the locations AND the marks (the restriction
  tests the marks, §6.4; `ap-history.md` F71): its `D-p` (the premise `j`) lies inside the `D-c` of that pattern, and
  its `D-c` (the piece `g'`) lies inside the `D-p` of that pattern (`HandoffMain.narrowing_canon_fwdM`, the location
  form `narrowing_canon_fwd`; for one run `Handoff.handF_narrowM`, `handF_narrow_locM`, the location forms
  `Handoff.handF_narrow`, `handF_narrow_loc`). The same holds for the backward demand edges with a non-zero premise
  (case 3 of §9.2; `HandoffMain.narrowing_canon_backM`, for concrete seeds, `narrowing_canon_back`;
  `Handoff.demOfN_narrowM`, `demOfN_narrow`). The general forms keep the cells (a) and (b) of §6.4 (`Handoff.RExc`) as
  exceptions on the locations, and the forms of one run also the cell (c) on the marks (an abstract conclusion mark).
  On the canonical sequence every run is concrete, so (c) does not occur, and in the cells (a) and (b) the marks still
  narrow. With the hand-off of the demand edges no demand pattern has a `*` tail (§6.4;
  `HandoffNoStar.canon_dem_nonstar`, for concrete seeds with no `*` tail), so the exceptions do not occur: the forward
  narrowing is exact from forward run 3 on (`HandoffNoStar.narrowing_canon_fwd_exactM`, the location form
  `narrowing_canon_fwd_exact`), and the backward narrowing is exact after every restricted forward run
  (`HandoffNoStar.narrowing_canon_back_exactM`, `narrowing_canon_back_exact`; after run 1 only the cell (a) at a `*/{}`
  exit pattern, a policy fact of §6.2, which adds no location, `narrowing_canon_back_loc`). So THE NARROWING THEOREM:
  every demand pattern of forward run `n + 4` WITH AN EXIT PATTERN (case 3 of §9.2: a fact-to-fact demand edge) lies
  inside a demand pattern of forward run `n + 2` of the same method key, in the locations and the marks, with no
  exception: its entry pattern inside the entry pattern, its exit pattern inside the exit pattern, every location with
  its mark (`HandoffNoStar.narrowing_canon_loc_exactM`; the location form `HandoffNoStar.narrowing_canon_loc_exact`;
  the form with the exception cells `HandoffMain.narrowing_canonM`, `narrowing_canon_locM`, and the location forms
  `HandoffMain.narrowing_canon`, `narrowing_canon_loc`, whose exceptions do not name the edge,
  `HandoffNoStar.base_loc_exception_weak`). The theorem does not narrow the zero demand and the patterns `(gb, none)`
  of the zero-premise backward edges (case 2 of §9.2, the seed paths): as locations they shrink when the backward
  field limit grows (argued, §11.2), but their COUNT can grow. With the `[any-taint]` exclusion the narrowing of one
  hand-off holds with the exclusions and the marks read (`HandoffX.handF_narrowXM`, `handF_narrowX_DRXM`,
  `restrictIX_narrowM`; the location forms `HandoffX.handF_narrowX`, `handF_narrowX_DRX`, `restrictIX_narrow`), and
  the narrowing over one round on the canonical X sequence, with the exclusions and the marks of the forward piece and
  premise read, is `HandoffXMain.narrowing_canonX_fwdM`, `narrowing_canonX_backM`, `narrowing_canonXM` (in the
  exception cells the marks still narrow; the location forms `HandoffXMain.narrowing_canonX_fwd`,
  `narrowing_canonX_back`, `narrowing_canonX`, `narrowing_canonX_loc`). On the patterns that the hand-off reads
  (without the exclusions, §9.2) a step can be coarser at the operation level (`HandoffX.XVec.v_inside_only_with_excl`;
  the composed location form has the alternative `HandoffXMain.Dropped`: a location that a dropped exclusion
  excludes; vectors `HandoffXMain.XMVec.exit_dropped`, `entry_dropped`). With no `*` pattern it is exact on the exit
  side, and on the entry side except for a premise with the exclusion Universe (`HandoffNoStar.narrowing_canonX_fwd_exact`,
  `narrowing_canonX_loc_exact`; vector `HandoffNoStar.NSVec.entry_univ`), which the AP does not have (S8). These exact
  X forms are stated as locations; the marks narrow on the X sequence by `HandoffXMain.narrowing_canonXM`. THE
  NARROWING AND F72: these theorems read the concrete restricted runs. Since F72 demand patterns with a `*` tail and
  the mark `*` occur (§6.4), so the exceptions (a), (b) and (c) of §6.4 can occur, and the exact forms
  (`HandoffNoStar.narrowing_canon_fwd_exactM`, `narrowing_canon_back_exactM`, `narrowing_canon_loc_exactM`, their
  location forms and `narrowing_canonX_fwd_exact`, `narrowing_canonX_loc_exact`) do not describe the F72 runs. The
  hand-off normalization of F72 (`*∖X` becomes `*`, §9.2) makes a pattern larger in its marks. The narrowing for the
  F72 runs is part of the pending model (§11.2).
* THE STOP RULES. After a COMPLETE forward run (§1) the driver stops the iteration when one of these holds
  (`analyzer-core.md` §7.1, `EndReason`):
  1. `STOP_RULE`: after the run the report has no DEMAND entry (§1, §8.10, THE SEEDS). Then the next backward run has
     no seed, so it has no requirement (and so no trigger of an end fact fires). The report is final for its
     CONFIRMED part: every real vulnerability is CONFIRMED by a complete forward run up to this one (by THE ITERATION
     THEOREM with `C k`, this run reports it or an earlier run confirmed it, and with no DEMAND entry every vulnerability
     that this run reports is CONFIRMED; for the driver `PipelineHandoffDriverExt.driver_iterationNX_upto`), and a
     CONFIRMED entry is final. That every later forward run only repeats the zero fact and the records is argued
     (`HandoffExclusion.zinv_all` for every method with no seed, then `HandoffExclusion.exclusion_demand` per method;
     the composition is not stated, §11.2).
  2. `NO_DEMAND_EDGE`: the run has no demand-layer edge, no demand-layer summary edge (§8.5) and NO DEMAND LINK (a
     link whose added fact is in the demand layer, §8.3). Then every sink edge of the run is normal, every link is
     normal, and every premise of a triggered normal sink edge is the zero fact, an exact concrete fact or a
     must-premise (a restricted run: `RExact.complete_premise_exact`, `AnyTaintExKinds.DRX_normal_premise`, for the
     concrete design; since F72 a normal edge can also have a FLOW premise, but a sink never triggers under it, §4.9;
     run 1: a `*` premise with a concrete mark starts in the demand layer, §6.5). So each sink witness satisfies conditions 1
     and 2 of §4.9 and the normal link of condition 3.2.2, and a DEMAND entry of the run fails only the joint support
     of a conjunction (condition 3, §4.6): no one call supplies all the premises of its sink edges. That a later
     forward run cannot supply them at one call either is argued, and it is an open question (§11.2). So this rule
     does not make the report final: its DEMAND entries stay in the output (§8.10).
  3. `POLICY` and `ABNORMAL`: as before (`analyzer-core.md` §7.1).

---

## 7. Representation (the optimization)

The concept of a conclusion is a set of path facts. The representation groups path edges into TREES.

### 7.1 Initial fact and premise key

```kotlin
/** The initial fact (premise): one linear path. Its mark is * or a concrete mark (never *∖X). It is also the premise
 *  key of a premise set with one member (below). */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,           // interned, linked from the root node; no [any], $ or mark accessors (W4, W5)
    val tail: Tail,                // ANY_TAINT: a must-premise, only in a forward restricted run (W8), concrete mark
    val exclusion: ExclusionSet,   // Empty in run 1; a restricted run can emit the exclusion of a `*/E` demand
                                   // (the FLOW form of a `*/E` pattern, F72);
                                   // a must-premise has the exclusion of its `[any-taint]/E` added fact (W8)
    val mark: MarkSlot,            // `*` (a FLOW premise: run 1, and since F72 a restricted run) or concrete
) : PremiseKey {
    fun toPattern(): Pattern       // the list form of §3.4, for the reference forms
}

/** The premise SET of an edge (§4.6): never empty. ONE member is the common case (the zero fact, a policy fact, an
 *  answer, an emission): the InitialAp itself is the key, with no wrapper. Two or more members: a PremiseSet, a
 *  canonical array (sorted by the intern id, no duplicates): an ND edge. No member is the zero fact (§4.6), every
 *  member has a concrete mark, and its edges are TAINT (§7.2). Both are interned, so equal keys are the same object. The layer is not part of the premise key; every store
 *  key that needs the layer has it as a separate part. */
sealed interface PremiseKey {
    val size: Int
    fun member(k: Int): InitialAp
    val isZero: Boolean            // the premise set {zero}: the one member is the zero fact
    val nonZeroCount: Int          // §4.6: 0 a zero-to-fact edge ({zero}), 1 a fact-to-fact edge, >= 2 an ND edge
}
class PremiseSet(val members: Array<InitialAp>) : PremiseKey      // size >= 2
```

`PathNode` is the current `AccessPath.AccessNode` without the `[any]`, `$` and mark accessors.

The tail and the exclusion are part of the premise key. So the must-premise `(x, p, [any-taint], E, T)`, a
must-premise at the same path with another exclusion, and the `[any]` premise `(x, p, [any], T)` are different
premise keys, with their own edges and summaries: a must-premise starts in the normal layer, the `[any]` premise in
the demand layer (§6.5). One path gets several when must and may added facts meet a demand at that path (§6.3). A
published summary edge and a record keep the tail and the exclusion of their premise (§8.4, §8.7; Lean: the
publication of `PipelineAnyTaintEx.sysDRX` carries the must flag and the exclusion of the callee premise, and a link
the added fact with its flag and its exclusion; round 1 `PipelineAnyTaint.sysDRT`).

### 7.2 Conclusions: three kinds

The conclusions of one edge group have ONE CONCLUSION KIND (§1). The premise mark separates FLOW from the other two
kinds: a premise with the mark `*` has FLOW conclusions, and the zero premise or a concrete premise has REACH or TAINT
conclusions. The base of the conclusion separates REACH from TAINT: a conclusion on the zero base (the zero fact) is
REACH, a conclusion on every other base is TAINT. So one premise set can have conclusions of two kinds, in two edge
groups: for example `{zero}` has the zero fact (REACH) and the result of a source (TAINT).

| Kind | Premise set | Conclusions | Normal layer | Demand layer |
|---|---|---|---|---|
| REACH | `{zero}` (a zero-to-zero edge); in the backward run also a concrete requirement `{jb}` that reached an unconditional source or an end-fact action (§9.2) | the zero fact | one bit | one bit |
| FLOW | one initial fact with the mark `*`: a policy fact or a position answer (run 1), or, since F72, the FLOW premise of a `*` pattern (a restricted run, §6.3) | abstract marks only: `*∖X`, with `X` the mark exclusion of the tree | `*` leaves, with the exclusion of the tree | `[any]` leaves, no exclusion |
| TAINT | `{zero}` (a source), concrete initial facts (also a must-premise `[any-taint]/E`, forward restricted runs only), or a set of them: EVERY premise set with two or more members (an ND edge, §4.6) | concrete marks only | `$` and `[any-taint]` leaves, with ONE exclusion of the tree for its `[any-taint]` leaves | `$` and `[any]` leaves, no exclusion |

The reasons: a `*` premise has only abstract conclusions (S7: a micro edge with a concrete target mark has a concrete
premise mark; a summary with a concrete premise does not apply to an abstract fact, §4.3). A concrete premise has only
concrete conclusions (`Coverage.edge_conc`). A `$` leaf has a concrete mark (S8: a `$`-target edge has a concrete
premise mark). A `*` leaf has an abstract mark and is normal (W2), and an `[any]` leaf is demand (W6). An
`[any-taint]` leaf has a concrete mark and is normal (W8), so it is TAINT and a FLOW tree has none: in run 1 under S15
and S10 (for the spec closure `AnyTaintEx.D6X`: `AnyTaintExKinds.D6X_any_conc`, `D6X_flow_no_any_taint`, the latter
also under S7, and a FLOW edge carries no exclusion, `D6X_flow_no_excl`; the packed partition
`AnyTaintExKinds.kinds_D6X`; round 1, for `AnyTaint.D6T`: `AnyTaintSim.D6T_any_conc`, `D6T_flow_no_any_taint`, also
under `W6.SummaryStar`, and `kinds_D6T`), in a forward restricted run of the concrete design because the run is
concrete (`AnyTaintExExact.DRX_conc`; a normal edge has a `$` premise or a must-premise,
`AnyTaintExKinds.DRX_normal_premise`, under C3; round 1 `AnyTaintSim.kinds_DRT`), and in an F72 run because a FLOW
premise meets no taint edge and no summary of a concrete premise: both need a concrete mark (§4.5; argued, PENDING
§11.2). Lean (§10.10):
`Kinds.kinds_D` packs the partition of run 1 (`flow_abstract`, `flow_no_exact`, `taint_concrete`, with W2
`Invariant.final_star_legal`); `Kinds.kinds_DR` and `Kinds.kinds_DB_taint` give REACH and TAINT only for the
concrete restricted runs (the claim is false for the F72 runs). The kinds theorems do not include W6; W6 is modelled
for `D` and `DR` in `W6.lean` (§10.3), and W6 with W8 (the rule W6T) in `AnyTaintSim.lean` and, with the exclusion, in `AnyTaintExKinds.lean` (§10.11).
`Kinds.kinds_D` is the run without the static rule and the conjunctions; the partition for run 1 with the static rule
(`Statics.DS`) or with the conjunctions (`NDZ.DNz`: its single-premise edges; its ND edges are `Kinds.ndz_taint`) is
argued (§11.2). So the
representation ENFORCES W1, W2, W6 and W8 by its types: a FLOW tree has no `$` leaf, no `[any-taint]` leaf and no
concrete mark; a TAINT tree has no `*` leaf and no mark exclusion; a normal TAINT tree has ONE exclusion, the
exclusion `E` of its `[any-taint]` leaves (W8; a part of the tree key, as the exclusion of a FLOW tree), and a demand
TAINT tree has the Empty exclusion; a normal tree has no `[any]` leaf; a demand tree has no `[any-taint]` leaf. The
layer of a TAINT tree gives the name of its any leaves: `[any-taint]` in a normal tree, `[any]` in a demand tree. Two
`[any-taint]` results of one premise key with different exclusions go to two TAINT trees (Lean: one annotated fact
`AnyTaintEx.XFact` per conclusion). Before F72 the restricted runs (forward and backward) were concrete: they had
REACH and TAINT conclusions only, and a FLOW tree occurred in run 1 and as the conclusion of a run-1 record with a `*`
premise (§8.7), which applies to a TAINT fact as a transfer function. SINCE F72 A RESTRICTED RUN CAN HAVE FLOW TREES:
the edges of its FLOW premises (§6.3) and the conclusions of `*`-premise records. The reasons above hold for them: a
FLOW tree has no `$` leaf, no `[any-taint]` leaf and no concrete mark (argued, PENDING §11.2).

```kotlin
/** The conclusions of one edge group at a node. */
sealed interface Facts { val base: AccessPathBase; val layer: Layer }

/** REACH: the zero fact (§2.4) is at the node. */
class Reach(override val layer: Layer) : Facts { override val base get() = AccessPathBase.Zero }

/** FLOW: a trie of paths; a leaf flag at a node is the leaf `p.*` (normal) or `p.[any]` (demand), with the mark `*∖X`. */
class FlowTree(
    override val base: AccessPathBase,
    override val layer: Layer,
    val exclusion: ExclusionSet,   // the exclusion of the `*` leaves (W1); always Empty in the demand layer
    val markExclusion: MarkSet,    // X of `*∖X`; empty for most trees
    val root: FlowNode,            // FlowNode(leaf: Boolean, accessors, children)
) : Facts

/** TAINT: a trie of paths; at a node, the marks of the `$` leaves and of the any leaves. In a normal tree `any` holds
 *  the marks of the `[any-taint]` leaves (W8), in a demand tree the marks of the `[any]` leaves (W6). */
class TaintTree(
    override val base: AccessPathBase,
    override val layer: Layer,
    val exclusion: ExclusionSet,   // the exclusion E of the `[any-taint]` leaves (W8); always Empty in the demand layer
    val root: TaintNode,           // TaintNode(exact: MarkSet, any: MarkSet, accessors, children)
) : Facts

// Both node types keep `boundedDepth`: the max number of counted accessors on a path below; the O(1) limit check.
```

Rules:

* T1. Merge rule 1: two trees with the same key merge by union.
* T2. Merge rule 2 (normal FLOW trees): two trees with the same premise, layer, mark exclusion and EQUAL content merge
  into one tree with the intersection of the exclusions (`Tree.rule2_den`). Not valid for different contents. The
  same for two normal TAINT trees with the same premise and layer and EQUAL content: the intersection of the
  exclusions of their `[any-taint]` leaves (§3.3; argued, §11.2).
* T2'. Merge rule 2 for marks (FLOW trees): the same with the mark exclusions (`Tree.rule2_mark`).
* T3. No union of exclusions or mark exclusions across trees. No merge across layers. No merge across conclusion
  kinds.
* T4. `add` returns the new part only (the delta), as `mergeAddDelta` does today. Exception: when merge rule 2 shrinks an
  exclusion or a mark exclusion of a stored tree, the delta is the WHOLE merged tree with the new exclusion.
* T5. Inside one demand-layer tree, an `[any]` leaf at `p` may absorb every leaf below `p` with the same mark (FLOW: every
  leaf; TAINT: the leaves with the mark `m` of the `[any]` leaf). The denotation does not change. NO `$` LEAF IS
  ABSORBED UNDER `[any-taint]` IN A NORMAL TREE: inside one normal TAINT tree with the exclusion `E`, an `[any-taint]`
  leaf at `p` may absorb only the `[any-taint]` leaves with its mark `m` at `p ++ r` with `r ≠ []` and `E` admitting
  `r`; it never absorbs a `$` leaf at or below `p`. The reason: a later cleaner `part` row of §4.7 that demotes the
  `[any-taint]` leaf (the demotions of §2.2) does not touch a `$` leaf apart from the cleaner, and that `$` leaf must
  stay normal and exact. Example: the normal tree `{x: [any-taint] (T), x.g: $ (T)}`, then `clean(x.f, exact, T)`:
  the cleaner demotes `x.[any-taint] (T)` to `x.[any] (T)` in the demand layer, and `x.g.$ (T)` is disjoint from the
  cleaner and stays normal, so `sink(x.g)` stays CONFIRMED; after an absorption only `x.[any] (T)` would remain, and
  `sink(x.g)` would be a DEMAND entry. The same holds for the subsumption (§8.1).
* T6. Intern the nodes, the mark sets and the exclusion sets.

### 7.3 Delta-concat on a tree

The computation of §4.1 on all paths of one tree at once. `Ec` is the tree exclusion (of a FLOW tree, or of the
`[any-taint]` leaves of a normal TAINT tree, §7.2). The results are grouped by their
new conclusion kind, layer, exclusion and mark exclusion (§7.2). The kinds make the mark gate simple (§4.1 step 4): on
a FLOW tree an edge with a concrete premise mark `T` gives no fact, only the request `T` (run 1) if `T ∉ X` (a
restricted run: no fact and no request, F72); on a
TAINT tree it keeps the leaves with the mark `T`. A micro edge from the zero fact applies only to REACH (the zero keep
edge gives REACH, a source gives TAINT).

1. Walk `from.path` from the root node of the tree. On each proper prefix node, read its payload as the case `above`
   (`r` is the rest of `from.path` after the node):
   * a `*` leaf gives a result only if `Ec` admits `r` (Lean: `Tree.cS`);
   * an `[any]` leaf always gives a result;
   * an `[any-taint]` leaf of a normal TAINT tree gives a result only if `Ec` admits `r` (W8);
   * a `$` leaf gives nothing (no overlap).

   Each result of a `*` or an `[any]` leaf is `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer. A
   result of an `[any-taint]` leaf follows the table of the case `above` of §4.1: `$`, `[any-taint]/Et` or (a `*`
   target) `[any-taint]/E` with the edge exclusion, in the layer of the tree; or `[any]` in the demand layer (a may
   `[any]` target). Apply the mark gate to each leaf mark (step 4). Lean: `Tree.contribB`. STATIC EXCEPTION (run 1,
   a statement micro edge with its premise on `S`; the rule is §4.10 item 1, the test §4.1): a `*` leaf of an identity static `*` edge at the root path or at a class gives
   no result; it raises the position request for `from.path` cut to at most two accessors.
2. At the node of `from.path` take the subtree `U`. Filter its root by the premise tail (with the exclusion of a
   must-premise) and the edge exclusion.
3. Transform `U` by the target tail:
   * a `*` target: the child subtrees (`r ≠ []`) keep the tree exclusion and are re-rooted under `to.path`; the root
     `*` leaf (`r = []`) gets the exclusion `Ec ∪ E`, so it goes to another tree; a root `[any-taint]` leaf gets the
     exclusion `Ec ∪ E` too (the exclusion edge, W8), so it goes to another TAINT tree, in the layer of the tree;
   * an `[any]` target (a may): fold `U` into one `[any]` payload with the Empty exclusion, in the demand layer (W6);
   * an `[any-taint]` target (a taint edge, or a summary conclusion `[any-taint]/Et`): fold `U` into one
     `[any-taint]` payload with the exclusion `Et` (Empty for a micro edge), in the layer of the tree (a TAINT tree:
     no `*` leaf, so no `lostCorr`);
   * a `$` target: fold `U` into one `$` payload with the Empty exclusion. It is in the demand layer if `U` has a `*`
     leaf and its exclusion is not Empty (`lostCorr`: `Ec ∪ E` for the root leaf of `U`, `Ec` for a leaf below it).
4. Apply the mark gate per payload mark, then the target mark (§4.1 steps 4, 5; a `*∖X` target adds `X` to the mark
   exclusion and stops the concrete marks in `X`). A payload mark that the gate sends to a request gives no result for
   that mark; it raises the request `(m, i, T)` (run 1, §4.5; a restricted run raises none, F72).
5. Layer and normal form (§4.1 step 6). A result is in the demand layer if the tree is in the demand layer, if the
   applied edge is a demand-layer summary edge (§4.3), or if a step above says so. Then a result with the `[any]` tail
   is in the demand layer (W6), a demand-layer result with the `[any-taint]` tail becomes `[any]` with the Empty
   exclusion (W8), and a result
   with the `*` tail and a concrete mark, or in the demand layer, becomes `[any]` with the Empty exclusion, in the
   demand layer (W2).
6. Where §4.4 puts a cut point (for example the statement transfer), apply the field limit with `boundedDepth`; cut
   paths go to the demand-layer tree. The cut is not part of `concat` (§4.1).
7. Route each result by its own layer bit.

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `U` only. The concept form visits every path
fact (`Tree.lean`: `applyTreeE_mem`, `applyTreeE_den`, `walkSteps_le`).

### 7.4 The restriction on a tree

The restriction of §6.4 applies to all conclusions of one summary tree at once, after the premise test (the premise
key of the tree must lie inside `D-c`, in its locations and its marks, §6.4). The mark test of the conclusion acts
leaf by leaf: a mark leaf whose mark does not meet the mark of `D-p` is dropped first (§6.4, THE MARK OF THE
CONCLUSION; for a concrete `D-p` mark `T` only the leaves with the mark `T` stay, for the `D-p` mark `*` every leaf
stays). Then:

1. Walk `D-p.path` from the root node of the tree. On each proper prefix node: keep a `*` leaf whole if the tree
   exclusion admits the rest of `D-p.path`, else drop it (§6.4, the row `above`, `*/E`; before F72 a restricted run
   had no `*` leaf, and the step dropped the flag); move the marks of the any leaves to `D-p.path`, as any leaves of
   the same tree (as `$` for a `$` exit pattern); drop the `$` marks and every
   child off the chain.
2. At the node of `D-p.path`, MEET the payload with the tail of `D-p` (§6.4, THE MEET: for a `$` exit pattern every
   any leaf becomes a `$` leaf with the same mark; for a `*/E2` exit pattern an `[any-taint]/E` leaf gets `E ∪ E2`;
   every other leaf stays), add the moved marks, and keep each child whose accessor the tail of `D-p` admits (all
   children for `[any]`, none for `$`).

The result is one well-formed tree. For the earlier restriction (`restrictU`, which keeps the payload at the node of
`D-p.path` whole) the model proves the tree form (`RStore.restrictTree`): one well-formed tree
(`RStore.restrictTreeE_inv`), equal to the per-path restriction (`restrictTreeE_mem_U`), with the cost
`|D-p.path| + 1 + width` new cells and the kept subtrees shared (`restrictTree_cost`). The meet of step 2 changes only
the leaves at one node, so it keeps these properties (argued, §11.2).

On a normal TAINT tree with the exclusion `E` (§7.2), step 1 moves an `[any-taint]` mark only from a node where `E`
admits the rest of `D-p.path`, and the moved `[any-taint]` leaf has the exclusion `E2` of a `*/E2` exit pattern, else
the Empty exclusion (§6.4), so it goes to the TAINT tree of the same premise and layer with that exclusion. In step 2
a `*/E2` exit pattern adds `E2` to the exclusion of the `[any-taint]` leaves at the node, so they go to the TAINT tree
with `E ∪ E2`. The leaves below the node keep `E`. (The model `RStore.restrictTree` has no exclusion of
`[any-taint]`; the per-path form is `HandoffX.restrictConcIX`. The tree form with the exclusion is argued, §11.2.)

### 7.5 Interning

Tries are hash-consed bottom-up as today. The walk of §7.3 has no memo: it shares every unchanged subtree, and a leaf
map keeps an identity memo of the nodes that it maps (F68). A memo of the walk is a later optimization, if a profile
asks for it. `boundedDepth` is part of the node, not of the hash.

### 7.6 Relation to the current code

The prescan (§1) still runs the current core. So the new AP lives beside the current types.

| Part | Decision |
|---|---|
| `AccessorIdx` | Reuse. |
| `AccessPath.AccessNode`, accessor interning (`AccessorInterner.AccessorStorage`) | Adapt: an interned path node; the accessor and mark tables keep only the field and the class storages (`ap-impl.md` §2, §3.1). |
| `AccessTree` merge, `mergeAddDelta`, interners, identity caches | Reuse the algorithms for `FlowNode` and `TaintNode` (§7.2). |
| `AccessBasedStorage` trie | Adapt for the path indexes of §8 (`PathTrie`, `ap-impl.md` §7.2). |
| `EdgeStorage` | Replace by the conclusion group: one premise key, every base and kind (`ap-impl.md` §4.3). |
| `AccessPathBaseStorage` | Not used: it rejects the zero base; the conclusion group keys its trees by base (`ap-impl.md` §7.3). |
| Exact-key subscription maps | Reuse with the new fact types. |
| `StatementSummaryBuilder`, `buildReversed` | Adapt (`interpreter.md`). |
| `InitialFactAp`, `FinalFactAp`, `ApManager` | New types `InitialAp`, `PremiseKey` and the conclusion kinds `Reach`, `FlowTree`, `TaintTree` (§7.2). They do not implement the old interfaces. |
| `Edge` (`ZeroToZero`, `ZeroToFact` requires Universe, `FactToFact`) | The premise key and the conclusion kind (§7.2): `ZeroToZero` is REACH; `ZeroToFact` and a concrete `FactToFact` are TAINT, or REACH if the conclusion is the zero fact (backward `{jb} → zero`); an abstract `FactToFact` is FLOW. Each has its layer. |
| `NDFactToFact` | A TAINT edge whose premise key has two or more premises that are not the zero fact (§4.6). |
| `DeepAccessorExclusion` | Replaced by the mark exclusion `*∖X` of the edge (§4.7). The old exclusion is tied to an abstraction point at a depth, so it is lost when the field limit cuts the path; the mark exclusion is not tied to a position. |
| `FactReader` (mark as accessor suffix) | New reader over `(path, tail, mark)`: `check` (§4.9). |
| `FactTypeChecker` | The type filter primitive (§4.8). |
| `EdgeNonUniverseExclusionMergingStorage` (union merge) | Replace by merge rules 1 and 2. |
| `TaintSinkTracker` (rule assumptions), vulnerability records | The standing conjunction store (§8.9); the vulnerability store of §8.10. |
| `TreeInitialFactAbstraction` | Replace by §6.2 (run 1) and §6.3 (restricted runs). |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used: the field limit is the only depth bound (§4.4). |

---

## 8. Storages

Every store has a CONCEPT (a list of entries with a filter) and an INDEX. `Store.lean`, `RestrictedStore.lean` and
`PipelineStore.lean` prove that the index returns every entry that the filter returns (the first two also give the
cost of the lookup), for these stores: the subscription store (§8.4), the demand store (§8.6), the record store
(§8.7) and the mark requests of the request store (§8.8). The position requests, the conjunction store, the
vulnerability store and the source hit store have no index theorem. The OWNER of each store is the method that §5.2
names. Lifetimes:

* RUN: one run (one direction, one field limit).
* HAND-OFF: from the end of one run until the next run has read it. This is what one run passes to the next: the
  demand edges (§8.5), the DEMAND entries of the report (§8.10) and the source hits of a backward run (§8.11). The next
  run reads them as its demand or as its seeds (§9.2 defines the hand-off; §8.6 stores the demand).
* PERSISTENT: all runs of one analysis.

The method key of a method is the same in every run (§1), so a key that contains it stays valid across runs.

PATH TRIES. Several indexes are path tries keyed by `base :: path` (the base, then the accessors of the path). For the
key `k`, `lookupPrefixes(k)` returns the entries whose key is a prefix of `k` (the entries at or above `k`, also at
`k`), and `lookupExtensions(k)` returns the entries whose key has `k` as a prefix (the entries at or below `k`, also at
`k`). An OVERLAP query is `lookupPrefixes(k) ++ lookupExtensions(k)`, with the entries at `k` once. Each lookup gives
candidates; the store then applies the exact test that the section names (`overlap`, `applicable`, `inside`, §3.4).

### 8.1 Method edge store (RUN, per method)

* Key and value per conclusion kind (§7.2): REACH: `(statement, premise key, layer)`, one bit. FLOW: `(statement,
  premise, layer, base, exclusion, mark exclusion)`, a `FlowTree`. TAINT: `(statement, premise key, layer, base,
  exclusion)`, a `TaintTree` (the exclusion of its `[any-taint]` leaves, W8; Empty in the demand layer).
* `add(...)` merges by rule 1, 2 or 2' (T1; T2 and T2' for FLOW, T2 also for a normal TAINT tree) and returns the
  delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer: the store drops a conclusion if a stored conclusion of the same premise key, layer and
  conclusion kind subsumes it (`Subsume.subsumesB`): the same base; the same mark (TAINT), or the stored mark `*∖Xs`
  and the dropped mark `*∖Xn` with `Xs ⊆ Xn` (FLOW); `[any]` at `p` subsumes every fact at or below `p` with its
  mark (the demand layer); `[any-taint]/Es` at `p` subsumes, in its layer (the normal layer: W8), only the
  `[any-taint]` facts with its mark that it covers (§3.4 `covers`: `[any-taint]/En` at `p ++ r` with `r ≠ []` if `Es`
  admits `r`, or at `p` with `Es ⊆ En`), and NEVER a `$` fact at or below `p` (a later demoting cleaner `part` row
  must leave that `$` fact normal and exact: the example of §7.2 T5); `*/Es` subsumes `*/En` at the same path if
  `Es ⊆ En`. `subsumes_sound` proves that every pair of
  the dropped fact is a pair of the stored fact (the model kind `.any` is both any tails; with the exclusion of
  `[any-taint]` it is argued, §11.2). The premise key includes the tail and the exclusion, so a fact of a
  must-premise never subsumes a fact of the `[any]` premise at the same path, or the reverse (§7.1).
* A demand-layer conclusion never subsumes a normal one (`Subsume.recordSubsumesLB_layer` for records).
* The unchanged propagation (`Sequent.Unchanged`, §4.2 step 2) skips the store: its items do not go through `add`.
  The method analyzer keeps them in their own queue, with a set that discards the repetitions, and it takes them
  before every other item. When that queue is empty, it drops the set (`analyzer-core.md` §4.3).
* The store lives for its run. No store of a run stays for a trace resolution: the trace resolution is out of scope
  (§8.10).

### 8.2 Initial fact store (RUN, per method; callee)

* `initials: Set<InitialAp>`: the initial facts of the method in this run (the zero fact, the emissions and the
  answers).
* The store keeps no support. The support of a premise set (§4.9 condition 3) is a property of the whole run: the
  confirmation computes it after a complete run, at the barrier, over the links of the added fact stores (§8.3;
  `analyzer-core.md` §7.5). Support is a property of a premise SET, not of one initial fact: two premises that are each
  supported at a different call do not make their set supported (`NDConfirmed.CexSites`).

### 8.3 Added fact store (RUN, per method; callee)

* A path trie keyed by `base :: path`. Each added fact keeps the set of its caller edges
  `(caller method, caller premise key, layer of the caller edge, call statement)`. One (added fact, caller edge) pair
  is a LINK.
* Each link also keeps the LAYER OF THE ADDED FACT on that link. It can differ from the layer of the caller edge: a
  cleaner `part` row can move the added fact to the demand layer (§4.7). Condition 3.2 of the confirmation (§4.9) reads
  it: only a link with a normal added fact supports a premise. An added fact with an any tail is `[any-taint]` on a
  normal link and `[any]` on a demand link (W8); the emission reads it (§6.3). A normal `[any-taint]` added fact has
  its exclusion `E`, and the store keeps it with `E` (an `[any-taint]/E` and an `[any-taint]/E'` added fact at one
  path are two added facts); an `[any]` added fact has none (W8 (b)). Lean: the flag `am` and the exclusion `aex` of
  `AnyTaintEx.XObj.added` (round 1: `AnyTaint.TObj.added`).
* A new link is event E2 of §5.3, also when the added fact exists already. The store gives the request store (§8.8)
  every new link.
* The standing request match (§4.5, §4.10) reads the store with OVERLAP queries (§8): the key is `base :: path` of
  the request premise (mark request) or `S :: p` of the requested position (position request).

### 8.4 Subscription store (RUN; caller)

* Key: the callee. Value: the subscriptions `(caller edge, call statement, added fact a)`.
* On a published summary edge of an initial fact `j`: find the subscribed `a` that satisfy `j` (§4.3), and apply. The
  index is a path trie keyed by `base :: a.path`. In run 1 (`applicable`: `a` at or below `j`) the query is
  `lookupExtensions(j.path)`. In a restricted run (`satI`: `j` inside `a`) the query is `lookupPrefixes(j.path)`; for
  a FLOW premise (F72: also `applicable`) it is the union of both, `around(base :: j.path)` (§8.7 R2).
  Then the store applies the exact test of §4.3 (`PipelineStore.deliver_run1`, `deliver_restricted`; the F72 query
  of a FLOW premise has no index theorem yet, PENDING §11.2).
* On a new subscription: apply every published summary edge of every initial fact that `a` satisfies, and every record
  that applies to `a` (§8.7 R4).
* Only this store answers the "satisfies" query.

### 8.5 Run summary store (HAND-OFF, per method; callee)

* Key: `(premise key, layer)`. Value: the exit conclusions (§7.2: REACH, FLOW trees or a TAINT tree). A summary edge is an exit fact after the exit order of
  `interpreter.md` §4.7 (event E4 of §5.3). Only the normal exit makes a summary edge (`interpreter.md` §3.4).
* In a restricted run the callee restricts each new summary edge by every demand pattern of the method (§6.4). It
  PUBLISHES the results to the subscription store. Run 1 publishes every summary edge as it is.
* At the end of a complete run, the store adds the summary edges that §8.7 R1 admits to the persistent record store.
* THE HAND-OFF READS THE PUBLICATIONS, not the summary edges before the restriction (§9.2; Lean `Handoff.Pub`:
  `Handoff.pubD` for run 1, `Handoff.pubR` for a restricted run). For each summary leaf that is not crossable (§1),
  every publication of it is one DEMAND EDGE of the run: the input of the next run in the other direction (§8.6, §9.2).
  A crossable leaf gives no demand edge: §8.7 R1 persists it as a record, and the next run of each direction crosses
  it (§8.7 R3, R4, R5). The store keeps the DEMAND EDGES DURING THE RUN: at each summary delta it takes the part of the
  summary whose leaves are not crossable, restricts it as the publication (§6.4; run 1 keeps it as it is), and stores
  the pieces beside the
  summary edges before the restriction (`ap-impl.md` DD17: `RunSummaryStore.addDemand`, `demandEdges()`). The
  restriction acts leaf by leaf, so the stored pieces are the publications of the non-crossable leaves (argued; the
  hand-off reads only them, §9.2). The summary edges before the restriction serve only the records (R1).
* The premise key keeps its tail and its exclusion: a must-premise and the `[any]` premise at the same path have
  their own summaries (§7.1). A forward summary with the `[any-taint]` tail on its premise or its conclusion is a
  record if it is normal (§8.7 R1); the backward run has no `[any-taint]` (W8 (d)). Such a leaf is never crossable
  (§1), so it is always a demand edge. The hand-off to the backward run reads a forward `[any-taint]/E` conclusion as
  the pattern `[any]` (§9.2).

### 8.6 Demand store (RUN, read only; callee)

* Content: `MethodKey → List<DemandPattern>`: the demand patterns of each method, in the orientation of this run (the
  entry pattern `D-c` and the exit pattern `D-p` or none). The driver fills the store at the start of the run from the
  hand-off of the run before (§8.5). §9.2 defines the hand-off in both directions.
* Index: a path trie keyed by `base :: D-c.path`.
* The query `near(q)`: the prefix walk of `q`, then the subtree strictly below the node of `q`. It returns the same
  entries as the list filter "the chain is not apart from `q`" (`RStore.near_equiv`, `near_sound`).
* Emission query (§6.3), for the added fact `a`: `near(a.path)`. It returns every demand pattern for which the emission
  gives a fact (`RStore.emit_complete_M`, `emit_lookup_equiv_M`). For a `$` added fact the prefix walk alone is enough
  (`emitM_exact_prefix`).
* Restriction query (§6.4), for the summary premise `j`: `near(j.path)` (`restrict_complete_U`,
  `restrict_lookup_equiv_U`: every pattern whose `D-c` overlaps `j`, the premise test of the earlier restriction). The
  intersection needs `j` inside `D-c`, so only a `D-c` at or above `j.path` can pass: the prefix walk is enough, and
  the exact test (the locations and the marks of §6.4) drops the other entries (argued from the overlap form, §11.2).
  The index is keyed by the chain only: the mark tests act on the returned entries.
* Cost (`near_query_cost`): at most `|q| + 1` nodes for the walk, plus `Σ |rel|`, against `|demand patterns|` tests in
  the list form. `|rel|` is the length of the part of a returned chain strictly below `q`; the sum is over the returned
  chains. The bound "walk + number of results" is FALSE for the plain
  trie (`deep_chain_cost`); a path-compressed (radix) trie gives it.

### 8.7 Persistent record store (PERSISTENT)

One direction-neutral store for the forward and the backward analysis:

```kotlin
enum class Direction { FORWARD, BACKWARD }

/** A record: a normal summary edge with ONE premise (R1), in the orientation in which it was derived. */
class Record(
    val method: MethodKey,
    val direction: Direction,          // FORWARD: premise = entry fact; BACKWARD: premise = exit fact
    val premise: InitialAp,            // the one member of the premise set; the zero fact only for FORWARD (R1);
                                       // the tail ANY_TAINT (a must record, with its exclusion) only for FORWARD
                                       // (R1); never reversed (R3)
    val conclusion: Facts,             // normal layer (§7.2): REACH (forward {zero} → zero, backward {jb} → zero),
                                       // a FLOW tree (a `*` premise, may carry a mark exclusion) or a TAINT tree
)

interface RecordStore {
    fun add(record: Record)
    fun byEntry(method: MethodKey, addedFact: Pattern): Sequence<Record>      // the added fact of a link
    fun byExit(method: MethodKey, fact: Pattern): Sequence<Record>            // a fact at the exit side
}
```

`byEntry` returns the candidate records for a reader in the direction of the record. `byExit` returns the candidate
records for a reader in the other direction: a requirement of the backward run at the forward exit reads the forward
records, and a forward fact at the forward entry reads the backward records (R3).

Rules:

* R1. THE PRINCIPLE: a summary edge is persisted (and so read reversed, leaf by leaf, by R3) ONLY IF IT IS COMPLETE
  (§1). A demand-layer
  summary edge is never persisted and never reversed. The store adds only a complete summary edge whose premise set
  has ONE member:
  * of a forward run: every normal such edge, also a zero-premise edge (the premise set `{zero}`), also an edge with
    `[any-taint]/E` leaves (with their exclusion), also an edge of a must-premise (a MUST RECORD, with the exclusion
    of its premise: end-exact, S14; `AnyTaintExExact.recs_of_DRX_valid`);
  * of a backward run: only a normal edge whose premise is NOT the zero fact. The backward run has no `[any-taint]`
    (W8 (d)), and its `[any]` results are in the demand layer (W6, §9.1), so a backward record has no any tail. A
    zero-premise backward edge can come from a seed (§9.2): the seed relates the zero location to every location of
    its sink pattern (Lean: `Backward.seed_den`), which is not a flow of the reversed program, so it is never persisted
    and never reversed. The backward records are exact forward records (Lean: `AnyTaintSim.backRecT`,
    `backRecT_sub`, `backRec_exact`, under the hypotheses of `BExact.revRecs_exact`). A backward summary through the
    reversal of a conjunctive micro edge is in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION), so it is never
    added.

  An edge whose premise set has two or more members (§4.6) is never added.

  A CROSSABLE leaf of a record (§1) is never a demand edge of its run (§9.2): the later runs reuse it instead of an
  analysis (R5). Every other leaf of a summary edge, also a normal one, is a demand edge (§8.5).
* R2. `byEntry` is a path trie keyed by `base :: premise path`. For the added fact at `q`, the lookup is
  `lookupPrefixes(base :: q)` for `applicable` (`Store.forward_equiv_prefixes`, `applicable_mem_candidatesB`) and
  `lookupExtensions(base :: q)` for `inside`, then the exact test. The union `around(base :: q)` returns every record
  that one of the two tests accepts (`PipelineStore.record_lookup`). `byExit` is a path trie keyed by
  `base :: leaf path` for EACH leaf path of the conclusion tree. Its lookup is `around(base :: q)` for the fact at
  `q`: a leaf whose reversal covers the fact is at or above it, and a leaf whose reversal lies inside the fact is at or
  below it (`PipelineStore.record_lookup`, with the reversed premise as the key).
* R3. Only a record is reversed, so only a complete summary edge (R1). A reader in the other direction reverses the
  record LEAF BY LEAF by §9.1 (the `byExit` index of R2 keys each leaf path) and then applies it as R4 says (the
  reversed premise is looked up in `byExit`, then tested as in R4). Only a mark-reversible record has a reversal (§1);
  a record that is not mark-reversible is not read in the other direction. Two kinds of leaf have NO reversal:
  * every leaf of a MUST RECORD (an `[any-taint]` premise): it is end-exact, not exact pair by pair, and its reversal
    would claim a must requirement ("every location below the premise leads to the sink") that the program does not
    have (`AnyTaintExact.CexRev.cex_rev`: the must record of `ret = p.g` reverses into a pair `ret → p.f` that is not
    a converse flow);
  * an `[any-taint]/E` leaf with `E ≠ {}`: a backward premise has no exclusion of `[any-taint]` (W8 (d)), and the
    reversal without `E` would relate the excluded locations, which the forward edge does not reach.

  Every other leaf of the same record reverses as usual (the whole record is never dropped for one leaf). Example: of
  the zero-premise record with the two leaves `(ret, ., [any-taint], {name}, T)` and `(ret, .k, $, U)`, only the `$`
  leaf reverses. A leaf `$ → [any-taint]` with `E = {}` (a source result)
  reverses into `[any] → $`: the backward premise tail is `[any]` (W8 (d); §9.1). It applies only to an `[any]`
  requirement (§4.3: a `$` requirement below the premise neither satisfies it by `applicable` nor contains it), and
  such a requirement is in the demand layer (W6), so the result is in the demand layer too: a reuse limit, no loss of
  soundness. Every record whose premise has the Empty exclusion and that is mark-reversible reverses exactly
  (`Reverse.rev_exact_of_empty_premise`), so every leaf that R3 reverses reverses exactly (§9.1). A reversed backward
  record has no type filter (the backward run does not type-filter): an expected false-positive source (§11.1). On a
  program without type filters (`Exact.FiltUp`), a normal backward
  summary with a non-zero premise reverses into an exact forward record under S11 (c) and (g), when the records that
  its backward run reads are exact (`BExact.rev_record_exact`, `revRecs_exact`, `revRecs_exactM`; without S11 (c) it
  is false, `BExact.CexZeroBack.cex_rec`). An exact forward record reverses into an exact backward record under
  S11 (g) (`Reverse.backward_reuse_precise`). The two directions together are argued (§11.2). The model has no end
  facts: a record through an end fact, in either direction, is not exact (§11.1).
  THE REVERSAL OF A CROSSABLE LEAF (§1) is exact (`Reverse.rev_exact_of_empty_premise`: the converse pairs; as a
  record, S14), and its premise has the tail `$` or `*` with the Empty exclusion. So
  it applies to EVERY concrete requirement that has a common location with it, by `inside` or by `applicable`
  (`Handoff.cross_applies`): the backward run crosses the call by it (rule `retRec`; `HandoffBackward.cross_step`) and
  does not enter the callee for it (R5). Since F72 a requirement can have the mark `*` (§9.2): a reversal with a `*`
  premise applies to it too, and a reversal with a concrete premise does not (no request, §4.5). In the same way the
  next forward run crosses a call by the reversal of a crossable backward leaf (`HandoffBackward.NextRecs`). A backward leaf through the reversal of a conjunctive micro
  edge is never crossable: it is in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION), because its reversal
  drops the other literals of the conjunction. A reversed `[any]` premise (the reversal of an `[any]` or an
  `[any-taint]` leaf) does not cross: a `$` requirement neither satisfies it nor is covered by it
  (`HandoffCases.revRec_any_premise`, `not_cross_of_any`, `dollar_blocked`), so such a leaf must stay a demand edge.
  A looser hand-off that reads only the forward conditions (1) to (3) of §1 and drops such a leaf loses a real
  vulnerability: the backward run cannot cross the call, so it does not reach the source
  (`HandoffCases.AnyW.cegar_cross_anyw`, with the source seeds; `HandoffCases.AnyM.cegar_cross_anym`, with no source
  seeds).
* R4. A record applies to an added fact when its premise covers the fact (`applicable`, §4.3) or lies inside it
  (`inside`, §4.3), in every run after the run that made it, IN THE SAME DIRECTION (run 1 is the first run, so it
  reads no record). Lean: rule `retRec` (`sat ∨ applicable`). A MUST RECORD applies by `inside` with the result of the
  application, and by `applicable` only with a DEMAND result (the record demotion of §4.3; Lean: `AnyTaintEx.DRX`,
  rule `retRec` with `AnyTaintEx.recLayerX`; round 1 `AnyTaint.DRT` with `AnyTaint.recLayer`; necessary:
  `AnyTaintExact.CexApp.cex_app`). A record is exact (S14; a must record end-exact), so it adds no false pair (a must
  record, applied by `inside`: no false end location). For the records of a forward run this is proved run by run: a
  normal edge of run 1 or of a forward restricted run is exact when the records that the run reads are exact
  (`RExact.recs_of_D_valid`, `recs_of_DR_valid`; for programs without type filters `recs_of_D`, `recs_of_DR`; the union of two record sets,
  `recs_union`). If every record is an exit edge of an earlier forward run (`BExact.RecsFromRuns`), the forward
  records stay exact over the run sequence (`BExact.recsSeq_exact`, `recsSeq_exactV`, `accRecs_exact`,
  `accRecs_exactM`). So every normal edge and every confirmed vulnerability of every forward run is real with no
  EXACTNESS hypothesis on the records (`BExact.seq_edge_exact`, `seq_confirmed_real` for `Exact.FiltUp`; with S13,
  compose `BExact.recsSeq_exactV` with `RExact.edge_exactR_valid` and `RMain.confirmed_real_M_valid`). With the
  reversed backward records of R3, and with the source seeds, this is argued (§11.2). With the `[any-taint]` tail and
  its exclusion the same holds for the closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX` (with every restriction that has
  `AnyTaintExExact.RestrictOKX`, the intersection by `HandoffX.restrictIX_ok`): the exit edges of run 1 are
  exact records (`AnyTaintExExact.liftRecsX_exact`), those of a forward restricted run are exact or end-exact on the
  admitted locations, with a concrete conclusion mark and in the normal form of W8 (`recs_of_DRX_valid`,
  `recsConc_of_DRX`, `recsWF_of_DRX`), over the run sequence too when every record is an exit edge of an earlier
  forward run of the same program (`recsSeq_exactX_valid`, `RecsFromRunsX`), and then every confirmed vulnerability of
  every forward restricted run is real with no EXACTNESS hypothesis on the records (`seq_confirmed_realX_valid`; the
  hypothesis `RecsFromRunsX` stays).
  A backward normal edge with a non-zero premise is exact for the reversed program (`BExact.edge_exactB`,
  `edge_exactB_valid`, `edge_exactB_rev`; under S11 (c)). A zero-premise backward edge is never persisted (R1).
  A conjunction result whose premise set has one member can be a record. It is exact for the support semantics of
  §3.5 (`NDZeroThms.nd_edge_exact_z`, `nd_edge_exact_valid_z`), not in the sense of `RExact.RecsExact`. Its reuse
  (R4) and its reversal (R3) are argued with the restricted runs with ND edges (§11.2). The exactness holds for the
  reference semantics (§3.5), modulo the expected false-positive sources (§11.1). Lean: rule `retRec` (§11.2),
  `RCases.p3_reuse`, `RMain.p3_reuse_exact`.
  A CROSSABLE record (§1) applies to EVERY concrete added fact that has a common location with its premise
  (`Handoff.cross_applies`: by `inside` or by `applicable`), so every pair of the record from such a location reaches
  the caller (rule `retRec`; the recorded calls of `Handoff.FlowRR`, `Handoff.coverageRN`). Since F72 an added fact
  can have an abstract mark (a fact of a FLOW premise of the caller): a crossable record with a `*` premise applies
  to it too (its premise has the Empty exclusion, so it covers the added fact or lies inside it at every common
  location; argued, PENDING §11.2), and a record with a concrete premise does not (§4.5). A record of a FLOW premise
  of a restricted run (§6.5) is a `*`-premise record; its exactness is the lemma L5 of the pending model (§11.2).
* R5. Strict demand: after run 1 the abstraction reads only the demand (§6.3). It emits the demanded facts and
  checks nothing else; a record never causes an emission and never replaces one. The records only add edges (R4).
  But THE HAND-OFF LEAVES OUT THE CROSSABLE LEAVES (the leaves that R1 persists as records): a crossable leaf is not
  a demand edge (§9.2). So a callee whose summary leaves are all crossable gets no demand pattern from them, and so no
  emission from them (except the zero fact, §9.2; a seed in its call subtree still gives it the patterns of the seed
  paths, §9.2 case 2). The later runs cross it by its records (R4) and by their reversals (R3), and
  the later forward runs do not analyse it again while no seed lies in its call subtree (§6.6, THE EXCLUSION;
  `HandoffMain.exclusion_canon`). The crossable records are then not an optimization:
  the coverage needs them (`HandoffBackward.NextRecs`, `HandoffMain.iteration_generalN`).

### 8.8 Request store (RUN 1 only, per method; callee)

* Entries: `(method, initial fact, mark)` for a mark request (§4.5) and `(method, initial fact, position)` for a
  position request (§4.10), plus the answers already emitted. A request stands for the whole run.
* Index: per method, a path trie (§8). A mark request is keyed by `base :: path` of its premise `i`. A position
  request is keyed by `S :: p`, the requested position, because the match reads `(S, p)` and not the premise.
* On every new link (added fact, caller edge) of the method (§8.3), find ALL standing requests that overlap the added
  fact (`Store.standing_complete`, for the mark requests): for a mark request the premise `i`, for a position request
  the position `(S, p)`. Answer each one, or propagate it through THIS caller edge (§4.5; §4.10 items 2 and 3; §5.3
  event E2).
* On a new request, read every existing link of the added fact store whose added fact overlaps it (§5.3 events E5 and
  E7).

### 8.9 Conjunction store (RUN, per method)

* Entries: `(conjunctive micro edge or sink alternative, statement, literal index) → set of (fact, premise key,
  layer)`: the facts that overlap a literal of a conjunctive micro edge and pass its mark gate (§4.6), standing for the
  run. The literal index is the place of the literal in its conjunctive micro edge or sink alternative (§1). A
  conjunctive exit source keys its entries by its exit statement (§4.6; `interpreter.md` §4.7, D31).
* The same entries for a conjunctive sink: the sink edges that trigger a literal of a sink alternative (§4.9). An
  entry stays for the run, also when the global-state rule drops the evaluated part from the summary edge
  (`interpreter.md` §4.7, D30; only on a zero-premise item on `S`: a state that the method or its callees set): a
  later item can complete the combination with it. A caller-set `S` fact is stored as the input of its literal, and
  it is not dropped (§11.1).
* On a new fact for a literal: combine it with the stored facts of the other literals of the same conjunctive micro
  edge or sink alternative (one per literal, every combination). A result has the union of the premise sets WITHOUT
  THE ZERO FACT, and `{zero}` if every input has `{zero}` (§4.6). For a conjunctive sink, each combination is a sink
  edge set of the vulnerability: a sink witness (§4.9, §8.10).
* The same for a callee summary with several premises at a call statement: `(callee summary, premise index) → links`
  (the added fact with its caller edge; §4.6, event E6).

### 8.10 Vulnerability store and the report (PERSISTENT)

A reported vulnerability (Kotlin: `Report.Entry`, `analyzer-core.md` §10; the store keeps the `SinkWitness`es) has
these fields:

| Field | Content |
|---|---|
| key | `(rule, method, statement)` (Kotlin: `VulnerabilityKey`): the sink rule, the METHOD of the method key WITHOUT its context, and the sink statement. |
| sink witnesses | The sink witnesses (§1) of the key in the run of its state: the first complete forward run that confirmed it, or the latest complete forward run. The store keeps the witnesses of every run, each with its run. |
| state | CONFIRMED if a complete forward run confirmed one of its sink witnesses (§4.9); else DEMAND. |

A sink witness (Kotlin: `SinkWitness`) has these fields:

| Field | Content |
|---|---|
| alternative | The sink alternative of the rule at the statement that the witness triggered (§1). |
| method key | The method key of its sink edges, with the context. The confirmation reads the support of the premise sets in this method key (§4.9 condition 3). |
| pattern | DERIVED, not stored: the sink patterns of `alternative` of the rule at the statement in the method key (`SinkRule.patterns`; the same in every run, `interpreter.md` I5): the sink pattern `s` (§4.9); for an unconditional sink, the zero fact (§4.9); for a conjunctive sink, the literal patterns. |
| sink edges | One sink edge (its premise key, its layer and its sink fact), or, for a conjunctive sink, one sink edge set (one edge per literal, §4.9) with the set of the sink facts. |
| confirmed | Whether the witness is confirmed (§4.9). Only a complete forward run confirms a witness. |
| end facts | The end facts of the witness, if the sink rule has end-fact actions (§4.9; `interpreter.md` §4.1, END FACTS). |
| run | The run that reported the witness. |

* The key has no context. One sink statement that is reached in several contexts is ONE vulnerability. The same key in
  two runs is the same vulnerability. One entry of the report holds the sink witnesses of its key (the table above).
* Each sink witness keeps its own alternative and its own method key. Two sink witnesses with different alternatives
  or different method keys are different sink witnesses: they never merge.
* A CONFIRMED vulnerability persists. It is real for the reference semantics (§3.5), modulo the expected
  false-positive sources of §11.1.
* At every complete FORWARD run, every real vulnerability is reported by that run or was confirmed by an earlier
  complete forward run (§6.6). A DEMAND entry after complete forward run `n` (reported by run `n`, confirmed by no
  complete forward run so far) is seeded (§9.2). If complete forward run `n + 2` does not report it (no vulnerability
  with the same key), it is REFUTED: under B it is not real.
* THE REPORT of the analysis reads the COMPLETE forward runs only (§1, §6.6). It holds:
  * every vulnerability that a complete forward run confirmed, with the state CONFIRMED. This state is final;
  * every demand vulnerability of the LATEST complete forward run (§1), with the state DEMAND (a DEMAND entry).

  A key that is in both groups has the state CONFIRMED. An INCOMPLETE run (forward or backward) adds nothing to the
  report and refutes nothing: it is not the fixed point of its rules (S6), so no theorem applies to it, and it
  confirms nothing (§4.9). If run 1 is incomplete, no forward run is complete: the report has no entry and the output
  is empty, and the status of the analysis (`AnalysisEnd`, `analyzer-core.md` §7.1) gives the cause. This is a
  deviation from today: a full scan that times out outputs the vulnerabilities that it found before the timeout
  (`TaintAnalyzer.kt:157-223`; `ap-history.md` F68).
* THE TRACES. The trace resolution is out of scope (§0). No store of a run stays for it (§8.1). THE OUTPUT of the
  analysis holds EVERY entry of the report: the CONFIRMED vulnerabilities and the DEMAND vulnerabilities of the
  latest complete forward run (`ap-history.md` F68, which amends F67 (4)). Each one gets a SIMPLE trace: the trace
  with only the sink statement (Kotlin: `TracePathGenerationResult.Simple`). Its method key is the method key of a
  confirmed sink witness if the entry has one, else of its first sink witness. The analysis logs the number of the
  entries per state (CONFIRMED, DEMAND). So the output holds every real vulnerability that the report holds (§0.1,
  §6.6). A DEMAND entry can be false (§11.1). The end-fact check of today's trace step is out of scope too: a known
  gap (§11.1).
* The DEMAND entries of the report after a complete forward run are also its HAND-OFF: the next backward run reads
  their sink witnesses of that run as its sink seeds (§9.2). A CONFIRMED vulnerability is final, so it is not seeded,
  also when a later run reports it only in the demand layer. Only THE TRIGGER OF AN END FACT (§9.2) fires the sink
  seeds of an alternative of a CONFIRMED vulnerability: a requirement that reaches its reversed end-fact edge needs the
  witness of the trigger. A backward run reports no vulnerability (§9.2, the backward sink role).
* THE `[any-taint]` TAIL (F69). A vulnerability whose taint comes from an `[any]`-target source (for example the
  whole-object DTO source of a Spring entry point) can be CONFIRMED (§4.9; a field read after a setter of another
  field, confirmed in run 1: `AnyTaintExCases.S.run1_email_confirmed`; a getter in a callee, confirmed in forward run
  3: `AnyTaintExCases2.G.run3_confirmed`). Its entry is CONFIRMED, and the state is final. A field that a setter or a
  strong write overwrote is not reported at all: the exclusion removes it (`AnyTaintExCases.S.run1_name_not_reported`;
  the round-1 rule kept it a DEMAND entry in every forward run, through the setter record). Only a vulnerability that
  rests on a may `[any]` (a pass rule with an `AnyField` target) or on another demotion of §2.2 stays a DEMAND entry.
  The output still holds every DEMAND entry (F68). Before F69 every `[any]`-target source finding was a DEMAND entry
  (W6); after F69 it is one only when it rests on such an approximation (`ap-history.md` F68, F69).

### 8.11 Source hit store (HAND-OFF; backward run)

* Entries: `(method key, statement, source edge)`: the unconditional sources that the backward run reached (§9.2,
  SOURCE HITS). The backward analyzer of the method adds an entry when it applies the reversed source edge of the
  statement to a requirement and gets a result.
* The next forward run reads the entries as its source seeds (§6.1 rule 6): per (method key, statement), the set of
  the source edges that may fire.
* A source edge has an identity that is the same in both runs: its method key, its statement and its forward micro
  edge (Lean: `σ M n e`). The interpreter gives the same micro edges in every run (`interpreter.md` I5).

---

## 9. Reversal and the backward direction

### 9.1 Reversal of a record or a micro edge

The reversal `rev(i, f)` (Lean: `revEdge`, `revKinds`) reads an edge `i → f` from the other side. It reverses a record
for a reader in the other direction (§8.7 R3), and every micro edge of the reversed program (§9.2). The new premise is
the old conclusion; the exclusion goes to the NEW CONCLUSION, so the new premise has the Empty exclusion. A micro edge
can have every row of the table except the row `$ → */E`, which S8 forbids, and the rows with an `[any-taint]`
premise (S15: only a target has the `[any-taint]` tail); a row `*/E → $` or `*/E → [any]` has `E = {}` (S11 (g),
`interpreter.md` I3). A forward micro edge with an `[any]` premise is the `[any]` literal of a source (S15: a pass
rule with an `AnyField` premise is a rule error, `interpreter.md` D33). The last column says whether a record can
have the row. Only three rows occur for a record, because:

* an `[any]` premise starts in the demand layer (§6.5), so it has no record;
* an `[any]` conclusion is in the demand layer (W6), so it is no record;
* no leaf of a record with an `[any-taint]` premise (a must record) and no `[any-taint]/E` leaf with `E ≠ {}` is ever
  reversed; R3 is leaf by leaf, so the other leaves of the record reverse (§8.7 R3; `AnyTaintExact.CexRev.cex_rev`);
* a `*` premise has no `[any-taint]` conclusion (run 1: `AnyTaintExKinds.D6X_flow_no_any_taint` for the spec closure
  `AnyTaintEx.D6X`, under S7, S10 and S15; round 1 `AnyTaintSim.D6T_flow_no_any_taint`, also under `W6.SummaryStar`;
  a restricted run of the concrete design has no `*` premise, `AnyTaintExExact.DRX_conc`, round 1
  `AnyTaintSim.kinds_DRT`; a FLOW premise of an F72 run has none either: an `[any-taint]` target needs a concrete
  premise mark, §4.5; argued, PENDING §11.2);
* a `$` premise has a concrete mark (S8), so it has no `*` conclusion (W2, `Coverage.edge_conc`);
* a `*` premise never gives a normal `$` conclusion: every `$`-target micro edge has a concrete premise mark (S8),
  so on a `*`-mark fact the mark gate raises a request, and a case `above` result is in the demand layer.

| `i.tail` | `f.tail` | new premise tail | new conclusion tail | occurs for a record |
|---|---|---|---|---|
| `*` | `*/E` | `*` | `*/E` | yes |
| `$` | `$` | `$` | `$` | yes |
| `[any]` | `*/E` | `*` | `*/E` | no |
| `$` | `*/E` | `$` | `$` | no |
| `*` | `$` | `$` | `[any]` | no |
| `[any]` | `$` | `$` | `[any]` (the `[any]` literal of a source; in the demand layer, W6) | no |
| `$` | `[any]` | `[any]` | `$` | no (a pass rule with an `AnyField` target: every result in the demand layer, below) |
| `*` | `[any]` | `[any]` | `[any]` | no |
| `[any]` | `[any]` | `[any]` | `[any]` | no |
| `$` | `[any-taint]` (`E = {}`) | `[any]` | `$` | yes: a source result; the reversal applies only to an `[any]` requirement, so with a demand result (§8.7 R3) |
| `$` | `[any-taint]/E`, `E ≠ {}` | | | no: not reversed (§8.7 R3) |
| `[any]` | `[any-taint]` | `[any]` | `[any]` | no (a conditional source with an `[any]` literal) |
| `[any-taint]` | every tail | | | no: a must record is not reversed (§8.7 R3) |

THE BACKWARD RUN HAS NO `[any-taint]` (W8 (d)): in a reversal every new premise or conclusion with an any tail is
`[any]`. So the reversed `[any]` literal of a source (a `ContainsMarkOnAnyField` check) has the target `[any]`, and
the reversed edge of a source whose forward target is `[any-taint]` has the backward premise tail `[any]`
(`interpreter.md` §4.9). W6 puts every `[any]` result of the backward run in the demand layer (argued, §11.2).

THE REVERSAL OF A MAY. The reversal of a micro edge whose FORWARD target is `[any]` (a pass rule with an `AnyField`
target, a may) gives EVERY result in the demand layer, also a `$` result: the forward edge writes some field, not
every field, so a requirement through its reversal is not exact. The reversal of a micro edge whose forward target is
`[any-taint]` (a source, a must) follows the ordinary rows and keeps the layer of the requirement (for example the
source hit, §9.2). The forward target tail tells the two apart: no other rule-kind flag is needed (`interpreter.md`
I14, §4.9). This layer rule is argued with the backward W6 (§11.2). A reversed record never has an any-tail
conclusion.

THE REVERSAL OF A CONJUNCTION. The reversal of a conjunctive micro edge (two or more positive literals, §4.6; also a
conjunctive exit source) gives one micro edge per literal (§9.2), and it gives EVERY result in the demand layer, as
the reversal of a may: a requirement that reaches one literal is not a converse flow of the conjunction, because the
conjunction also needs the other literals. So no backward summary through it is a record (§8.7 R1) or crossable (§1,
Lean `Handoff.CrossB`), and case 3 of §9.2 hands it off to the next forward run, which analyses the callee with every
member of the premise set. This rule repairs a false positive that existed before F70: R3 reversed such a normal
backward summary into a forward record of one literal, and that record gives a normal result without the other
literals (`ap-history.md` F70). Example (`lib(a, b)`: a conjunctive source `ContainsMark(arg0, T1) ∧
ContainsMark(arg1, T2) → Result.$ (T)`):

```java
root():    a = srcT1();  b = srcT2();
           r1 = M(a, b);  y.f.g = r1;  sinkT(y.f.g);   // V1: real
           r2 = M(a, c);  sinkT(r2);                   // V2: not real (c carries no T2)
M(p1, p2): ret = lib(p1, p2);  return ret;
```

With the field limits 1, 2 and 3, forward run 1 reports V1 as a DEMAND entry (the cut of `y.f.g`) and does not report
V2. Backward run 2 reverses the conjunction in `M` into `(ret, ., $, T) → (p1, ., $, T1)` and
`(ret, ., $, T) → (p2, ., $, T2)`. With these edges in the normal layer (as before this rule), each backward summary
is a record and crossable, and forward run 3 applies the one-literal record `(p1, ., $, T1) → (ret, ., $, T)` at
the second call (with the hand-off of the demand edges `M` gets only the zero demand, so this record is the only
path through `M`): V2 CONFIRMED, a false positive. With every result in the demand layer, case 3 gives `M` the demand
patterns of both members, and forward run 3 analyses `M` with the conjunction: V2 is not reported. Argued, not
modelled (restricted runs with ND edges, §11.2).

The new premise mark is `i.mark` if `f.mark` is abstract (`*` or `*∖X`), else `f.mark`. The new conclusion mark is
`f.mark` (`*` or `*∖X`) if it is abstract, else `i.mark`.

* The reversal needs a MARK-REVERSIBLE edge: `f.mark` is abstract, or `i.mark` is concrete (Lean: `Reverse.MarkRev`).
  A mark-producing edge under a `*`-mark premise has no reversal (`no_rev_of_star_conc`). S11 (b) asks that every
  statement micro edge is mark-reversible; a call binding has the marks `*` to `*` (S10, S11 (a)), so it is
  mark-reversible too.
* The reversal of an edge is EXACT (the reversed pairs are exactly the converse pairs) if the edge is mark-reversible
  and has an EXACT SHAPE: every row of the table except `*/E → $` and `*/E → [any]` with a premise exclusion
  `E ≠ {}` (Lean: `Reverse.ExactShape`). With the Empty premise exclusion every row has an exact shape
  (`rev_exact_of_empty_premise`). A normal edge of a forward restricted run has a premise with the `$` tail (for `DR`:
  `RExact.complete_premise_exact`; for `AnyTaintEx.DRX` under C3, which `AnyTaintEx.emitX_copies` gives:
  `AnyTaintExKinds.DRX_normal_premise`, a `$` premise that is not a must-premise, or a must-premise, which has the
  `[any-taint]` tail and a concrete mark, `DRX_must_premise`) or
  a must-premise (not reversed, §8.7 R3), and a record of run 1 has a
  premise with the Empty exclusion (§2.2). (For the concrete design. Since F72 a normal edge of a restricted run can
  also have a FLOW premise, which can have the exclusion `E` of its `*/E` pattern. Its normal leaves have the `*` tail
  (§7.2: a FLOW tree has no `$` leaf, and its `[any]` leaves are demand), and a leaf `*/E → */E'` has an exact shape,
  so it reverses exactly too; argued, PENDING §11.2.) So every leaf of a mark-reversible forward record that R3
  reverses reverses exactly, also a leaf `$ → [any-taint]` with `E = {}` (its premise has the Empty exclusion;
  `Reverse.rev_exact_of_empty_premise`, with the model kind `.any`). A normal backward summary with a non-zero premise
  reverses into an exact forward record (`BExact.summary_rev_flow`, `rev_record_exact`; under `Exact.FiltUp`, S11 (c)
  and (g)).

### 9.2 The backward run

The backward run is a restricted run (§6.1) on the REVERSED PROGRAM, with the zero rules below (Lean:
`Backward.DB` on `Reverse.Program.rev`). It uses the same facts, operations, storages and primitives. Only the meaning
of a mark and the roles of the rules change (`interpreter.md` §4.9 gives the rule roles and the call order).

* A backward fact is a REQUIREMENT: "if a location of this set carries `T` here, a sink is reached".
* The backward premise is at the forward exit of the method; the backward summary edge ends at the forward entry. The
  reversed program swaps the entry and the exit of every method and reverses every CFG edge.
* THE REVERSED STATEMENT (Lean: `Reverse.Stmt.rev`). Each forward micro edge `i → f` becomes `rev(i, f)` (§9.1). The
  reversed statement touches the forward touched bases and the target base of every forward micro edge. A target base
  that the forward statement does not touch (a gen-only alias target, `interpreter.md` A3) gets the identity edge
  `b.* → b.*` (`interpreter.md` A5); without it the reversed flow is wrong (`Reverse.revNoId_breaks`). The transfer of
  §4.2 then applies (§4.2 gives its backward steps).
* A CONJUNCTIVE micro edge `L1 ∧ … ∧ Lk → z` (§4.6) reverses into the `k` micro edges `rev(Lj, z)`: a requirement at
  `z` reaches every literal (an OR). This over-approximates the demand. Every result of these edges is in the demand
  layer (§9.1, THE REVERSAL OF A CONJUNCTION), so no backward summary through them is a record or crossable, and case
  3 below hands it off. It is argued, not modelled (§11.2).
* THE ANY TAILS IN THE BACKWARD RUN. The backward run has no `[any-taint]` (W8 (d)); its any tail is `[any]`, as
  before F69. Every `[any]` result is in the demand layer (W6, argued for the backward run, §11.2): the seed of an
  `[any]` sink pattern (below), the reversed edge of an `[any]` literal of a source or of a conjunction
  (`Q.[any] (T') → P.$ (T)` reverses to `P.$ (T) → Q.[any] (T')`, §9.1), and every `[any]` result of the rules of §4.
  The reversal of a pass rule with an `AnyField` target gives EVERY result in the demand layer, also a `$` result
  (§9.1: the reversal of a may). A backward premise with an any tail is `[any]` and starts in the demand layer (§6.5;
  `AnyTaintSim.DB_any_premise_demand`). So a backward edge with an any tail is never persisted and never reversed
  (§8.7 R1). The emission is the rule of §6.3, with the requirement as the added fact and the forward summary
  conclusion as the entry pattern; the requirement is never `[any-taint]`. THE BACKWARD WEAKENING (F72, R2): under a
  `*` pattern (a forward summary conclusion with an abstract mark) the emitted requirement is the FLOW form of the
  pattern, a `*` requirement; under a concrete pattern it is the meet of §6.3, as before. Example: the getter
  `ret = p.name`, the requirement `(ret, ., $, T)` under `D-c = (ret, ., [any], *)` gives the requirement
  `(ret, ., *, {}, *)` (§6.3, THE GETTER). So the backward run has `*` requirements, `*` conclusions and FLOW trees,
  and the backward demand is COARSER: the FLOW form of the pattern in place of the requirement (here `ret.*` in place
  of `ret`). One `*` requirement serves every mark. A requirement for a concrete mark stays where a concrete pattern
  asks for it: the concrete patterns come from the run-1 answers (§4.5). The reason is in `ap-history.md` F69
  (amendment (a)): the emission reads no pattern layer (§6.3; `AnyTaint.EmitVec`, `AnyTaintEx.emitTX`), and the
  backward demand that a forward run hands off does not read the forward must flags (round 1:
  `AnyTaintSim.backward_reads_sameT`, `PipelineAnyTaintDriver.handoff_sameT`).
* A cleaner is its own reversal (Lean: `Reverse.revInstr`). `interpreter.md` §4.9 places it on the requirement at the
  callee start. A `RemoveAllMarks` kill on `S` (`interpreter.md` §1.4) is a statement, not a cleaner: the reversal of
  each keep edge `S.q.* →_{E} S.q.*` is the same keep edge, and the kill acts on the requirement at the place of the
  reversed cleaners.
* THE REVERSED CALL (Lean: `Reverse.Call.rev`). The touched bases are those of the forward call and the alias bases
  of its call results (`interpreter.md` §3.8 AC2). The backward binding into the callee is the reversal of the forward
  binding back (`r.* → ret.*`, `ai.* → argi.*`, `S.* → S.*`) and of each call alias edge (`b.q.* → P.*`). An alias base
  also gets the identity edge `b.* → b.*` from after the call to before it, in caller coordinates (it passes over the
  callee), as a gen-only target of a statement does. The backward binding back is the
  reversal of the forward binding into the callee (`argi.* → ai.*`, `S.* → S.*`, `zero.* → zero.*`). A REACH
  conclusion `{jb} → zero` of the callee (a requirement that reached an unconditional source or an end-fact action,
  §7.2) returns to the caller through the reversed zero binding. The alias part is argued, not modelled (§11.2).
  `interpreter.md` §4.9 gives the order of the reversed call.
* NO TYPE FILTER. The backward run applies no type filter (§11.2 gives the difference to the model).
* THE ZERO FACT. The backward run starts at each ROOT with the zero fact as an initial fact, at the forward exit of the
  root. The zero fact passes over every call (Lean: rule `zpass`). It also ENTERS every callee directly: it is an
  initial fact of the callee at the forward exit of the callee, with no emission and no demand pattern (Lean: rule
  `zin`). This entry is not the reversal of a forward binding: with the plain reversal the zero fact only goes up, and
  a requirement inside a callee never reaches the callers (`Backward.lost_plain`, `Backward.B_fails_plain`). S11 (d)
  and (e) keep the zero fact alive on every path to a seed. With S11 (c), a requirement that enters a callee through a
  backward binding is never the zero fact, so its backward summary goes to the hand-off as case 3 below, or, if it is
  crossable, to the records (§8.7 R1, R3).
* SINK SEEDS (Lean: rule `seed`). The seeds are the DEMAND entries of the report after the previous forward run: the
  vulnerabilities that the previous forward run reported and that no complete forward run confirmed so far (§8.10). A
  CONFIRMED vulnerability is final, so it is not seeded (`ap-history.md` F70). For each sink witness of such a
  vulnerability in the previous forward run, the
  sink rule fires at the method key and the statement of the witness, with the patterns of every alternative of the
  rule there (`analyzer-core.md` §4.7; `interpreter.md` §7.2 item 14), where the zero fact reaches the sink statement,
  as a zero-to-fact edge `Zero → (sink statement, requirement)`. The requirement
  is the sink pattern, cut by the field limit of the backward run (§4.4). The seed of an `[any]` sink pattern
  (`ContainsMarkOnAnyField`) is the requirement `[any]`, in the demand layer (W6; the model `Backward.DB` keeps it as
  a normal `.any` edge, `AnyTaintSim.seed_any_normal`, so the backward W6 is argued, §11.2). A conjunctive sink seeds
  one requirement per literal pattern. An unconditional sink seeds nothing: its pattern is the zero fact (§4.9), and
  the zero rules keep the zero fact already. `interpreter.md` §4.9 places the seed of a sink call after the reversed cleaners of that
  call. One more rule fires sink seeds: THE TRIGGER OF AN END FACT (below).
* THE TRIGGER OF AN END FACT. An end fact exists only after its sink triggers (§4.9), so its reversal must demand the
  trigger. When the reversed end-fact edge of a sink alternative `A` at the statement `s` of the method key `M` applies
  to a requirement, it gives the zero fact (as a reversed unconditional source, THE ZERO DEMAND below), AND the
  backward run fires the sink seeds of `A` at `(M, s)`: the requirements of SINK SEEDS above for the patterns of `A`,
  where the zero fact reaches `s`, once per `(M, s, A)`. So the witness of the trigger is demanded in the next forward
  run, also when the vulnerability of `A` is CONFIRMED (THE SEEDS of §6.6 still seed only the DEMAND entries). Without
  this rule a real DEMAND vulnerability that rests on the end fact of a CONFIRMED sink is lost. Example (`sinkCall`: a
  sink rule `ContainsMark(arg0, T)` with the end-fact action `AssignMark(U, Result)`; `wrap`: an unresolved callee with
  the pass rule `CopyAllMarks(arg0 → Result.[AnyField])`, a may; `sinkAny`: a sink rule
  `ContainsMarkOnAnyField(arg0, U)`):

  ```java
  root():  x = source();  r = M(x);  sinkAny(r);        // V2: real (r holds y, and y carries U)
  M(p):    y = sinkCall(p);  w = wrap(y);  return w;    // V1 at sinkCall; its end fact (y, ., $, U)
  ```

  Forward run 1 confirms V1 and reports V2 as a DEMAND entry (the may of `wrap`). Backward run 2 seeds only V2; the
  requirement `(y, ., [any], U)` reaches the reversed end-fact edge of `sinkCall` in `M`. Without the trigger it only
  gives the zero fact, `source()` is not hit, forward run 3 does not trigger `sinkCall` (`source()` is no source
  seed, so `p` has no fact), so it makes no end fact and does not report V2: V2 is refuted, and the analysis stops
  with `STOP_RULE`.
  With the trigger, the sink seeds of `sinkCall` fire in `M`, the requirement `(p, ., $, T)` reaches `source()` in
  `root`, and forward run 3 triggers `sinkCall`, makes the end fact and reports V2. Argued (the model has no end
  facts, §11.2).
* THE BALANCED RETURN (Lean: rule `zret`). A requirement goes back to the forward entry of its method. A zero-premise
  backward edge there is a zero-premise backward summary of the callee. Every caller applies it to its own zero fact at
  the call site where that zero fact entered the callee, through the backward binding back, then the field limit. The
  callee does not restrict this summary (§6.4 does not apply), and the caller makes no satisfaction test. So every
  return of a seed is BALANCED.
* RECORDS. A forward record applies in the backward run through its reversal, leaf by leaf (§8.7 R3: no reversal of
  a leaf of a must record or of an `[any-taint]/E` leaf with `E ≠ {}`; the other leaves of the record reverse). The
  reversal of a CROSSABLE leaf (§1) takes the place of the demand edge of that leaf: the backward run crosses the call
  by it and does not enter the callee for it (§8.7 R3, R5). A
  backward summary edge with a premise that is not the zero fact can become a record if it is normal (§8.7 R1). A zero-premise backward edge never becomes a record: a seed
  is not a converse flow of the program.
* THE BACKWARD SINK ROLE. The backward run has no sink check (Lean: `Backward.DB` is used with no sinks; its only sink
  rule is `seed`). A forward source is not a backward sink: its reversed micro edge carries a requirement to the zero
  fact (THE ZERO DEMAND below). So a backward run reports no vulnerability. Its hand-off is the demand and the source
  hits below.
* SOURCE HITS (Lean: `FSeeds.srcHit`). A requirement that reaches a source continues to the zero fact through the
  reversed source edge. The backward run records these sources as HITS. The hit of the source edge `e` at the forward
  statement `s` of the method `M`: a backward edge after `s` (in the forward order) has a concrete fact that covers a
  location that `e` gives. Then the reversed edge of `e` applies to that requirement (`FSeeds.srcHit_applies`). A
  `*` requirement (F72) gives no hit: the reversed source edge has a concrete premise mark, and on a `*` fact the mark
  gate gives nothing (§4.5). The concrete requirement of a concrete pattern, or the concrete requirement of a caller
  after a `*`-premise backward summary (the summary passes the concrete mark of the caller), gives the hit. The
  hits are the SOURCE SEEDS of the next forward run (§6.1 rule 6). Every source step of a justified witness of a
  seeded vulnerability is hit: with the hand-off of the demand edges every source step outside the recorded calls
  (`HandoffSrc.seg_genN_src`, `reach_of_db_genN_src`, `demanded_genN_src`, `B_srcN`; a recorded call reads no seed);
  with the earlier hand-off every source step (`FSeeds.seg_src`, `demanded_src`, `B_src`). A source inside a callee
  that the backward run crosses by a record is not hit and does not fire; the record of the callee gives its result
  (THE ZERO DEMAND below). An implementation may record more: more seeds keep the coverage, and every seed is a real
  edge of the program.
* THE ZERO DEMAND. The forward demand of every method contains `(zero, none)` (the hand-off below), so the next forward
  run emits the zero fact in every method that it reaches. The zero fact carries the support (§4.9) and the
  unconditional sinks. It is also the place of the seeds: a source seed fires where the zero fact reaches its
  statement, as a sink seed does in the backward run. So the work of the zero fact from the roots repeats in every
  run: in the backward run the zero fact enters every callee (rule `zin`), and in the forward run every callee that
  the zero fact reaches emits it. The localization of the zero fact is a later task (`ap-history.md` F70; §11.2). But
  after run 1 only the seeded sources fire, and the backward run seeds only the DEMAND entries of the forward run before
  (and the triggers of the end facts, above). All other work follows the demand edges: a method key of which the
  forward run hands off no demand edge (for example: all its summary leaves are crossable), with no seed in its call
  subtree, is analysed only from the zero fact in the next forward run (§6.6, THE EXCLUSION). A persisted zero-premise
  forward record still applies (§8.7 R4): it is exact (S14; not a record through an end fact, §11.1), so it adds no
  false pair, also when its source is not a seed. So the source seeds do not filter the records: a record of run 1
  fires the effect of a source that the seeds drop (`HandoffSrc.SrcRec.found_unseeded`; a precision point only, it
  adds real facts and removes none).
* Every backward run is a restricted run with its own field limit (§6.1). Its seeds have concrete marks. Since F72
  it is NOT concrete (THE BACKWARD WEAKENING, above), and it has no request rule (§4.5). (Before F72 it was concrete
  and raised no request: `BExact.DB_concrete`, `DB_no_request`, theorems of the concrete design.)
* THE DEMAND OF THE BACKWARD RUN (hand-off, forward run `n` to backward run `n + 1`; Lean: `Handoff.handF`). The
  hand-off reads the PUBLICATIONS of forward run `n` (§8.5; the run stores the pieces of its demand edges during the
  run): run 1 publishes every summary edge as it is (Lean `Handoff.pubD`), and a restricted run publishes the results
  of the restriction of §6.4 (`Handoff.pubR`). For every
  summary leaf `j → g` of forward run `n` that is NOT crossable (§1), every publication `j → g'` of it gives the
  backward demand pattern `(D-c = g', D-p = j)`: a DEMAND EDGE of forward run `n`. A crossable leaf gives no demand
  pattern: the backward run crosses it by its reversal (§8.7 R3). Every leaf of a summary with several premises
  `{j1, …, jk} → g` (§4.6) is a demand edge (it is never a record, R1): one pattern `(D-c = g', D-p = jm)` per member
  `jm` (argued, §11.2). This swaps the two patterns of the summary; it is not the reversal of §9.1. A forward summary
  can have the conclusion mark `*∖X` (a cleaner in the callee). THE HAND-OFF NORMALIZATION (F72, rule R1; the same in
  the hand-off to the next forward run, below): in both hand-offs every pattern mark `*∖X` becomes `*`, in `D-c` and
  in `D-p` (Lean, PENDING: `markNorm`, `normDem`, the hand-offs `handFA`, `demOfNA`). A larger demand is sound. The
  summary itself keeps `*∖X`: it stops a mark that the callee cleans (§4.1 step 5), so it blocks a mark propagation
  that cannot happen; for the demand the exclusion means nothing. If a run really demands a mark `T ∈ X`, it has its
  own demand edge with the concrete mark `T` (a summary of a run-1 answer of `T`, §4.5). (F71 kept `*∖X` in the
  pattern, and the backward run read it exactly: a requirement with a mark in `X` got no premise from it, the
  emission, §6.3, and a backward premise with a mark in `X` was not inside it, the restriction, §6.4. Before F71
  `*∖X` counted as `*`. Since F72 these cells do not occur.) The hand-off keeps the other marks of the pattern and
  reads its locations as a location set. It
  DROPS the exclusion of an `[any-taint]/E` conclusion or must-premise and gives the pattern the tail `[any]`: the
  backward demand is then larger, which is sound (W8 (d); Lean: the backward run reads a forward run through
  `AnyTaintExCov.forget6` and `forgetX`, which drop the exclusions and the must flags). The hand-off of a refined run
  can be SMALLER than the hand-off
  of the round-1 rules on the same demand: the exclusion removes summaries, for example of a read through an
  overwritten field (`AnyTaintExCov.CexRoute.route_a_false`); the iteration theorem reads each refined run as it is
  (§6.6). An `[any-taint]` leaf and a leaf of a must-premise are never crossable (§1), so the exclusion that the
  hand-off drops is always on a demand edge. The sink seeds are the DEMAND entries after forward run `n` (SINK SEEDS,
  above; §8.10), and the triggers of the end facts (above). (The EARLIER hand-off read the summary edges of forward run `n` BEFORE the restriction, the exit edges
  of each initial fact in every layer, crossable or not: Lean `Backward.revSummaryDemand`, through
  `Restricted.summaryDemand`. A complete callee was then entered again in every run, program WRAP of §6.6. It stays in
  the model as the record of the earlier design; `ap-history.md` F70.)
* THE SOURCE SEEDS OF THE NEXT FORWARD RUN (hand-off, backward run `n + 1` to forward run `n + 2`): the source hits
  of backward run `n + 1` (above; the store of §8.11).
* THE DEMAND OF THE NEXT FORWARD RUN (hand-off, backward run `n + 1` to forward run `n + 2`; Lean: `Handoff.demOfN`).
  This is the only definition of the forward demand. For every method `M`:
  1. the zero demand `(D-c = zero, D-p = none)`;
  2. for every zero-premise backward edge at the forward entry of `M`, with the conclusion `gb`: `(D-c = gb, none)`
     (never a record: the seed paths, §8.7 R1);
  3. for every backward summary leaf `jb → gb` of `M` whose premise `jb` is NOT the zero fact and that is NOT
     crossable (§1: crossable means normal, with a crossable reversal; Lean `¬ Handoff.CrossB jb gb`), every
     publication `jb → gb'` of it (the result of the restriction of §6.4 by a backward demand pattern):
     `(D-c = gb', D-p = jb)`, a DEMAND EDGE of backward run `n + 1`. So every demand-layer backward leaf is a demand
     edge, also a leaf through the reversal of a conjunction or of a may (§9.1). A crossable leaf gives no demand
     pattern: forward run `n + 2` crosses it by its reversal (§8.7 R3; the records of `HandoffBackward.NextRecs`).
     THE HAND-OFF NORMALIZATION (F72, R1) acts here too: since F72 a backward conclusion can have the mark `*∖X` (a
     cleaner on a `*` requirement, §4.7), and a mark `*∖X` of `gb'` or `jb` becomes `*`. A `*` requirement `jb` gives
     a `*` pattern: forward run `n + 2` emits its FLOW form (§6.3).

  (The EARLIER hand-off, Lean `Backward.demOf`, gave case 3 for every backward summary in every layer, before the
  restriction. It stays in the model as the record of the earlier design.)
* NO `[any-taint]` PATTERN. No demand pattern has the `[any-taint]` tail: a forward `D-c` or `D-p` comes from the
  backward run, which has no `[any-taint]`, and a backward `D-c` or `D-p` from a forward summary has the tail `[any]`
  (above). The reason is in `ap-history.md` F69 (amendment (a); §10.11).

The backward run satisfies contract B (§6.6) under S11 (`HandoffBackward.B_generalN`; for the canonical demand and
records `B_generalN_canon`; THE CONCRETE DESIGN: for the F72 rules this is CONTRACT B WITH MODES of §6.6, PENDING,
§11.2): for every forward run, if the demand of the backward run contains the demand edges of the
forward run (`Handoff.handF`), its records contain the reversals of the crossable records and leaves of the forward
run, its sink seeds contain the DEMAND entries that the forward run reported, and the next forward run gets at least
the demand `Handoff.demOfN` and the records of `HandoffBackward.NextRecs` (the records that the forward run read, its
crossable leaves, and the reversals of the crossable backward leaves). `HandoffMain.iteration_generalN` joins the runs
(§6.6). With the source seeds (the statement sources) this hand-off satisfies contract B too
(`HandoffSrc.B_srcN`; the iteration `HandoffSrc.iteration_srcN`, `iteration_srcN_canon`); for the earlier hand-off
`FSeeds.B_src`, `FSeeds.iteration_src` (without the source seeds `Backward.B_general`, `Backward.iteration_general`).
For the worked programs 1 and 2 (§6.3, §6.4) the hand-off of the backward run is exactly three parts: the demand
patterns of the callees that §6.3 and §6.4 give (`RCases.dem1M`, `dem2M`), the zero demand of every method
(`Backward.zeroDem`), and the pattern `(D-c, none)` of the root where the requirement reaches the source
(`Backward.dem1_exact`, `dem2_exact`). Forward run 3 reports the vulnerability (`Backward.p1_found`, `p2_found`; on
the full program, with no source seeds). These Lean results use the earlier hand-off and the earlier restriction. With
the intersection and the hand-off of the demand edges the model proves that the hand-off CONTAINS the callee patterns
and that forward run 3 reports the vulnerability: program 1 `HandoffRCases.p1_no_exit`, `p1_found_I`, `p1_handoff`,
`p1_chain`; program 2 `HandoffRCases.r1_c_not_cross`, `b2_handF`, `b2_inside`, `b2_restrictI_eq_U`, `b2_not_crossB`,
`p2_handoff`, `f3_inside`, `f3_restrictI_eq_U`, `p2_found_I`, `p2_chain` (the mark tests of the restriction pass:
`b2_insideB`, `b2_concMark`, `f3_insideB`, `f3_concMark`). That this hand-off is EXACTLY the three
parts is checked by hand (§11.2). In program 1 backward run 2 has only the zero fact as an initial fact, so no
restriction acts and `Backward.dem1_exact` holds for every backward demand and every backward record set (the
patterns of `c` and `m` are case 2, `HandoffRCases.p1_handoff`). In program 2 the run-1 summary of `c` that backward run 2 uses
(`Backward.revDem_c`) is in the demand layer, so it is a demand edge (`HandoffRCases.r1_c_not_cross`, `b2_handF`); the
crossable run-1 summaries (the identity of `c`, the zero edge of the root) are not demand edges any more, and no
requirement used them; the backward summary of `c` has an `[any]` premise, so it is in the demand layer and not
crossable, and it stays a demand edge (`HandoffRCases.b2_not_crossB`; case 3). The WRAP program of §6.6 is the example
where the two hand-offs differ.

`Reverse.flow_rev_iff_calls` proves that the flow of the reversed program is the converse flow, with calls, cleaners and
filters, if every micro edge and every call binding has an exact shape and is mark-reversible (`RevStmts`, `RevCalls`).

---

## 10. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

THE THEOREMS AND DECISION F72. Every theorem below about a restricted run or the iteration (§10.7, the restricted
part of §10.8 and §10.10, the restricted forward run of §10.11, §10.12) is about the CONCRETE restricted runs of F70
and F71: the emission `emitM` (`AnyTaintEx.emitX`), which copies the mark of the added fact, the satisfaction `satI`
(`satX`), and the closures `DR`, `AnyTaintEx.DRX`, `Backward.DB`, whose request rules never fire. The theorems hold
for that design, and their names stay. FOR THE RULES OF F72 THEY ARE NOT YET PROVED (§11.2, PENDING: THE LEAN MODEL OF
F72). The theorems whose CLAIM IS FALSE for the F72 runs (they describe the concrete design) are listed in that item.
The theorems of run 1 (§10.1 to §10.6, run 1 in §10.8 to §10.11) do not change.

### 10.1 Soundness of run 1 — `Coverage.lean`

Hypotheses: the program is well-formed (S10 and S5; Lean: `Program.WF`) and the abstraction satisfies C1 (§6.1).

| Theorem | Statement |
|---|---|
| `coverage` | If the value at the entry location `l0` of method `M` flows to `l` at node `n` (`Flow`: statements, calls, call-to-return, cleaners, type filters, nested callee flows), and the initial fact `i` of `M` covers `l0`, then the analysis has an edge `(i → f)` at `n` with `den(i, f)(l0, l)`, OR the request `(M, i, l0.mark)`. |
| `coverage_conc` | If `i` has a concrete mark, the first case holds. |
| `reach_strong`, `vuln_found` | If the zero location of a root flows through any chain of calls to a location that a sink pattern covers (`Reach`), the analysis reports the vulnerability at that sink. |
| `coverage_policy`, `vuln_found_policy` | The same for the run-1 policy (`policy1` is `policy` with the empty demand), for every field limit. |
| `edge_conc`, `req_initial_star` | A concrete-mark initial fact has only concrete-mark conclusions; a request is always on a premise whose mark is not concrete. |

That is the property "if the fact exists and the data flow exists (intra and inter procedural), the fact reaches the
destination". The cleaner case uses `Core.cleanRes_sound` (a covering result, or the request for the entry mark); the
filter case uses `Core.filt_keeps`.

### 10.2 Local lemmas — `Core.lean`, `SharedExcl.lean`

| Lemma | Statement |
|---|---|
| `applyEdge_sound` | THE CORE LEMMA: delta-concat covers the composition of the fact relation and the edge relation, or raises the request for the premise mark — in both cases, strong enough and not strong enough, for every fact mark `*`, `T`, `*∖X`. |
| `transfer_sound`, `applySummary_sound` | The statement transfer covers the statement step; summary application covers the composition with the callee flow. |
| `markComp_sound`, `markComp_none_no_pair` | The result mark composes the mark relations; a `*∖X` target that stops a concrete mark in `X` loses no pair. |
| `cleanRes_sound`, `cleanPos_inside_sound`, `cleanPos_disjoint_sound` | THE CLEANER LEMMA: a real location that the cleaner keeps is covered by a result, or the request for its entry mark is raised; the position test is sound. |
| `filt_keeps` | A prefix-closed type filter never drops a fact that covers a real (accepted) location. |
| `climbsB_of_den` | A request for the mark of the location climbs through an abstract added fact. |
| `limitF_sound`, `CoreAux.norm_sound` | The field limit and the normal form only enlarge. |
| `startFact_sound`, `coversB_sound`, `applicable_sound`, `applicable_mark`, `overlapB_of_common` | The start fact; the syntactic cover test; the mark of an applicable premise; overlap. |
| `check_sound`, `check_request_star` | A covered tainted location triggers the sink or raises the request. |
| `answerInit_covers`, `answerInit_applicable`, `policy_applicable` | The answer covers the requested location and is applicable; the run-1 policy satisfies C1. |
| `SharedExcl.applyEdge_shared_excl`, `den_shared_excl` | ONE exclusion per edge. |

### 10.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `W6.lean`

| Theorem | Statement |
|---|---|
| `Exact.edge_exact_valid`, `closed_exact_valid` | Under S7 (`MarkWF`) and S13 (a validity predicate that every filter accepts, `FiltValid`, and that goes back along every statement micro edge and both call bindings, `BackOK`): every pair of a normal-layer edge whose end location is valid is a concrete flow. |
| `Exact.edge_exact`, `complete_exact`, `closed_exact` | The same for filters that keep every extension of an accepted path (`FiltUp`; with prefix-closure this makes a filter constant, so this form is for programs without type filters). |
| `Exact.CexFilt`, `CexMark` | The two hypotheses are necessary in the model (the two programs break W6 and S8): a filter lets a fact pass whose lower locations do not exist; a `*`-premise edge with a concrete target forgets a cleaned mark. |
| `Exact.cleanRes_exact` | A normal-layer result of the cleaner denotes only pairs of the input whose end location the cleaner keeps. |
| `Closed.closed_records_exact`, `closed_records_exact_valid` | A property of records: no request on the initial fact and only normal exit edges ⇒ the records are exactly the concrete flow from its location set. |
| `Invariant.final_star_legal`, `final_star_abstract` | W2: a `*` conclusion has the mark `*` or `*∖X` and is in the normal layer. |
| `Invariant.no_univ_star` (+ `no_univ_needs_*`) | S8 ⇒ no `*/Universe` edge fact; each hypothesis is necessary. |
| `Invariant.demand_of_any_ok` | W6 is a layer refinement. |
| `W6.D_le_D6`, `D6_le_D`, `D6_w6`, `D6_normal` | (The rule of `W6.lean` puts EVERY `[any]` result in the demand layer. The spec rule of the forward runs is now W6T, W6 with W8, which demotes only a may `[any]` result (§2.3, §10.11); every normal edge of `W6.D6` is a normal edge of the round-1 closure `AnyTaint.D6T`, `AnyTaintSim.D6_normal_D6T`. The backward run keeps W6 for every `[any]` result (§9.2). `W6.lean` stays as the record of the old rule.) W6 FOR THE WHOLE RUN 1 (`D`): under `W6.SummaryStar` the run with W6 has the same facts, with the same or a raised layer; W6 holds in it; its normal edges are normal edges of the plain run. `SummaryStar` holds for the run-1 policy with no other hypothesis (`W6.summaryStar_policy`), and for every abstraction under the hypotheses of `Invariant.no_univ_star` (`W6.summaryStar_of_noUniv`). |
| `W6.DR_le_DR6`, `DR6_le_DR`, `DR6_w6`, `DR6_normal` | The same for a forward restricted run (`DR`), under `W6.RestrictLE` (the restriction copies the layer; for the earlier restriction `restrictU`: `W6.restrictU_LE`) and `W6.ExactInitConc` (every `$` initial fact has a concrete mark; the mark-copying emission gives it: `W6.DR_eic`). No S8 hypothesis. W6 is proved for `D` and `DR` only, not for `Statics.DS`, `ND.DN` or `Backward.DB`. |
| `W6.vuln_found6`, `edge_exact6`, `edge_exact_valid6`, `edge_exactR6`, `edge_exactR_valid6`, `confirmed_real6`, `confirmed_real_valid6`, `confirmed_real_M6`, `confirmed_real_M6_valid`, `iteration_sound_M6`, `iteration_general6` | With W6 in every forward run: soundness, exactness and confirmation (also the valid forms, under S13; in a restricted run under S14) and the iteration (`iteration_general6` has no S8 hypothesis). |
| `W6.Cex.cex_w6_changes_fact` | Without `SummaryStar`, W6 changes a fact, not only its layer. The program uses an abstraction outside the spec: it emits a `$` initial fact with an abstract mark, so `Invariant.PremConc` and `W6.ExactInitConc` are false for it. |
| `Invariant.star_final_keeps_initial_excl`, `star_initial_complete`, the demand-monotone lemmas | A final `*/Ec` under an initial `*/Ei` keeps `Ei ⊆ Ec`; under `*/Ei` a normal-layer final fact has the `*` tail or `Ei = {}`; the demand layer never goes back. |
| `Confirmed.confirmed_real_valid`, `confirmed_real` | A CONFIRMED vulnerability (§4.9) is a real concrete vulnerability for the reference semantics (§3.5) (valid form; `MarkWF ∧ FiltUp` form; §11.1 lists the expected false-positive sources). `CexConfFilt`, `CexConfMark`: both hypotheses are necessary in the model (the programs break W6 or S8). |
| `Confirmed.Weak.weak_support_gap`, `Confirmed.Rev2.rev2_not_confirmed` | The weaker support condition admits a false positive; the counter-example program `Confirmed.Rev2` is not confirmed. |

### 10.4 Concept against optimization — `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean`

| Theorem | Statement |
|---|---|
| `Tree.insert_mem`, `fromList_mem` | The Lean `EdgeTree` (a FLOW tree of §7.2: one premise, layer, exclusion and mark exclusion; `*` leaves are flags) holds exactly its path edges. |
| `Tree.rule1_mem`, `rule1_den`, `rule2_den`, `rule2_mark` | Merge rule 1 is exact; merge rule 2 (exclusions, and mark exclusions) is exact for EQUAL trees; counter-examples for different trees and for a union. |
| `Tree.applyTreeE_mem`, `applyTreeE_den`, `applyTreeE_grouped_key`, `applyTreeE_mx`, `applyTreeE_inv`, `applyTreeE_star_normal` | For a `*`-to-`*` micro edge with the mark `*` on both sides (not the mark gate or the cut of §7.3): the tree form of delta-concat equals the per-path form, fact and layer; output trees have distinct keys and keep the mark exclusion. |
| `Tree.fromList_size`, `fan_list`, `fan_tree`, `prepend_shares`, `walkSteps_le`, `applyListC_spec` | Cost of the tree representation. |
| `Store.*` | The record index (`byEntry`, `byExit`) and the mark-request index return every entry that the concept filter returns; lookup cost. The demand store of `Store.lean` (its part 4) and its subscription store (part 5) model the superseded version-2 designs; the demand store of the spec is the `RStore` index below, and its subscription index is `PipelineStore.deliver_run1`, `deliver_restricted` (§8.4). |
| `Subsume.subsumes_sound`, `markSubsB_sound` | The conclusion subsumption test is sound, with mark exclusions (`*∖Xs` subsumes `*∖Xn` if `Xs ⊆ Xn`). |
| `Subsume.merge_inter`, `merge_mark_inter`, `union_loses_pairs`, `union_marks_loses_pairs` | Merge rule 2 is exact for exclusions and for mark exclusions; a union loses a real pair. |
| `Subsume.record_subsumes`, `recordSubsumesB_sound`, `recordSubsumesLB_*` | Record subsumption. |
| `RStore.near_equiv`, `near_sound`, `emit_complete_M`, `emit_lookup_equiv_M`, `emitM_exact_prefix`, `restrict_complete_U`, `restrict_lookup_equiv_U`, `near_query_cost`, `deep_chain_cost` | The demand store: index = filter; complete for the emission and the restriction (the premise test of the earlier restriction, an overlap; the intersection needs less, §8.6); cost walk + length of the returned chains (not walk + count). |
| `RStore.restrictTreeE_mem_U`, `restrictTreeE_inv`, `restrictTreeE_mx`, `restrictTree_cost` | The restriction of a whole tree equals the per-path restriction (of the earlier restriction `restrictU`; the meet of the intersection at the node of `D-p.path` is argued, §7.4); one well-formed tree; it keeps the mark exclusion; cost walk + width, shared subtrees. |

### 10.5 Reversal — `Reverse.lean`

| Theorem | Statement |
|---|---|
| `revEdge_sound`, `revEdge_exact`, `rev_exact_of_empty_premise`, `rev_starEx_exact` | §9.1: sound for every mark-reversible record; exact with the Empty premise exclusion, also for a `*∖X` record. |
| `policy_premEmpty`, `answerInit_premEmpty`, `answerInit_markRev`, `revEdge_premise_mark` | Run-1 initial facts have the Empty premise exclusion; a reversed premise never has a mark exclusion. |
| `star_exact_no_exact_rev`, `no_rev_of_star_conc`, `no_rev_of_two_marks` | The limits of the reversal. |
| `Reverse.Stmt.rev_step_iff`, `flow_rev_iff_calls`, `rev_WF`, `backward_of_forward_calls` | The reversed program has the converse flow, with calls, cleaners and filters (under `RevStmts`, `RevCalls`: S11 (b), (g)); it is well-formed; the forward closure `D` on the reversed program (`Reverse.Program.rev`) is covered by the forward theorem. This is not a theorem about the backward run `Backward.DB`, which adds the zero rules and the seeds. |
| `backward_reuse`, `backward_reuse_needs_cover`, `backward_reuse_precise` | Reversed records cover the converse flows; the cover condition is necessary; `backward_reuse_precise`: an exact forward record with the Empty premise exclusion reverses into an exact record of the reversed program (under `RevStmts`, `RevCalls`). |

### 10.6 ND edges — `ND.lean`, `NDExact.lean`

| Theorem | Statement |
|---|---|
| `ND.nd_coverage` (+ `nd_coverage_single`, `nd_coverage_flow`, `nd_coverage_conc`) | THE ND COVERAGE THEOREM. For a support derivation `TaintN M n l L0` (the location `l` is tainted at `n` when the entry locations `L0` are) and initial facts lined up with `L0`, each covering its location: the edge keyed by exactly these initial facts covers `l` at `n` (with `den` for one premise), OR the closure has a request on one of them with the mark of its location. |
| `ND.nd_vuln`, `nd_vuln_root`, `nd_vuln_reach`, `nd_vuln_found` | A tree-shaped vulnerability witness gives a vulnerability. |
| `ND.ndConclusion_uncorrelated` | W7: an edge with two or more premises has no `*` tail and has a concrete mark. |
| `ND.answer_loop` | A request at one support position is answered or climbs; the loop over positions ends. |
| `ND.flow_taintN`, `D_sub_DN` | Every ordinary flow is a support derivation with one location; every object of `D` is in the ND closure. |
| `ND.Example.vuln3`, `c3_normal` | Today's `NDRule` sample (`$A = src(); $B = src(); $C = pass($A, $B); sink($C)`) gives the vulnerability, from a normal-layer conjunction. |
| `NDExact.nd_edge_exact`, `nd_edge_exact_valid`, `nd_edge_exact_gen`, `nd_edgeOK` | THE ND EXACTNESS THEOREM. Under S7 and S9, and either `Exact.FiltUp` (`NDExact.nd_edge_exact`) or S13 for valid end locations (`NDExact.nd_edge_exact_valid`: `Exact.FiltValid`, `Exact.BackOK` and `NDExact.ConjOK`): a normal-layer edge with the premise list `P` gives a support derivation `ND.TaintN M n l L0` for EVERY support `L0` that `P` covers and every end location `l` of the edge (with `den` for one premise). The converse of `ND.nd_coverage`. |
| `NDExact.nd_edge_exact_single`, `nd_edge_exact_nd` | The single-premise form (`den i f l0 l ⇒ TaintN … [l0]`) and the form for two or more premises (every covered support, every covered location). |
| `NDExact.CexLit.cex_lit`, `CexConjOK.cex_conjOK` | Both hypotheses are necessary: an abstract literal lets a correlated input with a mark exclusion through (the excluded locations reach nothing); without `ConjOK` a valid end location has an invalid support. |
| `NDExact.covers_nonempty` | Every fact covers some location (also `*/Universe` and `*∖X`), so a support can always be built. |
| `NDConfirmed.SupN`, `ConfirmedN`, `confirmed_real_N`, `confirmed_real_N_valid` | THE ND CONFIRMATION THEOREM. Under S7, S9 and S10 (`ND.NProg.WF`), and either `Exact.FiltUp` or S13 (`NDConfirmed.confirmed_real_N_valid`: `Exact.FiltValid`, `Exact.BackOK`, `NDExact.ConjOK`): a vulnerability whose sink edge is normal, whose premises are exact concrete facts, and whose premise set is supported JOINTLY (§4.9 condition 3: one call supplies every premise) is real for the support semantics (a tree witness `ND.ReachN`). |
| `NDConfirmed.CexSites.cex_sites` | Support of each premise on its own is not enough: two premises supplied at two different calls confirm a vulnerability that has no witness. |
| `NDConfirmed.confirmed_lift`, `confirmedN_iff`, `DN_lower`, `reachN_reach` | Without conjunctions the ND confirmation is the confirmation of §4.9 for one premise. |

### 10.7 Restricted runs and the iteration — `Restricted*.lean`, `Backward.lean`, `BackwardExact.lean`

The restricted closure `DR` (`Restricted.lean`) is the rule list of a restricted run (§6.1), with the rules `initR`,
`ret` and `retRec`. A demanded flow and a demanded witness (`FlowR`, `ReachR`) are defined in §1; in this earlier
model the `D-p` part reads the exit location without its mark (`PFact.coversLoc`), as the restriction `restrictU`
does (§1; the spec form `Handoff.FlowRR` reads it with its mark, `ap-history.md` F71). The coverage and
iteration theorems of this section are generic over the rules, given the contracts C2 (`EmitContractOn`), C4
(`SatContract`) and C5 in its earlier OVERLAP form (`RestrictContract`). They are about the EARLIER design: the
restriction `restrictU` and the hand-off of every summary edge (`Backward.revSummaryDemand`, `Backward.demOf`). They
stay in the model as its record. The spec restriction (the intersection) and the hand-off of the demand edges are
in §10.12 (`ap-history.md` F70). The exactness, record and confirmation theorems of this section that take a
restriction with `RestrictSub` hold for the spec restriction too (`Handoff.restrictI_sub`). All of them are about the
concrete restricted runs; for F72 see the intro of §10.

| Theorem | Statement |
|---|---|
| `RCore.emitM_contract_I`, `emitM_copies`, `satI_contract`, `emitM_satI`, `emitM_inter`, `emitM_complete`, `emitM_shape`, `emitM_chain_strong` | The spec emission satisfies C2 for concrete added facts and copies the mark (C3); the emitted fact is exactly `a ∩ D-c`, lies inside its added fact, and has the chain of the fact or the demand chain. Since F71 `markMatchB` reads a `*∖X` entry mark exactly, and the proof of `RCore.emitM_contract` takes its cell: a location that the entry pattern covers has a mark that is not in `X`. |
| `RCore.satI_markSub`, `satI_conc_record` | The satisfaction compares locations, and the marks of the fact against the marks of the premise: a cleaned fact reads a `*` premise, a concrete fact reads a `*`-premise summary. |
| `RCore.emitM_not_full_any` | C2 fails for a `*`-mark added fact under a `T` demand, for every satisfaction: the concreteness of the run is necessary. |
| `RCov.concInvR_all`, `added_concR`, `no_reqR`, `RExact.DR_concrete`, `DR_no_request`, `final_not_star`, `RMain.no_request_M` | A restricted run with a mark-copying emission is CONCRETE: every initial fact, edge and added fact has a concrete mark, no final fact has the `*` tail, and the run has NO request (also with cleaners). (The concrete design: the F72 emission does not copy the mark under a `*` pattern, and the concreteness claim is false for the F72 runs; they have no request rule, §4.5.) |
| `RCore.restrictU_fails`, `restrictS_contract`, `restrictU_eq_S_nonstar`, `RExact.restrict_U_eq_S` | The earlier restriction (`restrictU`) does not satisfy C5 as a function; the auxiliary restriction `restrictS` does; the two agree on every conclusion without the `*` tail, and with a mark-copying emission they give the same run. So the coverage theorem holds for the run with `restrictU`. (The spec restriction `Handoff.restrictI` satisfies C5 for a premise inside `D-c` directly, §10.12.) |
| `RExact.complete_premise_exact`, `complete_rev_exact` | A normal edge of a concrete run has a premise with the `$` tail, so its record reverses exactly. (False for the F72 runs: a normal edge can have a FLOW premise, §9.1.) |
| `RCases.p1_found_M`, `p2_found_M`, `p1_reachR_M`, `p2_reachR_M` | Run 3 (forward) reports programs 1 and 2, with the emission of §6.3 and the earlier restriction `restrictU`. (With the intersection: `HandoffRCases.p1_found_I`, `p2_found_I`, §10.12.) |
| `RCov.coverageR`, `reach_strongR`, `vuln_foundR` | THE COVERAGE OF A RESTRICTED RUN: for a demanded flow from a covered entry location, an edge covers the pair or the run has the request; its own summaries demand the same flow. |
| `RCov.coverageD`, `reach_to_reachR`, `vuln_foundD` | Run 1 reports every real vulnerability, and its summaries demand its witness. |
| `RCov.iteration_sound`, `iteration_sound_conc`, `RMain.iteration_sound_M`, `iteration_sound_M_identity` | THE ITERATION THEOREM: if every backward step satisfies the strong form of contract B (`BackwardContract`: every vulnerability witness that the summaries of a forward run demand stays demanded), EVERY forward run reports every real vulnerability; any field limits, any records. The form of the earlier §6.6 (`Backward.BackwardContractD`) is weaker and is enough (`Backward.iteration_sound_M_D`). |
| `RCov.backward_identity`, `backward_of_superset`, `RMain.noSink_contract`, `everyWitness_contract_fails` | The identity backward step satisfies B; B is about sink witnesses only. |
| `Backward.DB`, `demOf`, `revSummaryDemand` | The backward run of §9.2: the rules of `DR` on the reversed program, the zero fact from the roots, the zero binding into every callee, the seeds, the balanced return (generic in the emission, the satisfaction, the restriction, the demand and the records); the EARLIER hand-offs in both directions (every summary edge, in every layer, before the restriction; the spec hand-offs `Handoff.handF`, `demOfN` are in §10.12). |
| `Backward.B_general`, `iteration_general`, `BackwardContractD`, `repD_of_rep`, `iteration_sound_D`, `iteration_sound_M_D` | THE BACKWARD RUN SATISFIES THE CONTRACT, for the earlier hand-off: for every forward run, if the backward demand contains its reversed summaries and the seeds contain its reported sinks, the hand-off satisfies the mark-aware contract; so every forward run reports every real vulnerability. (For the spec hand-off: `HandoffBackward.B_generalN`, `HandoffMain.iteration_generalN`, §10.12.) |
| `Backward.BackwardContractRep`, `rep_of_B`, `iteration_sound_rep`, `B_fragment_rep` | The contract for reported vulnerabilities only, with the plain demanded witness; on programs where no call binds back the backward run satisfies it directly. |
| `Backward.dem1_exact`, `dem2_exact`, `p1_found`, `p2_found` | For programs 1 and 2 the hand-off of the backward run is exactly the callee demand of `RCases.dem1M` (`dem2M`), the zero demand `Backward.zeroDem`, and one pattern `(D-c, none)` of the root; forward run 3 reports the vulnerability. (Earlier hand-off. The hand-off of the demand edges contains the same callee patterns, `HandoffRCases.p1_handoff`, `p2_handoff`; that it is exactly these parts is checked by hand, §9.2.) |
| `Backward.lost_plain`, `B_fails_plain` | With the plain converse of the forward bindings (no zero binding into the callee) program 1 is lost. |
| `BExact.DB_concrete`, `DB_no_request`, `DB_no_requestM`, `CexSeed.cex_seed` | The backward run is concrete and raises no request when its seeds have concrete marks (a seed with the mark `*` would raise one). (The concrete design: the F72 backward run has `*` requirements, §9.2, and no request rule.) |
| `BExact.edge_exactB`, `edge_exactB_valid`, `edge_exactB_rev`, `summary_rev_flow`, `rev_record_exact`, `revRecs_exact`, `CexZeroBack.cex_rec` | A normal backward edge with a non-zero premise is exact for the reversed program and reverses into an exact forward record, under S11 (c); the reversal also under S11 (g) (`Reverse.RevStmts`, `RevCalls`) and with the records of the backward run exact off the zero base (`BExact.RecsExactNZ`); all for `Exact.FiltUp`, with no form for type filters; without S11 (c) it is false. |
| `BExact.recsSeq_exact`, `recsSeq_exactV`, `accRecs_exact`, `accRecs_exactM`, `seq_edge_exact`, `seq_confirmed_real` | The persisted forward records stay exact over the whole run sequence (S14 for the forward records: every record is an exit edge of an earlier forward run, `BExact.RecsFromRuns`); every normal edge and every confirmed vulnerability of every forward run is real. |
| `BExact.binv_all`, `no_static_rule_backward` | The backward run needs no static rule, if the reversed program satisfies S12 (a) to (d) and its seeds and records keep the invariant (`BExact.SeedsOK`, `StaticsIter.RecOK`); an `[any]` sink on a class position is outside it (precision only). |
| `RExact.edge_exactR_valid`, `closed_exactR_valid`, `recs_of_DR_valid`, `recs_of_D_valid` (valid locations, S13 and `RExact.RecsExactV`); `edge_exactR`, `complete_exactR`, `recs_of_DR`, `recs_of_D`, `closed_exactR`, `RMain.closed_records_exactM` (`Exact.FiltUp` and `RExact.RecsExact`); `RExact.recs_union` | Exactness and record reuse in forward restricted runs. Hypotheses: S7, the records that the run reads are exact (S14), every satisfaction reads the marks (`RExact.SatMark`), and the restriction only removes pairs (`RestrictSub`). The exit records of the run are exact again, and the union of exact record sets is exact. |
| `RExact.SupM`, `ConfirmedM`, `confirmed_realM_gen`, `confirmed_realM_gen_valid` (every satisfaction with `SatMark`, every restriction with `RestrictSub`, so also the intersection by `Handoff.restrictI_sub`); `RMain.confirmed_real_M`, `confirmed_real_M_valid` (the earlier restriction `restrictU`) | A confirmed vulnerability of a forward restricted run is real for the reference semantics (§3.5), under S7, S14 and `Exact.FiltUp` or S13 (`Exact.FiltValid`, `Exact.BackOK`); the support accepts the emitted exact fact. |

### 10.8 Statics — `Statics.lean`, `StaticsIter.lean`, `StaticsConfirmed.lean`

| Theorem | Statement |
|---|---|
| `Statics.coverageD`, `vulnD` | Under the construction rules (`SWF`), run 1 with the position request of §4.10 (`Design`) reports every real vulnerability. |
| `Statics.DS_edgeOK`, `edge_exactS`, `edge_exact_validS`, `complete_exactS` | Its normal edges denote only real flows. |
| `Statics.cinv_all`, `no_any_above` | No static fact with the `[any]` tail occurs above a static position; a static fact above a position that is not exact is an identity static `*` edge (the premise at the same path, the normal layer). |
| `Statics.gen_read_DS`, `gen_read_sreq` | A static read on the abstract static root gives no fact and raises the position request. |
| `Statics.CexAbove.y_vuln_normal`, `CexWide.w_vuln_normal`, `CexClean.deep_vuln_normal` | A write in the caller, a write in a callee and a cleaner in a callee: the vulnerability is found through a normal edge. |
| `Statics.CopyF2F.c_vuln_normal`, `DeepSink.e_vuln_normal`, `DeepSinkParam.p_vuln` | A pass rule between static fields; a sink below a static field (the ordinary mark request climbs to a static caller premise: a normal edge; to a parameter premise: the request chain, a demand edge, as for an instance field). |
| `Statics.abovePos_len`, `f2f_not_above` | A path above a static position has at most one accessor; a field-to-field edge never lands above a static position. |
| `Statics.CexClean.shallow_misses`, `CexAbove.cex_user_misses`, `CexWide.counterexample` | The rule variants that fail: the chain answer of a static mark request; the narrow climb without a fallback; the first fire (the static root, reads only) with the fallback only for caller premises off the static base (`CexWide.Xn`, also with the at-or-below answer, `CexWide.Xc`). |
| `Statics.CexAny.counterexample` | Not a failing variant: the at-or-below answer, which the final rule uses (§4.10 item 2; `Statics.Design`, part `below`; in the program `CexAny.Xb`, `CexAny.Xc`, with the first fire, `gen = false`), loses a flow WHEN a source puts an `[any]` fact on a bare class (`(S, <C>, [any], T)`). This is the reason for S12 (b): the interpreter rejects such a source (`interpreter.md` §1.4). |
| `StaticsIter.rinv_all`, `no_any_above_R`, `static_step_below`, `static_sink_below`, `no_request`, `DeepReadIter.deep_read_above` | AFTER RUN 1 NO STATIC RULE IS NEEDED (the concrete design; with FLOW premises on `S`, F72, PENDING, §4.10): in a forward restricted run (`DR`), under S12 (a) to (d) (`StaticsIter.SWFR`) and persisted records that keep the static invariant (`StaticsIter.RecOK`), for every demand, no static `*` or `[any]` fact lies above a static position; every static operation at most two accessors deep is the case at or below; no request. A deeper static read or sink follows the ordinary rules of an instance field (`DeepReadIter.deep_read_above`: a restricted run can hold `(S, <C>.f, [any], T)` above a deep read). |
| `StaticsIter.reach_strongDSD`, `iteration_general_DS`, `no_static_rule_after_run1` | The iteration from run 1 = `DS`, with plain forward restricted runs after it: every forward run reports every real vulnerability, and every later forward run satisfies the invariant (under `StaticsIter.RecOK` for the records). The static invariant of the backward run `Backward.DB`: `BExact.no_static_rule_backward` (§10.7, with its hypotheses). |
| `StaticsIter.ExampleIter.run3_confirmed`, `WideIter.run3_confirmed`, `AboveIter.run3_confirmed`, `CleanIter.run3_confirmed`, `ExampleIter.demE_exact` | The worked static programs: forward run 3 confirms the vulnerability through a normal edge with no request; the exact demand for `Example`. |
| `StaticsConfirmed.SupS`, `ConfirmedS`, `confirmed_realS`, `confirmed_realS_valid` | Run 1 with the static rule confirms only real vulnerabilities; the support accepts the mark answer on a static premise (§4.10 item 4). |
| `StaticsConfirmed.confirmedS_iff`, `CexS.cexS_filt`, `CexS.cexS_mark`, `ExampleConf.confirmed`, `CleanConf.confirmed` | Without a static initial fact the static confirmation is the plain one; S7 and the validity are necessary; the worked programs are confirmed in run 1. |

### 10.9 Source seeds — `ForwardSeeds.lean`, `PipelineSeeds.lean`

| Theorem | Statement |
|---|---|
| `FSeeds.keepSources`, `mem_keepStmt`, `unseeded_dropped`, `cond_kept`, `zero_kept` | The program of a forward restricted run (§6.1 rule 6): every unseeded unconditional source edge is dropped; the conditional sources and the zero keep edge stay. |
| `FSeeds.keep_WF`, `keep_bindStar`, `keep_markRev`, `keep_noZeroBack`, `keep_zeroKept`, `keep_exitReach` | The seeded program keeps every hypothesis of `Backward.iteration_general`. |
| `FSeeds.flow_keep`, `reach_keep`, `reachRD_keep`, `flow_keep_mono`, `flow_keep_all_iff` | The seeded program has fewer flows than `P`; more seeds give more flows; seeding every source gives the flows of `P`. |
| `FSeeds.srcHit`, `srcHit_applies` | The source hits of a backward run (§9.2); a hit is a reversed source edge that applies to a concrete requirement. |
| `FSeeds.demanded_src`, `B_src` | Contract B with item 3 (§6.6): the demanded witness is a witness of the program seeded by every superset of the source hits. |
| `FSeeds.iteration_src`, `runSeqSrc` | The iteration with source seeds: every forward run reports every real vulnerability of `P`. |
| `PipelineSeeds.driver_iteration_src` | The same for the driver of `analyzer-core.md` (§7.7). |

### 10.10 Conclusion kinds and the zero-drop — `Kinds.lean`, `NDZ.lean`, `NDZero.lean`, `NDZeroThms.lean`, `NDZeroBase.lean`

| Theorem | Statement |
|---|---|
| `Kinds.flow_abstract`, `flow_no_exact`, `flow_no_exact_gen`, `taint_concrete`, `kinds_D` | §7.2 for run 1 without the static rule (the closure `D`): a `*` premise gives an abstract conclusion mark and no `$` tail (FLOW); a concrete or zero premise gives a concrete mark and no `*` tail (TAINT); a `*` tail is abstract and normal (W2). Hypotheses: S7 (`Exact.MarkWF`), S8 (`Invariant.no_univ_star` conditions), `Kinds.ExactTargetConc` (S8 duty), the run-1 policy (`Kinds.InitK`). |
| `Kinds.CexK.cex_etc`, `cex_premConc`, `cex_noUniv`, `cex_markWF`, `cex_alpha` | Each hypothesis is necessary: without it a FLOW edge gets a `$` tail or a concrete mark. |
| `Kinds.nd_taint`, `ndz_taint`, `CexND.*`, `ZeroMembers.*` | §4.6: an edge with two or more premises is TAINT: every member concrete, a concrete conclusion with no `*` tail; in `NDZ.DNz` also no zero member. |
| `Kinds.kinds_DR`, `kinds_DR_emitM`, `kinds_DB`, `kinds_DB_taint`, `CexSeedTail.cex_seed_tail` | The restricted runs have REACH and TAINT only; the backward tails need `SeedTails` (S11 (f)). (The concrete design: since F72 a restricted run has FLOW trees, §7.2.) |
| `NDZ.DNz`, `dropZ`, `zStar` | The closure of the spec (§4.6): `ND.DN` with the union of the premise sets WITHOUT the zero fact at a conjunction and at an ND summary application. |
| `NDZero.zero_everywhere`, `zero_everywhere_z` | The zero fact is at every node that an edge reaches, in `ND.DN` and in `NDZ.DNz`. Hypotheses: `Backward.ZeroKept` (S11 (d)), `NDZero.ZeroCalls` (§3.5: no call touches the zero base; the zero binding), `ConjAdj` (a conjunction beside an instruction edge), the policy serves the zero fact by itself. |
| `NDZero.dnz_to_dn`, `dn_to_dnz`, `edge_iff`, `ninit_iff`, `nadded_iff`, `nreq_iff` | THE CORRESPONDENCE: a `NDZ.DNz` edge with the premise set `P'` is a `ND.DN` edge with a list `P` with `NDZ.dropZ P = P'` and the same fact; a NORMAL `NDZ.DNz` edge comes from a NORMAL `ND.DN` edge. The converse (`dn_to_dnz`) needs `NDZero.ZeroLinks`, which `zeroLinks_of_noZeroGen` gives from `NDZeroBase.NoZeroGen` (§4.6; `interpreter.md` I11 (c), (d), §3.1, §5.3). |
| `NDZero.summary_nd_fact`, `summary_nd_exists` | An ND conclusion applied by the single-premise `ret` (a `{zero, i}` summary of the model is the summary `{i}` of the spec) gives the same fact, in a layer that is not lower. |
| `NDZeroThms.nd_coverage_z`, `nd_coverage_zg`, `nd_vuln_found_z`, `nd_vuln_found_zg`, `nd_vuln_reach_z` | Coverage and the vulnerability theorem for `NDZ.DNz`. |
| `NDZeroThms.nd_edge_exact_z`, `nd_edge_exact_valid_z` | Exactness of a normal `NDZ.DNz` edge: a support derivation with the support of `P'` plus zero locations. |
| `NDZeroThms.ConfirmedNz`, `confirmedNz_N`, `confirmed_real_Nz`, `confirmed_real_Nz_valid` | The confirmation of §4.9 on the `NDZ.DNz` premise set: it gives the confirmation of the `ND.DN` vulnerability (a zero member is supplied by the caller zero edge at the same call, `supN_zero`), so a confirmed vulnerability is real (`ND.ReachN`). |
| `NDZeroBase.zero_base_inv`, `dnz_applicable_zero` | Under `NoZeroGen` and `AlphaZero` (the run-1 policy satisfies it, `NDZeroBase.policy1_alphaZero`), every `NDZ.DNz` fact on the zero base is the zero fact, so only the zero premise is satisfied by the zero added fact. |

### 10.11 The `[any-taint]` tail — `AnyTaint*.lean`, `PipelineAnyTaint*.lean`

The model has one tail kind `.any` for both any tails (§11.2 gives the correspondence): a normal `.any` conclusion is
`[any-taint]`, a demand `.any` conclusion is `[any]`, and a premise with the flag `must` is an `[any-taint]` premise.
The exclusion of `[any-taint]/E` is the field `ex` of an annotated conclusion (`AnyTaintEx.XFact`) and the field `jex`
of a premise (`AnyTaintEx.XObj`). The base closures `D` and `DR` apply no W6, and every normal edge of them is exact,
normal `.any` edges included (§10.3, §10.7).

THE SPEC CLOSURES are the refined closures of round 2 (`AnyTaintExDefs.lean`, namespace `AnyTaintEx`):

* `AnyTaintEx.D6X`: run 1 with W6T (`w6tX`) and the exclusion: the core operation `applyEdgeX` (the base
  `applyEdge` with the annotation rules `annX` and the layer rule `layerX`, §4.1), the field limit `limitFX` (§4.4),
  the cleaner `cleanResX` (§4.7), the sink check `checkX` (§4.9);
* `AnyTaintEx.DRX`: a forward restricted run over the objects `XObj` with must flags and exclusions, the start fact
  `startX` (§6.5) and the record demotion `recLayerX` (§4.3); the emission, the satisfaction and the restriction are
  parameters;
* `AnyTaintEx.DRXs`: `DRX` with the rules `emitX` (§6.3), `satX` (§4.3) and the EARLIER restriction `restrictX`.
  The spec restriction of §6.4 is the intersection `HandoffX.restrictIX` (§10.12): the spec forward restricted run is
  `AnyTaintEx.DRX` with `emitX`, `satX` and `HandoffX.restrictIX`. Every theorem below that takes the restriction as a
  parameter with `AnyTaintExExact.RestrictOKX` holds for it (`HandoffX.restrictIX_ok`); the theorems stated for
  `AnyTaintEx.DRXs` (the names with `Xs`, and `AnyTaintExExact.specX_rules`) are for the earlier restriction.

The backward run stays `Backward.DB` (no `[any-taint]`, W8 (d)). It reads a forward run with the exclusions and the
must flags dropped (`AnyTaintExCov.forget6`, `forgetX`).

THE ROUND-1 CLOSURES (`AnyTaintDefs.lean`, namespace `AnyTaint`) model the first F69 text, which demoted an
`[any-taint]` fact at an exclusion: `AnyTaint.D6T` (run 1 with W6T: `w6t`, `transferT`) and `AnyTaint.DRT` (a forward
restricted run over `TObj` with must flags: `emitT`, `startT`, `recLayer`). They are not the spec closures. This spec
cites a round-1 result only where it states a rule of the amended design: the rule W6T, the must flags and the record
demotion, the conjunction rule (`AnyTaintND`) and the round-1 counterexamples; and, next to the refined theorem, for
contrast. The kinds invariant of run 1 and the premises of a normal restricted edge are proved for the spec closures
(`AnyTaintExKinds`, below). The round-1 programs with no exclusion (G, C, I and P) are re-derived in the spec closures
(`AnyTaintExCases2`, below; run 3 with the earlier restriction `AnyTaintEx.DRXs`); the round-1 names of their results (`AnyTaintCases`) are the model of the first F69 text
only. A refined object has a base object of the round-1 closure (the relations `AnyTaintEx.Refines6`, `RefinesR`): the
simulations `AnyTaintEx.Sim6X` and `SimRX` are proved (`AnyTaintExKinds.sim6X` under `AnyTaintEx.NoBelowCleaner`, and
`simRX` also under `AnyTaintEx.RecsRefine`), but no spec claim needs them: each refined run justifies its own
witnesses (§6.6). (The docstrings of `AnyTaintSim` name the round-1 decisions; the statements are those of the tables
below.)

The hypotheses of round 2, each with the spec item that makes it true: `AnyTaintEx.SatInsideX` (the satisfaction reads
`inside` with the exclusions, §4.3; `satX_inside`), `AnyTaintEx.EmitCopiesMarkX` (C3; `emitX_copies`),
`AnyTaintExExact.RestrictOKX` (the restriction keeps the normal form of W8, §6.4; for the spec restriction
`HandoffX.restrictIX_ok`, for the earlier one `AnyTaintExExact.restrictX_ok`; it replaces `AnyTaintEx.RestrictSubX`, which is
false for `restrictX`), and for the records `AnyTaintEx.RecsExactX`,
`AnyTaintExExact.RecsConcX` and `RecsWFX` (S14; the run sequence discharges them). The hypotheses
`AnyTaint.TaintConc` (S15) and `BindNoAny` (S10) serve only the kinds invariant of run 1 (`AnyTaintExKinds.kinds_D6X`;
round 1 `AnyTaintSim.kinds_D6T`), and `W6.SummaryStar` only the round-1 simulation of run 1 (the run-1 policy has it,
`W6.summaryStar_policy`; the refined kinds theorems do not need it). The simulations of the refined runs need
`AnyTaintEx.NoBelowCleaner` (no `below` cleaner: its new `$` fact has no base object) and, for a restricted run,
`AnyTaintEx.RecsRefine`. No theorem has a hypothesis on the choice of the taint edges, except the kinds invariant.

RUN 1 (`AnyTaintEx.D6X`):

| Theorem | Statement |
|---|---|
| `AnyTaintExCov.applyEdgeX_sound`, `annX_admits`, `transferX_sound`, `bind_inX`, `bind_outX`, `applySummaryX_sound`, `limitFX_sound`, `startX_sound`, `checkX_sound`, `cleanResX_sound`, `partX_sound` | THE LOCAL SOUNDNESS: every refined operation covers the composition of the fact relation and the edge relation, and the exclusion of its result admits every reached end location (the core lemma of §4.1 with the exclusion). |
| `AnyTaintExCov.coverage6X`, `reach_strong6X`, `vuln_found6X`, `vuln_found_policy6X` | COVERAGE and the vulnerability theorem of run 1: every real vulnerability is reported, in some layer. For the policy the only hypothesis is S10. |
| `AnyTaintExExact.applyEdgeX_exact`, `applyEdgeX_cov`, `keep_row_exact`, `above_row_exact`, `below_row_exact`, `transferX_exact`, `applySummaryX_exact`, `cleanResX_exact`, `clean_rows_exact`, `below_new_fact_real` | THE LOCAL EXACTNESS: a normal result is exact on the admitted locations. The rows of W8 stay in the normal layer and are exact: the exclusion edge at `r = []`, the case `above` with the edge exclusion, the case `below` that keeps `E`, and the cleaners `atAndBelow` and `below` one accessor below the fact; the new `$` fact of the `below` cleaner is real. |
| `AnyTaintExExact.D6X_wf`, `D6X_NS`, `D6X_edgeOK`, `edge_exact6X`, `edge_exact_valid6X` | EXACTNESS OF RUN 1: every edge conclusion is in the normal form of W8; every pair of a normal edge, also `[any-taint]/E` with its exclusion read, is a concrete flow (under S7 and `Exact.FiltUp`; the valid form under S7 and S13). |
| `AnyTaintExExact.sup_entry6X`, `sup_entry6X_valid`, `confirmed_real6X`, `confirmed_real_valid6X`, `confirmed_real_valid6X_of`, `sink_denX` | CONFIRMATION IN RUN 1 (§4.9): a vulnerability confirmed on a NORMAL sink edge (`AnyTaintEx.Confirmed6X`: also `[any-taint]/E`, and the sink pattern meets an admitted location) under a supported premise (`Sup6X`) is real (under S7 and `Exact.FiltUp`; the valid form under S7 and S13, with a sink pattern of valid locations). |
| `AnyTaintExKinds.D6X_any_conc`, `D6X_flow_no_any_taint`, `D6X_flow_no_excl`, `kinds_D6X`, `kinds_D6X_gen`; `AnyTaintSim.CexKinds.cex_taintConc`, `cex_bindNoAny` | THE KINDS INVARIANT (§7.2, W8 (a)) of `AnyTaintEx.D6X`, by a direct induction (not through a simulation): under `AnyTaint.TaintConc` (S15) and `AnyTaint.BindNoAny` (S10) every normal `.any` conclusion (`[any-taint]/E`) has a concrete mark, for every abstraction; so a FLOW edge has no `[any-taint]` conclusion (`AnyTaintExKinds.D6X_flow_no_any_taint`, also under S7; no `W6.SummaryStar`) and carries no exclusion (`AnyTaintExKinds.D6X_flow_no_excl`); with the hypotheses of `Kinds.kinds_D`, the partition of run 1 (`AnyTaintExKinds.kinds_D6X` for the policy, `kinds_D6X_gen` for every `Kinds.InitK` abstraction). The `below` cleaner's new `$` fact has the concrete mark of its `[any-taint]` fact, so it touches no claim. Both hypotheses are necessary. |
| `AnyTaintSim.D6T_any_conc`, `D6T_flow_no_any_taint`, `kinds_D6T` | ROUND 1, THE KINDS INVARIANT of `AnyTaint.D6T`: the same claims; `AnyTaintSim.D6T_flow_no_any_taint` also under `W6.SummaryStar`, which its simulation needs. |
| `AnyTaintExKinds.sim6X`, `sim6XIn`, `D6X_abs_same`, `applyEdgeX_LE`, `annX_geo_ex`, `RelA` | THE SIMULATION OF RUN 1 (`AnyTaintEx.Sim6X`, `Sim6XIn`) under `AnyTaintEx.NoBelowCleaner`: every object of `AnyTaintEx.D6X` has an `AnyTaint.D6T` object with the same base fact (`AnyTaintEx.Refines6`); an abstract-mark edge of `D6X` is a `D6T` edge with the same fact and layer (`AnyTaintExKinds.D6X_abs_same`). A non-empty result exclusion comes from a base demotion or from an exclusion of the input, the premise or the target (`AnyTaintExKinds.annX_geo_ex`). No spec claim needs it. |
| `AnyTaintSim.D_le_D6T`, `D6T_le_D`, `D_le_D6T_1`, `D6T_le_D_1`, `D6T_same_shape`, `D6T_normal`, `coverage6T`, `vuln_found_policy6T`, `edge_exact6T`, `edge_exact_valid6T`; `AnyTaintSim.CexT.cex_w6t_changes_fact`; `AnyTaintExact.D6T_edgeOK`, `recs_of_D6T_valid`, `confirmed_real_valid6T` | ROUND 1, THE RULE W6T without the exclusion (`AnyTaint.D6T`): `D6T` has the objects of `D`, each edge with the same fact in the same or a raised layer (hypothesis `W6.SummaryStar`; the forms `_1` for the run-1 policy with no hypothesis); without `SummaryStar` W6T changes a fact. Its coverage (S10 for the policy), its exactness (the `AnyTaintSim` forms under `W6.SummaryStar` too), its records and its confirmation. |
| `AnyTaintSim.D6_le_D6T`, `D6_normal_D6T`, `D6_normal_D6T_1` | ROUND 1: W6T is not less precise than the old rule W6: every normal edge of `W6.D6` is a normal edge of `AnyTaint.D6T` (for an abstraction that gives `$` only with a concrete mark; the forms `_1` for the run-1 policy). |

THE RESTRICTED FORWARD RUN (`AnyTaintEx.DRX`, with the rules as parameters; the names with `Xs` and
`AnyTaintExExact.specX_rules` are for `AnyTaintEx.DRXs`, the earlier restriction). These theorems are about the
concrete restricted runs (the hypothesis `AnyTaintEx.EmitCopiesMarkX`, C3 of the concrete design, or the rules
`emitX`, `satX`); for F72 they are PENDING (the intro of §10):

| Theorem | Statement |
|---|---|
| `AnyTaintExCov.concX_all`, `noReqX`; `AnyTaintExExact.DRX_wf`, `DRX_mustAny`, `DRX_conc` | CONCRETENESS (under C3): every premise, conclusion and added fact has a concrete mark; no request; no `*` final tail; every conclusion is in the normal form of W8; every must-premise has an any tail. (The concreteness claim is false for the F72 runs.) |
| `AnyTaintExKinds.DRX_normal_premise`, `DRX_must_premise`, `DRX_premLayer`, `DRXs_normal_premise`, `DRXs_must_premise` | THE PREMISE OF A NORMAL EDGE (§9.1; the form of `RExact.complete_premise_exact` for `AnyTaintEx.DRX`): a normal edge has a `$` premise that is not a must-premise, or a must-premise, which has the `.any` tail and a concrete mark (`[any-taint]`, with or without an exclusion); never a non-must `.any` or a `*` premise. Hypothesis `AnyTaintEx.EmitCopiesMarkX` (C3, which `AnyTaintEx.emitX_copies` gives for the spec run); for the earlier instance `DRXs` none (`AnyTaintExKinds.DRXs_normal_premise`, `DRXs_must_premise`). (False for the F72 runs: a normal edge can have a FLOW premise.) |
| `AnyTaintExKinds.simRX`, `simRXIn` | THE SIMULATION OF A RESTRICTED RUN (`AnyTaintEx.SimRX`, `SimRXIn`) under `AnyTaintEx.NoBelowCleaner` and `AnyTaintEx.RecsRefine`: every object of `DRXs` has an object of the spec instance of `AnyTaint.DRT` with the same base fact (`AnyTaintEx.RefinesR`). No spec claim needs it. |
| `AnyTaintExCov.emitX_contract`, `SatContractX`, `satX_contract`, `RestrictContractNSX`, `restrictX_contractNS`, `restrictX_not_contract` | THE CONTRACTS of §6.1 with the exclusions: C2 for `AnyTaintEx.emitX`, C4 for `satX`; C5 in the earlier overlap form for the earlier restriction `restrictX` on every conclusion without the `*` tail, the full form false, as for `restrictU`. (The spec restriction `HandoffX.restrictIX` satisfies C5 for a premise inside `D-c` on every conclusion, §10.12.) |
| `AnyTaintExCov.coverageRX`, `coverageRX_summary`, `reach_strongRX`, `vuln_foundRX`, `coverageRXs`, `vuln_foundRXs` | COVERAGE relative to the demand (§10.7) and the vulnerability theorem; with the earlier rules (`coverageRXs`, `vuln_foundRXs`) under S10 only. (The spec run with the intersection: `HandoffX.coverageRXI`, `coversN_DRXI`, §10.12.) |
| `AnyTaintExExact.DRX_edgeOK`, `summaryX_pair`, `summaryX_end`, `startX_must_end`, `edge_exactX_gen`, `edge_exactX`, `edge_exactX_valid` | THE EXACTNESS INVARIANT (`AnyTaintEx.EdgeOKX`): a normal edge of a premise that is not a must-premise is exact pair by pair on the admitted locations; a normal edge of a must-premise is END-EXACT on the admitted locations (`AnyTaintEx.EndExactX`). Hypotheses: S7, `Exact.FiltUp` or S13 (`Exact.FiltValid`, `Exact.BackOK`), `AnyTaintEx.SatInsideX`, `AnyTaintExExact.RestrictOKX`, `AnyTaintEx.EmitCopiesMarkX`, the records `AnyTaintEx.RecsExactX` with `AnyTaintExExact.RecsConcX` and `RecsWFX`. A must record applied by `applicable` only gives a demand result, so it needs no exactness. |
| `AnyTaintExExact.recs_of_DRX`, `recs_of_DRX_valid`, `recs_of_DRX_gen`, `recsConc_of_DRX`, `recsWF_of_DRX` | THE RECORDS (S14, §8.7): the exit edges of an `AnyTaintEx.DRX` run, with their must flags and exclusions, are exact or end-exact records, with concrete must records, in normal form. |
| `AnyTaintExExact.restrictX_ok`, `restrictOKX_of`, `specX_rules`; `AnyTaintEx.satX_inside`, `emitX_copies` | THE RULES have the three properties: `emitX` copies the mark, `satX` reads `inside` with the exclusions, the earlier restriction `restrictX` keeps the normal form, the layer, and only removes pairs (`specX_rules`: the earlier rules). The spec restriction has the third property too (`HandoffX.restrictIX_ok`, §10.12). |
| `AnyTaintExExact.sup_entryX`, `confirmed_realX`, `confirmed_realX_valid`, `confirmed_realX_valid_of`, `confirmed_realXs` | THE SUPPORT AND THE CONFIRMATION (§4.9): every admitted location of a supported premise (`AnyTaintEx.SupX`, `SupLinkX`: the same concrete mark, `inside` with the exclusions) is entry-reachable, ALL admitted locations of a must-premise; a vulnerability confirmed on a normal sink edge under a supported premise (`AnyTaintEx.ConfirmedX`) is real. Hypotheses as `AnyTaintExExact.edge_exactX`; for the earlier rules `confirmed_realXs`; for the spec rules through `HandoffX.restrictIX_ok`. |
| `AnyTaintExExact.runX`, `liftRecsX`, `liftRecsX_exact`, `liftRecsX_conc`, `liftRecsX_wf`, `RecsFromRunsX`, `recsSeq_exactX`, `recsSeq_exactX_valid`, `seq_confirmed_realX`, `seq_confirmed_realX_valid` | THE RUN SEQUENCE: if every record is an exit edge of run 1 or of an earlier restricted run of the same program (`RecsFromRunsX`), every record set is exact with concrete must records in normal form, and every confirmed vulnerability of every restricted run is real, with no exactness hypothesis on the records. The reversed backward records and the seeded runs with exclusions are argued (§11.2). |
| `AnyTaintSim.factSim`, `factSim_M`, `DRT_flag_swap`, `DRT_must_any`, `kinds_DRT`; `AnyTaintExact.DRT_edgeOK`, `edge_exactT_valid`, `confirmed_realT_valid`, `RecsFromRunsT`, `seq_confirmed_realT_valid` | ROUND 1, THE MUST FLAGS without the exclusion (`AnyTaint.DRT`): `DRT` has the facts of `DR` (hypotheses `EmitCopiesMark`, `AnyTaint.RestrictFact`); the must flag of a premise changes only layers; a non-must edge is exact pair by pair, a must edge END-EXACT (`AnyTaint.EdgeOKT`, `EndExact`); the confirmation, also over the run sequence when every record is an exit edge of an earlier forward run (`AnyTaintExact.RecsFromRunsT`). |

THE COUNTEREXAMPLES (each one shows that a rule of the amended design is necessary):

| Theorem | Statement |
|---|---|
| `AnyTaintExExact.CexAbove.cex_above` | The check of the exclusion in the case `above` (§4.1): without it the read of the field that a setter wrote gives a normal edge that no flow has. |
| `AnyTaintExExact.CexExactCleaner.cex_exact_cleaner` | The `exact` cleaner one accessor below an `[any-taint]` fact must demote it (§4.7): `[any-taint]/{f}` would miss the real `x.f.g` (a soundness loss), and a normal `[any-taint]/{}` would claim the cleaned `x.f` (not exact, `¬ AnyTaintEx.EdgeOK6X`). |
| `AnyTaintExExact.CexRestrictSub.cex_restrict_sub` | The form `AnyTaintEx.RestrictSubX` is false for `restrictX` on a conclusion that is not in normal form: so the hypothesis is `AnyTaintExExact.RestrictOKX`. |
| `AnyTaintExExact.CexSideConditions.cex_htx`, `cex_hfx` | The two side conditions of the local lemma `applyEdgeX_exact` are necessary; the closures give them. |
| `AnyTaintExCov.CexRoute.route_a_false`, `rx_no_y` | The hand-off of a refined run can be SMALLER than that of the round-1 run on the same demand (the exclusion removes summaries), so the iteration is proved directly (§6.6). |
| `AnyTaintEx.Vec.below_keeps_loc` | The case `below` does not test `r` against the exclusion of the fact: such a test would lose a real flow (§4.1). |
| `AnyTaintExact.CexApp.cex_app`, `CexApp.record_not_pair_exact`, `CexRev.cex_rev`, `CexSupMark.cex_sup_mark`, `CexRecConc.cex_rec_conc` | ROUND 1: without the record demotion a must record applied by `applicable` gives a false normal edge (§4.3); a must record is end-exact, not exact pair by pair; the reversal of a must record is not a converse flow (§8.7 R3); without the same-mark condition `AnyTaint.SupLink` accepts a premise with the mark `*` (§4.9; a concrete premise has the condition, `AnyTaintExact.markSub_conc`); the concrete mark of a must record (`RecsConcT`) is necessary. |
| `AnyTaintCases.W.keep_normal_false`, `keep_normal_not_endExact`, `keep_normal_confirms_unreal` | ROUND 1: a normal keep result WITHOUT the exclusion is false (it confirms the overwritten field, which is not real): so the exclusion edge must carry the written field (§4.1). |

THE ITERATION AND THE BACKWARD RUN:

| Theorem | Statement |
|---|---|
| `AnyTaintExCov.runSeqX`, `forget6`, `forgetX`, `iteration_invariantX`, `iteration_generalX`, `iteration_reportsX`, `runSeqSrcX`, `iteration_src_invariantX`, `iteration_srcX` | THE ITERATION (§6.6): run 1 `AnyTaintEx.D6X`, the backward runs `Backward.DB` (restricted by the hand-off of each forward run, read with the exclusions and the must flags dropped), the forward restricted runs `AnyTaintEx.DRXs`: EVERY COMPLETE FORWARD RUN REPORTS EVERY REAL VULNERABILITY, in some layer (`AnyTaintExCov.iteration_reportsX` is the form to cite for the EARLIER hand-off and the earlier restriction). Hypotheses: those of `Backward.iteration_general` (with the source seeds those of `FSeeds.iteration_src`); none on the taint edges or on the records. The spec hand-off and restriction: `HandoffXIter.iteration_generalNX`, §10.12. |
| `AnyTaintSim.startFact_any_demand`, `DB_any_premise_demand`, `seed_any_normal` | THE BACKWARD ANY TAIL (§9.2): every backward edge of an any-tail premise is a demand edge (under C3 and `BExact.SeedsConc`); the model keeps an `[any]` sink seed within the field limit as a normal `.any` edge, so the backward W6 is argued (§11.2). |
| `AnyTaintSim.backRecT`, `backRecT_sub`, `backRec_exact`, `backRec_exactM`, `backRec_flow`, `recsDR_liftRecs` | THE BACKWARD RECORDS (§8.7 R1): a normal backward summary with a non-zero premise and no any tail, reversed, is an exact forward record (the hypotheses of `BExact.revRecs_exact`); a forward run that reads such records has the facts of `DR`. |
| `AnyTaintSim.revSummaryDemandT_iff`, `backward_reads_sameT`, `revSummaryDemand6T_iff` | ROUND 1, THE FORWARD LABEL: the backward run read the same patterns from `AnyTaint.DRT` as from `DR`, and from `AnyTaint.D6T` as from `D`: the forward must flags were a label for the hand-off (with the emission of §6.3, which reads no pattern layer, the reason for W8 (d)). |
| `AnyTaintSim.runSeqT`, `iteration_generalT`, `iteration_reportsT`, `runSeqSrcT`, `iteration_srcT` | ROUND 1: the iteration with run 1 `AnyTaint.D6T` and the forward restricted runs `AnyTaint.DRT`. |

THE CONJUNCTION (`AnyTaintND`, the rule of §4.6 for an `[any-taint]` input; `ap-history.md` F69). The closure
`AnyTaintND.DNzT` has the conjunction rule but neither W6T nor the exclusion: with them the rule is argued (§11.2).

| Theorem | Statement |
|---|---|
| `AnyTaintND.conjLayerT`, `DNzT`, `dnz_to_dnzT`, `dnzT_to_dnz`, `conj_results_corr` | The rule of §4.6: a normal `[any-taint]` input that overlaps its literal keeps the result normal. `AnyTaintND.DNzT` (`NDZ.DNz` with `AnyTaintND.conjLayerT`) has the facts of `NDZ.DNz`, each edge in the same or a lower layer. |
| `AnyTaintND.nd_coverage_zT`, `nd_coverage_single_zT`, `nd_coverage_zgT`, `nd_vuln_found_zT`, `nd_vuln_reach_zT`, `nd_vuln_found_zgT` | Coverage and the vulnerability theorems of `NDZeroThms.lean` for `AnyTaintND.DNzT`. |
| `AnyTaintND.lit_loc`, `nd_edgeOKT`, `nd_edge_exact_genT`, `nd_edge_exact_zT`, `nd_edge_exact_valid_zT` | EXACTNESS of a normal `AnyTaintND.DNzT` edge against `ND.TaintN`, under the hypotheses of `NDZeroThms.nd_edge_exact_z` and `nd_edge_exact_valid_z`. The new case (`AnyTaintND.lit_loc`): an `[any-taint]` input that overlaps its literal and passes the mark gate has a location in the literal. |
| `AnyTaintND.ConfirmedNzT`, `confirmed_real_NzT`, `confirmed_real_NzT_valid_of`, `confirmed_real_NzT_valid`, `confirmedNz_confirmedNzT` | CONFIRMATION with a normal sink edge (also `[any-taint]`), under the hypotheses of `NDZeroThms.confirmed_real_Nz`, `confirmed_real_Nz_valid`; every vulnerability that the old rule confirms, the new rule confirms. |
| `AnyTaintND.Example.layer_new`, `layer_old`, `c3`, `vuln3`, `confirmed`, `real`, `old_not_confirmed` | `x = srcAny(); y = src();` and the conjunction `(x, .f, $, T) ∧ (y, ., $, U) → (z, ., $, V)`: the result is normal with the new rule and demand with the old one; the vulnerability is confirmed and real; the old rule does not confirm it. W6T is not part of `DNzT` (argued, §11.2). |

THE WORKED PROGRAMS OF ROUND 2 (`AnyTaintExCases`: derivations and complete runs in `AnyTaintEx.D6X` and
`AnyTaintEx.DRXs`, the earlier restriction; on run 3 of program B the intersection gives the same cells, checked by
hand) AND THEIR VECTORS:

| Theorem | Statement |
|---|---|
| `AnyTaintExCases.S.record_app`, `keep_forms`, `run1_record`, `run1_dto_ann`, `run1_name_no_trigger`, `run1_name_not_reported`, `run1_email_normal`, `run1_email_confirmed`, `run1_no_demand`, `name_not_real`, `email_real`; `inv1T`, `run1T_vulns`, `run1T_no_normal`, `run1T_not_confirmed`, `refines_dto` | PROGRAM S (the setter): `root() { dto = srcAny(); dto.setName(c); sink(dto.name); sink(dto.email); }`, `setName(n) { this.name = n; }`. The run-1 record `(this, ., *) → (this, ., */{name})` of `setName` on the added fact `(this, ., [any-taint], T)` gives `(dto, ., [any-taint], {name}, T)` in the NORMAL layer. `sink(dto.name)` is not reported (no sink edge triggers it; it is not real), and `sink(dto.email)` is CONFIRMED in run 1; run 1 has no demand report. For contrast, the round-1 rule (`AnyTaint.D6T`) reports both sinks in the demand layer only. |
| `AnyTaintExCases.SD.run1_deep_record`, `run1_dto_ann`, `run1_name_not_reported`, `run1_email_confirmed`, `same_result` | PROGRAM SD (the setter one call deeper): the exclusion goes through the `*/{name}` record of the outer callee; the results in `root` are those of S. |
| `AnyTaintExCases.B.run1_d_ann`, `run1_e_ann`, `run1_name_not_reported`, `run1_anyE_confirmed`, `recs1_complete`, `inv3`, `must_summary_ops`, `run3_must`, `run3_summary`, `run3_d_ann`, `run3_e_ann`, `run3_name_not_reported`, `run3_anyE_confirmed`, `run3_with_records` | PROGRAM B (the broad demand): `root1() { d = srcAny(); d.setName(c); sink(d.name); }`, `root2() { e = srcAny(); e.setName(c); sinkAny(e); }`. Run 1: `sink(d.name)` is not reported, `sinkAny(e)` is confirmed. Run 3 with the broad demand `((this, ., [any], T), (this, ., [any], T))` of `setName` (written by hand): the must-premise `(this, ., [any-taint], {}, T)` and its NORMAL summary `→ (this, ., [any-taint], {name}, T)`; `sink(d.name)` is still not reported, and `sinkAny(e)` is confirmed; also with every record set inside the run-1 records. |
| `AnyTaintExCases.X.two_results`, `locations_exact`, `run1_results`, `fg_not_reported`, `fh_confirmed`, `k_confirmed`, `run1_no_demand` | PROGRAM X (a two-level write in ONE statement, an AP-level program: on the JVM the write goes through a local, §13 item 16): `x = srcAny(); x.f.g = c; sink(x.f.g); sink(x.f.h); sink(x.k)`. The write gives `(x, ., [any-taint], {f}, T)` and `(x, .f, [any-taint], {g}, T)`, both normal, which cover exactly the locations that are not at or below `x.f.g`; `sink(x.f.g)` is not reported, the two other sinks are confirmed. |
| `AnyTaintExCases.R.reads`, `no_y`, `run1_z`, `y_not_reported`, `z_confirmed` | PROGRAM R (the reads): after the setter of S, `y = dto.name` gives nothing (`name` is excluded) and `z = dto.email` gives `(z, ., [any-taint], {}, T)`, normal; `sinkAny(y)` is not reported, `sinkAny(z)` is confirmed. |
| `AnyTaintExCases.CL.clean_vectors`, `atAndBelow_result`, `below_result`, `exact_result` | PROGRAM CL (the cleaners at `x.f` on `(x, ., [any-taint], T)`): `atAndBelow` gives `(x, ., [any-taint], {f}, T)`; `below` gives it and `(x, .f, $, T)`, all normal; `exact` gives `(x, ., [any], T)` in the demand layer (every sink is a demand entry, also the cleaned `sink(x.f)`). |
| `AnyTaintExCases.CUT.cut_ops`, `run1_cut`, `cut_reports` | PROGRAM CUT (program X with the field limit 0, an AP-level program: no run has `L = 0`, §4.4): the cut gives `(x, ., [any], T)` in the demand layer and drops the exclusion `{g}`; `sink(x.f.h)` is a demand entry only. |
| `AnyTaintEx.Vec.setter_keep`, `setter_keep_base`, `read_excluded`, `read_admitted`, `above_star_excl`, `source_any_target`, `clean_atAndBelow`, `clean_below`, `clean_exact`, `clean_excluded`, `below_new_fact`, `cut_drops`, `emit_at`, `emit_above_excluded`, `emit_above_exact`, `emit_below`, `start_must`, `sat_vectors`, `summary_ann`, `restrict_vectors`, `check_vectors`, `below_keeps`, `below_keeps_loc` | THE VECTORS of the rows of W8 (`decide`): the keep edge (normal with the exclusion; the round-1 rule gave demand), the reads, the case `above` with an edge exclusion, a source, the cleaners, the cut, the emission, the start, the satisfaction, the summary, the restriction, the sink check, the case `below`. |

THE ROUND-1 PROGRAMS IN THE SPEC CLOSURES (`AnyTaintExCases2`: the programs `AnyTaintCases.G.prog`, `C.prog`,
`I.prog`, `PassRule.prog` of round 1, re-derived in `AnyTaintEx.D6X` and `AnyTaintEx.DRXs`). These are the results
that this spec states for G, C, I and P. Run 3 of G and C uses the earlier restriction and the earlier hand-off; with
the intersection and the hand-off of the demand edges the same results are checked by hand (§11.2). None of these
programs has an exclusion edge, a cleaner or a type filter, so
the refined runs make no annotation and give the round-1 objects with the Empty exclusion:

| Theorem | Statement |
|---|---|
| `AnyTaintExCases2.G.inv1`, `run1_flow_above`, `run1_vuln`, `run1_no_normal`, `run1_not_confirmed`, `run1_forgets`, `run1_forget_eq`, `revDemX_bound`, `revDemX_get`, `HX_exact`, `handoffX_get`, `r3_eJ1`, `run3_must`, `run3_must_supported`, `run3_sink_normal`, `run3_vuln_normal`, `run3_confirmed`, `run3_confirmed_handoff` | PROGRAM G (the getter): the complete run 1 (`AnyTaintExCases2.G.inv1`, in `AnyTaintEx.D6X`) has the FLOW summary `(p, ., *) → (ret, ., [any], *)` of `get` in the demand layer (the case `above`), so its only report is DEMAND, not `AnyTaintEx.Confirmed6X`. `AnyTaintExCov.forget6` of the refined run 1 is the round-1 run 1, so the backward run hands off exactly the demand `((p, .f, [any], T), (ret, ., [any], T))` of `get` and the zero demand (`AnyTaintExCases2.G.HX_exact`, `handoffX_get`; no added hypothesis). Run 3 (`AnyTaintEx.DRXs`) with this demand emits the must-premise `(p, .f, [any-taint], {}, T)`, which is supported (`AnyTaintEx.SupX`); its summary `→ (ret, ., [any-taint], {}, T)` is normal (`AnyTaintExCases2.G.r3_eJ1`), the sink edge in `root` is normal, and the vulnerability is `AnyTaintEx.ConfirmedX` for every record set, also with the derived hand-off. |
| `AnyTaintExCases2.C.run3_must`, `run3_sink_normal`, `run3_vuln_normal`, `run3_supported`, `run3_confirmed`, `run3_confirmed_handoff` | PROGRAM C (the sink in the callee): run 3 with the demand `((o, .f, [any], T), none)` of `use` emits the must-premise `(o, .f, [any-taint], {}, T)`; its start fact is the normal sink edge; it is supported through the must branch of `AnyTaintEx.SupLinkX` (inside the normal added fact `(o, ., [any-taint], {}, T)`, with the same mark); `AnyTaintEx.ConfirmedX`, also with the hand-off of the backward run (`AnyTaintCases.C.handoff_use`). |
| `AnyTaintExCases2.I.inv1`, `run1_flow`, `app_normal`, `run1_sink_normal`, `run1_vuln_normal`, `run1_confirmed`, `run1_no_demand` | PROGRAM I (the identity callee): the FLOW summary `(p, ., *) → (ret, ., *)` of `id` is normal; its application is a `keep` row of `AnyTaintEx.annX` with the Empty exclusion and keeps the normal layer; the sink edge is normal, and run 1 confirms the vulnerability (`AnyTaintEx.Confirmed6X`), with no demand report. |
| `AnyTaintExCases2.PassRule.source_vs_pass`, `source_normal`, `source_confirmed`, `pass_demand`, `invPass`, `pass_not_confirmed` | PROGRAM P: the micro edge `P.$ (T) → Q.[any] (T)` as a source gives `(Q, ., [any-taint], {}, T)`, normal, confirmed in run 1; as a pass rule it gives `(Q, ., [any], T)` in the demand layer, and the complete run reports demand only (not `AnyTaintEx.Confirmed6X`). |
| `AnyTaintExCases2.Carry.EdgeFree`, `ExclFreeProg`, `NoClean`, `SumFree`, `SumFreeR`, `RecsLift`, `RecsFree`, `d6x_iff_d6t`, `forget6_d6x`, `sup6x_iff`, `confirmed6x_iff`, `drx_iff_drt`, `supX_iff`, `confirmedX_iff`, `dollar_premise_annotates`; `AnyTaintExCases2.G.run1_carry`, `run1_not_confirmed_carry`; `AnyTaintExCases2.I.run1_carry`, `run1_confirmed_carry`; `AnyTaintExCases2.PassRule.run1_carry`, `confirmed_carry` | THE CARRY-OVER (the conditions `AnyTaintExCases2.Carry.EdgeFree`, `ExclFreeProg`, `NoClean`, `SumFree`, `SumFreeR`, `RecsLift`, `RecsFree`): with no exclusion edge (a `$` premise with a `*` target counts as one, because it gives an annotation, `AnyTaintExCases2.Carry.dollar_premise_annotates`), no cleaner and free summaries, `AnyTaintEx.D6X` is `AnyTaint.D6T` with the Empty exclusions, and `AnyTaintEx.Confirmed6X` is `AnyTaint.ConfirmedT6`; for a restricted run, also under the record conditions, `AnyTaintEx.DRXs` is the spec instance of `AnyTaint.DRT`, and `AnyTaintEx.ConfirmedX` is `AnyTaint.ConfirmedT`. Run 1 of G, I and P by this carry-over. |

THE WORKED PROGRAMS OF ROUND 1 (`AnyTaintCases`, in `AnyTaint.D6T` and `AnyTaint.DRT`): the model of the first F69
text. The results that this spec states for G, C, I and P are the theorems of `AnyTaintExCases2` (above); the rows
below are their round-1 derivations and the contrast with the old rule W6. W is the program of the demotion that the
exclusion replaces (its counterexample rows stay, above):

| Theorem | Statement |
|---|---|
| `AnyTaintCases.I.run1T_flow`, `app_normal`, `run1T_sink_normal`, `run1T_confirmed`, `run1T_no_demand`, `vuln_real`, `run1W6_vuln`, `run1W6_no_normal` | PROGRAM I (the identity callee): `root() { dto = srcAny(); x = id(dto); sinkAny(x); }`, `id(p) { return p; }`: the FLOW summary of `id` keeps the whole object, so run 1 CONFIRMS; with the old rule W6 the vulnerability is demand only. |
| `AnyTaintCases.G.wf`, `bindNoAny`, `taintConc`, `run1W6_vuln`, `run1W6_no_normal`, `run3W6_vuln`, `run3W6_no_normal`, `run1T_flow_above`, `run1T_vuln`, `run1T_no_normal`, `run1T_not_confirmed`, `handoff_exact`, `handoff_get`, `t3_eJ1`, `run3T_must`, `run3T_must_supported`, `run3T_sink_normal`, `run3T_vuln_normal`, `run3T_confirmed`, `run3T_confirmed_handoff`, `vuln_real` | PROGRAM G (the getter): `root() { dto = srcAny(); x = get(dto); sinkAny(x); }`, `get(p) { return p.f; }`. With the old rule W6 the vulnerability is demand in run 1 and in run 3 (`run3W6_no_normal` for every record set inside the complete run-1 records, `recs1W_complete`). With W6T run 1 still has only a demand sink edge (the FLOW summary of `get` is the case `above`). Backward run 2 hands off exactly the demand `((p, .f, [any], T), (ret, ., [any], T))` of `get` and the zero demand. Forward run 3 emits the must-premise `(p, .f, [any-taint], T)`, its sink edge is normal, and the vulnerability is CONFIRMED and real. |
| `AnyTaintCases.C.handoff_use`, `run3_must`, `run3_sink_normal`, `run3_supported`, `run3_confirmed`, `run3_confirmed_handoff`, `vuln_real` | PROGRAM C (the sink in the callee): `root() { dto = srcAny(); use(dto); }`, `use(o) { sinkAny(o.f); }`: run 3 confirms it through the supported must-premise `(o, .f, [any-taint], T)`. |
| `AnyTaintCases.W.keep_demand`, `run1_vuln_demand`, `run1_not_confirmed`, `run3_vuln_demand`, `run3_not_confirmed`, `vuln_not_real`, `keep_normal_false`, `keep_normal_not_endExact`, `keep_normal_confirms_unreal` | PROGRAM W (the strong write): `dto = srcAny(); dto.f = cl; sink(dto.f)`. The round-1 rule made `(dto, ., [any], T)` in the demand layer, so the vulnerability was reported and not confirmed; it is not real, and a normal result WITHOUT the exclusion would confirm it. The exclusion replaces the demotion: the keep edge gives `(dto, ., [any-taint], {f}, T)`, and `sink(dto.f)` is not reported (as `AnyTaintExCases.X.fg_not_reported`). |
| `AnyTaintCases.PassRule.source_vs_pass`, `source_normal`, `source_confirmed`, `pass_demand`, `pass_not_confirmed` | PROGRAM P: the micro edge `P.$ (T) → Q.[any] (T)` as a source (a taint edge: normal, confirmed in run 1) and as a pass rule (a may: demand, not confirmed). |
| `AnyTaintCases.Cut.cut_transfer`, `limitF_cut_demand` | THE CUT (§4.4): an `[any-taint]` fact over the field limit becomes `[any]` in the demand layer. |
| `AnyTaint.EmitVec`, `AnyTaint.Sanity` | The vectors of round 1: every cell of the emission table of §6.3 without the exclusion and the rows `below` and `above` (`decide`); a source result is a normal `[any-taint]` edge of `D6T` and of `DRT`, and the same micro edge as a pass rule is demand. |

THE PIPELINE (`analyzer-core.md` §12):

| Theorem | Statement |
|---|---|
| `PipelineAnyTaintEx.sysD6X`, `sysDRX`, `sysD6X_wf`, `sysDRX_wf`, `clD6X_iff`, `clDRX_iff`, `clD6X_link`, `clD6X_sub`, `clD6X_pub`, `clDRX_link`, `clDRX_sub`, `clDRX_pub` | The closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX` as pipeline systems. A link carries the added fact with its flag and its exclusion; a publication carries the callee premise with its flag and its exclusion (the premise keys of §7.1). |
| `PipelineAnyTaintEx.known_D6X`, `known_DRX`, `result_D6X`, `result_DRX`, `result_DRXs`, `no_lost_summary_D6X`, `no_lost_summary_DRX` | At a reachable quiescent state the processed objects are exactly the closure (`Pipeline.quiescent_exact`); a summary edge is never lost. No instance of `Pipeline.quiescent_dominates` (argued, as for `PipelineAP`). |
| `PipelineAnyTaintExDriver.driver_iterationX`, `driver_iteration_uptoX`, `driver_iteration_srcX`, `resultSeqX`, `resultSeqX_runSeqX`, `resultSeqX_runSeqSrcX`, `vuln_sink_D6X`, `vuln_sink_DRX`, `runSeqX_congr` | THE DRIVER: if every run is complete and the driver computes the hand-offs of `analyzer-core.md` §7.3, §7.4 (each forward run read with the exclusions and the must flags dropped), every forward run reports every real vulnerability, in some layer. No new hypothesis: those of `PipelineAnyTaintDriver.driver_iterationT` with `PipelineAnyTaintEx.sysD6X` and `sysDRX` (with the source seeds those of `PipelineSeeds.driver_iteration_src`). There is no analog of `PipelineAnyTaintDriver.handoff_sameT`: the refined hand-off can be smaller (`AnyTaintExCov.CexRoute.route_a_false`). (The earlier hand-off; the driver of the spec hand-off is `PipelineHandoffDriver.driver_iterationNX`, with every reported vulnerability seeded, and `PipelineHandoffDriverExt.driver_iterationNX_demand`, with the seeds of the DEMAND entries only, §10.12.) |
| `PipelineAnyTaint.sysD6T`, `sysDRT`, `clD6T_iff`, `clDRT_iff`, `result_D6T`, `result_DRT`; `PipelineAnyTaintDriver.driver_iterationT`, `driver_iteration_uptoT`, `driver_iteration_srcT`, `handoff_sameT` | ROUND 1: the same for `AnyTaint.D6T` and `AnyTaint.DRT`; there the driver handed on the same backward demand as from `DR` (the pattern tail was a label). |

### 10.12 The hand-off of the demand edges — `Handoff*.lean`, `PipelineHandoffDriver*.lean`

The model of decision F70 (§6.4, §6.6, §8.5, §8.7 R5, §9.2; `ap-history.md` F70), with the mark-aware restriction of
decision F71 (§3.2, §6.3, §6.4; `ap-history.md` F71). `HandoffDefs.lean` (namespace
`Handoff`) has the definitions: the restriction as an intersection `Handoff.restrictI`, mark-aware (the premise test
`insideB`: the location part `insideLocB` and the mark part `markSubB`; the mark test of the conclusion `concMarkB`;
the conclusion `restrictConcI`, the meet `meetConcK`); the crossable records `CrossK`, `Cross`, the reversed record
`revRec` and the crossable backward leaf `CrossB` (normal, with a crossable reversal; `revRec` itself gives the normal
layer, so `CrossB` tests the layer of the backward leaf); the publications `Pub`, `pubD` (run 1) and `pubR` (a restricted run); the two hand-offs `handF` (forward to
backward) and `demOfN` (backward to forward); the input witness of a forward run `FlowRR`, `ReachRR` (every call that
returns is demanded, the exit location in `D-p` with its mark, or recorded) and its output witness `FlowRDN`, `ReachRDN` (every call that returns is justified by
a published piece or a record); the forward contract `CoversN` and the backward contract `BackwardContractN`. The spec
runs of the base model are `D` with `policy1` (run 1), `DR` with `emitM`, `satI`, `Handoff.restrictI` (a forward
restricted run) and `Backward.DB` with `emitM`, `satI`, `Handoff.restrictI` (the backward run). With the `[any-taint]` tail and its
exclusion they are `AnyTaintEx.D6X`, `AnyTaintEx.DRX` with `emitX`, `satX`, `HandoffX.restrictIX` (read without the
exclusions, `AnyTaintExCov.forget6`, `forgetX`), and `Backward.DB`. The earlier restriction and hand-off stay in the
model as the record of the earlier design (§10.7, §10.11). EVERY THEOREM OF THIS SECTION IS ABOUT THE CONCRETE
RESTRICTED RUNS of F70 and F71 (the emission `emitM`, the hand-offs without the normalization of F72). For the rules
of F72 (§4.3, §4.5, §6.3, §9.2) they are NOT YET PROVED; the model of F72 is the pending task of §11.2, and the
theorems below whose claim is false for the F72 runs are named there.

THE RESTRICTION (`HandoffRestrict.lean`, namespace `Handoff`):

| Theorem | Statement |
|---|---|
| `restrictI_sub` | The restriction only removes pairs and keeps the layer (`RestrictSub restrictI`). |
| `restrictI_contract` | C5 (§6.1), MARK-AWARE (F71): for a premise inside `D-c` in its locations and its marks (`insideB`), a pair of the edge whose exit location `D-p` covers WITH ITS MARK (`p.covers l2`) stays, in the same layer; every cell, also a `*` conclusion, and every mark cell. (Changed in F71: the hypotheses were `insideLocB` and `p.coversLoc l2`.) |
| `restrictI_contract_loc_false` | CEGAR (F71): the location form of C5 (`insideLocB`, `p.coversLoc l2`, the marks ignored) is FALSE for the mark-aware restriction: the example of F71 (§6.4) has a pair whose exit location lies in the locations of `D-p`, but not in its marks, and no result. |
| `RAux.concMarkB_of_den`, `RAux.concMarkB_conc`, `RAux.concMarkB_conc_admits`, `RAux.markMatchB_conc`, `RAux.mark_conc_or_abs` | The mark helpers (F71): a pair whose exit mark `D-p` admits passes the mark test of the conclusion (every mark cell); on a concrete mark the mark test and the emission test are `markSubB`; a mark is concrete or abstract (`Invariant.AbsMark`). |
| `insideB_loc`, `insideB_mark`, `insideB_intro`, `insideB_covers` | `insideB` is the location part and the mark part; every location of the premise, with its mark, is a location of the pattern. |
| `emitM_insideB`, `emitM_covers` | C2, the inside part with the marks (F71): an emitted premise of a CONCRETE added fact lies inside its entry pattern in its locations and its marks, and has the mark of the added fact. |
| `restrictI_someM`, `restrictConcI_mark`, `restrictI_exit_mark` | A result of `restrictI` has passed both mark tests; the restriction keeps the mark of the conclusion; the exit mark of a pair of a result is a mark of `D-p`, unless the conclusion mark is abstract. |
| `restrictI_interM`, `restrictI_inter_conc`; `Handoff.RVec.inter_exc_absmark` | THE INTERSECTION WITH THE MARKS (F71): every pair of a result has its entry location with its mark in `D-c`, and its exit location in `D-p` (except `RExc`) with a mark of `D-p` (except an abstract conclusion mark, the exception (c) of §6.4, which is real); for a concrete conclusion mark, the exit location with its mark in `D-p`, except `RExc`, where the exit mark is still a mark of `D-p`. |
| `restrictI_narrowM`, `restrictI_narrow_conc`, `handF_narrowM`, `handF_narrow_locM`, `demOfN_narrowM`, `handF_narrow_DRM`, `handF_narrow_DR_exactM` | THE NARROWING OF ONE RUN WITH THE MARKS (F71): as the location forms below, with `insideB`; a restricted forward run with `emitM` is concrete, so the mark exception does not occur (`handF_narrow_DRM`), and with no `*` exit pattern in its demand the narrowing is exact in the locations and the marks (`handF_narrow_DR_exactM`). |
| `restrictI_not_RestrictContract` | The earlier overlap form of C5 (`RestrictContract`) is FALSE for the intersection: a premise that only overlaps `D-c` has a demanded pair and no result. |
| `emitM_inside`, `insideLoc_coversLoc`, `emitM_coversLoc` | An emitted premise lies inside the entry pattern that emitted it, as locations; the location form. |
| `restrictI_inter`, `RExc`, `rexc_any_chain`; `Handoff.RVec.inter_exc_any`, `inter_exc_star`, `inter_exc_star_at` | THE INTERSECTION, the location form: every pair of a result has its entry location in `D-c` and its exit location in `D-p`, as locations, except the two cells of `RExc` (an `[any]` conclusion at or above a `*/E` exit pattern, the exit location then on the chain of `D-p`; a `*` conclusion); each exception is real. |
| `restrictConcI_cases`, `restrictI_some`, `restrictI_of`, `restrictConcI_sub`, `restrictConcI_exit`, `restrictConcI_inside`, `restrictI_narrow`, `restrictConcI_star` | The cells of the restriction (§6.4, the table and THE MEET). `restrictI_some` is the location form of `restrictI_someM`; `restrictI_of` takes `insideB` and the mark test of the conclusion (changed in F71: it took `insideLocB`). |
| `handF_narrow`, `handF_narrow_loc`, `demOfN_narrow` | THE NARROWING OF ONE RUN, the location form: a demand edge that a restricted run hands off lies inside the reversal of the demand pattern that published it, as locations (except `RExc`); the same for the backward hand-off with a non-zero premise. |
| `DR_exit_not_star`, `handF_narrow_DR`, `NoStarK`, `emitM_nonstar`, `DR_nonstar`, `restrictConcI_nonstar`, `handF_DR_nonstar`, `handF_narrow_DR_exact` | A restricted forward run with `emitM` has no `*` exit edge, so only the `[any]` exception occurs; with no `*` entry pattern in its demand it hands off no `*` pattern; with no `*` exit pattern in its demand the narrowing is exact. (False for the F72 runs: a FLOW premise has `*` exit edges, §6.4.) |
| `pubD_sub`, `pubR_sub` | A published piece has only pairs of its summary edge (both publications). |
| `star_meet_exact`, `tailExcl_admits_iff`, `meetConcKX`, `meetConcKX_tailF`, `meetConcKX_tailF_of`, `meetConcKX_exact` | A remark, not a spec rule: the exact meet of a `*` conclusion is representable (`*/(E ∪ tailExcl k)`); the spec keeps a `*` conclusion whole, because a restricted run of the concrete design has none. (Since F72 a restricted run has `*` conclusions; whether to use the exact meet is an open point, §11.2.) |
| `Handoff.RVec.v64_restrictI`, `v64_restrictU`, `vOverlap_overlapB`, `vOverlap_inside`, `vOverlap_restrictI`, `vOverlap_restrictU`, `vNoExit`, `row_base`, `row_at_any_exact`, `row_at_any_any`, `row_at_any_star`, `row_at_exact_exact`, `row_at_exact_any`, `row_at_exact_star`, `row_at_star_exact`, `row_at_star_any`, `row_at_star_star`, `row_below_any`, `row_below_star_adm`, `row_below_starc`, `row_below_exact`, `row_below_star_excl`, `row_above_any_exact`, `row_above_any_any`, `row_above_any_star`, `row_above_star_adm`, `row_above_star_excl`, `row_above_exact`, `row_apart` | THE VECTORS (`decide`) of §6.4: the example `[any]` against `$` gives `$` (the earlier restriction kept `[any]`), a premise that only overlaps `D-c` gives nothing (the earlier restriction gave a result), no `D-p` gives nothing, and every row and every meet cell of `restrictConcI`. |
| `Handoff.RVec.vMark_user_inside`, `vMark_user_concMark`, `vMark_user_restrictI`, `vMark_user_restrictU`, `vMark_user_loc`, `vMark_user_same`, `vMark_prem_loc`, `vMark_prem_inside`, `vMark_prem_restrictI`, `vMark_inStarEx_T`, `vMark_inStarEx_U`, `vMark_outStarEx_T`, `vMark_outStarEx_U` | THE MARK VECTORS (`decide`) of §6.4 (F71): the example of F71 (`(x, ., $, T) → (ret, .f, $, T)` against `D-p = (ret, .f, $, U)`) gives nothing, the earlier restriction and the location-only test keep it, and `D-p = (ret, .f, $, T)` keeps it; a premise mark that `D-c` does not admit gives nothing; the `*∖X` cells on the entry side and on the exit side. |
| `Handoff.RVec.vEmit_starEx_T`, `vEmit_starEx_T_pre70`, `vEmit_starEx_U`, `vEmit_abstract`, `markMatchB70`, `emitM70` | THE EMISSION VECTORS (`decide`) of §6.3 (F71): a `*∖{T}` entry pattern emits nothing for an added fact with the mark `T`, and the emission before F71 (`emitM70`, with the old test `markMatchB70`, where `*∖X` counts as `*`) emitted the premise; an added fact with the mark `U` gives a premise inside the entry pattern with its mark; a remark: on an abstract added fact the emission test is looser than `markSubB`, so `emitM_insideB` needs a concrete added fact. (The suffix `70` names the state before F71.) |

THE COVERAGE (`HandoffCoverage.lean`, namespace `Handoff`):

| Theorem | Statement |
|---|---|
| `cross_applies` | A crossable premise (`$`, or `*` with the Empty exclusion) that has a common location with a concrete added fact is satisfied by it (`satI`) or covers it (`applicable`): the record applies (rule `retRec`). (For an abstract added fact, F72: a `*` crossable premise applies too, a concrete one does not, §8.7 R4; argued, PENDING.) |
| `coverageRN` | THE COVERAGE THEOREM of `DR … emitM satI restrictI rc …` for a demanded-or-recorded flow (`FlowRR`): an edge of the initial fact covers the pair, and the run justifies the flow (`FlowRDN … (pubR dem) rc`). A demanded call uses `emitM_insideB` (the premise inside `D-c` with its mark; the added fact is concrete) and `restrictI_contract` (with the exit location in `D-p` with its mark, from `FlowRR`); a recorded call uses `cross_applies`. No request branch: the run is concrete. (No statement change in F71. The concrete design; the F72 coverage with modes is the lemma L1 of §11.2, PENDING.) |
| `reach_strongRN`, `coversN_DR` | The same for a vulnerability witness; THE FORWARD CONTRACT `CoversN` of the restricted run, under `P.WF` only. |
| `run1_reachRDN`, `run1_justifies` | Run 1 (`D … policy1 …`, the publication `pubD`, no record) justifies every real witness and reports its vulnerability. |
| `added_concN`, `no_reqN`, `flowRD_flowRDN`, `reachRD_reachRDN`, `policy1_applicable`, `Handoff.RAux.markSubB_of_conc` | Helpers. |

THE BACKWARD RUN (`HandoffBackward.lean`, namespace `HandoffBackward`):

| Theorem | Statement |
|---|---|
| `cross_step` | The backward run crosses a call by the reversal `Handoff.revRec (j, g)` of a crossable record (rule `retRec`). |
| `seg_genN`, `reach_of_db_genN`, `demanded_genN` | A justified flow (`Handoff.FlowRDN`) and a concrete backward edge give the backward edge at the forward entry, and the flow is demanded or recorded in the next forward run (`Handoff.FlowRR` with the demand `Handoff.demOfN` and the records `rcnext`). At a call: a crossable exit edge or record gives a recorded call; a non-crossable exit edge gives a demand edge of `handF`, then a demanded call (`demOfN` case 3) or, if the backward leaf is crossable (`Handoff.CrossB`), a recorded call. The demanded call has the exit location in `D-p` WITH ITS MARK: the emitted backward premise lies inside its `D-c` with its mark (the requirement is concrete) and covers the exit location with its mark (F71; no statement change). |
| `NextRecs` | The records of the next forward run: the records that the forward run read, its crossable exit edges, and the reversals of the crossable backward exit edges (`Handoff.CrossB`) with a non-zero premise. |
| `B_generalN` | THE BACKWARD CONTRACT `Handoff.BackwardContractN` of `Backward.DB (Program.rev P) … demB emitM satI restrictI recsB …`, under `P.WF`, S11 (a) to (f) (`Reverse.BindTargetsStar`, `Backward.StmtsMarkRev`, `Backward.NoZeroBack`, `Backward.ZeroKept`, `Backward.ExitReach`, sink tails `$` or `[any]`), with `Handoff.handF ⊆ demB`, the reversed crossable records in `recsB`, every publication only removing pairs, and `NextRecs`. |
| `recsBOf`, `recsBOf_spec`, `rcNextOf`, `rcNextOf_spec`, `rcNextOf_cross`, `B_generalN_canon` | The canonical record sets and the contract for the canonical backward run (demand `Handoff.handF`, records `HandoffBackward.recsBOf`). |
| `zero_initN`, `zero_atN`, `cross_em`, `crossB_em`, `crossK_em`, `markRev_em`, `emitM_inside_B`, `emitM_insideB_B`, `concMarkB_of_den_B`, `cross_applies_B`, `restrictI_contract_B` | Helpers; `cross_em`, `crossB_em`: `Cross` and `CrossB` are decidable in constructive logic; `emitM_insideB_B`, `concMarkB_of_den_B` are local copies of the mark lemmas of F71; `restrictI_contract_B` is the local copy of `Handoff.restrictI_contract` (with `insideB` and `p.covers l2` since F71). |

THE ITERATION (`HandoffIter.lean`, namespace `HandoffIter`; `HandoffMain.lean`, namespace `HandoffMain`):

| Theorem | Statement |
|---|---|
| `HandoffIter.Run0Contract`, `iteration_invariantN` | Run 1 justifies and reports every real witness; the strengthened induction (the witness stays justified). |
| `HandoffIter.iteration_abstract_or` | THE ABSTRACT ITERATION: for any run sequence whose run 1 satisfies `HandoffIter.Run0Contract`, whose forward runs satisfy `Handoff.CoversN` and whose backward steps satisfy `Handoff.BackwardContractN`, and in which every reported vulnerability of run `k` is confirmed (`C k`, any predicate) or seeded: every real vulnerability is, at every forward run `k`, reported by run `k` or confirmed by an earlier run. |
| `HandoffIter.iteration_abstract`, `iteration_invariant_neg`, `iteration_abstract_neg`, `iteration_all_seeded` | The form "not confirmed ⇒ seeded" with a decidable `C`; the form with no decidable `C` and the conclusion "no earlier run confirmed it ⇒ run `k` reports it"; the corollary `C = False`. |
| `HandoffMain.canonState`, `backOf`, `rcOf`, `stepState`, `state0`, `canon_pubSub`, `canon_run0`, `canon_covers`, `canon_backward` | THE CANONICAL RUN SEQUENCE of the spec rules (forward runs only: state `k` is run `2k + 1`), and its four ingredients. |
| `HandoffMain.iteration_generalN` | THE ITERATION THEOREM (§6.6): on the canonical sequence, under the hypotheses of `HandoffBackward.B_generalN`, if every reported vulnerability is confirmed (`C k`) or seeded, every real vulnerability is, at every forward run, reported by that run or confirmed by an earlier one. |
| `HandoffMain.iteration_generalN_all` | With every reported vulnerability seeded, every forward run reports every real vulnerability. |
| `HandoffMain.iteration_generalN_incl`, `runSeqN`, `pubSeqN`, `pubSeqN_sub`, `flowRR_mono`, `reachRR_mono`, `flowRDN_mono_rc`, `reachRDN_mono_rc` | The inclusion form: the driver may hand off more demand edges and give more records (a larger backward demand, more backward records, a larger forward demand, any first record set). |

THE EXCLUSION AND THE NARROWING (`HandoffExclusion.lean`, namespace `HandoffExclusion`; `HandoffMain.lean`):

| Theorem | Statement |
|---|---|
| `HandoffExclusion.NoZeroGenP`, `Reaches` | The program conditions on the zero base (the conditions of `NDZeroBase.NoZeroGen` on a `Program`); the call subtree of a method. |
| `HandoffExclusion.zinv_all`, `exclusion_backward`, `exclusion_backward_nodem`, `init_zero_nodem` | In a call-closed method set with no seed, every zero-premise backward edge has the zero fact; a method with only the zero fact as an initial fact (or with no demand) and no seed in its call subtree has only the edge `zero → zero` in the backward run. |
| `HandoffExclusion.exclusion_demand`, `emitM_zero_din`, `forward_zero_init`, `forward_zero_edges`, `exclusion_theorem` | Then `Handoff.demOfN` gives it only the zero pattern, and the next forward run has only the zero fact as an initial fact of it and only zero-premise edges in it. |
| `HandoffExclusion.exclusion_round` | ONE ROUND: a method key with no non-crossable exit edge in forward run `k` and no seed in its call subtree is analysed only from the zero fact in the next forward run (for every backward demand inside `handF`). |
| `HandoffMain.exclusion_canon` | THE EXCLUSION on the canonical sequence (§6.6), under `HandoffExclusion.NoZeroGenP`, no cleaner on the zero base and concrete seeds. |
| `HandoffMain.narrowing_canon_fwd`, `narrowing_canon_back` | The narrowing of each hand-off on the canonical sequence, as locations (forward: only the `[any]` cell of `Handoff.RExc`; backward: `Handoff.RExc`). |
| `HandoffMain.narrowing_canon_fwdM`, `narrowing_canon_backM` | The same in the locations AND the marks (F71; `Handoff.insideB`, the backward form for concrete seeds `BExact.SeedsConc`): the runs are concrete, so in the cells of `Handoff.RExc` the marks still narrow. |
| `HandoffMain.narrowing_canon`, `narrowing_canon_loc` | The narrowing with the exception cells: every demand pattern of forward run `k + 2` (Lean numbering) is the zero demand, a zero-premise backward pattern, or lies inside a demand pattern of forward run `k + 1` of the same method, as locations (entry inside entry, exit inside exit), except the cells of `Handoff.RExc`. The exceptions of `HandoffMain.narrowing_canon_loc` do not name the edge (`HandoffNoStar.base_loc_exception_weak`); the narrowing theorem of §6.6 is the exact form `HandoffNoStar.narrowing_canon_loc_exactM` (below). |
| `HandoffMain.narrowing_canonM`, `narrowing_canon_locM` | The same in the locations AND the marks (F71; `Handoff.insideB`, `PFact.covers`), for concrete seeds; in the cells of `Handoff.RExc` the marks still narrow. |

THE WORKED PROGRAMS AND THE CEGAR OF `Cross` (`HandoffCases.lean`, namespace `HandoffCases`, sub-namespaces `Wrap`,
`VecCross`, `AnyW`, `AnyM`, `Getter`):

| Theorem | Statement |
|---|---|
| `HandoffCases.crossK_iff`, `markRev_iff`, `cross_iff`, `restrictI_none` | `Cross` as a Boolean test (`decide`); no `D-p`, no result. |
| `HandoffCases.Wrap.inv_w1`, `w1_exit_cross`, `w1_wrap_exits_cross`, `w1_vuln`, `seedsW_exact`, `w1_wrap_normal` | PROGRAM WRAP (§6.6), run 1: the exit edge of `wrap` is the complete summary `(arg, ., *) → (ret, .f, *)`, and it is crossable; `wrap` has no demand-layer edge. |
| `HandoffCases.Wrap.old_b2_wrap_init`, `old_dem_w`, `inv_bo`, `old_demOf_exact`, `old_f3_wrap_init`, `old_f3_wrap_cut`, `old_f3_found` | THE EARLIER HAND-OFF: backward run 2 enters `wrap` with a non-zero premise and hands off a demand pattern of `wrap`; forward run 3 emits a non-zero fact into `wrap` and cuts INSIDE `wrap`, for every record set; it reports the vulnerability. |
| `HandoffCases.Wrap.handF_w1_exact`, `inv_bn`, `bn_cross`, `bn_wrap_zero_only`, `bn_wrap_edges_zero`, `demN_exact`, `inv_fn`, `fn_wrap_zero_only`, `fn_wrap_edges_zero`, `fn_record_applicable`, `fn_cut_in_root`, `fn_found`, `fn_vuln_exact`, `wrap_reachRR`, `wrap_old_vs_new` | THE HAND-OFF OF THE DEMAND EDGES: run 1 hands off no demand edge of `wrap`; backward run 2 crosses `wrap` by the reversed record and has only the zero fact in it; `wrap` gets only the zero demand; forward run 3 analyses `wrap` only from the zero fact and reports the vulnerability through the record of `wrap`, applied in the root by `applicable`, with the cut in the root; the witness is demanded or recorded. `wrap_old_vs_new`: both parts in one statement. |
| `HandoffCases.revRec_any_premise`, `not_cross_of_any`, `dollar_blocked`, `any_record_blocks_dollar`, `coversB_exact_any`; `HandoffCases.VecCross.*` | CEGAR (i): an `[any]` conclusion has an `[any]` reversed premise, so the leaf is not crossable; a `$` requirement neither satisfies it nor is covered by it (an `[any]` requirement crosses it). |
| `HandoffCases.AnyW.cegar_cross_anyw`, `fl_lost`, `fs_found`, `bl_no_srcHit`, `bs_srcHit`, `a1_exit_crossL` | CEGAR (ii), program ANYW (`ret = anyTaint(arg)`, the source in the root, with the source seeds): a looser hand-off that reads only the forward conditions of `Cross` (`CrossL`, `handFL`) loses a real, seeded vulnerability; the hand-off with `Cross` keeps it. |
| `HandoffCases.AnyM.cegar_cross_anym`, `flm_lost`, `fsm_found` | CEGAR (ii'), program ANYM (the source in a callee, with no source seeds): the same loss. |
| `HandoffCases.Getter.g1_exit_demand`, `handF_g1_exact`, `revRec_g_cross`, `revRec_g_crossB`, `demG_exact`, `fg_getter_zero_only`, `fg_record_sat`, `fg_found` | A GETTER `ret = arg.f`: its run-1 summary is in the demand layer (the case `above`), so it is a demand edge; the normal backward summary has a crossable reversal, so the getter gets only the zero demand in forward run 3, which reports the vulnerability in the normal layer through the reversed record. |

WITH THE `[any-taint]` EXCLUSION (`HandoffXRestrict.lean`, `HandoffXCoverage.lean`, namespace `HandoffX`;
`HandoffXIter.lean`, namespace `HandoffXIter`; `PipelineHandoffDriver.lean`, namespace `PipelineHandoffDriver`):

| Theorem | Statement |
|---|---|
| `HandoffX.insideLocXB`, `insideXB`, `meetExX`, `chainExX`, `restrictConcIX`, `restrictIX` | THE RESTRICTION WITH THE EXCLUSION (§6.4): the premise test reads the exclusion of the premise (`insideLocXB`) and, since F71, its mark (`insideXB`: `insideLocXB` and `markSubB`), and the conclusion has the mark test `Handoff.concMarkB` (the same mark tests as `Handoff.restrictI`); the meet adds `E2` of a `*/E2` exit pattern to an `[any-taint]/E` conclusion; above a `*/E2` exit pattern an `[any-taint]/E` conclusion gives the chain `[any-taint]/E2`. |
| `HandoffX.insideXB_loc`, `insideXB_mark`, `insideXB_intro`, `insideXB_of_base`, `insideXB_sound`, `emitX_insideXB`, `restrictIX_someM`, `restrictConcIX_mark`, `restrictIX_of` | The mark-aware X premise test (F71): its two parts; the base test gives it; every admitted location of the premise, with its mark, is a location of the pattern; an emitted premise of a concrete added fact passes it; a result passed both mark tests and keeps the mark of the conclusion; `restrictIX_of` takes `insideXB` and the mark test (changed in F71: it took `insideLocXB`). |
| `HandoffX.restrictIX_interM`, `restrictIX_inter_conc`, `restrictIX_narrowM`, `handF_narrowXM`, `handF_narrowX_DRXM` | THE INTERSECTION AND THE NARROWING OF ONE HAND-OFF WITH THE MARKS (F71), as the base forms `Handoff.restrictI_interM`, `restrictI_inter_conc`, `restrictI_narrowM`, `handF_narrowM`; in a `DRX` run (concrete) the piece lies inside `D-p` with its exclusion and its mark, or it is the `[any]` exception on a demand-layer piece, with a mark of `D-p`. |
| `HandoffX.XVec.vM_user`, `vM_prem`, `vM_inStarEx`, `vM_outStarEx`, `vM_emit`, `restrictIX_contract_loc_false` | THE MARK VECTORS WITH THE EXCLUSIONS (`decide`, F71): the example of F71 (`restrictIX` gives nothing, the earlier `AnyTaintEx.restrictX` keeps the edge), a premise mark that `D-c` does not admit, the `*∖X` cells (the exit side with an `[any-taint]/{f}` conclusion), the emission under a `*∖{T}` entry pattern; CEGAR: the location form of C5 is false for `restrictIX`. |
| `HandoffX.restrictIX_ok`, `restrictIX_sub_base`, `restrictConcIX_fact`, `restrictIX_restrictI` | `AnyTaintExExact.RestrictOKX restrictIX`: the normal form of W8, the same layer, fewer pairs; the facts without the exclusions only lose pairs; with a premise inside `D-c` without its exclusion the result is the base restriction `restrictI`. |
| `HandoffX.restrictIX_contract`, `restrictIX_contract_base`, `restrictIX_not_RestrictContractX` | C5 for a premise inside `D-c` (with its exclusion and, since F71, its mark: `insideXB`; the base form `insideB`), a pair whose exit location `D-p` covers with its mark (`p.covers l2`; changed in F71: `p.coversLoc l2`), every conclusion, also `*`; the overlap form is false. |
| `HandoffX.emitX_inside`, `emitX_inside_base`, `emitX_emitM`, `insideLocXB_sound`, `insideLocXB_of_base` | An emitted premise lies inside its entry pattern (with and without its exclusion), as locations; the location form. |
| `HandoffX.restrictIX_inter`, `RExcX`, `restrictConcIX_inside`, `restrictIX_narrow` | The intersection with the exclusions, as locations, except the cells of `RExcX`: a demand `[any]` at or above a `*/E2` exit pattern, and a `*` conclusion. |
| `HandoffX.pubRXw`, `pubRX`, `pubRX_sub`, `handF_narrowX`, `handF_narrowX_DRX` | The publication of an X run read without the exclusions; the narrowing of its hand-off, as locations (in a `DRX` run only the `[any]` exception, on a demand-layer piece). |
| `HandoffX.XVec.v64_demand`, `v64_taint`, `v_taint_star`, `v_at_rows`, `v_above_rows`, `v_below_rows`, `v_overlap`, `v_inside_only_with_excl`, `v_inside_only_with_excl_loc`, `inter_exc_any`, `inter_exc_star`, `v_old_above_not_inter` | THE VECTORS (`decide`): every cell with the exclusions; the earlier cell above a `*/E2` exit pattern (`[any-taint]` with the Empty exclusion) has a pair outside `D-p`; a premise inside `D-c` only with its exclusion. |
| `HandoffX.EmitInsideX`, `RestrictInsideX`, `CrossSatX`, `RecsEmbed`, `restrictIX_inside_contract`, `emitX_insideX`, `recLayerX_false`, `cross_appliesX` | The contracts of the generic X rules and the spec rules have them; a crossable base record is the X record with no must flag and no exclusion (`RecsEmbed`), which the record demotion never demotes. Since F71 the two contracts read the marks: `EmitInsideX` gives `insideXB` for a concrete added fact, and `RestrictInsideX` takes `insideXB` and `p.covers l2`. |
| `HandoffX.coverageRXI`, `reach_strongRXI`, `coversN_DRXI_gen`, `coversN_DRXI` | THE FORWARD CONTRACT `Handoff.CoversN` of `AnyTaintEx.DRX … emitX satX restrictIX …` read without the exclusions, under `P.WF` and `RecsEmbed`. |
| `HandoffX.run0X_contract` | Run 1 with the exclusion (`AnyTaintEx.D6X` with `policy1`, read by `forget6`) satisfies `HandoffIter.Run0Contract`. |
| `HandoffXIter.canonStateX`, `embedRecs`, `canonX_pubSub`, `canonX_run0`, `canonX_covers`, `canonX_backward` | THE CANONICAL X SEQUENCE: run 1 `D6X`, the backward run of the base model, the forward runs `DRX … emitX satX restrictIX` with the embedded records. |
| `HandoffXIter.iteration_generalNX`, `iteration_generalNX_all`, `iteration_reportsNX_canon` | THE ITERATION THEOREM WITH THE EXCLUSION: as `HandoffMain.iteration_generalN`; with every reported vulnerability seeded, run 1 and every forward run report every real vulnerability. |
| `HandoffXIter.iteration_generalNX_incl`, `iteration_reportsNX`, `runSeqNX`, `pubSeqNX`, `pubSeqNX_sub` | The inclusion form (the driver may hand off more), with the hypotheses of `AnyTaintExCov.iteration_reportsX`. |
| `PipelineHandoffDriver.driver_iterationNX`, `resultSeqX_runSeqNX`, `pubSeqXst`, `pubSeqXst_pubSeqNX` | THE DRIVER (`analyzer-core.md` §7) WITH EVERY REPORTED VULNERABILITY SEEDED: if every run is complete, the driver computes the hand-offs of the demand edges from the final states, and the seeds contain EVERY reported vulnerability (`hseeds`), then every forward run of the driver reports every real vulnerability, in some layer. The driver of §6.6 seeds only the DEMAND entries: its form is `PipelineHandoffDriverExt.driver_iterationNX_demand` (below). The pipeline systems `PipelineAP.sysDB` and `PipelineAnyTaintEx.sysDRX` are generic in the restriction, so no new system. |

THE NO-`*` DEMAND AND THE EXACT NARROWING (`HandoffNoStar.lean`, namespace `HandoffNoStar`). The seeds have concrete
marks and no `*` tail (every sink pattern has the tail `$` or `[any]`, S11 (f)). Since F72 demand patterns with a `*`
tail occur after run 1 (§6.4): the claims of this table about the later runs (no `*` premise, no `*` conclusion, no
`*` pattern, the exact narrowing) are FALSE for the F72 runs; W2 itself still holds there (argued, §2.3). The claims
about run 1 (`Run1K`, `D_premK`, `run1_exit_star_cross`,
`handF_run1_nonstar`, and the X forms for run 1) still hold, because F72 does not change run 1:

| Theorem | Statement |
|---|---|
| `Run1K`, `D_premK`, `run1_exit_star_cross`, `handF_run1_nonstar` | Run 1: every premise has the tail `$` or `*/{}`; every exit edge with a `*` conclusion is normal with an abstract mark (W2), so it is crossable; so the hand-off of run 1 has no `*` entry pattern, and its exit patterns have the tail `$` or `*/{}` (§6.4). |
| `DB_added_nonstar`, `DB_init_nonstar`, `LegalE`, `DB_legal`, `DB_edge_nonstar`, `demOfN_nonstar`, `nonstar_of_sinkK` | The backward run: no `*` added fact; no `*` premise under a demand with no `*` entry pattern; W2 for seeds with no `*` tail, so no `*` conclusion (§2.3); its hand-off has no `*` pattern. |
| `canon_dem_nonstar`, `canon_handF_nonstar`, `NoStarOrEmpty`, `rexc_empty_loc` | The canonical sequence: no demand pattern of a forward run has a `*` tail; a hand-off has no `*` entry pattern, and a `*/{}` exit pattern only after run 1, where the cell (a) of `Handoff.RExc` adds no location. |
| `narrowing_canon_fwd_exact`, `narrowing_canon_back_exact`, `narrowing_canon_back_loc`, `narrowing_canon_loc_exact` | THE NARROWING THEOREM (§6.6), with no exception, as locations: the hand-off of every restricted forward run lies inside its demand; the backward hand-off lies inside the forward hand-off (after run 1 in location form); every demand pattern of forward run `k + 2` (Lean numbering) with an exit pattern lies inside a demand pattern of forward run `k + 1` of the same method, entry inside entry and exit inside exit. The zero demand and the seed-path patterns are not covered. |
| `narrowing_canon_fwd_exactM`, `narrowing_canon_back_exactM`, `narrowing_canon_loc_exactM` | THE NARROWING THEOREM IN THE LOCATIONS AND THE MARKS (F71; the form that §6.6 states): the same three statements with `Handoff.insideB` and `PFact.covers`: every location of the exit pattern, with its mark, is a location of the exit pattern of run `k + 1`, and the same for the entry patterns; no exception. |
| `base_loc_exception_weak`, `base_loc_exception_weak_entry` | A remark: the exception disjuncts of `HandoffMain.narrowing_canon_loc` hold for every `*` exit pattern and for every `[any]` or `*` piece, so they do not name the edge. |
| `PremK6`, `D6X_premK`, `run1X_exit_star_cross`, `handF_run1X_nonstar`, `DRX_init_nonstar`, `handF_DRX_nonstar`, `canonX_dem_nonstar`, `canonX_handF_nonstar`, `insideLocXB_nonstar` | The same on the canonical X sequence (run 1 `AnyTaintEx.D6X`, the forward runs `AnyTaintEx.DRX`): no demand pattern has a `*` tail; with no `*` tail the X premise test differs from the base one only for the exclusion Universe. |
| `narrowing_canonX_fwd_exact`, `narrowing_canonX_back_loc`, `narrowing_canonX_loc_exact`; `HandoffNoStar.NSVec.entry_univ`, `entry_univ_loc` | THE NARROWING ON THE X SEQUENCE: the forward step is exact, and the piece lies inside `D-p` also without its exclusion; the composed form is exact on the exit side, and on the entry side except at a location that a dropped premise exclusion Universe excludes (a real cell of the operations, `HandoffNoStar.NSVec.entry_univ`; the AP has no Universe exclusion, S8). |

THE EXCLUSION AND THE ROUND NARROWING ON THE X CLOSURES (`HandoffXMain.lean`, namespace `HandoffXMain`):

| Theorem | Statement |
|---|---|
| `HandoffXMain.forward_zero_initX`, `forward_zero_edgesX`, `forward_zero_init_forgetX`, `forward_zero_edges_forgetX`, `emitTX_zero` | A forward X run whose demand gives `M` only the zero pattern has only the zero fact (no must flag, no exclusion) as an initial fact of `M`, and only zero-premise edges in `M`; the same on the view without the exclusions. |
| `HandoffXMain.exclusion_roundX`, `exclusion_canonX` | THE EXCLUSION (§6.6) on the X closures: one round, and on the canonical X sequence (`HandoffXIter.canonStateX`), under the hypotheses of `HandoffMain.exclusion_canon`. |
| `HandoffXMain.narrowing_canonX_fwd`, `narrowing_canonX_back`, `narrowing_canonX`, `narrowing_canonX_loc`, `FwdExc`, `Dropped`, `covLoc_split`, `not_dropped_empty` | THE NARROWING OVER ONE ROUND on the canonical X sequence, with the exclusions of the forward piece and premise read; in location form a location can be one that a dropped exclusion excludes (`Dropped`; none for the Empty exclusion). |
| `HandoffXMain.narrowing_canonX_fwdM`, `narrowing_canonX_backM`, `narrowing_canonXM` | The same in the locations AND the marks (F71; `HandoffX.insideXB`, `Handoff.insideB`): the X runs and the backward runs are concrete (`AnyTaintExCov.concX_all`, `BExact.DB_edge_concrete`), so in the cells `FwdExc` and `Handoff.RExc` the marks still narrow. |
| `HandoffXMain.XMVec.exit_dropped`, `exit_dropped_loc`, `entry_dropped`, `entry_dropped_loc` | The vectors (`decide`): each step is a real cell of the operations, and the composed exit (entry) location lies outside `D-p` (`D-c`) at a dropped location, with a `*/{4}` demand pattern (which the spec runs do not have, `HandoffNoStar.canonX_dem_nonstar`). |

THE SOURCE SEEDS, THE FINITE FORMS AND PROGRAMS 1 AND 2 (`HandoffSrc.lean`, `HandoffUpto.lean`, `HandoffRCases.lean`;
the namespaces of the file names):

| Theorem | Statement |
|---|---|
| `HandoffSrc.seg_genN_src`, `reach_of_db_genN_src`, `demanded_genN_src`, `B_srcN`, `B_generalN_of_src` | CONTRACT B WITH THE SOURCE SEEDS (§6.6 item 3): the justified witness is demanded or recorded in the next forward run on `FSeeds.keepSources P σ`, for every `σ` that contains the source hits of the backward run; a recorded call reads no seed. With every source seeded it is `HandoffBackward.B_generalN`. |
| `HandoffSrc.runSeqSrcN`, `iteration_srcN`, `iteration_srcN_upto`, `canonStateSrc`, `iteration_srcN_canon`, `runSeqSrcNX`, `iteration_srcNX`, `iteration_srcNX_upto` | THE ITERATION WITH THE SOURCE SEEDS (§6.6): as `HandoffMain.iteration_generalN`, on the seeded programs; the canonical sequence; the X closures; the finite forms. |
| `HandoffSrc.SrcRec.run1_exit`, `exit_cross`, `rec_next`, `src_dropped`, `found_unseeded` | THE SOURCE SEEDS DO NOT FILTER THE RECORDS (§9.2): a crossable zero-premise record of run 1 fires the effect of a source that the seeds drop, and the next forward run reports the vulnerability in the normal layer through it (a precision point only). |
| `HandoffUpto.BackwardContractNIn`, `iteration_invariant_upto`, `iteration_prog_upto`, `iteration_abstract_upto`, `iteration_generalN_upto`, `iteration_generalN_canon_upto`, `iteration_generalNX_upto`, `iteration_generalNX_canon_upto` | THE FINITE FORMS: the hypotheses only for the runs before forward run `K`, the conclusion for every forward run up to `K`; no run after `K` is read. |
| `HandoffRCases.p1_no_exit`, `p1_found_I`, `p1_handoff`, `p1_chain` | PROGRAM 1 (§6.3) with the intersection: no `D-p`, no result; forward run 3 reports the vulnerability; the hand-off of the demand edges contains the callee patterns (case 2); run 1, backward run 2 and forward run 3 report it. |
| `HandoffRCases.r1_c_not_cross`, `b2_handF`, `b2_emit`, `b2_inside`, `b2_restrictI`, `b2_restrictI_eq_U`, `b2_not_crossB`, `p2_handoff`, `ddM_eq`, `f3_emit`, `f3_inside`, `f3_restrictI`, `f3_restrictI_eq_U`, `p2_found_I`, `p2_chain`, `b2_insideB`, `b2_concMark`, `f3_insideB`, `f3_concMark` | PROGRAM 2 (§6.4) with the intersection: the run-1 summary of `c` is a demand edge; the backward premise lies inside its `D-c`, and the backward summary is in the demand layer (case 3); the forward premise lies inside its `D-c`; on this program the intersection equals the earlier restriction; forward run 3 reports the vulnerability. The mark tests of F71 pass in both restrictions (`b2_insideB`, `b2_concMark`, `f3_insideB`, `f3_concMark`), so the results stay. That the hand-off is EXACTLY the three parts of §9.2 is checked by hand. |

THE DRIVER WITH THE SEEDS OF §6.6 (`PipelineHandoffDriverExt.lean`, namespace `PipelineHandoffDriverExt`):

| Theorem | Statement |
|---|---|
| `PipelineHandoffDriverExt.driver_iterationNX_demand`, `driver_iterationNX_demand_known`, `known_of_resultSeqX`, `known_of_resultSeqX_upto` | THE DRIVER (`analyzer-core.md` §7) with the hand-offs of `PipelineHandoffDriver.driver_iterationNX` and the seeds of THE SEEDS (§6.6): every vulnerability that the driver reads from forward run `k` (Lean numbering: `k` counts the forward runs) is confirmed (`C k`) or seeded. Then every real vulnerability is, at every forward run `k`, reported by run `k` or confirmed by an earlier run; also on the final states. With `C k` = confirmed by a complete forward run up to `k` (§4.9) this is the claim of §6.6. |
| `PipelineHandoffDriverExt.driver_iterationNX_confirmed` | The instance with `C k` = "a forward run up to `k` reports the vulnerability in the normal layer". This test is weaker than CONFIRMED (§4.9 also needs the support), so it is not the confirmation of this spec: it says only that a normal-layer report ends the need for a seed. |
| `PipelineHandoffDriverExt.driver_iterationNX_upto` | THE FINITE FORM: the driver stops after forward run `K`; the runs up to `K` are complete; the conclusion holds for every forward run up to `K`. |
| `PipelineHandoffDriverExt.driver_iteration_srcNX`, `driver_iteration_srcNX_upto`, `resultSeqX_runSeqSrcNX`, `pubSeqXst_pubSeqSrcNX` | The same with the source seeds (§6.1 rule 6). |

---

## 11. What the proofs do not cover

### 11.1 Expected false-positive sources

The theorems say that a confirmed vulnerability is real for the reference semantics (§3.5): the program that the
micro edges describe. On the JVM the micro edges over-approximate the real program at the points below. There a
confirmed vulnerability (and a normal edge, and a record) can be false. These are EXPECTED false-positive sources: the
analysis keeps their results in the normal layer and does not refine them.

* A type filter on a `*`, `[any]` or `[any-taint]` fact. The filter checks the concrete path only, so the fact keeps
  the locations below its path that a real value cannot have (§4.8). A normal `[any-taint]/E` fact claims EVERY
  admitted location below its path, also a location that the static type does not have; the exactness theorems are
  for the valid locations only (S13).
* A reversed backward record. The backward run does not type-filter, so the record has no type filter (§8.7 R3; the
  reversal theorems `BExact.rev_record_exact` and `revRecs_exact` assume `Exact.FiltUp`).
* The weak alias write. The alias base keeps its old content (S2, `interpreter.md` A3, gap G7).
* The constructor pass-over. An added fact also passes over a constructor call, so the constructor does not
  overwrite the caller facts (`interpreter.md` §3.5, gap G8).
* The default identity of an unresolved callee. It is a weak update of the receiver and of the arguments
  (`interpreter.md` §3.7): the real callee can overwrite a field, and the facts of the caller keep it.
* THE WEAK UPDATES AND `[any-taint]`. A weak update (the alias write, the constructor pass-over, the default identity
  of an unresolved callee, an alias of a call result, `interpreter.md` AC2) keeps an `[any-taint]` object whole: the
  exclusion of W8 comes only from a strong write on the object itself. Example: `a = dto.address; a.city = clean;
  sink(dto.address.city)`. The write is strong for `a`, and the alias edge to `dto.address.city` is gen-only, so `dto`
  keeps `(dto, ., [any-taint], T)` with no exclusion, and the sink is CONFIRMED, although it is not real. The same for
  a deep write through a getter, and for `dto.setName(clean)` on an unresolved `setName` (the default identity). Such
  a false positive is now a CONFIRMED entry; before F69 it was a DEMAND entry (the result of an `[any]`-target source
  was `[any]`, W6). A `$` fact has the same false positive today (`interpreter.md` §0.1, G7, G8, §3.7).
* The catch local. A catch statement does not kill its local, so an old fact on it stays (`interpreter.md` G9).
* The path-insensitive reading. A conjunction can combine literals that hold on paths that exclude each other (§4.6),
  and a negated mark literal counts as true (§3.5).
* A pass rule with a mark literal. It is a rule error that is not rejected (`interpreter.md` §1.3), and the
  interpreter applies it without its mark literals (`interpreter.md` §4.2, D24), so it also fires where a literal is
  false.
* The global-state rule (`interpreter.md` §4.7 step 3, G2, D30). An exit sink drops an evaluated part on `S` only
  from a zero-premise item: a state that the method or its callees set. A caller-set `S` fact is evaluated (it can
  report, and a conjunctive literal stores it as its input, §8.9), but it is not dropped: it returns to the caller
  through the callee summary, also through the run-1 FLOW summary and its record. As today: today's exit sinks run
  only on zero-premise edges (`JIRMethodExitRuleProvider.kt:18-19`), and only a reached sink drops
  (`JIRSequentTaintUtil.kt:76-85`). So a later sink in the caller can see the state, and the exit sink of the caller
  can evaluate it again. The model has no global-state rule (a gap of the interpreter, `interpreter.md` §0.1 G2).
* The end facts of a sink (§4.9; `interpreter.md` §4.1). An end fact is a context-insensitive zero-to-fact edge, as
  today: its premise set is `{zero}`, whatever the premise set of its sink edge. So its summaries reach every caller,
  also a caller that does not supply the premise of the sink edge, and its records are not exact. The backward run
  applies the reversed end-fact edge to every requirement, with no check of the trigger (`interpreter.md` §4.9; it
  also fires the sink seeds of the alternative, §9.2 THE TRIGGER OF AN END FACT), so a backward record through it
  reverses into a forward zero-premise record that is not exact either (§8.7 R3). The model has no end facts.
* A sink rule with end-fact actions: a KNOWN GAP for now. Today the vulnerability check of the trace step reports such
  a vulnerability only if one of its end facts reaches the end of the analysis (`VulnerabilityChecker`). That check is
  out of scope with the trace resolution (§8.10 THE TRACES). So every vulnerability of such a rule that the report
  holds is in the output, also one whose end facts never reach the end of the analysis (`ap-history.md` F67, F68).

THE DEMAND ENTRIES OF THE OUTPUT. The output holds the DEMAND vulnerabilities of the latest complete forward run too
(§8.10; `ap-history.md` F68). They are not confirmed: a DEMAND entry rests on a demand-layer edge, an
over-approximation of §2.2 (the case `above`, a lost correlation, the field limit cut, W2, W6, and the other
demand-layer operations of §2.2, whose `[any-taint]` results W8 (b) names `[any]`), so it can be false also for the
reference semantics. Only a later complete forward run that does not report it
refutes it (§8.10). The soundness theorems cover the output: at every complete forward run, every real vulnerability
is reported by that run, in some layer, or was confirmed by an earlier complete forward run, and the report keeps
every confirmed vulnerability (`HandoffMain.iteration_generalN`; with the `[any-taint]` tail and its exclusion
`HandoffXIter.iteration_generalNX`; the earlier hand-off: `Backward.iteration_general`, `W6.iteration_general6`,
`AnyTaintExCov.iteration_reportsX`).

THE PRECISION LIMITS OF THE `[any-taint]` TAIL. These keep a real `[any]`-target source finding a DEMAND entry. They
are precision losses, not false positives. The first five items are the demotions of §2.2, the complete list. (An
exclusion does not demote: a strong write into an `[any-taint]` object and a setter summary or record `*/{f}` keep it
normal with `f` in its exclusion, §4.1.)

* The field limit cut (§4.4): an `[any-taint]/E` fact over the limit becomes `[any]` in the demand layer, and the
  exclusion is dropped (`AnyTaintExCases.CUT.cut_reports`). A later forward run with a larger limit repairs it (§6.6).
* A cleaner `part` row of §4.7 other than the `atAndBelow` and `below` rows one accessor below the fact: the `exact`
  cleaner at or one accessor below an `[any-taint]` object, or any cleaner two or more accessors below it. The whole
  object becomes `[any]` in the demand layer, in every run (`AnyTaintExCases.CL.exact_result`): no shape exists for
  "every location but one" (`AnyTaintExExact.CexExactCleaner.cex_exact_cleaner`). The same holds for the call
  cleaners and the summary rewriter at such a position.
* A may target: a pass rule with an `AnyField` target is a may (§2.3): its results stay `[any]` in the demand layer
  (W6), also when the real callee writes every field; in the backward run every result of its reversal is in the
  demand layer (§9.1).
* A demand input: an `[any-taint]` fact through a demand-layer summary edge or record, a demand link (an `[any]` added
  fact), or a conjunction with another input in the demand layer gives a demand result (§2.2, §4.3, §4.6).
* The must-record demotion: a must record that applies by `applicable` only gives a demand result (§4.3).
* Run 1 does not confirm an `[any-taint]` finding through a getter in a callee (§6.2: the FLOW summary is the case
  `above`, a demand edge); a later forward run with the demand does (`AnyTaintExCases2.G.run3_confirmed`).
* THE MERGES IN A NORMAL TAINT TREE (§3.3, §7.2 T2 and T5, §8.1). They keep the location set, so they are exact, but a
  later demotion acts on the merged fact. So no `$` leaf is absorbed or subsumed under an `[any-taint]` leaf (§7.2
  T5). Merge rule 2 and the absorption or subsumption of an `[any-taint]` fact by an `[any-taint]` fact stay: after
  them a later cleaner `part` row that demotes the kept `[any-taint]` fact also demotes the locations of the other
  fact, also where that fact alone is disjoint from the cleaner. Example: `(x, ., [any-taint], {f}, T)` subsumed by
  `(x, ., [any-taint], {}, T)`, then `clean(x.f, exact, T)`: the kept fact becomes `(x, ., [any], T)` in the demand
  layer, and `(x, ., [any-taint], {f}, T)` alone would be disjoint from the cleaner and stay normal.
* THE REUSE OF A SOURCE RECORD. The reversal of a forward record leaf `$ → [any-taint]` is `[any] → $` (§8.7 R3): it
  applies only to an `[any]` requirement, so it gives the backward run only demand results. No leaf of a must record
  and no `[any-taint]/E` leaf with `E ≠ {}` is reversed; the other leaves of the record are (§8.7 R3).
* THE HAND-OFF DROPS THE EXCLUSION (§9.2): the backward demand of an `[any-taint]/E` summary conclusion is the pattern
  `[any]`, so the backward run can follow requirements on the excluded locations, which no forward fact reaches. For
  the same reason one step of the narrowing of §6.6 can be coarser on the patterns that the hand-off reads (no
  exclusions) than with the exclusions (`HandoffX.XVec.v_inside_only_with_excl`). On the spec runs no demand pattern
  has a `*` tail, so the composed narrowing is exact on the exit side and, except for a premise exclusion Universe
  that the AP does not have (S8), on the entry side (`HandoffNoStar.narrowing_canonX_loc_exact`; §6.6).

### 11.2 Other limits

* The concrete semantics is alias-free and location-level (§3.5), and per root: every root starts with the zero fact
  only, so no static state crosses roots (as today; D27 clears it between Spring controllers on purpose;
  `interpreter.md` G13).
* The theorems are about the closures `D` (run 1), `DR` (a forward restricted run), `NDZ.DNz` (run 1 with
  conjunctions; the list model `ND.DN`), `Statics.DS` (run 1 with the static rule) and `Backward.DB` (the backward
  run), and, with the `[any-taint]` tail and its exclusion, the spec closures `AnyTaintEx.D6X` (run 1) and
  `AnyTaintEx.DRX` with `emitX`, `satX` and `HandoffX.restrictIX` (a forward restricted run; `AnyTaintEx.DRXs` with the
  earlier restriction), the round-1 closures without the exclusion `AnyTaint.D6T` and `AnyTaint.DRT`, and
  `AnyTaintND.DNzT` (run 1 with conjunctions, without W6T and without the exclusion) (§10.11, §10.12). The rules of
  the CONCRETE restricted runs of F70 and F71 are the emission of §6.3 for a concrete pattern, the satisfaction `inside`
  of §4.3 and the intersection of §6.4 (`emitM`, `satI`, `Handoff.restrictI`), with the hand-offs of §9.2 without the
  normalization (`Handoff.handF`, `demOfN`). The rules of F72 (the FLOW form, `satW`, no request rules, the hand-off
  normalization) are not modelled yet: the item PENDING: THE LEAN MODEL OF F72 below. A real run differs from the
  modelled rules by optimizations. Each one keeps the soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§8.1) | the dropped pairs are pairs of the kept fact (`Subsume.subsumes_sound`) | the local step is proved; the composition is argued |
| merge rules 1 and 2, also for marks (§3.3, T1, T2, T2') | exact (`Tree.rule1_mem`, `rule2_den`, `rule2_mark`, `Subsume.merge_inter`, `merge_mark_inter`) | proved |
| the T5 fold | the denotation does not change (in a normal TAINT tree an `[any-taint]` leaf absorbs no `$` leaf, §7.2) | argued |
| persisted records (R4) | a normal edge has no false pair (a must-premise edge is end-exact, §10.11); adding edges keeps coverage (rule `retRec`, with `applicable` or `satI`). With the hand-off of the demand edges a crossable record is not only an optimization: it replaces the analysis of its callee, and the coverage needs it (§8.7 R5; `HandoffBackward.NextRecs`, `HandoffMain.iteration_generalN`, proved) | proved for one forward run under S14 (`RExact.recApp_markSub`, `RMain.p3_reuse_exact`); over the forward runs (`BExact.recsSeq_exact`, `recsSeq_exactV`, `seq_edge_exact`, `seq_confirmed_real`; `RecsFromRuns`); over the backward runs (`BExact.recsBSeq_exact`); and for the reversed summaries of one backward run (`BExact.revRecs_exact`, `Exact.FiltUp`). Argued: the two directions together, and the conjunction records (the list below) |
| W6 (`[any]` always in the demand layer; the old rule, the record of §10.3) | a layer refinement: the W6 run has the same facts, with the same or a raised layer (`W6.D_le_D6`, `D6_le_D`, `DR_le_DR6`, `DR6_le_DR`) | proved for `D` (under `W6.SummaryStar`, which `W6.summaryStar_policy` gives for the run-1 policy) and for `DR` (under `W6.RestrictLE` and `W6.ExactInitConc`, which `W6.restrictU_LE` and `W6.DR_eic` give): soundness, exactness, confirmation and the iteration (§10.3). Argued for `Statics.DS`, `ND.DN` and the backward run |
| W6T: W6 with W8 (only a may `[any]` result in the demand layer; the spec rule of the forward runs, §2.3) | run 1 without the exclusion: a layer refinement of `D` (`AnyTaintSim.D_le_D6T`, `D6T_le_D`); a forward restricted run with must-premises: the facts of `DR` (`AnyTaintSim.factSim`); the must-premise edges are end-exact | proved in the spec closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX` (the theorems with the restriction as a parameter, for the intersection through `HandoffX.restrictIX_ok`; the instance `AnyTaintEx.DRXs` has the earlier restriction) (§10.11, §10.12), and in the round-1 closures `AnyTaint.D6T` (under `W6.SummaryStar`) and `AnyTaint.DRT` (under `EmitCopiesMark` and `AnyTaint.RestrictFact`): soundness, exactness, confirmation, the records and the iteration. Argued for `Statics.DS` and for `NDZ.DNz` (the layer raise on top of `AnyTaintND.DNzT`); the backward run keeps W6 (the list below) |
| the exclusion of `[any-taint]` (W8; §4.1, §4.7, §6.3, §6.4) | an exclusion removes only locations that no flow reaches (`AnyTaintExCov.applyEdgeX_sound`, `annX_admits`, `cleanResX_sound`); every normal result is exact on its admitted locations (`AnyTaintExExact.applyEdgeX_exact`, `cleanResX_exact`) | proved for `AnyTaintEx.D6X` and, with the earlier restriction, `AnyTaintEx.DRXs`: soundness (`AnyTaintExCov.iteration_reportsX`), exactness, confirmation and the records (§10.11); with the spec restriction `HandoffX.restrictIX` and the hand-off of the demand edges: soundness (`HandoffXIter.iteration_generalNX`; with the source seeds `HandoffSrc.iteration_srcNX`), the exclusion (`HandoffXMain.exclusion_canonX`), the narrowing (`HandoffXMain.narrowing_canonX`, `HandoffNoStar.narrowing_canonX_loc_exact`), and exactness, confirmation and the records through `HandoffX.restrictIX_ok` (§10.12). Argued: merge rule 2, the subsumption, T5 and the tree key with the exclusion (§3.3, §7.2, §8.1), the tree restriction (§7.4), `Statics.DS`, the conjunctions and the exactness of the seeded runs (the list below) |

* PENDING: THE LEAN MODEL OF F72 (`ap-history.md` F72; the user's order: the spec first, then the proofs, then the
  proposals `ap-impl.md` and `analyzer-impl.md`, which follow F71 until the proofs are done; the user: "Mark the
  updating proofs as the pending task"). The rules R1 to R5 of F72 are normative (§4.3, §4.5, §4.7, §4.9, §6.3, §6.4,
  §9.2), and no theorem of §10 is about them yet. The theorems of the restricted runs and of the iteration (§0.1,
  §6.1, §6.6, §10.7, the restricted parts of §10.8, §10.10 and §10.11, §10.12; `analyzer-core.md` §7.7, §7.8, §12)
  are proved for the CONCRETE restricted runs of F70 and F71: the emission `emitM` (`AnyTaintEx.emitX`), the
  closures `DR`, `AnyTaintEx.DRX` and `Backward.DB` with request rules that never fire, and the concreteness lemmas
  (`RExact.DR_concrete`). Their names stay; they hold for that design. The task:
  * THE DEFINITIONS (planned Lean names; the file `AbsDefs.lean` is in progress, and no claim of this spec rests on
    it yet): `markNorm` (`*∖X` becomes `*`) and `normDem`, the
    hand-offs `handFA`, `demOfNA` (`Handoff.handF`, `demOfN` with `normDem`); `flowK`, `flowForm`; the emission
    `emitW` (nothing if `emitM d a` is nothing; else `flowForm d` if `d.mark = *`, else `emitM d a`); the satisfaction
    `satW` (`satI`, or `applicable` for a premise with the mark `*`); the closures `DRA` (forward: `DR` with no request
    rules) and `DBA` (backward: `Backward.DB` with no request rules: no `reqStmt`, `reqSink`, `reqClean`, `reqUp`,
    `answer`), with the emission, the satisfaction, the restriction and the records as parameters, as in `DR`; the
    mark-agnostic flow `FlowMA`; the witnesses with modes (`FlowRRA`, `ReachRRA`: the input form of `Handoff.FlowRR`,
    `ReachRR`; `FlowRDNA`, `ReachRDNA`: the output form of `FlowRDN`, `ReachRDN`); the contracts with modes
    (`CoversNA`, `BackwardContractNA`, as `Handoff.CoversN`, `BackwardContractN`).
  * THE MODES (§6.6, CONTRACT B WITH MODES). A demanded witness carries a mode at each call that returns: ABSTRACT if
    a `*` pattern demands it (its inner flow is mark-agnostic), CONCRETE if a concrete pattern demands it (its inner
    flow as before; nested calls of either mode).
  * THE LEMMAS. L1 (forward abstract coverage): from a `*` premise that covers the entry location, a mark-agnostic
    flow is covered by an edge of the premise, with no request (no request rule exists). L2 (run 1 picks the right
    mode): run 1 (`D` with `policy1` and its requests) justifies every real witness, at each call by a FLOW premise
    (then the inner flow is mark-agnostic: the coverage followed it with no request) or by an answer (a concrete
    premise). L3 (backward abstract coverage): a `*` requirement covers the reversed flow of a mark-agnostic flow (the
    reversal of a `*`-mark micro edge has `*` marks, `Reverse.MarkRev`; a cleaner is its own reversal). L4 (contract B
    with modes): an abstract-mode call justified by a FLOW summary meets a `*` pattern in the next forward run; a
    concrete-mode call justified by a concrete summary meets a concrete pattern. L5 (exactness): a normal edge of a
    `*` premise in a restricted run is exact, so the records stay exact. (A hint, not checked: `RExact.edge_exactR_valid`
    and `confirmed_realM_gen_valid` take any emission and a satisfaction with `RExact.SatMark`, which `satW` has, and a
    closure with no request rules has a subset of the rules of `DR`; the X forms need `AnyTaintEx.EmitCopiesMarkX`,
    which `emitW` does not have.) L6 (the emission contract): for every pattern and every added fact that both cover a
    location with its mark, `emitW` gives a premise that covers it and that the added fact satisfies by `satW` (a `*`
    pattern: the FLOW form covers the location with every mark; a concrete pattern: as `RCore.emitM_contract_I`, for
    a concrete added fact).
  * THE ITERATION: as `HandoffMain.iteration_generalN`, with the new closures and the modes; then the X closures
    (`AnyTaintEx.DRX` with the F72 emission), the source seeds, the finite forms and the driver.
  * THE CEGAR PROGRAMS, FIRST (closure invariants, as in `HandoffCases.lean`): (i) THE GETTER with two marks `T` and
    `U` under one `*` pattern (§6.3, THE GETTER): one FLOW premise or one record for both added facts, and both
    vulnerabilities reported; (ii) A MARK-CHANGING PASS RULE `T → U` inside a callee that a `*` pattern reaches: the
    `*` analysis gives nothing for it (a concrete premise mark), and the flow is found through the concrete pattern
    that the request and the answer of run 1 made; (iii) A PARTIAL CLEANER of `T` under a `*` premise: the fact
    continues as `*∖{T}` with no request, and the flow of `T` through the part that the cleaner does not clean comes
    from a concrete pattern; (iv) THE SEARCH FOR A COUNTEREXAMPLE TO R6: a flow that needs a concrete mark in a callee
    that only `*` patterns reach after run 1 (for example a concrete demand that the backward weakening loses). If R6
    fails, the program and the smallest rule change go to `ap-history.md`.
  * OPEN POINTS OF THE RULES that the model must decide: (a) L6 is false for a `*` pattern with the tail `*/E`,
    `E ≠ {}`: its FLOW premise `(x, ., */{f}, *)` and the added fact `(x, ., */{g}, *)` have common locations, but
    neither `inside` nor `applicable` holds (§4.3). The model must show that the hand-off gives no such pattern (a
    normal leaf with a `*` conclusion is crossable, §4.3, §6.3), or change the satisfaction or the FLOW form for it;
    (b) a `*` conclusion above a `*` exit pattern is kept whole (§6.4, the exception (b)): a precision point, and the
    exact meet at one path is representable (`Handoff.star_meet_exact`); (c) the static invariant of the restricted
    runs with FLOW premises on `S` (§4.10); (d) the exceptions of the intersection, the narrowing and the exclusion of §6.4 and §6.6 for the F72 runs; (e) the index query of a FLOW
    premise in the subscription store (§8.4).
  * THEOREMS WHOSE CLAIM IS FALSE FOR THE F72 RUNS. They describe the concrete design and stay in the model as its
    record: the concreteness of a restricted run (`RCov.concInvR_all`, `added_concR`, `RExact.DR_concrete`,
    `final_not_star`, `complete_premise_exact`, `BExact.DB_concrete`, `AnyTaintExCov.concX_all`,
    `AnyTaintExExact.DRX_conc`, `AnyTaintExKinds.DRX_normal_premise`, `Kinds.kinds_DR`, `kinds_DR_emitM`, `kinds_DB`,
    `kinds_DB_taint`: their hypothesis `EmitCopiesMark` (`EmitCopiesMarkX`) fails for the F72 emission under a `*`
    pattern); the absence of `*` exits and `*` patterns after run 1 (`Handoff.DR_exit_not_star`, `handF_DR_nonstar`,
    `HandoffNoStar.DB_init_nonstar`, `DB_edge_nonstar`, `demOfN_nonstar`, `canon_dem_nonstar`, `canon_handF_nonstar`,
    `DRX_init_nonstar`, `handF_DRX_nonstar`, `canonX_dem_nonstar`, `canonX_handF_nonstar`), and the exact narrowings
    that rest on it (`HandoffNoStar.narrowing_canon_fwd_exact`, `narrowing_canon_back_exact`,
    `narrowing_canon_loc_exact`, their forms `narrowing_canon_fwd_exactM`, `narrowing_canon_back_exactM`,
    `narrowing_canon_loc_exactM`, and `narrowing_canonX_fwd_exact`, `narrowing_canonX_loc_exact`). The request lemmas
    (`RCov.no_reqR`, `RExact.DR_no_request`, `RMain.no_request_M`, `BExact.DB_no_request`) derive "no request" from the
    concreteness; the F72 closures have no request rules, so the claim holds there by definition. These theorems still
    hold for the F72 rules: `HandoffNoStar.handF_run1_nonstar` and `run1_exit_star_cross` (they read run 1 only, which
    F72 does not change, and the normalization changes only marks).
* The backward run is modelled as the closure `Backward.DB` (the rules of `DR` on the reversed program, with the zero
  rules of §9.2), and it satisfies the contract B (with the hand-off of the demand edges and the intersection
  `HandoffBackward.B_generalN`; with the earlier hand-off `Backward.B_general`). The reversal of a conjunctive micro edge into
  one edge per literal with every result in the demand layer (§9.1, §9.2), the alias edges of the reversed call (§9.2;
  the model is alias-free, S2) and the interpreter's call-site rules of the backward run (`interpreter.md` §4.9) are
  argued, not modelled.
* ND edges are modelled for run 1 (`ND.DN`): coverage, the vulnerability theorems (§10.6) and the exactness of the
  normal layer against the support semantics `ND.TaintN` (`NDExact`, under S7, S9, S10 and S13) are proved. The
  CONFIRMATION of a vulnerability through a conjunction is proved too, with the joint support of §4.9 condition 3
  (`NDConfirmed.confirmed_real_N`), in run 1. No edge with two or more premises is a record (§8.7 R1). A restricted
  run with ND edges is ARGUED, not modelled:
  1. it has no request rule (§4.5): before F72 its facts were concrete, so a literal never raised a request; since
     F72 a literal on a fact with an abstract mark gives nothing;
  2. the restriction of a summary with several premises (§6.4, the special cases) only removes pairs from the
     conclusion;
  3. the contract B for a TREE witness (`ND.ReachAll`) needs a demand pattern on every node of the tree. The backward
     run reverses a conjunctive edge into one edge per literal (§9.2), so a requirement at the conclusion reaches every
     branch. Every result of these edges is in the demand layer (§9.1, THE REVERSAL OF A CONJUNCTION), so no backward
     summary through them is a record or crossable, and case 3 of §9.2 gives each branch its demand pattern: the next
     forward run analyses the callee again with every member, and no one-literal record replaces the conjunction.
  4. a one-member conjunction record (§8.7 R4) applies in a later run as an ordinary record, and it is reversed
     (R3). It is real for the support semantics in every caller context, because the zero binding supplies the zero
     premise that the zero-drop removed.

  `ND.D_sub_DN` embeds the distributive part, so the iteration theorem holds unchanged for a program without
  conjunctions.
* PREMISE SETS AND LISTS. The zero fact is a premise in the spec and in the model (§1). `ND.lean` keeps premise LISTS
  (with `[zeroFact]` for a zero-to-fact edge); this spec keeps SETS. A list and its set name the same entry locations,
  so every ND theorem carries over (argued). A conjunction drops the zero fact from the union of its premise sets
  (§4.6): the model edge with the premises `[zeroFact, i]` is the spec edge with the premise set `{i}`. This is PROVED
  (§10.10): the closure `NDZ.DNz` corresponds to `ND.DN` edge by edge (`NDZero.dnz_to_dn`, `dn_to_dnz`), because the
  zero fact is at every node that an edge reaches (`NDZero.zero_everywhere`); coverage, exactness and confirmation
  carry over (`NDZeroThms`). A conjunction result whose premise
  set has one member is an ordinary edge; it can be a record if it is normal, and it is exact for the support
  semantics (`NDZeroThms.nd_edge_exact_z`; through `NDZero.dnz_to_dn` it is the `ND.DN` edge `[zero, i]` of
  `NDExact.nd_edge_exact`).
* The static rule of §4.10 is modelled as a separate run-1 closure `Statics.DS`. Soundness, exactness and the
  iteration that starts from it are proved (`StaticsIter.iteration_general_DS`). The run-1 proof needs that a cleaner
  on `S` names its mark (S12 (e)). The interpreter makes it true: `RemoveAllMarks` on a position of `S`, at any depth,
  is the kill of a strong write, not a cleaner (`interpreter.md` §1.4). The one exception, the whole-base cleaner
  `(S, atAndBelow, all)` of `AnyClassStatic`, is argued: every fact on `S` lies inside it, so it drops each fact whole
  and raises no request; its effect is that of a statement that touches `S` with no micro edge on `S`, which S12 (a)
  allows. The restricted runs do not need it (`StaticsIter.SWFR`). The
  static rule and the conjunctions are in separate models: a conjunction literal on `S` uses the plain run-1 rules
  (§4.6).
* ARGUED, NOT PROVED. These claims of the spec have no Lean proof. Each item gives the claim in one sentence:
  * The source seeds (§6.1 rule 6) at a call, at the method start and at the method exit. The model has the
    statement sources only (`FSeeds.keepSources`); the others are the same micro edges at another place. The model
    keys a seed by the node before the statement; the implementation keys it by (method key, statement), which is the
    same on the JVM graph.
  * A seeded forward run is exact for `P`. `BExact.recsSeq_exact`, `seq_edge_exact` and `seq_confirmed_real` are
    proved for the runs on `P`. A seeded run has fewer flows (`FSeeds.flow_keep`), and it reads records that are exact
    for `P`, also a record of a source that is not a seed (§9.2; `HandoffSrc.SrcRec.found_unseeded`).
  * The source seeds with the static rule (`Statics.DS`) and with the conjunctions (`ND.DN`).
  * The backward run needs no static rule: proved if the reversed program satisfies S12 (a) to (d) and its seeds keep
    the invariant (`BExact.no_static_rule_backward`, `BExact.SeedsOK`); that the interpreter's reversed program
    satisfies them is argued (the static positions of the reversed program are the forward write targets).
  * Every persisted record keeps the static invariant `StaticsIter.RecOK` that the static theorems of the restricted
    runs assume: argued from the run-1 invariant (`Statics.cinv_all`), the restricted-run invariant
    (`StaticsIter.rinv_all`) and the backward-run invariant (`BExact.recOK_of_DB`), run by run.
  * W3 (every result of a run has at most `L` counted accessors when the field limit does not decrease) is argued.
  * A conjunction of `k > 2` literals is argued by chaining binary conjunctions; the model `ND.Conj` has two literals.
  * A conjunctive sink (§4.9) is argued as a conjunction to a fresh target with a sink on it; `ND.DN` has no
    conjunctive sink rule.
  * The cleaners of a call act on the bound fact before the callee (§5.3 step 4), and they give the added fact its own
    layer on the link (§8.3): argued, because the model `Call` has no cleaners (a cleaner is an instruction of the
    CFG, `Instr.clean`).
  * The summary rewriter (§4.7, §5.3 step 5) overrides the callee flow, so the analysis with it does not cover `Flow`
    (§3.5). The theorems read each call with selected rules as a WRAPPED call: the callee flow, then the cleaner
    `(P, exact, T)` of each selected rule, mark and position (for an `AnyField` position `(P, atAndBelow, T)` for a
    source, `(P, below, T)` for a cleaner, §4.7), on the callee results, before the binding back; the
    source results and the end facts of the call bypass the wrapper. Soundness and exactness with the override are
    argued against this overridden semantics, as for the call cleaners above.
  * A summary with several premises: its restriction (§6.4: every member inside a `D-c` of the method, one member
    inside the `D-c` of the restricting pattern) and its hand-off (§9.2: every leaf is a demand edge, one pattern per
    member) are argued.
  * The conclusion kinds of §7.2, and W2 (§2.3), for run 1 with the static rule (`Statics.DS`). `Kinds.kinds_D` is
    proved for `D`; `DS` adds the position answer `(S, p, *, {}, *)`, a premise with the mark `*`, and the mark answer
    on a static premise, an added fact with a concrete mark (§4.10 items 2 and 4). Each one has the premise mark of its
    kind, so the reasons of §7.2 hold for it. For run 1 with the conjunctions (`NDZ.DNz`): the ND edges are
    `Kinds.ndz_taint`; the single-premise edges are the item THE ZERO-BASE AND KIND INVARIANTS below.
  * The two exits of a JVM method (the normal exit and the exceptional exit) are one virtual exit of the one-exit model
    (S4): the exit rules act at both exits (so an unconditional exit sink can report at both), the backward zero fact
    and the seeds of the exit sinks start at both (S11 (e) reads the virtual exit), and only the normal exit makes a
    summary edge, because no exception flow crosses a call (below).
  * RECORDS ACROSS THE DIRECTIONS (§8.7 R3). A forward run reads the reversed backward records, and a backward run
    reads the reversed forward records. Each step is proved for `Exact.FiltUp` (`BExact.revRecs_exact`,
    `Reverse.backward_reuse_precise`, `RExact.recs_union`, `recs_of_DR`, `BExact.recsB_step`); the induction over the
    alternating sequence is argued. With type filters, a reversed backward record is not exact (§11.1). The soundness
    does not use the exactness of the records. With the hand-off of the demand edges it uses their PRESENCE: a
    crossable leaf that is not handed off must be a record of the next runs (`HandoffBackward.NextRecs`,
    `HandoffMain.iteration_generalN`). (With the earlier hand-off the record sets are free, `Backward.iteration_general`.)
    A backward summary through the reversal of a conjunction is never a record (§9.1, THE REVERSAL OF A CONJUNCTION):
    before F70 R3 reversed such a normal summary into a forward record of one literal, a false positive
    (`ap-history.md` F70). The rule is argued with the restricted runs with ND edges (above).
  * END FACTS in the restricted and backward runs. A real flow from an end fact is found in forward run `n + 2`. Its
    sink triggered in forward run `n` (an end fact exists only then). If the vulnerability of the sink is a DEMAND
    entry, it is seeded. If it is CONFIRMED, it is not seeded (§6.6, THE SEEDS), but a requirement of backward run
    `n + 1` that reaches the end fact reaches its reversed end-fact edge, and THE TRIGGER OF AN END FACT (§9.2) fires
    the sink seeds of its alternative there. In both cases contract B keeps the witness of the trigger demanded or
    recorded, so the sink triggers again in forward run `n + 2`, and the end-fact action is not restricted (§6.1 rule
    6). The reversed end-fact edge also gives the zero fact, read as a reversed unconditional source (§9.2); it only
    adds requirements. The model has no end facts. (With the seeds of the DEMAND entries only and no trigger rule, a
    real DEMAND vulnerability that rests on the end fact of a CONFIRMED sink is refuted: the program of §9.2 THE
    TRIGGER OF AN END FACT.)
  * THE HAND-OFF OF THE DEMAND EDGES (§6.4, §6.6, §8.7 R5, §9.2; `ap-history.md` F70, with the mark-aware
    restriction of F71). Proved (§10.12): its
    soundness (also with the source seeds of the statement sources, in the finite form and for the driver of §6.6
    with the seeds of the DEMAND entries only), the exclusion of one round and the narrowing of one round (in the
    locations and the marks), on the base closures and on the closures with the `[any-taint]` exclusion, and the
    absence of `*` demand patterns (so the narrowing has no exception; on the X closures the exact form is stated as
    locations only, `HandoffNoStar.narrowing_canonX_loc_exact`, and the marks narrow by
    `HandoffXMain.narrowing_canonXM`). All of it is proved for the concrete restricted runs; with F72 the `*` demand
    patterns occur, and these parts are PENDING (the item above). These parts are argued:
    * THE ZERO FACT IS NOT LOCALIZED (a later task). It still enters every callee: the backward rule `zin`, and the
      forward zero demand `(zero, none)` of every method (§9.2). So a method key that THE EXCLUSION (§6.6) excludes is
      still analysed from the zero fact in every run. With only the zero demand it publishes nothing (no `D-p`, no
      result, `HandoffCases.restrictI_none`), so it hands off no demand edge and stays out; the callers use its records
      (§8.7 R4). In run 1 a zero-premise leaf that is not crossable is a demand edge (run 1 publishes every summary).
      In a restricted run a zero-premise summary is published only through a demand pattern `(zero, jb)` (from a
      backward summary `jb → zero` that is not crossable), so a zero-premise leaf that is not crossable (for example
      `zero → (ret, ., [any-taint], T)` from a source in the method: its reversed premise is `[any]`) is a demand edge
      only for a method key with such a pattern. The frontier log measures this work: the method keys that only the
      zero fact reaches (`analyzer-core.md` §7.8). It is a limit of the cost, not of the soundness.
    * THE SEED PATHS ARE NOT NARROWED. The narrowing theorem leaves out the zero demand and the patterns `(gb, none)`
      of the zero-premise backward edges (§9.2 case 2). As locations they shrink when the backward field limit grows
      (a larger limit cuts a requirement less), but their COUNT can grow.
    * THE EXCLUSION OVER SEVERAL ROUNDS (§6.6). Each round is the one-round theorem (`HandoffExclusion.exclusion_theorem`;
      with the `[any-taint]` exclusion its backward parts and `HandoffXMain.forward_zero_initX`, `forward_zero_edgesX`),
      and its hypothesis "no demand edge of `M`" holds again after the round (`HandoffCases.restrictI_none`); the
      composition over the rounds is not stated.
    * NO `*` DEMAND PATTERN WITH THE STATIC RULE AND THE CONJUNCTIONS (§6.4; the concrete design: since F72 the later
      runs have `*` patterns, but run 1 still hands off none). That run 1 hands off no `*` entry
      pattern is proved for `D` (`HandoffNoStar.handF_run1_nonstar`). With the static rule (`Statics.DS`) a position
      answer is `*` with the Empty exclusion and the mark `*`, so its `*` exit edges are crossable too; with the
      conjunctions an ND edge has no `*` tail (W7). Argued.
    * THE STOP RULE `STOP_RULE` (§6.6): with no DEMAND entry the next backward run has no seed, so every later forward
      run only repeats the zero fact and the records. Argued: `HandoffExclusion.zinv_all` for every method with no
      seed, then `HandoffExclusion.exclusion_demand` per method; the composition is not stated. (That every real
      vulnerability is CONFIRMED at that stop is proved, §6.6.)
    * THE STOP RULE `NO_DEMAND_EDGE` (§6.6): in a complete forward run with no demand-layer edge, no demand-layer
      summary and no demand link, every sink witness and every link is normal, so each DEMAND entry fails only the
      joint support of §4.9 condition 3 (a conjunction). Argued from the conditions of §4.9 and the premises of a
      normal edge (`RExact.complete_premise_exact`, `AnyTaintExKinds.DRX_normal_premise`); no Lean theorem states it.
      A demand link must count: a call cleaner can demote an `[any-taint]` bound fact to `[any]` on its link (§2.2),
      the emission `[any] ∩ $ = $` then gives a premise that starts normal (§6.5), and every edge of the callee is
      normal, but the sink fails condition 3.2.2. A later run with a larger backward field limit can give the caller a
      `$` premise whose bound fact is apart from the cleaner: its link is normal, and that run confirms the sink. So
      without the demand links the rule stops too early. OPEN QUESTION: in such a run, if a premise set of a sink witness
      has no call that supplies every member, does no later forward run (a narrower demand, a larger field limit, more
      records) have such a call for a sink witness of the same key? No counterexample is known (with every link
      normal, an emitted member equals its added fact or lies inside a normal `[any-taint]` link, so a call that
      supplies the set in a later run supplies it in this run too), but a restricted run with ND edges is not modelled
      (above). So the rule does not claim that the report is final; its DEMAND entries stay in the output (§8.10).
    * THE TREE FORM AND THE INDEX OF THE INTERSECTION (§7.4, §8.6): the model proves them for the earlier restriction
      (`RStore.restrictTreeE_mem_U`, `restrictTree_cost`, `restrict_complete_U`); the meet at the node of `D-p.path`,
      the exclusion `E2` on a moved `[any-taint]` leaf, the inside test of the premise, and the mark tests of F71 (the
      premise key in its marks, the mark leaves against the mark of `D-p`, §7.4) are argued. So is the
      claim that the pieces that the run stores at each summary delta are the publications of the non-crossable
      leaves (§8.5: the restriction acts leaf by leaf).
    * PROGRAMS 1 AND 2 (§6.3, §6.4, §9.2): that the hand-off of the demand edges of backward run 2 is EXACTLY the three
      parts of §9.2 is checked by hand. The model proves that it contains the callee patterns and that forward run 3
      reports the vulnerability (`HandoffRCases.p1_handoff`, `p2_handoff`, `p1_chain`, `p2_chain`). PROGRAMS G AND C
      of the `[any-taint]` tail (§0.1, §4.9) with the intersection and the hand-off of the demand edges: the Lean runs
      use the earlier restriction and hand-off (`AnyTaintExCases2.G.run3_confirmed`, `C.run3_confirmed`). On these
      programs the two give the same cells (the must-premise lies inside its `D-c`, and `[any-taint] ∩ [any]` keeps
      `[any-taint]`), and the run-1 summary of the getter is in the demand layer, so it is a demand edge: checked by
      hand. The same for run 3 of program B (`AnyTaintExCases.B.run3_anyE_confirmed`, with a demand written by hand).
    * A DEMAND PIECE BESIDE A CROSSABLE PIECE (a cost limit). The normal and the demand trees of one premise key are
      separate edges, and no subsumption crosses the layers (§8.1). So a demand-layer piece whose pairs a crossable
      piece of the same premise and of the same demand pattern already has (a may next to an exact write:
      `M(p) { t.f = p; wrapInto(t, p); return t; }`, with `wrapInto` a may into `t.[AnyField]`, under the exit
      pattern `(ret, .f, $, T)`) is still a demand edge. The backward run enters the callee for it, the reversed may
      gives a demand backward leaf (case 3), and the callee stays in the frontier while the seed exists. Cost only. A
      rule that drops such a piece in the hand-off needs a Lean variant of `HandoffBackward.seg_genN` (later).
  * THE ZERO-BASE AND KIND INVARIANTS OUTSIDE `NDZ.DNz`. (a) In `DR` and `Backward.DB`, every conclusion on the zero
    base is the zero fact (proved for `NDZ.DNz`: `NDZeroBase.zero_base_inv`). The only edges onto the zero base are
    the zero keep edge, the zero binding and, in the backward run, the reversed sources and end-fact actions, whose
    target is the zero fact (`interpreter.md` I11 (d)). (b) The §7.2 partition for a one-member `NDZ.DNz` edge: a
    conjunction target (W7) over a concrete premise (S9). (c) The zero fact is at every node of a restricted run (the
    zero demand, §9.2), as the zero-drop needs.
  * The static exception at a call and at the method boundaries (§4.10 item 1): the rule statement of a call, the
    unresolved callee (also a call whose every callee is an empty method), the `RemoveAllMarks` kill on `S`, and the
    rule statements of the entry and the exits are read as `Instr.stmt` of the model's CFG, in the caller or before
    the exit; the binding `S.* → S.*` keeps the path.
  * A conjunctive micro edge whose target is a class position (`interpreter.md` §1.4; S12 (b)) has a `$` target and
    concrete `$` literals. Its result is a concrete `$` fact of the S12 (b) shape, so it keeps the static invariant.
    (`Statics.DS` has no conjunctions, and `ND.DN` has no static rule.)
  * THE `[any-taint]` TAIL (§2.3 W8, §10.11) outside the proved spec closures `AnyTaintEx.D6X` and `AnyTaintEx.DRX`
    with the spec rules (`emitX`, `satX`, `HandoffX.restrictIX`; and `AnyTaintEx.DRXs` with the earlier restriction)
    (and outside `AnyTaintND.DNzT`). (The kinds invariant of `AnyTaintEx.D6X` and the premises of a normal
    `AnyTaintEx.DRX` edge are proved, `AnyTaintExKinds.kinds_D6X`, `DRX_normal_premise`, `DRXs_normal_premise`, and so
    are the results of the round-1 programs G, C, I and P in the closures with the earlier restriction,
    `AnyTaintExCases2`; §10.11. The hand-off of the demand edges and the intersection with the exclusion are PROVED
    for these closures, not argued: the restriction, the coverage, the narrowing of one hand-off
    (`HandoffX.handF_narrowX`) and of one round (`HandoffXMain.narrowing_canonX`, `HandoffNoStar.narrowing_canonX_loc_exact`),
    the exclusion (`HandoffXMain.exclusion_roundX`, `exclusion_canonX`), the iteration (also with the source seeds and
    in the finite form) and the driver, §10.12.)
    * W6T and the exclusion in run 1 with the static rule (`Statics.DS`): the static rule does not read the layer or
      the exclusion of an any-tail fact, and `Statics.no_any_above` covers both any tails (§4.10), so W6T only raises
      layers, as W6 does, and an exclusion only removes locations that no flow reaches. The mark answer on a static
      premise drops the exclusion of an `[any-taint]/E` added fact (§4.10 item 4): a larger premise.
    * W6T and the exclusion with the conjunctions: `AnyTaintND.DNzT` has the conjunction rule of §4.6 but neither
      W6T nor the exclusion. W6T on top of it is a layer raise of the results of the may `[any]` targets: it removes
      normal edges and adds no fact. With the exclusion the store keeps an `[any-taint]/E` input only if its ADMITTED
      part overlaps the literal (§3.2, §4.6), and every admitted location carries the mark, so the step of
      `AnyTaintND.lit_loc` holds on the admitted part.
    * THE BACKWARD W6 WITH THE REVERSAL OF A MAY AND OF A CONJUNCTION (§9.1, §9.2): every `[any]` result of the
      backward run, and every result of the reversal of a micro edge whose forward target is `[any]` or of a
      conjunctive micro edge, is in the demand layer. This is not a
      pure layer raise in `Backward.DB`: a demoted requirement can reach the zero fact as a demand zero fact, and
      `Backward.DB` reads the normal zero fact. But wherever such a requirement of a zero premise reaches the zero
      fact, the normal zero edge of the zero premise is already at that node (the rule `start`, `Backward.ZeroKept`,
      the rule `zpass` from the seed node), and the hand-off and `FSeeds.srcHit` read every layer (a demand-layer
      backward leaf is always a demand edge, §9.2; the earlier `Backward.demOf` read every edge). So the rule only
      removes normal backward edges: it only removes records (a crossable leaf that it demotes becomes a demand edge),
      and it keeps the demand and the source hits.
    * Merge rule 2, the subsumption, T5 and the key of a TAINT tree with the exclusion (§3.3, §7.2, §8.1; in a normal
      TAINT tree no `$` leaf is absorbed or subsumed under an `[any-taint]` leaf), and the tree restriction with the
      exclusion (§7.4): the model has the per-path forms only (`AnyTaintEx.XFact`, `HandoffX.restrictConcIX`; the
      earlier `AnyTaintEx.restrictConcX`). Each one keeps the location set.
    * The seeded forward runs with the exclusion: the soundness is proved for both hand-offs (the earlier
      `AnyTaintExCov.iteration_srcX`; the hand-off of the demand edges `HandoffSrc.iteration_srcNX`,
      `iteration_srcNX_upto`, for the driver `PipelineHandoffDriverExt.driver_iteration_srcNX`); the exactness and the
      confirmation of a seeded run are argued as for the runs without the exclusion (above).
    * The reversed records across the directions with the exclusion (§8.7 R3): R3 reverses leaf by leaf, and not a
      leaf of a must record or an `[any-taint]/E` leaf with `E ≠ {}`; every other leaf reverses as before F69 (the
      model kind `.any`, `Reverse.rev_exact_of_empty_premise`). The induction over the directions is argued with the
      other record items.
    * `[any-taint]` in a restricted run with ND edges: as the other ND items of this list (the conjunction rule of
      §4.6 is proved for run 1 only, `AnyTaintND`).
    * The cleaners of a call and the summary rewriter (§4.7) on an `[any-taint]/E` fact: as the call-cleaner item
      above. Their rows are the rows of §4.7 (Lean `AnyTaintEx.cleanResX` for a cleaner of the CFG); the rewriter
      cleans an `AnyField` position of a selected source with `atAndBelow` (`interpreter.md` D34), and an `AnyField`
      position of a selected cleaner with its cleaner row `below` (`interpreter.md` §5.2).
    * The pipeline dominance: no instance of `Pipeline.quiescent_dominates` for `PipelineAnyTaintEx.sysD6X` and
      `sysDRX`, as for `PipelineAP` (`analyzer-core.md` §12).
    * The necessity of `AnyTaintEx.SatInsideX` for the rule `ret` (a summary, not a record): the round-1
      counterexample `AnyTaintExact.CexApp` shows it for a record; for a summary it needs a second call site.
* THE IMPLEMENTATION AGAINST THE MODEL. This is the only list of these differences. Each one keeps the theorems,
  except where the item says otherwise:
  * THE ANY TAILS, W6 AND W8 (§2.3; F69). The model has one tail kind `.any` for both any tails. The correspondence
    (Lean `AnyTaintDefs.lean` and `AnyTaintExDefs.lean`, their headers):

    | spec | model |
    |---|---|
    | `*/E` | `.star e` |
    | `$` | `.exact` |
    | an `[any]` conclusion (a may) | `.any` in the demand layer, with no exclusion |
    | an `[any-taint]/E` conclusion (a must) | `.any` in the normal layer, with a concrete mark and the exclusion `ex = E` (`AnyTaintEx.XFact`, `carriesB`, `normX`) |
    | an `[any-taint]/E` premise (a must-premise) | a premise with the flag `must = true` and the exclusion `jex = E` (`AnyTaintEx.XObj`, `startX`; round 1 `AnyTaint.TObj`, `startT`) |
    | a demand pattern | a `PFact` (`DemandEdge`): the hand-off drops the exclusions and the must flags (`AnyTaintExCov.forget6`, `forgetX`; the publication of an X run `HandoffX.pubRX`), so no pattern has the `[any-taint]` tail (§9.2) |
    | a summary leaf, a crossable leaf, a demand edge (§1) | an exit edge `j → g` of the model (one premise, one path conclusion); `Handoff.Cross j g` (a backward leaf: `Handoff.CrossB jb gb`); an element of `Handoff.handF` or `Handoff.demOfN` (a `DemandEdge`) |
    | a taint edge (S15) | a micro edge with `taint e = true` (`AnyTaint.TaintEdges`) |

    The Lean `applyEdge` gives a normal `.any` result on a normal `.any` input, or for an `.any` target on an exact
    derivation: that is the spec `[any-taint]`, and `Exact.edge_exact` proves it exact. The base model demotes a normal
    `.any` fact where an exclusion meets it (`belowCase` with a non-empty exclusion, `aboveCase`); the refined model
    replaces these demotions by the exclusion (`AnyTaintEx.annX`, `layerX`) and keeps the other demotions, the list of
    §2.2 (the cut `limitFX`; the `part` rows of `AnyTaintEx.partX` other than the `atAndBelow` and `below` cleaners one
    accessor below the fact; a may target, `w6tX`; a demand input, as the layer only rises; the record demotion
    `recLayerX`), and the start of an `.any` premise that is not a must-premise. The refined closures are proved on
    their own (§10.11); they are related to the round-1 closures by the simulations `AnyTaintExKinds.sim6X` and `simRX`
    (under `AnyTaintEx.NoBelowCleaner`), which no spec claim needs. They are not a layer refinement of `D` and `DR`:
    an exclusion removes locations, and the `below` cleaner one accessor below an `[any-taint]` fact adds the fact `(x, q.f, $, T)`, which the base model does not have
    (`AnyTaintEx.Vec.below_new_fact`; it is real, `AnyTaintExExact.below_new_fact_real`). The implementation puts only
    the result of a MAY `[any]` target in the demand layer (§4.1 step 6; the rule W6T, `AnyTaint.w6t`,
    `AnyTaintEx.w6tX`), and it names a demand `.any` result `[any]` (W8 (b)). In the round-1 closures W6T only moves
    edges from the normal layer to the demand layer. Soundness ignores the layer, and exactness and confirmation hold
    for every subset of the normal edges (`Invariant.demand_of_any_ok`). For the whole run, `AnyTaint.D6T` has the facts
    of `D` (`AnyTaintSim.D_le_D6T`, `D6T_le_D` under `W6.SummaryStar`), and `AnyTaint.DRT` has the facts of `DR`
    (`AnyTaintSim.factSim` under `EmitCopiesMark` and `AnyTaint.RestrictFact`). With an abstraction outside the spec,
    W6T can change a fact, not only its layer (`AnyTaintSim.CexT.cex_w6t_changes_fact`). THE OLD RULE W6 (every `[any]`
    result in the demand layer) is the record of `W6.lean` (§10.3: `W6.D6_le_D`, `D_le_D6`, `W6.DR_le_DR6`,
    `DR6_le_DR`; `W6.Cex.cex_w6_changes_fact`); every normal edge under it is a normal edge under W6T
    (`AnyTaintSim.D6_normal_D6T`). The backward run keeps W6 for every `[any]` result: argued (the list above). The
    Lean predicate `AFact.complete` (normal, and no `.any` conclusion) is the reading of a normal edge of the backward
    run only, which has no `[any-taint]` and keeps its `[any]` results in the demand layer (§1;
    `AnyTaintSim.backRecT`, `DB_any_premise_demand`). A normal forward edge of the spec is `demand = false` in the
    model, also with the `[any-taint]` tail; its records are the records with must flags and exclusions of §10.11
    (`AnyTaintEx.RecsExactX`, end-exact for a must record).
  * THE EXCLUSION IN THE TESTS OF §3.4. `covers`, `overlap`, `applicable` and `inside` read the exclusion of an
    `[any-taint]/E` fact or premise. The model reads it in `AnyTaintEx.satX`, `overlapX`, `checkX`, `emitX`,
    `restrictX` and the spec restriction `HandoffX.restrictIX` (its premise test `HandoffX.insideLocXB`), but its rule
    `ret` of run 1 and its rule `retRec` test the base `applicable`, and its rule `answer` of run 1 the base `overlapB`,
    without the exclusion of the added fact. So the implementation applies fewer records and makes fewer answers: one
    that the exclusion rejects has no admitted location in common with the added fact, and the coverage of the refined
    runs needs only the admitted locations (`AnyTaintExCov.coverage6X`; a crossable record that the exclusion rejects
    has no admitted location to carry, `HandoffX.cross_appliesX`). For the run-1 policy fact (the Empty
    exclusion) both tests are equal. Argued.
  * Universe (§1). The model keeps the exclusion `Excl.univ`: it encodes a `$` premise in the operation tables
    (`tailExcl`). The AP has no Universe exclusion (S8).
  * The preconditions of `concat` (§4.1). The model computes a result for an edge that breaks S7 or S8; the
    implementation asserts that no such edge exists.
  * The cleaner request (§4.7). The model `cleanRes` also raises the request `T` for a `*∖X` fact with `T ∈ X` (the
    first row of the result table). The implementation does not raise it: an answer for `T` only makes facts that an
    earlier cleaner already cleaned, so the request costs work and adds nothing.
  * The effective mark of the sink check (§4.9). The model `check` reads the effective mark (§1), so it also triggers
    for an abstract `f.mark` under a concrete `i.mark`. This case does not occur (`Coverage.edge_conc`); the
    implementation asserts it.
  * The type filters of the backward run (§9.2). The model keeps the type filters in the backward run; the
    implementation drops them. This only adds backward flows, so it only enlarges the demand, and its reversed records
    are not exact (§11.1).
  * End facts (§4.9). The model has none. Their exactness: §11.1. Their coverage: argued (above).
  * The field limit on a conjunction result (§4.6). The model rules `ND.DN.conj` and `NDZ.DNz.conj` apply no field
    limit to their result. The implementation applies it: it only enlarges (`limitF_sound`) and raises the layer.
* The interpreter (`interpreter.md`) is outside the model, except through S1, S2, S5 and S7 to S13. Its known gaps are
  listed in `interpreter.md` §0.1. The reading of a negated mark literal as true (S1) is not modelled: the model has no
  rule conditions.
* Exceptions are out of scope: no exception flow crosses a call, and a catch block does not read `exc`
  (`interpreter.md` §3.4, G1).
* The tree theorems cover the `*`-to-`*` micro edges with the mark `*` on both sides; other micro edges use the per-path
  operation on the touched subtree. The mark gate and the field limit inside the tree (§7.3) and the T5 fold are not
  modelled in `Tree.lean`.

---

## 12. The formal model

| File | Content |
|---|---|
| `Basic.lean` | The definitions of the run-1 closure `D` (no static rule, no conjunctions; `policy1` is in `Restricted.lean`): locations, facts (marks `*`, `T`, `*∖X`), `den`, `applyEdge` with `markComp`, the normal form, the field limit, statements, calls, cleaners (`Cleaner`, `cleanPos`, `cleanRes`), type filters, `Flow`, the closure `D`, `Reach`, `answerInit`, `policy`, `revEdge`. |
| `Backward.lean` | The backward run (`DB`), the earlier hand-offs, the contract B for it (general and for programs 1 and 2). |
| `Statics.lean` | The static rule of §4.10 as the run-1 closure `DS`: soundness, exactness, the invariant, the worked programs, the failing variants. |
| `StaticsIter.lean` | No static rule after run 1: the invariant of forward restricted runs, the iteration from `DS`, the worked programs through forward run 3. |
| `NDConfirmed.lean` | The confirmation through a conjunction (joint support), with its counter-examples. |
| `StaticsConfirmed.lean` | The confirmation of run 1 with the static rule. |
| `BackwardExact.lean` | The backward run: concreteness, no request, exactness of its edges, exact reversed records; record exactness over the run sequence; the static invariant of the backward run. |
| `W6.lean` | W6 for the whole run: the simulation, soundness, exactness, confirmation, the iteration. |
| `Restricted.lean` | The restricted runs: demand patterns (`DemandEdge`), the emission `emitM`, the satisfaction `satI`, the earlier restriction `restrictU` (the spec restriction `Handoff.restrictI` is in `HandoffDefs.lean`), the closure `DR`, `FlowR`, `ReachR`, the contracts, `summaryDemand`, `BackwardContract`, and auxiliary rules that some proofs use (for example `restrictS`, §10.7). The version-3/4 rules `emitU`, `emitS`, `satU`, `satS`, `satO` and their theorems (`RMain.*_S`, `RMain.closed_records_exactR`) are a record of the review; no spec claim uses them. |
| `ND.lean` | ND edges: conjunctive micro edges, the support semantics `TaintN`, the closure `DN`, the ND coverage and vulnerability theorems. |
| `NDExact.lean` | The exactness of normal-layer ND edges against `ND.TaintN` (`NDExact.LitConc` = S9, `ConjOK`), with the two counterexamples. |
| `Cases.lean`, `RestrictedCases.lean` | Test vectors (`decide`), programs 1 and 2. |
| `Core.lean`, `SharedExcl.lean`, `RestrictedCore.lean` | The local lemmas. |
| `Coverage.lean`, `RestrictedCoverage.lean`, `RestrictedMain.lean` | Soundness of run 1 and of the iteration; the instantiation with the earlier restriction `restrictU` (§10.7). |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `RestrictedExact.lean` | Exactness, invariants, the records of a request-free initial fact, confirmed vulnerabilities. |
| `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean` | Concept against optimization. |
| `Reverse.lean` | Reversal. |
| `ForwardSeeds.lean`, `PipelineSeeds.lean` | The source seeds of the forward restricted runs (§6.1 rule 6, §9.2, §10.9). |
| `Kinds.lean` | The conclusion kinds of §7.2: FLOW, TAINT, REACH; ND edges are TAINT (§10.10). |
| `NDZ.lean`, `NDZero.lean`, `NDZeroThms.lean`, `NDZeroBase.lean` | The ND closure of the spec with the zero-drop (`NDZ.DNz`), its correspondence with `ND.DN`, its theorems, and the zero-base invariant (§4.6, §10.10). |
| `PipelineNDZ.lean` | The pipeline encoding of `NDZ.DNz` (`analyzer-core.md` §5.5). |
| `Pipeline.lean`, `PipelineProofs.lean`, `PipelineAP.lean`, `PipelineStore.lean`, `PipelineDriver.lean` | The analyzer pipeline of `analyzer-core.md` (its §12): the no-loss theorem, the encodings of the closures, the index lookups, the driver. |
| `AnyTaintExDefs.lean` | THE SPEC CLOSURES of the `[any-taint]` tail with its exclusion (§2.3 W8, §10.11), definitions in the namespace `AnyTaintEx`: the annotated fact `AnyTaintEx.XFact` (`carriesB`, `normX`), the location tests with the exclusions (`coversX`, `coversFX`, `denX`, `overlapX`, `insideExB`, `satX`), the refined operations (`annX`, `layerX`, `applyEdgeX`, `applySummaryX`, `w6tX`, `transferX`, `limitFX`, `cleanPosX`, `partX`, `cleanResX`, `checkX`, `startX`, `recLayerX`, `emitX`, `emitTX`, the earlier restriction `restrictX`), the closures `D6X` (run 1), `DRX` and `DRXs` (a forward restricted run; `DRX` with the spec restriction `HandoffX.restrictIX` of `HandoffXRestrict.lean` is the spec run), the relations to the round-1 closures (`Refines6`, `RefinesR`, `Sim6X`, `SimRX`, `NoBelowCleaner`, `RecsRefine`: statements; `AnyTaintExKinds.lean` proves the simulations), the predicates of the proofs (`EdgeOKX`, `EndExactX`, `RecsExactX`, `SatInsideX`, `EmitCopiesMarkX`, `SupLinkX`, `SupX`, `Confirmed6X`, `ConfirmedX`), the vectors `AnyTaintEx.Vec`. |
| `AnyTaintExCov.lean` | The soundness of the spec closures: the local soundness, the contracts with the exclusions, the coverage of run 1 and of a restricted run, the iteration (`AnyTaintExCov.iteration_reportsX`, `iteration_srcX`), the counterexample `AnyTaintExCov.CexRoute`. |
| `AnyTaintExExact.lean` | The exactness of the spec closures (pair-exact, and end-exact for a must-premise, on the admitted locations), the records, the support and the confirmation; the run sequence; the counterexamples `AnyTaintExExact.CexAbove`, `AnyTaintExExact.CexExactCleaner`, `AnyTaintExExact.CexRestrictSub`, `AnyTaintExExact.CexSideConditions`. |
| `AnyTaintExCases.lean` | The worked programs of round 2: S, SD, B, X, R, CL, CUT (§10.11). |
| `AnyTaintExKinds.lean` | The kinds invariant of the spec run 1 (`AnyTaintExKinds.D6X_any_conc`, `D6X_flow_no_any_taint`, `D6X_flow_no_excl`, `kinds_D6X`, `kinds_D6X_gen`), the premises of a normal edge of a spec restricted run (`AnyTaintExKinds.DRX_normal_premise`, `DRX_must_premise`, `DRXs_normal_premise`, `DRXs_must_premise`), and the simulations of the refined runs by the round-1 runs (`AnyTaintExKinds.sim6X`, `sim6XIn`, `simRX`, `simRXIn`) (§2.3, §7.2, §9.1, §10.11). |
| `AnyTaintExCases2.lean` | The round-1 worked programs G, C, I and P re-derived in the spec run 1 `AnyTaintEx.D6X` and in `AnyTaintEx.DRXs` (the earlier restriction), and the carry-over of a run with no exclusion edge (`AnyTaintExCases2.Carry`) (§4.9, §6.2, §6.3, §10.11). |
| `PipelineAnyTaintEx.lean` | The pipeline encodings of `AnyTaintEx.D6X` and `AnyTaintEx.DRX` (`analyzer-core.md` §12). |
| `PipelineAnyTaintExDriver.lean` | The iteration driver over the encodings of `AnyTaintEx.D6X`, `Backward.DB` and `AnyTaintEx.DRXs`, with the earlier hand-off. |
| `AnyTaintDefs.lean` | ROUND 1 (the `[any-taint]` tail without the exclusion: the model of the first F69 text, §10.11), definitions in the namespace `AnyTaint`: the taint edges and S15 (`AnyTaint.TaintEdges`, `TaintConc`), `BindNoAny` (S10), the rule W6T (`w6t`, `transferT`), the closures `D6T` (run 1) and `DRT` (a forward restricted run with must-premises: `TObj`, `emitT`, `startT`, `recLayer`), the predicates of the proofs (`EndExact`, `EdgeOKT`, `RecsExactT`, `SatInside`, `SupLink`, `SupT`, `ConfirmedT6`, `ConfirmedT`), the vectors `EmitVec` and `Sanity`. |
| `AnyTaintSim.lean` | ROUND 1: the soundness by simulation (run 1 against `D`, a restricted run against `DR`), the kinds invariant, the iteration, the backward `[any]` premises and the backward records. |
| `AnyTaintExact.lean` | ROUND 1: the exactness (pair-exact, and end-exact for a must-premise), the records, the support and the confirmation of `AnyTaint.D6T` and `AnyTaint.DRT`; the run sequence; the counterexamples. |
| `AnyTaintND.lean` | The conjunction rule of §4.6 for an `[any-taint]` input (`AnyTaintND.DNzT`, without W6T and without the exclusion): simulation, coverage, exactness, confirmation, the worked example. |
| `AnyTaintCases.lean` | ROUND 1: the worked programs G, C, W, P, I, S and the cut (§10.11; S with the demotion that the exclusion replaces). |
| `PipelineAnyTaint.lean` | ROUND 1: the pipeline encodings of `AnyTaint.D6T` and `AnyTaint.DRT` (`analyzer-core.md` §12). |
| `PipelineAnyTaintDriver.lean` | ROUND 1: the iteration driver over the encodings of `AnyTaint.D6T`, `Backward.DB` and `AnyTaint.DRT`. |
| `HandoffDefs.lean` | THE HAND-OFF OF THE DEMAND EDGES (decision F70; §6.4, §9.2, §10.12), definitions in the namespace `Handoff`: the restriction as an intersection, mark-aware since F71 (`restrictI`, `insideB`, `insideLocB`, `concMarkB`, `restrictConcI`, `meetConcK`), the crossable records (`CrossK`, `Cross`, `revRec`, `CrossB`), the publications (`Pub`, `pubD`, `pubR`), the hand-offs (`handF`, `demOfN`), the witnesses (`FlowRR`, `ReachRR`, `FlowRDN`, `ReachRDN`) and the contracts (`CoversN`, `BackwardContractN`). |
| `HandoffRestrict.lean`, `HandoffCoverage.lean` | The restriction (C5, the intersection and its exceptions, the narrowing of one run, each also with the marks of F71, the vectors `Handoff.RVec`) and the coverage of the restricted forward run and of run 1 (§10.12). |
| `HandoffBackward.lean`, `HandoffIter.lean`, `HandoffMain.lean` | The backward contract of the backward run with the new hand-off; the abstract iteration; the canonical run sequence, the iteration theorem, the exclusion and the narrowing on it (§6.6, §10.12). |
| `HandoffExclusion.lean` | The exclusion theorem: a method key with no demand edge and no seed below is analysed only from the zero fact (§6.6, §10.12). |
| `HandoffCases.lean` | The program WRAP (the earlier hand-off against the new one), the CEGAR of `Cross` (programs ANYW and ANYM), a getter (§6.6, §8.7 R3, §10.12). |
| `HandoffXRestrict.lean`, `HandoffXCoverage.lean`, `HandoffXIter.lean`, `PipelineHandoffDriver.lean` | The hand-off of the demand edges on the closures with the `[any-taint]` exclusion: the restriction `HandoffX.restrictIX`, the coverage, the iteration, the driver with every reported vulnerability seeded (§10.12). |
| `HandoffXMain.lean` | The exclusion and the narrowing over one round on the closures with the `[any-taint]` exclusion (§6.6, §10.12). |
| `HandoffNoStar.lean` | No demand pattern has a `*` tail, so the narrowing is exact (the base and the X sequence); W2 of the backward run (§2.3, §6.4, §6.6, §10.12). (The concrete design: since F72 the later runs have `*` patterns, §11.2.) |

THE MODEL OF F72 IS NOT COMPLETE (§11.2, PENDING: THE LEAN MODEL OF F72). The planned files are `AbsDefs.lean` (the
definitions; in progress), `AbsCases.lean` (the CEGAR programs) and the files of the lemmas L1 to L6 and of the
iteration. No claim of this spec rests on them yet. Every file above that models a restricted run models the concrete
design of F70 and F71.
| `HandoffSrc.lean`, `HandoffUpto.lean`, `HandoffRCases.lean` | The source seeds with the hand-off of the demand edges (contract B item 3, the iteration, base and X); the finite forms; programs 1 and 2 with the intersection (§6.3, §6.4, §6.6, §9.2, §10.12). |
| `PipelineHandoffDriverExt.lean` | The driver with the seeds of the DEMAND entries only, its finite form and its source seeds (§6.6, §10.12). |

Lean names. A qualified name `F.x` in this spec names the declaration `x` in the namespace `ApSpec.F`, or in the file
`F.lean`. The short namespaces: `RCore` is `RestrictedCore.lean`, `RCov` is `RestrictedCoverage.lean`, `RExact` is
`RestrictedExact.lean`, `RMain` is `RestrictedMain.lean`, `RCases` is `RestrictedCases.lean`, `RStore` is
`RestrictedStore.lean`, `BExact` is `BackwardExact.lean`, `FSeeds` is `ForwardSeeds.lean`, and `CoreAux` is in
`Core.lean`. The declarations of `Basic.lean`, `Core.lean` and `Restricted.lean` are in the namespace `ApSpec` itself
(for example `applyEdge`, `satI`, `emitM`, `restrictU`, `markMatchB`); `Core.x` names a declaration of `Core.lean`.
Two files share the namespace of another file: `NDZeroThms.lean` is in the namespace `NDZero` (so `NDZeroThms.x` is the
declaration `NDZero.x` of the file `NDZeroThms.lean`), and `PipelineProofs.lean` is in the namespace `Pipeline` (with
the sub-namespaces `Pipeline.PCex` and `Pipeline.Quiesce`). `Cases.lean` has the namespaces `Cases` and `CleanCases`.
`AnyTaintDefs.lean` is in the namespace `AnyTaint` (so `AnyTaint.x` is a declaration of `AnyTaintDefs.lean`; no file
`AnyTaint.lean` exists), and `AnyTaintExDefs.lean` is in the namespace `AnyTaintEx` (so `AnyTaintEx.x` is a
declaration of `AnyTaintExDefs.lean`; no file `AnyTaintEx.lean` exists). `HandoffDefs.lean`, `HandoffRestrict.lean` and
`HandoffCoverage.lean` are in the namespace `Handoff` (with the sub-namespaces `Handoff.RVec` and `Handoff.RAux`; no
file `Handoff.lean` exists), and `HandoffXRestrict.lean` and `HandoffXCoverage.lean` are in the namespace `HandoffX`
(with the sub-namespaces `HandoffX.XVec` and `HandoffX.XAux`; no file `HandoffX.lean` exists). This spec writes the
declarations of these five files with their namespace: `Handoff.restrictI_sub` is the declaration `restrictI_sub` of
`HandoffRestrict.lean`, and `HandoffX.restrictIX_ok` is the declaration `restrictIX_ok` of `HandoffXRestrict.lean`.
`HandoffCases.lean` has the sub-namespaces `HandoffCases.Wrap`,
`VecCross`, `AnyW`, `AnyM` and `Getter`; `HandoffSrc.lean` has `HandoffSrc.SrcRec`, `HandoffXMain.lean` has
`HandoffXMain.XMVec`, and `HandoffNoStar.lean` has `HandoffNoStar.NSVec`. Every other file has the namespace of its name
(`Statics`, `StaticsIter`, `StaticsConfirmed`, `Backward`, `Reverse`, `ND`, `NDExact`, `NDConfirmed`, `NDZ`, `NDZero`,
`NDZeroBase`, `Kinds`, `W6`, `Store`, `Subsume`, `Tree`, `Pipeline`, `PipelineAP`, `PipelineStore`, `PipelineDriver`,
`PipelineSeeds`, `PipelineNDZ`, `AnyTaintSim`, `AnyTaintExact`, `AnyTaintND`, `AnyTaintCases`, `PipelineAnyTaint`,
`PipelineAnyTaintDriver`, `AnyTaintExCov`, `AnyTaintExExact`, `AnyTaintExCases`, `AnyTaintExKinds`,
`AnyTaintExCases2`, `PipelineAnyTaintEx`, `PipelineAnyTaintExDriver`, `HandoffBackward`, `HandoffIter`,
`HandoffExclusion`, `HandoffMain`, `HandoffCases`, `HandoffXIter`, `PipelineHandoffDriver`, `HandoffXMain`,
`HandoffNoStar`, `HandoffSrc`, `HandoffUpto`, `HandoffRCases`, `PipelineHandoffDriverExt`, and so on). The sub-namespaces of the
`[any-taint]` files: round 2: `AnyTaintEx.Vec`; `AnyTaintExCov.CexRoute`; `AnyTaintExExact.CexAbove`,
`CexExactCleaner`, `CexRestrictSub`, `CexSideConditions`; `AnyTaintExCases.S`, `SD`, `B`, `X`, `R`, `CL`, `CUT`;
`AnyTaintExCases2.G`, `C`, `I`, `PassRule`, `Carry`; round 1: `AnyTaint.EmitVec`, `AnyTaint.Sanity`;
`AnyTaintSim.CexKinds`, `AnyTaintSim.CexT`; `AnyTaintExact.CexApp`, `CexRev`, `CexSupMark`, `CexRecConc`;
`AnyTaintND.Example`; `AnyTaintCases.G`, `C`, `W`, `PassRule`, `Cut`, `I`, `S`. Some sub-namespaces have the same
name in two files (`AnyTaintCases.S` and `AnyTaintExCases.S`; `AnyTaintCases.G`, `C`, `I`, `PassRule` and
`AnyTaintExCases2.G`, `C`, `I`, `PassRule`; `Statics.CexAbove` and `AnyTaintExExact.CexAbove`): this spec writes them
with the name of their file. If neither `ApSpec.G` nor
the file `G.lean` has the declaration `x`, the name `G.x` is in the sub-namespace `G` of the namespace of the file of
the last qualified name before it: `CexWide.w_vuln_normal` after `Statics.CexAbove.y_vuln_normal` is
`Statics.CexWide.w_vuln_normal`, and `CexSeed.cex_seed` after `BExact.DB_no_requestM` is `BExact.CexSeed.cex_seed`.
A name with no qualifier belongs to the namespace or the file of the last qualified name before it, or to `ApSpec`
itself (for example `den`, `DR`, `applicable`). In the tables of §10, a name with no qualifier can also belong to a
file that the heading of its section names.

Build and audit:

```
cd spec/lean && rm -rf .lake/build/lib/lean/ApSpec* && lake build > build.log 2>&1
grep "depends on axioms" build.log | sed 's/.*axioms: //' | sort | uniq -c
grep -c "does not depend on any axioms" build.log
```

(A build prints the audit only for the modules that it compiles, so remove the old `ApSpec` build files first.)

The audit passes when the only sets are `[propext]` and `[propext, Quot.sound]` (and declarations with no axioms),
with no `sorry`, no `native_decide` and no `Classical`. The kernel checks the `example` vectors, almost all by
`decide`, and the derivations of the counterexample and example programs.

---

## 13. Test plan (TDD)

Write the tests first. Each test names the spec item that it checks. The interpreter tests are in `interpreter.md` §7.

1. Vector tests (`ApplyEdgeVectorsTest`): one test per `example` in `Cases.lean` and `RestrictedCases.lean`, on the
   concept implementation (§4.1 reference form) and on the tree implementation. These Lean files are the test data:
   each `example` gives the inputs and the expected result. Some vectors (the `lostCorr` vectors,
   and the §4.2 vector `a = b.f` on a normal-layer `(b, ., [any], {}, *)`) show the model result: an `[any]` result in
   the normal layer. The implementation applies W6T, so the test asserts the same fact in the layer of §4.1: in the
   demand layer for a may `[any]` target or an `[any]` input, and as a normal `[any-taint]` fact for a taint edge or a
   normal `.any` input with a CONCRETE mark; a `.any` input with the mark `*` (the §4.2 vector above) gives `[any]` in
   the demand layer (`Invariant.demand_of_any_ok`, §11.2). The vectors of the `[any-taint]` tail are test data too:
   the vectors of the exclusion `AnyTaintEx.Vec` (every vector: the keep edge, the reads, the case `above` with an
   edge exclusion, the cleaners, the cut, the emission, the start, the satisfaction, the summary, the restriction, the
   sink check, the case `below`), the `decide` vectors of `AnyTaintExCases.lean` (`AnyTaintExCases.X.two_results`,
   `AnyTaintExCases.R.reads`, `AnyTaintExCases.CL.clean_vectors`, `AnyTaintExCases.CUT.cut_ops`,
   `AnyTaintExCases.S.keep_forms`), the refined statement transfer of a source and of a pass rule
   (`AnyTaintExCases2.PassRule.source_vs_pass`), and the round-1 vectors without the exclusion: `AnyTaint.EmitVec`,
   `AnyTaint.Sanity` (a source result is a normal `[any-taint]` edge; the same micro edge as a pass rule is demand),
   `AnyTaintCases.PassRule.source_vs_pass`, `AnyTaintCases.Cut.cut_transfer`. The round-1 vector
   `AnyTaintCases.W.keep_demand` gives the demotion that the exclusion replaces: the test asserts
   `AnyTaintEx.Vec.setter_keep` instead.
2. Equivalence property tests (`EdgeTreeEquivalenceTest`): random path facts and micro edges; the tree result denotes
   the same pairs as the concept result, layer and mark exclusion included. The same for the tree restriction (§7.4).
   The tests of §3.4 (`covers`, `overlap`, `applicable`, `inside`) and `cleanPos` (§4.7) against the denotation of §3,
   on a bounded universe with a fresh accessor and a fresh mark.
3. Layer tests: a cut fact is in the demand layer; an `[any]` result is in the demand layer (W6); a demand-layer input
   gives a demand-layer output; a `*` conclusion is never in the demand layer; a `*` fact applied above a premise gives
   a demand-layer result. The `[any-taint]` tail (W8): a source with an `[any]` target gives a normal `[any-taint]`
   result, and the same edge as a pass rule gives `[any]` in the demand layer; every row of the two tables of §4.1 with
   an `[any-taint]/E` fact or target, also the case `above` of an `[any-taint]/E` fact (normal for a `$`, an
   `[any-taint]/Et` or a `*` target; the `*` target gives the edge exclusion; nothing if `E` does not admit the step).
   THE EXCLUSION ROWS (W8): the keep edge of a strong write gives `[any-taint]/(E ∪ {f})` in the layer of the input; a
   `*/E'` summary or record gives `[any-taint]/(E ∪ E')`; the case `below` keeps `E` at the new path end
   (`AnyTaintEx.Vec.below_keeps_loc`); a read through an excluded accessor gives nothing, through an admitted one
   `[any-taint]` with the Empty exclusion; a two-level write in one statement gives two normal results
   (`AnyTaintExCases.X`; a synthetic statement summary with the keep edges `x.* →_{f} x.*`, `x.f.* →_{g} x.f.*` on the
   AP, not a JVM statement: on the JVM `x.f.g = c` is `t = x.f; t.g = c`, the weak alias write of §11.1). THE
   DEMOTIONS to `[any]` with the Empty exclusion, every item of the list of §2.2: the cut (also with `L = 0`, program
   CUT, on the AP `limit`), every cleaner `part` row of §4.7 other than `atAndBelow` and `below` one accessor below the
   fact (the `exact` cleaner at and one accessor below the fact, a cleaner two accessors below), a may `[any]` target,
   a demand input (a demand-layer summary or record, a demand link, a demand conjunction input), the record demotion; a
   demand-layer `[any-taint]` result becomes `[any]` and drops its exclusion; the preconditions fail on an
   `[any-taint]` target or premise with the mark `*`; the `[any-taint]` rows of §4.2.
4. Mark tests: every row of the mark gate and of the result mark (§4.1 steps 4, 5); a `*∖X` summary conclusion stops an
   added fact with a mark in `X`; a sink for `T ∈ X` neither triggers nor requests; a request for `T ∈ X` does not
   climb; the preconditions of `concat` (§4.1) fail on a `*∖X` premise, on a concrete target mark under the premise
   mark `*`, on a `$` premise with the mark `*`, on a `$` premise with a `*` target, and on a `$` target under the
   premise mark `*`.
5. Cleaner tests: every row of the two tables of §4.7; the split (`*∖{T}` plus the request, then the concrete answer
   cleaned exactly); no request for `T ∈ X`; the all-marks cleaner; a cleaned fact through a field write past the field
   limit keeps its mark exclusion. The summary rewriter (§4.7): at a call it selects a conditional user-defined source
   and an unconditional user-defined cleaner, but not a conditional user-defined cleaner and not a rule that a rule
   error rejected; it acts on a zero-premise summary result and on the default identity of an unresolved callee; it
   cleans an `AnyField` position of a selected source with `atAndBelow` (`interpreter.md` D34), and an `AnyField`
   position of a selected cleaner with `below` (`interpreter.md` §5.2). The cleaner on an
   `[any-taint]/E` fact (§4.7): `atAndBelow` and `below` one accessor below the fact (normal, `E ∪ {f}`, and
   `(x, q.f, $, T)` for `below`), the `exact` cleaner there (demand `[any]`), a cleaner at an excluded accessor
   (`disjoint`, `AnyTaintEx.Vec.clean_excluded`), a cleaner two accessors below (demand `[any]`); the program
   `AnyTaintExCases.CL`.
6. Type filter tests: a fact on an accepted path passes, also with a `*` tail; a fact on a rejected path is dropped; the
   predicate is prefix-closed.
7. ND tests: a conjunction from two facts of different premises gives the union premise set; the last arriving fact
   completes it; a fact that only overlaps its literal enters the store and gives a demand-layer result, unless it is a
   normal `[any-taint]` fact (§4.6); an `[any]`
   literal (`ContainsMarkOnAnyField`) accepts a fact below its position; a summary with several premises needs one
   link per premise; ND conclusions have no `*` tail; a vulnerability through a conjunction is confirmed only if every
   premise of its sink edge is exact and the premise set is supported jointly at one call statement (§4.9 condition 3);
   the negative test `NDConfirmed.CexSites`: two premises supplied at two different calls are not confirmed. A
   conjunction of a zero-premise fact and a fact of the premise `i` gives the premise set `{i}` (the zero fact is
   dropped), and two zero-premise facts give `{zero}`. Today's `ExampleTest.test nd rule` as an analysis test. The
   `[any-taint]` rule of §4.6: a normal `[any-taint]` input that overlaps a `$` literal gives a NORMAL result, and the
   vulnerability is confirmed (`AnyTaintND.Example.layer_new`, `confirmed`); an `[any]` input gives a demand
   result; a conjunctive source with an `[any]` target gives an `[any-taint]` result; an `[any-taint]/E` input whose
   admitted part does not overlap the literal (the literal at an excluded accessor) is not stored.
8. Merge tests: rules 1, 2 and 2'; rule 2 for two normal TAINT trees with `[any-taint]` leaves of equal content
   (the intersection of the exclusions); a union of exclusions or mark exclusions is never made. T5 (§7.2): in a demand
   tree an `[any]` leaf absorbs the leaves below it with its mark; in a normal TAINT tree an `[any-taint]` leaf absorbs
   no `$` leaf: the example of §7.2 T5 (`{x: [any-taint] (T), x.g: $ (T)}`, then `clean(x.f, exact, T)`) keeps
   `x.g.$ (T)` in the normal layer (so a sink on `x.g` can be CONFIRMED), and the store (§8.1) does not subsume it.
9. Request tests (run 1): the mark gate raises a request; a standing request is answered by a later added fact and by a
   second added fact; a standing request reaches a second caller edge of an EXISTING added fact (the program of §4.5);
   propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain; every request
   premise is a policy fact `(x, [], *, {}, *)` or a static position answer `(S, p, *, {}, *)`. A restricted run has
   NO request rule (F72, §4.5): on a fact with the mark `*` (a fact of a FLOW premise), the mark gate of a concrete
   premise mark gives nothing, a literal stores nothing, a sink has no effect and a cleaner of `T` gives `*∖{T}`, each
   with no request; the request store of a restricted run stays empty. (Before F72 the test asserted that a
   restricted run never makes a request.)
   Position request tests (§4.10): on an identity static `*` edge at the root `[]` or a class, a static read, a Go global
   read, the class keep edge of a write, a pass rule between static fields and a conditional exit source whose literal
   is on a static field raise the position request (cut to the static field) and give no fact; a sink on `S` raises the ordinary mark request; a deep read below a static field is
   the ordinary case `above`; the root keep edge adds
   `<C>` to the exclusion; an added fact at or below the position answers it, an added fact above it does not; the
   climb through a caller edge on `S`; the mark answer on a static premise (item 4: the added fact itself at or below,
   the chain answer above); the programs `Statics.CexAbove`, `CexWide`, `CexClean`, `CopyF2F`, `DeepSink`, as
   analysis tests, find their vulnerability in the normal layer, and `DeepSinkParam` in the demand layer.
10. Call and ownership tests: every event of the table of §5.3, in two orders; the callee restricts before it publishes;
    a caller reads the summaries of every premise its fact satisfies; a record applies when its premise covers the added
    fact, in every run after the run that made it; the return order of §5.3 step 5; the zero fact passes over a call and
    enters every resolved callee. The must-premise (§4.3): a summary of an `[any-taint]` premise applies only by
    `inside`; through a demand `[any]` link its result is demand; a must record applied by `applicable` only gives a
    demand result with the same fact and no exclusion (the program `AnyTaintExact.CexApp`); `inside` reads the
    exclusions of the added fact and of a must-premise (`AnyTaintEx.Vec.sat_vectors`); a summary with an
    `[any-taint]/E` conclusion gives its exclusion to the result (`AnyTaintEx.Vec.summary_ann`).
11. Abstraction tests: run 1 emits the most abstract fact; every row of the three tables of §6.3 (every cell of the
    meet table: `AnyTaintEx.Vec.emit_at`, `emit_above_excluded`, `emit_above_exact`, `emit_below`; without the
    exclusion `AnyTaint.EmitVec`); the emitted fact is exactly `a ∩ D-c` with the mark of `a`; the same result for two
    insertion orders; no entry pattern has the `[any-taint]` tail (§9.2); a must and a may added fact at one path give
    two premise keys, and so do two must-premises with different exclusions (§7.1); a must-premise starts as itself,
    with its exclusion, in the normal layer (§6.5; `AnyTaintEx.Vec.start_must`); the backward run has no must-premise;
    a `*∖{T}` entry pattern emits nothing for an added fact with the mark `T` and emits for the mark `U`, with the
    premise inside the entry pattern with its mark (`Handoff.RVec.vEmit_starEx_T`, `vEmit_starEx_U`;
    `HandoffX.XVec.vM_emit`; the vectors of F71: since F72 no pattern has `*∖X`). THE EMISSION OF F72 (§6.3; PENDING
    the Lean model, §11.2): a `*` pattern `(x, .f, [any], *)` emits the FLOW form `(x, .f, *, {}, *)` for every added
    fact with a common location, and for the marks `T` and `U` it is ONE initial fact (SHARING); a `*/E` pattern
    emits itself with the mark `*`; a `*` pattern and an added fact with no common location emit nothing; a concrete
    pattern emits `a ∩ D-c` with the mark of `a`; an added fact with the mark `*` (or `*∖X`) under a concrete pattern
    emits NOTHING ("the added fact can't satisfy the demand"); the FLOW premise starts as the identity in the normal
    layer (§6.5); its summary applies by `inside` (the added fact above it) and by `applicable` (the added fact below
    it), and a summary of a concrete premise never applies to an abstract added fact (§4.3).
12. Restriction tests (the intersection, mark-aware, §6.4): every row of the table and every cell of THE MEET (the vectors
    `Handoff.RVec`: `v64_restrictI`, `vOverlap_restrictI`, `vNoExit`, every `row_*`; with the exclusions
    `HandoffX.XVec`: `v64_demand`, `v64_taint`, `v_taint_star`, `v_at_rows`, `v_above_rows`, `v_below_rows`,
    `v_overlap`, `v_inside_only_with_excl`); `[any]` against a `$` exit pattern gives `$`; a premise that only overlaps
    `D-c` gives no result, and a premise inside `D-c` (in its locations and its marks) keeps every pair whose exit
    location `D-p` covers with its mark; THE MARK TESTS (F71): the example of F71, `(x, ., $, T) → (ret, .f, $, T)`
    against `D-p = (ret, .f, $, U)`, gives no result, and with `D-p = (ret, .f, $, T)` it keeps the edge
    (`Handoff.RVec.vMark_user_restrictI`, `vMark_user_same`); a premise mark that `D-c` does not admit gives no result
    (`vMark_prem_restrictI`); the `*∖X` cells on both sides (`vMark_inStarEx_T`, `vMark_inStarEx_U`,
    `vMark_outStarEx_T`, `vMark_outStarEx_U`); the same with the exclusions (`HandoffX.XVec.vM_user`, `vM_prem`,
    `vM_inStarEx`, `vM_outStarEx`); the tree form drops the mark leaves that do not meet the mark of `D-p` (§7.4); the union over
    two demand patterns; no result without `D-p`; a summary with several premises keeps its whole premise set when
    every member lies inside a `D-c`; program 2 (§6.4); an `[any-taint]/E` conclusion above `D-p` gives the chain of
    `D-p` in its layer, with `E2` under a `*/E2` exit pattern and the Empty exclusion under `[any]`, if `E` admits the
    step down, and no result if not; below `D-p` it keeps `E`; at a `*/E2` exit pattern it gets `E ∪ E2`; the premise
    test reads the exclusion of a must-premise; a FLOW premise (F72) lies inside its own `*` pattern and inside no
    concrete pattern, and its `*` conclusion stays whole under its `*` exit pattern (§6.4); the two exceptions of the
    intersection (`Handoff.RVec.inter_exc_any`, `inter_exc_star`) give a pair outside `D-p`; the earlier rule above a `*/E2` exit pattern is not the intersection
    (`HandoffX.XVec.v_old_above_not_inter`). The vectors `AnyTaintEx.Vec.restrict_vectors` are for the earlier
    restriction: the test asserts the cells of `HandoffX.XVec` where they differ.
13. Iteration tests: programs 1 and 2 as analysis tests with the field limits 1 (run 1), 2 (run 2, backward) and 3 (run
    3), so the limit does not decrease (W3); the vulnerability is reported in every forward run. A worker loop with a
    sink that never returns (§9.2). The backward zero rules of §9.2: the zero fact enters every callee, a zero-premise
    backward summary returns to every caller without a restriction. THE HAND-OFF OF THE DEMAND EDGES (§9.2): it reads
    the publications; a crossable leaf gives no demand pattern and a leaf that is not crossable gives one per
    publication, in both directions; a normal leaf with an `[any]` or `[any-taint]` conclusion, a leaf of a must-premise,
    a demand-layer leaf (also a backward one with a crossable shape) and every leaf of a summary with several premises
    are demand edges; THE HAND-OFF NORMALIZATION (F72, §9.2): a summary conclusion with the mark `*∖X` gives a pattern
    with the mark `*`, in `D-c` and in `D-p`, in both hand-offs, and the summary keeps `*∖X` (it still stops an added
    fact with a mark in `X`); (F71, before: a `*∖X` entry pattern kept its mark and gave no premise to a requirement
    with a mark in `X`); a forward `[any-taint]/E` summary conclusion or must-premise, which the
    hand-off gives as the pattern `[any]` with no exclusion. Program WRAP (§6.6, `HandoffCases.Wrap`): forward run 3
    analyses `wrap` only from the zero fact, backward run 2 never enters `wrap` with a non-zero fact (it crosses `wrap`
    by the reversed record), and forward run 3 still reports the vulnerability. The CEGAR programs ANYW and ANYM
    (`HandoffCases.AnyW`, `AnyM`) and the getter (`HandoffCases.Getter`) report their vulnerability. THE SEEDS: the
    backward run seeds the DEMAND entries only, not a CONFIRMED one. THE TRIGGER OF AN END FACT (§9.2): in the program
    of §9.2 a requirement that reaches the reversed end-fact edge of the CONFIRMED sink `sinkCall` fires its sink
    seeds, `source()` is hit, and forward run 3 reports the DEMAND vulnerability `sinkAny(r)` again. THE REVERSAL OF A
    CONJUNCTION (§9.1, a regression test): in the program of §9.1 the backward summary of `M` through the conjunction
    is in the demand layer, no record, a demand edge of case 3, and forward run 3 does not report `sinkT(r2)`. THE
    SOURCE SEEDS: a source inside a callee that the backward run crosses by a record is not hit, and the record still
    gives its result (`HandoffSrc.SrcRec.found_unseeded`). THE EXCLUSION: a method key of which a forward run hands
    off no demand edge (for example: only crossable leaves), with no seed below, leaves the frontier, publishes nothing
    in the next forward run, and does not come back while this holds. THE NARROWING (the concrete design): no demand
    pattern has a `*` tail, and the demand patterns of forward run 5 with a `D-p` lie inside those of forward run 3, in
    the locations and the marks, with no exception (`HandoffNoStar.narrowing_canon_loc_exactM`); the zero demand and
    the patterns `(gb, none)` of the seed paths are not part of this check. Since F72 `*` patterns occur after run 1,
    so the test of the narrowing for the F72 runs waits for the model (PENDING, §11.2; item 18). THE STOP RULES:
    `STOP_RULE` after a run with no DEMAND entry; `NO_DEMAND_EDGE` after a run with no demand-layer edge, no demand-layer summary and no demand link, and not after
    a run whose only demand-layer object is a demand link (a call cleaner that demotes an `[any-taint]` bound fact,
    §11.2) (§6.6).
14. Store tests: index completeness against a list filter (records, demand patterns, requests, conjunctions,
    subscriptions). The conjunction store keeps two alternatives of one rule apart (§8.9), also with an equal literal
    pattern. The record store adds no demand-layer summary, no summary with two or more premises and no zero-premise
    backward summary (§8.7 R1). The method edge store (§8.1): the TAINT key holds the exclusion of the `[any-taint]`
    leaves, so two results with different exclusions are two trees; `[any-taint]/E` subsumes only the `[any-taint]` facts
    that it covers, and never a `$` fact. The
    added fact store keeps an `[any-taint]/E` added fact with its exclusion (§8.3). The vulnerability store (§8.10):
    one sink statement in two contexts is one key; two sink witnesses of two alternatives or of two method keys stay apart; after an incomplete forward run the report has
    the DEMAND entries of the latest complete forward run; after an incomplete run 1 the report has no entry and the
    output is empty. The output holds every entry of the report, the DEMAND entries too, each with a simple trace and
    the method key of a confirmed sink witness, else of the first sink witness (§8.10).
15. Reversal tests: every row of §9.1 that occurs for a record, also with `*∖X`; the forward record and its reversed
    reading give converse results on the same concrete pair. R3 reverses a record leaf by leaf: no leaf of a must
    record is reversed (`AnyTaintExact.CexRev`), and no `[any-taint]/E` leaf with `E ≠ {}`; the other leaves of the
    same record are. A leaf `$ → [any-taint]` reverses into `[any] → $`, which applies only to an `[any]` requirement,
    with a demand result. The reversed `[any]` literal of a source has the target `[any]` (demand); the reversed source
    edge has the premise `[any]` and gives a normal source hit. Every result of the reversal of a pass rule with an
    `AnyField` target is in the demand layer, also a `$` result: the reversed `CopyMark(T, P → Q.AnyField)` gives
    `(P, ., $, T)` in the demand layer, and the backward summary through it is not a record. Every result of the
    reversal of a conjunctive micro edge (also of a conjunctive exit source) is in the demand layer, one per literal,
    and the backward summary through it is not a record and not crossable (§9.1). The backward run makes no
    `[any-taint]` fact, and the record store adds no backward edge with an any tail (§8.7 R1).
16. Analysis tests (the gate of the new analyzer): the existing `*AnalysisTest` suites, run with `cleanTest`;
    `DeepCleanSummaryAnalysisTest` and the cleaner suites for §4.7. A finding whose taint comes from an `[any]`-target
    source (a Spring DTO entry-point argument) is CONFIRMED: in run 1 when the sink reads the object in the method of
    the source (`AnyTaintExCases2.PassRule.source_confirmed`), after a callee whose FLOW summary keeps the whole object
    (program I, `AnyTaintExCases2.I.run1_confirmed`), and after a setter of another field (program S:
    `sink(dto.email)` is CONFIRMED and `sink(dto.name)` is NOT REPORTED, `AnyTaintExCases.S`; the same one call deeper,
    program SD; the reads of program R); in forward run 3 through a getter (program G,
    `AnyTaintExCases2.G.run3_confirmed`) or a sink in the callee (program C, `AnyTaintExCases2.C.run3_confirmed`). A
    strong write into the object does not demote it: only the written field is not reported (program S). A finding
    through a pass rule with an `AnyField` target stays a DEMAND entry
    (`AnyTaintExCases2.PassRule.pass_not_confirmed`), and so does a finding under the `exact` cleaner below the object
    (`AnyTaintExCases.CL.exact_result`) or over the field limit (§8.10; on the JVM with `L = 1` and a write two counted
    accessors deep). Programs X and CUT are AP-level tests (item 3), not JVM analysis tests: CUT has the field limit
    `L = 0`, which no run has (§4.4: run 1 needs `L ≥ 1`, and the limit does not decrease); X is a two-level write in
    one statement, and on the JVM `x.f.g = c` is `t = x.f; t.g = c`, the weak alias write (S2, `interpreter.md` A3, gap
    G7), so a JVM analysis test of X expects `sink(x.f.g)` CONFIRMED, the documented false positive of §11.1, and
    `sink(x.f.h)`, `sink(x.k)` CONFIRMED (`interpreter.md` §7.2 item 30). A weak update of the object (an alias
    write, the default identity of an unresolved callee) gives an expected CONFIRMED false positive (§11.1). A lost finding is a test whose message
    says that no vulnerability reached the sink; read the message, do not count failures.
17. Confirmation tests of the `[any-taint]` tail (§4.9): a normal `[any-taint]/E` sink edge is confirmed when the sink
    pattern meets an admitted location, and does not trigger on an excluded one (`AnyTaintEx.Vec.check_vectors`); the
    support link of an `[any-taint]/E` added fact accepts a `$` or a must-premise inside it (with the exclusions) with
    the same mark, also the emission `a ∩ D-c = a`, and rejects a premise with the mark `*`
    (`AnyTaintExact.CexSupMark`); a demand `[any]` link supports nothing; the program G is demand in run 1 and
    confirmed in run 3 (`AnyTaintExCases2.G.run1_not_confirmed`, `run3_confirmed`); the program C is confirmed in run 3
    through the must branch of `AnyTaintEx.SupLinkX` (`AnyTaintExCases2.C.run3_supported`); the program
    `AnyTaintExCases.B` confirms `sinkAny(e)` in run 1 and in run 3 and never reports `sink(d.name)`.
18. Tests of F72, ABSTRACT MARKS IN THE RESTRICTED RUNS (PENDING the Lean model, §11.2; write them first, and keep
    them red where the model shows a rule change). As analysis tests with the field limits 1, 2 and 3: (i) THE GETTER
    with two marks (§6.3, THE GETTER): `get(p) { ret = p.name; }`, called with a fact of the mark `T` (the DTO fact)
    and a fact of the mark `U`; backward run 2 has ONE `*` requirement `(ret, ., *, {}, *)` in `get`; forward run 3
    has one record (or one FLOW premise `(p, .name, *, {}, *)`) for both marks, and both vulnerabilities are reported,
    the DTO one CONFIRMED; (ii) A MARK-CHANGING PASS RULE `T → U` inside a callee that a `*` pattern reaches: the `*`
    analysis gives nothing for it, and the vulnerability of `U` is found through the concrete pattern that the run-1
    request and answer made; (iii) A PARTIAL CLEANER of `T` under a `*` premise: the fact continues as `*∖{T}` with no
    request, and a flow of `T` through the part that the cleaner does not clean is found through a concrete pattern;
    (iv) the search for a counterexample to R6 (§6.6): a flow that needs a concrete mark in a callee that only `*`
    patterns reach after run 1. The AP-level tests: the hand-off normalization (§9.2); the emission rows of item 11;
    the FLOW form of an `[any]` pattern (`*/{}`) and of a `*/E` pattern (`*/E`); a check on the hand-off of every run
    that no `*` pattern has the tail `*/E` (§4.3, the open point (a) of §11.2: the FLOW premise `(x, ., */{f}, *)`
    and the added fact `(x, ., */{g}, *)` satisfy neither test).
