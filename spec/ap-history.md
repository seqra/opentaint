# Access paths and storages — design history

This document records the design decisions of the AP spec and the reasons for them: the versions, the decisions of
the design reviews, the decision log, and the resolved questions of the interpreter. It is not normative.
[`ap.md`](ap.md) is the normative document for the AP, and [`interpreter.md`](interpreter.md) for the IR
interpretation. The tags F*n*, UD*n* and the resolved Q*n* occur only here.

Language: ASD-STE100 Simplified Technical English.

---

## 1. Versions

* Version 2 came from the first design review.
* Version 3 added the runs that strictly follow the demand. It used location-only rules for the strict demand. Two
  agreed rows then lose a real flow (programs 1 and 2, `RCases.p1_lost_U`, `p2_lost_U`).
* Version 4 made the emission mark-aware. The restricted runs became concrete, and neither row can fire
  (`RCases.p1_found_M`, `p2_found_M`). The model keeps the version-3 rules for comparison.
* Version 5 splits the spec in two (`ap.md`, `interpreter.md`). It removes the Universe exclusion (it never occurs
  with the edges of the interpreter), puts every `[any]` conclusion in the demand layer, separates micro edges from
  summary edges, and adds the mark exclusion, the cleaner, the type filter and the ND edges.

## 2. Decisions of the design reviews

| Topic | Decision |
|---|---|
| Layer | A propagation edge is in the normal or the demand layer (`~`, `Zero~`). Only the AP operations move it to the demand layer; the expected over-approximations of a path-insensitive engine do not. A micro edge has no layer. An `[any]` conclusion is ALWAYS in the demand layer. So "complete" means "normal layer" (ap.md now says "normal edge"). |
| Exclusion | ONE exclusion per path edge, shared by premise and conclusion. An exclusion is a finite set of accessors; "Universe" does not exist in the AP. Two merge rules; no union across different conclusions. |
| Mark | A premise has the mark `*` or `T`. A conclusion has `*`, `T`, or `*∖X` (the premise mark passes unless it is in `X`; a cleaner makes it). |
| Read | A field read never changes an exclusion. Only a field write does. |
| Statics | One `ClassStatic` base with the class accessor. |
| Operations | One computation (delta-concat) and two operations on it: a MICRO EDGE applies to every overlapping fact; a SUMMARY EDGE applies only to a fact that satisfies its premise. |
| Ownership | The CALLER owns the subscriptions and applies the summaries. The CALLEE owns the added facts, the demand, the emission and its summaries; it restricts each summary by its demand before it publishes it. |
| Runs | Run 1 is unrestricted: it emits the most abstract facts. Every later run STRICTLY follows the demand of the previous run: the emission `a ∩ D-c` with the mark of `a` and the summary restriction. A restricted run is concrete. |
| Requests | The task rule for the answer (no chain deeper than the request). Requests stand for the whole run. Requests exist ONLY in run 1. |
| Conjunction | A rule with several mark literals on different facts makes an ND edge: a SET of premises. |
| Cleaner | A cleaner splits a `*`-mark fact by the mark: the fact continues as `*∖{T}`, and the mark `T` is requested and cleaned exactly on the concrete answer. |
| Type filter | A prefix-closed predicate on paths; it only drops facts that have no real location. |
| Report | Every forward run reports every real vulnerability (with B). Confirmed vulnerabilities persist. A demand vulnerability that the next forward run does not report is refuted. |

## 3. Notes removed from ap.md

These notes were inline in ap.md version 5. They explain a past state, not a current rule.

* Merge rules (ap.md §3.3). The current `EdgeNonUniverseExclusionMergingStorage` makes a union of exclusions across
  two edges. It was sound only with the old refinement.
* W6 (ap.md §2.3). It was decided for version 5 (F41) that the results of the any-field rules go to the demand layer:
  an `[any]` result never makes a record and never confirms.
* Satisfaction (ap.md §4.3). The version-4 form `satIold` compared the marks in both directions. It rejected a concrete
  fact against a `*`-premise record, which disabled record reuse. `RCore.satI_markSub` and `satI_conc_record` show that
  `satI` accepts these cases; `satIold_markSub_fails` and `satIold_conc_record_fails` show that the old form rejects
  them. The overlap test `satO` and its false demand vulnerability were a review argument, not modelled.
* Cleaner (ap.md §4.7). The `part` row of an all-marks cleaner on a `*`-mark fact normalises the result (F45): without
  it W2 failed (`Invariant` round 5).
* Type filter (ap.md §4.8). The two summary-side filters of today were dropped "in version 5".
* Restriction (ap.md §6.4, §7.4, §8.6). The table of §6.4 is the rule agreed with the user (`restrictU`). The
  version-3 repair `restrictS` keeps a `*` conclusion above `D-p`. In a concrete run both give the same run
  (`RExact.restrict_U_eq_S`), and the contract of `restrictS` holds (`RCore.restrictS_contract`). The demand store
  index also serves the version-3 form (`_S` lemmas).
* Version-3 theorems (ap.md §10.7): `RCore.emitS_contract`, `emitU_fails`, `restrictU_fails`; `RCases.p1_lost_U`,
  `p2_lost_U`; `RMain.iteration_sound_S`. The location-only rules: the agreed rows lose programs 1 and 2.
* Test vectors (ap.md §13 item 1). "The F16 vectors" were the vectors of `lostCorr` that give an `[any]` result in the
  normal layer of the model.
* Support (ap.md §10.3). `Confirmed.rev2_not_confirmed` is the counter-example of a review.
* Universe (ap.md §11). Two notes compared the Lean `applyEdge` and the Kotlin reference form on a `$`-premise edge: on
  an `[any]` fact with a `*` target Lean gives `$` and Kotlin `[any]` in the demand layer; on a `*` fact at `r = []`
  Lean gives `*/Universe`, which `AFact.norm` maps to `$`. Both cases need an edge that S8 or I7 forbids. ap.md now
  makes `concat` assert S8 and I7, so the notes are not necessary.
* Exceptions (ap.md §11, interpreter.md G1). Out of scope for now (F51).

## 4. Decision log

Each line comes from a failed proof, a counter-example checked by `decide`, a review comment, or the design
discussion. The `UD` lines are design decisions of the user from version 2. (The `D` numbers of `interpreter.md` are
its deviations from today's code.)

| # | Topic | Outcome |
|---|---|---|
| F1 | "No `[any]` ⇒ complete" | Changed: the demand layer (`~`, `Zero~`), set by the AP operations (F50). |
| F2 | Read builder | Adopted: a read never changes an exclusion. |
| F3 | One static base per class | Withdrawn: the class accessor stays. |
| F4 | Abstraction determinism | Adopted (ap.md §6.1). |
| F5 | Requests for mark-specific rules | Adopted (ap.md §4.5). |
| F6 | Callers of an answered initial fact | A caller reads every summary whose premise its fact satisfies. |
| F7 | Reversed records instead of an analysis | Replaced by the strict demand (R7, R8) and the iteration theorem. |
| F8 | Reversal shapes | Exact for every mark-reversible record with the Empty premise exclusion (ap.md §9.1). |
| F9 | Normal form | Adopted (ap.md §4.1 step 6). |
| F10 | Exclusion of a reversed record | On the new conclusion (ap.md §9.1). |
| F11–F12 | Store indexes | Path index; `base :: path` keys (ap.md §8). |
| F13 | `applicable` | Run 1; a restricted run uses `satI` (F36). |
| F14 | Answer by the meet | Withdrawn: the answer keeps the request chain. |
| F15 | Mark of the emitted fact | Run 1: `*`; a restricted run: the mark of the added fact (F34). |
| F16 | `lostCorr` | A `$` result without a lost restriction stays normal. For an `[any]` result F41 replaces it. |
| F17 | Standing requests | Adopted (ap.md §4.5). |
| F18 | Conclusion subsumption | `subsumesB`, with mark exclusions (ap.md §8.1). |
| F19 | Closed marker | No request (R5). |
| F20 | Identity edges of rules | `interpreter.md`. |
| F21 | Zero fact | Run 1: the zero fact; restricted: a zero demand emits the zero fact. The zero fact passes over every call and enters the callee by its binding. |
| UD1 | Exclusion | Per path edge, shared; merge rules 1 and 2; no union merge. |
| UD2 | Call processing | The four steps of call processing (now the event table of ap.md §5.3). |
| F22 | Confirmation | A normal-layer support chain (ap.md §4.9). |
| F23 | Approximating rules | Replaced by F50: the interpreter sets no layer. A condition that one fact does not decide is the expected over-approximation; a cleaner applies only its decided part. |
| F24 | Rule-2 delta | Merge rule 2 propagates the whole merged tree (T4). |
| F25 | Fold | Only inside demand-layer trees. |
| UD4 | Record subsumption | Inside the normal layer. |
| UD5 | Strict demand | Run 1 unrestricted; later runs follow the demand; soundness is iteration-relative under B. |
| F26 | One edge exclusion | The tables use one exclusion `E` per edge. |
| F27, F28, F29 | Version-3 repairs | Superseded by F34: a restricted run has no `*` fact. |
| F30 | Records in restricted runs | Exact; added when the caller fact satisfies the premise; only run-1 closed records replace an emission (R8). Since the user decision of 2026-10-06: a record applies when its premise covers the caller fact (`applicable`), in every run. |
| F31 | Report rule | Every forward run reports every real vulnerability. |
| F32 | Backward contract | About sink witnesses only. |
| F33 | Zero demand | The backward run continues a requirement through the reversed source edge to the zero fact. |
| F34 | Mark-aware emission | `a ∩ D-c` with the mark of `a`. |
| F35 | No request after run 1 | A restricted run is concrete (`no_request_M`). |
| F36 | Satisfaction in a restricted run | `satI`: the premise lies inside the fact as locations, and the premise mark admits the fact mark (the version-4 form compared marks both ways and disabled record reuse: `satIold_conc_record_fails`). |
| F37 | Support in a restricted run | `SupM` accepts the emitted exact fact. |
| F38 | Backward seeds | Directly at the sink statements of the reported vulnerabilities (non-returning code). |
| F39 | Split ap.md / interpreter.md | The AP and its primitives in `ap.md`; the IR interpretation in `interpreter.md`. |
| F40 | Universe | Removed from the AP; it never occurs under S8 (`no_univ_star`). |
| F41 | `[any]` layer (W6) | Every `[any]` conclusion is in the demand layer; "complete" = normal layer; a layer refinement (`demand_of_any_ok`). |
| F42 | Micro edge vs summary edge | A micro edge applies unguarded (both cases); a summary edge only to a satisfying fact. |
| F43 | Ownership | The caller owns the subscriptions; the callee owns the added facts, the demand, the emission, and restricts before it publishes. |
| F44 | Cleaner | The mark slot `*∖X` (the user's design): the cleaner splits a `*` fact by the mark; the request gives the concrete `T` path; positional only for all marks; exact for every other mark. Replaces `DeepAccessorExclusion` (lost at a field-limit cut). |
| F45 | Cleaner all-marks branch | A partly cleaned `*` fact under an all-marks cleaner is normalised (`[any]`, demand layer): without it W2 failed (`Invariant` round 5). |
| F46 | Type filter | A prefix-closed predicate; exactness only for valid locations (`CexFilt`). |
| F47 | Mark well-formedness (S7) | A concrete target mark needs a concrete premise mark (`CexMark`, `CexConfMark`). |
| F48 | ND edges | Premise lists; uncorrelated concrete conclusions; standing conjunctions and ND summaries; never records; support semantics. |
| F49 | Conjunction layer | The layer of the inputs (demand also if the literal does not cover an input). Literals on exclusive paths are the expected over-approximation of a path-insensitive engine, not a demand step (the user's decision; it replaces the review-5 H1 proposal "always demand"). |
| F50 | Micro edges | Every micro edge (statement edges, call bindings, alias edges) is precise and complete (S1, S2). A micro edge has no layer: the layer is a property of the propagation edge, and only the AP operations change it. The field limit applies to the result of an application, never to a micro edge. |
| F51 | Exceptions | Out of scope for now. |
| F52 | `ExactAndAnyField` | `atAndBelow` is the meaning of the rule. The cleaner removes a mark only from a fact that lies inside the cleaned locations; a partly covered fact is split or kept, so the cleaner never removes more than the rule says. |
| F53 | ND exactness | A normal-layer conjunction is exact against `TaintN` (`NDExact.nd_edge_exact`); it needs concrete literal marks (S9, `CexLit`). |
| F54 | Weak alias write | Kept (`interpreter.md` A3, G7): sound if an alias does not hold; a precision gap in the normal layer. |
| F55 | Decisions of 2026-10-06 | Type filters check the concrete path only; they are not stored or propagated. A type filter on a `*` fact, the weak alias write and the constructor pass-over are expected false-positive sources (ap.md §11.1); "a confirmed vulnerability is real" holds for the reference semantics of S1–S9, modulo these sources. The interpreter semantics stays as on the main branch. An `[any]`-target source result is always in the demand layer, so a vulnerability whose taint comes only from it is never confirmed. A record applies when its premise covers the caller fact, in every run. The iteration driver stays out of scope (ap.md §6.6 gives its general requirement). Micro edges (statement edges and call bindings) are precise and complete and have no layer. |
| F56 | R8 and the closed marker | Removed (2026-10-06). R8 let a later run skip a demanded initial fact that was closed in run 1 and use its records instead. Records are summaries only, so a vulnerability inside the skipped method that was only a demand vulnerability in run 1 was never checked again, and the report refuted it (a Lean-checked program). The user's rule: after run 1 the abstraction reads only the demand; no summary check. Records still apply (R4). |
| F57 | Backward run | The zero fact starts at the roots, passes over every call and enters every callee through its own binding; a sink fires as a zero-to-fact edge; every return is balanced (user's design, 2026-10-06). The earlier text placed seeds directly at the sinks and reversed the zero binding, which lost program 1 (`Backward.lost_plain`). Non-returning code is out of scope (`JIRBackwardExitWiringGraph`). Proved: `Backward.B_general`, `iteration_general`. |
| F58 | Statics in run 1 | A static operation below an abstract static fact (a read, the class keep edge of a write, a sink) raises a position request; the answer `(S, p, *, {}, *)` comes from the first caller with a precise added fact (user's design, 2026-10-06). A static fact with the `[any]` tail above a static position is impossible by construction (user). Lean showed: the write must request `<C>` (`CexWide`: without it a callee's write degrades a precise caller fact); a static mark request answers with the added fact itself (`CexClean`: the chain answer makes `(S, ., [any], T)` at a cleaner). Earlier variants that failed: the climb only from the root (`CexAbove`), a class-level `[any]` source (`CexAny`, excluded by construction). |
| F59 | Statics after run 1 | No request and no static rule after run 1: the demand covers the statics (user's claim, proved: `StaticsIter.rinv_all`, `iteration_general_DS`, `no_static_rule_after_run1`; no hypothesis on the demand is needed). |
| F60 | Analyzer core (phase 2), 2026-10-07 | `analyzer-core.md`. The user's decisions: (1) the summaries keep today's storage-with-subscription pattern (callee-side storage with subscribers, caller-side subscription manager with replay); a duplicate delivery is acceptable, a lost one is not. The alternative "the callee matches its links and sends the applications" was rejected. (2) A new engine (manager, runners, analyzers) for each run; the thread pool, the AP manager, the method context cache, the records and the vulnerabilities are shared. (3) The iteration driver is part of phase 2. (4) The pipeline proof of subsumption is generic; the simulation by the AP operations is argued. Lean showed the four protocol conditions P1 to P4 (`Pipeline.PCex.cex_P1` to `cex_P4`); the code reading found that today's delivery index breaks P4 for an `[any]` caller fact, and that today's replay read has no memory-model guarantee (P3). |
| F61 | The static base at a call, 2026-10-07 | `S` is touched at every call in every run, as in the model call. The user's reason: a callee that touches no static has a complete run-1 summary (a record) and no demand, so the static fact needs no special rule at the call. Removed: `interpreter.md` D15 and G5, the special case of `ap.md` §5.3 step 1 and its §11.2 note, and the static-touch set of `analyzer-core.md` (§7.4). |
| F62 | Seeds in both directions, 2026-10-07 | The user's rule: after run 1, every run has seeds. The backward seeds are the sinks that the forward run before reported; the forward seeds are the unconditional sources that the backward run before reached (its source hits, `ap.md` §8.11). A forward restricted run fires only the seeded sources (§6.1 rule 6); the zero fact still propagates from the roots. Proved: `FSeeds.B_src`, `iteration_src`, `PipelineSeeds.driver_iteration_src`. Also: the core is JVM-only (Go out of scope), the call bindings are statement summaries, and the 'Unchanged' defect was narrowed to the post-processor case (the normal path `addSequentialUnchangedEdge` is correct). |
| F63 | Interpreter deviations from today, 2026-10-07 | The implementation proposals (`ap-impl.md` §34) listed the points where `interpreter.md` and today's code disagree. The user's decisions: (1) a call sink also checks the array elements of an argument that may be an array, as on main (`interpreter.md` §4.2); (2) exit sinks check every fact (D21); (3) a `CopyAllMarks` rule has no mark literal in practice: such a rule is a rule error and applies without its mark literals (D24); (4) a lambda call that the prescan resolves has no unresolved path (D19); (5) the exit rules apply at both exits, with `Result` read as `exc` at the exceptional exit (§4.7; `analyzer-core.md` §4.3, §4.4); (6) an unconditional exit sink fires on the zero fact (D22); (7) only an unconditional cleaner acts: a cleaner with a mark literal in its condition does not act (D20; this replaces the 'decided part' rule of §4.2); (8) the summary rewriter applies to every summary result and to the default identity (D23). |

## 5. Interpreter questions

The resolved questions of `interpreter.md` §8. The open questions stay there.

| # | Question | Resolution |
|---|---|---|
| Q4 | Exception flow across calls. | RESOLVED: exceptions are out of scope for now (gap G1, F51). |
| Q5 | The meaning of `ExactAndAnyField`. | RESOLVED: `atAndBelow` is the meaning of `ExactAndAnyField`; the cleaner cleans only a fact that is precise enough, so it over-approximates (D9, F52). |
| Q7 | The constructor rule (`interpreter.md` §3.5) keeps the caller facts that the constructor overwrites. Keep this ad-hoc weak update? | RESOLVED (user decision of 2026-10-06): kept as on the main branch. It is an expected false-positive source (gap G8, ap.md §11.1). |
| Q8 | The zero fact at a call. | RESOLVED: the zero fact passes over every call (the zero base is never touched) and enters the callee by `zero.* → zero.*`; there is no binding back (ap.md §5.1, `interpreter.md` §3.3). |
| Q9 | Precision of the alias edges. | RESOLVED: every micro edge, also an alias edge, is precise and complete (I9, A6, F50); the alias analysis must give exactly the aliases that hold. |
| Q11 | Rules on a static position (`interpreter.md` §1.4). | RESOLVED (2026-10-06): an `[any]` target on a bare class position is a rule error; a pass rule from or to a bare class position is a rule error (a pass rule is a handcrafted summary; no data flows from or to a bare class); a pass rule between static fields is allowed; `RemoveAllMarks` on a static field is the kill of a strong write (no mark enumeration); a rule position deeper than a static field needs no rule (a sink raises the ordinary mark request; below the static field the ordinary rules apply). The backward run needs no liveness drop (an optimization for later). |

## Removed from interpreter.md in the self-containedness pass

The items below were removed from `interpreter.md` or rewritten there. The right column gives the place of the rule now.

| Item | Removed text | Now |
|---|---|---|
| Q6 | "The summary rewriter can raise a request on the caller premise (§5.2). The alternative is no request and a result in the demand layer. Confirm." | RESOLVED (already decided): the rewriter raises the request on the CALLER premise (`interpreter.md` §5.2, §5.4). |
| Status line | "(version 5)" | Removed: history wording. Section 1 of this file lists the versions. |
| §3.3 | "The `$` form `zero.$ → zero.$` is not well formed: a binding into the callee is a `*`-to-`*` edge." | The remark applies to bindings only (`interpreter.md` §3.3, I4). `zero.$ → zero.$` is the keep edge of a statement that touches the zero base (I11, the rule statement of a call in §4.1). |
| §4.1, source at a call | The keep edges `zero.$ → zero.$` and `Q.* → Q.*` as a part of the source edges. | `interpreter.md` §4.1, THE RULE STATEMENT OF A CALL: it keeps the zero fact and has no other keep edge, so a read fact does not pass over the call through it (as today: a source rule gives only its targets). |
| §4.5 | The Kotlin form `callStep` (its helpers `CallStmt`, `Premise`, `filter(..)(c)`, `callerBase`, `may`, `enter`, `applyEdge` were not defined). | The numbered steps of `interpreter.md` §4.5. |
| §2.1 | The Kotlin forms `strongKeep`, `weakKeep` over the undefined types `MicroEdge`, `star()`, `Base`. | Rewritten over the types of ap.md §3.4 and `PathEdge` of ap.md §4.1. |
| §0 | The notation table. | ap.md §1 (NOTATION); `interpreter.md` §0 keeps `#i`, `<G>` and the notation of the "Today" columns. |
| D7 | "decision: the same placement in both languages" | D7 keeps the reason without the word "decision". |
| §8 | "The resolved questions (Q4, Q5, Q7, Q8, Q9) are in ap-history.md §5." | A pointer to this file; Q6 is in this section. |

## Removed from ap.md in the self-containedness pass

The items below were removed from `ap.md` or rewritten there. The right column gives the place of the rule now.

| Item | Removed text | Now |
|---|---|---|
| Status line | "design spec for phase 1 of bidirectional-task.md ("New AP with all required storages"), version 5" | History wording. Section 1 of this file lists the versions. |
| §0 | "The contract of the backward run is in §10.7." | Contract B is stated in words in `ap.md` §6.6. |
| §1, layer | "The demand layer of premise `i` is written `i~`; of the zero fact, `Zero~`." (and "demand (`~`)" in §4.2, "the `~` premise" in §6.5) | The notation was not used elsewhere. Removed. |
| §1, normal edge | "(Lean: `AFact.complete`, which also excludes `[any]`; with W6 the two agree)" | `ap.md` §11.2 (the implementation against the model). |
| §2.2 | "Only a field write (a kill) makes it larger." | "Only a strong field write makes it larger." The word KILL keeps one meaning: `ap.md` §4.2 step 4. |
| §2.3, W6 | "W6 is a rule of the implementation. The model keeps an `[any]` conclusion possible in the normal layer. ... In the model a normal-layer `[any]` needs an `[any]`-target micro edge on an exact derivation." | `ap.md` §11.2. §2.3 keeps the normative consequences. |
| §2.3, Universe | "In the model, `Excl.univ` still exists: it encodes a `$` premise in the operation tables (`tailExcl`)." | The term Universe: `ap.md` §1; the model note: `ap.md` §11.2. |
| §4.1 | "a `$` premise has no `*` target (`interpreter.md` I7)" | The rule is part of S8 (`ap.md` §0.1). |
| §4.2 | "The cases of bidirectional-task.md §1 (checked by `decide` in `Cases.lean`)" | A task-file reference used as a definition. The table is in `ap.md` §4.2. |
| §4.3 | "The overlap test (`satO`) is sound too, but then a precise fact reads the demand-layer summaries of a coarser sibling premise, and a false demand vulnerability can survive every run (not modelled)." | A rejected alternative (version 4, review M2). The rule is `inside` (`ap.md` §4.3). |
| §4.4 | "There is no `[any]` depth charge and no fact-depth gate" | `ap.md` §7.6 (the `MethodAnalyzer` row). §4.4 keeps "the field limit is the only depth bound". |
| §4.5 | "ANSWER (bidirectional-task.md §4)." | A task-file reference; the answer rule is in `ap.md` §4.5. |
| §4.5 | "In run 1 only the policy (§6.2) makes such premises. So every request premise of run 1 is a policy fact `(x, [], *, {}, *)`." | False with statics: a position answer `(S, p, *, {}, *)` is a request premise too (`ap.md` §4.5, §4.10). The same correction in §13 item 9. |
| §4.7 | "The model `cleanRes` also raises the request `T` in the first row when `T ∈ X`. The implementation does not raise it: ..." | `ap.md` §11.2. |
| §4.7 | "(Today's `DeepAccessorExclusion` is tied to an abstraction point at a depth; it is lost when the field limit cuts the path.)" | `ap.md` §7.6 (the `DeepAccessorExclusion` row). |
| §4.8 | "as today (an Accept keeps the whole subtree)"; "(today: the caller content under a callee `*`, and the exit compatibility filter)" | Comparisons with today's code: `interpreter.md` D13, D14. |
| §4.9 | "(The model `check` reads the effective mark (§1), so it also triggers for an abstract `f.mark` under a concrete `i.mark`; this case does not occur.)" | `ap.md` §11.2. |
| §4.9 | "This covers bidirectional-task.md §2:" | "Examples:". |
| §4.10 | "The root keep edge `S.* →_{<C>} S.*` is at the root: it updates the exclusion, as on the main branch;" | History wording ("as on the main branch") removed. |
| §4.10 | The closed list of the fire points (a read, the class keep edge of a write, a sink). | The general rule of the model (`Statics.genFireB`): every statement micro edge with its premise on `S` strictly below an identity static `*` edge, and every sink pattern on `S` strictly below it (`ap.md` §4.10 item 1). |
| §4.10 | "Construction rules (`Statics.SWF`), all true for the interpreter: ..." | `ap.md` S12 (an assumption) and `interpreter.md` I12. The interpreter rules on a `ClassStatic` position do not all satisfy it today (`interpreter.md` Q11). |
| §4.10 | The proof paragraph of "AFTER RUN 1 NO STATIC RULE IS NEEDED" with the list of `StaticsIter` theorems and the worked programs. | `ap.md` §10.8. §4.10 keeps the rule and a pointer. |
| §5.1 | "(The form `zero.$ → zero.$` is not a `*`-to-`*` binding, so it is not well formed.)" | `ap.md` §3.5: a call binding has the premise mark `*` (S10), so the zero binding is `zero.* → zero.*`. A statement that touches the zero base keeps the zero fact by the micro edge from the zero fact to itself (S11 (d)). |
| §5.1 | The concrete call semantics. | `ap.md` §3.5 (CALL STEP); §5.1 is a pointer. |
| §5.3 step 5 | "The caller binds each summary result back (micro edges), applies the summary rewriter and the aliases" | Wrong order. The rewriter comes first, in callee coordinates (`ap.md` §5.3 step 5, `interpreter.md` §4.5 step 6). |
| §6.1 | The contracts (E1), (E2), (E3), and the references "the satisfaction contract (§4.3)" and "the restriction contract (§6.4)", which those sections did not state. | `ap.md` §6.1: C1 to C5, all stated in words. The events of §5.3 keep the names E1 to E7. |
| §6.3 | "Programs 1 and 2 (`RestrictedCases.lean`) are two programs where an emission that ignores the marks loses a real flow." | Not what the model shows. Program 1 is the example of the emission (`ap.md` §6.3), program 2 the example of the restriction (`ap.md` §6.4). |
| §6.3 | "The mark `M` of the entry pattern is `*` or `T`, never `*∖X`." | A backward entry pattern can have `*∖X` (a run-1 summary conclusion); it counts as `*` (`ap.md` §6.3, Lean `markMatchB`). |
| §6.4 | "In a concrete run this restriction gives the same run as the restriction `restrictS`, which keeps a `*` conclusion above `D-p`, and the contract of `restrictS` holds (...). So the restriction contract of §10.7 holds for the run." | The restriction contract C5 (`ap.md` §6.1). `restrictS` is only an auxiliary rule of the proof (`ap.md` §10.7). |
| §6.4 | The names `S = (S-p → S-c)` and `R = (R-p → R-c)`. | `j → g` and `j → g'`. The letter `S` names only the static base now (§7.3 uses `U` for a subtree). |
| §8.6 | "the edges of run `n + 1` on the paths from its seeds (the vulnerabilities of forward run `n`): demand-layer edges, reversed records and the zero edges (§9.2, contract B)" | Inconsistent with `Backward.demOf`. The hand-off is defined once, in `ap.md` §9.2. |
| §8.10 | "The vulnerabilities of a backward run only make the demand of the next run; they are not in the report." | A backward run reports no vulnerability (`ap.md` §9.2, the backward sink role). |
| §9.2 | "The backward run applies no type filter (as on the main branch; the model keeps the filters, which only makes its demand smaller, §11.2)." | `ap.md` §9.2 states the rule; `ap.md` §11.2 the model difference. |
| §10.3 | "(not used by the analysis)" for `Closed.closed_records_exact`. | Removed. |
| §10.7 | "`B_rep_fails_general` ... in general its mark-blind exit is too weak (counter-example), so the mark-aware form is used." | The reason for the mark-aware form of contract B. `ap.md` §6.6 states the form that is used. |
| §12 | "the location-only rules of earlier versions (`ap-history.md`)" | "auxiliary rules that some proofs use". |
| §7.6, §8.1, §13 | "The phase-3 prescan", "(phase 5)", "(phase 2 gate)" | The term prescan is in `ap.md` §1; the phases have names. |
| §8.9 | "(today's `TaintSinkTracker` assumptions)" | `ap.md` §7.6 (the `TaintSinkTracker` row). |

## Removed in the final review pass (self-containedness and proof consistency)

| Item | Removed text | Now |
|---|---|---|
| `interpreter.md` D17 | "(user decision)" as the reason for the static rule errors | The reason is the construction rules of `interpreter.md` I12 (`ap.md` S12). The decision is a design decision of the static rule. |
| `interpreter.md` G1, `ap.md` §11.2 | "Out of scope for now", "Exceptions are out of scope for now" | "Out of scope". |
| `interpreter.md` §1.4 | "'The marks that the rules use' is the finite set of the concrete marks that occur in the loaded rule set." | The term was not used. Removed. |
| `ap.md` §4.9 | The second copy of "The weaker condition 'the premise is exact' is not enough (`Confirmed.weak_support_gap`, a proved counter-example)." | One copy, with the name `Confirmed.Weak.weak_support_gap`. |
| `ap.md` §8.2 | "`initials: Map<InitialAp, Flags>`, with `class Flags(var supported: Boolean)`" | Support is a property of a premise SET (`ap.md` §4.9 condition 3): `supported: Set<PremiseKey>`. |
| `ap.md` §7.1, §4.6, §11.2 | "Empty: the zero fact"; "`{}` for the zero premise"; "this spec keeps SETS and drops the zero premise" | The zero fact is a premise like every other initial fact; the edge is named by its premises that are not the zero fact (`ap.md` §4.6). |
| `ap.md` §0.1, §4.9, §11.2 | The run-1 confirmation with the static rule, the backward records and the backward concreteness written as proved | Argued, listed in `ap.md` §11.2 (ARGUED, NOT PROVED). |

## Removed with decision F61 (the static base at a call)

| Item | Removed text | Now |
|---|---|---|
| `interpreter.md` §3.3 | "In a restricted run `S` is NOT touched when the callee, transitively, touches no static; the static fact then passes over the call. This is the deviation D15 … It needs the final call graph (G5)." | `S` is touched at every call, in every run; the run-1 identity summary of a static-free callee is a record. |
| `interpreter.md` G5, D15 | the gap and the deviation rows | removed |
| `ap.md` §5.3 step 1, §11.2 | the special case "the interpreter leaves `S` untouched when the callee, transitively, touches no static" and its §11.2 note | one special case: the zero base |
| `analyzer-core.md` §3, §7.4, §11 | `RunConfig.touchesStatic`, the STATIC CALL test, the static-touch set at the barrier after run 1 | §7.4 THE STATIC BASE |
