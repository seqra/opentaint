# Access paths and storages — specification

Status: design spec of the new access path with all its storages, for
[bidirectional-task.md](../bidirectional-task.md). This document is normative. The design decisions and their reasons
are in [`ap-history.md`](ap-history.md). The spec has two parts:

* this document (`ap.md`) defines the access path (AP): the fact, the edge, the operations and the primitives (micro
  edge, summary edge, mark request, mark conjunction, cleaner, type filter, emission), the runs and the storages;
* [`interpreter.md`](interpreter.md) defines how the analyzer interprets the IR with the AP: the micro edges of the
  statements and of the calls, the aliases, and the order of the rules.

The formal model is in [`spec/lean`](lean). Every theorem named here is machine-checked and constructive (§10 defines
the term, §12 gives the audit). The claims that are argued and not proved are listed in §11.2. This spec states every
rule in words. A Lean name is only a reference to the model.

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
gives only its general requirement) or the trace resolution. It defines the contracts that these parts use. The
contract of the backward run (contract B) is in §6.6.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | The interpreter describes a statement by its statement summary: the bases that it touches and its micro edges (`interpreter.md` §2). Every micro edge (a statement edge or a call binding edge) is PRECISE AND COMPLETE: the micro edges of a statement give exactly its flows. The flows of a rule are read in the reference semantics (§3.5): every negated mark literal is true. With this reading a source, sink or pass-rule edge is precise. | The interpreter. |
| S2 | Extra micro edges describe the aliasing: gen edges to the alias paths of the aliases that hold. Each alias edge is precise. The write at an alias is WEAK: the alias base is not touched, so it keeps its old content (`interpreter.md` A3, gap G7). This keeps soundness when an alias does not hold. It is an expected false-positive source (§11.1). The model itself is alias-free. | The alias analysis. |
| S3 | A method does not reassign its formal parameters. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. | The CFG normalisation. |
| S5 | A type filter accepts every path that a real value of the static type can have, and it is prefix-closed (§4.8). | The type checker. |
| S6 | The result of run 1 is the least fixed point of the rules of run 1 (§6.1; Lean: `D`). The result of a later run is the least fixed point of the rules of a restricted run (§6.1; Lean: `DR`, and `Backward.DB` for a backward run). The worklist may compute it in any order. | The analyzer. |
| S7 | Mark well-formedness: no micro edge or call binding has a `*∖X` premise, and a micro edge with a concrete target mark has a concrete premise mark (`Exact.MarkWF`). Without it a normal edge can claim a cleaned mark (`Exact.CexMark`). | The interpreter (sources have the premise mark `zeroMark`, conditional sources `T`). |
| S8 | No `*/Universe` edge (§1, Universe): a micro edge with a `$` premise has a concrete premise mark, and no micro edge, binding or initial fact has the kind `*/Universe` (`Invariant.no_univ_star`; each hypothesis is necessary: `no_univ_needs_*`). Also (an interpreter duty that no theorem uses; §4.1 asserts it): no micro edge has a `$` premise and a `*` target, and every micro edge with a `$` target has a concrete premise mark. | The interpreter (`interpreter.md` I7). |
| S9 | A conjunction literal has a concrete mark (`NDExact.LitConc`). Without it the ND exactness is false (`NDExact.CexLit.cex_lit`). | The interpreter (a mark literal names its mark). |
| S10 | Program well-formedness: every micro edge of a statement reads from a base that the statement touches, and every call binding has the premise mark `*` (it passes every mark). With conjunctions, also: the target of a conjunctive micro edge has a concrete mark and no `*` tail (W7). (Lean: `Program.WF`, its type-filter part is S5; with conjunctions `ND.NProg.WF`, its part `target`.) | The interpreter (`interpreter.md` §2, §3.1, §5.3). |
| S11 | The backward contracts (only the backward run and contract B, §6.6, need them): (a) every call binding has the target mark `*` (`Reverse.BindTargetsStar`); (b) every statement micro edge is mark-reversible (§1; `Backward.StmtsMarkRev`); (c) no call binds the zero base back (`Backward.NoZeroBack`); (d) every instruction that is not a call keeps the zero fact: a statement that touches the zero base has the micro edge from the zero fact to the zero fact, no cleaner is on the zero base, and a type filter on the zero base accepts the empty path (`Backward.ZeroKept`); (e) for every method that is a root or the callee of a call, every node on a CFG path from the method entry has a CFG path to the method exit (`Backward.ExitReach`); (f) every sink pattern has the tail `$` or `[any]` (§4.9). | The interpreter (`interpreter.md` I11); for (e) the CFG normalisation (it wires the code that never returns to the exit). |
| S12 | The static construction rules (run 1, §4.10). A STATIC POSITION is the premise path of a statement micro edge on the static base `S`, or the path of a sink pattern on `S`, CUT to at most two accessors (the class and the field: `[<C>, f]`, `[<C>]`, Go `[<G>]`). So a path above a static position is the root path `[]` or a class `[<C>]`. (a) A statement micro edge from `S` to `S` is an identity restriction `S.q.* →_{E} S.q.*` (the keep edges of a write), or a FIELD-TO-FIELD edge: its premise path and its target path are both at or below a static field (a pass rule between static fields). (b) A statement micro edge from another base into `S` whose target path lies strictly above a static position has a `$` target and a `$` premise with a concrete mark: a mark on a class position, `zero.$ (zeroMark) → S.<C>.$ (T)` or `Q.$ (T') → S.<C>.$ (T)`. So no rule makes a `*` or an `[any]` fact on a bare class position, and no pass rule reads or writes a bare class position. (c) A call binds `S` only by `S.* → S.*`, in both directions. (d) The class accessor is not counted, and `L ≥ 1`, so the field limit never cuts a path to a path above a static position. (e) A cleaner on `S` names its mark. (`RemoveAllMarks` on `S`, at any depth, is not a cleaner: it is the kill of a strong write, `interpreter.md` §1.4.) (f) `S` is not the zero base. (g) The abstraction of run 1 is the policy of §6.2. A rule position can be deeper than a static field: below the static field the ordinary rules apply. (Lean: `Statics.SWF`, its parts `ss`, `write`, `toC`, `fromC`, `cut`, `clean`, `base`, `alpha`; `PosIn`, `AbovePos`, `abovePos_len`.) A restricted run needs only (a) to (d), with its own field limit in (d) (`StaticsIter.SWFR`), and persisted records that keep the static invariant (§4.10). | The interpreter (`interpreter.md` I12). |
| S13 | Validity. The exactness and confirmation theorems read a VALIDITY predicate on locations (§4.8). Every type filter accepts every valid location of its base (`Exact.FiltValid`). The validity goes back along every statement micro edge and along every call binding, into the callee and back: a valid end location of the edge comes only from a valid start location (`Exact.BackOK`). With conjunctions, the validity also goes back from the target of a conjunctive micro edge to each literal: every location of a literal is valid if a location of the target is valid (`NDExact.ConjOK`). Without these conditions the valid forms are false (`Exact.CexFilt`, `NDExact.CexConjOK.cex_conjOK`). | The type-filter placement (`interpreter.md` §5.1). |
| S14 | Persisted records are exact: every pair of a persisted record whose end location is valid (S13) is a concrete flow (`RExact.RecsExact`; the valid form `RExact.RecsExactV`). The records of one forward run are exact if the records that the run reads are exact (run 1 reads none): run 1 (`RExact.recs_of_D`, `recs_of_D_valid`), a forward restricted run (`recs_of_DR`, `recs_of_DR_valid`); the union of two exact record sets is exact (`recs_union`). Over the whole run sequence the persisted forward records stay exact (`BExact.recsSeq_exact`, `recsSeq_exactV`), and a normal backward summary with a non-zero premise reverses into an exact forward record under S11 (c) (`BExact.rev_record_exact`). So S14 is a theorem for the records of §8.7 R1, not an extra assumption. | The record store (§8.7). It persists only the normal summary edges of the forward runs and the normal backward summary edges whose premise is not the zero fact (§8.7 R1). |

Inside this scope:

* Run 1 is SOUND: an edge covers every concrete flow (§3.5), and the run reports every real vulnerability (§10.1).
* A later run is SOUND RELATIVE TO ITS DEMAND: it reports every real vulnerability whose witness the demand covers,
  and it passes the same witness on as the demand of the next run (§10.7).
* The backward run of §9.2 satisfies contract B (§6.6; `Backward.B_general`), so EVERY FORWARD run reports
  every real vulnerability (`Backward.iteration_general`; `Backward.iteration_sound_M_D` for any backward step that
  satisfies contract B). So the analysis can stop at any forward run, and a vulnerability that a forward run does not
  report is not real.
* Inside the smaller scope of NORMAL edges the analysis is also EXACT. An end location is VALID if every type filter
  accepts it (S13); real values have only valid locations. Every pair of a normal edge whose end location is valid is a
  concrete flow: in run 1 under S7 and S13 (`Exact.edge_exact_valid`), in a restricted run also under S14
  (`RExact.edge_exactR_valid`; §10.3, §10.7).
* Exactness is against the path-insensitive reference semantics (§3.5). A conjunction (§4.6) and a rule condition that
  one fact does not decide (§4.2) are expected over-approximations. They do not move an edge to the demand layer. A
  normal edge with conjunctions is exact against the support semantics `ND.TaintN`, under S7, S9, S10 and S13
  (`NDExact.nd_edge_exact`; the valid form `nd_edge_exact_valid`).
* A CONFIRMED vulnerability (§4.9) whose sink pattern covers only valid locations is real for the reference semantics
  (§3.5), modulo the expected false-positive sources of §11.1. In run 1 this holds under S7, S10 and S13
  (`Confirmed.confirmed_real_valid`), in a restricted run also under S14 (`RMain.confirmed_real_M_valid`). For a
  program without type filters the same holds with no validity condition (`Confirmed.confirmed_real`,
  `RMain.confirmed_real_M`). These theorems are for programs without conjunctions and without the static rule.
* With conjunctions, a vulnerability that run 1 confirms with the joint support of §4.9 is real for the support
  semantics, under S7, S9, S10 and S13 (`NDConfirmed.confirmed_real_N`; the valid form `confirmed_real_N_valid`).
* With the static rule of §4.10, a vulnerability that run 1 confirms is real, under S7 and S13 (`StaticsConfirmed.confirmed_realS`;
  the valid form `confirmed_realS_valid`).

---

## 1. Terms

| Term | Meaning |
|---|---|
| base | A local, an argument, `this`, the return value (`ret`), the exception, a constant, the static base `S` (`ClassStatic`), or the zero base. |
| static base `S` | The base that holds every static field (JVM) and every global (Go) at a static path (§4.10). |
| accessor | A field, an array element, a class accessor `<C>`, or another structural step (type info, value). Not a mark, not `[any]`, not `$`. The set of accessors is unbounded: for each finite set of accessors there is an accessor outside it. So a `*/E` tail always admits a continuation other than `[]`, and `*/E` is never `$`. |
| counted accessor | A field or an element accessor. The field limit counts only these. |
| path | A finite list of accessors. |
| chain | The base and the concrete path of a fact or of a pattern, without its tail and its mark. |
| location | A concrete triple (base, path, mark): the value at `base.path` carries `mark`. |
| zero location | The location `(zero, [], zeroMark)`: the one location of the zero fact (§2.4). |
| tail | The end of a fact path: `*` (abstract), `[any]` (any continuation), or `$` (exact). |
| exclusion | A finite set of first accessors that a `*` continuation must not start with. |
| Universe | The exclusion of every accessor. A `*/Universe` tail admits only the empty continuation `[]`. The AP has no `*/Universe` fact, edge or initial fact (S8). The model keeps it only to encode a `$` premise (§11.2). |
| kind | The tail with its exclusion: `*/E`, `[any]` or `$` (Lean: `Kind`). |
| mark | `*` (abstract: the mark of the premise passes), `T` (concrete), or `*∖X` (abstract except the marks of `X`; conclusions only). The set of marks is unbounded, so two abstract marks always have a common mark. |
| zero mark | The concrete mark of the zero fact (Lean: `zeroMark`). No rule names it. |
| effective mark | The mark that a sink reads on an edge `i → f`: `f.mark` if it is concrete, else `i.mark` if it is concrete, else abstract (§4.9). |
| fact | A tuple (base, path, tail, exclusion, mark). §2. |
| premise | An initial fact of an edge: a fact that the edge depends on, at the method entry (forward run) or at the method exit (backward run). Every edge has a PREMISE SET. The zero fact is a premise like every other initial fact: a zero-to-fact edge has the premise set `{zero}` (§2.4). |
| conclusion | The final fact of an edge: the fact at a statement. |
| edge | (premise set, layer, statement, conclusion), with one exclusion. §4.6 names the edge by the number of its premises that are not the zero fact: none, a ZERO-TO-FACT edge (the premise set `{zero}`); one, a FACT-TO-FACT edge (the premise set `{i}`, or `{zero, i}` for a conjunction result); two or more, an ND edge. |
| propagation edge | An edge that the analysis derives and propagates inside a method. Not a micro edge. |
| caller edge | The propagation edge `(i, layer) → c` of the caller at a call statement (`i` is its premise set). The call binds its conclusion `c` into the callee (§5.3). |
| caller fact | The conclusion `c` of a caller edge, in caller coordinates. After a binding edge it is a bound fact, and after the cleaners an added fact. A summary edge of the callee applies to the added fact, not to the caller fact (§4.3). |
| layer | `normal` or `demand`. |
| normal edge | An edge in the normal layer (Lean: `AFact.complete`; §11.2). Only a normal summary edge can become a record. |
| demand-layer edge | An edge in the demand layer. The analysis uses it in its own run like every edge. It never persists it and never reverses it. |
| exact | (1) The `$` tail. (2) A property of an edge or a record: every pair of it is a concrete flow (no false pair). (The cleaner reach `exact` of §4.7 is a third, local meaning.) |
| mark-reversible | An edge `i → f` is mark-reversible if `f.mark` is abstract (`*` or `*∖X`), or if `i.mark` is concrete (§9.1; Lean: `Reverse.MarkRev`). |
| exact shape | An edge has an exact shape unless it is `*/E → $` or `*/E → [any]` with a premise exclusion `E ≠ {}` (§9.1; Lean: `Reverse.ExactShape`). |
| touched base | A base that a statement or a call can change. A fact on an untouched base passes the statement unchanged. A fact on a touched base keeps only what a micro edge gives (§4.2). |
| statement summary | What the interpreter gives for one statement: the touched bases, the micro edges and the type filters (`interpreter.md` I1). Not a summary edge. |
| micro edge | One edge of a statement summary, or one call binding edge, that the interpreter makes. A callee summary edge is NOT a micro edge (§4.3). |
| summary edge | An edge whose statement is the method exit (forward run) or the method entry (backward run). |
| record | A normal summary edge with one premise that the analysis persists for later runs (§8.7 R1). |
| summary rewriter | An interpreter feature that cleans the summary results at a call (`interpreter.md` §5.2). Not a summary edge. |
| bound fact | A caller fact after a binding edge into the callee, in callee coordinates. The sinks of the call check it (`interpreter.md` §4.5 step 3). |
| added fact | A bound fact after the cleaners of the call (`interpreter.md` §4.5 step 5.1). The callee gets it. |
| link | One (added fact, caller edge) pair in the added fact store of the callee (§8.3). A standing request checks every link (§4.5, §4.10). |
| abstraction, emission | The function that selects the initial facts for an added fact. §6. |
| policy, policy fact | The run-1 abstraction (§6.2; Lean: `policy1`). A policy fact is an initial fact that it gives: `(x, [], *, {}, *)` for an added fact on the base `x`. In this spec the word "policy" alone always means this abstraction. The MARK POLICY of the interpreter is a different rule: it drops a concrete mark on a primitive value (`interpreter.md` §5.1). |
| request | Run 1 only. A MARK request asks for a concrete mark on an initial fact (§4.5). A POSITION request asks for a static position: it comes from a statement micro edge whose premise lies strictly below an identity static `*` edge at the root path `[]` or at a class `[<C>]`, and it asks for that premise path cut to at most two accessors (§4.10). |
| chain answer, request chain | The REQUEST CHAIN is the base and the path of the premise of a mark request. The CHAIN ANSWER `answer(i, a, T)` is the answer of §4.5 at the request chain (Lean: `answerInit`). |
| static position | The premise path of a statement micro edge on `S`, or the path of a sink pattern on `S`, cut to at most two accessors: a static field `[<C>, f]` or a class `[<C>]` (S12). |
| standing | A standing request, subscription or conjunction fact stays active until the end of its run: it also acts on every matching event that comes later. |
| root | An entry method of the analysis (a ROOT METHOD). Every run starts with the zero fact as an initial fact of each root (Lean: `roots`). Not the same as the ROOT PATH: the empty path `[]` of a base. "At the root `[]`" and "the static root" (the position `(S, [])`) name the root path. |
| run | One analysis pass in one direction with one field limit `L`. The runs are numbered in order: run 1 (forward), run 2 (backward), run 3 (forward), and so on (§6.6). |
| restricted run | Every run after run 1, forward or backward. It strictly follows its demand (§6.1). |
| demand pattern | A pair of patterns that a restricted run gets from the run before it, in the orientation of the restricted run: the entry pattern `D-c` and the exit pattern `D-p` (or none, if the demand does not reach the method exit). Lean: `DemandEdge` (`din`, `dout`). The letters come from the run that made the pattern: `D-c` is a CONCLUSION of that run, and `D-p` is a PREMISE of that run (§9.2). |
| demand (of a run) | The set of demand patterns that a restricted run gets (§9.2 states the hand-off; §8.6 stores it). Not the same as the demand layer. |
| demanded flow, demanded witness | A concrete flow is DEMANDED if at every call in it that returns, one demand pattern of the callee has a `D-c` that covers the entry location of the callee with its mark, and a `D-p` that covers the exit location (marks ignored). A witness is DEMANDED if its flows are demanded and, at every call down, one demand pattern of the callee has a `D-c` that covers the entry location with its mark (Lean: `FlowR`, `ReachR`; §6.6). |
| demand vulnerability | A triggered vulnerability that is not confirmed (§4.9). Not the same as a demand-layer edge. |
| concrete flow | A chain of concrete steps (§3.5; Lean: `Flow`). |
| witness | The concrete flow of a vulnerability: from the zero location of a root, through a chain of calls down, to a location that the sink pattern covers (§3.5; Lean: `Reach`). |
| reference semantics, real | The concrete semantics of §3.5, with the rules read as §3.5 says. A flow or a vulnerability is REAL if it exists in the reference semantics. |
| support, supported | A property of a PREMISE SET, not of one premise. A premise set is SUPPORTED if one call statement supplies every premise of it exactly, through normal caller edges whose own premise sets are supported, down from the zero fact of a root. The support is a tree (§4.9 condition 3; Lean: `Confirmed.Sup`, `RExact.SupM`, `NDConfirmed.SupN`). |
| strong enough | A fact `a` is strong enough for a premise `j` if `applicable(j, a)` (§4.3): `j` covers `a`, and an `[any]` premise needs an `[any]` fact. Such a fact is at or below the premise (§4.1 case `below`). |
| not strong enough | The fact is not strong enough. A fact above the premise (§4.1 case `above`) is never strong enough: the result loses the correlation. |
| satisfies | A fact satisfies a premise if the caller may apply the summary edges of that premise to it: `applicable` in run 1, `inside` in a restricted run (§4.3). |
| concrete run | A run in which every fact has a concrete mark. Every restricted run is concrete: a forward one (§6.3) and a backward one, whose seeds have concrete marks (`BExact.DB_concrete`). |
| ND edge | A NON-DISTRIBUTIVE edge: an edge whose premise set has two or more premises that are not the zero fact. A conjunction makes it (§4.6). |
| prescan | A pass of the current analyzer core that runs before the new analysis. It resolves the lambdas and the closures and gives their type info (§7.6, `interpreter.md` §3.9). The new AP only reads its result. |
| method key | `MethodEntryPoint` (context plus entry statement), as today (Kotlin: `MethodKey`). The method key of a method is the same in every run. |

NOTATION. `ap.md` and `interpreter.md` use these forms. The interpreter-only forms are in `interpreter.md` §0.

| Form | Meaning |
|---|---|
| `(x, p, t, E, m)` | A fact or a pattern: the base `x`, the path `p`, the tail `t`, the exclusion `E`, the mark `m` (§2.1). |
| `(x, p, t, m)` | The same. The exclusion is Empty, or the kind `t = */E` carries it. |
| `(x, p, t)` | A pattern whose mark is not relevant (for example a pattern read as locations, §3.2). |
| `.`, `[]`, `.f.g`, `[f, g]` | A path. `.` and `[]` are the empty path. `.f.g` and `[f, g]` are the path of the accessors `f` and `g`. |
| `p ++ r`, `p·r` | The path `p` followed by the path `r`. |
| `x.p.*` | A micro-edge side or a fact `(x, p, *, {}, *)`: the `*` tail with the mark `*`. |
| `x.p.$ (T)`, `x.p.[any] (T)` | The tail `$` or `[any]` with the concrete mark `T`. Without `(T)` the mark is `*`. |
| `i → f` | An edge with the premise `i` and the conclusion `f`. `j → g` is a summary edge. `{j1, …, jk} → g` is an ND edge. |
| `a →_{f} b`, `i →_{E} f` | A micro edge or an edge with the exclusion `{f}` or `E`. With no subscript the exclusion is Empty. |
| `Zero → (layer, statement, fact)` | A zero-to-fact edge: an edge with the premise set `{zero}`. |
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

* `path` — the concrete accessors. It never contains `[any]`, a mark or `$`.
* `tail ∈ {*, [any], $}`.
* `exclusion` — a finite set of accessors, only with the `*` tail.
* `mark ∈ {*, T}` for a premise; `mark ∈ {*, T, *∖X}` for a conclusion.

### 2.2 Edges, layers, the edge exclusion and the mark exclusion

An edge is `(premise set, layer) → (statement, conclusion)`. A fact-to-fact edge is also written
`(premise, layer) → (statement, conclusion)`. The zero-to-fact edge is `Zero → (layer, statement, fact)`: its premise
set is `{zero}`. An ND edge is `({premise1, …, premisek}, layer) → (statement, conclusion)` with `k ≥ 2` premises that
are not the zero fact (§4.6).

* An edge has ONE exclusion `E`. In a CORRELATED edge (`*` premise, `*` conclusion) the premise and the conclusion
  share it: for `(x, p, *) →_E (y, q, *)`, the value at `x.p.σ` flows to `y.q.σ` for every `σ` that `E` admits. The
  model stores `E` on the conclusion (the kind `*/E` of the target). If the premise also stores an exclusion, the edge
  exclusion is the union of the two (`SharedExcl.applyEdge_shared_excl`, `den_shared_excl`). An implementation stores
  `E` once, on the edge.
* An UNCORRELATED edge (the conclusion is `$` or `[any]`) has the Empty exclusion on its conclusion. Every operation of
  §4 gives an uncorrelated result the Empty exclusion; if the result loses a restriction, it goes to the demand layer
  instead (`lostCorr`, §4.1). A `*/E` premise of an uncorrelated edge (a restricted run can emit one, §6.3) keeps `E` in
  its premise: `E` restricts the premise continuation only.
* The MARK EXCLUSION `X` of a conclusion `*∖X` stops the marks of `X`: the value at the premise location flows to the
  conclusion location only if its mark is not in `X`. It belongs to the edge, as the exclusion does; a cleaner makes it
  (§4.7). A premise never has one.
* The policy facts and the chain answers of run 1 have the Empty exclusion (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`). A position answer `(S, p, *, {}, *)` has the Empty exclusion by its definition
  (§4.10 item 2). The mark answer on a static premise is the added fact itself (§4.10 item 4). It has a concrete
  mark, so by W2 it has the `$` or the `[any]` tail and the Empty exclusion. (The Lean theorems above do not cover
  these two static answers; the statements follow from their definitions.) In a restricted run an emitted fact can
  have the exclusion of the demand (the meet with a `*/E` entry pattern, §6.3). It has a concrete mark, so it starts
  in the demand layer (§6.5) and makes no record. So the exclusion of a normal edge is a property of its conclusion.
  Only a strong field write makes it larger.
* The LAYER is part of the edge identity. A micro edge has no layer (§4.2): the layer belongs to the propagation edge.
  Only these AP operations put a propagation edge in the demand layer:
  * the start fact of an initial fact with the `[any]` tail, or with the `*` tail and a concrete mark (§6.5);
  * the case `above` of §4.1, and a lost correlation (`lostCorr`, §4.1);
  * an `[any]` result (W6), and the normal form W2 of a `*` result (§4.1 step 6);
  * the cut of the field limit (§4.4);
  * a conjunction with an input that is in the demand layer or that its literal does not cover (§4.6);
  * the application of a demand-layer summary edge (§4.3), also of a summary with several premises (§4.6);
  * the `part` rows of the cleaner that give a demand-layer result (§4.7).

  A demand-layer input gives a demand-layer result. The layer of an edge never goes back to normal
  (`Invariant.applyEdge_demand_monotone` and the related lemmas).

Lean: `PFact` (a premise or a conclusion; the conclusion `*/E` carries the exclusion of the edge; the mark is `MarkA`
with `star`, `conc t`, `starEx x`) and `AFact` (a conclusion plus `demand : Bool`, the layer).

### 2.3 Well-formedness rules

| Rule | Text |
|---|---|
| W1 | An edge with no `*` side has the Empty exclusion. |
| W2 | A conclusion with the `*` tail has the mark `*` or `*∖X` and is in the normal layer. A premise may have the `*` tail with a concrete mark (a request answer in run 1; in a restricted run, the meet of an added fact with a `*/E` entry pattern). |
| W3 | In a run with the field limit `L`, every result of an operation has at most `L` counted accessors (§4.4). This holds if the field limit does not decrease from run to run (§6.6): then a premise emitted from a demand chain (§6.3) and a fact that passes an untouched base are also in the bound. A micro edge (§4.2) has no bound. W3 is argued, not proved (§11.2). |
| W4 | `[any]` is a tail only. A path has no inner `[any]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. |
| W6 | A conclusion with the `[any]` tail is in the demand layer. |
| W7 | Only a conclusion has a mark exclusion. An edge whose premise set has two or more members (an ND edge, or a conjunction result `{zero, i}`, §4.6) has no `*` tail. |

W2 holds for every derived fact, in run 1 and in every forward restricted run (`Invariant.final_star_legal`,
`RExact.final_star_legalR`). The backward run is concrete (`BExact.DB_concrete`); that it satisfies W2 is argued (§11.2).

W6 only moves edges from the normal layer to the demand layer (§11.2 gives the difference to the model). The
interpreter has one kind of `[any]`-target micro edge: the any-field rules, a source or a pass rule with an `[any]`
target (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`; `interpreter.md` §4.1). Under W6 every result of these rules is in
the demand layer. So an `[any]` result never makes a record, and a vulnerability whose taint comes only from an
`[any]`-target source is never confirmed: it stays a demand vulnerability.

No exclusion is Universe (§1). A `*/Universe` conclusion needs a `$`-premise edge that acts on a `*`-tail fact. Every
`$`-premise micro edge has a concrete premise mark (S8: `zeroMark` for sources, `T` for conditional sources). A `*`-tail
fact has the mark `*` or `*∖X` (W2). So the mark gate never lets such a fact through (§4.1 step 4).
`Invariant.no_univ_star` proves it under S8, and `Invariant.final_star_legal` proves W2 for every derived fact.

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. Its one location is the zero location. An unconditional source rule
is a micro edge from the zero fact (a conditional source reads another fact, `interpreter.md` §4.1). The zero fact is
a premise like every other initial fact: a zero-to-fact edge is an edge with the premise set `{zero}`, in the normal or
the demand layer, and a conjunction result can have the zero fact in its premise set (§4.6). The cases where an
operation treats the zero fact in a special way:

* the statement transfer (§4.2) and the call (§3.5, §5.3): the zero fact passes, and it enters every resolved callee;
* the conjunction (§4.6): the zero fact does not count for the name of the edge;
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
| `$` | `σ = []` | `τ = []` |

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
`PFact.covers`, `den`, `MarkA.admits`, `MarkA.passes`.

Derived relations:

* `i` COVERS the fact `c` if every location of `c` is a location of `i` (Lean: `coversB`). It compares the marks: the
  marks of `c` must be a subset of the marks of `i` (Lean: `markSubB`).
* Two facts OVERLAP if they have a common location with the marks ignored (Lean: `overlapB`). Every overlap test of
  this spec ignores the marks: the request match (§4.5), the conjunction store (§4.6), the sink check (§4.9) and the
  restriction (§6.4). Each of these places tests the marks separately.
* The restriction reads a demand pattern as LOCATIONS without marks (`PFact.coversLoc`). The emission and the demanded
  flows read the entry pattern with its mark (`PFact.covers`).

### 3.3 Exclusion algebra and merge rules

* The edge exclusion is the union of what the model stores on the two sides (`SharedExcl.applyEdge_shared_excl`).
* MERGE RULE 1: two edges with the same premise, the same layer, the same exclusion and the same mark exclusion merge
  their conclusions (union).
* MERGE RULE 2: two edges with the same premise, the same layer and the same conclusion merge their exclusions by
  INTERSECTION: `admits(E1 ∩ E2, σ) = admits(E1, σ) ∨ admits(E2, σ)`. The union of the two relations is exact
  (`Subsume.merge_inter`).
* MERGE RULE 2 FOR MARKS: two edges with the same premise, layer, exclusion and conclusion but mark exclusions `X1`, `X2`
  merge into one with `X1 ∩ X2`: a mark passes the merged edge if and only if it passes one of them
  (`Tree.rule2_mark`).
* A UNION of exclusions happens only along one derivation (a field write after another, a cleaner after another). A
  union across two different edges is FORBIDDEN: it removes pairs that one of the two edges has
  (`Subsume.union_loses_pairs`).

### 3.4 Reference types and tests

The reference forms of §4 and §6 use these types. A premise, a pattern and an added fact are a `Pattern`: a path fact
with the exclusion of its `*` tail. The implementation interns a premise as an `InitialAp` (§7.1).

```kotlin
enum class Tail { STAR, ANY, EXACT }

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

/** `*` is Star(MarkSet.EMPTY). A premise never has excluded marks. A demand entry pattern has them only when it comes
 *  from a run-1 summary conclusion; then it counts as `*` (§6.3). An added fact can have them. */
sealed interface MarkSlot {
    data class Star(val excluded: MarkSet) : MarkSlot     // *  or  *∖X
    data class Concrete(val mark: TaintMark) : MarkSlot   // T; the zero mark is a concrete mark
}

data class PathFact(val base: AccessPathBase, val path: List<Accessor>, val tail: Tail, val mark: MarkSlot)

/** A premise, a demand pattern or an added fact: a fact with its own exclusion (Empty unless the tail is STAR). */
data class Pattern(val fact: PathFact, val exclusion: ExclusionSet)

/** A demand pattern (§1): the entry pattern D-c and the exit pattern D-p (null: the demand does not reach the exit). */
data class DemandPattern(val entry: Pattern, val exit: Pattern?)

/** §3.1: the tail admits the continuation r. */
fun tailAdmits(tail: Tail, exclusion: ExclusionSet, r: List<Accessor>): Boolean = when (tail) {
    Tail.STAR -> exclusion.admits(r)          // r = [] or the first accessor of r is not excluded
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
    Tail.STAR -> when (c.fact.tail) {
        Tail.EXACT -> true
        Tail.ANY -> i.exclusion == ExclusionSet.Empty
        Tail.STAR -> i.exclusion.isSubsetOf(c.exclusion)
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

/** §4.3, run 1 and every record: the premise j covers the added fact a (Lean: applicable). */
fun applicable(j: Pattern, a: Pattern): Boolean =
    covers(j, a) && (j.fact.tail != Tail.ANY || a.fact.tail == Tail.ANY)

/** §4.3, the summaries of a restricted run: j lies inside a as locations, and markSub(j, a) (Lean: satI). */
fun inside(j: Pattern, a: Pattern): Boolean =
    covers(a.copy(fact = a.fact.copy(mark = MarkSlot.Star(MarkSet.EMPTY))), j) && markSub(j.fact.mark, a.fact.mark)
```

An empty Concrete `ExclusionSet` must not exist (return `Empty`). `Accessor` is an interned accessor, and
`AccessorIdx` is its intern id (the accessor interning of today, §7.6): `admits(r)` reads the `AccessorIdx` of the
first accessor of `r` and tests it against `ids`. Keep the excluded accessors as a CANONICAL (sorted, de-duplicated)
`IntArray` of `AccessorIdx`; the same for `MarkSet`. The edge trees are keyed by both, so two equal sets
must be equal values. Because the sets of accessors and marks are unbounded (§1), these tests are exact: `covers`,
`overlap` and `cleanPos` (§4.7) need no "all accessors" or "all marks" case.

### 3.5 Concrete semantics

The theorems compare the analysis with this semantics. It is the program that the micro edges describe (S1). It is
alias-free and location-level. Lean: `Basic.lean` (`Stmt.step`, `Flow`, `Reach`).

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
* REFERENCE SEMANTICS OF RULES. The interpreter rules are read in this semantics as follows (S1). A source, a sink or a
  pass rule fires with every negated mark literal true. A conjunction of literals on different facts is
  path-insensitive: each literal can hold on its own path. Its semantics is the SUPPORT semantics: a location is tainted
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
* a restricted run: the request row of step 4 never occurs (every fact is concrete, §6.3). The implementation asserts
  it;
* `concat` does not apply the field limit. The operation that calls it does (§4.4).

Preconditions. `concat` ASSERTS them; an edge that breaks one is a bug of the interpreter or of the analyzer:

* the premise mark is `*` or `T`, never `*∖X` (S7);
* a `$` premise has a concrete mark (S8);
* a `$` premise has no `*` target (S8).

So a `$` premise meets only facts with a concrete mark: on a `*`-tail fact (mark `*` or `*∖X`, W2) the mark gate gives a
request or nothing (step 4). A summary edge meets the preconditions too: an initial fact never has `*∖X` (§2.2); a `$`
initial fact is the zero fact, an answer or an emission, all with a concrete mark; and a concrete premise has only
concrete conclusions (`Coverage.edge_conc`), which have no `*` tail (W2).

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
premise for every `r`. For a `*` target and `r ≠ []`, `E` must also admit `r` (row 1). Then:

| `to.tail` | `r` | `c.tail` | result path | result tail | to the demand layer |
|---|---|---|---|---|---|
| `*` | `≠ []` (`E` admits `r`) | any | `to.path ++ r` | `c.tail` (with `Ec`) | no |
| `*` | `[]` | `$` | `to.path` | `$` | no |
| `*` | `[]` | `*/Ec` | `to.path` | `*/(Ec ∪ E)` | no |
| `*` | `[]` | `[any]` | `to.path` | `[any]` | yes (W6) |
| `[any]` | any | any | `to.path` | `[any]` | yes (W6) |
| `$` | any | `*/Ec` | `to.path` | `$` | if the correlation of `c` restricts the premise (`lostCorr`) |
| `$` | any | `[any]` or `$` | `to.path` | `$` | no (an `[any]` `c` is in the demand layer already, W6) |

`lostCorr` is true if `Ec ∪ E ≠ {}` for `r = []`, or `Ec ≠ {}` for `r ≠ []`. Otherwise the premise admits every
continuation, and the uncorrelated result is exact (`Exact.applyEdge_exact`).

Case `above r`. The premise decides WHETHER the edge applies: the tail of `c` must admit `r` (`*/Ec`: `Ec` admits `r`;
`[any]`: yes; `$`: no overlap). The target decides WHAT comes out: `(to.path, $)` if `to.tail = $`, else
`(to.path, [any])`. The result is always in the demand layer: a `*` fact loses its correlation, and an `[any]` fact is in
the demand layer already (W6).

Step 4 — mark gate. The premise mark `from.mark` (never `*∖X`) against the fact mark `c.mark`:

| `from.mark` | `c.mark` | result |
|---|---|---|
| `*` | any | apply |
| `T` | `T` | apply |
| `T` | `T' ≠ T` | empty |
| `T` | `*∖X`, `T ∈ X` | empty (the mark was cleaned) |
| `T` | `*` or `*∖X` with `T ∉ X` | NO fact; the request `T` on the premise of `c` (§4.5). Run 1 only: a restricted run has no such fact (assert) |

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

* W6: a result with the `[any]` tail is in the demand layer.
* W2: a result with the `*` tail and (a concrete mark, or the demand layer) becomes uncorrelated: `[any]` with the
  Empty exclusion, in the demand layer.

The step only enlarges the fact (`CoreAux.norm_sound`, `Invariant.demand_of_any_ok`). The step does not apply the
field limit (§4.4).

Theorem `Core.applyEdge_sound` (THE CORE LEMMA): `concat` covers the composition of the fact relation and the edge
relation, or raises the request for the premise mark. This holds in both cases: at or below the premise, and above it.

Reference form (the vector tests of §13 compare the tree implementation with it). It uses the types of §3.4. The edge
carries its one exclusion:

```kotlin
/** A path edge `from → to` with its ONE exclusion (W1: Empty if no side has the STAR tail). */
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet)

/** The current conclusion: the fact, the exclusion of its edge, the layer of its edge. */
data class Conclusion(val fact: PathFact, val exclusion: ExclusionSet, val demand: Boolean)

private fun PathEdge.premiseAdmits(r: List<Accessor>): Boolean = when (from.tail) {
    Tail.EXACT -> r.isEmpty()
    else -> exclusion.admits(r)        // `*`: E; `[any]`: E is Empty unless the target is `*` (row 1)
}

private class Shape(val path: List<Accessor>, val tail: Tail, val exclusion: ExclusionSet, val demand: Boolean)

private fun below(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    if (!edge.premiseAdmits(r)) return null
    val to = edge.to
    return when (to.tail) {
        Tail.STAR -> when {
            r.isNotEmpty() -> Shape(to.path + r, c.fact.tail, c.exclusion, demand = false)
            c.fact.tail == Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, false)
            c.fact.tail == Tail.STAR -> Shape(to.path, Tail.STAR, c.exclusion.union(edge.exclusion), false)
            else -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6
        }
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6
        Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty,
            demand = c.fact.tail == Tail.STAR &&
                (if (r.isEmpty()) c.exclusion.union(edge.exclusion) else c.exclusion) != ExclusionSet.Empty)
    }
}

private fun above(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    val admitted = when (c.fact.tail) {
        Tail.STAR -> c.exclusion.admits(r); Tail.ANY -> true; Tail.EXACT -> false
    }
    if (!admitted) return null
    val tail = if (edge.to.tail == Tail.EXACT) Tail.EXACT else Tail.ANY
    return Shape(edge.to.path, tail, ExclusionSet.Empty, demand = true)
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
    check(from.tail != Tail.EXACT || from.mark is MarkSlot.Concrete)                    // S8
    check(from.tail != Tail.EXACT || edge.to.tail != Tail.STAR)                         // S8
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
                check(!restricted)                                            // a restricted run is concrete
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

/** Step 6: W6, then the normal form W2. */
fun normalize(f: PathFact, exclusion: ExclusionSet, demand: Boolean): Conclusion = when {
    f.tail == Tail.ANY -> Conclusion(f, ExclusionSet.Empty, demand = true)                                  // W6
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

1. Liveness (JVM only). If `c.base` is a local that is dead at the statement, drop `c` (`interpreter.md` §2.1 step 1).
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
* A RESTRICTED RUN has no request and no position request (§6.1).
* THE BACKWARD RUN applies the reversed statement (§9.2) with steps 2, 4 and 6 only: no liveness drop and no type
  filter. (Without a drop the backward run only keeps more requirements, so this is sound.)

Every micro edge (a statement edge, with its alias edges, or a call binding edge) is precise and complete (S1, S2).
The field limit never applies to a micro edge: a micro edge keeps its full paths, of any length. The analyzer applies
the limit to the RESULT, after it applies the micro edge to the propagated edge (§4.4; Lean: `transfer` limits the
results, and `Program.WF` puts no bound on a micro edge).

A micro edge has NO LAYER. The layer belongs to the propagation edge, and only the AP operations of §2.2 change it. The
interpreter sets no layer. A negated mark literal counts as true for a source, a sink and a pass rule (the reference
semantics, §3.5). This is the expected over-approximation of a path-insensitive engine, as the conjunction is (§4.6).
Positive literals on different facts make a conjunction for a source or a pass rule (§4.6), and a conjunctive sink
(§4.9). A cleaner applies only its decided part (§4.7, `interpreter.md` §4.2).

The cases below are checked by `decide` in `Cases.lean`. The two static rows follow §4.10. The model checks the read
row (`Statics.gen_read_DS`, `gen_read_sreq`); the write row follows from §4.10 item 1 and is not checked separately:

| Statement | Input fact | Result | Layer |
|---|---|---|---|
| `a = b.f` | `(b, .f, *, E, *)` | `(a, ., *, E, *)` | normal |
| `a = b.f` | `(b, ., *, E, *)`, `f ∉ E` | `(a, ., [any], {}, *)` | demand |
| `a = b.f` | `(b, ., *, {f}, *)` | nothing for `a` | |
| `a = b.f` | `(b, ., [any], {}, *)` | `(a, ., [any], {}, *)` | demand |
| `a = b.f` | `(b, ., $, {}, *)` | nothing for `a` | |
| `a.f = b` | `(b, .g, *, E, *)` | `(a, .f.g, *, E, *)`; under `L = 1`: `(a, .f, [any], {}, *)` | normal; under the cut: demand |
| `a.f = b` | `(a, .f, *, E, *)` | nothing (strong update) | |
| `a.f = b` | `(a, ., *, E, *)` | `(a, ., *, E ∪ {f}, *)`, no request | normal |
| `x = C.s` (run 1) | the identity static `*` edge to `(S, ., *, E, *)`, `<C> ∉ E` | `(S, ., *, E, *)`; nothing for `x`; the position request `[<C>, s]` | normal |
| `C.s = x` (run 1) | the identity static `*` edge to `(S, ., *, E, *)`, `<C> ∉ E` | `(S, ., *, E ∪ {<C>}, *)`; the class keep edge gives the position request `[<C>]` | normal |

The premise of the edge does not change in any case. Only its layer can change, from normal to demand.

### 4.3 Apply a summary edge

`applySummary(a, j, g) = concat(a, j → g, edgeDemand = the layer of the summary edge)` (§4.1; Lean: `applySummary`).
The input `a` is the ADDED FACT of a link (§1), in callee coordinates; the result has the layer of `a` on that link
(§8.3) or a higher one. PRECONDITION: `a` SATISFIES the premise `j`. The caller tests it before it applies the
summary (§5.3 events E2 and E4); `applySummary` does not test it again.

* RUN 1: `j` covers `a` (strong enough):

  ```
  applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j.tail = [any] ⇒ a.tail = [any])
  ```

  The application is the case `below`, and the mark gate passes (`applicable_mark`). The abstraction of run 1 covers
  every added fact (C1, §6.1). Lean: `coversB`, `applicable`, `applicable_sound`; reference form `applicable` (§3.4).
* RESTRICTED RUN: the premise lies INSIDE the fact as LOCATIONS (the location part of `a` covers every location of
  `j`, marks ignored), and the marks of `a` are a subset of the marks of `j` (Lean: `satI`, `RCore.satI_markSub`,
  `satI_conc_record`; reference form `inside`, §3.4). So a concrete fact satisfies a `*` premise, and a cleaned fact
  `*∖X` satisfies a `*` premise. This is the reverse of run 1: the emitted fact is `a ∩ D-c` (§6.3), so it always lies
  inside its added fact (`RCore.emitM_satI`), and it can be smaller than `a` at the same path. The application is the
  case `below` if `a` is at or below `j`. It is the case `above` if `a` is above `j` (for example `a = (x, ., [any], T)`
  and `j = (x, .f, [any], T)`); then the result is in the demand layer (§4.1 step 3).
* A RECORD `j → g` (§8.7) applies in the direction in which it was derived when `applicable(j, a)`, in every run
  after the run that made it (R4). In the other direction it applies through its reversal (R3, §9.1). A record is
  exact (S14), so the result adds no false pair. A record is not restricted.

The mark condition makes the mark gate pass: a summary application never raises a request (`Coverage.summary_step`,
`RCov.sat_step`, `RCore.summary_stepR`). A summary conclusion `*∖X` stops an added fact whose concrete mark is in `X`
(§4.1 step 5). In a restricted run the CALLEE restricts the summary by its demand patterns before it publishes it
(§6.4).

The special cases of the summary application:

* SEVERAL PREMISES. A summary with one premise, applied to a caller edge with a premise set, keeps the premise set of
  the caller edge. A summary whose premise set has two or more members (an ND summary `{j1, …, jk} → g`, or a
  conjunction result `{zero, j} → g`) applies through event E6: one added fact per member (§4.6, §5.3).
* THE BACKWARD RUN. The zero-premise summary of a callee applies to the zero fact of each caller with no restriction
  and no satisfaction test (§9.2, the balanced return).
* STATICS. A static initial fact is an ordinary premise: run 1 applies its summaries by `applicable`. An added fact
  above a static initial fact does not read its summaries; the position request (§4.10) makes the precise initial fact
  instead.
* FIELD LIMIT. The caller applies it after the binding back (§5.3 step 5, §4.4).

* The exclusion of a summary edge FILTERS the delta: the summary `(arg0, ., *) → (ret, ., */{f})` applied to the
  added fact `(arg0, ., */{})` gives `(ret, ., */{f})` (bound back to the lhs `r`), and applied to
  `(arg0, .f.g, $, T)` gives nothing.
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
* the results of the exit rules at the normal exit, before the summary edge: the exit sources and the end facts of an
  exit sink (`interpreter.md` §4.7);
* the conjunction result (§4.6) and the application of a summary with several premises (§4.6, event E6);
* the backward seed (§9.2).

The cut:

* If the path has at most `L` counted accessors, the fact does not change.
* Otherwise, cut the path before the `(L+1)`-th counted accessor. Uncounted accessors before that point stay in the
  prefix. The tail becomes `[any]`, the exclusion Empty, the mark stays (also `*∖X`), and the edge goes to the demand
  layer. `L = 0` keeps the empty path.

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

Requests exist ONLY in run 1. A forward restricted run is concrete (§6.3): it raises no request and makes no answer
(`RCov.no_reqR`, `RExact.DR_no_request`, `RMain.no_request_M`). The demand pattern already has the mark that a rule
needs. The backward run raises no request either, because its seeds have concrete marks (`BExact.DB_no_request`;
`CexSeed.cex_seed`: a seed with the mark `*` would raise one).
The implementation asserts it in every restricted run.

A position request (§4.10) works in the same way: it stands, it uses the request store (§8.8), and the events E2 and
E7 of §5.3 check it per link. Its answer and its climb are §4.10 items 2 and 3.

### 4.6 Mark conjunction: ND edges

A CONJUNCTIVE micro edge `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)` gives the mark `T` at `z.π` if every literal holds
at the statement. A literal tail `tj` is `$` (`ContainsMark`) or `[any]` (`ContainsMarkOnAnyField`). The target tail
`t` is `$` or `[any]` (W7). The interpreter makes the edge for a rule with several mark literals (`interpreter.md` §4.2,
§5.3).

* The CONJUNCTION STORE (§8.9) keeps, STANDING for the run, per (rule, statement, literal), each fact `c` at the
  statement that:
  * OVERLAPS the literal pattern `xj.ρj.tj` (§3.2, marks ignored), and
  * passes the mark gate of the literal mark `Tj` (§4.1 step 4, so `c.mark = Tj`).

  It keeps the fact with the premise set of its edge (`{zero}` for a zero-to-fact edge, `{i}`, or a larger set). Lean:
  rule `conj` of `ND.DN`.
* If the mark gate gives the request `Tj` (a fact with the mark `*`, or `*∖X` with `Tj ∉ X`), the store keeps nothing
  and raises the request (run 1, §4.5; Lean: rule `reqConj`). In a restricted run every fact is concrete, so this
  never occurs (assert). A literal has no static exception: on the static base it uses the mark request (§4.10 covers
  only the statement micro edges and the sinks).
* When a fact arrives, the store combines it with the stored facts of the other literals: one fact per literal, every
  combination. The result `z.π.t(T)` has the UNION of the premise sets. The zero fact is a member of the union if one
  input has it. The number of the members that are NOT the zero fact names the edge: 0 gives a zero-to-fact edge (the
  premise set `{zero}`), 1 a fact-to-fact edge (`{i}` or `{zero, i}`), 2 or more an ND edge. Then the field limit
  applies to the result (§4.4).
* The result is in the demand layer if one input is in the demand layer, or if its literal does not COVER it
  (`!coversB lit c`: the input has a location that is not a location of the literal, for example an `[any]` input for a
  `$` literal, or an input above the literal). An `[any]` target puts the result in the demand layer too (W6). Lean:
  `ND.conjLayer`, `ND.Example.c3_normal`. A normal result is exact against the support semantics, under S7, S9, S10
  and S13 (`NDExact.nd_edge_exact`; the valid form `nd_edge_exact_valid`).
* The engine is path-insensitive: the stored facts are per statement, not per execution path, so the literals can hold
  on paths that exclude each other (`if c then a := srcA else b := srcB; r := f(a, b)`). This is the EXPECTED
  over-approximation; it does not move the result to the demand layer. The reference semantics of a conjunction
  (`ND.TaintN`, below) is path-insensitive in the same way.
* An ND edge propagates through micro edges with its premise set unchanged. Its conclusion is uncorrelated (`$` or
  `[any]`; W7): a `*` tail is the correlation with ONE premise.
* At a call, the callee sees an ordinary added fact. A callee summary `j → g` with one premise, applied to a caller
  edge with a larger premise set, keeps the premise set of the caller edge. A callee SUMMARY WITH SEVERAL PREMISES (its
  premise set has two or more members: an ND summary `{j1, …, jk} → g`, or `{zero, j} → g`) needs one link at the
  call statement per member `jm`: an added fact that satisfies `jm` (§4.3), with its caller edge. The caller zero fact
  supplies the member `zero`. The rule is standing: the link that arrives last completes it (event E6 of §5.3; the
  store of §8.9). The result has the union of the premise sets of the caller edges. It is in the demand layer if the
  summary is, or if one added fact of the combination is in the demand layer on its link (§8.3; Lean: `ND.DN.ndBind`).
  Then the caller binds it back and applies the field limit (§5.3 step 5). In a restricted run the callee restricts
  such a summary before it publishes it (§6.4).
* An edge whose premise set has two or more members is never a record: the analysis never persists it and never
  reverses it (§8.7 R1). The backward run reverses a conjunctive micro edge into one micro edge per literal (§9.2).
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
concrete semantics (§3.5) a location keeps its value unless the cleaner cleans it (Lean: `Cleaner`, `cleansB`,
`Flow.clean`).

The cleaner compares the location set of a fact `c` with the cleaned locations, marks ignored: `inside` (every location
is cleaned), `disjoint` (no location is) or `part` (some locations are). The test is exact (Lean: `cleanPos`):

| `c` against the position `x.p` | `exact` | `below` | `atAndBelow` |
|---|---|---|---|
| another base, or apart | `disjoint` | `disjoint` | `disjoint` |
| strictly below (`c.path = p ++ r`, `r ≠ []`) | `disjoint` | `inside` | `inside` |
| at (`c.path = p`), tail `$` | `inside` | `disjoint` | `inside` |
| at, tail `*/E` or `[any]` | `part` | `part` | `inside` |
| strictly above (`p = c.path ++ r`), tail `$` | `disjoint` | `disjoint` | `disjoint` |
| strictly above, tail `*/E` | `part` if `E` admits `r`, else `disjoint` | the same | the same |
| strictly above, tail `[any]` | `part` | `part` | `part` |

The result:

| `c.mark` | cleaner mark | `inside` | `disjoint` | `part` |
|---|---|---|---|---|
| `*` or `*∖X` | `T` | `c` with `*∖(X ∪ {T})` | `c` | `c` with `*∖(X ∪ {T})`; if `T ∉ X`, also the request `T` on the premise of `c` (run 1) |
| `*` or `*∖X` | every mark | dropped | `c` | `c` in the demand layer, normalised: a `*` tail becomes `[any]` (W2) |
| `T` (cleaned) | `T` or every mark | dropped | `c` | the part that the cleaner does not surely clean: an `[any]` fact at `x.p` under a `below` cleaner becomes `(x, p, $, T)`, in the layer of `c`; any other `c` goes to the demand layer (it has a concrete mark, so it has no `*` tail, W2) |
| `T'` (not cleaned) | `T` | `c` | `c` | `c` |

Lean: `cleanRes`, `addEx`, `concPart` (§11.2 gives the difference to the model in the first row).

So the cleaner SPLITS a `*`-mark fact by the mark. The edge `*∖{T}` propagates every mark except `T`, exactly, in the
normal layer. The mark `T` goes through the cleaner only on the concrete answer of the request, which the cleaner cleans
exactly (except on `[any]`, which is in the demand layer already). The union of the two covers every real flow
(`Core.cleanRes_sound`, `Coverage.coverage`); a normal result denotes only real flows (`Exact.cleanRes_exact`).

* A summary conclusion `*∖X` stops an added fact with a concrete mark in `X` (§4.1 step 5). A sink for `T ∈ X` on a
  `*∖X` fact neither triggers nor requests (§4.9). A request for `T ∈ X` does not climb through a `*∖X` fact (§4.5).
* The mark exclusion is not tied to a position, so a field write, a field read or a cut does not change it.
* A fact that the cleaner surely cleans (`inside`) needs no request: the `T` path can only make a fact that the
  cleaner drops.
* In a restricted run every fact is concrete (`RExact.DR_concrete`, for any records): only the rows with a concrete mark
  apply, and no `*∖X` fact occurs (assert). A reused run-1 record with a `*∖X` conclusion gives a concrete mark on a
  concrete fact, or nothing (§4.1 step 5).
* THE STATIC BASE (run 1). A request that the cleaner raises on a static premise is answered as §4.10 item 4 says. A
  cleaner on `S` names its mark (S12 (e)): the all-marks `part` row makes an `[any]` static fact above a static
  position. A `RemoveAllMarks` rule on `S` is not a cleaner: it is the kill of a strong write, a statement summary
  with keep edges (`interpreter.md` §1.4).
* THE ZERO BASE. No cleaner is on the zero base (S11 (d)).
* The interpreter places the cleaner (`interpreter.md` §5.2): at a call to a cleaner method, on the bound facts before
  they enter the callee, on the facts of an unresolved call before its pass rules, and in the summary rewriter on the
  summary results. The model has no cleaner inside a call (a cleaner is an instruction of the CFG, `Instr.clean`), so
  the call cleaners are argued (§11.2).
* THE BACKWARD RUN. A cleaner is its own reversal (§9.2). `interpreter.md` §4.9 places it on the requirement at the
  callee start.
* `clean` is unconditional. Of a cleaner with a condition, the interpreter applies only the part that the cleaned fact
  decides: `ContainsMark(P, T)` with an action that removes `T` at `P` is the unconditional `(P, exact, T)`
  (`interpreter.md` §4.2). Where the fact does not decide the condition, the cleaner does not act. Cleaning there is
  unsound.

### 4.8 The type filter

A type filter `filter(b, may)` at a statement drops a fact on the base `b` whose path cannot exist on a value of the
static type of `b`. `may` is a predicate on paths. Contract (S5):

* `may` accepts every path that a real value of the static type can have;
* `may` is PREFIX-CLOSED: `may(p ++ q) ⇒ may(p)`.

Then a fact that covers a real location has a path that `may` accepts (its path is a prefix of the path of the
location), and the filter never drops it (`Core.filt_keeps`). Lean: `Instr.filt`, `Flow.filt`, rule `filt`;
`Program.WF.filtPrefix`.

The filter checks the concrete path of the fact only. It keeps a `*` or an `[any]` tail whole. The analysis does not
store a filter in a fact or an edge, and it does not propagate a filter to later statements. So a `*` or `[any]` fact
that passes a filter can still denote locations below its path that the filter rejects (`Exact.CexFilt`). Those
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
condition is necessary).

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
* If `f.mark` is `*`, or `*∖X` with `T ∉ X`: raise the REQUEST `(m, i, T)` (run 1 only; a restricted run has no such
  fact, assert). Here `i.mark` is abstract too: a concrete premise has only concrete conclusions
  (`Coverage.edge_conc`). The implementation asserts it (§11.2 gives the difference to the model).

Examples: `(x,.,$,T)` triggers, `(x,.f,$,T)` does not, `(x,.,[any],T)` triggers, `(x,.,*,{},*)` raises the request
`T`. Lean: `check`, `check_sound`, `check_request_star`. A sink on the static base `S` uses this check too: in run 1
the request on a static premise is answered by the added fact itself (§4.10 item 4).

An UNCONDITIONAL SINK has no positive mark literal: it has no literal, or every literal is negated (a negated literal
counts as true, §3.5). Its sink pattern is the zero fact `(zero, [], $, {}, zeroMark)`, so it triggers on the zero fact
at the sink statement. Its sink edge is the edge of the zero fact there: the premise set `{zero}`, the conclusion the
zero fact, in the normal layer. The three conditions below confirm it if the premise set `{zero}` is supported
(condition 3): at a root, or through a chain of calls whose caller edges are the zero edges of the callers.

A CONJUNCTIVE SINK has positive mark literals on several positions (`interpreter.md` §4.2). Each literal is a sink
pattern. The conjunction store (§8.9) keeps, standing for the run, per (rule, statement, literal), each sink edge whose
check of that literal triggers. A check that gives the request raises it (run 1). When every literal has a stored
edge, each combination (one edge per literal) is a SINK EDGE SET of the vulnerability, with the set of the sink facts.
The vulnerability store keeps every sink edge set under the one key of the vulnerability (§8.10). A sink edge set is in
the demand layer if one of its edges is.

THE BACKWARD RUN has no sink check. Its sink rule is the seed (§9.2).

A triggered vulnerability is CONFIRMED only if all three conditions hold:

1. The sink edge is a normal edge.
2. Each member of the premise set of the sink edge (§4.6; the zero fact is a member like every other) is the zero fact
   or an EXACT concrete fact `(x, p, $, T)`: a request answer in run 1, an emitted fact in a restricted run.
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
         added fact itself, §4.10 item 4), or the emission `a ∩ D-c = a` in a restricted run.

      Different premises can use different caller edges at that one call, and those caller edges can be supported
      through different calls of the caller. So the support is a tree.
   3. No other premise set is supported.

   For one premise this is the chain of supported caller edges. The weaker condition "the premise is exact" is not
   enough (`Confirmed.Weak.weak_support_gap`, a proved counter-example). For two or more premises, "each premise is
   supported at some call" is not enough: two premises supplied at two different calls never meet at one execution
   (`NDConfirmed.CexSites.cex_sites`).

A conjunctive sink is a conjunction to a fresh target with a sink on it: it is confirmed if every sink edge of its set
is normal and the UNION of their premise sets is supported jointly (condition 3). A conjunction is the expected
over-approximation of a path-insensitive engine (§4.6), so a vulnerability through a normal conjunction result can be
confirmed: it is real for the path-insensitive support semantics `ND.TaintN` (`NDConfirmed.confirmed_real_N`,
`confirmed_real_N_valid`; for a program without conjunctions the rule is the one of `Confirmed.confirmed_real`,
`NDConfirmed.confirmedN_iff`).

The analyzer computes the support and the confirmation at the fixed point of the run (S6), after the last event:
condition 3 is a least fixed point over the caller edges, and it can change until the run ends.

Every other triggered vulnerability is a DEMAND vulnerability. In particular, every result of an `[any]`-target source
is in the demand layer (W6). So a vulnerability whose taint comes only from such a source is never confirmed: it stays
a demand vulnerability in every run.

`Confirmed.confirmed_real_valid` (run 1, under S7, S10 and S13) and `RMain.confirmed_real_M_valid` (every forward
restricted run, also under S14; the support `RExact.SupM`; the satisfaction `satI`) prove that a confirmed
vulnerability is real for the reference semantics (§3.5), for a sink pattern whose locations are valid (§4.8). The
forms without the validity condition (`Confirmed.confirmed_real`, `RMain.confirmed_real_M`) are for programs without
type filters (`Exact.FiltUp`). On the real program, a confirmed vulnerability is real modulo the expected
false-positive sources of §11.1. These theorems are about the closures `D` and `DR`, which have no static rule.
With the static rule of §4.10, `StaticsConfirmed.confirmed_realS` and `confirmed_realS_valid` prove it for run 1: the
support of condition 3 then also accepts the mark answer on a static premise (§4.10 item 4: the added fact itself).

### 4.10 Statics in run 1: the position request

The static base `S` holds every static field at the path `[<C>, f]`: the class accessor `<C>` (not counted by the field
limit) and the field `f`. A Go global `G` is at the path `[<G>]`. A rule can also put a concrete mark on a class
position `[<C>]` with no field, for example `(S, <C>, $, {}, T)`. The run-1 static fact is abstract: the policy fact
`(S, ., *, {}, *)` (§6.2). An operation whose premise is below an abstract static fact is the case `above` of §4.1, and
the ordinary result is `[any]` in the demand layer. In run 1 the static base uses a POSITION REQUEST instead. So no
static fact with the `[any]` tail occurs above a static position (`Statics.no_any_above`). The rule needs the
construction rules S12.

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
   conditional source whose premise is on a static field.
   * A statement micro edge AT A CALL acts on a fact of the caller edge `(i → c)`: a source of the rule statement of
     the call and a `RemoveAllMarks` kill on `S` act on the bound fact, a pass rule of an unresolved callee on the
     added fact (§5.3 steps 3 and 4). The binding `S.* → S.*` does not change the path, so the test reads the caller
     edge `(i → c)` in the caller `m`, and the position request is `(m, i, p')`.
   * The other micro edges of the statement apply as usual, so the kill stays (§4.2). The root keep edge
     `S.* →_{<C>} S.*` of a write (Go: `S.* →_{<G>} S.*`) is at `q = []`, not strictly below it: it applies and adds the
     class accessor to the exclusion (§4.2, the static rows of the table).
   * A SINK on `S` raises no position request: it uses the ordinary sink check and mark request (§4.9, §4.5), and item
     4 answers the request.
   * Below a static field (an identity edge at `[<C>, f]` or deeper, or a static fact that is not an identity edge) the
     ordinary rules apply: a deep read is the case `above` of §4.1 and gives `[any]` in the demand layer, as for an
     instance field.
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
     `(a.base, a.path, a.kind, T)`, not the chain answer;
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
record conclusion with a `*` or `[any]` tail above a static position is an identity static `*` record; Lean
`StaticsIter.RecOK`). The proof has four steps:

1. For EVERY demand, no static fact of the run with a `*` or `[any]` tail lies above a static position.
2. The reason: the emission gives the added fact, its meet at the same path, or the demand pattern below it; the
   restriction only moves a conclusion down; and a fact above a position is exact.
3. So every static read, write keep edge and sink of the run at most two accessors deep is the case at or below of
   §4.1, and none of them makes an `[any]` result. A deeper static read or sink follows the ordinary rules of an
   instance field, and it can meet an `[any]` fact above it (`StaticsIter.DeepReadIter.deep_read_above`).
4. The run raises no request.

§10.8 lists the theorems (`StaticsIter.rinv_all`, `static_step_below`, `no_request`, `no_static_rule_after_run1`,
`iteration_general_DS`). The backward run satisfies the same invariant and raises no request
(`BExact.binv_all`, `no_static_rule_backward`) if the reversed program satisfies the construction rules S12 (a) to (d);
that the interpreter's reversed program satisfies them is argued (§11.2).
That the persisted records keep the static invariant over the run sequence is argued (§11.2).

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
| CALLER (the method that contains the call) | the subscriptions: (caller edge, call statement, added fact) | binds each caller fact into the callee (micro edges); applies every published summary edge of the callee whose premise its added fact satisfies, and every record whose premise covers it (§4.3); binds back; applies the field limit |
| CALLEE (the called method) | the added facts (with the caller edges that made each added fact), the demand patterns of the method, the emission, its initial facts, its edges and summaries, its requests (run 1) | emits the initial facts for each added fact (§6); analyses them; restricts each new summary edge by its demand patterns (restricted runs, §6.4) and then PUBLISHES it to the subscribers; answers and propagates its mark requests (§4.5) and its position requests (§4.10) |

### 5.3 Call processing

The interpreter gives the order of the steps at a call (`interpreter.md` §4.5). For the caller edge `(i, layer) → c`
at the call statement:

1. RELEVANCE. If `c.base` is not a touched base of the call, the edge passes over the call (call-to-return). The
   touched bases are those of §3.5 (`interpreter.md` §3.1 lists them for each call kind), with two special cases:
   in a restricted run the interpreter leaves `S` untouched when the callee, transitively, touches no static
   (`interpreter.md` §3.3, D15); and the zero base is never touched (THE ZERO FACT below).
2. BIND. Apply the caller-side type filter of each binding into the callee (`interpreter.md` §3.1, §5.1). For each
   binding edge `e` into the callee: the bound fact `b = concat(c, e)` (a micro edge, §4.2).
3. SINKS AND SOURCES. The sinks of the call check `b` (§4.9); a triggered sink can add end facts (`interpreter.md`
   §4.1, END FACTS). The sources of the call apply to `b`: they are the rule statement of the call (`interpreter.md`
   §4.1), with statement micro edges (§4.2) and conjunctions (§4.6). The fact `b` has the premise set and the layer of
   the caller edge `(i → c)`, so in run 1 the static exception (§4.1, §4.10 item 1) tests the caller edge, and a
   position request goes to `(caller, i, p')`. A source result goes back to the caller through the binding back and
   the aliases, with NO summary rewriter (the rewriter removes the mark of a user-defined source at its own
   position), then the field limit (§4.4; `interpreter.md` §4.5 step 4). The end facts go the same way.
4. PER CALLEE POSITION. The cleaners of the call clean `b` (§4.7), chained in the rule order. A `RemoveAllMarks` rule on
   `S` is not a cleaner: at its place in the rule order it applies to `b` as a statement summary, the kill of a strong
   write (`interpreter.md` §1.4), with the static exception as in step 3. Each result `a` is an ADDED FACT (§1), with
   its own layer on the link (§8.3). Then:
   * for each resolved callee: the CALLEE PROCESSING below, for the link (`a`, caller edge);
   * at a JVM constructor call: `a` also passes over the call (`interpreter.md` §3.5);
   * for an unresolved callee or a resolution failure: the statement summary of the unresolved callee applies to `a`
     (`interpreter.md` §3.7), as statement micro edges (§4.2 step 4), with the static exception as in step 3. It is
     never restricted.
5. RETURN. For each result of step 4 (a summary result or an unresolved result), in callee coordinates: apply the
   summary rewriter (`interpreter.md` §5.2). Then bind the result back, with the binding-back type filters
   (`interpreter.md` §3.1). Then apply the aliases (`interpreter.md` §3.8: they apply to the results that its alias
   rule AC3 names). Then apply the field limit (§4.4). A constructor pass-over result skips the rewriter. This order is
   the order of `interpreter.md` §4.5 step 6.

THE ZERO FACT at a call (`interpreter.md` §4.6). The zero fact does not use steps 1 to 5; it uses this order:

1. The call does not touch the zero base, so the zero fact passes over the call.
2. The unconditional sinks and sources of the call fire on the zero fact, in the order of `interpreter.md` §4.6, and
   the stored facts of a conjunction can complete it (§4.6). The source rules form the rule statement of the call
   (`interpreter.md` §4.1): a statement summary that touches the zero base and keeps the zero fact by the micro edge
   from the zero fact to itself (S11 (d)). Their results go back as in step 3.
3. The zero fact enters every resolved callee through the binding `zero.* → zero.*` (§3.5), with no cleaner: it is an
   added fact of the callee, and the callee emits the zero fact for it (§6.2, §6.3). The results of the callee
   summaries that this added fact satisfies are summary results: they return by step 5.

The zero fact itself takes no cleaner, no pass rule and no rewriter. An unresolved call only passes the zero fact over.
In the backward run the zero fact enters the callees by the rule of §9.2.

The callee processing is a set of STANDING rules. Each event triggers its actions; the actions can make new events.
The order of the events does not change the fixed point (S6). An implementation can process them in any order.

| # | Event | Actions |
|---|---|---|
| E1 | A new added fact `a` of the callee | The callee adds `a` to its added fact store (§8.3). It EMITS the initial facts for `a` (§6): in run 1 the policy fact (§6.2), in a restricted run the emission `a ∩ D-c` for each demand pattern of the callee (§6.3). Each new initial fact is event E3. |
| E2 | A new link (added fact `a`, caller edge), also a new caller edge of an existing added fact | The callee stores the caller edge with `a` (§8.3). It checks every standing mark request and position request that overlaps `a`, and answers it or propagates it through THIS caller edge (§4.5; §4.10 items 2 and 3). The caller SUBSCRIBES `(caller edge, call statement, a)` (§8.4). It applies every published summary edge with one premise whose premise `a` satisfies (§4.3), and every record whose premise covers `a` (§8.7), then step 5. For a summary with several premises the new link is event E6. |
| E3 | A new initial fact `j` of the callee (an emission, an answer or a position answer) | The callee analyses `j` from its start fact (§6.5). (The interpreter filters the start fact by the context type, `interpreter.md` §4.3.) Each summary edge of `j` is event E4. |
| E4 | A new summary delta `j → g` of the callee: an exit fact after the exit order of `interpreter.md` §4.7 (exit sources, exit sinks, the removals of that section; no summary for a local base) | In a restricted run the callee restricts it by each demand pattern of the callee (§6.4); a zero-premise summary of the backward run is not restricted (§9.2, the balanced return). It PUBLISHES each result. For a summary with one premise: for each subscription whose added fact satisfies `j`, the caller applies the result (§4.3), then step 5. A summary with several premises goes to event E6. |
| E5 | A new mark request `(m, i, T)` in the callee `m` (run 1) | The callee stores it (§8.8). For each added fact `a` of `m` that overlaps `i`, and each caller edge of `a`: answer or propagate, as in E2 (§4.5). |
| E6 | A new link at the call statement whose added fact satisfies one premise of a callee summary with several premises (§4.6), or a new such summary | The caller combines the link with the stored links of the other premises of that summary (§4.6, §8.9). A full combination (one link per premise) applies the summary, then step 5. |
| E7 | A new position request `(m, i, p)` in the callee `m` (run 1) | The callee stores it (§8.8). For each added fact `a` of `m` that overlaps `(S, p)`, and each caller edge of `a`: answer it if `a` is at or below `p`, or climb through the caller edge if `a` is above `p` and the caller premise is on `S` (§4.10 items 2 and 3). |

The result of a summary application is in the demand layer if the added fact is in the demand layer on its link
(§8.3), if the summary edge is, or if the application itself moves it there (§4.1).

---

## 6. Runs and abstraction

### 6.1 Rules of a run and their contracts

RUN 1. The result of run 1 is the least fixed point (S6) of these rules (Lean: `D`; with the static rule `Statics.DS`;
with the conjunctions `ND.DN`):

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
with the rules `initR`, `ret`, `retRec`; for the backward run `Backward.DB`, §9.2):

1. An initial fact comes only from the emission (§6.3), for an added fact and a demand pattern of its method. The zero
   fact of a root is an initial fact too. (The backward run adds the zero rules of §9.2.)
2. A callee summary edge applies only after the restriction by a demand pattern of the callee (§6.4), and only to an
   added fact that satisfies its premise by `inside` (§4.3). (The backward run has one exception: the balanced return
   of §9.2.)
3. A record applies when its premise covers the added fact (`applicable`, §8.7 R4).
4. There is no mark request, no position request and no static rule (§4.5, §4.10). The run is concrete (§6.3), so no
   rule needs them. The implementation asserts it. The same holds for the backward run (`BExact.DB_concrete`,
   `DB_no_request`).
5. The run has its own field limit (§4.4) and its own demand (§9.2 gives the hand-off).

THE CONTRACTS. The abstraction selects the initial facts for an added fact `a` of the method `m`. It is a function of
`m`, `a` and constants of the run (the field limit, the demand). It must not depend on the order of events. `α(m, a)`
is the initial fact that the run-1 abstraction selects (§6.2). The spec rules satisfy the contracts below; the coverage
theorems need only the contracts.

```
(C1)  run 1:            applicable(α(m, a), a)
(C2)  restricted run:   for every demand pattern d of m, every CONCRETE added fact a and every location l (with its
                        mark) that D-c and a both cover, the emission emit(D-c, a) gives an initial fact j that
                        covers l, and a satisfies j
(C3)  restricted run:   the emitted fact has the mark of the added fact
(C4)  satisfaction:     if a satisfies j, the marks of a are a subset of the marks of j (so the mark gate raises no
                        request); and if a satisfies j and a has the concrete mark T, a satisfies answer(j, a, T) (§4.5)
(C5)  restriction:      for every pair (l1, l2) of a summary edge j → g (§3.2) such that D-c covers l1 and D-p covers
                        l2 as locations (marks ignored), the restriction by d gives an edge j → g' that has the pair
                        (l1, l2), in the layer of g
```

Lean: C1 `policy_applicable`; C2 `EmitContractOn`, proved for the emission of §6.3 as `RCore.emitM_contract_I`; C3
`EmitCopiesMark`, `RCore.emitM_copies`; C4 `SatContract`, `RCore.satI_contract`; C5 `RestrictContract`. The
restriction of §6.4 (`restrictU`) does NOT satisfy C5 as a function (`RCore.restrictU_fails`). C5 holds for the
auxiliary restriction `restrictS` (`RCore.restrictS_contract`), and in every run with a mark-copying emission (C3) the
two restrictions give the same run (`RExact.restrict_U_eq_S`; they agree on every conclusion without the `*` tail,
`RCore.restrictU_eq_S_nonstar`). So the coverage theorem of a restricted run holds for the restriction of §6.4.

The coverage theorem of run 1 needs only C1. The coverage theorem of a restricted run needs C2 for the added facts of
the run, C4 and C5 (for the spec restriction, through the run equality above). C3 makes every added fact of a restricted
run concrete (`RCov.concInvR_all`, `RExact.DR_concrete`), so C2 covers all of them (`RCov.emitOn_of_conc`).

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

### 6.3 Restricted run: the emission

For the added fact `a` of method `m`, for each demand pattern of `m` with the entry pattern `D-c = (b, p, t, M)`, emit
`a ∩ D-c`: the part of `a` that `D-c` covers, with the mark of `a`. The mark `M` of the entry pattern is `*` or `T`. A
concrete `M` is a demand for that mark. The entry pattern of a backward demand pattern can have the mark `*∖X` (a
run-1 summary conclusion, §9.2); it counts as `*` (Lean: `markMatchB`). Every added fact of a restricted run has a
concrete mark (C3), so the table has only concrete marks for `a`. An abstract added fact never occurs (assert).

| `D-c` mark | `a` mark | result |
|---|---|---|
| `T` | `T` | emit |
| `T` | `T' ≠ T` | nothing |
| `*`, or `*∖X` (counts as `*`) | `T` | emit, with the mark `T` of `a` |

| `a` against `p` | emitted fact |
|---|---|
| another base, or apart | nothing |
| below (`a.path = p·r`, `r ≠ []`), `t` admits `r` | `a` itself |
| below, `t` does not admit `r` | nothing |
| at `p` | `(b, p, meet(a.tail, t))`: `[any]` gives the other tail; `$` with any tail gives `$`; `*/E1` with `*/E2` gives `*/(E1 ∪ E2)` |
| above (`p = a.path·r`), the tail of `a` admits `r` | `(b, p, t)`: the demand chain and tail |
| above, the tail of `a` does not admit `r` | nothing: no common location |

Properties:

* The emitted fact is EXACTLY `a ∩ D-c` as locations (`RCore.emitM_inter`), with the mark of `a` (`emitM_mark`,
  `emitM_copies`). Nothing is lost when the marks match (`emitM_complete`). Its chain is the chain of `a` or, above `a`,
  the demand chain (`emitM_shape`): never a chain that neither the fact nor the demand has.
* C2 holds for concrete added facts (`RCore.emitM_contract_I`); it fails for a `*`-mark added fact under a `T` demand
  (`emitM_not_full_any`, for every satisfaction), and a restricted run has no such fact.
* NO REQUEST. The root starts from the zero fact, every emitted fact copies a concrete mark, a concrete-mark premise has
  only concrete-mark conclusions, and a `*`-premise record applied to a concrete fact gives a concrete result. So every
  fact of a forward restricted run has a concrete mark, no final fact has the `*` tail (`RExact.final_not_star`), and no
  request rule can fire (`RExact.DR_no_request`). The backward run is concrete and raises no request too
  (`BExact.DB_concrete`, `DB_no_request`).
  Condition: the only callee summaries with a `*` premise in a restricted run are persisted run-1 records and, in a
  backward run, their reversals (§9.1). The interpreter makes no precomputed `*`-premise summary
  (`interpreter.md` §3.7, I8).
* THE ZERO FACT. A demand that covers the zero location with the zero mark emits the zero fact itself. Every forward
  demand has the zero demand `(zero, none)` in every method (§9.2), so every forward callee that gets the zero fact
  emits it. In the backward run the zero fact needs no emission: it enters every callee as an initial fact directly
  (§9.2; Lean: rule `zin`).
* Precision. An exact added fact gives an exact concrete initial fact; its edges are in the normal layer, and a
  vulnerability under it can be confirmed (§4.9). A fact cut to `[any]` gives an `[any]` premise in the demand layer.
* Cost. There is NO SHARING: one initial fact per distinct added fact (path, tail, mark). The demand bounds which
  methods the run analyses and the chain prefix, but NOT the number of contexts below an `[any]` demand chain; the spec
  sets no cap. Nothing below a forward field-limit cut can be confirmed until a later forward run has a larger limit;
  the driver must grow the forward limit as well as the backward one (§6.6).

Program 1 (`RestrictedCases.lean`) is the worked example of the emission: the added fact of `c` is below the demand
chain, so the emission gives the fact itself; the added fact of `m` is above the demand chain, so the emission gives
the chain. Run 3 (forward) reports the vulnerability (`RCases.p1_found_M`). The demand of `c` is
`D-c = (x, .g.h, [any], T)` and the demand of `m` is `D-c = (arg, .f.k, [any], T)`, both with no `D-p`
(`RCases.dem1M`). Program 2 is the example of the restriction (§6.4).

```java
root():  x.g.h.f.k.z = source();  c(x);      // (x, .g.h.f, [any], T) after the cut
c(x):    y = x.g.h;  m(y);                    // c gets (x, .g.h.f, [any], T); then (y, .f, [any], T)
m(arg):  sink(arg.f.k.z);                     // m gets (arg, .f, [any], T) ∩ (arg, .f.k, [any], T)
                                              //       = (arg, .f.k, [any], T): the sink triggers
```

Reference form (types and tests of §3.4):

```kotlin
/** §6.3, the `at` row: the meet of two tails at the same path (Lean: meetK). */
fun meet(a: Pattern, d: Pattern): Pair<Tail, ExclusionSet> = when {
    a.fact.tail == Tail.ANY -> d.fact.tail to d.exclusion
    d.fact.tail == Tail.ANY -> a.fact.tail to a.exclusion
    a.fact.tail == Tail.EXACT || d.fact.tail == Tail.EXACT -> Tail.EXACT to ExclusionSet.Empty
    else -> Tail.STAR to a.exclusion.union(d.exclusion)
}

/** §6.3. The part of the added fact `a` that the entry pattern `d` covers, with the mark of `a`. */
fun emit(d: Pattern, a: Pattern): Pattern? {
    check(a.fact.mark is MarkSlot.Concrete)                                      // a restricted run is concrete (C3)
    if (d.fact.base != a.fact.base) return null
    if (d.fact.mark is MarkSlot.Concrete && d.fact.mark != a.fact.mark) return null  // a T demand needs the mark T
    // a Star demand mark (`*`, or `*∖X` from a run-1 summary, §9.2) admits every mark (Lean: markMatchB)
    val p = d.fact.path
    val q = a.fact.path
    return when {
        q.size > p.size && q.startsWith(p) ->                                   // below: the fact itself
            if (d.tailAdmits(q.drop(p.size))) a else null
        q == p -> {                                                              // at: the meet of the tails
            val (tail, excl) = meet(a, d)
            Pattern(a.fact.copy(tail = tail), excl)
        }
        p.startsWith(q) ->                                                       // above: the demand chain and tail
            if (a.tailAdmits(p.drop(q.size))) Pattern(d.fact.copy(mark = a.fact.mark), d.exclusion) else null
        else -> null
    }
}

/** §4.3. The added fact `a` satisfies the premise `j` of a summary edge (a record: `applicable` in every run). */
fun satisfies(j: Pattern, a: Pattern, restricted: Boolean): Boolean =
    if (!restricted) applicable(j, a)       // run 1: a inside j
    else inside(j, a)                       // restricted run: j inside a
```

### 6.4 Summary restriction (restricted runs, in the callee)

The CALLEE restricts each summary edge `j → g` by each of its demand patterns `d` (entry pattern `D-c`, exit pattern
`D-p`) BEFORE it publishes the result `j → g'` to the subscribers. Lean: `restrictU` (`restrictWith`, `restrictConcU`).
The restriction reads `D-c` and `D-p` as locations: it ignores their marks (§3.2).

* No `D-p` (the demand does not reach the method exit): no result.
* The premise stays `j` if `j` and `D-c` overlap (§3.2, marks ignored); else no result. (`j` is one path, so the
  intersection is all of `j` or nothing.)
* The conclusion `g'` follows the position of `g` against `D-p`:

| `g` against `D-p` | `g` tail | `g'` |
|---|---|---|
| at or below (`g.path = D-p.path ++ r`), the tail of `D-p` admits `r` | any | `g` |
| at or below, the tail of `D-p` does not admit `r` | any | no result |
| above (`D-p.path = g.path ++ r`) | `[any]` | `(D-p.path, [any])`, or `(D-p.path, $)` if `D-p` has the `$` tail; the mark of `g` |
| above | `*/E` | no result; it never occurs in a restricted run (no `*` final tail) |
| above | `$` | no result |
| apart, or another base | | no result |

* The restriction filters by the chain of `g`. It is not an intersection with `D-p`: at or below `D-p` it keeps the
  whole `g`, also the locations of `g` that `D-p` does not cover (example: `g = (y, ., [any])` against
  `D-p = (y, ., $)` gives `g`). It only removes whole pairs (`RCore.restrictU_sub`).
* One summary edge can have results for several demand patterns. The subscribers get every result (the union).
* `j → g'` has the layer and the mark of `j → g`.
* The restriction gives the same run as an auxiliary restriction that satisfies the restriction contract C5 (§6.1
  gives the theorems). The restriction itself does not satisfy C5 as a function (`RCore.restrictU_fails`).

The special cases of the restriction:

* A SUMMARY WITH SEVERAL PREMISES `{j1, …, jk} → g` (§4.6). The result keeps the whole premise set if one `jm`
  overlaps `D-c`; else no result. `g'` follows the table. The restriction only removes pairs from the conclusion.
  (Argued, not modelled, §11.2.)
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
itself (§6.3). The exit fact of `c` is `(ret, .f, [any], T)`, in the demand layer. It is above `D-p`, so the
restriction gives `(ret, .f.k, [any], T)` (the row `above`, `[any]`). The added fact satisfies the premise
(`inside`, §4.3). The summary application and the binding back give `(r, .f.k, [any], T)`, and the sink triggers on it.
Run 3 (forward) reports the vulnerability (`RCases.p2_found_M`). The hand-off of backward run 2 is exactly this demand
pattern of `c`, the zero demand of every method, and the pattern `((x, .h.i, [any], T), none)` of the root
(`Backward.dem2_exact`).

Reference form (types and tests of §3.4):

```kotlin
/** §6.4. Restrict the summary conclusion `sc` (the `g` of `j → g`) of the premise `sp` (the `j`) by the demand
 *  pattern `d` (in the callee). The result is `g'`. */
fun restrict(sp: Pattern, sc: Conclusion, d: DemandPattern): Conclusion? {
    val dp = d.exit ?: return null                           // the demand does not reach the exit
    if (!overlap(sp, d.entry)) return null                   // the premise: all of j or nothing
    if (sc.fact.base != dp.fact.base) return null
    val p = dp.fact.path
    val q = sc.fact.path
    return when {
        q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null     // at or below D-p
        p.startsWith(q) -> when (sc.fact.tail) {                                // above D-p
            Tail.ANY -> sc.copy(fact = sc.fact.copy(path = p,
                tail = if (dp.fact.tail == Tail.EXACT) Tail.EXACT else Tail.ANY), exclusion = ExclusionSet.Empty)
            else -> null                     // `*`: never occurs in a restricted run; `$`: no overlap
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
| `(x, p, $, m)` | `(x, p, $, {}, m)` | normal |

A premise never has the mark `*∖X` (§2.2). Lean: `startFact`, `startFact_sound`. The zero fact starts as itself, in
the normal layer. A position answer `(S, p, *, {}, *)` starts with the identity, in the normal layer (§4.10). The
interpreter adds the start rules of a method: the filter of the start fact by the context type, and the JVM entry rules
of the zero fact (`interpreter.md` §4.3).

### 6.6 The run sequence

* The analysis ALTERNATES forward and backward runs: run 1 (forward), run 2 (backward), run 3 (forward), and so on. The
  field limit INCREASES from run to run (W3 needs at least that it does not decrease). A forward run with no demand
  vulnerability (§4.9) stops the iteration: every vulnerability that it reports is confirmed. The iteration driver, its
  termination and its budget are out of scope of this spec: the fact domain grows with the field limit, so the
  iteration does not stop by itself.
* Run 1 uses the rules of run 1 (§6.1). Each later run uses the rules of a restricted run (§6.1) with the demand that
  the run before it gives (§9.2), its own field limit and the persisted records (§8.7). Lean `RCov.runSeq` numbers only
  the forward runs: `runSeq k` is run `2k + 1`, and the demand `dem k` comes from the backward run `2k + 2`.
* CONTRACT B. The backward run `n + 1` between the forward runs `n` and `n + 2` must satisfy contract B. Let forward
  run `n` report a vulnerability at the sink pattern `s` (with the concrete mark `T`) at the node `x` of the method `M`.
  Let `W` be a witness of it (§3.5) that run `n` JUSTIFIES:
  1. at each call down in `W`, run `n` has an initial fact of the callee that covers the entry location of the callee,
     with its mark;
  2. at each call in `W` that returns, run `n` has a summary edge `j → g` of the callee such that `j` is an initial fact
     that covers the entry location of the callee (with its mark), and the pair (entry location, exit location) is a
     pair of `j → g` (§3.2).

  Then the demand that backward run `n + 1` hands to forward run `n + 2` DEMANDS `W` (§1, demanded witness):
  1. at each call down in `W`, a demand pattern of the callee has a `D-c` that covers the entry location of the
     callee, with its mark;
  2. at each call in `W` that returns, ONE demand pattern of the callee has both parts: a `D-c` that covers the entry
     location of the callee, with its mark, and a `D-p` that covers the exit location (marks ignored).

  Lean: `Backward.BackwardContractD` (with `Backward.ReachRD`, `FlowRD` for the justified witness and `ReachR`,
  `FlowR` for the demanded witness).
* Every forward run justifies a witness of each real vulnerability that it reports (`Backward.reach_strongRD`,
  `reach_strongDD`). The backward run of §9.2 satisfies contract B under S11 (`Backward.B_general`). The iteration
  driver must give the backward run at least the demand and the seeds of §9.2, and give the next forward run at least
  the hand-off of §9.2.
* Then every forward run reports every real vulnerability (`Backward.iteration_general`; for any backward step that
  satisfies contract B, `Backward.iteration_sound_M_D`). So the analysis can stop at any forward run. The report is in
  §8.10.

---

## 7. Representation (the optimization)

The concept of a conclusion is a set of path facts. The representation groups path edges into TREES.

### 7.1 Initial fact

```kotlin
/** The initial fact (premise): one linear path. Its mark is * or a concrete mark (never *∖X). */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,           // interned, linked from the root node; no [any], $ or mark accessors (W4, W5)
    val tail: Tail,
    val exclusion: ExclusionSet,   // Empty in run 1; a restricted run can emit the exclusion of a `*/E` demand
    val mark: MarkSlot,
) {
    fun toPattern(): Pattern       // the list form of §3.4, for the reference forms
}

/** The premise SET of an edge: a CANONICAL set of initial facts (sorted by the intern id, no duplicates), never
 *  empty. The zero fact is an InitialAp like every other. One element: a zero-to-fact edge (the zero fact) or a
 *  fact-to-fact edge. Two or more: a conjunction result (§4.6); it is an ND edge if two or more elements are not the
 *  zero fact. The layer is not part of the premise key; every store key that needs the layer has it as a separate
 *  part. */
data class PremiseKey(val initials: List<InitialAp>)
```

`PathNode` is the current `AccessPath.AccessNode` without the `[any]`, `$` and mark accessors.

### 7.2 Conclusion trees

One tree per (statement, premise key, layer, base, exclusion, mark exclusion): the key of the method edge store
(§8.1). The exclusion and the mark exclusion belong to the tree; a `*` leaf is a flag.

```kotlin
/** The marks of the leaves of one kind at one node: the abstract mark flag plus concrete marks. */
class LeafMarks(val star: Boolean, val concrete: MarkSet)

/** Payload of one trie node at path p. */
class Payload(
    val star: Boolean,        // the leaf p.* with the tree exclusion and the tree mark *∖X (W2)
    val any: LeafMarks,       // the leaves p.[any] with these marks (the star flag is *∖X of the tree)
    val exact: LeafMarks,     // the leaves p.$ with these marks
)

class FactNode(
    val payload: Payload,
    val accessors: IntArray?,       // sorted AccessorIdx, as today
    val children: Array<FactNode>?,
) {
    @JvmField val boundedDepth: Short = ...   // max counted accessors on a path below; O(1) limit check
}

/** One edge group: the conclusions of one premise key, one layer, one exclusion and one mark exclusion. */
class EdgeTree(
    val base: AccessPathBase,
    val exclusion: ExclusionSet,   // the exclusion of the * leaves; Empty if the tree has no * leaf (W1)
    val markExclusion: MarkSet,    // X of the abstract marks of the tree (*∖X); empty for most trees
    val demand: Boolean,           // the layer; a demand-layer tree has no * leaf (W2)
    val root: FactNode,
)
```

Rules:

* T1. Merge rule 1: two trees with the same key merge by union.
* T2. Merge rule 2: two trees with the same premise key, layer, mark exclusion and EQUAL content merge into one tree with
  the intersection of the exclusions (`Tree.rule2_den`). Not valid for different contents.
* T2'. Merge rule 2 for marks: the same with the mark exclusions (`Tree.rule2_mark`).
* T3. No union of exclusions or mark exclusions across trees. No merge across layers.
* T4. `add` returns the new part only (the delta), as `mergeAddDelta` does today. Exception: when merge rule 2 shrinks an
  exclusion or a mark exclusion of a stored tree, the delta is the WHOLE merged tree with the new exclusion.
* T5. Inside one demand-layer tree, an `[any]` leaf with the mark `m` at `p` may absorb every leaf with the mark `m`
  below `p`. The denotation does not change. A normal tree has no `[any]` leaf (W6).
* T6. Share one empty payload; intern payloads, mark sets and exclusion sets.

### 7.3 Delta-concat on a tree

The computation of §4.1 on all paths of one tree at once. `Ec` is the tree exclusion. The results are grouped by their
new (layer, exclusion, mark exclusion):

1. Walk `from.path` from the root node of the tree. On each proper prefix node, read its payload as the case `above`
   (`r` is the rest of `from.path` after the node):
   * a `*` leaf gives a result only if `Ec` admits `r` (Lean: `Tree.cS`);
   * an `[any]` leaf always gives a result;
   * a `$` leaf gives nothing (no overlap).

   Each result is `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer. Apply the mark gate to each leaf
   mark (step 4). Lean: `Tree.contribB`. STATIC EXCEPTION (run 1, a statement micro edge with its premise on `S`; the
   rule is §4.10 item 1, the test §4.1): a `*` leaf of an identity static `*` edge at the root path or at a class gives
   no result; it raises the position request for `from.path` cut to at most two accessors.
2. At the node of `from.path` take the subtree `U`. Filter its root by the premise tail and the edge exclusion.
3. Transform `U` by the target tail:
   * a `*` target: the child subtrees (`r ≠ []`) keep the tree exclusion and are re-rooted under `to.path`; the root
     `*` leaf (`r = []`) gets the exclusion `Ec ∪ E`, so it goes to another tree;
   * an `[any]` target: fold `U` into one `[any]` payload with the Empty exclusion, in the demand layer (W6);
   * a `$` target: fold `U` into one `$` payload with the Empty exclusion. It is in the demand layer if `U` has a `*`
     leaf and its exclusion is not Empty (`lostCorr`: `Ec ∪ E` for the root leaf of `U`, `Ec` for a leaf below it).
4. Apply the mark gate per payload mark, then the target mark (§4.1 steps 4, 5; a `*∖X` target adds `X` to the mark
   exclusion and stops the concrete marks in `X`). A payload mark that the gate sends to a request gives no result for
   that mark; it raises the request `(m, i, T)` (run 1, §4.5).
5. Layer and normal form (§4.1 step 6). A result is in the demand layer if the tree is in the demand layer, if the
   applied edge is a demand-layer summary edge (§4.3), or if a step above says so. Then a result with the `[any]` tail
   is in the demand layer (W6), and a result with the `*` tail and a concrete mark, or in the demand layer, becomes
   `[any]` with the Empty exclusion, in the demand layer (W2).
6. Where §4.4 puts a cut point (for example the statement transfer), apply the field limit with `boundedDepth`; cut
   paths go to the demand-layer tree. The cut is not part of `concat` (§4.1).
7. Route each result by its own layer bit.

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `U` only. The concept form visits every path
fact (`Tree.lean`: `applyTreeE_mem`, `applyTreeE_den`, `walkSteps_le`).

### 7.4 The restriction on a tree

The restriction of §6.4 applies to all conclusions of one summary tree at once (`RStore.restrictTree`):

1. Walk `D-p.path` from the root node of the tree. On each proper prefix node: drop the `*` flag (§6.4; a restricted run
   has no `*` leaf); move the `[any]` marks to `D-p.path` (as `$` for a `$` exit pattern); drop the `$` marks and every
   child off the chain.
2. At the node of `D-p.path`, keep the payload, add the moved marks, and keep each child whose accessor the tail of
   `D-p` admits (all children for `[any]`, none for `$`).

The result is one well-formed tree (`RStore.restrictTreeE_inv`); the tree form equals the per-path restriction
(`restrictTreeE_mem_U`); cost `|D-p.path| + 1 + width` new cells, kept subtrees shared (`restrictTree_cost`).

### 7.5 Interning

Tries are hash-consed bottom-up as today; an identity cache memoises the walk of §7.3. `boundedDepth` is part of the
node, not of the hash.

### 7.6 Relation to the current code

The prescan (§1) still runs the current core. So the new AP lives beside the current types.

| Part | Decision |
|---|---|
| `AccessPath.AccessNode`, accessor interning, `AccessorIdx` | Reuse. |
| `AccessTree` merge, `mergeAddDelta`, interners, identity caches | Reuse the algorithms for `FactNode`. |
| `AccessBasedStorage` trie | Reuse for the path indexes of §8. |
| `EdgeStorage`, `AccessPathBaseStorage`, exact-key subscription maps | Reuse with the new fact types. |
| `StatementSummaryBuilder`, `buildReversed` | Adapt (`interpreter.md`). |
| `InitialFactAp`, `FinalFactAp`, `ApManager` | New types `InitialAp`, `EdgeTree`. They do not implement the old interfaces. |
| `Edge` (`ZeroToFact` requires Universe) | New edge classes with the layer: `Zero → (layer, statement, fact)`, `(premise key, layer) → (statement, fact)`. |
| `NDFactToFact` | An edge whose premise key has two or more premises that are not the zero fact (§4.6). |
| `DeepAccessorExclusion` | Replaced by the mark exclusion `*∖X` of the edge (§4.7). The old exclusion is tied to an abstraction point at a depth, so it is lost when the field limit cuts the path; the mark exclusion is not tied to a position. |
| `FactReader` (mark as accessor suffix) | New reader over `(path, tail, mark)`: `check` (§4.9). |
| `FactTypeChecker` | The type filter primitive (§4.8). |
| `EdgeNonUniverseExclusionMergingStorage` (union merge) | Replace by merge rules 1 and 2. |
| `TaintSinkTracker` (rule assumptions), vulnerability records | The standing conjunction store (§8.9); the vulnerability record of §8.10. |
| `TreeInitialFactAbstraction` | Replace by §6.2 (run 1) and §6.3 (restricted runs). |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used: the field limit is the only depth bound (§4.4). |

---

## 8. Storages

Every store has a CONCEPT (a list of entries with a filter) and an INDEX. `Store.lean` and `RestrictedStore.lean` prove
that each index returns every entry that the filter returns, and give the cost of the lookup. The OWNER of each store
is the method that §5.2 names. Lifetimes:

* RUN: one run (one direction, one field limit).
* HAND-OFF: from the end of one run until the next run has read it. This is what one run passes to the next: the
  summary edges (§8.5) and the reported vulnerabilities (§8.10). The next run reads them as its demand or as its seeds
  (§9.2 defines the hand-off; §8.6 stores the demand).
* PERSISTENT: all runs of one analysis.

The method key of a method is the same in every run (§1), so a key that contains it stays valid across runs.

PATH TRIES. Several indexes are path tries keyed by `base :: path` (the base, then the accessors of the path). For the
key `k`, `lookupPrefixes(k)` returns the entries whose key is a prefix of `k` (the entries at or above `k`, also at
`k`), and `lookupExtensions(k)` returns the entries whose key has `k` as a prefix (the entries at or below `k`, also at
`k`). An OVERLAP query is `lookupPrefixes(k) ++ lookupExtensions(k)`, with the entries at `k` once. Each lookup gives
candidates; the store then applies the exact test that the section names (`overlap`, `applicable`, `inside`, §3.4).

### 8.1 Method edge store (RUN, per method)

* Key: `(statement, premise key, layer, base, exclusion, mark exclusion)`. Value: an `EdgeTree`.
* `add(...)` merges by rule 1, 2 or 2' (T1, T2, T2') and returns the delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer: the store drops a conclusion if a stored conclusion of the same premise key and layer
  subsumes it (`Subsume.subsumesB`): the same base; the same mark, or the stored mark `*∖Xs` and the dropped mark
  `*∖Xn` with `Xs ⊆ Xn`; `[any]` at `p` subsumes every fact at or below `p`; `*/Es` subsumes `*/En` at the same path if
  `Es ⊆ En`. `subsumes_sound` proves
  that every pair of the dropped fact is a pair of the stored fact.
* A demand-layer conclusion never subsumes a normal one (`Subsume.recordSubsumesLB_layer` for records).
* Unchanged propagation (`Sequent.Unchanged`) may skip the store, as today.
* Queries for the trace resolution: `edgesAt(stmt, premise?)`, `edgesAt(stmt, pattern)`. The store of the
  last forward run stays until the trace resolution ends.

### 8.2 Initial fact store (RUN, per method; callee)

* `initials: Set<InitialAp>`: the initial facts of the method in this run (the zero fact, the emissions and the
  answers).
* `supported: Set<PremiseKey>`: the premise SETS of the method that are supported jointly (§4.9 condition 3). Support
  is a property of a premise set, not of one initial fact: two premises that are each supported at a different call
  do not make their set supported (`NDConfirmed.CexSites`). The analyzer computes the set at the fixed point of the
  run, after the last event (§4.9).

### 8.3 Added fact store (RUN, per method; callee)

* A path trie keyed by `base :: path`. Each added fact keeps the set of its caller edges
  `(caller method, caller premise key, layer of the caller edge, call statement)`. One (added fact, caller edge) pair
  is a LINK.
* Each link also keeps the LAYER OF THE ADDED FACT on that link. It can differ from the layer of the caller edge: a
  cleaner `part` row can move the added fact to the demand layer (§4.7). Condition 3.2 of the confirmation (§4.9) reads
  it: only a link with a normal added fact supports a premise.
* A new link is event E2 of §5.3, also when the added fact exists already. The store gives the request store (§8.8)
  every new link.
* The standing request match (§4.5, §4.10) reads the store with OVERLAP queries (§8): the key is `base :: path` of
  the request premise (mark request) or `S :: p` of the requested position (position request).

### 8.4 Subscription store (RUN; caller)

* Key: the callee. Value: the subscriptions `(caller edge, call statement, added fact a)`.
* On a published summary edge of an initial fact `j`: find the subscribed `a` that satisfy `j` (§4.3), and apply. The
  index is a path trie keyed by `base :: a.path`. In run 1 (`applicable`: `a` at or below `j`) the query is
  `lookupExtensions(j.path)`. In a restricted run (`satI`: `j` inside `a`) the query is `lookupPrefixes(j.path)`.
  Then the store applies the exact test of §4.3.
* On a new subscription: apply every published summary edge of every initial fact that `a` satisfies, and every record
  whose premise covers `a` (§8.7).
* Only this store answers the "satisfies" query.

### 8.5 Run summary store (HAND-OFF, per method; callee)

* Key: `(premise key, layer)`. Value: the exit `EdgeTree`s. A summary edge is an exit fact after the exit order of
  `interpreter.md` §4.7 (event E4 of §5.3). Only the normal exit makes a summary edge (`interpreter.md` §3.4).
* In a restricted run the callee restricts each new summary edge by every demand pattern of the method (§6.4). It
  PUBLISHES the results to the subscription store.
* At the end of the run, the store adds the summary edges that §8.7 R1 admits to the persistent record store.
* The summary edges are the input of the next run in the other direction (§8.6, §9.2).

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
  `restrict_lookup_equiv_U`).
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
    val premise: InitialAp,            // the one member of the premise set; the zero fact only for FORWARD (R1)
    val conclusion: EdgeTree,          // normal layer; may carry a mark exclusion
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

* R1. The store adds only a normal summary edge whose premise set has ONE member:
  * of a forward run: every such edge, also a zero-premise edge (the premise set `{zero}`);
  * of a backward run: only an edge whose premise is NOT the zero fact. A zero-premise backward edge can come from a
    seed (§9.2), which is not a converse flow of the program (Lean: `Backward.seed_den`), so it is never persisted and
    never reversed.

  An edge whose premise set has two or more members (§4.6) is never added.
* R2. `byEntry` is a path trie keyed by `base :: premise path`. The lookup is `lookupPrefixes(base :: q)` for the
  added fact at `q`, and then the `applicable` filter, in every run (`forward_equiv_prefixes`,
  `applicable_mem_candidatesB`, `extension_half_redundant`). `byExit` is a path trie keyed by `base :: leaf path` for
  EACH leaf path of the conclusion tree. Its lookup is `lookupPrefixes(base :: q)` for the fact at `q`: a leaf whose
  reversal covers the fact is at or above it.
* R3. A reader in the other direction reverses the record by §9.1 and then applies it as R4 says: when the new premise
  covers the fact (`applicable`). Only a mark-reversible record has a reversal (§1); a record that is not
  mark-reversible is not read in the other direction. Every record whose premise has the Empty exclusion and that is
  mark-reversible reverses exactly (`Reverse.rev_exact_of_empty_premise`), so every mark-reversible forward record
  reverses exactly (§9.1). A reversed backward record has no type filter (the backward run does not type-filter): an
  expected false-positive source (§11.1). A normal backward summary with a non-zero premise reverses into an exact
  forward record (`BExact.rev_record_exact`, `revRecs_exact`, `revRecs_exactM`; under S11 (c): without it a backward
  summary is not a reversed flow, `BExact.CexZeroBack.cex_rec`).
* R4. A record applies to an added fact when its premise covers the fact (`applicable`, §4.3), in every run after the
  run that made it, IN THE SAME DIRECTION (run 1 is the first run, so it reads no record). A record is exact (S14), so
  it adds no false pair. For the records of a forward run this is proved run by run: a normal edge of run 1 or of a
  forward restricted run is exact when the records that the run reads are exact (`RExact.recs_of_D_valid`,
  `recs_of_DR_valid`; for programs without type filters `recs_of_D`, `recs_of_DR`; the union of two record sets,
  `recs_union`). Over the whole run sequence the persisted forward records stay exact (`BExact.recsSeq_exact`,
  `recsSeq_exactV`, `accRecs_exact`, `accRecs_exactM`), so every normal edge and every confirmed vulnerability of every
  run is real with no hypothesis on the records (`BExact.seq_edge_exact`, `seq_confirmed_real`).
  A backward normal edge with a non-zero premise is exact for the reversed program (`BExact.edge_exactB`,
  `edge_exactB_valid`, `edge_exactB_rev`; under S11 (c)). A zero-premise backward edge is never persisted (R1).
  A conjunction result whose premise set has one member can be a record; its exactness is `NDExact.nd_edge_exact`
  (the valid form `nd_edge_exact_valid`). The exactness holds for the reference semantics (§3.5), modulo the expected
  false-positive sources (§11.1). Lean: rule `retRec` (§11.2), `RCases.p3_reuse`, `RMain.p3_reuse_exact`.
* R5. Strict demand: after run 1 the abstraction reads only the demand (§6.3). It emits the demanded facts and
  checks nothing else; a record never causes an emission and never replaces one. The records only add edges (R4).

### 8.8 Request store (RUN 1 only, per method; callee)

* Entries: `(method, initial fact, mark)` for a mark request (§4.5) and `(method, initial fact, position)` for a
  position request (§4.10), plus the answers already emitted. A request stands for the whole run.
* Index: per method, a path trie (§8). A mark request is keyed by `base :: path` of its premise `i`. A position
  request is keyed by `S :: p`, the requested position, because the match reads `(S, p)` and not the premise.
* On every new link (added fact, caller edge) of the method (§8.3), find ALL standing requests that overlap the added
  fact (`standing_complete`): for a mark request the premise `i`, for a position request the position `(S, p)`. Answer
  each one, or propagate it through THIS caller edge (§4.5; §4.10 items 2 and 3; §5.3 event E2).
* On a new request, read every existing link of the added fact store whose added fact overlaps it (§5.3 events E5 and
  E7).

### 8.9 Conjunction store (RUN, per method)

* Entries: `(rule, statement, literal) → set of (fact, premise key, layer)`: the facts that overlap a literal of a
  conjunctive micro edge and pass its mark gate (§4.6), standing for the run.
* The same entries for a conjunctive sink: the sink edges that trigger a literal (§4.9).
* On a new fact for a literal: combine it with the stored facts of the other literals (one per literal, every
  combination); the results have the union of the premise keys. For a conjunctive sink, each combination is a sink
  edge set of the vulnerability (§4.9, §8.10).
* The same for a callee summary with several premises at a call statement: `(callee summary, premise index) → links`
  (the added fact with its caller edge; §4.6, event E6).

### 8.10 Vulnerability store and the report (PERSISTENT)

A reported vulnerability (Kotlin: `VulnerabilityRecord`) has these fields:

| Field | Content |
|---|---|
| rule | The sink rule. |
| method, statement | The method key and the sink statement. |
| pattern | The sink pattern `s` (§4.9); for an unconditional sink, the zero fact (§4.9); for a conjunctive sink, the literal patterns. |
| sink edges | Every sink edge that triggers the sink at the statement: its premise key, its layer, its sink fact and whether it is confirmed. For a conjunctive sink, every sink edge set (one edge per literal, §4.9), with the set of the sink facts. The trace resolution starts from them. |
| state | CONFIRMED if at least one of its sink edges (or sets) is confirmed (§4.9); else DEMAND. |
| end facts | The end facts of the sink rule, if the rule has end-fact actions (`interpreter.md` §4.1, END FACTS). The trace resolution reads them. |
| run | The run that reported it. |

* Key: `(rule, method key, statement)`. The same key in two runs is the same vulnerability. One record holds every
  sink edge with this key.
* A CONFIRMED vulnerability persists. It is real for the reference semantics (§3.5), modulo the expected
  false-positive sources of §11.1.
* Every FORWARD run reports every real vulnerability (§6.6). A demand vulnerability of forward run `n` that forward run
  `n + 2` does not report (no vulnerability with the same key) is REFUTED: under B it is not real.
* The REPORT of the analysis is every vulnerability that a run confirmed, and every demand vulnerability of the last
  forward run. A vulnerability has the state CONFIRMED in the report if some run confirmed it.
* The vulnerabilities of a forward run are also its HAND-OFF: the next backward run reads them as its seeds (§9.2). A
  backward run reports no vulnerability (§9.2, the backward sink role).

---

## 9. Reversal and the backward direction

### 9.1 Reversal of a record or a micro edge

The reversal `rev(i, f)` (Lean: `revEdge`, `revKinds`) reads an edge `i → f` from the other side. It reverses a record
for a reader in the other direction (§8.7 R3), and every micro edge of the reversed program (§9.2). The new premise is
the old conclusion; the exclusion goes to the NEW CONCLUSION, so the new premise has the Empty exclusion. A micro edge
can have every row of the table except the row `$ → */E`, which S8 forbids. The last column says whether a record can
have the row. Only two rows occur for a record, because:

* an `[any]` premise starts in the demand layer (§6.5), so it has no record;
* an `[any]` conclusion is in the demand layer (W6), so it is no record;
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
| `[any]` | `$` | `$` | `[any]` | no |
| `$` | `[any]` | `[any]` | `$` | no |
| `*` | `[any]` | `[any]` | `[any]` | no |
| `[any]` | `[any]` | `[any]` | `[any]` | no |

The new premise mark is `i.mark` if `f.mark` is abstract (`*` or `*∖X`), else `f.mark`. The new conclusion mark is
`f.mark` (`*` or `*∖X`) if it is abstract, else `i.mark`.

* The reversal needs a MARK-REVERSIBLE edge: `f.mark` is abstract, or `i.mark` is concrete (Lean: `Reverse.MarkRev`).
  A mark-producing edge under a `*`-mark premise has no reversal (`no_rev_of_star_conc`). S11 (b) asks that every
  statement micro edge is mark-reversible; a call binding has the marks `*` to `*` (S10, S11 (a)), so it is
  mark-reversible too.
* The reversal of an edge is EXACT (the reversed pairs are exactly the converse pairs) if the edge is mark-reversible
  and has an EXACT SHAPE: every row of the table except `*/E → $` and `*/E → [any]` with a premise exclusion
  `E ≠ {}` (Lean: `Reverse.ExactShape`). With the Empty premise exclusion every row has an exact shape
  (`rev_exact_of_empty_premise`). A normal edge of a forward restricted run has a premise with the `$` tail
  (`RExact.complete_premise_exact`), and a record of run 1 has a premise with the Empty exclusion (§2.2). So every
  mark-reversible forward record reverses exactly. A normal backward summary with a non-zero premise reverses into an
  exact forward record (`BExact.summary_rev_flow`, `rev_record_exact`).

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
  `z` reaches every literal (an OR). This over-approximates the demand. It is argued, not modelled (§11.2).
* A cleaner is its own reversal (Lean: `Reverse.revInstr`). `interpreter.md` §4.9 places it on the requirement at the
  callee start. A `RemoveAllMarks` kill on `S` (`interpreter.md` §1.4) is a statement, not a cleaner: the reversal of
  each keep edge `S.q.* →_{E} S.q.*` is the same keep edge, and the kill acts on the requirement at the place of the
  reversed cleaners.
* THE REVERSED CALL (Lean: `Reverse.Call.rev`). The touched bases are those of the forward call and the alias bases
  of its call results (`interpreter.md` §3.8 AC2). The backward binding into the callee is the reversal of the forward
  binding back (`r.* → ret.*`, `ai.* → argi.*`, `S.* → S.*`) and of each call alias edge (`b.q.* → P.*`). An alias base
  also gets the identity edge `b.* → b.*`, as a gen-only target of a statement does. The backward binding back is the
  reversal of the forward binding into the callee (`argi.* → ai.*`, `S.* → S.*`). The alias part is argued, not
  modelled (§11.2). `interpreter.md` §4.9 gives the order of the reversed call.
* NO TYPE FILTER. The backward run applies no type filter (§11.2 gives the difference to the model).
* THE ZERO FACT. The backward run starts at each ROOT with the zero fact as an initial fact, at the forward exit of the
  root. The zero fact passes over every call (Lean: rule `zpass`). It also ENTERS every callee directly: it is an
  initial fact of the callee at the forward exit of the callee, with no emission and no demand pattern (Lean: rule
  `zin`). This entry is not the reversal of a forward binding: with the plain reversal the zero fact only goes up, and
  a requirement inside a callee never reaches the callers (`Backward.lost_plain`, `Backward.B_fails_plain`). S11 (d)
  and (e) keep the zero fact alive on every path to a seed. With S11 (c), a requirement that enters a callee through a
  backward binding is never the zero fact, so its backward summary goes to the hand-off as case 3 below.
* SEEDS (Lean: rule `seed`). The sink rule of each vulnerability that the previous forward run reported fires where the
  zero fact reaches the sink statement, as a zero-to-fact edge `Zero → (sink statement, requirement)`. The requirement
  is the sink pattern, cut by the field limit of the backward run (§4.4). A conjunctive sink seeds one requirement per
  literal pattern. An unconditional sink seeds nothing: its pattern is the zero fact (§4.9), and the zero rules keep
  the zero fact already. `interpreter.md` §4.9 places the seed of a sink call after the reversed cleaners of that
  call.
* THE BALANCED RETURN (Lean: rule `zret`). A requirement goes back to the forward entry of its method. A zero-premise
  backward edge there is a zero-premise backward summary of the callee. Every caller applies it to its own zero fact at
  the call site where that zero fact entered the callee, through the backward binding back, then the field limit. The
  callee does not restrict this summary (§6.4 does not apply), and the caller makes no satisfaction test. So every
  return of a seed is BALANCED.
* RECORDS. A forward record applies in the backward run through its reversal (§8.7 R3). A backward summary edge with
  a premise that is not the zero fact can become a record (§8.7 R1). A zero-premise backward edge never becomes a
  record: a seed is not a converse flow of the program.
* THE BACKWARD SINK ROLE. The backward run has no sink check (Lean: `Backward.DB` is used with no sinks; its only sink
  rule is `seed`). A forward source is not a backward sink: its reversed micro edge carries a requirement to the zero
  fact (THE ZERO DEMAND below). So a backward run reports no vulnerability. Its hand-off is the demand below.
* THE ZERO DEMAND. A requirement that reaches a source continues to the zero fact through the reversed source edge.
  The forward demand of every method contains `(zero, none)` (the hand-off below), so the next forward run emits the
  zero fact in every method that it reaches. The work from the roots to the sources (forward) and from the sinks to the
  roots (backward) repeats in every run. The work decreases because a backward run seeds only the sinks that the
  previous forward run reported, and a later run never adds a sink. All other work follows the demand.
* Every backward run is a restricted run with its own field limit (§6.1). It is concrete and raises no request
  (`BExact.DB_concrete`, `DB_no_request`; the seeds have concrete marks).
* THE DEMAND OF THE BACKWARD RUN (hand-off, forward run `n` to backward run `n + 1`; Lean: `Backward.revSummaryDemand`,
  which reads the exit edges of the run through `Restricted.summaryDemand`). The hand-off reads the summary edges of
  forward run `n` BEFORE the restriction of §6.4: the exit edges of each initial fact, in every layer. For every such
  summary edge `j → g`, the backward demand pattern `(D-c = g, D-p = j)`. For a summary with several premises
  `{j1, …, jk} → g` (§4.6), one pattern `(D-c = g, D-p = jm)` per member `jm` (argued, §11.2). This swaps the two
  patterns of the summary; it is not the reversal of §9.1. A forward summary of run 1 can have the conclusion mark
  `*∖X`; as an entry pattern it counts as `*` (§6.3). The seeds are the vulnerabilities that forward run `n` reported
  (§8.10).
* THE DEMAND OF THE NEXT FORWARD RUN (hand-off, backward run `n + 1` to forward run `n + 2`; Lean: `Backward.demOf`).
  This is the only definition of the forward demand. For every method `M`:
  1. the zero demand `(D-c = zero, D-p = none)`;
  2. for every zero-premise backward edge at the forward entry of `M`, with the conclusion `gb`: `(D-c = gb, none)`;
  3. for every backward summary `jb → gb` of `M` whose premise `jb` is NOT the zero fact, in every layer:
     `(D-c = gb, D-p = jb)`.

The backward run satisfies contract B (§6.6) under S11 (`Backward.B_general`): for every forward run, if the demand of
the backward run contains the patterns above and its seeds contain the sinks that the forward run reported.
`Backward.iteration_general` joins the runs: every forward run reports every real vulnerability. For the worked
programs 1 and 2 (§6.3, §6.4) the hand-off of the backward run is exactly three parts: the demand patterns of the
callees that §6.3 and §6.4 give (`RCases.dem1M`, `dem2M`), the zero demand of every method (`Backward.zeroDem`), and
the pattern `(D-c, none)` of the root where the requirement reaches the source (`Backward.dem1_exact`, `dem2_exact`).
Forward run 3 reports the vulnerability (`Backward.p1_found`, `p2_found`).

`Reverse.flow_rev_iff_calls` proves that the flow of the reversed program is the converse flow, with calls, cleaners and
filters, if every micro edge and every call binding has an exact shape and is mark-reversible (`RevStmts`, `RevCalls`).

---

## 10. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

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

### 10.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`

| Theorem | Statement |
|---|---|
| `Exact.edge_exact_valid`, `closed_exact_valid` | Under S7 (`MarkWF`) and S13 (a validity predicate that every filter accepts, `FiltValid`, and that goes back along every statement micro edge and both call bindings, `BackOK`): every pair of a normal-layer edge whose end location is valid is a concrete flow. |
| `Exact.edge_exact`, `complete_exact`, `closed_exact` | The same for filters that keep every extension of an accepted path (`FiltUp`; with prefix-closure this makes a filter constant, so this form is for programs without type filters). |
| `Exact.CexFilt`, `CexMark` | The two hypotheses are necessary: a filter lets a fact pass whose lower locations do not exist; a `*`-premise edge with a concrete target forgets a cleaned mark. |
| `Exact.cleanRes_exact` | A normal-layer result of the cleaner denotes only pairs of the input whose end location the cleaner keeps. |
| `Closed.closed_records_exact`, `closed_records_exact_valid` | A property of records: no request on the initial fact and only normal exit edges ⇒ the records are exactly the concrete flow from its location set. |
| `Invariant.final_star_legal`, `final_star_abstract` | W2: a `*` conclusion has the mark `*` or `*∖X` and is in the normal layer. |
| `Invariant.no_univ_star` (+ `no_univ_needs_*`) | S8 ⇒ no `*/Universe` edge fact; each hypothesis is necessary. |
| `Invariant.demand_of_any_ok` | W6 is a layer refinement. |
| `W6.D_le_D6`, `D6_le_D`, `D6_w6`, `D6_normal` | W6 FOR THE WHOLE RUN 1 (`D`): under `W6.SummaryStar` the run with W6 has the same facts, with the same or a raised layer; W6 holds in it; its normal edges are normal edges of the plain run. `SummaryStar` holds for the run-1 policy with no other hypothesis (`W6.summaryStar_policy`), and for every abstraction under the hypotheses of `Invariant.no_univ_star` (`W6.summaryStar_of_noUniv`). |
| `W6.DR_le_DR6`, `DR6_le_DR`, `DR6_w6`, `DR6_normal` | The same for a forward restricted run (`DR`), under `W6.RestrictLE` (the restriction copies the layer; for the restriction of §6.4: `W6.restrictU_LE`) and `W6.ExactInitConc` (every `$` initial fact has a concrete mark; the mark-copying emission gives it: `W6.DR_eic`). No S8 hypothesis. W6 is proved for `D` and `DR` only, not for `Statics.DS`, `ND.DN` or `Backward.DB`. |
| `W6.vuln_found6`, `edge_exact6`, `edge_exact_valid6`, `edge_exactR6`, `edge_exactR_valid6`, `confirmed_real6`, `confirmed_real_valid6`, `confirmed_real_M6`, `confirmed_real_M6_valid`, `iteration_sound_M6`, `iteration_general6` | With W6 in every forward run: soundness, exactness and confirmation (also the valid forms, under S13; in a restricted run under S14) and the iteration (`iteration_general6` has no S8 hypothesis). |
| `W6.Cex.cex_w6_changes_fact` | Without `SummaryStar`, W6 changes a fact, not only its layer. The program uses an abstraction outside the spec: it emits a `$` initial fact with an abstract mark, so `Invariant.PremConc` and `W6.ExactInitConc` are false for it. |
| `star_final_keeps_initial_excl`, `star_initial_complete`, the demand-monotone lemmas | A final `*/Ec` under an initial `*/Ei` keeps `Ei ⊆ Ec`; under `*/Ei` a normal-layer final fact has the `*` tail or `Ei = {}`; the demand layer never goes back. |
| `Confirmed.confirmed_real_valid`, `confirmed_real` | A CONFIRMED vulnerability (§4.9) is a real concrete vulnerability for the reference semantics (§3.5) (valid form; `MarkWF ∧ FiltUp` form; §11.1 lists the expected false-positive sources). `CexConfFilt`, `CexConfMark`: both hypotheses are necessary. |
| `Confirmed.Weak.weak_support_gap`, `Confirmed.Rev2.rev2_not_confirmed` | The weaker support condition admits a false positive; the counter-example program `Confirmed.Rev2` is not confirmed. |

### 10.4 Concept against optimization — `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean`

| Theorem | Statement |
|---|---|
| `Tree.insert_mem`, `fromList_mem` | The `EdgeTree` (one premise, layer, exclusion and mark exclusion; `*` leaves are flags) holds exactly its path edges. |
| `Tree.rule1_mem`, `rule1_den`, `rule2_den`, `rule2_mark` | Merge rule 1 is exact; merge rule 2 (exclusions, and mark exclusions) is exact for EQUAL trees; counter-examples for different trees and for a union. |
| `Tree.applyTreeE_mem`, `applyTreeE_den`, `applyTreeE_grouped_key`, `applyTreeE_mx`, `applyTreeE_inv`, `applyTreeE_star_normal` | For a `*`-to-`*` micro edge with the mark `*` on both sides (not the mark gate or the cut of §7.3): the tree form of delta-concat equals the per-path form, fact and layer; output trees have distinct keys and keep the mark exclusion. |
| `Tree.fromList_size`, `fan_list`, `fan_tree`, `prepend_shares`, `walkSteps_le`, `applyListC_spec` | Cost of the tree representation. |
| `Store.*` | The record, request and demand indexes return every entry that the concept filter returns; lookup cost. |
| `Subsume.subsumes_sound`, `markSubsB_sound` | The conclusion subsumption test is sound, with mark exclusions (`*∖Xs` subsumes `*∖Xn` if `Xs ⊆ Xn`). |
| `Subsume.merge_inter`, `merge_mark_inter`, `union_loses_pairs`, `union_marks_loses_pairs` | Merge rule 2 is exact for exclusions and for mark exclusions; a union loses a real pair. |
| `Subsume.record_subsumes`, `recordSubsumesB_sound`, `recordSubsumesLB_*` | Record subsumption. |
| `RStore.near_equiv`, `near_sound`, `emit_complete_M`, `emit_lookup_equiv_M`, `emitM_exact_prefix`, `restrict_complete_U`, `restrict_lookup_equiv_U`, `near_query_cost`, `deep_chain_cost` | The demand store: index = filter; complete for the emission and the restriction; cost walk + length of the returned chains (not walk + count). |
| `RStore.restrictTreeE_mem_U`, `restrictTreeE_inv`, `restrictTreeE_mx`, `restrictTree_cost` | The restriction of a whole tree equals the per-path restriction; one well-formed tree; it keeps the mark exclusion; cost walk + width, shared subtrees. |

### 10.5 Reversal — `Reverse.lean`

| Theorem | Statement |
|---|---|
| `revEdge_sound`, `revEdge_exact`, `rev_exact_of_empty_premise`, `rev_starEx_exact` | §9.1: sound for every mark-reversible record; exact with the Empty premise exclusion, also for a `*∖X` record. |
| `policy_premEmpty`, `answerInit_premEmpty`, `answerInit_markRev`, `revEdge_premise_mark` | Run-1 initial facts have the Empty premise exclusion; a reversed premise never has a mark exclusion. |
| `star_exact_no_exact_rev`, `no_rev_of_star_conc`, `no_rev_of_two_marks` | The limits of the reversal. |
| `Stmt.rev_step_iff`, `flow_rev_iff_calls`, `rev_WF`, `backward_of_forward_calls` | The reversed program has the converse flow, with calls, cleaners and filters; it is well-formed; the forward closure `D` on the reversed program (`Program.rev`) is covered by the forward theorem. This is not a theorem about the backward run `Backward.DB`, which adds the zero rules and the seeds. |
| `backward_reuse`, `backward_reuse_needs_cover`, `backward_reuse_precise` | Reversed records cover the converse flows; the cover condition is necessary. |

### 10.6 ND edges — `ND.lean`, `NDExact.lean`

| Theorem | Statement |
|---|---|
| `ND.nd_coverage` (+ `nd_coverage_single`, `nd_coverage_flow`, `nd_coverage_conc`) | THE ND COVERAGE THEOREM. For a support derivation `TaintN M n l L0` (the location `l` is tainted at `n` when the entry locations `L0` are) and initial facts lined up with `L0`, each covering its location: the edge keyed by exactly these initial facts covers `l` at `n` (with `den` for one premise), OR the closure has a request on one of them with the mark of its location. |
| `ND.nd_vuln`, `nd_vuln_root`, `nd_vuln_reach`, `nd_vuln_found` | A tree-shaped vulnerability witness gives a vulnerability. |
| `ND.ndConclusion_uncorrelated` | W7: an edge with two or more premises has no `*` tail and has a concrete mark. |
| `ND.answer_loop` | A request at one support position is answered or climbs; the loop over positions ends. |
| `ND.flow_taintN`, `D_sub_DN` | Every ordinary flow is a support derivation with one location; every object of `D` is in the ND closure. |
| `ND.Example.vuln3`, `c3_normal` | Today's `NDRule` sample (`$A = src(); $B = src(); $C = pass($A, $B); sink($C)`) gives the vulnerability, from a normal-layer conjunction. |
| `NDExact.nd_edge_exact`, `nd_edge_exact_valid`, `nd_edge_exact_gen`, `nd_edgeOK` | THE ND EXACTNESS THEOREM. Under S7 and S9, and either `Exact.FiltUp` (`nd_edge_exact`) or S13 for valid end locations (`nd_edge_exact_valid`: `Exact.FiltValid`, `Exact.BackOK` and `NDExact.ConjOK`): a normal-layer edge with the premise list `P` gives a support derivation `TaintN M n l L0` for EVERY support `L0` that `P` covers and every end location `l` of the edge (with `den` for one premise). The converse of `nd_coverage`. |
| `NDExact.nd_edge_exact_single`, `nd_edge_exact_nd` | The single-premise form (`den i f l0 l ⇒ TaintN … [l0]`) and the form for two or more premises (every covered support, every covered location). |
| `NDExact.CexLit.cex_lit`, `CexConjOK.cex_conjOK` | Both hypotheses are necessary: an abstract literal lets a correlated input with a mark exclusion through (the excluded locations reach nothing); without `ConjOK` a valid end location has an invalid support. |
| `NDExact.covers_nonempty` | Every fact covers some location (also `*/Universe` and `*∖X`), so a support can always be built. |
| `NDConfirmed.SupN`, `ConfirmedN`, `confirmed_real_N`, `confirmed_real_N_valid` | THE ND CONFIRMATION THEOREM. Under S7, S9 and S10 (`ND.NProg.WF`), and either `Exact.FiltUp` or S13 (`confirmed_real_N_valid`: `Exact.FiltValid`, `Exact.BackOK`, `NDExact.ConjOK`): a vulnerability whose sink edge is normal, whose premises are exact concrete facts, and whose premise set is supported JOINTLY (§4.9 condition 3: one call supplies every premise) is real for the support semantics (a tree witness `ND.ReachN`). |
| `NDConfirmed.CexSites.cex_sites` | Support of each premise on its own is not enough: two premises supplied at two different calls confirm a vulnerability that has no witness. |
| `NDConfirmed.confirmed_lift`, `confirmedN_iff`, `DN_lower`, `reachN_reach` | Without conjunctions the ND confirmation is the confirmation of §4.9 for one premise. |

### 10.7 Restricted runs and the iteration — `Restricted*.lean`

The restricted closure `DR` (`Restricted.lean`) is the rule list of a restricted run (§6.1), with the rules `initR`,
`ret` and `retRec`. A demanded flow and a demanded witness (`FlowR`, `ReachR`) are defined in §1. The coverage and
iteration theorems are generic over the rules, given the contracts C2 (`EmitContractOn`), C4 (`SatContract`) and C5
(`RestrictContract`) of §6.1.

| Theorem | Statement |
|---|---|
| `RCore.emitM_contract_I`, `emitM_copies`, `satI_contract`, `emitM_satI`, `emitM_inter`, `emitM_complete`, `emitM_shape`, `emitM_chain_strong` | The spec emission satisfies C2 for concrete added facts and copies the mark (C3); the emitted fact is exactly `a ∩ D-c`, lies inside its added fact, and has the chain of the fact or the demand chain. |
| `RCore.satI_markSub`, `satI_conc_record` | The satisfaction compares locations, and the marks of the fact against the marks of the premise: a cleaned fact reads a `*` premise, a concrete fact reads a `*`-premise summary. |
| `RCore.emitM_not_full_any` | C2 fails for a `*`-mark added fact under a `T` demand, for every satisfaction: the concreteness of the run is necessary. |
| `RCov.concInvR_all`, `added_concR`, `no_reqR`, `RExact.DR_concrete`, `DR_no_request`, `final_not_star`, `RMain.no_request_M` | A restricted run with a mark-copying emission is CONCRETE: every initial fact, edge and added fact has a concrete mark, no final fact has the `*` tail, and the run has NO request (also with cleaners). |
| `RCore.restrictU_fails`, `restrictS_contract`, `restrictU_eq_S_nonstar`, `RExact.restrict_U_eq_S` | The restriction of §6.4 (`restrictU`) does not satisfy C5 as a function; the auxiliary restriction `restrictS` does; the two agree on every conclusion without the `*` tail, and with a mark-copying emission they give the same run. So the coverage theorem holds for the run with `restrictU`. |
| `RExact.complete_premise_exact`, `complete_rev_exact` | A normal edge of a concrete run has a premise with the `$` tail, so its record reverses exactly. |
| `RCases.p1_found_M`, `p2_found_M`, `p1_reachR_M`, `p2_reachR_M` | Run 3 (forward) reports programs 1 and 2, with the emission of §6.3 and the restriction of §6.4. |
| `RCov.coverageR`, `reach_strongR`, `vuln_foundR` | THE COVERAGE OF A RESTRICTED RUN: for a demanded flow from a covered entry location, an edge covers the pair or the run has the request; its own summaries demand the same flow. |
| `RCov.coverageD`, `reach_to_reachR`, `vuln_foundD` | Run 1 reports every real vulnerability, and its summaries demand its witness. |
| `RCov.iteration_sound`, `iteration_sound_conc`, `RMain.iteration_sound_M`, `iteration_sound_M_identity` | THE ITERATION THEOREM: if every backward step satisfies the strong form of contract B (`BackwardContract`: every vulnerability witness that the summaries of a forward run demand stays demanded), EVERY forward run reports every real vulnerability; any field limits, any records. The form of §6.6 is weaker and is enough (`Backward.iteration_sound_M_D`). |
| `RCov.backward_identity`, `backward_of_superset`, `RMain.noSink_contract`, `everyWitness_contract_fails` | The identity backward step satisfies B; B is about sink witnesses only. |
| `Backward.DB`, `demOf`, `revSummaryDemand` | The backward run of §9.2: the rules of `DR` on the reversed program, the zero fact from the roots, the zero binding into every callee, the seeds, the balanced return; the hand-offs in both directions. |
| `Backward.B_general`, `iteration_general`, `BackwardContractD`, `repD_of_rep`, `iteration_sound_D`, `iteration_sound_M_D` | THE BACKWARD RUN SATISFIES THE CONTRACT: for every forward run, if the backward demand contains its reversed summaries and the seeds contain its reported sinks, the hand-off satisfies the mark-aware contract; so every forward run reports every real vulnerability. |
| `Backward.BackwardContractRep`, `rep_of_B`, `iteration_sound_rep`, `B_fragment_rep` | The contract for reported vulnerabilities only, with the plain demanded witness; on programs where no call binds back the backward run satisfies it directly. |
| `Backward.dem1_exact`, `dem2_exact`, `p1_found`, `p2_found` | For programs 1 and 2 the hand-off of the backward run is exactly the callee demand of `RCases.dem1M` (`dem2M`), the zero demand `Backward.zeroDem`, and one pattern `(D-c, none)` of the root; forward run 3 reports the vulnerability. |
| `Backward.lost_plain`, `B_fails_plain` | With the plain converse of the forward bindings (no zero binding into the callee) program 1 is lost. |
| `BExact.DB_concrete`, `DB_no_request`, `DB_no_requestM`, `CexSeed.cex_seed` | The backward run is concrete and raises no request when its seeds have concrete marks (a seed with the mark `*` would raise one). |
| `BExact.edge_exactB`, `edge_exactB_valid`, `edge_exactB_rev`, `summary_rev_flow`, `rev_record_exact`, `revRecs_exact`, `CexZeroBack.cex_rec` | A normal backward edge with a non-zero premise is exact for the reversed program and reverses into an exact forward record, under S11 (c); without S11 (c) it is false. |
| `BExact.recsSeq_exact`, `recsSeq_exactV`, `accRecs_exact`, `accRecs_exactM`, `seq_edge_exact`, `seq_confirmed_real` | The persisted forward records stay exact over the whole run sequence (S14 is a theorem); every normal edge and every confirmed vulnerability of every run is real. |
| `BExact.binv_all`, `no_static_rule_backward` | The backward run needs no static rule, if the reversed program satisfies S12 (a) to (d). |
| `RExact.edge_exactR_valid`, `closed_exactR_valid`, `recs_of_DR_valid`, `recs_of_D_valid` (valid locations, S13 and `RExact.RecsExactV`); `edge_exactR`, `complete_exactR`, `recs_of_DR`, `recs_of_D`, `closed_exactR`, `RMain.closed_records_exactM` (`Exact.FiltUp` and `RExact.RecsExact`); `RExact.recs_union` | Exactness and record reuse in forward restricted runs. Hypotheses: S7, the records that the run reads are exact (S14), every satisfaction reads the marks (`RExact.SatMark`), and the restriction only removes pairs (`RestrictSub`). The exit records of the run are exact again, and the union of exact record sets is exact. |
| `RExact.SupM`, `ConfirmedM`, `confirmed_realM_gen`, `confirmed_realM_gen_valid` (every satisfaction with `SatMark`, every restriction with `RestrictSub`); `RMain.confirmed_real_M`, `confirmed_real_M_valid` (the spec rules) | A confirmed vulnerability of a forward restricted run is real for the reference semantics (§3.5), under S7, S14 and `Exact.FiltUp` or S13 (`Exact.FiltValid`, `Exact.BackOK`); the support accepts the emitted exact fact. |

### 10.8 Statics — `Statics.lean`, `StaticsIter.lean`

| Theorem | Statement |
|---|---|
| `Statics.coverageD`, `vulnD` | Under the construction rules (`SWF`), run 1 with the position request of §4.10 (`Design`) reports every real vulnerability. |
| `Statics.DS_edgeOK`, `edge_exactS`, `edge_exact_validS`, `complete_exactS` | Its normal edges denote only real flows. |
| `Statics.cinv_all`, `no_any_above` | No static fact with the `[any]` tail occurs above a static position; a static fact above a position is an abstract static `*` fact. |
| `Statics.gen_read_DS`, `gen_read_sreq` | A static read on the abstract static root gives no fact and raises the position request. |
| `Statics.CexAbove.y_vuln_normal`, `CexWide.w_vuln_normal`, `CexClean.deep_vuln_normal` | A write in the caller, a write in a callee and a cleaner in a callee: the vulnerability is found through a normal edge. |
| `Statics.CopyF2F.c_vuln_normal`, `DeepSink.e_vuln_normal`, `DeepSinkParam.p_vuln` | A pass rule between static fields; a sink below a static field (the ordinary mark request climbs to a static caller premise: a normal edge; to a parameter premise: the request chain, a demand edge, as for an instance field). |
| `Statics.abovePos_len`, `f2f_not_above` | A path above a static position has at most one accessor; a field-to-field edge never lands above a static position. |
| `Statics.CexClean.shallow_misses`, `CexAbove.cex_user_misses`, `CexWide.counterexample` | The rule variants that fail: the chain answer of a static mark request; the narrow climb without a fallback; the first fire (the static root, reads only) with the fallback only for caller premises off the static base (`CexWide.Xn`, also with the at-or-below answer, `CexWide.Xc`). |
| `Statics.CexAny.counterexample` | Not a failing variant: the at-or-below answer, which the final rule uses (§4.10 item 2; `Statics.Design`, part `below`; in the program `CexAny.Xb`, `CexAny.Xc`), loses a flow WHEN a source puts an `[any]` fact on a bare class (`(S, <C>, [any], T)`). This is the reason for S12 (b): the interpreter rejects such a source (`interpreter.md` §1.4). |
| `StaticsIter.rinv_all`, `no_any_above_R`, `static_step_below`, `static_sink_below`, `no_request`, `DeepReadIter.deep_read_above` | AFTER RUN 1 NO STATIC RULE IS NEEDED: in a forward restricted run (`DR`), under S12 (a) to (d) (`StaticsIter.SWFR`) and persisted records that keep the static invariant (`StaticsIter.RecOK`), for every demand, no static `*` or `[any]` fact lies above a static position; every static operation at most two accessors deep is the case at or below; no request. A deeper static read or sink follows the ordinary rules of an instance field (`DeepReadIter.deep_read_above`: a restricted run can hold `(S, <C>.f, [any], T)` above a deep read). |
| `StaticsIter.reach_strongDSD`, `iteration_general_DS`, `no_static_rule_after_run1` | The iteration from run 1 = `DS`, with plain forward restricted runs after it: every forward run reports every real vulnerability, and every later forward run satisfies the invariant (under `StaticsIter.RecOK` for the records). The backward run `Backward.DB` is not covered (§11.2). |
| `StaticsIter.ExampleIter.run3_confirmed`, `WideIter.run3_confirmed`, `AboveIter.run3_confirmed`, `CleanIter.run3_confirmed`, `ExampleIter.demE_exact` | The worked static programs: forward run 3 confirms the vulnerability through a normal edge with no request; the exact demand for `Example`. |

| `StaticsConfirmed.SupS`, `ConfirmedS`, `confirmed_realS`, `confirmed_realS_valid` | Run 1 with the static rule confirms only real vulnerabilities; the support accepts the mark answer on a static premise (§4.10 item 4). |
| `StaticsConfirmed.confirmedS_iff`, `CexS.cexS_filt`, `CexS.cexS_mark`, `ExampleConf.confirmed`, `CleanConf.confirmed` | Without a static initial fact the static confirmation is the plain one; S7 and the validity are necessary; the worked programs are confirmed in run 1. |
---

## 11. What the proofs do not cover

### 11.1 Expected false-positive sources

The theorems say that a confirmed vulnerability is real for the reference semantics (§3.5): the program that the
micro edges describe. On the JVM the micro edges over-approximate the real program at the points below. There a
confirmed vulnerability (and a normal edge, and a record) can be false. These are EXPECTED false-positive sources: the
analysis keeps their results in the normal layer and does not refine them.

* A type filter on a `*` or `[any]` fact. The filter checks the concrete path only, so the fact keeps the locations below
  its path that a real value cannot have (§4.8).
* A reversed backward record. The backward run does not type-filter, so the record has no type filter (§8.7 R3).
* The weak alias write. The alias base keeps its old content (S2, `interpreter.md` A3, gap G7).
* The constructor pass-over. An added fact also passes over a constructor call, so the constructor does not
  overwrite the caller facts (`interpreter.md` §3.5, gap G8).
* The path-insensitive reading. A conjunction can combine literals that hold on paths that exclude each other (§4.6),
  and a negated mark literal counts as true (§3.5).

### 11.2 Other limits

* The concrete semantics is alias-free and location-level (§3.5).
* The theorems are about the closures `D` (run 1), `DR` (a forward restricted run), `DN` (run 1 with conjunctions),
  `Statics.DS` (run 1 with the static rule) and `Backward.DB` (the backward run). A real run differs from them by
  optimizations. Each one keeps the soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§8.1) | the dropped pairs are pairs of the kept fact (`subsumes_sound`) | the local step is proved; the composition is argued |
| merge rules 1 and 2, also for marks (§3.3, T1, T2, T2') | exact (`rule1_mem`, `rule2_den`, `rule2_mark`, `merge_inter`, `merge_mark_inter`) | proved |
| the T5 fold | the denotation does not change | argued |
| persisted records (R4) | a normal edge has no false pair; adding edges keeps coverage (rule `retRec`, with `applicable`) | proved for one forward run under S14 (`RExact.recApp_markSub`, `RMain.p3_reuse_exact`); the composition over the run sequence and the backward records are argued (the list below) |
| W6 (`[any]` always in the demand layer) | a layer refinement: the W6 run has the same facts, with the same or a raised layer (`W6.D_le_D6`, `D6_le_D`, `DR_le_DR6`, `DR6_le_DR`) | proved for `D` (under `W6.SummaryStar`, which `W6.summaryStar_policy` gives for the run-1 policy) and for `DR` (under `W6.RestrictLE` and `W6.ExactInitConc`, which `W6.restrictU_LE` and `W6.DR_eic` give): soundness, exactness, confirmation and the iteration (§10.3). Argued for `Statics.DS`, `ND.DN` and the backward run |

* The backward run is modelled as the closure `Backward.DB` (the rules of `DR` on the reversed program, with the zero
  rules of §9.2), and it satisfies the contract B (`Backward.B_general`). The reversal of a conjunctive micro edge into
  one edge per literal (§9.2), the alias edges of the reversed call (§9.2; the model is alias-free, S2) and the
  interpreter's call-site rules of the backward run (`interpreter.md` §4.9) are argued, not modelled.
* ND edges are modelled for run 1 (`DN`): coverage, the vulnerability theorems (§10.6) and the exactness of the normal
  layer against the support semantics `TaintN` (`NDExact`, under S7, S9, S10 and S13) are proved. The CONFIRMATION of
  a vulnerability through a conjunction is proved too, with the joint support of §4.9 condition 3
  (`NDConfirmed.confirmed_real_N`), in run 1. No edge with two or more premises is a record (§8.7 R1). A restricted
  run with ND edges is ARGUED, not modelled:
  1. its facts are concrete, so a literal never raises a request (§4.5);
  2. the restriction of a summary with several premises (§6.4, the special cases) only removes pairs from the
     conclusion;
  3. the contract B for a TREE witness (`ND.ReachAll`) needs a demand pattern on every node of the tree. The backward
     run reverses a conjunctive edge into one edge per literal (§9.2), so a requirement at the conclusion reaches every
     branch.

  `D_sub_DN` embeds the distributive part, so the iteration theorem holds unchanged for a program without conjunctions.
* PREMISE SETS AND LISTS. The zero fact is a premise in the spec and in the model (§1). `ND.lean` keeps premise LISTS
  (with `[zeroFact]` for a zero-to-fact edge); this spec keeps SETS. A list and its set name the same entry locations,
  so every ND theorem carries over (argued). The spec names an edge by the premises that are not the zero fact (§4.6):
  `{zero, i}` is a fact-to-fact edge here and an edge with two premises in the model. It applies at a call like the
  model edge, with one link per member (§4.6, event E6), and it is never a record (§8.7 R1). A conjunction result whose
  premise set has one member is an ordinary edge; it can be a record if it is normal, and it is exact
  (`NDExact.nd_edge_exact`, for every premise list).
* The static rule of §4.10 is modelled as a separate run-1 closure `Statics.DS`. Soundness, exactness and the
  iteration that starts from it are proved (`StaticsIter.iteration_general_DS`). The run-1 proof needs that a cleaner
  on `S` names its mark (S12 (e)). The interpreter makes it true: `RemoveAllMarks` on `S`, at any depth, is the kill of
  a strong write, not a cleaner (`interpreter.md` §1.4). The restricted runs do not need it (`StaticsIter.SWFR`). The
  static rule and the conjunctions are in separate models: a conjunction literal on `S` uses the plain run-1 rules
  (§4.6).
* ARGUED, NOT PROVED. These claims of the spec have no Lean proof. Each item gives the claim in one sentence:
  * The backward run satisfies W2 (it is concrete, `BExact.DB_concrete`; no theorem states W2 for `Backward.DB`).
  * The backward run needs no static rule: proved if the reversed program satisfies S12 (a) to (d)
    (`BExact.no_static_rule_backward`); that the interpreter's reversed program satisfies them is argued (the static
    positions of the reversed program are the forward write targets).
  * Every persisted record keeps the static invariant `StaticsIter.RecOK` that the static theorems of the restricted
    runs assume: argued from the run-1 invariant (`Statics.cinv_all`) and the restricted-run invariant
    (`StaticsIter.rinv_all`), run by run.
  * W3 (every result of a run has at most `L` counted accessors when the field limit does not decrease) is argued.
  * A conjunction of `k > 2` literals is argued by chaining binary conjunctions; the model `ND.Conj` has two literals.
  * A conjunctive sink (§4.9) is argued as a conjunction to a fresh target with a sink on it; `ND.DN` has no
    conjunctive sink rule.
  * The cleaners of a call act on the bound fact before the callee (§5.3 step 4), and they give the added fact its own
    layer on the link (§8.3): argued, because the model `Call` has no cleaners (a cleaner is an instruction of the
    CFG, `Instr.clean`).
  * The backward demand of a summary with several premises, one pattern per member (§9.2), is argued.
* THE IMPLEMENTATION AGAINST THE MODEL. This is the only list of these differences. Each one keeps the theorems,
  except where the item says otherwise:
  * W6 (§2.3). The Lean `applyEdge` can give an `[any]` result in the normal layer: on an `[any]` input in the normal
    layer, or for an `[any]` target on an exact derivation. The implementation puts such a result in the demand layer
    (§4.1 step 6). W6 only moves edges from the normal layer to the demand layer. Soundness ignores the layer, and
    exactness and confirmation hold for every subset of the normal edges (`Invariant.demand_of_any_ok`). For the
    whole run, the W6 run has the same facts (§10.3: `W6.D6_le_D`, `D_le_D6` under `W6.SummaryStar`; `W6.DR_le_DR6`,
    `DR6_le_DR` under `W6.RestrictLE` and `W6.ExactInitConc`). The two agree on every input that satisfies W6, except
    for this layer bit. With an abstraction outside the spec, W6 can change a fact, not only its layer
    (`W6.Cex.cex_w6_changes_fact`). In the backward run W6 is argued: its zero rules read the normal-layer zero fact.
    The Lean predicate of a normal edge, `AFact.complete`, also excludes `[any]`; with W6 the two agree.
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
  * The record application (§8.7 R4). The model rule `retRec` applies a record when the run's satisfaction OR
    `applicable` holds. The implementation uses `applicable` only. A record only adds edges, so fewer applications keep
    the coverage, and each application is exact.
  * The type filters of the backward run (§9.2). The model keeps the type filters in the backward run; the
    implementation drops them. This only adds backward flows, so it only enlarges the demand.
  * The static base at a call in a restricted run (§5.3 step 1). The model call always touches `S`; the interpreter
    leaves it untouched when the callee touches no static (`interpreter.md` D15). This keeps the theorems only over
    the final call graph (gap G5).
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
| `Basic.lean` | All definitions of run 1: locations, facts (marks `*`, `T`, `*∖X`), `den`, `applyEdge` with `markComp`, the normal form, the field limit, statements, calls, cleaners (`Cleaner`, `cleanPos`, `cleanRes`), type filters, `Flow`, the closure `D`, `Reach`, `answerInit`, `policy`, `revEdge`. |
| `Backward.lean` | The backward run (`DB`), the hand-offs, the contract B for it (general and for programs 1 and 2). |
| `Statics.lean` | The static rule of §4.10 as the run-1 closure `DS`: soundness, exactness, the invariant, the worked programs, the failing variants. |
| `StaticsIter.lean` | No static rule after run 1: the invariant of forward restricted runs, the iteration from `DS`, the worked programs through forward run 3. |
| `NDConfirmed.lean` | The confirmation through a conjunction (joint support), with its counter-examples. |
| `StaticsConfirmed.lean` | The confirmation of run 1 with the static rule. |
| `BackwardExact.lean` | The backward run: concreteness, no request, exactness of its edges, exact reversed records; record exactness over the run sequence. |
| `W6.lean` | W6 for the whole run: the simulation, soundness, exactness, confirmation, the iteration. |
| `Restricted.lean` | The restricted runs: demand patterns (`DemandEdge`), the emission `emitM`, the satisfaction `satI`, the restriction `restrictU`, the closure `DR`, `FlowR`, `ReachR`, the contracts, `summaryDemand`, `BackwardContract`, and auxiliary rules that some proofs use (for example `restrictS`, §10.7). |
| `ND.lean` | ND edges: conjunctive micro edges, the support semantics `TaintN`, the closure `DN`, the ND coverage and vulnerability theorems. |
| `NDExact.lean` | The exactness of normal-layer ND edges against `TaintN` (`LitConc` = S9, `ConjOK`), with the two counterexamples. |
| `Cases.lean`, `RestrictedCases.lean` | Test vectors (`decide`), programs 1 and 2. |
| `Core.lean`, `SharedExcl.lean`, `RestrictedCore.lean` | The local lemmas. |
| `Coverage.lean`, `RestrictedCoverage.lean`, `RestrictedMain.lean` | Soundness of run 1 and of the iteration; the instantiation with the spec rules. |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `RestrictedExact.lean` | Exactness, invariants, the records of a request-free initial fact, confirmed vulnerabilities. |
| `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean` | Concept against optimization. |
| `Reverse.lean` | Reversal. |

Lean names. A qualified name `F.x` in this spec names the declaration `x` in the namespace `ApSpec.F`, or in the file
`F.lean`. The short namespaces: `RCore` is `RestrictedCore.lean`, `RCov` is `RestrictedCoverage.lean`, `RExact` is
`RestrictedExact.lean`, `RMain` is `RestrictedMain.lean`, `RCases` is `RestrictedCases.lean`, `RStore` is
`RestrictedStore.lean`, and `CoreAux` is in `Core.lean`. The declarations of `Basic.lean`, `Core.lean` and
`Restricted.lean` are in the namespace `ApSpec` itself (for example `applyEdge`, `satI`, `emitM`, `restrictU`,
`markMatchB`); `Core.x` names a declaration of `Core.lean`. Every other file has the namespace of its name (`Statics`,
`StaticsIter`, `Backward`, `Reverse`, `ND`, `NDExact`, and so on). A name with no qualifier belongs to the file or the
namespace of the last qualified name before it.

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
   the normal layer. The implementation applies W6, so the test asserts the same fact in the demand layer
   (`Invariant.demand_of_any_ok`, §11.2).
2. Equivalence property tests (`EdgeTreeEquivalenceTest`): random path facts and micro edges; the tree result denotes
   the same pairs as the concept result, layer and mark exclusion included. The same for the tree restriction (§7.4).
   The tests of §3.4 (`covers`, `overlap`, `applicable`, `inside`) and `cleanPos` (§4.7) against the denotation of §3,
   on a bounded universe with a fresh accessor and a fresh mark.
3. Layer tests: a cut fact is in the demand layer; an `[any]` result is in the demand layer (W6); a demand-layer input
   gives a demand-layer output; a `*` conclusion is never in the demand layer; a `*` fact applied above a premise gives
   a demand-layer result.
4. Mark tests: every row of the mark gate and of the result mark (§4.1 steps 4, 5); a `*∖X` summary conclusion stops an
   added fact with a mark in `X`; a sink for `T ∈ X` neither triggers nor requests; a request for `T ∈ X` does not
   climb; the preconditions of `concat` (§4.1) fail on a `*∖X` premise, on a `$` premise with the mark `*`, and on a
   `$` premise with a `*` target.
5. Cleaner tests: every row of the two tables of §4.7; the split (`*∖{T}` plus the request, then the concrete answer
   cleaned exactly); no request for `T ∈ X`; the all-marks cleaner; a cleaned fact through a field write past the field
   limit keeps its mark exclusion.
6. Type filter tests: a fact on an accepted path passes, also with a `*` tail; a fact on a rejected path is dropped; the
   predicate is prefix-closed.
7. ND tests: a conjunction from two facts of different premises gives the union premise set; the last arriving fact
   completes it; a fact that only overlaps its literal enters the store and gives a demand-layer result; an `[any]`
   literal (`ContainsMarkOnAnyField`) accepts a fact below its position; a summary with several premises needs one
   link per premise; ND conclusions have no `*` tail; a vulnerability through a conjunction is confirmed only if every
   premise of its sink edge is exact and the premise set is supported jointly at one call statement (§4.9 condition 3);
   the negative test `NDConfirmed.CexSites`: two premises supplied at two different calls are not confirmed. A
   conjunction of a zero-premise fact and a fact of the premise `i` gives the premise set `{zero, i}`, a fact-to-fact
   edge that is never a record. Today's `ExampleTest.test nd rule` as an analysis test.
8. Merge tests: rules 1, 2 and 2'; a union of exclusions or mark exclusions is never made.
9. Request tests (run 1): the mark gate raises a request; a standing request is answered by a later added fact and by a
   second added fact; a standing request reaches a second caller edge of an EXISTING added fact (the program of §4.5);
   propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain; every request
   premise is a policy fact `(x, [], *, {}, *)` or a static position answer `(S, p, *, {}, *)`. In a restricted run, a
   request is a bug (assert it).
   Position request tests (§4.10): on an identity static `*` edge at the root `[]` or a class, a static read, a Go global
   read, the class keep edge of a write and a pass rule between static fields raise the position request (cut to the
   static field) and give no fact; a sink on `S` raises the ordinary mark request; a deep read below a static field is
   the ordinary case `above`; the root keep edge adds
   `<C>` to the exclusion; an added fact at or below the position answers it, an added fact above it does not; the
   climb through a caller edge on `S`; the mark answer on a static premise (item 4: the added fact itself at or below,
   the chain answer above); the programs `Statics.CexAbove`, `CexWide`, `CexClean`, `CopyF2F`, `DeepSink` find their
   vulnerability in the normal layer, and `DeepSinkParam` in the demand layer.
10. Call and ownership tests: every event of the table of §5.3, in two orders; the callee restricts before it publishes;
    a caller reads the summaries of every premise its fact satisfies; a record applies when its premise covers the added
    fact, in every run after the run that made it; the return order of §5.3 step 5; the zero fact passes over a call and
    enters every resolved callee.
11. Abstraction tests: run 1 emits the most abstract fact; every row of the two tables of §6.3; the emitted fact is
    exactly `a ∩ D-c` with the mark of `a`; the same result for two insertion orders.
12. Restriction tests: every row of the table of §6.4; the union over two demand patterns; no result without `D-p`;
    a summary with several premises keeps its whole premise set; program 2 (§6.4).
13. Iteration tests: programs 1 and 2 as analysis tests with the field limits 1 (run 1), 2 (run 2, backward) and 3 (run
    3), so the limit does not decrease (W3); the vulnerability is reported in every forward run. A worker loop with a
    sink that never returns (§9.2). The backward zero rules of §9.2: the zero fact enters every callee, a zero-premise
    backward summary returns to every caller without a restriction; the hand-off of §9.2 in both directions, also a
    `*∖X` entry pattern.
14. Store tests: index completeness against a list filter (records, demand patterns, requests, conjunctions,
    subscriptions).
15. Reversal tests: every row of §9.1 that occurs for a record, also with `*∖X`; the forward record and its reversed
    reading give converse results on the same concrete pair.
16. Analysis tests (the gate of the new analyzer): the existing `*AnalysisTest` suites, run with `cleanTest`;
    `DeepCleanSummaryAnalysisTest` and the cleaner suites for §4.7. A lost finding is a test whose message says that no
    vulnerability reached the sink; read the message, do not count failures.
