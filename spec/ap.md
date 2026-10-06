# Access paths and storages — specification

Status: design spec for phase 1 of [bidirectional-task.md](../bidirectional-task.md) ("New AP with all required
storages"), version 5. This document is normative. The design decisions and their reasons are in
[`ap-history.md`](ap-history.md). The spec has two parts:

* this document (`ap.md`) defines the access path (AP): the fact, the edge, the operations and the primitives (micro
  edge, summary edge, mark request, mark conjunction, cleaner, type filter, emission), the runs and the storages;
* [`interpreter.md`](interpreter.md) defines how the analyzer interprets the IR with the AP: the micro edges of the
  statements and of the calls, the aliases, and the order of the rules.

The formal model is in [`spec/lean`](lean). Every theorem named here is machine-checked and constructive (§12).

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
contract of the backward run is in §10.7.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | The interpreter describes a statement by its statement summary: the bases that it touches and its micro edges (`interpreter.md` §2). Every micro edge (a statement edge or a call binding edge) is PRECISE AND COMPLETE: the micro edges of a statement give exactly its flows. The flows of a rule are read with every negated mark literal true (the reference semantics of a path-insensitive engine, §4.2); with this reading a source, sink or pass-rule edge is precise. | The interpreter. |
| S2 | Extra micro edges describe the aliasing: gen edges to the alias paths of the aliases that hold. Each alias edge is precise. The write at an alias is WEAK: the alias base is not touched, so it keeps its old content (`interpreter.md` A3, gap G7). This keeps soundness when an alias does not hold. It is an expected false-positive source (§11.1). The model itself is alias-free. | The alias analysis. |
| S3 | A method does not reassign its formal parameters. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. | The CFG normalisation. |
| S5 | A type filter accepts every path that a real value of the static type can have, and it is prefix-closed (§4.8). | The type checker. |
| S6 | The result of run 1 is the least fixed point of the rules of §4–§6 (Lean: `D`). The result of a later run is the least fixed point of the restricted rules (Lean: `DR`). The worklist may compute it in any order. | The analyzer. |
| S7 | Mark well-formedness: no micro edge or call binding has a `*∖X` premise, and a micro edge with a concrete target mark has a concrete premise mark (`Exact.MarkWF`). Without it a normal edge can claim a cleaned mark (`Exact.CexMark`). | The interpreter (sources have the premise mark `zeroMark`, conditional sources `T`). |
| S8 | No `*/Universe` edge: a micro edge with a `$` premise has a concrete premise mark, and no micro edge, binding or initial fact has the kind `*/Universe` (`Invariant.no_univ_star`; each hypothesis is necessary: `no_univ_needs_*`). | The interpreter. |
| S9 | A conjunction literal has a concrete mark (`NDExact.LitConc`). Without it the ND exactness is false (`NDExact.CexLit.cex_lit`). | The interpreter (a mark literal names its mark). |

Inside this scope:

* Run 1 is SOUND: an edge covers every concrete flow, and the run reports every concrete source-to-sink flow (§10.1).
* A later run is SOUND RELATIVE TO ITS DEMAND: it reports every concrete vulnerability whose flow the demand covers,
  and it passes the same flow on as the demand of the next run (§10.7).
* The backward run of §9.2 satisfies the contract of the iteration (`Backward.B_general`), so EVERY FORWARD run reports
  every concrete vulnerability (`Backward.iteration_general`; `RMain.iteration_sound_M` for any backward step that
  satisfies the contract). So the analysis can stop at any forward run, and a vulnerability that a forward run does not
  report is not real.
* Inside the smaller scope of NORMAL edges the analysis is also EXACT: every pair of such an edge whose end location
  is VALID (every type filter accepts it; real values have only valid locations) is a concrete flow
  (`Exact.edge_exact_valid`, §10.3). The validity must go back along the micro edges (`BackOK`, §4.8). Exactness is
  against the path-insensitive reference semantics: a conjunction (§4.6) and a rule condition that one fact does not
  decide (§4.2) are expected over-approximations; they do not move an edge to the demand layer. A normal edge with
  conjunctions is exact against the support semantics `ND.TaintN` (`NDExact.nd_edge_exact`, `nd_edge_exact_valid`,
  under S9).
* A CONFIRMED vulnerability (§4.9) whose sink pattern covers only valid locations is real for the reference semantics
  of S1–S9, modulo the expected false-positive sources of §11.1 (`Confirmed.confirmed_real_valid`,
  `RMain.confirmed_real_M_valid`). For a program without type filters the same holds with no validity condition
  (`Confirmed.confirmed_real`, `RMain.confirmed_real_M`). The confirmation theorems are for programs without
  conjunctions, so a vulnerability through an ND edge or a conjunction is never confirmed (§4.9).

---

## 1. Terms

| Term | Meaning |
|---|---|
| base | A local, an argument, `this`, the return value, the exception, a constant, the `ClassStatic` base, or the zero base. |
| accessor | A field, an array element, a class accessor (`<static>(C)`), or another structural step (type info, value). Not a mark, not `[any]`, not `$`. The set of accessors is unbounded: for each finite set of accessors there is an accessor outside it. So a `*/E` tail always admits a continuation other than `[]`, and `*/E` is never `$`. |
| counted accessor | A field or an element accessor. The field limit counts only these. |
| path | A finite list of accessors. |
| location | A concrete triple (base, path, mark): the value at `base.path` carries `mark`. |
| tail | The end of a fact path: `*` (abstract), `[any]` (any continuation), or `$` (exact). |
| exclusion | A finite set of first accessors that a `*` continuation must not start with. |
| kind | The tail with its exclusion: `*/E`, `[any]` or `$` (Lean: `Kind`). |
| mark | `*` (abstract: the mark of the premise passes), `T` (concrete), or `*∖X` (abstract except the marks of `X`; conclusions only). The set of marks is unbounded, so two abstract marks always have a common mark. |
| zero mark | The concrete mark of the zero fact (Lean: `zeroMark`). No rule names it. |
| effective mark | The mark that a sink reads on an edge `i → f`: `f.mark` if it is concrete, else `i.mark` if it is concrete, else abstract (§4.9). |
| fact | A tuple (base, path, tail, exclusion, mark). §2. |
| premise | The initial fact of an edge: the fact that the edge depends on, at the method entry (forward run) or at the method exit (backward run). An ND edge has a SET of premises. |
| conclusion | The final fact of an edge: the fact at a statement. |
| edge | (premise or premise set, layer, statement, conclusion), with one exclusion. The zero fact is also a premise. |
| layer | `normal` or `demand`. The demand layer of premise `i` is written `i~`; of the zero fact, `Zero~`. |
| normal edge | An edge in the normal layer (Lean: `AFact.complete`, which also excludes `[any]`; with W6 the two agree). Only a normal summary edge can become a record. |
| demand-layer edge | An edge in the demand layer. The analysis uses it in its own run like every edge. It never persists it and never reverses it. |
| exact | (1) The `$` tail. (2) A property of an edge or a record: every pair of it is a concrete flow (no false pair). (The cleaner reach `exact` of §4.7 is a third, local meaning.) |
| touched base | A base that a statement or a call can change. A fact on an untouched base passes the statement unchanged. A fact on a touched base keeps only what a micro edge gives (§4.2). |
| statement summary | What the interpreter gives for one statement: the touched bases, the micro edges and the type filters (`interpreter.md` I1). Not a summary edge. |
| micro edge | One edge of a statement summary, or one call binding edge, that the interpreter makes. A callee summary edge is NOT a micro edge (§4.3). |
| summary edge | An edge whose statement is the method exit (forward run) or the method entry (backward run). |
| record | A normal summary edge that the analysis persists for later runs (§8.7). |
| summary rewriter | An interpreter feature that cleans the summary results at a call (`interpreter.md` §5.2). Not a summary edge. |
| bound fact | A caller fact after a binding edge into the callee, in callee coordinates. The sinks of the call check it (`interpreter.md` §4.5 step 3). |
| added fact | A bound fact after the cleaners of the call (`interpreter.md` §4.5 step 5.1). The callee gets it. |
| link | One (added fact, caller edge) pair in the added fact store of the callee (§8.3). A standing request checks every link (§4.5). |
| abstraction, emission | The function that selects the initial facts for an added fact. §6. |
| request | Run 1 only. A MARK request asks for a concrete mark on an initial fact (§4.5); a POSITION request asks for a static position on the abstract static root (§4.10). |
| standing | A standing request, subscription or conjunction fact stays active until the end of its run: it also acts on every matching event that comes later. |
| root | An entry method of the analysis. Every run starts with the zero fact as an initial fact of each root (Lean: `roots`). |
| run | One analysis pass in one direction with one field limit `L`. The runs are numbered in order: run 1 (forward), run 2 (backward), run 3 (forward), and so on (§6.6). |
| restricted run | Every run after run 1. It strictly follows its demand. |
| demand pattern | A pair of patterns that a restricted run gets from the run before it, in the orientation of the restricted run: the entry pattern `D-c` and the exit pattern `D-p` (or none, if the demand does not reach the method exit). Lean: `DemandEdge`. |
| demand (of a run) | The set of demand patterns that a restricted run gets (§8.6). Not the same as the demand layer. |
| demanded flow | A concrete flow whose every call step has a demand pattern of the callee that covers it (Lean: `FlowR`, §10.7). |
| demand vulnerability | A triggered vulnerability that is not confirmed (§4.9). Not the same as a demand-layer edge. |
| support, supported | A premise is SUPPORTED if a chain of normal call bindings from the zero fact of a root produces it exactly (§4.9 condition 3; Lean: `Sup`, `SupM`). |
| strong enough | A fact is strong enough for a premise if the premise covers it (`applicable`, §4.3). Such a fact is at or below the premise (§4.1 case `below`). |
| not strong enough | The premise does not cover the fact. A fact above the premise (§4.1 case `above`) is never strong enough: the result loses the correlation. |
| satisfies | A fact satisfies a premise if the caller may apply the summary edges of that premise to it (§4.3). |
| concrete run | A run in which every fact has a concrete mark. Every restricted run is concrete (§6.3). |
| method key | `MethodEntryPoint` (context plus entry statement), as today (Kotlin: `MethodKey`). The method key of a method is the same in every run. |

---

## 2. The fact and the edge (the concept)

### 2.1 The tuple

A fact is `(base, path, tail, exclusion, mark)`:

* `path` — the concrete accessors. It never contains `[any]`, a mark or `$`.
* `tail ∈ {*, [any], $}`.
* `exclusion` — a finite set of accessors, only with the `*` tail.
* `mark ∈ {*, T}` for a premise; `mark ∈ {*, T, *∖X}` for a conclusion.

### 2.2 Edges, layers, the edge exclusion and the mark exclusion

An edge is `(premise, layer) → (statement, conclusion)`. The zero-to-fact edge is `Zero → (layer, statement, fact)`.
An ND edge is `({premise1, …, premisek}, layer) → (statement, conclusion)` with `k ≥ 2` (§4.6).

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
* Every initial fact that run 1 emits has the Empty exclusion (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`). In a restricted run an emitted fact can have the exclusion of the demand (the meet
  with a `*/E` entry pattern, §6.3); it has a concrete mark, so it starts in the demand layer and makes no record. So in
  practice the exclusion is a property of the conclusion. Only a field write (a kill) makes it larger.
* The LAYER is part of the edge identity. A micro edge has no layer (§4.2): the layer belongs to the propagation edge.
  Only these AP operations move a propagation edge to the demand layer:
  * the case `above` of §4.1, and a lost correlation (`lostCorr`, §4.1);
  * an `[any]` result (W6);
  * the cut of the field limit (§4.4);
  * a conjunction with an input that is in the demand layer or that its literal does not cover (§4.6);
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
| W3 | In a run with the field limit `L`, every result of an operation has at most `L` counted accessors (§4.4). This holds if the field limit does not decrease from run to run (§6.6): then a premise emitted from a demand chain (§6.3) and a fact that passes an untouched base are also in the bound. A micro edge (§4.2) has no bound. |
| W4 | `[any]` is a tail only. A path has no inner `[any]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. |
| W6 | A conclusion with the `[any]` tail is in the demand layer. |
| W7 | Only a conclusion has a mark exclusion. An ND conclusion has no `*` tail. |

W2 holds for every derived fact, in run 1 and in every restricted run (`Invariant.final_star_legal`,
`RExact.final_star_legalR`).

W6 is a rule of the implementation. The model keeps an `[any]` conclusion possible in the normal layer. The rule W6
only moves edges from the normal layer to the demand layer, so every theorem stays true for the rule W6: soundness
ignores the layer, and exactness and confirmation hold for every subset of the normal edges
(`Invariant.demand_of_any_ok`: an `[any]` result in the demand layer keeps its pairs and only raises the layer). In the
model a normal-layer `[any]` needs an `[any]`-target micro edge on an exact derivation. The interpreter has one kind:
the any-field rules, a source or a pass rule with an `[any]` target (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`;
`interpreter.md` §4.1). Under W6 every result of these rules is in the demand layer. So an `[any]` result never makes a
record, and a vulnerability whose taint comes only from an `[any]`-target source is never confirmed: it stays a demand
vulnerability.

No exclusion is "Universe". In the model, `Excl.univ` still exists: it encodes a `$` premise in the operation tables
(`tailExcl`). A `*/Universe` conclusion needs a `$`-premise edge that acts on a `*`-tail fact. Every `$`-premise micro
edge of the interpreter has a concrete premise mark (`zeroMark` for sources, `T` for conditional sources). A `*`-tail
fact has the mark `*` or `*∖X` (W2). So the mark gate never lets such a fact through (§4.1 step 4).
`Invariant.no_univ_star` proves it under S8, and `Invariant.final_star_legal` proves W2 for every derived fact.

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. A source rule is a micro edge from the zero fact. Zero-to-fact edges are
edges with the zero premise, in the normal or the demand layer.

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
  merge into one with `X1 ∩ X2` (a mark passes the merged edge iff it passes one of them; `Tree.rule2_mark`).
* A UNION of exclusions happens only along one derivation (a field write after another, a cleaner after another). A
  union across two different edges is FORBIDDEN: it removes pairs that one of the two edges has
  (`Subsume.union_loses_pairs`).

### 3.4 Reference types and tests

The reference forms of §4 and §6 use these types. A premise, a pattern and an added fact are a `Pattern`: a path fact
with the exclusion of its `*` tail. The implementation interns a premise as an `InitialAp` (§7.1).

```kotlin
enum class Tail { STAR, ANY, EXACT }

/** A canonical (sorted, de-duplicated) set of concrete marks: the X of *∖X. Operations: `in`, `isSubsetOf`, `+`. */
class MarkSet(val ids: IntArray)

/** `*` is Star(MarkSet.EMPTY). A premise and a demand pattern never have excluded marks; an added fact can. */
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
        is MarkSlot.Star -> i.excluded.isSubsetOf(c.excluded)   // *∖X ⊇ *∖Y iff X ⊆ Y; * ⊇ every abstract mark
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

/** §4.3, run 1 and every record: the premise j covers the caller fact a (Lean: applicable). */
fun applicable(j: Pattern, a: Pattern): Boolean =
    covers(j, a) && (j.fact.tail != Tail.ANY || a.fact.tail == Tail.ANY)

/** §4.3, the summaries of a restricted run: j lies inside a as locations, and markSub(j, a) (Lean: satI). */
fun inside(j: Pattern, a: Pattern): Boolean =
    covers(a.copy(fact = a.fact.copy(mark = MarkSlot.Star(MarkSet.EMPTY))), j) && markSub(j.fact.mark, a.fact.mark)
```

`ExclusionSet` is a finite set: Empty or Concrete, with the operations `admits(r)`, `union` and `isSubsetOf`. An empty
Concrete set must not exist (return `Empty`). Keep the excluded accessors as a CANONICAL (sorted, de-duplicated)
`IntArray` of `AccessorIdx`; the same for `MarkSet`. The edge trees are keyed by both, so two equal sets must be equal
values. Because the sets of accessors and marks are unbounded
(§1), these tests are exact: `covers`, `overlap` and `cleanPos` (§4.7) need no "all accessors" or "all marks" case.

---

## 4. Operations and primitives

### 4.1 The core computation: delta-concat

`concat(c, from →_E to)` computes the result of an edge `from → to` with the edge exclusion `E` on the conclusion `c` of
a current edge. `Ec` is the exclusion of the edge of `c`. `E` is the one exclusion of the edge (§2.2): the shared
exclusion of a correlated edge, or the exclusion of a `*` premise of an uncorrelated edge, else Empty. Two operations
use `concat`: the micro edge (§4.2) and the summary edge (§4.3). Lean: `applyEdge`.

Preconditions. `concat` ASSERTS them; an edge that breaks one is a bug of the interpreter or of the analyzer:

* the premise mark is `*` or `T`, never `*∖X` (S7);
* a `$` premise has a concrete mark (S8);
* a `$` premise has no `*` target (`interpreter.md` I7).

So a `$` premise meets only facts with a concrete mark: on a `*`-tail fact (mark `*` or `*∖X`, W2) the mark gate gives a
request or nothing (step 4). A summary edge meets the preconditions too: an initial fact never has `*∖X` (§2.2); a `$`
initial fact is the zero fact, an answer or an emission, all with a concrete mark; and a concrete premise has only
concrete conclusions (`Coverage.edge_conc`), which have no `*` tail (W2).

Step 1 — base. If `c.base ≠ from.base`, the result is empty.

Step 2 — position:

* `below r`: `c.path = from.path ++ r`. The fact is AT OR BELOW the premise.
* `above r`: `from.path = c.path ++ r`, `r ≠ []`. The fact is ABOVE the premise: NOT STRONG ENOUGH.
* `apart`: neither. The result is empty.

A fact in the case `below` is strong enough only if the premise covers it (§1): an `[any]` fact at a `*/E` premise is
in the case `below r = []`, but the premise does not cover it.

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
| `T` | `*` or `*∖X` with `T ∉ X` | NO fact; the request `T` on the premise of `c` (§4.5) |

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

The step only enlarges the fact (`CoreAux.norm_sound`, `Invariant.demand_of_any_ok`).

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
    data class Request(val mark: TaintMark) : EdgeOutcome
}

/** `edgeDemand`: the layer of the applied edge; true for a demand-layer summary edge (§4.3), false for a micro edge. */
fun concat(c: Conclusion, edge: PathEdge, edgeDemand: Boolean = false): EdgeOutcome {
    val from = edge.from
    check(from.mark !is MarkSlot.Star || from.mark.excluded == MarkSet.EMPTY)          // S7
    check(from.tail != Tail.EXACT || from.mark is MarkSlot.Concrete)                    // S8
    check(from.tail != Tail.EXACT || edge.to.tail != Tail.STAR)                         // I7
    if (c.fact.base != from.base) return EdgeOutcome.None
    val p = from.path
    val q = c.fact.path
    val shape = when {
        q.size >= p.size && q.subList(0, p.size) == p -> below(c, edge, q.drop(p.size))
        p.size > q.size && p.subList(0, q.size) == q -> above(c, edge, p.drop(q.size))
        else -> null
    } ?: return EdgeOutcome.None
    val premiseMark = from.mark
    if (premiseMark is MarkSlot.Concrete) {                                   // step 4: the mark gate
        when (val cm = c.fact.mark) {
            is MarkSlot.Concrete -> if (cm.mark != premiseMark.mark) return EdgeOutcome.None
            is MarkSlot.Star ->
                return if (premiseMark.mark in cm.excluded) EdgeOutcome.None
                else EdgeOutcome.Request(premiseMark.mark)
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
caller base; `interpreter.md` §2, §3). A callee summary edge is not a micro edge: it applies only to a fact that
satisfies its premise (§4.3). A micro edge applies to EVERY fact on a touched base that overlaps its premise: both cases
of §4.1. Example: the fact `(a, ., *, {}, *)` and the micro edge `(a, .f, *) → (b, ., *)` of `b = a.f` give
`(b, ., [any], {}, *)` in the demand layer (`Cases.lean`).

The statement transfer of one conclusion `c` (Lean: `transfer`):

* If `c.base` is not touched: the result is `c` (`Sequent.Unchanged`).
* Otherwise: the union of `concat(c, e)` over all micro edges `e`, then the field limit (§4.4). A touched base keeps only
  what an edge gives again. That is the kill.

Every micro edge (a statement edge, with its alias edges, or a call binding edge) is precise and complete (S1, S2).
The field limit never applies to a micro edge: a micro edge keeps its full paths, of any length. The analyzer applies
the limit to the RESULT, after it applies the micro edge to the propagated edge (§4.4; Lean: `transfer` limits the
results, and `Program.WF` puts no bound on a micro edge).

A micro edge has NO LAYER. The layer belongs to the propagation edge, and only the AP operations of §2.2 change it. The
interpreter sets no layer. A negated mark literal counts as true for a source, a sink and a pass rule. This is the
expected over-approximation of a path-insensitive engine, as the conjunction is (§4.6). Positive literals on different
facts make a conjunction for a source or a pass rule (§4.6), and a vulnerability with a set of facts for a sink. A
cleaner applies only its decided part (§4.7, `interpreter.md` §4.2).

The cases of bidirectional-task.md §1 (checked by `decide` in `Cases.lean`):

| Statement | Input fact | Result | Layer |
|---|---|---|---|
| `a = b.f` | `(b, .f, *, E, *)` | `(a, ., *, E, *)` | normal |
| `a = b.f` | `(b, ., *, E, *)`, `f ∉ E` | `(a, ., [any], {}, *)` | demand (`~`) |
| `a = b.f` | `(b, ., *, {f}, *)` | nothing for `a` | |
| `a = b.f` | `(b, ., [any], {}, *)` | `(a, ., [any], {}, *)` | demand |
| `a = b.f` | `(b, ., $, {}, *)` | nothing for `a` | |
| `a.f = b` | `(b, .g, *, E, *)` | `(a, .f.g, *, E, *)`; under `L = 1`: `(a, .f, [any], {}, *)` | normal; under the cut: demand |
| `a.f = b` | `(a, .f, *, E, *)` | nothing (strong update) | |
| `a.f = b` | `(a, ., *, E, *)` | `(a, ., *, E ∪ {f}, *)`, no request | normal |

The premise of the edge does not change in any case. Only its layer can change, from normal to demand.

### 4.3 Apply a summary edge

`applySummary(a, j, g) = concat(a, j → g, edgeDemand = the layer of the summary edge)` (§4.1; Lean: `applySummary`).
PRECONDITION: the caller fact `a` SATISFIES the premise `j`. The caller tests it before it applies the summary
(§5.3); `applySummary` does not test it again.

* RUN 1: `j` covers `a` (strong enough):

  ```
  applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j.tail = [any] ⇒ a.tail = [any])
  ```

  The application is the case `below`, and the mark gate passes (`applicable_mark`). The abstraction of run 1 covers
  every added fact ((E1), §6.1). Lean: `coversB`, `applicable`, `applicable_sound`; reference form `applicable` (§3.4).
* RESTRICTED RUN: the premise lies INSIDE the fact as LOCATIONS (the location part of `a` covers every location of
  `j`, marks ignored), and the marks of `a` are a subset of the marks of `j` (Lean: `satI`, `RCore.satI_markSub`,
  `satI_conc_record`; reference form `inside`, §3.4). So a concrete fact satisfies a `*` premise, and a cleaned fact
  `*∖X` satisfies a `*` premise. This is the reverse of run 1: the emitted fact is `a ∩ D-c` (§6.3), so it always lies
  inside its added fact (`RCore.emitM_satI`), and it can be smaller than `a` at the same path. The overlap test (`satO`)
  is sound too, but then a precise fact reads the demand-layer summaries of a coarser sibling premise, and a false
  demand vulnerability can survive every run (not modelled).
* A RECORD `j → g` (§8.7) applies to a caller fact `a` when `applicable(j, a)`, in run 1 and in every restricted run.
  The record is exact (R4), so the result adds no false pair.

The mark condition makes the mark gate pass: a summary application never raises a request (`Coverage.summary_step`,
`RCov.sat_step`, `RCore.summary_stepR`). A summary conclusion `*∖X` stops a caller fact whose concrete mark is in `X`
(§4.1 step 5). In a restricted run the CALLEE restricts the summary by its demand patterns before it publishes it
(§6.4). A record is not restricted.

* The exclusion of a summary edge FILTERS the delta: the summary `(arg0, ., *) → (ret, ., */{f})` applied to the bound
  caller fact `(arg0, ., */{})` gives `(ret, ., */{f})` (bound back to the lhs `r`), and applied to
  `(arg0, .f.g, $, T)` gives nothing.
* Run 1 never applies a summary to a fact that only overlaps its premise. Another initial fact of run 1 serves that
  fact.

### 4.4 The field limit

A run has the field limit `L`. After each operation that can make a path longer (the statement transfer, the summary
application), the analyzer applies `limit_L` to the result. It never applies it to a micro edge or a summary edge
before the application:

* If the path has at most `L` counted accessors, the fact does not change.
* Otherwise, cut the path before the `(L+1)`-th counted accessor. Uncounted accessors before that point stay in the
  prefix. The tail becomes `[any]`, the exclusion Empty, the mark stays (also `*∖X`), and the edge goes to the demand
  layer. `L = 0` keeps the empty path.

Lean: `cutPath`, `limitF`; `limitF_sound` (the cut only enlarges). There is no `[any]` depth charge and no fact-depth
gate: the field limit is the only depth bound. Each run may have its own limit (`RCov.iteration_sound`). The bound W3
needs a limit that does not decrease from run to run (§6.6).

### 4.5 Mark gate and mark request (run 1 only)

Some rules need a concrete mark `T`: a sink, a conditional source, a mark-specific pass rule, a literal of a
conjunction, and a cleaner on a partly cleaned fact. Such a rule can meet a fact with the mark `*`, or `*∖X` with
`T ∉ X`. Then the rule gives no fact for `T`. It raises the REQUEST `(m, i, T)` on the premise `i` of the fact, in its
method `m`. A rule that drops the fact without a request loses the flow. A rule that applies anyway lets every mark
through.

A request is always on a premise with an abstract mark (`Coverage.req_initial_star`). In run 1 only the policy (§6.2)
makes such premises. So every request premise of run 1 is a policy fact `(x, [], *, {}, *)`.

A request STANDS for the whole run. The callee `m` checks it against every LINK (added fact `a`, caller edge) of its
added fact store (§8.3) where `a` overlaps `i` (§3.2). It checks the links that exist when the request arrives, and
every link that arrives later. A new caller edge of an existing added fact is a new link too (§5.3, events E2 and E5).
For each link:

* If `a.mark = T`: ANSWER (bidirectional-task.md §4). Emit the initial fact `answer(i, a, T)`:
  * `(i.base, i.path, $, {}, T)` if `a` has the `$` tail and `a.path = i.path`;
  * otherwise `(i.base, i.path, i.kind, T)`: the request premise with the mark `T` (it keeps the exclusion of `i`).

  In run 1 the answer is `(x, [], $, {}, T)` for the added fact `(x, [], $, T)`, and `(x, [], *, {}, T)` for every
  other added fact. The answer starts per §6.5: a `*` tail starts as `[any]` in the demand layer; a `$` tail stays `$`
  in the normal layer. The chain is never deeper than the request.
  Exception: on a static premise (base `S`) an added fact `a` at or below `i` answers with `a` itself and the mark `T`
  (§4.10 item 4).
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
through a new caller edge. If the request checked only new added facts, it would never climb to `A`, and the
vulnerability `main2 → A → m → sink` would be lost.

Requests exist ONLY in run 1. A restricted run is concrete (§6.3): it raises no request and makes no answer
(`RCov.no_reqR`, `RExact.DR_no_request`, `RMain.no_request_M`). The demand pattern already has the mark that a rule
needs.

### 4.6 Mark conjunction: ND edges

A CONJUNCTIVE micro edge `x1.ρ1.t1(T1) ∧ … ∧ xk.ρk.tk(Tk) → z.π.t(T)` gives the mark `T` at `z.π` if every literal holds
at the statement. A literal tail `tj` is `$` (`ContainsMark`) or `[any]` (`ContainsMarkOnAnyField`). The target tail
`t` is `$` or `[any]` (W7). The interpreter makes the edge for a rule with several mark literals (`interpreter.md` §4.2,
§5.3).

* The CONJUNCTION STORE (§8.9) keeps, STANDING for the run, per (rule, statement, literal), each fact `c` at the
  statement that:
  * OVERLAPS the literal pattern `xj.ρj.tj` (§3.2, marks ignored), and
  * passes the mark gate of the literal mark `Tj` (§4.1 step 4, so `c.mark = Tj`).

  It keeps the fact with the premise set of its edge (`{}` for the zero premise, `{i}`, or the ND set). Lean: rule
  `conj` of `ND.DN`.
* If the mark gate gives the request `Tj` (a fact with the mark `*`, or `*∖X` with `Tj ∉ X`), the store keeps nothing
  and raises the request (run 1, §4.5; Lean: rule `reqConj`). In a restricted run every fact is concrete.
* When a fact arrives, the store combines it with the stored facts of the other literals: one fact per literal, every
  combination. The result `z.π.t(T)` has the UNION of the premise sets. Its size decides the edge: 0 gives a
  zero-to-fact edge, 1 a fact-to-fact edge, 2 or more an ND edge.
* The result is in the demand layer if one input is in the demand layer, or if its literal does not COVER it
  (`!coversB lit c`: the input has a location that is not a location of the literal, for example an `[any]` input for a
  `$` literal, or an input above the literal). An `[any]` target puts the result in the demand layer too (W6). Lean:
  `ND.conjLayer`, `ND.Example.c3_normal`. A normal result is exact against the support semantics
  (`NDExact.nd_edge_exact`, S9).
* The engine is path-insensitive: the stored facts are per statement, not per execution path, so the literals can hold
  on paths that exclude each other (`if c then a := srcA else b := srcB; r := f(a, b)`). This is the EXPECTED
  over-approximation; it does not move the result to the demand layer. The reference semantics of a conjunction
  (`ND.TaintN`, below) is path-insensitive in the same way.
* An ND edge propagates through micro edges with its premise set unchanged. Its conclusion is uncorrelated (`$` or
  `[any]`; W7): a `*` tail is the correlation with ONE premise.
* At a call, the callee sees an ordinary added fact. A callee summary `j → g` applied to an ND caller edge keeps the
  premise set of the caller edge. A callee ND summary `{j1, …, jk} → g` needs one caller fact per premise at the call
  statement, each satisfying its `jm` (§4.3). It is standing too: the caller fact that arrives last completes it. The
  result has the union of the premise sets of the caller facts. It is in the demand layer if the summary or one caller
  edge is (`ND.ndBind`).
* An ND edge is never a record: the analysis never persists it and never reverses it. The backward run treats a
  conjunctive edge as an OR of its requirements, which over-approximates the demand.
* The concrete semantics of a conjunction is a SUPPORT semantics: a location is tainted at a node together with the
  list of entry locations that its derivation needs (`ND.TaintN`); a vulnerability witness is a tree.

Lean: `ND.lean` (§10.6).

### 4.7 The cleaner

A cleaner `clean(position, reach, mark)` at a statement removes the mark `T` (or every mark) from the locations of its
position `x.p`. The reach is `exact` (`x.p` only), `below` (everything strictly below `x.p`, the position `x.p.*`) or
`atAndBelow`. (The reach `below` excludes `x.p` itself; the case `below r` of §4.1 includes `r = []`.) Concretely, a
location keeps its value unless the cleaner cleans it (Lean: `Cleaner`, `cleansB`, `Flow.clean`).

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

Lean: `cleanRes`, `addEx`, `concPart`. The model `cleanRes` also raises the request `T` in the first row when `T ∈ X`.
The implementation does not raise it: an answer for `T` only makes facts that an earlier cleaner already cleaned, so the
request costs work and adds nothing.

So the cleaner SPLITS a `*`-mark fact by the mark. The edge `*∖{T}` propagates every mark except `T`, exactly, in the
normal layer. The mark `T` goes through the cleaner only on the concrete answer of the request, which the cleaner cleans
exactly (except on `[any]`, which is in the demand layer anyway). The union of the two covers every real flow
(`Core.cleanRes_sound`, `Coverage.coverage`); a normal result denotes only real flows (`Exact.cleanRes_exact`).

* A summary conclusion `*∖X` stops a caller fact with a concrete mark in `X` (§4.1 step 5). A sink for `T ∈ X` on a
  `*∖X` fact neither triggers nor requests (§4.9). A request for `T ∈ X` does not climb through a `*∖X` fact (§4.5).
* The mark exclusion is not tied to a position, so a field write, a field read or a cut does not change it. (Today's
  `DeepAccessorExclusion` is tied to an abstraction point at a depth; it is lost when the field limit cuts the path.)
* A fact that the cleaner surely cleans (`inside`) needs no request: the `T` path would only make a fact that the
  cleaner drops.
* In a restricted run every fact is concrete (`RExact.DR_concrete`, for any records): only the rows with a concrete mark
  apply, and no `*∖X` fact occurs. A reused run-1 record with a `*∖X` conclusion gives a concrete mark on a concrete
  fact, or nothing (§4.1 step 5).
* The interpreter places the cleaner (`interpreter.md` §5.2): at a call to a cleaner method, on the bound facts before
  they enter the callee, on the facts of an unresolved call before its pass rules, and in the summary rewriter on the
  summary results.
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

The filter checks the concrete path of the fact only. It keeps a `*` or an `[any]` tail whole, as today (an Accept
keeps the whole subtree). The analysis does not store a filter in a fact or an edge, and it does not propagate a
filter to later statements. So a `*` or `[any]` fact that passes a filter can still denote locations below its path
that the filter rejects (`Exact.CexFilt`). Those locations do not exist on a real value. On the JVM this is an expected
false-positive source (§11.1).

So the exactness theorem holds for VALID locations only: the end locations that every filter accepts
(`Exact.edge_exact_valid`, `closed_exact_valid`, `Closed.closed_records_exact_valid`). The validity predicate must also
go back along the micro edges (`Exact.BackOK`): a valid end location of a micro edge comes from a valid start location.
A confirmation (§4.9) needs a sink pattern whose locations are valid (`Confirmed.confirmed_real_valid`;
`Confirmed.CexConfFilt` shows that the condition is necessary).

The interpreter places the filters (`interpreter.md` §5.1 gives the table). The mark policy (a concrete mark on a
primitive value) is NOT a type filter: it reads the mark, the model has no mark filter, and it can drop a real flow, so
it is outside S5 (`interpreter.md` G6). The AP has no summary-side filter (today: the caller content under a callee
`*`, and the exit compatibility filter). Without a filter the analysis only adds facts, so this is sound and costs
precision (`interpreter.md` D13, D14, Q3). The backward run does not type-filter.

### 4.9 Sink check and confirmation

A sink checks the pattern `s = (v, ρ, t, T)` with the tail `t = $` (`ContainsMark`) or `t = [any]`
(`ContainsMarkOnAnyField`). For an edge `(i, layer) → f`:

* If `f` and `s` do not overlap (§3.2, marks ignored): no effect.
* If `f.mark = *∖X` with `T ∈ X`: no effect (the mark was cleaned).
* If `f.mark = T'`: the sink is TRIGGERED if `T' = T`; otherwise no effect.
* If `f.mark` is `*`, or `*∖X` with `T ∉ X`: raise the REQUEST `(m, i, T)` (run 1). Here `i.mark` is abstract too: a
  concrete premise has only concrete conclusions (`Coverage.edge_conc`). The implementation asserts it. (The model
  `check` reads the effective mark (§1), so it also triggers for an abstract `f.mark` under a concrete `i.mark`; this
  case does not occur.)

This covers bidirectional-task.md §2: `(x,.,$,T)` triggers, `(x,.f,$,T)` does not, `(x,.,[any],T)` triggers,
`(x,.,*,{},*)` raises the request `T`. Lean: `check`, `check_sound`, `check_request_star`.

A triggered vulnerability is CONFIRMED only if all three conditions hold:

1. The sink edge is a normal edge.
2. Each premise of the sink edge (one premise, or the premise set of an ND edge, §4.6) is the zero fact or an EXACT
   concrete fact `(x, p, $, T)`: a request answer in run 1, an emitted fact in a restricted run.
3. Each premise is SUPPORTED (Lean: `Sup` in run 1, `SupM` in a restricted run):
   1. The zero fact of a root is supported.
   2. A premise `j` of a callee is supported if a normal caller edge `(i, normal) → c` whose premises are all
      supported reaches a call to the callee, the binding of `c` gives the normal
      added fact `a`, and `j = a` (the same base, path, tail and mark). So `j` and `a` are the zero fact, or `a` is
      exact with a concrete mark: `j` is the answer of `a` in run 1, or the emission `a ∩ D-c = a` in a restricted
      run.
   3. No other premise is supported.

   The weaker condition "the premise is exact" is not enough (`Confirmed.weak_support_gap`, a proved counter-example).
A sink with a set of facts (`interpreter.md` §4.2) is confirmed if the sink edge of each fact is confirmed. A
conjunction is the expected over-approximation of a path-insensitive engine (§4.6), so a vulnerability through a normal
conjunction result can be confirmed: it is real for the path-insensitive support semantics `ND.TaintN`. Lean:
`Confirmed.confirmed_real` and `RMain.confirmed_real_M` for programs without conjunctions; with conjunctions the
exactness of the normal layer is proved (`NDExact.nd_edge_exact`), and the confirmation is argued from it (§11.2).

The analyzer computes the support and the confirmation at the fixed point of the run (S6), after the last event:
condition 3 is a least fixed point over the caller edges, and it can change until the run ends.

Every other triggered vulnerability is a DEMAND vulnerability. In particular, every result of an `[any]`-target source
is in the demand layer (W6). So a vulnerability whose taint comes only from such a source is never confirmed: it stays
a demand vulnerability in every run.

`Confirmed.confirmed_real_valid` (run 1) and `RMain.confirmed_real_M_valid` (every restricted run; support `SupM`; the
satisfaction `satI`) prove that a confirmed vulnerability is real for the reference semantics of S1–S9, for a sink
pattern whose locations are valid (§4.8). The forms without the validity condition (`confirmed_real`,
`confirmed_real_M`) are for programs without type filters (`FiltUp`). On the real program, a confirmed vulnerability
is real modulo the expected false-positive sources of §11.1.

### 4.10 Statics in run 1: the position request

The static base `S` holds every static field at the path `[<C>, f]`: the class accessor `<C>` (not counted by the field
limit) and the field `f`. A rule can also put a concrete mark on a class position `[<C>]` with no field, for example
`(S, <C>, $, {}, T)`. The run-1 static fact is abstract: the root `(S, ., *, E, *)`. An operation whose premise is
below an abstract static fact is the case `above` of §4.1, and the ordinary result is `[any]` in the demand layer. In
run 1 the static base uses a POSITION REQUEST instead. So no static fact with the `[any]` tail occurs above a static
position (`Statics.no_any_above`).

1. RAISE. A propagation edge from a static `*` premise `(S, q, *, E0, *)` to the static `*` fact at the same path
   `(S, q, */E, m)` (an abstract mark `m`, normal layer; `q` is the root or a class position) meets a static operation
   strictly below `q`, at the position `p = q ++ r` with `r ≠ []` and `E` admitting `r`:
   * a READ micro edge `S.p.* → x.*` (`x = C.f`, `p = [<C>, f]`);
   * the class KEEP edge of a WRITE `S.<C>.* →_{f} S.<C>.*` (`C.f = v`, `p = [<C>]`). The root keep edge
     `S.* →_{<C>} S.*` is at the root: it updates the exclusion, as on the main branch;
   * a SINK pattern on `S` (instead of the mark request; the mark request then comes on the answer).
   The operation gives NO fact and raises the position request `(m, i, p)` on the premise `i`.
2. ANSWER. The request stands for the run. An added fact of `m` at or below `p` answers it: the answer is the initial
   fact `(S, p, *, {}, *)` of `m`, with the identity start edge. Callers read its summaries as usual (§4.3).
3. CLIMB. For every caller edge whose premise is on `S` and whose added fact overlaps `(S, p)` and is above `p`, raise
   the request `(caller, ic, p)`. The first caller that has an added fact at or below `p` answers, and the precise fact
   goes down the calls.
4. MARK ANSWER ON A STATIC PREMISE. A mark request (§4.5) on a static premise `i` is answered by an added fact `a` at or
   below `i` with `a` itself and the requested mark: `(a.base, a.path, a.tail, T)`, not the request chain. (The chain
   of the root is `[]`, and `(S, ., *, T)` would start as `(S, ., [any], T)`: a cleaner on the static root then turns a
   precise caller fact into it, `Statics.CexClean`.)

Construction rules (`Statics.SWF`), all true for the interpreter: a static micro edge from `S` to `S` is an identity
restriction (the keep edges of a write); a micro edge into `S` that lands above a static position has a `$` target and
a concrete premise mark (a mark on a class position); no rule makes an `[any]` fact on a bare class; calls bind `S`
only through `S.* → S.*`; the field limit of run 1 is at least 1, so a cut never stops at `[<C>]`; a cleaner on `S`
names its mark.

AFTER RUN 1 NO STATIC RULE IS NEEDED. A restricted run (forward or backward) has no position request, no mark request
and no other static rule: the demand alone handles the statics. Under the construction rules no static fact of a
restricted run with a `*` or `[any]` tail lies above a static position, for EVERY demand (`StaticsIter.rinv_all`,
`no_any_above_R`): the emission gives the added fact, its meet at the same path, or the demand pattern below it; the
restriction only moves a conclusion down; and a fact above a position is exact. So every static read, write keep edge
and sink of a restricted run is the case at or below of §4.1 (`StaticsIter.static_step_below`, `static_sink_below`),
no `[any]` comes from a static operation, and the run raises no request (`StaticsIter.no_request`). The iteration that
starts from run 1 with this rule and continues with the plain restricted runs reports every real vulnerability in every
forward run (`StaticsIter.iteration_general_DS`, with the first link `reach_strongDSD`), and every later run satisfies
the invariant (`StaticsIter.no_static_rule_after_run1`). The worked programs are confirmed through normal edges in
forward run 3 with no request (`ExampleIter`, `WideIter`, `AboveIter`, `CleanIter`: `run3_vuln_normal`,
`run3_confirmed`).

Lean: `Statics.lean`, the run-1 closure `DS` (as `ND.lean`), with the rules `sreqStmt`, `sanswer`, `sreqUp` and the
answer `SCtx.ansInit`; the final rule is `Statics.Design`. Soundness: `Statics.vulnD` (`coverageD`). Exactness:
`Statics.edge_exactS`, `edge_exact_validS`. The invariant: `Statics.no_any_above`, `cinv_all`. The effect:
`Statics.gen_read_DS` (no fact on `x`), `gen_read_sreq` (the request). The worked programs are found through normal
edges: `CexAbove.y_vuln_normal` (a write in the caller), `CexWide.w_vuln_normal` (a write in a callee),
`CexClean.deep_vuln_normal` (a cleaner in a callee). `CexClean.shallow_misses`: with the chain answer of item 4 the
vulnerability is lost.

---

## 5. Calls and ownership

### 5.1 Concrete semantics (the model)

A call `r = m(a1..an)` has: the touched caller bases (the arguments, the result, the static base), the binding edges
into the callee (`ai.* → argi.*`, `S.* → S.*`, `zero.* → zero.*`), and the binding edges back (`argi.* → ai.*`,
`return.* → r.*`, `S.* → S.*`). A caller location on an untouched base passes over the call. A location on a touched
base goes into the callee and comes back through the callee flow. The zero base is never touched: the zero fact passes
over every call and also enters the callee by its binding. The zero binding is `zero.* → zero.*`: the zero fact is below
its premise. (The form `zero.$ → zero.$` is not a `*`-to-`*` binding, so it is not well formed.) Lean: `Call`,
`Flow.pass`, `Flow.call`.
The interpreter gives the bindings of each call kind (`interpreter.md` §3).

### 5.2 Who owns what

| Side | Owns | Does |
|---|---|---|
| CALLER (the method that contains the call) | the subscriptions: (caller edge, call statement, added fact) | binds each caller fact into the callee (micro edges); applies every published summary edge of the callee whose premise its added fact satisfies, and every record whose premise covers it (§4.3); binds back; applies the field limit |
| CALLEE (the called method) | the added facts (with the caller edges that made each added fact), the demand patterns of the method, the emission, its initial facts, its edges and summaries, its requests (run 1) | emits the initial facts for each added fact (§6); analyses them; restricts each new summary edge by its demand patterns (restricted runs, §6.4) and then PUBLISHES it to the subscribers; answers and propagates its requests (§4.5) |

### 5.3 Call processing

The interpreter gives the order of the steps at a call (`interpreter.md` §4.5):

1. RELEVANCE. If `c.base` is not touched, the caller edge `(i, layer) → c` passes over the call (call-to-return).
2. BIND. For each binding edge `e` into the callee: the bound fact `b = concat(c, e)` (a micro edge, §4.2).
3. The sinks and the sources of the call read `b`. The cleaners of the call clean `b`. Each cleaned result `a` is an
   ADDED FACT of the callee (§1).
4. The CALLEE PROCESSING below, for the link (`a`, caller edge), in each resolved callee.
5. RETURN. The caller binds each summary result back (micro edges), applies the summary rewriter and the aliases
   (`interpreter.md` §4.5 step 6), and applies the field limit (§4.4).

The callee processing is a set of STANDING rules. Each event triggers its actions; the actions can make new events.
The order of the events does not change the fixed point (S6). An implementation can process them in any order.

| # | Event | Actions |
|---|---|---|
| E1 | A new added fact `a` of the callee | The callee adds `a` to its added fact store (§8.3). It EMITS the initial facts for `a` (§6): in run 1 the most abstract fact, in a restricted run the emission `a ∩ D-c` for each demand pattern of the callee. Each new initial fact is event E3. |
| E2 | A new link (added fact `a`, caller edge), also a new caller edge of an existing added fact | The callee stores the caller edge with `a` (§8.3). It checks every standing request that overlaps `a`, and answers it or propagates it through THIS caller edge (§4.5). The caller SUBSCRIBES `(caller edge, call statement, a)` (§8.4). It applies every published summary edge of every initial fact that `a` satisfies (§4.3), and every record whose premise covers `a` (§8.7). |
| E3 | A new initial fact `j` of the callee (an emission or an answer) | The callee analyses `j` from its start fact (§6.5). (The interpreter filters the start fact by the context type, `interpreter.md` §4.3.) Each summary edge of `j` is event E4. |
| E4 | A new summary delta `j → g` of the callee | In a restricted run the callee restricts it by each demand pattern of the callee (§6.4). It PUBLISHES each result. For each subscription whose added fact satisfies `j`, the caller applies the result (§4.3), then step 5. |
| E5 | A new request `(m, i, T)` in the callee `m` (run 1) | The callee stores it (§8.8). For each added fact `a` of `m` that overlaps `i`, and each caller edge of `a`: answer or propagate, as in E2 (§4.5). |
| E6 | A new caller fact for one premise of a callee ND summary at the call statement, or a new ND summary | The caller combines it with the stored caller facts of the other premises of that summary (§4.6, §8.9). A full combination (one caller fact per premise) applies the ND summary. |

The result of a summary application is in the demand layer if the caller edge or the summary edge is, or if the
application itself moves it there (§4.1).

---

## 6. Runs and abstraction

### 6.1 Contracts

The abstraction selects the initial facts for an added fact `a` of method `m`. It is a function of `m`, `a` and
constants of the run (the field limit, the demand). It must not depend on the order of events.

```
(E1)  run 1:            applicable(α(m, a), a)
(E2)  restricted run:   for every demand pattern d of m, every CONCRETE added fact a and every location l (with its
                        mark) that D-c and a both cover, the emission emit(D-c, a) gives an initial fact j that
                        covers l, and a satisfies j
(E3)  restricted run:   the emitted fact has the mark of the added fact
```

The coverage theorem of run 1 needs only (E1). The coverage theorem of a restricted run needs (E2) for the added facts
of the run (`EmitContractOn`), the satisfaction contract (§4.3) and the restriction contract (§6.4). (E3) makes every
added fact of a restricted run concrete (`RCov.concInvR_all`, `RExact.DR_concrete`), so (E2) covers all of them
(`RCov.emitOn_of_conc`).

### 6.2 Run 1

The run-1 abstraction gives:

* for the zero fact: the zero fact;
* for every other added fact `a`: the most abstract fact `(a.base, [], *, {}, *)`.

Lean: `policy1`, `policy_applicable` (E1). The caller gets the marks back through the summary application: a `*`-mark
premise passes the mark of the caller fact through. A sink, a mark-specific rule or a cleaner inside the callee gets the
mark through a request (§4.5). Run 1 is the ONLY run with requests.

### 6.3 Restricted run: the emission

For the added fact `a` of method `m`, for each demand pattern of `m` with the entry pattern `D-c = (b, p, t, M)`, emit
`a ∩ D-c`: the part of `a` that `D-c` covers, with the mark of `a`. The mark `M` of the entry pattern is `*` or `T`,
never `*∖X`. A concrete `M` is a demand for that mark.

| `D-c` mark | `a` mark | result |
|---|---|---|
| `T` | `T` | emit |
| `T` | `T' ≠ T` | nothing |
| `T` | `*` or `*∖X` | nothing; it never occurs (no abstract fact in a restricted run) |
| `*` | any | emit, with the mark of `a` |

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
* (E2) holds for concrete added facts (`RCore.emitM_contract_I`); it fails for a `*`-mark added fact under a `T` demand
  (`emitM_not_full_any`, for every satisfaction), and a restricted run has no such fact.
* NO REQUEST. The root starts from the zero fact, every emitted fact copies a concrete mark, a concrete-mark premise has
  only concrete-mark conclusions, and a `*`-premise record applied to a concrete fact gives a concrete result. So every
  fact of a restricted run has a concrete mark, no final fact has the `*` tail (`RExact.final_not_star`), and no request
  rule can fire (`RExact.DR_no_request`). Condition: the only callee summaries with a `*` premise in a restricted run are
  persisted run-1 records and, in a backward run, their reversals (§9.1). The interpreter makes no precomputed
  `*`-premise summary (`interpreter.md` I8, §3.7).
* The zero fact. A demand that covers the zero location with the zero mark emits the zero fact itself.
* Precision. An exact added fact gives an exact concrete initial fact; its edges are in the normal layer, and a
  vulnerability under it can be confirmed (§4.9). A fact cut to `[any]` gives an `[any]` premise in the demand layer.
* Cost. There is NO SHARING: one initial fact per distinct added fact (path, tail, mark). The demand bounds which
  methods the run analyses and the chain prefix, but NOT the number of contexts below an `[any]` demand chain; the spec
  sets no cap. Nothing below a forward field-limit cut can be confirmed until a later forward run has a larger limit;
  the driver must grow the forward limit as well as the backward one (§6.6).

Programs 1 and 2 (`RestrictedCases.lean`) are two programs where an emission that ignores the marks loses a real flow.
With this emission, run 3 (forward) reports both vulnerabilities (`RCases.p1_found_M`, `p2_found_M`). Program 1:

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
    check(d.fact.mark !is MarkSlot.Star || d.fact.mark.excluded == MarkSet.EMPTY)   // never *∖X
    if (d.fact.base != a.fact.base) return null
    if (d.fact.mark is MarkSlot.Concrete && d.fact.mark != a.fact.mark) return null  // a T demand needs the mark T
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

The CALLEE restricts each summary edge `S = (S-p → S-c)` by each of its demand patterns `d` (entry pattern `D-c`, exit
pattern `D-p`) BEFORE it publishes the result `R = (R-p → R-c)` to the subscribers. Lean: `restrictU` (`restrictWith`,
`restrictConcU`).

* No `D-p` (the demand does not reach the method exit): no result.
* `R-p := S-p` if `S-p` and `D-c` overlap (§3.2, marks ignored); else no result. (`S-p` is one path, so the
  intersection is all of `S-p` or nothing.)
* `R-c` follows the position of `S-c` against `D-p`:

| `S-c` against `D-p` | `S-c` tail | `R-c` |
|---|---|---|
| at or below (`S-c.path = D-p.path ++ r`), the tail of `D-p` admits `r` | any | `S-c` |
| at or below, the tail of `D-p` does not admit `r` | any | no result |
| above (`D-p.path = S-c.path ++ r`) | `[any]` | `(D-p.path, [any])`, or `(D-p.path, $)` if `D-p` has the `$` tail |
| above | `*/E` | no result; it never occurs in a restricted run (no `*` final tail) |
| above | `$` | no result |
| apart, or another base | | no result |

* The restriction filters by the chain of `S-c`. It is not an intersection with `D-p`: at or below `D-p` it keeps the
  whole `S-c`, also the locations of `S-c` that `D-p` does not cover (example: `S-c = (y, ., [any])` against
  `D-p = (y, ., $)` gives `S-c`). It only removes whole pairs (`RCore.restrictU_sub`).
* One summary edge can have results for several demand patterns. The subscribers get every result (the union).
* `R` has the layer and the mark of `S`.
* In a concrete run this restriction gives the same run as the restriction `restrictS`, which keeps a `*` conclusion
  above `D-p`, and the contract of `restrictS` holds (`RExact.restrict_U_eq_S`, `RCore.restrictS_contract`). So the
  restriction contract of §10.7 holds for the run.

Reference form (types and tests of §3.4):

```kotlin
/** §6.4. Restrict the summary conclusion `sc` of the premise `sp` by the demand pattern `d` (in the callee). */
fun restrict(sp: Pattern, sc: Conclusion, d: DemandPattern): Conclusion? {
    val dp = d.exit ?: return null                           // the demand does not reach the exit
    if (!overlap(sp, d.entry)) return null                   // R-p: all of S-p or nothing
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
| `(x, p, */E, T)` | `(x, p, [any], {}, T)` (W2) | demand: the `~` premise |
| `(x, p, [any], m)` | `(x, p, [any], {}, m)` | demand |
| `(x, p, $, m)` | `(x, p, $, {}, m)` | normal |

A premise never has the mark `*∖X` (§2.2). Lean: `startFact`, `startFact_sound`.

### 6.6 The run sequence

* The analysis ALTERNATES forward and backward runs: run 1 (forward), run 2 (backward), run 3 (forward), and so on. The
  field limit INCREASES from run to run (W3 needs at least that it does not decrease). A forward run with no demand
  vulnerability (§4.9) stops the iteration: every vulnerability that it reports is confirmed. The iteration driver, its
  termination and its budget are out of scope of this spec: the fact domain grows with the field limit, so the
  iteration does not stop by itself.
* Run 1 is `D` with `policy1`. Each later run is `DR` with the demand that the run before it gives (§8.6), its own field
  limit and the persisted records (§8.7). Lean `RCov.runSeq` numbers only the forward runs: `runSeq k` is run `2k + 1`,
  and the demand `dem k` comes from the backward run `2k + 2`.
* The backward run `n + 1` between the forward runs `n` and `n + 2` satisfies the contract B (§9.2, §10.7): every
  witness of a vulnerability that forward run `n` reported stays demanded (`Backward.B_general`).
* Every forward run reports every real vulnerability (`RMain.iteration_sound_M`). So the analysis can stop at any
  forward run. The report is in §8.10.

---

## 7. Representation (the optimization)

The concept of a conclusion is a set of path facts. The representation groups path edges into TREES.

### 7.1 Initial fact

```kotlin
/** The initial fact (premise): one linear path. Its mark is * or a concrete mark (never *∖X). */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,           // interned, linked from the root; no [any], $ or mark accessors (W4, W5)
    val tail: Tail,
    val exclusion: ExclusionSet,   // Empty in run 1; a restricted run can emit the exclusion of a `*/E` demand
    val mark: MarkSlot,
) {
    fun toPattern(): Pattern       // the list form of §3.4, for the reference forms
}

/** The premise of an analysis context: a CANONICAL set of initial facts (sorted by the intern id, no duplicates).
 *  Empty: the zero fact. One element: a fact-to-fact edge. Two or more: an ND edge (§4.6). The layer is not part of
 *  the premise key; every store key that needs the layer has it as a separate part. */
data class PremiseKey(val initials: List<InitialAp>)
```

`PathNode` is the current `AccessPath.AccessNode` without the `[any]`, `$` and mark accessors.

### 7.2 Conclusion trees

One tree per (premise key, layer, exclusion, mark exclusion). The exclusion and the mark exclusion belong to the tree; a
`*` leaf is a flag.

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
  exclusion or a mark exclusion of a stored tree, the delta is the WHOLE merged tree with the new exclusion. A change of
* T5. Inside one demand-layer tree, an `[any]` leaf with the mark `m` at `p` may absorb every leaf with the mark `m`
  below `p`. The denotation does not change. A normal tree has no `[any]` leaf (W6).
* T6. Share one empty payload; intern payloads, mark sets and exclusion sets.

### 7.3 Delta-concat on a tree

The computation of §4.1 on all paths of one tree at once. `Ec` is the tree exclusion. The results are grouped by their
new (layer, exclusion, mark exclusion):

1. Walk `from.path` from the root. On each proper prefix node, read its payload as the case `above` (`r` is the rest
   of `from.path` after the node):
   * a `*` leaf gives a result only if `Ec` admits `r` (Lean: `Tree.cS`);
   * an `[any]` leaf always gives a result;
   * a `$` leaf gives nothing (no overlap).

   Each result is `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer. Apply the mark gate to each leaf
   mark (step 4). Lean: `Tree.contribB`.
2. At the node of `from.path` take the subtree `S`. Filter its root by the premise tail and the edge exclusion.
3. Transform `S` by the target tail:
   * a `*` target: the child subtrees (`r ≠ []`) keep the tree exclusion and are re-rooted under `to.path`; the root
     `*` leaf (`r = []`) gets the exclusion `Ec ∪ E`, so it goes to another tree;
   * an `[any]` target: fold `S` into one `[any]` payload with the Empty exclusion, in the demand layer (W6);
   * a `$` target: fold `S` into one `$` payload with the Empty exclusion. It is in the demand layer if `S` has a `*`
     leaf and its exclusion is not Empty (`lostCorr`: `Ec ∪ E` for the root leaf of `S`, `Ec` for a leaf below it).
4. Apply the mark gate per payload mark, then the target mark (§4.1 steps 4, 5; a `*∖X` target adds `X` to the mark
   exclusion and stops the concrete marks in `X`).
5. Apply the field limit with `boundedDepth`; cut paths go to the demand-layer tree.
6. Route each result by its own layer bit.

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `S` only. The concept form visits every path
fact (`Tree.lean`: `applyTreeE_mem`, `applyTreeE_den`, `walkSteps_le`).

### 7.4 The restriction on a tree

The restriction of §6.4 applies to all conclusions of one summary tree at once (`RStore.restrictTree`):

1. Walk `D-p.path` from the root. On each proper prefix node: drop the `*` flag (§6.4; a restricted run has no `*`
   leaf); move the `[any]` marks to `D-p.path` (as `$` for a `$` exit pattern); drop the `$` marks and every child off
   the chain.
2. At the node of `D-p.path`, keep the payload, add the moved marks, and keep each child whose accessor the tail of
   `D-p` admits (all children for `[any]`, none for `$`).

The result is one well-formed tree (`RStore.restrictTreeE_inv`); the tree form equals the per-path restriction
(`restrictTreeE_mem_U`); cost `|D-p.path| + 1 + width` new cells, kept subtrees shared (`restrictTree_cost`).

### 7.5 Interning

Tries are hash-consed bottom-up as today; an identity cache memoises the walk of §7.3. `boundedDepth` is part of the
node, not of the hash.

### 7.6 Relation to the current code

The phase-3 prescan still runs the current core. So the new AP lives beside the current types.

| Part | Decision |
|---|---|
| `AccessPath.AccessNode`, accessor interning, `AccessorIdx` | Reuse. |
| `AccessTree` merge, `mergeAddDelta`, interners, identity caches | Reuse the algorithms for `FactNode`. |
| `AccessBasedStorage` trie | Reuse for the path indexes of §8. |
| `EdgeStorage`, `AccessPathBaseStorage`, exact-key subscription maps | Reuse with the new fact types. |
| `StatementSummaryBuilder`, `buildReversed` | Adapt (`interpreter.md`). |
| `InitialFactAp`, `FinalFactAp`, `ApManager` | New types `InitialAp`, `EdgeTree`. They do not implement the old interfaces. |
| `Edge` (`ZeroToFact` requires Universe) | New edge classes with the layer: `Zero → (layer, statement, fact)`, `(premise key, layer) → (statement, fact)`. |
| `NDFactToFact` | An edge whose premise key has two or more premises (§4.6). |
| `DeepAccessorExclusion` | Replaced by the mark exclusion `*∖X` of the edge (§4.7). |
| `FactReader` (mark as accessor suffix) | New reader over `(path, tail, mark)`: `check` (§4.9). |
| `FactTypeChecker` | The type filter primitive (§4.8). |
| `EdgeNonUniverseExclusionMergingStorage` (union merge) | Replace by merge rules 1 and 2. |
| `TaintSinkTracker` (rule assumptions), vulnerability records | The standing conjunction store (§8.9); the vulnerability record of §8.10. |
| `TreeInitialFactAbstraction` | Replace by §6.2 (run 1) and §6.3 (restricted runs). |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used (§4.4). |

---

## 8. Storages

Every store has a CONCEPT (a list of entries with a filter) and an INDEX. `Store.lean` and `RestrictedStore.lean` prove
that each index returns every entry that the filter returns, and give the cost of the lookup. The OWNER of each store
is the method that §5.2 names. Lifetimes:

* RUN: one run (one direction, one field limit).
* HAND-OFF: from the end of one run until the next run has read it. This is what one run passes to the next: the
  summary edges (§8.5) and the reported vulnerabilities (§8.10). The next run reads them as its demand (§8.6) or as its
  seeds (§9.2).
* PERSISTENT: all runs of one analysis.

The method key of a method is the same in every run (§1), so a key that contains it stays valid across runs.

### 8.1 Method edge store (RUN, per method)

* Key: `(statement, premise key, layer, base, exclusion, mark exclusion)`. Value: an `EdgeTree`.
* `add(...)` merges by rule 1 or 2 and returns the delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer: the store drops a conclusion if a stored conclusion of the same premise key and layer
  subsumes it (`Subsume.subsumesB`): the same base; the same mark, or a mark exclusion that is a subset; `[any]` at `p`
  subsumes every fact at or below `p`; `*/Es` subsumes `*/En` at the same path if `Es ⊆ En`. `subsumes_sound` proves
  that every pair of the dropped fact is a pair of the stored fact.
* A demand-layer conclusion never subsumes a normal one (`Subsume.recordSubsumesLB_layer` for records).
* Unchanged propagation (`Sequent.Unchanged`) may skip the store, as today.
* Queries for the trace resolution (phase 5): `edgesAt(stmt, premise?)`, `edgesAt(stmt, pattern)`. The store of the
  last forward run stays until the trace resolution ends.

### 8.2 Initial fact store (RUN, per method; callee)

* `initials: Map<InitialAp, Flags>`, with the flag `supported` (§4.9; computed at the fixed point of the run).

### 8.3 Added fact store (RUN, per method; callee)

* A path trie keyed by `base :: path`. Each added fact keeps the set of its caller edges
  `(caller method, caller premise key, layer, call statement)`. One (added fact, caller edge) pair is a LINK.
* A new link is event E2 of §5.3, also when the added fact exists already. The store gives the request store (§8.8)
  every new link.
* The standing request match (§4.5) reads the store with OVERLAP queries: `lookupPrefixes ++ lookupExtensions` of the
  path of the request premise.

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

* Key: `(premise key, layer)`. Value: the exit `EdgeTree`s. (Only the normal exit makes a summary edge,
  `interpreter.md` §3.4.)
* In a restricted run the callee restricts each new summary edge by every demand pattern of the method (§6.4). It
  PUBLISHES the results to the subscription store.
* At the end of the run, the store adds every normal summary edge to the persistent record store (§8.7).
* The summary edges are the input of the next run in the other direction (§8.6, §9.2).

### 8.6 Demand store (RUN, read only; callee)

* Content: `MethodKey → List<DemandPattern>`: the demand patterns of each method, in the orientation of this run (the
  entry pattern `D-c` and the exit pattern `D-p` or none). The driver fills the store at the start of the run from the
  hand-off of the run before (§8.5). For a forward run `n + 2` the backward run `n + 1` gives them: the edges of run
  `n + 1` on the paths from its seeds (the vulnerabilities of forward run `n`): demand-layer edges, reversed records and
  the zero edges (§9.2, contract B). The demand of a backward run comes from the forward run before it (§9.2).
* Index: a path trie keyed by `base :: D-c.path`.
* The query `near(q)`: the prefix walk of `q`, then the subtree strictly below the node of `q`. It returns the same
  entries as the list filter "the chain is not apart from `q`" (`RStore.near_equiv`, `near_sound`).
* Emission query (§6.3), for the added fact `a`: `near(a.path)`. It returns every demand pattern for which the emission
  gives a fact (`RStore.emit_complete_M`, `emit_lookup_equiv_M`). For a `$` added fact the prefix walk alone is enough
  (`emitM_exact_prefix`).
* Restriction query (§6.4), for the summary premise `j`: `near(j.path)` (`restrict_complete_U`,
  `restrict_lookup_equiv_U`).
* Cost (`near_query_cost`): at most `|q| + 1` nodes for the walk, plus `Σ |rel|` over the returned chains strictly below
  `q`, against `|demand patterns|` tests in the list form. The bound "walk + number of results" is FALSE for the plain
  trie (`deep_chain_cost`); a path-compressed (radix) trie gives it.

### 8.7 Persistent record store (PERSISTENT)

One direction-neutral store for the forward and the backward analysis:

```kotlin
/** A record: a normal summary edge, in the orientation in which it was derived. */
class Record(
    val method: MethodKey,
    val direction: Direction,          // FORWARD: premise = entry fact; BACKWARD: premise = exit fact
    val premise: InitialAp,
    val conclusion: EdgeTree,          // normal layer; may carry a mark exclusion
)

interface RecordStore {
    fun add(record: Record)
    fun byEntry(method: MethodKey, callerFact: Pattern): Sequence<Record>     // the added fact of the caller
    fun byExit(method: MethodKey, requirement: Pattern): Sequence<Record>     // a requirement at the exit
}
```

Rules:

* R1. Only normal summary edges are added. ND edges are never added.
* R2. `byEntry` is a path trie keyed by `base :: premise path`. The lookup is `lookupPrefixes(base :: q)` for the
  caller fact at `q`, and then the `applicable` filter, in every run (`forward_equiv_prefixes`,
  `applicable_mem_candidatesB`, `extension_half_redundant`). `byExit` is a path trie keyed by `base :: leaf path` for
  EACH leaf path of the conclusion tree.
* R3. A reader in the other direction applies the reversal of §9.1. Every record whose premise has the Empty exclusion
  and that is mark-reversible reverses exactly (`Reverse.rev_exact_of_empty_premise`). A reversed backward record has
  no type filter (the backward run does not type-filter): an expected false-positive source (§11.1).
* R4. A record applies to a caller fact when its premise covers the fact (`applicable`, §4.3), in run 1 and in every
  restricted run IN THE SAME DIRECTION. This is always sound: a normal edge of run 1 or of a restricted run is exact
  (`Exact.edge_exact_valid`, `RExact.recs_of_DR_valid`, `recs_of_D_valid`; for programs without type filters
  `Exact.edge_exact`, `recs_of_DR`, `recs_of_D`), so it adds no false pair. A conjunction result with fewer than two
  premises can be a record; its exactness is `NDExact.nd_edge_exact`. The exactness holds for the reference semantics
  of S1–S9, modulo the expected false-positive sources (§11.1). Lean: rule `retRec` (`sat` or `applicable`), `RCases.p3_reuse`, `RMain.p3_reuse_exact`.
* R5. Strict demand: after run 1 the abstraction reads only the demand (§6.3). It emits the demanded facts and
  checks nothing else; a record never causes an emission and never replaces one. The records only add edges (R4).

### 8.8 Request store (RUN 1 only, per method; callee)

* Entries: `(method, initial fact, mark)` for a mark request (§4.5) and `(method, initial fact, position)` for a
  position request (§4.10), plus the answers already emitted. A request stands for the whole run.
* Index: a path trie keyed by `method :: base :: path` of the request initial fact.
* On every new link (added fact, caller edge) of the method (§8.3), find ALL standing requests that overlap the added
  fact (`standing_complete`). Answer each one, or propagate it through THIS caller edge (§4.5, §5.3 event E2).
* On a new request, read every existing link of the added fact store whose added fact overlaps it (§5.3 event E5).

### 8.9 Conjunction store (RUN, per method)

* Entries: `(rule, statement, literal) → set of (fact, premise key, layer)`: the facts that overlap a literal of a
  conjunctive micro edge and pass its mark gate (§4.6), standing for the run (today's `TaintSinkTracker` assumptions).
* On a new fact for a literal: combine it with the stored facts of the other literals (one per literal, every
  combination); the results have the union of the premise keys.
* The same for ND summaries at a call statement: `(callee summary, premise index) → caller facts`.

### 8.10 Vulnerability store and the report (PERSISTENT)

A reported vulnerability (Kotlin: `VulnerabilityRecord`) has these fields:

| Field | Content |
|---|---|
| rule | The sink rule. |
| method, statement | The method key and the sink statement. |
| pattern | The sink pattern `s` (§4.9). |
| premise key, facts | The premise key of the sink edge and its sink fact; for a sink with a set of facts (`interpreter.md` §4.2), the set. The trace resolution starts from them. |
| state | CONFIRMED or DEMAND (§4.9). A vulnerability with a set of facts is CONFIRMED only if each fact is. |
| run | The run that reported it. |

* Key: `(rule, method key, statement)`. The same key in two runs is the same vulnerability.
* A CONFIRMED vulnerability persists. It is real for the reference semantics of S1–S9, modulo the expected
  false-positive sources of §11.1.
* Every FORWARD run reports every real vulnerability (§6.6). A demand vulnerability of forward run `n` that forward run
  `n + 2` does not report (no vulnerability with the same key) is REFUTED: under B it is not real.
* The REPORT of the analysis is every vulnerability that a run confirmed, and every demand vulnerability of the last
  forward run. A vulnerability has the state CONFIRMED in the report if some run confirmed it.
* The vulnerabilities of a forward run are also its HAND-OFF: the next backward run reads them as its seeds (§9.2). The
  vulnerabilities of a backward run only make the demand of the next run; they are not in the report.

---

## 9. Reversal and the backward direction

### 9.1 Reversal of a record

The reversal `rev(i, f)` (Lean: `revEdge`, `revKinds`) reads a record from the other side. The new premise is the old
conclusion; the exclusion goes to the NEW CONCLUSION, so the new premise has the Empty exclusion. The last column says
whether a record can have the row. Only two rows occur, because:

* an `[any]` premise starts in the demand layer (§6.5), so it has no record;
* an `[any]` conclusion is in the demand layer (W6), so it is no record;
* a `$` premise has a concrete mark (S8), so it has no `*` conclusion (W2, `Coverage.edge_conc`);
* a `*` premise never gives a normal `$` conclusion: every `$`-target micro edge has a concrete premise mark (S7, S8),
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
`f.mark` (`*` or `*∖X`) if it is abstract, else `i.mark`. The reversal needs a MARK-REVERSIBLE record (`MarkRev`); a
mark-producing record under a `*`-mark premise has no reversal (`no_rev_of_star_conc`). With the Empty premise exclusion
every row is exact (`rev_exact_of_empty_premise`). A normal edge of a restricted run has an EXACT premise
(`RExact.complete_premise_exact`), so every mark-reversible record of every run reverses exactly.

### 9.2 The backward run

The backward analysis uses the same facts, operations, storages and primitives. Only the meaning of a mark and the
roles of the rules change (`interpreter.md` §4.9).

* A backward fact is a REQUIREMENT: "if a location of this set carries `T` here, a sink is reached".
* The backward premise is at the forward exit of the method; the backward summary edge ends at the forward entry.
* The statement transfer applies the REVERSED micro edges (§9.1), with an identity edge for a target base that the
  statement does not touch (`Reverse.Stmt.rev`; `revNoId_breaks`). A call is reversed (`Reverse.Call.rev`): the
  backward binding into the callee is the converse of the forward binding back (`r.* → return.*`, `ai.* → argi.*`,
  `S.* → S.*`); the backward binding back is the converse of the forward binding into the callee (`argi.* → ai.*`,
  `S.* → S.*`). A cleaner is its own reversal. The backward run applies no type filter (as on the main branch; the
  model keeps the filters, which only makes its demand smaller, §11.2).
* THE ZERO FACT. The backward run starts at each ROOT with the zero fact, at the forward exit of the root. The zero
  fact passes over every call, and it ENTERS every callee through its own binding `zero.* → zero.*`, at the forward
  exit of the callee. This binding is not the converse of a forward binding: with the plain converse the zero fact
  only goes up, and a requirement inside a callee never reaches the callers (`Backward.lost_plain`,
  `Backward.B_fails_plain`).
* SEEDS. The sink rule of a vulnerability that the previous forward run reported fires as a zero-to-fact edge where the
  zero fact reaches the sink statement: `Zero → (sink statement, requirement)`. The requirement goes back to the
  forward entry of its method. There it is a zero-premise backward summary, and every caller applies it at its call
  site, where its own zero fact entered the callee. So every return is BALANCED. Assumption: every instruction that
  the forward run reaches is backward reachable (the implementation wires code that never returns to the exit;
  `Backward.ExitReach`).
* THE ZERO DEMAND. A requirement that reaches a source continues to the zero fact through the reversed source edge.
  The zero fact is in every method, so every method gets the demand pattern `(zero, none)`, and the next forward run
  emits the zero fact in every method. The work from the roots to the sources (forward) and from the sinks to the roots
  (backward) repeats in every run. The work decreases because a backward run seeds only the sinks that the previous
  forward run reported, and a later run never adds a sink. All other work follows the demand.
* Every backward run is a restricted run (§6.3): concrete, no request, its own field limit.
* HAND-OFF, backward run to the next forward run (`Backward.demOf`): a backward summary `jb → gb` gives the forward
  demand pattern `(D-c = gb, D-p = jb)`; a zero-premise backward edge at the forward entry gives `(gb, none)`.
* HAND-OFF, forward run to the next backward run: the reported vulnerabilities (the seeds), and the reversed forward
  summaries as the demand of the backward run (`Backward.revSummaryDemand`: a forward summary `j → g` gives the
  backward demand pattern `(D-c = g, D-p = j)`).

The backward run satisfies the contract of the iteration (§10.7). `Backward.B_general`: for every forward run `Rk`, if
the demand of the backward run contains the reversed summaries of `Rk` and its seeds contain the sinks that `Rk`
reported, its hand-off satisfies the mark-aware contract `Backward.BackwardContractD`. The hypotheses are interpreter
contracts: the bindings have `*` targets with the mark `*` (`Reverse.BindTargetsStar`), the statement micro edges are
mark-reversible (`Backward.StmtsMarkRev`), no call binds the zero base back (`Backward.NoZeroBack`), every
non-call instruction keeps the zero fact (`Backward.ZeroKept`), and `Backward.ExitReach`. `Backward.iteration_general`
joins the runs: every forward run reports every real vulnerability. For the worked programs 1 and 2 of §6.3 the backward run
gives exactly their demand (`Backward.dem1_exact`, `dem2_exact`), and forward run 3 reports the vulnerability
(`Backward.p1_found`, `p2_found`).

`Reverse.flow_rev_iff_calls` proves that the flow of the reversed program is the converse flow, with calls, cleaners and
filters, if every micro edge and every call binding has an exact shape and is mark-reversible (`RevStmts`, `RevCalls`).

---

## 10. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

### 10.1 Soundness of run 1 — `Coverage.lean`

Hypotheses: the program is well-formed (`Program.WF`: every micro edge reads from a touched base; call bindings are
mark-agnostic; every type filter is prefix-closed) and the abstraction satisfies (E1).

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
| `answerInit_covers`, `answerInit_applicable`, `policy_applicable` | The answer covers the requested location and is applicable; the run-1 policy satisfies (E1). |
| `SharedExcl.applyEdge_shared_excl`, `den_shared_excl` | ONE exclusion per edge. |

### 10.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`

| Theorem | Statement |
|---|---|
| `Exact.edge_exact_valid`, `closed_exact_valid` | Under S7 (`MarkWF`) and with a validity predicate that every filter accepts (`FiltValid`) and that goes back along micro edges (`BackOK`): every pair of a normal-layer edge whose end location is valid is a concrete flow. |
| `Exact.edge_exact`, `complete_exact`, `closed_exact` | The same for filters that keep every extension of an accepted path (`FiltUp`; with prefix-closure this makes a filter constant, so this form is for programs without type filters). |
| `Exact.CexFilt`, `CexMark` | The two hypotheses are necessary: a filter lets a fact pass whose lower locations do not exist; a `*`-premise edge with a concrete target forgets a cleaned mark. |
| `Exact.cleanRes_exact` | A normal-layer result of the cleaner denotes only pairs of the input whose end location the cleaner keeps. |
| `Closed.closed_records_exact`, `closed_records_exact_valid` | A property of records (not used by the analysis): no request on the initial fact and only normal exit edges ⇒ the records are exactly the concrete flow from its location set. |
| `Invariant.final_star_legal`, `final_star_abstract` | W2: a `*` conclusion has the mark `*` or `*∖X` and is in the normal layer. |
| `Invariant.no_univ_star` (+ `no_univ_needs_*`) | S8 ⇒ no `*/Universe` edge fact; each hypothesis is necessary. |
| `Invariant.demand_of_any_ok` | W6 is a layer refinement. |
| `star_final_keeps_initial_excl`, `star_initial_complete`, the demand-monotone lemmas | A final `*/Ec` under an initial `*/Ei` keeps `Ei ⊆ Ec`; under `*/Ei` a normal-layer final fact has the `*` tail or `Ei = {}`; the demand layer never goes back. |
| `Confirmed.confirmed_real_valid`, `confirmed_real` | A CONFIRMED vulnerability (§4.9) is a real concrete vulnerability for the reference semantics of S1–S9 (valid form; `MarkWF ∧ FiltUp` form; §11.1 lists the expected false-positive sources). `CexConfFilt`, `CexConfMark`: both hypotheses are necessary. |
| `Confirmed.weak_support_gap`, `rev2_not_confirmed` | The weaker support condition admits a false positive; the counter-example program `Confirmed.Rev2` is not confirmed. |

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
| `Stmt.rev_step_iff`, `flow_rev_iff_calls`, `rev_WF`, `backward_of_forward_calls` | The reversed program has the converse flow, with calls, cleaners and filters; it is well-formed; the backward analysis is covered by the forward theorem. |
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
| `NDExact.nd_edge_exact`, `nd_edge_exact_valid`, `nd_edge_exact_gen`, `nd_edgeOK` | THE ND EXACTNESS THEOREM. Under S7 and S9 (and `FiltUp`, or valid locations with `ConjOK`): a normal-layer edge with the premise list `P` gives a support derivation `TaintN M n l L0` for EVERY support `L0` that `P` covers and every end location `l` of the edge (with `den` for one premise). The converse of `nd_coverage`. |
| `NDExact.nd_edge_exact_single`, `nd_edge_exact_nd` | The single-premise form (`den i f l0 l ⇒ TaintN … [l0]`) and the form for two or more premises (every covered support, every covered location). |
| `NDExact.CexLit.cex_lit`, `CexConjOK.cex_conjOK` | Both hypotheses are necessary: an abstract literal lets a correlated input with a mark exclusion through (the excluded locations reach nothing); without `ConjOK` a valid end location has an invalid support. |
| `NDExact.covers_nonempty` | Every fact covers some location (also `*/Universe` and `*∖X`), so a support can always be built. |

### 10.7 Restricted runs and the iteration — `Restricted*.lean`

The restricted closure `DR` (`Restricted.lean`) has the rules of `D`, with three changes: `initR` (an initial fact only
from the emission and a demand pattern), `ret` (a summary edge only through a restriction by a demand pattern, and only
for a satisfied premise), and `retRec` (persisted records, applied when the run's satisfaction or `applicable` holds). A DEMANDED flow (`FlowR`, `ReachR`) is a concrete
flow whose every call step has a demand pattern of the callee: `D-c` covers the entry location with its mark, and
`D-p` covers the exit location. The coverage and iteration theorems are generic over the rules, given the contracts
`EmitContractOn`, `SatContract` and `RestrictContract`.

| Theorem | Statement |
|---|---|
| `RCore.emitM_contract_I`, `emitM_copies`, `satI_contract`, `emitM_satI`, `emitM_inter`, `emitM_complete`, `emitM_shape`, `emitM_chain_strong` | The spec emission satisfies (E2) for concrete added facts and copies the mark (E3); the emitted fact is exactly `a ∩ D-c`, lies inside its added fact, and has the chain of the fact or the demand chain. |
| `RCore.satI_markSub`, `satI_conc_record` | The satisfaction compares locations, and the marks of the fact against the marks of the premise: a cleaned fact reads a `*` premise, a concrete fact reads a `*`-premise summary. |
| `RCore.emitM_not_full_any` | (E2) fails for a `*`-mark added fact under a `T` demand, for every satisfaction: the concreteness of the run is necessary. |
| `RCov.concInvR_all`, `added_concR`, `no_reqR`, `RExact.DR_concrete`, `DR_no_request`, `final_not_star`, `RMain.no_request_M` | A restricted run with a mark-copying emission is CONCRETE: every initial fact, edge and added fact has a concrete mark, no final fact has the `*` tail, and the run has NO request (also with cleaners). |
| `RExact.restrict_U_eq_S`, `RCore.restrictU_eq_S_nonstar`, `restrictS_contract` | In a concrete run the restriction of §6.4 (`restrictU`) gives the same run as `restrictS`, whose contract holds. |
| `RExact.complete_premise_exact`, `complete_rev_exact` | A normal edge of a concrete run has an exact premise, so its record reverses exactly. |
| `RCases.p1_found_M`, `p2_found_M`, `p1_reachR_M`, `p2_reachR_M` | Run 3 (forward) reports programs 1 and 2, with the restriction of §6.4. |
| `RCov.coverageR`, `reach_strongR`, `vuln_foundR` | THE COVERAGE OF A RESTRICTED RUN: for a demanded flow from a covered entry location, an edge covers the pair or the run has the request; its own summaries demand the same flow. |
| `RCov.coverageD`, `reach_to_reachR`, `vuln_foundD` | Run 1 reports every real vulnerability, and its summaries demand its witness. |
| `RCov.iteration_sound`, `iteration_sound_conc`, `RMain.iteration_sound_M`, `iteration_sound_M_identity` | THE ITERATION THEOREM: if every backward step satisfies the contract B (`BackwardContract`: every vulnerability witness that the summaries of a forward run demand stays demanded), EVERY forward run reports every real vulnerability; any field limits, any records. |
| `RCov.backward_identity`, `backward_of_superset`, `RMain.noSink_contract`, `everyWitness_contract_fails` | The identity backward step satisfies B; B is about sink witnesses only. |
| `Backward.DB`, `demOf`, `revSummaryDemand` | The backward run of §9.2: the rules of `DR` on the reversed program, the zero fact from the roots, the zero binding into every callee, the seeds, the balanced return; the hand-offs in both directions. |
| `Backward.B_general`, `iteration_general`, `BackwardContractD`, `repD_of_rep`, `iteration_sound_D`, `iteration_sound_M_D` | THE BACKWARD RUN SATISFIES THE CONTRACT: for every forward run, if the backward demand contains its reversed summaries and the seeds contain its reported sinks, the hand-off satisfies the mark-aware contract; so every forward run reports every real vulnerability. |
| `Backward.BackwardContractRep`, `rep_of_B`, `iteration_sound_rep`, `B_fragment_rep`, `B_rep_fails_general` | The contract for reported vulnerabilities only is enough; on programs where no call binds back it holds directly; in general its mark-blind exit is too weak (counter-example), so the mark-aware form is used. |
| `Backward.dem1_exact`, `dem2_exact`, `p1_found`, `p2_found` | For programs 1 and 2 the backward run gives exactly their demand, and forward run 3 reports the vulnerability. |
| `Backward.lost_plain`, `B_fails_plain` | With the plain converse of the forward bindings (no zero binding into the callee) program 1 is lost. |
| `RExact.edge_exactR_valid`, `closed_exactR_valid`, `recs_of_DR_valid`, `recs_of_D_valid` (valid locations); `edge_exactR`, `complete_exactR`, `recs_of_DR`, `recs_of_D`, `closed_exactR`, `RMain.closed_records_exactM` (`FiltUp`) | Exactness and record reuse in restricted runs. |
| `RExact.SupM`, `ConfirmedM`, `confirmed_realM_gen`, `confirmed_realM_gen_valid` (every satisfaction with `SatMark`); `RMain.confirmed_real_M`, `confirmed_real_M_valid` (the spec rules) | A confirmed vulnerability of a restricted run is real for the reference semantics of S1–S9; the support accepts the emitted exact fact. |

---

### 10.8 Statics — `Statics.lean`, `StaticsIter.lean`

| Theorem | Statement |
|---|---|
| `Statics.coverageD`, `vulnD` | Under the construction rules (`SWF`), run 1 with the position request of §4.10 (`Design`) reports every real vulnerability. |
| `Statics.DS_edgeOK`, `edge_exactS`, `edge_exact_validS`, `complete_exactS` | Its normal edges denote only real flows. |
| `Statics.cinv_all`, `no_any_above` | No static fact with the `[any]` tail occurs above a static position; a static fact above a position is an abstract static `*` fact. |
| `Statics.gen_read_DS`, `gen_read_sreq` | A static read on the abstract static root gives no fact and raises the position request. |
| `Statics.CexAbove.y_vuln_normal`, `CexWide.w_vuln_normal`, `CexClean.deep_vuln_normal` | A write in the caller, a write in a callee and a cleaner in a callee: the vulnerability is found through a normal edge. |
| `Statics.CexClean.shallow_misses`, `CexAbove.cex_user_misses`, `CexAny.counterexample`, `CexWide.counterexample` | The rule variants that fail: the chain answer of a static mark request, the climb only from the static root, an `[any]` source on a bare class, and a write that does not request `<C>`. |
| `StaticsIter.rinv_all`, `no_any_above_R`, `static_step_below`, `static_sink_below`, `no_request` | AFTER RUN 1 NO STATIC RULE IS NEEDED: in a restricted run, for every demand, no static `*` or `[any]` fact lies above a static position; every static operation is the case at or below; no request. |
| `StaticsIter.reach_strongDSD`, `iteration_general_DS`, `no_static_rule_after_run1` | The iteration from run 1 = `DS`, with plain restricted runs after it: every forward run reports every real vulnerability, and every later run satisfies the invariant. |
| `StaticsIter.ExampleIter.run3_confirmed`, `WideIter.run3_confirmed`, `AboveIter.run3_confirmed`, `CleanIter.run3_confirmed`, `ExampleIter.demE_exact` | The worked static programs: forward run 3 confirms the vulnerability through a normal edge with no request; the exact demand for `Example`. |

## 11. What the proofs do not cover

### 11.1 Expected false-positive sources

The theorems say that a confirmed vulnerability is real for the reference semantics of S1–S9: the program that the
micro edges describe. On the JVM the micro edges over-approximate the real program at the points below. There a
confirmed vulnerability (and a normal edge, and a record) can be false. These are EXPECTED false-positive sources: the
analysis keeps their results in the normal layer and does not refine them.

* A type filter on a `*` or `[any]` fact. The filter checks the concrete path only, so the fact keeps the locations below
  its path that a real value cannot have (§4.8).
* A reversed backward record. The backward run does not type-filter, so the record has no type filter (§8.7 R3).
* The weak alias write. The alias base keeps its old content (S2, `interpreter.md` A3, gap G7).
* The constructor pass-over. A bound caller fact also passes over a constructor call, so the constructor does not
  overwrite the caller facts (`interpreter.md` §3.5, gap G8).
* The path-insensitive reading. A conjunction can combine literals that hold on paths that exclude each other (§4.6),
  and a negated mark literal counts as true (§4.2).

### 11.2 Other limits

* The concrete semantics is alias-free and location-level (S1–S9).
* The theorems are about the closures `D`, `DR` and `DN`. A real run differs from them by optimizations. Each one keeps
  the soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§8.1) | the dropped pairs are pairs of the kept fact (`subsumes_sound`) | the local step is proved; the composition is argued |
| merge rules 1 and 2, also for marks (§3.3, T1, T2, T2') | exact (`rule1_mem`, `rule2_den`, `rule2_mark`, `merge_inter`, `merge_mark_inter`) | proved |
| the T5 fold | the denotation does not change | argued |
| persisted records (R4) | a normal edge has no false pair; adding edges keeps coverage (rule `retRec`, with `applicable`) | proved (`RExact.recApp_markSub`, `RMain.p3_reuse_exact`) |
| W6 (`[any]` always in the demand layer) | a layer refinement (`demand_of_any_ok`) | proved per fact; the run is argued |

* The backward run is modelled as the closure `Backward.DB` (the rules of `DR` on the reversed program, with the zero
  rules of §9.2), and it satisfies the contract B (`Backward.B_general`). The model keeps the type filters in the
  backward run; the implementation drops them (§9.2), which only adds backward flows and so only enlarges the demand.
  ND conjunctions in the backward run and the interpreter's call-site rules (`interpreter.md` §4.9) are argued.
* ND edges are modelled for run 1 (`DN`): coverage, the vulnerability theorems (§10.6) and the exactness of the normal
  layer against the support semantics `TaintN` (`NDExact`, under S9) are proved. The CONFIRMATION of a vulnerability
  through a conjunction is ARGUED from that exactness and the support of each premise (§4.9), not proved. No ND edge
  is a record (§4.6). A
  restricted run with ND edges is ARGUED, not modelled:
  1. its facts are concrete, so a literal never raises a request (§4.5);
  2. the callee restricts an ND summary `{j1, …, jk} → g` by a demand pattern `d` as a single-premise summary (§6.4): the
     result keeps the whole premise list if one `jm` overlaps `D-c`, and `R-c` follows the table of §6.4; the
     restriction only removes pairs from the conclusion;
  3. the contract B for a TREE witness (`ND.ReachAll`) needs a demand pattern on every node of the tree. The backward run
     reads a conjunctive edge as an OR of its literals (§4.6), so a requirement at the conclusion reaches every branch.
  `D_sub_DN` embeds the distributive part, so the iteration theorem holds unchanged for a program without conjunctions.
* `ND.lean` keeps premise LISTS with the zero premise `[zeroFact]`; this spec keeps SETS and drops the zero premise. So
  `[zero, i]` is an ND edge in the model and a fact-to-fact edge here. Every ND theorem holds for the list form. A
  conjunction result with fewer than two premises is an ordinary edge in the spec, so it can be a record if it is
  normal; it is exact (`NDExact.nd_edge_exact`, for every premise list).
* The static rule of §4.10 is modelled as a separate run-1 closure `Statics.DS`. Soundness, exactness and the
  iteration that starts from it are proved (`StaticsIter.iteration_general_DS`). That a cleaner on `S` must name its
  mark is a hypothesis of the run-1 proof (no counter-example is known for a cleaner of every mark); the restricted runs
  do not need it (`StaticsIter.SWFR`).
* The implementation rules differ from the model at these points:
  * W6 (§2.3). On an `[any]` input in the normal layer, or for an `[any]` target, the Lean `applyEdge` can give an
    `[any]` result in the normal layer. The implementation puts it in the demand layer (§4.1 step 6). The two agree on
    every input that satisfies W6, except for this layer bit (`Invariant.demand_of_any_ok`).
  * The preconditions of `concat` (§4.1). The model computes a result for an edge that breaks S7, S8 or I7; the
    implementation asserts that no such edge exists.
  * The cleaner request (§4.7). The model also raises the request `T` for a `*∖X` fact with `T ∈ X`; the
    implementation does not. The request only costs work.
* The interpreter (`interpreter.md`) is outside the model, except through S1, S2, S5, S7, S8 and S9. Its known gaps are
  listed in `interpreter.md` §0.1. The reading of a negated mark literal as true (S1) is not modelled: the model has no
  rule conditions.
* Exceptions are out of scope for now: no exception flow crosses a call, and a catch block does not read `exc`
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
| `StaticsIter.lean` | No static rule after run 1: the invariant of restricted runs, the iteration from `DS`, the worked programs through forward run 3. |
| `Restricted.lean` | The restricted runs: demand patterns (`DemandEdge`), the emission `emitM`, the satisfaction `satI`, the restriction `restrictU`, the closure `DR`, `FlowR`, `ReachR`, the contracts, `summaryDemand`, `BackwardContract`, and the location-only rules of earlier versions (`ap-history.md`). |
| `ND.lean` | ND edges: conjunctive micro edges, the support semantics `TaintN`, the closure `DN`, the ND coverage and vulnerability theorems. |
| `NDExact.lean` | The exactness of normal-layer ND edges against `TaintN` (`LitConc` = S9, `ConjOK`), with the two counterexamples. |
| `Cases.lean`, `RestrictedCases.lean` | Test vectors (`decide`), programs 1 and 2. |
| `Core.lean`, `SharedExcl.lean`, `RestrictedCore.lean` | The local lemmas. |
| `Coverage.lean`, `RestrictedCoverage.lean`, `RestrictedMain.lean` | Soundness of run 1 and of the iteration; the instantiation with the spec rules. |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `RestrictedExact.lean` | Exactness, invariants, the records of a request-free initial fact, confirmed vulnerabilities. |
| `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean` | Concept against optimization. |
| `Reverse.lean` | Reversal. |

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
   concept implementation (§4.1 reference form) and on the tree implementation. Some vectors (the `lostCorr` vectors,
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
4. Mark tests: every row of the mark gate and of the result mark (§4.1 steps 4, 5); a `*∖X` summary conclusion stops a
   caller fact with a mark in `X`; a sink for `T ∈ X` neither triggers nor requests; a request for `T ∈ X` does not
   climb; the preconditions of `concat` (§4.1) fail on a `*∖X` premise, on a `$` premise with the mark `*`, and on a
   `$` premise with a `*` target.
5. Cleaner tests: every row of the two tables of §4.7; the split (`*∖{T}` plus the request, then the concrete answer
   cleaned exactly); no request for `T ∈ X`; the all-marks cleaner; a cleaned fact through a field write past the field
   limit keeps its mark exclusion.
6. Type filter tests: a fact on an accepted path passes, also with a `*` tail; a fact on a rejected path is dropped; the
   predicate is prefix-closed.
7. ND tests: a conjunction from two facts of different premises gives the union premise set; the last arriving fact
   completes it; a fact that only overlaps its literal enters the store and gives a demand-layer result; an `[any]`
   literal (`ContainsMarkOnAnyField`) accepts a fact below its position; an ND summary needs one caller fact per
   premise; ND conclusions have no `*` tail; a vulnerability through a conjunction is confirmed only if every premise
   of its sink edge is exact and supported (§4.9). Today's `ExampleTest.test nd rule` as an analysis test.
8. Merge tests: rules 1, 2 and 2'; a union of exclusions or mark exclusions is never made.
9. Request tests (run 1): the mark gate raises a request; a standing request is answered by a later added fact and by a
   second added fact; a standing request reaches a second caller edge of an EXISTING added fact (the program of §4.5);
   propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain; every request
   premise is `(x, [], *, {}, *)`. In a restricted run, a request is a bug (assert it).
10. Call and ownership tests: every event of the table of §5.3, in two orders; the callee restricts before it
    publishes; a caller reads the summaries of every premise its fact satisfies; a record applies when its premise
    covers the caller fact, in run 1 and in a restricted run.
11. Abstraction tests: run 1 emits the most abstract fact; every row of the two tables of §6.3; the emitted fact is
    exactly `a ∩ D-c` with the mark of `a`; the same result for two insertion orders.
12. Restriction tests: every row of the table of §6.4; the union over two demand patterns; no result without `D-p`.
13. Iteration tests: programs 1 and 2 as analysis tests with a forward limit 3 and a backward limit 2; the vulnerability
    is reported in every forward run. A worker loop with a sink that never returns (§9.2).
14. Store tests: index completeness against a list filter (records, demand patterns, requests, conjunctions,
    subscriptions).
15. Reversal tests: every row of §9.1 that occurs for a record, also with `*∖X`; the forward record and its reversed
    reading give converse results on the same concrete pair.
16. Analysis tests (phase 2 gate): the existing `*AnalysisTest` suites, run with `cleanTest`; `DeepCleanSummaryAnalysisTest`
    and the cleaner suites for §4.7. A lost finding is a test whose message says that no vulnerability reached the sink;
    read the message, do not count failures.
