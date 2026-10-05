# Access paths and storages — specification

Status: design spec for phase 1 of [bidirectional-task.md](../bidirectional-task.md) ("New AP with all required
storages"), version 5. Version 2 came from the first design review, version 3 added the runs that strictly follow the
demand, version 4 made the demand mark-aware. Version 5 splits the spec in two and adds the last primitives:

* this document (`ap.md`) defines the access path (AP): the fact, the edge, the operations and the primitives (micro
  edge, summary edge, mark request, mark conjunction, cleaner, type filter, emission), the runs and the storages;
* [`interpreter.md`](interpreter.md) defines how the IR is interpreted in terms of the AP: the micro edges of the
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

This spec does not define the IR interpretation (`interpreter.md`), the analyzer scheduling, the iteration driver or
the trace resolution. It defines the contracts that these parts use. The contract of the backward run is in §10.7.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | A statement is described by its summary: the bases that it touches and its micro edges (`interpreter.md` §2). Every micro edge is PRECISE AND COMPLETE: the micro edges of a statement give exactly its flows. This holds also for the call bindings and the alias edges. The flows of a rule are read with every negated mark literal true (the reference semantics of a path-insensitive engine, §4.2); with this reading a source, sink or pass-rule edge is precise. | The interpreter. |
| S2 | Aliasing is described by extra micro edges (gen edges to alias paths), precise and complete as S1 asks. The write at an alias is WEAK: the alias base keeps its old content (`interpreter.md` A3, gap G7). This keeps soundness when an alias does not hold, and costs precision. The model itself is alias-free. | The alias analysis. |
| S3 | Formal parameters are not reassigned inside the method. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. | The CFG normalisation. |
| S5 | A type filter accepts every path that a real value of the static type can have, and it is prefix-closed (§4.8). | The type checker. |
| S6 | The result of run 1 is the least fixed point of the rules of §4–§6 (Lean: `D`). The result of a later run is the least fixed point of the restricted rules (Lean: `DR`). The worklist may compute it in any order. | The analyzer. |
| S7 | Mark well-formedness: no micro edge or call binding has a `*∖X` premise, and a micro edge with a concrete target mark has a concrete premise mark (`Exact.MarkWF`). Without it a normal-layer edge can claim a cleaned mark (`Exact.CexMark`). | The interpreter (sources have the premise mark `zeroMark`, conditional sources `T`). |
| S8 | No `*/Universe` edge: a micro edge with a `$` premise has a concrete premise mark, and no micro edge, binding or initial fact has the kind `*/Universe` (`Invariant.no_univ_star`; each hypothesis is necessary: `no_univ_needs_*`). | The interpreter. |
| S9 | A conjunction literal has a concrete mark (`NDExact.LitConc`). Without it the ND exactness is false (`NDExact.CexLit.cex_lit`). | The interpreter (a mark literal names its mark). |

Inside this scope:

* Run 1 is SOUND: an edge covers every concrete flow, and every concrete source-to-sink flow is reported (§10.1).
* A later run is SOUND RELATIVE TO ITS DEMAND: it reports every concrete vulnerability whose flow the demand covers,
  and it passes the same flow on as the demand of the next run (§10.7).
* With the contract of the backward run (B, §10.7), EVERY FORWARD run reports every concrete vulnerability
  (`RMain.iteration_sound_M`). So stopping at any forward run is sound, and a vulnerability that a forward run does not
  report is not real.
* Inside the smaller scope of NORMAL-LAYER edges the analysis is also EXACT: every pair of such an edge whose end
  location is VALID (every type filter accepts it; real values have only valid locations) is a concrete flow
  (`Exact.edge_exact_valid`, §10.3). The validity must go back along the micro edges (`BackOK`, §4.8). Exactness is
  against the path-insensitive reference semantics: a conjunction (§4.6) and a rule condition that one fact does not
  decide (§4.2) are expected over-approximations, not demand steps. A normal-layer edge with conjunctions is exact
  against the support semantics `ND.TaintN` (`NDExact.nd_edge_exact`, `nd_edge_exact_valid`, under S9). A CONFIRMED
  vulnerability whose sink pattern covers only valid locations is a real one (`Confirmed.confirmed_real_valid`,
  `RMain.confirmed_real_M_valid`). For a program without type filters the same holds with no validity condition
  (`Confirmed.confirmed_real`, `RMain.confirmed_real_M`). The same two forms hold for the closed records (R5,
  `Closed.closed_records_exact_valid`, `closed_records_exact`). The confirmation theorems are for programs without
  conjunctions; a confirmation through a conjunction is not proved (§11).

### 0.2 Decisions of the design reviews

| Topic | Decision |
|---|---|
| Layer | A propagation edge is in the normal or the demand layer (`~`, `Zero~`). Only the AP operations of §4.2 move it to the demand layer; the expected over-approximations of a path-insensitive engine (§4.2, §4.6) do not. A micro edge has no layer. An `[any]` conclusion is ALWAYS in the demand layer. So "complete" means "normal layer". |
| Exclusion | ONE exclusion per path edge, shared by premise and conclusion (§2.2). An exclusion is a finite set of accessors; "Universe" does not exist in the AP. Two merge rules (§3.3); no union across different conclusions. |
| Mark | A premise has the mark `*` or `T`. A conclusion has `*`, `T`, or `*∖X` (the premise mark passes unless it is in `X`; a cleaner makes it, §4.7). |
| Read | A field read never changes an exclusion. Only a field write does. |
| Statics | One `ClassStatic` base with the class accessor. |
| Operations | One computation (delta-concat, §4.1) and two operations on it: a MICRO EDGE applies to every overlapping fact (§4.2); a SUMMARY EDGE applies only to a fact that satisfies its premise (§4.3). |
| Ownership | The CALLER owns the subscriptions and applies the summaries. The CALLEE owns the added facts, the demand edges, the emission and its summaries; it restricts each summary by its demand edges before it publishes it (§5). |
| Runs | Run 1 is unrestricted: it emits the most abstract facts. Every later run STRICTLY follows the demand of the previous run: the emission `a ∩ D-c` with the mark of `a` (§6.3) and the summary restriction (§6.4). A restricted run is concrete. |
| Requests | The task rule for the answer (no chain deeper than the request). Requests stand for the whole run. Requests exist ONLY in run 1 (§4.5). |
| Conjunction | A rule with several mark literals on different facts makes an ND edge: a SET of premises (§4.6). |
| Cleaner | A cleaner splits a `*`-mark fact by the mark: the fact continues as `*∖{T}`, and the mark `T` is requested and cleaned exactly on the concrete answer (§4.7). |
| Type filter | A prefix-closed predicate on paths; it only drops facts that have no real location (§4.8). |
| Report | Every forward run reports every real vulnerability (with B). Confirmed vulnerabilities persist. A demand vulnerability that the next forward run does not report is refuted (§8.10). |

### 0.3 History

* Version 3 used location-only rules for the strict demand. Two agreed rows then lose a real flow (programs 1 and 2,
  `RCases.p1_lost_U`, `p2_lost_U`). Version 4 made the emission mark-aware; the restricted runs became concrete, and
  neither row can fire (`RCases.p1_found_M`, `p2_found_M`). The model keeps the version-3 rules as the record.
* Version 5 removes the Universe exclusion (it never occurs with the interpreter's edges, §2.3), puts every `[any]`
  conclusion in the demand layer, separates micro edges from summary edges, and adds the mark exclusion, the cleaner,
  the type filter and the ND edges.

---

## 1. Terms

| Term | Meaning |
|---|---|
| base | A local, an argument, `this`, the return value, the exception, a constant, the `ClassStatic` base, or the zero base. |
| accessor | A field, an array element, a class accessor (`<static>(C)`), or another structural step (type info, value). Not a mark, not `[any]`, not `$`. |
| counted accessor | A field or an element accessor. The field limit counts only these. |
| path | A finite list of accessors. |
| location | A concrete triple (base, path, mark): the value at `base.path` carries `mark`. |
| tail | The end of a fact path: `*` (abstract), `[any]` (any continuation), or `$` (exact). |
| exclusion | A finite set of first accessors that a `*` continuation must not start with. |
| mark | `*` (abstract: the mark of the premise passes), `T` (concrete), or `*∖X` (abstract except the marks of `X`; conclusions only). |
| fact | A tuple (base, path, tail, exclusion, mark). §2. |
| premise | The initial fact of an edge: the fact at the method start that the edge depends on. An ND edge has a SET of premises. |
| conclusion | The final fact of an edge: the fact at a statement. |
| edge | (premise or premise set, layer, statement, conclusion), with one exclusion. The zero fact is also a premise. |
| layer | `normal` or `demand`. The demand layer of premise `i` is written `i~`; of the zero fact, `Zero~`. |
| complete edge | An edge in the normal layer. |
| incomplete edge | An edge in the demand layer. |
| micro edge | One edge of a statement or call summary that the interpreter makes. |
| summary edge, record | An edge whose statement is the method exit. A persisted complete summary edge is a record. |
| added fact | A caller fact rebased to the callee bases at a call site. |
| abstraction, emission | The function that selects the initial facts for an added fact. §6. |
| request | A request for a concrete mark on an initial fact (run 1 only). §4.5. |
| run | One analysis pass in one direction with one field limit `L` (forward-1, backward-2, forward-3, ...). |
| restricted run | Every run after run 1. It strictly follows its demand. |
| demand edge | An edge of the previous run (the other direction) that a restricted run gets. In the orientation of the restricted run it has an entry pattern `D-c` and an exit pattern `D-p` (or none, if the demand does not reach the method exit). |
| demand (of a run) | The set of demand edges that a restricted run gets (§8.6). Not the same as the demand LAYER. |
| demand vulnerability | A triggered vulnerability that is not confirmed (§4.9). |
| strong enough | A fact is strong enough for a premise if the premise covers it (`applicable`). Then the fact is at or below the premise (§4.1 case `below`). |
| not strong enough | The fact is above the premise (§4.1 case `above`). The result loses the correlation. |
| satisfies | A fact satisfies a premise if the caller may apply the summary edges of that premise to it (§4.3). |
| concrete run | A run in which every fact has a concrete mark. Every restricted run is concrete (§6.3). |
| method key | `MethodEntryPoint` (context plus entry statement), as today. |

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

* An edge has ONE exclusion `E`. The premise and the conclusion share it: for `(x, p, *) →_E (y, q, *)`, the value at
  `x.p.σ` flows to `y.q.σ` for every `σ` that `E` admits. It does not matter on which side the model stores `E`: only
  the union counts (`SharedExcl.applyEdge_shared_excl`, `den_shared_excl`).
* For an uncorrelated edge (the conclusion is `$` or `[any]`) the exclusion restricts the premise continuation only.
* The MARK EXCLUSION `X` of a conclusion `*∖X` stops the marks of `X`: the value at the premise location flows to the
  conclusion location only if its mark is not in `X`. It belongs to the edge, as the exclusion does; a cleaner makes it
  (§4.7). Premises never carry one.
* Every initial fact that run 1 emits has the Empty exclusion (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`). In a restricted run an emitted fact can carry the exclusion of the demand (the meet
  with a `*/E` entry pattern, §6.3); it has a concrete mark, so it starts in the demand layer and makes no complete
  record. So in practice the exclusion is a property of the conclusion. It grows only by a field write (a kill).
* The LAYER is part of the edge identity. The layer of a propagation edge changes only by the AP operations of §4.2:
  the case `above` of §4.1, a lost correlation (`lostCorr`), an `[any]` result (W6), the cut of §4.4, a conjunction
  with an input that is demand or that its literal does not cover (§4.6), and the `part` rows of §4.7 that give a
  demand result. A demand input gives a demand result. A micro edge has no layer (§4.2). The layer of an edge never goes
  back (`Invariant.applyEdge_demand_monotone` and the related lemmas).

Lean: `PFact` (a premise or a conclusion; the conclusion `*/E` carries the exclusion of the edge; the mark is `MarkA`
with `star`, `conc t`, `starEx x`) and `AFact` (a conclusion plus `demand : Bool`, the layer).

### 2.3 Well-formedness rules

| Rule | Text |
|---|---|
| W1 | An edge with no `*` side has the Empty exclusion. |
| W2 | A conclusion with the `*` tail has the mark `*` or `*∖X` and is in the normal layer. A premise may have the `*` tail with a concrete mark (a request answer in run 1; in a restricted run, the meet of an added fact with a `*/E` entry pattern). |
| W3 | Every result of an operation has at most `L` counted accessors in a run with the field limit `L` (§4.4). A micro edge (§4.2) and a premise emitted from a demand chain (§6.3) have no bound. |
| W4 | `[any]` is a tail only. A path has no inner `[any]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. |
| W6 | A conclusion with the `[any]` tail is in the demand layer. |
| W7 | Only a conclusion has a mark exclusion. An ND conclusion has no `*` tail. |

W2 holds for every derived fact, in run 1 and in every restricted run (`Invariant.final_star_legal`,
`RExact.final_star_legalR`).

W6 is a rule of the implementation. The model keeps an `[any]` conclusion possible in the normal layer; the rule only
moves edges from the normal to the demand layer, so every theorem stays true for it: soundness ignores the layer, and
exactness and confirmation hold for every subset of the normal edges. In the model a normal-layer `[any]` needs an
`[any]`-target micro edge on an exact derivation. The interpreter has one kind: the any-field rules, a source or pass
rule with an `[any]` target (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`; `interpreter.md` §4.1). Under W6 their
results go to the demand layer, as decided for version 5 (F41): an `[any]` result never makes a complete record and
never confirms.

No exclusion is "Universe". In the model `Excl.univ` still exists as the encoding of a `$` premise in the operation
tables (`tailExcl`). A `*/Universe` conclusion would need a `$`-premise edge to act on a `*` fact; every `$`-premise
micro edge of the interpreter has a concrete premise mark (`zeroMark` for sources, `T` for conditional sources), and a
`*`-tail fact has the mark `*` or `*∖X` (W2), so the mark gate never lets it through. `Invariant.no_univ_star` proves it
under S8, and W2 for every derived fact (`Invariant.final_star_legal`). W6 is a layer refinement
(`Invariant.demand_of_any_ok`: marking an `[any]` result as demand keeps its pairs and only raises the layer).

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. A source rule is a micro edge from the zero fact. Zero-to-fact edges are
edges with the zero premise, in the normal or the demand layer.

### 2.5 Classification

* COMPLETE edge: normal layer (Lean: `AFact.complete`, which also excludes `[any]`; with W6 the two agree). Complete edges
  are persisted and reused in later runs and in the other direction (§8.7).
* INCOMPLETE edge: every other edge. Incomplete edges are used in their own run like every edge. They are never
  persisted and never reversed.
* The DEMAND of a restricted run comes from the previous run in the other direction (§8.6): the edges of that run on
  the paths from the vulnerabilities of the run before it — incomplete edges, reversed complete records, and the zero
  edges (§9).

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

with `admits(*, m)`, `admits(T, m) ⇔ m = T`, `out(*, m) = out(*∖X, m) = m`, `out(T, m) = T`, and
`passes(*∖X, m) ⇔ m ∉ X` (true for the other marks).

`den(i, f)(l0, l1)` reads: "the value at `l0` on method entry flows to `l1` at the statement of the edge". Lean:
`PFact.covers`, `den`, `MarkA.passes`. The restriction reads a demand pattern as LOCATIONS without marks
(`PFact.coversLoc`); the emission and the demanded flows read the entry pattern with its mark (`PFact.covers`).

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
  (`Subsume.union_loses_pairs`). (The current `EdgeNonUniverseExclusionMergingStorage` does that. It was sound only
  with the old refinement.)

---

## 4. Operations and primitives

### 4.1 The core computation: delta-concat

`concat(c, from →_E to)` computes the result of an edge `from → to` with the edge exclusion `E` on the conclusion `c` of
a current edge. `Ec` is the exclusion of the edge of `c`. Two operations use it: the micro edge (§4.2) and the summary
edge (§4.3). Lean: `applyEdge`.

Step 1 — base. If `c.base ≠ from.base`, the result is empty.

Step 2 — position:

* `below r`: `c.path = from.path ++ r`. The fact is at or below the premise: STRONG ENOUGH.
* `above r`: `from.path = c.path ++ r`, `r ≠ []`. The fact is above the premise: NOT STRONG ENOUGH.
* `apart`: neither. The result is empty.

Step 3 — overlap and result shape.

Case `below r`. The premise must admit `r` (`*`: `E` admits `r`; `$`: `r = []`; `[any]`: every `r`). Then:

| `to.tail` | `r` | `c.tail` | result path | result tail | demand step |
|---|---|---|---|---|---|
| `*` | `≠ []` (`E` admits `r`) | any | `to.path ++ r` | `c.tail` (with `Ec`) | no |
| `*` | `[]` | `$` | `to.path` | `$` | no |
| `*` | `[]` | `*/Ec` | `to.path` | `*/(Ec ∪ E)` | no |
| `*` | `[]` | `[any]` | `to.path` | `[any]` | yes (W6) |
| `[any]` | any | any | `to.path` | `[any]` | yes (W6) |
| `$` | any | `*/Ec` | `to.path` | `$` | if the correlation of `c` restricts the premise (`lostCorr`) |
| `$` | any | `[any]` or `$` | `to.path` | `$` | no (an `[any]` `c` is in the demand layer already) |

`lostCorr` is true if `Ec ∪ E ≠ {}` for `r = []`, or `Ec ≠ {}` for `r ≠ []`. Otherwise every premise continuation is
admitted, and the uncorrelated result is exact (`Exact.applyEdge_exact`).

Case `above r`. The premise decides WHETHER the edge applies: the tail of `c` must admit `r` (`*/Ec`: `Ec` admits `r`;
`[any]`: yes; `$`: no overlap). The target decides WHAT comes out: `(to.path, $)` if `to.tail = $`, else
`(to.path, [any])`. The result is always in the demand layer: a `*` fact loses its correlation, and an `[any]` fact is in
the demand layer already (W6).

Step 4 — mark gate. The premise mark `from.mark` against the fact mark `c.mark`:

| `from.mark` | `c.mark` | result |
|---|---|---|
| `*` | any | apply |
| `T` | `T` | apply |
| `T` | `T' ≠ T` | empty |
| `T` | `*∖X`, `T ∈ X` | empty (the mark was cleaned) |
| `T` | `*` or `*∖X` with `T ∉ X` | NO fact; the request `T` on the premise of `c` (§4.5) |

Step 5 — result mark `comp(to.mark, c.mark)`:

| `to.mark` | `c.mark` | result mark |
|---|---|---|
| `*` | `m` | `m` |
| `T` | any | `T` |
| `*∖X` | `*` | `*∖X` |
| `*∖X` | `*∖Y` | `*∖(X ∪ Y)` |
| `*∖X` | `T` | `T` if `T ∉ X`; NO fact if `T ∈ X` |

A `*∖X` target occurs only on a summary conclusion (a callee with a cleaner). Lean: `markComp`.

Step 6 — layer: the result is in the demand layer if `c` is, or if step 3 says so. Normal form (W2): a result with the
`*` tail and (a concrete mark, or the demand layer) becomes uncorrelated, `[any]`, in the demand layer. The step only
enlarges the fact (`CoreAux.norm_sound`).

Theorem `Core.applyEdge_sound` (THE CORE LEMMA): `concat` covers the composition of the fact relation and the edge
relation, or raises the request for the premise mark — in both cases, strong enough and not strong enough.

Reference form (the vector tests of §13 compare the tree implementation with it). The edge carries its one exclusion:

```kotlin
enum class Tail { STAR, ANY, EXACT }

/** `*` is MarkSlot.Star(excluded = empty); a premise never has excluded marks. */
sealed interface MarkSlot {
    data class Star(val excluded: MarkSet) : MarkSlot     // *  or  *∖X
    data class Concrete(val mark: TaintMark) : MarkSlot
}

data class PathFact(val base: AccessPathBase, val path: List<Accessor>, val tail: Tail, val mark: MarkSlot)

/** A path edge `from → to` with its ONE exclusion (W1: Empty if no side has the STAR tail). */
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet)

/** The current conclusion: the fact, the exclusion of its edge, the layer of its edge. */
data class Conclusion(val fact: PathFact, val exclusion: ExclusionSet, val demand: Boolean)

private fun PathEdge.premiseAdmits(r: List<Accessor>): Boolean = when (from.tail) {
    Tail.EXACT -> r.isEmpty()
    else -> exclusion.admits(r)
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

fun concat(c: Conclusion, edge: PathEdge): EdgeOutcome {
    val from = edge.from
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
        shape.exclusion, c.demand || shape.demand))
}

fun compose(to: MarkSlot, c: MarkSlot): MarkSlot? = when (to) {
    is MarkSlot.Concrete -> to
    is MarkSlot.Star -> when (c) {
        is MarkSlot.Star -> MarkSlot.Star(to.excluded + c.excluded)
        is MarkSlot.Concrete -> if (c.mark in to.excluded) null else c
    }
}

/** Step 6 (W2). */
fun normalize(f: PathFact, exclusion: ExclusionSet, demand: Boolean): Conclusion {
    if (f.tail != Tail.STAR || (f.mark is MarkSlot.Star && !demand)) return Conclusion(f, exclusion, demand)
    return Conclusion(f.copy(tail = Tail.ANY), ExclusionSet.Empty, demand = true)
}
```

`ExclusionSet` is a finite set: Empty or Concrete. An empty Concrete set must not exist (return `Empty`). Keep the
excluded accessors as a CANONICAL (sorted, de-duplicated) `IntArray` of `AccessorIdx`; the same for `MarkSet`. The edge
trees are keyed by both, so two equal sets must be equal values.

### 4.2 Apply a micro edge

A micro edge is an edge of a statement or call summary (`interpreter.md`). It applies to EVERY fact on a touched base
that overlaps its premise: both cases of §4.1. Example: the fact `(a, ., *, {}, *)` and the micro edge
`(a, .f, *) → (b, ., *)` of `b = a.f` give `(b, ., [any], {}, *)` in the demand layer (`Cases.lean`).

The statement transfer of one conclusion `c` (Lean: `transfer`):

* If `c.base` is not touched: the result is `c` (`Sequent.Unchanged`).
* Otherwise: the union of `concat(c, e)` over all micro edges `e`, then the field limit (§4.4). A touched base keeps only
  what an edge regenerates. That is the kill.

A call binding edge (caller base to callee base, callee exit base to caller base) is a micro edge too (§5).

Every micro edge is precise and complete (S1, S2): a statement edge, a call binding and an alias edge. The field limit
never applies to a micro edge: a micro edge keeps its full paths, of any length. The limit
applies to the RESULT, after the micro edge is applied to the propagated edge (§4.4; Lean: `transfer` limits the
results, and `Program.WF` puts no bound on a micro edge).

A micro edge has NO LAYER. The layer is a property of the propagation edge, and only the operations of this spec change
it: the case `above` of §4.1 and a lost correlation (`lostCorr`), the cut (§4.4), W6, a conjunction with an input that
is demand or that its literal does not cover (§4.6), and the `part` rows of the cleaner that give a demand result (an
all-marks cleaner, or a cleaned concrete mark; §4.7). A demand input gives a demand result. The interpreter sets no
layer. A negated mark literal counts as true for a source, a sink and a pass rule; this is the expected
over-approximation of a path-insensitive engine, as the conjunction (F49). Positive literals on different facts make a
conjunction for a source or a pass rule (§4.6) and a vulnerability with a set of facts for a sink. A cleaner applies
only its decided part (§4.7, `interpreter.md` §4.2).

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

`applySummary(a, j, g) = concat(a, j → g)`, with the layer of the summary edge added and the normal form. The caller
fact `a` must SATISFY the premise `j`:

* RUN 1: `j` covers `a` (strong enough):

  ```
  applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j.tail = [any] ⇒ a.tail = [any])
  ```

  The application is the case `below`, and the mark gate passes (`applicable_mark`). The abstraction of run 1 covers
  every added fact (A1, §6.1). Lean: `coversB`, `applicable`, `applicable_sound`.
* RESTRICTED RUN: the premise lies INSIDE the fact as LOCATIONS (the location part of `a` covers every location of
  `j`, marks ignored), and the premise mark admits the fact mark. Lean: `satI`. (Comparing the marks in both directions
  would reject a concrete fact against a `*`-premise record, which disables record reuse: `RCore.satI_markSub` and
  `satI_conc_record` show that `satI` accepts these cases, `satIold_markSub_fails` and `satIold_conc_record_fails` that
  the old form rejects them.) This is the reverse of run 1: the emitted fact is `a ∩ D-c` (§6.3), so it always lies inside
  its added fact (`RCore.emitM_satI`), and it can be smaller than `a` at the same path. The overlap test (`satO`) is
  sound too, but a precise fact then reads the demand-layer summaries of a coarser sibling premise, and a false demand
  vulnerability can survive every run (a review argument, not modelled).

The mark condition makes the mark gate pass: a summary application never raises a request (`Coverage.summary_step`,
`RCov.sat_step`, `RCore.summary_stepR`). A summary conclusion `*∖X` stops a caller fact whose concrete mark is in `X`
(§4.1 step 5). In a restricted run the CALLEE restricts the summary by its demand edges before it publishes it (§6.4).

* The exclusion of a summary edge FILTERS the delta: the summary `(arg0, ., *) → (ret, ., */{f})` applied to the bound
  caller fact `(arg0, ., */{})` gives `(ret, ., */{f})` (bound back to the lhs `r`), and applied to
  `(arg0, .f.g, $, T)` gives nothing.
* A partial overlap is never applied in run 1. Another initial fact of run 1 serves it.

### 4.4 The field limit

A run has the field limit `L`. After each operation that can make a path longer (the statement transfer, the summary
application), the analyzer applies `limit_L` to the result. It never applies it to a micro edge or a summary edge
before the application:

* If the path has at most `L` counted accessors, the fact does not change.
* Otherwise, cut the path before the `(L+1)`-th counted accessor. Uncounted accessors before that point stay in the
  prefix. The tail becomes `[any]`, the exclusion Empty, the mark stays, and the edge goes to the demand layer.

Lean: `cutPath`, `limitF`; `limitF_sound` (the cut only enlarges). There is no `[any]` depth charge and no fact-depth
gate: the field limit is the only depth bound. Each run may have its own limit (`RCov.iteration_sound`).

### 4.5 Mark gate and mark request (run 1 only)

A rule that needs a concrete mark `T` (a sink, a conditional source, a mark-specific pass rule, a conjunct of an ND
rule, a cleaner on a partly cleaned fact) on a fact with the mark `*` (or `*∖X`, `T ∉ X`) gives no fact for `T`: it
raises the REQUEST `(m, i, T)` on the premise `i` of the fact. If the rule dropped the fact without a request, the flow
would be lost; if it applied the rule anyway, every mark would pass the rule.

A request STANDS for the whole run. On every added fact `a` of `m` that overlaps `i`, also an added fact that arrives
later:

* If `a.mark = T`: ANSWER (bidirectional-task.md §4). If `a` is exact at `i.path`, emit `(i.base, i.path, $, {}, T)`.
  Otherwise emit `(i.base, i.path, i.tail, {}, T)`. It starts per §6.5: a `*` tail starts as `[any]` in the demand layer;
  a `$` tail stays `$` in the normal layer. The chain is never deeper than the request.
* If `a.mark` is `*`, or `*∖X` with `T ∉ X`: PROPAGATE to every caller edge `(ic → c)` that produced `a`: raise the
  request `(caller, ic, T)` (Lean: `climbsB`). A fact whose mark excludes `T` does not propagate it.

One answer does not stop the request. The answered initial facts are initial facts like every other: callers read their
summaries (§5). Lean: `answerInit`, rules `answer`, `reqUp`; `answerInit_covers`, `answerInit_applicable`.

Requests exist ONLY in run 1. A restricted run is concrete (§6.3): no request is raised there, and no answer is made
(`RCov.no_reqR`, `RExact.DR_no_request`, `RMain.no_request_M`). The mark that a rule needs is already in the demand
edge.

### 4.6 Mark conjunction: ND edges

A CONJUNCTIVE micro edge `x1.ρ1.$(T1) ∧ … ∧ xk.ρk.$(Tk) → z.π.$(T)` gives the mark `T` at `z.π` if every literal holds at
the statement. The interpreter makes it for a rule with several mark literals (`interpreter.md` §4).

* Each fact `c` at the statement that satisfies a literal `j` (it covers `xj.ρj` and has the mark `Tj`) is stored,
  STANDING for the run, per (rule, statement, literal), with the premise set of its edge (`{}` for the zero premise,
  `{i}`, or the ND set).
* When a fact arrives, it is combined with the stored facts of the other literals: one fact per literal, every
  combination. The result `(z, π, $, T)` has the UNION of the premise sets. Its size decides the edge: 0 gives a
  zero-to-fact edge, 1 a fact-to-fact edge, 2 or more an ND edge.
* The result is in the demand layer if one input is demand or its literal does not cover it (`!coversB lit f`: the input
  has a location that is not the literal location, for example an `[any]` input). Lean: `ND.conjLayer`,
  `ND.Example.c3_normal`. A normal-layer result is exact against the support semantics (`NDExact.nd_edge_exact`, S9).
* The engine is path-insensitive: the stored facts are per statement, not per execution path, so the literals can hold
  on paths that exclude each other (`if c then a := srcA else b := srcB; r := f(a, b)`). This is the EXPECTED
  over-approximation, not a demand step. The reference semantics of a conjunction (`ND.TaintN`, below) is
  path-insensitive in the same way.
* A literal on a `*`-mark fact raises the request `Tj` (run 1, §4.5). In a restricted run every fact is concrete.
* An ND edge propagates through micro edges with its premise set unchanged. Its conclusion is uncorrelated (`$` or
  `[any]`; W7): a `*` tail is the correlation with ONE premise.
* At a call, the callee sees an ordinary added fact. A callee summary `j → g` applied to an ND caller edge keeps the
  caller's premise set. A callee ND summary `{j1, …, jk} → g` needs one caller fact per premise at the call statement,
  each satisfying its `jm` (§4.3); it is standing too: the caller fact that arrives last completes it. The result has the
  union of the caller facts' premise sets. It is in the demand layer if the summary or one caller edge is (`ND.ndBind`).
* ND edges are never complete records (never persisted, never reversed). The backward run treats a conjunctive edge as
  an OR of its requirements, which over-approximates the demand.
* The concrete semantics of a conjunction is a SUPPORT semantics: a location is tainted at a node together with the
  list of entry locations that its derivation needs (`ND.TaintN`); a vulnerability witness is a tree.

Lean: `ND.lean` (§10.6).

### 4.7 The cleaner

A cleaner `clean(position, reach, mark)` at a statement removes the mark `T` (or every mark) from the locations of its
position `x.p`. The reach is `exact` (`x.p` only), `below` (everything strictly below `x.p`, the position `x.p.*`) or
`atAndBelow`. Concretely, a location keeps its value unless the cleaner cleans it (Lean: `Cleaner`, `cleansB`,
`Flow.clean`).

The cleaner compares the location set of a fact `c` with the cleaned locations (marks ignored): `inside` (every location
is cleaned), `disjoint` (none is) or `part` (otherwise; the safe default). Lean: `cleanPos`.

| `c.mark` | cleaner mark | `inside` | `disjoint` | `part` |
|---|---|---|---|---|
| `*` or `*∖X` | `T` | `c` with `*∖(X ∪ {T})` | `c` | `c` with `*∖(X ∪ {T})`, and the request `T` on the premise of `c` (run 1; not needed if `T ∈ X`, where the model raises it anyway, which costs work only) |
| `*` or `*∖X` | every mark | dropped | `c` | `c` normalised in the demand layer: a `*` tail becomes `[any]` (F45) |
| `T` (cleaned) | `T` or every mark | dropped | `c` | the part that is not definitely cleaned: an `[any]` fact at `x.p` under a `below` cleaner becomes `(x, p, $, T)`; otherwise `c` in the demand layer |
| `T'` (not cleaned) | `T` | `c` | `c` | `c` |

Lean: `cleanRes`, `addEx`, `concPart`.

So the cleaner SPLITS a `*`-mark fact by the mark. The edge `*∖{T}` propagates every mark except `T`, exactly, in the
normal layer. The mark `T` goes through the cleaner only on the concrete answer of the request, which the cleaner cleans
exactly (except on `[any]`, which is in the demand layer anyway). The union of the two covers every real flow
(`Core.cleanRes_sound`, `Coverage.coverage`); a normal-layer result denotes only real flows (`Exact.cleanRes_exact`).

* A summary conclusion `*∖X` stops a caller fact with a concrete mark in `X` (§4.1 step 5). A sink for `T ∈ X` on a
  `*∖X` fact neither triggers nor requests (§4.9). A request for `T ∈ X` does not climb through a `*∖X` fact (§4.5).
* The mark exclusion is not tied to a position, so a field write, a field read or a cut does not change it. (Today's
  `DeepAccessorExclusion` is tied to an abstraction point at a depth; it is lost when the path is cut at the field
  limit.)
* A definitely cleaned fact needs no request: the `T` path would only make a fact that the cleaner drops.
* In a restricted run every fact is concrete (`RExact.DR_concrete`, for any records): only the rows with a concrete mark
  apply, and no `*∖X` fact arises. A reused run-1 record with a `*∖X` conclusion gives a concrete mark on a concrete
  fact, or nothing (§4.1 step 5).
* The interpreter places the cleaner (`interpreter.md` §5): at a call to a cleaner method, on the caller facts that enter
  the callee, on the facts of an unresolved call before its pass rules, and in the summary rewriter on the summary
  results.
* `clean` is unconditional. Of a cleaner with a condition, the interpreter applies only the part that the cleaned fact
  decides: `ContainsMark(P, T)` with an action that removes `T` at `P` is the unconditional `(P, exact, T)`
  (`interpreter.md` §4.2). Where the condition is not decided, the cleaner does not act. Cleaning there is unsound.

### 4.8 The type filter

A type filter `filter(b, may)` at a statement drops a fact on the base `b` whose path cannot exist on a value of the
static type of `b`. `may` is a predicate on paths. Contract (S5):

* `may` accepts every path that a real value of the static type can have;
* `may` is PREFIX-CLOSED: `may(p ++ q) ⇒ may(p)`.

Then a fact that covers a real location has a path that `may` accepts (its path is a prefix of the location's path), and
the filter never drops it (`Core.filt_keeps`). The filter checks the fact's path only: a `*` or `[any]` tail is kept
whole, as today (an Accept keeps the whole subtree). Lean: `Instr.filt`, `Flow.filt`, rule `filt`; `Program.WF.filtPrefix`.

Exactness holds for VALID locations only: a fact that passes a filter can still denote locations below its path that
the filter rejects (`Exact.CexFilt`), and those locations do not exist. So the exactness theorem is stated for the end
locations that every filter accepts (`Exact.edge_exact_valid`, `closed_exact_valid`, `Closed.closed_records_exact_valid`).
The validity predicate must also go back along the micro edges (`Exact.BackOK`): a valid end location of a micro edge
comes from a valid start location. A confirmation (§4.9) needs a sink pattern whose locations are valid
(`Confirmed.confirmed_real_valid`; `Confirmed.CexConfFilt` shows that the condition is necessary).

The interpreter places the filters: the statement pre-filter on the touched bases (a cast narrows its operand; a field
access checks the declaring class; an array access needs an array type), the call bindings with the caller-side types,
the result binding with the type of the left-hand side, the method start with the context type, the pass rules with the
declared signature (`interpreter.md` §5). The mark policy (a concrete mark on a primitive value) is NOT a type filter: it
reads the mark, the model has no mark filter, and it can drop a real flow, so it is outside S5 (`interpreter.md` G6). Today's two summary-side filters (the caller content under a callee `*`, and the exit compatibility filter) are not
part of the AP in version 5: dropping a filter only adds facts, so this is sound and costs precision
(`interpreter.md` D13, D14, Q3). The backward run does not type-filter.

### 4.9 Sink check and confirmation

A sink checks the pattern `s = (v, ρ, $ or [any], T)`. For an edge `(i, layer) → f`:

* If `f` and `s` do not overlap: no effect.
* If `f.mark = *∖X` with `T ∈ X`: no effect (the mark was cleaned).
* If the effective mark of `f` is concrete (`f.mark = T'`, or an abstract `f.mark` and `i.mark = T'`): the sink is
  TRIGGERED if `T' = T`.
* If `f.mark` and `i.mark` are abstract: raise the REQUEST `(m, i, T)` (run 1).

This covers bidirectional-task.md §2: `(x,.,$,T)` triggers, `(x,.f,$,T)` does not, `(x,.,[any],T)` triggers,
`(x,.,*,{},*)` raises the request `T`. Lean: `check`, `check_sound`, `check_request_star`.

A triggered vulnerability is CONFIRMED only if all three hold:

1. the sink edge is complete;
2. its premise is the zero fact or an EXACT concrete fact `(x, p, $, T)`: a request answer in run 1, an emitted fact in
   a restricted run;
3. the premise is SUPPORTED: it is the zero fact of an entry method, or a normal-layer caller edge of a supported premise
   produced, through a normal binding, the zero fact (for the zero premise) or the exact added fact `a`, and the premise
   IS that added fact (same base, same path): the answer of `a` in run 1, the emission `a ∩ D-c = a` in a restricted run.
   The weaker condition "the premise is exact" is not enough (`Confirmed.weak_support_gap`, a proved counter-example).

Every other triggered vulnerability is a DEMAND vulnerability. `Confirmed.confirmed_real_valid` (run 1) and
`RMain.confirmed_real_M_valid` (every restricted run; support `SupM`; the satisfaction `satI`) prove that a confirmed
vulnerability is real, for a sink pattern whose locations are valid (§4.8). The forms without the validity condition
(`confirmed_real`, `confirmed_real_M`) are for programs without type filters (`FiltUp`).

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
| CALLER (the method that contains the call) | the subscriptions: (caller edge, call statement, added fact) | binds each caller fact into the callee (micro edges); applies every published summary edge of the callee whose premise its added fact satisfies (§4.3); binds back; applies the field limit |
| CALLEE (the called method) | the added-fact set (with the caller edges that made each added fact), the demand edges of the method, the emission, its initial facts, its edges and summaries, its requests (run 1) | emits the initial facts for each added fact (§6); analyses them; restricts each new summary edge by its demand edges (restricted runs, §6.4) and then PUBLISHES it to the subscribers; answers and propagates its requests (§4.5) |

### 5.3 Call processing

For a caller edge `(i, layer) → c` at a call:

0. If `c.base` is not touched: pass `c` (call-to-return).
1. BIND: for each binding edge `e` into the callee, `a = concat(c, e)` (a micro edge, §4.2).
2. ADD `a` to the added set of the callee, with the caller edge (for request propagation), and SUBSCRIBE.
3. The callee EMITS the initial facts for `a` (§6): in run 1 the most abstract fact, in a restricted run the emission
   `a ∩ D-c` for each demand edge of the callee. Each new initial fact is analysed.
4. APPLY: every published summary edge of every initial fact that `a` satisfies, the existing ones and the ones that
   arrive later (the subscription stands for the whole run); every persisted complete record whose premise `a`
   satisfies (§8.7). Then the binding edges back and the field limit.

The result layer is the caller layer, or the summary layer, or a demand step of the application.

---

## 6. Runs and abstraction

### 6.1 Contracts

The abstraction selects the initial facts for an added fact `a` of method `m`. It is a function of `m`, `a` and
constants of the run (the field limit, the demand). It must not depend on the order of events.

```
(A1)  run 1:            applicable(α(m, a), a)
(A2)  restricted run:   for every demand edge d of m, every CONCRETE added fact a and every location l (with its
                        mark) that D-c and a both cover, the emission emit(D-c, a) gives an initial fact j that
                        covers l, and a satisfies j
(A3)  restricted run:   the emitted fact has the mark of the added fact
```

The coverage theorem of run 1 needs only (A1). The coverage theorem of a restricted run needs (A2) for the added facts
of the run (`EmitContractOn`), the satisfaction contract (§4.3) and the restriction contract (§6.4). (A3) makes every
added fact of a restricted run concrete (`RCov.concInvR_all`, `RExact.DR_concrete`), so (A2) covers all of them
(`RCov.emitOn_of_conc`).

### 6.2 Run 1

* The zero fact is served by the zero fact.
* Every other added fact `a` is served by the most abstract fact `(a.base, [], *, {}, *)`.

Lean: `policy1`, `policy_applicable` (A1). The caller gets the marks back through the summary application: a `*`-mark
premise passes the mark of the caller fact through. A sink, a mark-specific rule or a cleaner inside the callee gets the
mark through a request (§4.5). Run 1 is the ONLY run with requests.

### 6.3 Restricted run: the emission

For the added fact `a` of method `m`, for each demand edge of `m` with the entry pattern `D-c = (b, p, t, M)`, emit
`a ∩ D-c`: the part of `a` that `D-c` covers, with the mark of `a`. The demand mark is a demand for that mark.

| `D-c` mark | `a` mark | result |
|---|---|---|
| `T` | `T` | emit |
| `T` | `T' ≠ T` | nothing |
| `T` | `*` | nothing; it never occurs (no `*` fact in a restricted run) |
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
* (A2) holds for concrete added facts (`RCore.emitM_contract_I`); it fails for a `*`-mark added fact under a `T` demand
  (`emitM_not_full_any`, for every satisfaction), and there is none.
* NO REQUEST. The root starts from the zero fact, every emitted fact copies a concrete mark, a concrete-mark premise has
  only concrete-mark conclusions, and a run-1 record applied to a concrete fact gives a concrete result. So every fact of
  a restricted run has a concrete mark, no final fact has the `*` tail (`RExact.final_not_star`), and no request rule can
  fire (`RExact.DR_no_request`). Condition: a restricted run has no callee summary with a `*` premise except persisted
  run-1 records; the interpreter makes no precomputed `*`-premise summary (`interpreter.md` §3).
* The zero fact. A demand that covers the zero location with the zero mark emits the zero fact itself.
* Precision. An exact added fact gives an exact concrete initial fact; its edges are in the normal layer, and a
  vulnerability under it can be confirmed (§4.9). A fact cut to `[any]` gives an `[any]` premise in the demand layer.
* Cost. There is NO SHARING: one initial fact per distinct added fact (path, tail, mark). The demand bounds which
  methods are analysed and the chain prefix, but NOT the number of contexts below an `[any]` demand chain; the spec sets
  no cap. Nothing below a forward field-limit cut can be confirmed until a later forward run has a larger limit; the
  driver must grow the forward limit as well as the backward one.

Programs 1 and 2 (§0.3): with this emission the forward run 3 reports both vulnerabilities, with the agreed
restriction (`RCases.p1_found_M`, `p2_found_M`). Program 1:

```java
root():  x.g.h.f.k.z = source();  c(x);      // (x, .g.h.f, [any], T) after the cut
c(x):    y = x.g.h;  m(y);                    // c gets (x, .g.h.f, [any], T); then (y, .f, [any], T)
m(arg):  sink(arg.f.k.z);                     // m gets (arg, .f, [any], T) ∩ (arg, .f.k, [any], T)
                                              //       = (arg, .f.k, [any], T): the sink triggers
```

Reference form:

```kotlin
/** §6.3. The part of the added fact `a` that the demand entry pattern `d` covers, with the mark of `a`. */
fun emit(d: PatternFact, a: PathFact, aExclusion: ExclusionSet): InitialAp? {
    if (d.base != a.base) return null
    if (d.mark is MarkSlot.Concrete && d.mark != a.mark) return null   // a T demand needs the fact mark T
    val p = d.path
    val q = a.path
    return when {
        q.size > p.size && q.startsWith(p) ->                             // below: the fact itself
            if (d.tailAdmits(q.drop(p.size))) InitialAp(a.base, q, a.tail, aExclusion, a.mark) else null
        q == p -> {                                                        // at: the meet of the tails
            val (tail, excl) = meet(a.tail, aExclusion, d.tail, d.exclusion)
            InitialAp(a.base, p, tail, excl, a.mark)
        }
        p.startsWith(q) ->                                                 // above: the demand chain and tail
            if (tailAdmits(a.tail, aExclusion, p.drop(q.size))) InitialAp(d.base, p, d.tail, d.exclusion, a.mark)
            else null
        else -> null
    }
}

/** §4.3. The fact `a` satisfies the premise `j`. */
fun satisfies(j: InitialAp, a: PathFact, aExclusion: ExclusionSet, restricted: Boolean): Boolean =
    if (!restricted) applicable(j, a, aExclusion)                          // run 1: a inside j
    else coversLocations(a, aExclusion, j) && markAdmits(j.mark, a.mark)   // restricted run: j inside a
```

### 6.4 Summary restriction (restricted runs, in the callee)

The CALLEE restricts each summary edge `S = (S-p → S-c)` by each of its demand edges `d` (entry pattern `D-c`, exit
pattern `D-p`) BEFORE it publishes the result `R = (R-p → R-c)` to the subscribers:

* `R-p := S-p` if `S-p` and `D-c` overlap (a common location, marks ignored); else no result.
* `R-c := concat(D-p, delta(S-c, D-p))`, by the position of `S-c` against `D-p`:

| `S-c` against `D-p` | `S-c` tail | `R-c` |
|---|---|---|
| at or below (`S-c.path = D-p.path ++ r`), the tail of `D-p` admits `r` | any | `S-c` |
| at or below, the tail of `D-p` does not admit `r` | any | no result |
| above (`D-p.path = S-c.path ++ r`) | `[any]` | `(D-p.path, [any])`, or `(D-p.path, $)` if `D-p` has the `$` tail |
| above | `*/E` | no result (as agreed); it never occurs in a restricted run (no `*` final tail) |
| above | `$` | no result |
| apart, or another base | | no result |

* No `D-p` (the demand does not reach the method exit): no result.
* One summary edge can be restricted by several demand edges. The subscribers get every result (the union).
* `R` has the layer and the mark of `S`. The restriction only removes pairs (`RCore.restrictU_sub`).
* In a restricted run the agreed rule gives the same run as the version-3 repair `restrictS`, whose contract holds
  (`RExact.restrict_U_eq_S`, `RCore.restrictS_contract`).

Reference form:

```kotlin
/** §6.4. Restrict the summary conclusion `sc` of the premise `sp` by the demand edge `d` (in the callee). */
fun restrict(sp: InitialAp, sc: Conclusion, d: DemandEdge): Conclusion? {
    val dp = d.exit ?: return null                           // the demand does not reach the exit
    if (!overlap(sp, d.entry)) return null                   // R-p: all of S-p or nothing
    if (sc.fact.base != dp.base) return null
    val p = dp.path
    val q = sc.fact.path
    return when {
        q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null     // at or below D-p
        p.startsWith(q) -> when (sc.fact.tail) {                                // above D-p
            Tail.ANY -> sc.copy(fact = sc.fact.copy(path = p,
                tail = if (dp.tail == Tail.EXACT) Tail.EXACT else Tail.ANY), exclusion = ExclusionSet.Empty)
            else -> null                     // `*`: as agreed, never occurs in a restricted run; `$`: no overlap
        }
        else -> null
    }
}
```

### 6.5 The start fact

| initial fact `i` | start conclusion | layer |
|---|---|---|
| `(x, p, *, {}, *)` | `(x, p, *, {}, *)` (identity) | normal |
| `(x, p, *, E, T)` | `(x, p, [any], {}, T)` (W2) | demand: the `~` premise |
| `(x, p, [any], m)` | `(x, p, [any], {}, m)` | demand |
| `(x, p, $, m)` | `(x, p, $, {}, m)` | normal |

Lean: `startFact`, `startFact_sound`.

### 6.6 The run sequence and the report

* Run 1 is `D` with `policy1`. Run k+1 (forward) is `DR` with the demand `dem k` that the backward run between them
  gives, any field limits, any persisted records (Lean: `RCov.runSeq`).
* The backward run between forward run k and forward run k+1 must satisfy the contract B (§10.7): every vulnerability
  witness that the summaries of forward run k carry stays demanded.
* Every forward run reports every real vulnerability (`RMain.iteration_sound_M`). So stopping at any forward run is
  sound; a demand vulnerability of a forward run that the next forward run does not report is REFUTED; the report of the
  analysis is the confirmed vulnerabilities plus the demand vulnerabilities of the last forward run.

---

## 7. Representation (the optimization)

The concept of a conclusion is a set of path facts. The representation groups path edges into TREES.

### 7.1 Initial fact

```kotlin
enum class ApTail { STAR, ANY, EXACT }

/** The initial fact (premise): one linear path. Its mark is * or a concrete mark (never *∖X). */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,       // interned, linked from the root; no [any], $ or mark accessors (W4, W5)
    val tail: ApTail,
    val exclusion: ExclusionSet,   // Empty in run 1; a restricted run can emit the exclusion of a `*/E` demand
    val mark: ApMark,
)

/** The key of an analysis context: the premise (or the premise set of an ND edge) and the layer. */
data class PremiseKey(val initials: List<InitialAp>, val demand: Boolean)   // empty list: the zero fact
```

`PathNode` is the current `AccessPath.AccessNode` without the `[any]`, `$` and mark accessors.

### 7.2 Conclusion trees

One tree per (premise key, layer, exclusion, mark exclusion). The exclusion and the mark exclusion belong to the tree; a
`*` leaf is a flag.

```kotlin
/** A set of marks: the abstract mark flag plus sorted concrete mark ids. */
class MarkSet(val star: Boolean, val concrete: IntArray)

/** Payload of one trie node at path p. */
class Payload(
    val star: Boolean,      // the leaf p.* with the tree exclusion and the tree mark *∖X (W2)
    val any: MarkSet,       // the leaves p.[any] with these marks (the star flag is *∖X of the tree)
    val exact: MarkSet,     // the leaves p.$ with these marks
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
    val demand: Boolean,           // the layer; a demand tree has no * leaf (W2)
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
* T5. Inside one DEMAND tree, an `[any]` leaf with the mark `m` at `p` may absorb every leaf with the mark `m` below
  `p`. The denotation does not change. A normal tree has no `[any]` leaf (W6).
* T6. Share one empty payload; intern payloads, mark sets and exclusion sets.

### 7.3 Delta-concat on a tree

The computation of §4.1 on all paths of one tree at once. The results are grouped by their new (layer, exclusion, mark
exclusion):

1. Walk `from.path` from the root. On each proper prefix node, read its payload as the case `above`: `*` and `[any]`
   leaves give `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer.
2. At the node of `from.path` take the subtree `S`. Filter its root by the premise tail and the edge exclusion.
3. Transform `S` by the target tail. For a `*` target: the child subtrees (`r ≠ []`) keep the tree exclusion and are
   re-rooted under `to.path`; the root `*` leaf (`r = []`) gets the exclusion `Ec ∪ E`, so it goes to another tree.
   `[any]` and `$` targets fold `S` into one uncorrelated payload with the Empty exclusion.
4. Apply the mark gate per payload mark, then the target mark (§4.1 steps 4, 5; a `*∖X` target adds `X` to the mark
   exclusion and stops the concrete marks in `X`).
5. Apply the field limit with `boundedDepth`; cut paths go to the demand tree.
6. Route each result by its own layer bit.

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `S` only. The concept form visits every path
fact (`Tree.lean`: `applyTreeE_mem`, `applyTreeE_den`, `walkSteps_le`).

### 7.4 The restriction on a tree

The restriction of §6.4 applies to all conclusions of one summary tree at once (`RStore.restrictTree`):

1. Walk `D-p.path` from the root. On each proper prefix node: drop the `*` flag (the agreed rule; a restricted run has no
   `*` leaf); move the `[any]` marks to `D-p.path` (as `$` for a `$` exit pattern); drop the `$` marks and every child
   off the chain.
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
| `TaintSinkTracker` (rule assumptions), vulnerability records | The standing conjunction store (§8.9); add the confirmed/demand state (§8.10). |
| `TreeInitialFactAbstraction` | Replace by §6.2 (run 1) and §6.3 (restricted runs). |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used (§4.4). |

---

## 8. Storages

Every store has a CONCEPT (a list of records with a filter) and an INDEX. `Store.lean` and `RestrictedStore.lean` prove
that each index returns every record that the filter returns, and give the cost of the lookup. Lifetime: RUN = one run
(one direction, one limit); PERSISTENT = all runs of one analysis. The OWNER of each store is the method that §5.2 names.

### 8.1 Method edge store (RUN, per method)

* Key: `(statement, premise key, layer, base, exclusion, mark exclusion)`. Value: an `EdgeTree`.
* `add(...)` merges by rule 1 or 2 and returns the delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer: a conclusion is dropped if a stored conclusion of the same premise key and layer
  subsumes it (`Subsume.subsumesB`): the same base; the same mark, or a mark exclusion that is a subset; `[any]` at `p`
  subsumes every fact at or below `p`; `*/Es` subsumes `*/En` at the same path if `Es ⊆ En`. `subsumes_sound` proves
  that every pair of the dropped fact is a pair of the stored fact.
* An incomplete conclusion never subsumes a complete one (`Subsume.recordSubsumesLB_layer` for records).
* Unchanged propagation (`Sequent.Unchanged`) may skip the store, as today.
* Queries for the trace resolution (phase 5): `edgesAt(stmt, premise?)`, `edgesAt(stmt, pattern)`. The store of the
  last forward run stays until the trace resolution ends.

### 8.2 Initial fact store (RUN, per method; callee)

* `initials: Map<InitialAp, Status>`, `Status ∈ {analysing, done}`, with the flags `allComplete`, `hasRequest` and
  `supported` (§4.9).
* `uses: Map<InitialAp, Set<(callee, InitialAp)>>`: the callee initial facts that serve the calls inside each initial
  fact (for the closed marker, R5).

### 8.3 Added fact store (RUN, per method; callee)

* A path trie keyed by `base :: path`, with the caller edges `(caller method, caller premise key, layer, call statement)`
  that produced each added fact.
* The standing request match (§4.5) reads it with OVERLAP queries; the subscription (§5.3 step 4) with SATISFIES
  queries: `lookupPrefixes ++ lookupExtensions` of the query path.

### 8.4 Subscription store (RUN; caller)

* Key: the callee. Value: the caller records `(caller edge, call statement, added fact a)`.
* On a published summary edge of an initial fact `j`: find the subscribed `a` that satisfy `j` (§4.3), and apply.
* On a new subscription: apply every published summary edge of every initial fact that `a` satisfies.

### 8.5 Run summary store (RUN, per method; callee)

* Key: `(premise key, layer, exit kind)`. Value: the exit `EdgeTree`s.
* In a restricted run, each new summary edge is restricted by every demand edge of the method (§6.4); the results are
  PUBLISHED to the subscription store.
* Complete summary edges go to the persistent record store at the end of the run (§8.7).
* The summary edges on the paths of the vulnerabilities are the input of the next run in the other direction (§8.6).

### 8.6 Demand store (RUN, read only; callee)

* Content: the demand edges of the method, in the orientation of this run: the entry pattern `D-c` and the exit pattern
  `D-p` or none. The previous run (the other direction) gives them: the edges of that run on the paths from the
  vulnerabilities of the run before it, incomplete edges, reversed complete records and the zero edges (§9, contract B).
* Index: a path trie keyed by `base :: D-c.path`.
* The query `near(q)`: the prefix walk of `q`, then the subtree strictly below the node of `q`. It returns the same
  records as the list filter "the chain is not apart from `q`" (`RStore.near_equiv`, `near_sound`).
* Emission query (§6.3), for the added fact `a`: `near(a.path)`. It returns every demand edge for which the emission
  gives a fact (`RStore.emit_complete_M`, `emit_lookup_equiv_M`). For a `$` added fact the prefix walk alone is enough
  (`emitM_exact_prefix`).
* Restriction query (§6.4), for the summary premise `j`: `near(j.path)` (`restrict_complete_U`,
  `restrict_lookup_equiv_U`; the same for the version-3 form `_S`).
* Cost (`near_query_cost`): at most `|q| + 1` nodes for the walk, plus `Σ |rel|` over the returned chains strictly below
  `q`, against `|demand edges|` tests in the list form. The bound "walk + number of results" is FALSE for the plain trie
  (`deep_chain_cost`); a path-compressed (radix) trie gives it.

### 8.7 Persistent complete record store (PERSISTENT)

One direction-neutral store for the forward and the backward analysis:

```kotlin
/** A complete summary edge, in the orientation in which it was derived. */
class CompleteRecord(
    val method: MethodKey,
    val direction: Direction,          // FORWARD: premise = entry fact; BACKWARD: premise = exit fact
    val premise: InitialAp,
    val conclusion: EdgeTree,          // normal layer; may carry a mark exclusion
)

interface CompleteRecordStore {
    fun add(record: CompleteRecord)
    fun byEntry(method: MethodKey, callerFact: InitialAp): Sequence<CompleteRecord>
    fun byExit(method: MethodKey, requirement: InitialAp): Sequence<CompleteRecord>
    fun markClosed(method: MethodKey, direction: Direction, initial: InitialAp, limit: Int, vulns: List<VulnerabilityRecord>)
    fun closed(method: MethodKey, direction: Direction, fact: InitialAp): ClosedInitial?
}
```

Rules:

* R1. Only complete edges are added. ND edges are never added.
* R2. `byEntry` is a path trie keyed by `base :: entry path`, `byExit` by `base :: exit path`. In run 1 the lookup is
  `lookupPrefixes(base :: q)` and then the `applicable` filter (`forward_equiv_prefixes`, `applicable_mem_candidatesB`,
  `extension_half_redundant`). In a restricted run the satisfaction reads the premise inside the fact, so the lookup
  needs the extension half.
* R3. A reader in the other direction applies the reversal of §9.1. Every complete record whose premise has the Empty
  exclusion and that is mark-reversible reverses exactly (`Reverse.rev_exact_of_empty_premise`).
* R4. Adding complete records to a later run IN THE SAME DIRECTION is always sound: a complete edge of run 1 or of a
  restricted run is exact (`Exact.edge_exact_valid`, `RExact.recs_of_DR_valid`, `recs_of_D_valid`; for programs
  without type filters `Exact.edge_exact`, `recs_of_DR`, `recs_of_D`), so it adds no false pair (rule `retRec`). A
  conjunction result with fewer than two premises can be a record; its exactness is `NDExact.nd_edge_exact`.
* R5. CLOSED marker: in its run the initial fact reached the fixed point, raised no request, had only complete edges, and
  every initial fact that serves a call inside it is closed (the greatest fixed point over recursion, computed with
  `uses`). In run 1 its records are then exactly the concrete flow from its location set to the exit
  (`Closed.closed_records_exact_valid`; without type filters `closed_records_exact`). In a restricted run they are exact
  and cover every DEMANDED flow from its location set (`RExact.closed_exactR_valid`; without type filters
  `RMain.closed_records_exactM`).
* R6. A closed marker is valid for every later run with a limit at least the limit of the run that set it (argued).
* R7. Strict demand: in a restricted run, records never cause an emission.
* R8. A demand edge whose entry pattern is an initial fact `j` that was CLOSED IN RUN 1 is served by the records of `j`
  when `j` and the added fact have the same locations (`j` covers the added fact, and the added fact satisfies `j`,
  §4.3): the abstraction emits nothing for this demand edge (`closed_records_exact`, `summary_step`; argued for the
  composition). In practice only the zero fact and exact facts meet it.

### 8.8 Request store (RUN 1 only, per method; callee)

* Records: `(method, initial fact, mark)` plus the answers already emitted. A request stands for the whole run (§4.5).
* Index: a path trie keyed by `method :: base :: path` of the request initial fact. On every new added fact, find ALL
  requests that overlap it (`standing_complete`); answer or propagate each one.

### 8.9 Conjunction store (RUN, per method)

* Records: `(rule, statement, literal) → set of (fact, premise key)`: the facts that satisfy a literal of a conjunctive
  micro edge (§4.6), standing for the run (today's `TaintSinkTracker` assumptions).
* On a new fact for a literal: combine with the stored facts of the other literals (one per literal, every
  combination); the results have the union of the premise keys.
* The same for ND summaries at a call statement: `(callee summary, premise index) → caller facts`.

### 8.10 Vulnerability store (PERSISTENT)

* Key: `(rule, statement)` as today. The value keeps today's fields (trigger position, initial-fact groups,
  `EndFactRequirement`, rule assumptions) and adds the state (confirmed or demand) and the run.
* A CONFIRMED vulnerability (§4.9) persists: it is real.
* Every FORWARD run reports every real vulnerability (§6.6). A demand vulnerability of a forward run that the next
  forward run does not report is REFUTED. The report of the analysis is the confirmed vulnerabilities plus the demand
  vulnerabilities of the last forward run. The vulnerabilities of a backward run only make its demand.

---

## 9. Reversal and the backward direction

### 9.1 Reversal of a record

The reversal `rev(i, f)` (Lean: `revEdge`) reads a record from the other side. The new premise is the old conclusion;
the exclusion goes to the NEW CONCLUSION, so the new premise has the Empty exclusion:

| `i.tail` | `f.tail` | new premise tail | new conclusion tail |
|---|---|---|---|
| `*` | `*/E` | `*` | `*/E` |
| `[any]` | `*/E` | `*` | `*/E` |
| `$` | `*/E` | `$` | `$` |
| `$` | `$` | `$` | `$` |
| `*` | `$` | `$` | `[any]` |
| `[any]` | `$` | `$` | `[any]` |
| `$` | `[any]` | `[any]` | `$` |
| `*` | `[any]` | `[any]` | `[any]` |
| `[any]` | `[any]` | `[any]` | `[any]` |

The new premise mark is `i.mark` if `f.mark` is abstract (`*` or `*∖X`), else `f.mark`. The new conclusion mark is
`f.mark` (`*` or `*∖X`) if it is abstract, else `i.mark`. The reversal needs a MARK-REVERSIBLE record (`MarkRev`); a
mark-producing record under a `*`-mark premise has no reversal (`no_rev_of_star_conc`). With the Empty premise exclusion
every row is exact (`rev_exact_of_empty_premise`). A complete edge of a restricted run has an EXACT premise
(`RExact.complete_premise_exact`), so every mark-reversible complete record of every run reverses exactly.

### 9.2 The backward run

The backward analysis uses the same facts, operations, storages and primitives. Only the meaning of a mark and the
roles of the rules change (`interpreter.md` §4.9):

* A backward fact is a REQUIREMENT: "if a location of this set carries `T` here, a sink is reached".
* The backward premise is at the method exit; the backward summary edge ends at the method entry.
* The statement transfer applies the REVERSED micro edges (§9.1), with an identity edge for a target base that the
  statement does not touch (`Reverse.Stmt.rev`; `revNoId_breaks`). A call is reversed (`Reverse.Call.rev`): the
  backward binding into the callee is the converse of the forward binding back (`r.* → return.*`, `ai.* → argi.*`,
  `S.* → S.*`); the backward binding back is the converse of the forward binding into the callee (`argi.* → ai.*`,
  `S.* → S.*`, `zero.* → zero.*`), so a backward zero fact at a callee entry goes up to its callers. A cleaner and a type filter are their own reversal (`Reverse.Program.rev`; the backward run does
  not type-filter).
* SEEDS. A backward run places its seed DIRECTLY at every sink statement where an earlier forward run reported a
  vulnerability: `Zero → (sink statement, requirement)`. So a sink in code that never returns is seeded too.
* The ZERO DEMAND. A requirement that reaches a source continues to the zero fact (the reversed source edge), and the
  zero fact goes up through the reversed zero bindings. So every method between a source and the sink gets the demand
  edge whose entry pattern is the zero fact, and the next forward run emits the zero fact there.
* Every backward run is a restricted run (the first one, backward-2, follows forward-1). It is concrete too.
* The backward run between forward run k and forward run k+1 must satisfy the contract B (§10.7).

The backward run is the closure on the reversed program. `Reverse.flow_rev_iff_calls` proves that its flow is the
converse flow, with calls, cleaners and filters, if every micro edge and every call binding has an exact shape and is
mark-reversible (`RevStmts`, `RevCalls`); `backward_of_forward_calls` applies the forward coverage theorem to it.

---

## 10. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

### 10.1 Soundness of run 1 — `Coverage.lean`

Hypotheses: the program is well-formed (`Program.WF`: every micro edge reads from a touched base; call bindings are
mark-agnostic; every type filter is prefix-closed) and the abstraction satisfies (A1).

| Theorem | Statement |
|---|---|
| `coverage` | If the value at the entry location `l0` of method `M` flows to `l` at node `n` (`Flow`: statements, calls, call-to-return, cleaners, type filters, nested callee flows), and the initial fact `i` of `M` covers `l0`, then the analysis has an edge `(i → f)` at `n` with `den(i, f)(l0, l)`, OR the request `(M, i, l0.mark)`. |
| `coverage_conc` | If `i` has a concrete mark, the first case holds. |
| `reach_strong`, `vuln_found` | If the zero location of an entry method flows through any chain of calls to a location that a sink pattern covers (`Reach`), the analysis reports the vulnerability at that sink. |
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
| `answerInit_covers`, `answerInit_applicable`, `policy_applicable` | The answer covers the requested location and is applicable; the run-1 policy satisfies (A1). |
| `SharedExcl.applyEdge_shared_excl`, `den_shared_excl` | ONE exclusion per edge. |

### 10.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`

| Theorem | Statement |
|---|---|
| `Exact.edge_exact_valid`, `closed_exact_valid` | Under S7 (`MarkWF`) and with a validity predicate that every filter accepts (`FiltValid`) and that goes back along micro edges (`BackOK`): every pair of a normal-layer edge whose end location is valid is a concrete flow. |
| `Exact.edge_exact`, `complete_exact`, `closed_exact` | The same for filters that keep every extension of an accepted path (`FiltUp`; with prefix-closure this makes a filter constant, so this form is for programs without type filters). |
| `Exact.CexFilt`, `CexMark` | The two hypotheses are necessary: a filter lets a fact pass whose lower locations do not exist; a `*`-premise edge with a concrete target forgets a cleaned mark. |
| `Exact.cleanRes_exact` | A normal-layer result of the cleaner denotes only pairs of the input whose end location the cleaner keeps. |
| `Closed.closed_records_exact`, `closed_records_exact_valid` | R5: no request on the initial fact and only normal exit edges ⇒ the records are exactly the concrete flow from its location set. |
| `Invariant.final_star_legal`, `final_star_abstract` | W2: a `*` conclusion has the mark `*` or `*∖X` and is in the normal layer. |
| `Invariant.no_univ_star` (+ `no_univ_needs_*`) | S8 ⇒ no `*/Universe` edge fact; each hypothesis is necessary. |
| `Invariant.demand_of_any_ok` | W6 is a layer refinement. |
| `star_final_keeps_initial_excl`, `star_initial_complete`, the demand-monotone lemmas | A final `*/Ec` under an initial `*/Ei` keeps `Ei ⊆ Ec`; under `*/Ei` a normal-layer final fact has the `*` tail or `Ei = {}`; the demand layer never goes back. |
| `Confirmed.confirmed_real_valid`, `confirmed_real` | A CONFIRMED vulnerability (§4.9) is a real concrete vulnerability (valid form; `MarkWF ∧ FiltUp` form). `CexConfFilt`, `CexConfMark`: both hypotheses are necessary. |
| `Confirmed.weak_support_gap`, `rev2_not_confirmed` | The weaker support condition admits a false positive; the review counter-example is not confirmed. |

### 10.4 Concept against optimization — `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean`

| Theorem | Statement |
|---|---|
| `Tree.insert_mem`, `fromList_mem` | The `EdgeTree` (one premise, layer, exclusion and mark exclusion; `*` leaves are flags) holds exactly its path edges. |
| `Tree.rule1_mem`, `rule1_den`, `rule2_den`, `rule2_mark` | Merge rule 1 is exact; merge rule 2 (exclusions, and mark exclusions) is exact for EQUAL trees; counter-examples for different trees and for a union. |
| `Tree.applyTreeE_mem`, `applyTreeE_den`, `applyTreeE_grouped_key`, `applyTreeE_mx`, `applyTreeE_inv`, `applyTreeE_star_normal` | For a `*`-to-`*` micro edge with the mark `*` on both sides (not the mark gate or the cut of §7.3): the tree form of delta-concat equals the per-path form, fact and layer; output trees have distinct keys and keep the mark exclusion. |
| `Tree.fromList_size`, `fan_list`, `fan_tree`, `prepend_shares`, `walkSteps_le`, `applyListC_spec` | Cost of the tree representation. |
| `Store.*` | The record, request and demand indexes return every record that the concept filter returns; lookup cost. |
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
from the emission and a demand edge), `ret` (a summary edge only through a restriction by a demand edge, and only for a
satisfied premise), and `retRec` (persisted records). A DEMANDED flow (`FlowR`, `ReachR`) is a concrete flow whose every
call step has a demand edge of the callee: `D-c` covers the entry location with its mark, and `D-p` covers the exit
location. The coverage and iteration theorems are generic over the rules, given the contracts `EmitContractOn`,
`SatContract` and `RestrictContract`.

| Theorem | Statement |
|---|---|
| `RCore.emitM_contract_I`, `emitM_copies`, `satI_contract`, `emitM_satI`, `emitM_inter`, `emitM_complete`, `emitM_shape`, `emitM_chain_strong` | The spec emission satisfies (A2) for concrete added facts and copies the mark (A3); the emitted fact is exactly `a ∩ D-c`, lies inside its added fact, and has the chain of the fact or the demand chain. |
| `RCore.satI_markSub`, `satI_conc_record`, `satIold_*` | The satisfaction compares locations, and the premise mark against the fact mark: a cleaned fact reads a `*` premise, a concrete fact reads a `*`-premise record; the version-4 form failed both. |
| `RCore.emitM_not_full_any` | (A2) fails for a `*`-mark added fact under a `T` demand, for every satisfaction: the concreteness of the run is necessary. |
| `RCov.concInvR_all`, `added_concR`, `no_reqR`, `RExact.DR_concrete`, `DR_no_request`, `final_not_star`, `RMain.no_request_M` | A restricted run with a mark-copying emission is CONCRETE: every initial fact, edge and added fact has a concrete mark, no final fact has the `*` tail, and the run has NO request (also with cleaners). |
| `RExact.restrict_U_eq_S`, `RCore.restrictU_eq_S_nonstar`, `restrictS_contract` | In a concrete run the agreed restriction gives the same run as the version-3 repair, whose contract holds. |
| `RExact.complete_premise_exact`, `complete_rev_exact` | A complete edge of a concrete run has an exact premise, so its record reverses exactly. |
| `RCases.p1_found_M`, `p2_found_M`, `p1_reachR_M`, `p2_reachR_M` | Programs 1 and 2 are reported by forward run 3 with the agreed restriction. |
| `RCov.coverageR`, `reach_strongR`, `vuln_foundR` | THE COVERAGE OF A RESTRICTED RUN: for a demanded flow from a covered entry location, an edge covers the pair or the run has the request; its own summaries demand the same flow. |
| `RCov.coverageD`, `reach_to_reachR`, `vuln_foundD` | Run 1 reports every real vulnerability, and its summaries demand its witness. |
| `RCov.iteration_sound`, `iteration_sound_conc`, `RMain.iteration_sound_M`, `iteration_sound_M_identity` | THE ITERATION THEOREM: if every backward step satisfies the contract B (`BackwardContract`: every vulnerability witness that the summaries of forward run k demand stays demanded), EVERY forward run reports every real vulnerability; any field limits, any records. |
| `RCov.backward_identity`, `backward_of_superset`, `RMain.noSink_contract`, `everyWitness_contract_fails` | The identity backward step satisfies B; B is about sink witnesses only. |
| `RExact.edge_exactR_valid`, `closed_exactR_valid`, `recs_of_DR_valid`, `recs_of_D_valid` (valid locations); `edge_exactR`, `complete_exactR`, `recs_of_DR`, `recs_of_D`, `closed_exactR`, `RMain.closed_records_exactM` (`FiltUp`) | Exactness and record reuse in restricted runs. |
| `RExact.SupM`, `ConfirmedM`, `confirmed_realM_gen`, `confirmed_realM_gen_valid` (every satisfaction with `SatMark`); `RMain.confirmed_real_M`, `confirmed_real_M_valid` (the spec rules) | A confirmed vulnerability of a restricted run is real; the support accepts the emitted exact fact. |
| Version 3 (record): `RCore.emitS_contract`, `emitU_fails`, `restrictU_fails`; `RCases.p1_lost_U`, `p2_lost_U`; `RMain.iteration_sound_S` | The location-only rules: the agreed rows lose programs 1 and 2. |

---

## 11. What the proofs do not cover

* The concrete semantics is alias-free and location-level (S1–S8).
* The theorems are about the closures `D`, `DR` and `DN`. A real run differs from them by optimizations. Each one keeps
  the soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§8.1) | the dropped pairs are pairs of the kept fact (`subsumes_sound`) | the local step is proved; the composition is argued |
| merge rules 1 and 2, also for marks (§3.3, T1, T2, T2') | exact (`rule1_mem`, `rule2_den`, `rule2_mark`, `merge_inter`, `merge_mark_inter`) | proved |
| the T5 fold | the denotation does not change | argued |
| persisted complete records (R4) | a complete edge has no false pair; adding edges keeps coverage (rule `retRec`) | proved |
| a demand edge served by run-1 closed records (R8) | `closed_records_exact`, `summary_step` | the local steps are proved; the composition is argued |
| W6 (`[any]` always demand) | a layer refinement (`demand_of_any_ok`) | proved per fact; the run is argued |

* The contract B of the backward run (§10.7) is an assumption of the iteration theorem. That the real backward run
  satisfies it is argued: it is a restricted run on the reversed program; the model has no rule for an unbalanced return,
  so the mirrored coverage theorem is not machine-checked. The seeds and the zero demand (§9.2) are part of B.
* ND edges are modelled for run 1 (`DN`): coverage, the vulnerability theorems (§10.6) and the exactness of the normal
  layer against the support semantics `TaintN` (`NDExact`, under S9) are proved. The CONFIRMATION of a vulnerability
  through a conjunction is NOT proved. No ND edge is a record (§4.6). A restricted run with ND edges is ARGUED, not
  modelled:
  1. its facts are concrete, so a literal never raises a request (§4.5);
  2. the callee restricts an ND summary `{j1, …, jk} → g` by a demand edge `d` as a single-premise summary (§6.4): the
     result keeps the whole premise list if one `jm` overlaps `D-c`, and `R-c` follows the table of §6.4; the
     restriction only removes pairs from the conclusion;
  3. the contract B for a TREE witness (`ND.ReachAll`) needs a demand edge on every node of the tree. The backward run
     reads a conjunctive edge as an OR of its literals (§4.6), so a requirement at the conclusion reaches every branch.
  `D_sub_DN` embeds the distributive part, so the iteration theorem holds unchanged for a program without conjunctions.
* `ND.lean` keeps premise LISTS with the zero premise `[zeroFact]`; this spec keeps SETS and drops the zero premise. So
  `[zero, i]` is an ND edge in the model and a fact-to-fact edge here. Every ND theorem holds for the list form. A
  conjunction result with fewer than two premises is an ordinary edge in the spec, so it can be a record if it is
  normal; it is exact (`NDExact.nd_edge_exact`, for every premise list).
* The Kotlin reference form of §4.1 and the Lean `applyEdge` differ on a `$`-premise micro edge with a `*` target (on an
  `[any]` fact Lean gives `$`, Kotlin `[any]` in the demand layer). The interpreter makes no such edge
  (`interpreter.md` I7), so the difference is not reachable.
* With a `$` premise at `r = []` on a `*` fact, Lean gives `*/Universe` where the table of §4.1 and the Kotlin form give
  `$` or `*/(Ec ∪ E)`; and `AFact.norm` maps `*/Universe` to `$` where §4.1 step 6 says `[any]`. Under S8 this case
  does not occur: the mark gate raises a request first (`Invariant.no_univ_star`).
* The interpreter (`interpreter.md`) is outside the model, except through S1, S2, S5, S7, S8 and S9. Its known gaps are
  listed in `interpreter.md` §0.1. The reading of a negated mark literal as true (S1) is not modelled: the model has no
  rule conditions.
* Exceptions are out of scope for now (F51): no exception flow crosses a call, and a catch block does not read `exc`
  (`interpreter.md` §3.4, G1).
* The tree theorems cover the `*`-to-`*` micro edges with the mark `*` on both sides; other micro edges use the per-path
  operation on the touched subtree. The mark gate and the field limit inside the tree (§7.3) and the T5 fold are not
  modelled in `Tree.lean`.

---

## 12. The formal model

| File | Content |
|---|---|
| `Basic.lean` | All definitions of run 1: locations, facts (marks `*`, `T`, `*∖X`), `den`, `applyEdge` with `markComp`, the normal form, the field limit, statements, calls, cleaners (`Cleaner`, `cleanPos`, `cleanRes`), type filters, `Flow`, the closure `D`, `Reach`, `answerInit`, `policy`, `revEdge`. |
| `Restricted.lean` | The restricted runs: demand edges, the emission `emitM`, the satisfaction `satI`, the restriction `restrictU`, the closure `DR`, `FlowR`, `ReachR`, the contracts, `summaryDemand`, `BackwardContract` (and the version-3 rules). |
| `ND.lean` | ND edges: conjunctive micro edges, the support semantics `TaintN`, the closure `DN`, the ND coverage and vulnerability theorems. |
| `NDExact.lean` | The exactness of normal-layer ND edges against `TaintN` (`LitConc` = S9, `ConjOK`), with the two counterexamples. |
| `Cases.lean`, `RestrictedCases.lean` | Test vectors (`decide`), programs 1 and 2. |
| `Core.lean`, `SharedExcl.lean`, `RestrictedCore.lean` | The local lemmas. |
| `Coverage.lean`, `RestrictedCoverage.lean`, `RestrictedMain.lean` | Soundness of run 1 and of the iteration; the instantiation with the spec rules. |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `RestrictedExact.lean` | Exactness, invariants, closed reuse, confirmed vulnerabilities. |
| `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean` | Concept against optimization. |
| `Reverse.lean` | Reversal. |

Build and audit:

```
cd spec/lean && rm -rf .lake/build/lib/lean/ApSpec* && lake build > build.log 2>&1
grep "depends on axioms" build.log | sed 's/.*axioms: //' | sort | uniq -c
grep -c "does not depend on any axioms" build.log
```

(A build prints the audit only for the modules that it compiles, so remove the old `ApSpec` build files first.)

The audit passes when the only sets are `[propext]` and `[propext, Quot.sound]` (and declarations with no axioms).
At the time of writing: 639 audited declarations (309 `[propext, Quot.sound]`, 273 `[propext]`, 57 with no axioms), no
`sorry`, no `native_decide`, no `Classical`, and 305 `example` vectors checked by the kernel, almost all by `decide`
(83 in `Cases.lean`, 127 in `RestrictedCases.lean`, 18 in `RestrictedStore.lean`, 24 in `Reverse.lean`, 13 in
`Store.lean`, 20 in `Subsume.lean`, 20 in `Tree.lean`), plus the derivations of the counterexample and example
programs.

---

## 13. Test plan (TDD)

Write the tests first. Each test names the spec item that it checks. The interpreter tests are in `interpreter.md` §7.

1. Vector tests (`ApplyEdgeVectorsTest`): one test per `example` in `Cases.lean` and `RestrictedCases.lean`, on the
   concept implementation (§4.1 reference form) and on the tree implementation. The F16 vectors, and the §4.2 vector
   `a = b.f` on a normal-layer `(b, ., [any], {}, *)`, show the model result: an `[any]` result in the normal layer. The
   implementation applies W6, so the test asserts the same fact in the demand layer (`Invariant.demand_of_any_ok`).
2. Equivalence property test (`EdgeTreeEquivalenceTest`): random path facts and micro edges; the tree result denotes the
   same pairs as the concept result, layer and mark exclusion included. The same for the tree restriction (§7.4).
3. Layer tests: a cut fact is demand; an `[any]` result is demand (W6); a demand input gives a demand output; a `*`
   conclusion is never in the demand layer; a `*` fact applied above a premise gives a demand result.
4. Mark tests: every row of the mark gate and of the result mark (§4.1 steps 4, 5); a `*∖X` summary conclusion stops a
   caller fact with a mark in `X`; a sink for `T ∈ X` neither triggers nor requests; a request for `T ∈ X` does not
   climb.
5. Cleaner tests: every row of the table of §4.7; the split (`*∖{T}` plus the request, then the concrete answer cleaned
   exactly); the all-marks cleaner; a cleaned fact through a field write past the field limit keeps its mark exclusion.
6. Type filter tests: a fact on an accepted path passes, also with a `*` tail; a fact on a rejected path is dropped; the
   predicate is prefix-closed.
7. ND tests: a conjunction from two facts of different premises gives the union premise set; the last arriving fact
   completes it; an ND summary needs one caller fact per premise; ND conclusions have no `*` tail. Today's
   `ExampleTest.test nd rule` as an analysis test.
8. Merge tests: rules 1, 2 and 2'; a union of exclusions or mark exclusions is never made.
9. Request tests (run 1): the mark gate raises a request; a standing request is answered by a later added fact and by a
   second added fact; propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain. In a
   restricted run, a request is a bug (assert it).
10. Call and ownership tests: the four steps of §5.3; the callee restricts before it publishes; a caller reads the
    summaries of every premise its fact satisfies.
11. Abstraction tests: run 1 emits the most abstract fact; every row of the two tables of §6.3; the emitted fact is
    exactly `a ∩ D-c` with the mark of `a`; the same result for two insertion orders.
12. Restriction tests: every row of the table of §6.4; the union over two demand edges; no result without `D-p`.
13. Iteration tests: programs 1 and 2 as analysis tests with a forward limit 3 and a backward limit 2; the vulnerability
    is reported in every forward run. A worker loop with a sink that never returns (§9.2).
14. Store tests: index completeness against a list filter (records, demand edges, requests, conjunctions); the closed
    marker only for all-complete initial facts without requests.
15. Reversal tests: every row of §9.1, also with `*∖X`; the forward record and its reversed reading give converse results
    on the same concrete pair.
16. Analysis tests (phase 2 gate): the existing `*AnalysisTest` suites, run with `cleanTest`; `DeepCleanSummaryAnalysisTest`
    and the cleaner suites for §4.7. A lost finding is a test whose message says that no vulnerability reached the sink;
    read the message, do not count failures.

---

## 14. Decision log

Each line comes from a failed proof, a counter-example checked by `decide`, a review comment, or the design discussion. The `UD` lines are design decisions of the user from version 2 (the `D` numbers of `interpreter.md` are its
deviations).

| # | Topic | Outcome |
|---|---|---|
| F1 | "No `[any]` ⇒ complete" | Changed: the demand layer (`~`, `Zero~`), set by the AP operations of §4.2 (F50). |
| F2 | Read builder | Adopted: a read never changes an exclusion. |
| F3 | One static base per class | Withdrawn: the class accessor stays. |
| F4 | Abstraction determinism | Adopted (§6.1). |
| F5 | Requests for mark-specific rules | Adopted (§4.5). |
| F6 | Callers of an answered initial fact | A caller reads every summary whose premise its fact satisfies. |
| F7 | Reversed records instead of an analysis | Replaced by the strict demand (R7, R8) and the iteration theorem. |
| F8 | Reversal shapes | Exact for every mark-reversible record with the Empty premise exclusion (§9.1). |
| F9 | Normal form | Adopted (§4.1 step 6). |
| F10 | Exclusion of a reversed record | On the new conclusion (§9.1). |
| F11–F12 | Store indexes | Path index; `base :: path` keys (§8). |
| F13 | `applicable` | Run 1; a restricted run uses `satI` (F36). |
| F14 | Answer by the meet | Withdrawn: the answer keeps the request chain. |
| F15 | Mark of the emitted fact | Run 1: `*`; a restricted run: the mark of the added fact (F34). |
| F16 | `lostCorr` | A `$` result without a lost restriction stays normal. For an `[any]` result F41 replaces it. |
| F17 | Standing requests | Adopted (§4.5). |
| F18 | Conclusion subsumption | `subsumesB`, with mark exclusions (§8.1). |
| F19 | Closed marker | No request (R5). |
| F20 | Identity edges of rules | `interpreter.md`. |
| F21 | Zero fact | Run 1: the zero fact; restricted: a zero demand emits the zero fact. The zero fact passes over every call and enters the callee by its binding. |
| UD1 | Exclusion | Per path edge, shared; merge rules 1 and 2; no union merge. |
| UD2 | Call processing | The four steps (§5.3). |
| F22 | Confirmation | A normal-layer support chain (§4.9). |
| F23 | Approximating rules | Replaced by F50: the interpreter sets no layer. A condition that one fact does not decide is the expected over-approximation; a cleaner applies only its decided part. |
| F24 | Rule-2 delta | Merge rule 2 propagates the whole merged tree (T4). |
| F25 | Fold | Only inside demand trees. |
| UD4 | Record subsumption | Inside the complete layer. |
| UD5 | Strict demand | Run 1 unrestricted; later runs follow the demand; soundness is iteration-relative under B. |
| F26 | One edge exclusion | The tables use one exclusion `E` per edge. |
| F27, F28, F29 | Version-3 repairs | Superseded by F34: a restricted run has no `*` fact. |
| F30 | Records in restricted runs | Exact; added when the caller fact satisfies the premise; only run-1 closed records replace an emission (R8). |
| F31 | Report rule | Every forward run reports every real vulnerability. |
| F32 | Backward contract | About sink witnesses only. |
| F33 | Zero demand | The backward run continues a requirement through the reversed source edge to the zero fact. |
| F34 | Mark-aware emission | `a ∩ D-c` with the mark of `a`. |
| F35 | No request after run 1 | A restricted run is concrete (`no_request_M`). |
| F36 | Satisfaction in a restricted run | `satI`: the premise lies inside the fact as locations, and the premise mark admits the fact mark (the version-4 form compared marks both ways and disabled record reuse: `satIold_conc_record_fails`). |
| F37 | Support in a restricted run | `SupM` accepts the emitted exact fact. |
| F38 | Backward seeds | Directly at the sink statements of the reported vulnerabilities (non-returning code). |
| F39 | Split ap.md / interpreter.md | The AP and its primitives here; the IR interpretation in `interpreter.md`. |
| F40 | Universe | Removed from the AP; it never occurs under S8 (`no_univ_star`). |
| F41 | `[any]` layer (W6) | Every `[any]` conclusion is demand; "complete" = normal layer; a layer refinement (`demand_of_any_ok`). |
| F42 | Micro edge vs summary edge | A micro edge applies unguarded (both cases); a summary edge only to a satisfying fact. |
| F43 | Ownership | The caller owns the subscriptions; the callee owns the added facts, the demand, the emission, and restricts before it publishes. |
| F44 | Cleaner | The mark slot `*∖X` (the user's design): the cleaner splits a `*` fact by the mark; the request gives the concrete `T` path; positional only for all marks; exact for every other mark. Replaces `DeepAccessorExclusion` (lost at a field-limit cut). |
| F45 | Cleaner all-marks branch | A partly cleaned `*` fact under an all-marks cleaner is normalised (`[any]`, demand): without it W2 failed (`Invariant` round 5). |
| F46 | Type filter | A prefix-closed predicate; exactness only for valid locations (`CexFilt`). |
| F47 | Mark well-formedness (S7) | A concrete target mark needs a concrete premise mark (`CexMark`, `CexConfMark`). |
| F48 | ND edges | Premise lists; uncorrelated concrete conclusions; standing conjunctions and ND summaries; never records; support semantics. |
| F49 | Conjunction layer | The layer of the inputs (demand also if the literal does not cover an input). Literals on exclusive paths are the expected over-approximation of a path-insensitive engine, not a demand step (the user's decision; it replaces the review-5 H1 proposal "always demand"). |
| F50 | Micro edges | Every micro edge (statement edges, call bindings, alias edges) is precise and complete (S1, S2). A micro edge has no layer: the layer is a property of the propagation edge, and only the AP operations change it. The field limit applies to the result of an application, never to a micro edge. |
| F51 | Exceptions | Out of scope for now. |
| F52 | `ExactAndAnyField` | `atAndBelow` is the meaning of the rule. The cleaner removes a mark only from a fact that lies inside the cleaned locations (§4.7); a partly covered fact is split or kept, so the cleaner never removes more than the rule says. |
| F53 | ND exactness | A normal-layer conjunction is exact against `TaintN` (`NDExact.nd_edge_exact`); it needs concrete literal marks (S9, `CexLit`). |
| F54 | Weak alias write | Kept (`interpreter.md` A3, G7): sound if an alias does not hold; a precision gap in the normal layer. |
