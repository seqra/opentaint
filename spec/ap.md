# Access paths and storages — specification

Status: design spec for phase 1 of [bidirectional-task.md](../bidirectional-task.md) ("New AP with all required
storages"), version 4. Version 2 came from the first design review. Version 3 added the runs that strictly follow the
demand. Version 4 makes the demand mark-aware: the emission is the part of the added fact that the demand covers, with
its mark (§7.3), and requests exist only in run 1 (§6.3, §6.4, §7, §11.7). The formal model is in [`spec/lean`](lean). Every theorem named here is
machine-checked and constructive (§12).

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

This spec defines:

* the fact representation (the access path, "AP") for the forward and the backward analysis;
* the operations on facts: statement transfer, call binding, summary application, summary restriction, field limit,
  rule checks, mark requests, abstraction, reversal;
* the storages that the analyzer uses in one run and across runs;
* the soundness theorems for these operations and the scope in which they hold.

This spec does not define the analyzer scheduling, the iteration driver or the trace resolution. It defines the
contracts that these parts use. The contract of the backward run is in §11.7.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | A statement is described by its summary: the bases that it touches and its micro edges (§4.2). | The summary builder (`JIRStatementSummary`, `GoStatementSummary`). |
| S2 | Aliasing is described by extra micro edges (gen edges to alias paths). The model itself is alias-free. | The alias analysis. |
| S3 | Formal parameters are not reassigned inside the method. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. | The CFG normalisation. |
| S5 | A type filter only removes facts that have no concrete instance. | The type checker. |
| S6 | The result of run 1 is the least fixed point of the rules of §4–§8 (Lean: the inductive predicate `D`). The result of a later run is the least fixed point of the restricted rules (Lean: `DR`, §6.4, §7.3). The worklist may compute it in any order. | The analyzer. |

Inside this scope:

* Run 1 is SOUND: an edge covers every concrete flow, and every concrete source-to-sink flow is reported (§11.1).
* A later run is SOUND RELATIVE TO ITS DEMAND: it reports every concrete vulnerability whose flow the demand covers,
  and it passes the same flow on as the demand of the next run (§11.7).
* With the contract of the backward run (B, §11.7), EVERY FORWARD run reports every concrete vulnerability
  (`RCov.iteration_sound`, `RMain.iteration_sound_M`). So stopping at any forward run is sound, and a vulnerability
  that a forward run does not report is not real. The model has forward runs only; a backward run is represented by
  its contract B.
* Inside the smaller scope of COMPLETE edges the analysis is also EXACT: every pair of a complete edge is a concrete
  flow, in run 1 and in every later run (§11.3, §11.7). A CONFIRMED vulnerability is a real one
  (`Confirmed.confirmed_real`, `RMain.confirmed_real_M`).

§11.6 lists the optimizations of a real run (subsumption, merges, the fold, record reuse) and why each one keeps the
soundness.

### 0.2 Decisions of the design review

The task text is the base. The reviews with the user refined it as follows (details in §14):

| Topic | Decision |
|---|---|
| Completeness | An edge is complete if it is in the normal layer and its conclusion has no `[any]`. Every approximation step moves the edge to the DEMAND layer (`~`, `Zero~`), also when the result has no `[any]`. |
| Exclusion | ONE exclusion per path edge, shared by premise and conclusion (§2.2, `SharedExcl.applyEdge_shared_excl`). Two merge rules (§3.3). A union of exclusions across different conclusions is forbidden. |
| Read | A field read never changes an exclusion. Only a field write does. |
| Statics | One `ClassStatic` base with the class accessor. A static write on the abstract static fact gives a demand that the abstraction resolves. |
| Calls | Four steps: apply the current summaries, add the fact to the callee, the callee abstraction emits per the demand, new summaries are applied (§6.2). A caller reads every summary whose premise its fact satisfies (§6.3). |
| Runs | Run 1 is unrestricted: it emits the most abstract facts (§7.2). Every later run STRICTLY follows the demand of the previous run: the emission `a ∩ D-c` with the mark of `a` (§7.3) and the summary restriction (§6.4). A restricted run is concrete: every fact has a concrete mark. |
| Satisfaction | Run 1: the premise covers the fact (strong enough). Restricted run: the premise overlaps the fact and its mark admits the fact mark (§6.3). |
| Requests | The task rule for the answer (no chain deeper than the request). Requests stand for the whole run. Mark-specific rules raise requests too. Requests exist ONLY in run 1: in a restricted run the demand edge carries the mark (§7.3). |
| Report | Every forward run reports every real vulnerability (with B). Confirmed vulnerabilities persist. A vulnerability is confirmed only through a normal-layer support chain (§8.1). A demand vulnerability that a later run does not report is refuted (§10.10). |

### 0.3 History of the strict-demand rules

Version 3 used location-only rules: the emission ignored the mark and emitted `*`-mark facts. The proofs found two
agreed rows that then lose a real flow (programs 1 and 2, §7.3, §6.4), and version 3 repaired them. Version 4 makes the
emission mark-aware (the user's rule). Then every fact of a restricted run has a concrete mark: no `*` mark and no `*`
final tail. Neither row can fire, and the agreed restriction stays as agreed; the emission table is replaced.

| Row | Version 3 | Version 4 |
|---|---|---|
| Emission: a `*` added fact above the demand chain | agreed "nothing" loses program 1 (`RCases.p1_lost_U`, `RCore.emitU_fails`); repaired | no `*` added fact exists; program 1 is reported (`RCases.p1_found_M`) |
| Restriction: a correlated `*` summary conclusion above `D-p` | agreed "no result" loses program 2 (`RCases.p2_lost_U`, `RCore.restrictU_fails`); repaired | no `*` conclusion exists; the agreed rule gives the same run as the repair (`RExact.restrict_U_eq_S`); program 2 is reported (`RCases.p2_found_M`) |

The cause of both version-3 losses: the field limit of the backward run cuts the demand of a caller and the demand of
its callee at different depths, and a `*` fact cannot carry the correlation across the cut. The model keeps the
version-3 rules and the counterexamples as the record of the review.

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
| exclusion | The set of first accessors that a `*` continuation must not start with: Empty, Concrete, or Universe. |
| fact | A tuple (base, path, tail, exclusion, mark). §2. |
| premise | The initial fact of an edge: the fact at the method start that the edge depends on. |
| conclusion | The final fact of an edge: the fact at a statement. |
| edge | (premise, layer, statement, conclusion), with one exclusion. The zero fact is also a premise. |
| layer | `normal` or `demand`. The demand layer of premise `i` is written `i~`; of the zero fact, `Zero~`. |
| complete edge | An edge in the normal layer whose conclusion has no `[any]` tail. |
| incomplete edge | Every other edge. |
| micro edge | One edge of a statement summary (`StatementSummary.Edge`). |
| summary edge, record | An edge whose statement is the method exit. A persisted complete summary edge is a record. |
| added fact | A caller fact rebased to the callee bases at a call site. |
| abstraction | The function that selects the initial facts for an added fact. §7. |
| request | A request for a concrete mark on an initial fact. §8. |
| run | One analysis pass in one direction with one field limit `L` (forward-1, backward-2, forward-3, ...). |
| restricted run | Every run after run 1. It strictly follows its demand. |
| demand edge | An edge of the previous run (the other direction) that a restricted run gets. In the orientation of the restricted run it has an entry pattern `D-c` and an exit pattern `D-p` (or none, if the demand does not reach the method exit). |
| demand (of a run) | The set of demand edges that a restricted run gets (§10.6). Not the same as the demand LAYER. |
| demand vulnerability | A triggered vulnerability that is not confirmed (§8.1). |
| strong enough | A fact is strong enough for a premise if the premise covers it (`applicable`, §6.3). Then the fact is at or below the premise (§4.1 case `below`). A fact at or below a premise that does not cover it (for example, another exclusion) is a partial overlap. |
| not strong enough | The fact is above the premise (§4.1 case `above`). The result loses the correlation. |
| satisfies | A fact satisfies a premise if the caller may apply the summary edges of that premise to it (§6.3). |
| concrete run | A run in which every fact has a concrete mark. Every restricted run is concrete (§7.3). |
| method key | `MethodEntryPoint` (context plus entry statement), as today. |

---

## 2. The fact (the concept)

### 2.1 The tuple

A fact is `(base, path, tail, exclusion, mark)`:

* `path` — the concrete accessors. It never contains `[any]`, a mark or `$`.
* `tail ∈ {*, [any], $}`.
* `exclusion` — only with the `*` tail.
* `mark ∈ {*, T}` — abstract (pass the mark of the premise through) or concrete.

### 2.2 Edges, layers and the edge exclusion

An edge is `(premise, layer) → (statement, conclusion)`. The zero-to-fact edge is `Zero → (layer, statement, fact)`.

* An edge has ONE exclusion `E`. The premise and the conclusion share it: for `(x, p, *) →_E (y, q, *)`, the value at
  `x.p.σ` flows to `y.q.σ` for every `σ` that `E` admits. It does not matter on which side the model stores `E`: only
  the union counts (`SharedExcl.applyEdge_shared_excl`, `den_shared_excl`).
* For an uncorrelated edge (the conclusion is `$` or `[any]`) the exclusion `E` restricts the premise continuation only.
  A `$` premise counts as `E = Universe`, an `[any]` premise as `E = Empty`.
* Every initial fact that run 1 emits has the Empty exclusion (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`). In a restricted run an emitted fact can carry the exclusion of the demand (the meet
  with a `*/E` entry pattern, §7.3); it has a concrete mark, so it starts in the demand layer and makes no complete
  record. So in practice the exclusion is a property of the conclusion. It grows only by a field write (a kill).
* The LAYER is part of the edge identity. An edge goes to the demand layer when a step of its derivation
  over-approximates (§4.4). It never goes back (`Invariant.applyEdge_demand_monotone` and the related lemmas).

Lean: `PFact` (a premise or a conclusion; the conclusion `*/E` carries the exclusion of the edge) and `AFact` (a
conclusion plus `demand : Bool`, the layer).

### 2.3 Well-formedness rules

| Rule | Text |
|---|---|
| W1 | An edge with no `*` side has the Empty exclusion. |
| W2 | A conclusion with the `*` tail has the mark `*` and is in the normal layer. A premise may have the `*` tail with a concrete mark (a request answer). |
| W3 | A path has at most `L` counted accessors in a run with the field limit `L` (§5). |
| W4 | `[any]` is a tail only. A path has no inner `[any]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. |

W2 holds for every derived fact, in run 1 and in every restricted run (`Invariant.final_star_legal`,
`RExact.final_star_legalR`).

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. A source rule is a micro edge from the zero fact (§4.2). Zero-to-fact
edges are edges with the zero premise, in the normal or the demand layer.

### 2.5 Classification

* COMPLETE edge: normal layer and no `[any]` in the conclusion (Lean: `AFact.complete`). Complete edges are persisted
  and reused in later runs and in the other direction (§10.7).
* INCOMPLETE edge: every other edge. Incomplete edges are used in their own run like every edge. They are never
  persisted and never reversed.
* A rule that assigns a mark on `[any]` makes an incomplete edge. That is intended. Such an edge cannot go away, so the
  driver stops when the demand no longer changes (not when it is empty).
* The DEMAND of a restricted run comes from the previous run in the other direction (§10.6): the edges of that run on
  the paths from the vulnerabilities of the run before it — incomplete edges, reversed complete records, and the zero
  edges (§8.5).

---

## 3. Denotation

### 3.1 Admitted continuations

`E.admits σ` is true if `σ = []`, or if the first accessor of `σ` is not in `E`. Universe admits only `[]`.

| Tail | As a premise, the continuations `σ` that it covers | As a conclusion, the relation of the premise continuation `σ` to its own continuation `τ` |
|---|---|---|
| `*/E` | all `σ` that `E` admits | `τ = σ` and `E` admits `σ` (CORRELATED) |
| `[any]` | all `σ` | any `τ` (not correlated) |
| `$` | `σ = []` | `τ = []` |

### 3.2 Location set and edge relation

```
covers(i, l)  ⇔  l.base = i.base ∧ l.path = i.path ++ σ ∧ σ admitted by i.tail ∧ i.mark admits l.mark

den(i, f)(l0, l1)  ⇔  l0.base = i.base ∧ l1.base = f.base
                    ∧ i.mark admits l0.mark ∧ l1.mark = out(f.mark, l0.mark)
                    ∧ ∃ σ τ. l0.path = i.path ++ σ ∧ l1.path = f.path ++ τ
                             ∧ σ admitted by i.tail ∧ (σ, τ) related by f.tail
```

with `admits(*, m)`, `admits(T, m) ⇔ m = T`, `out(*, m) = m`, `out(T, m) = T`.

`den(i, f)(l0, l1)` reads: "the value at `l0` on method entry flows to `l1` at the statement of the edge". Lean:
`PFact.covers`, `den`. The restriction reads a demand pattern as LOCATIONS without marks (`PFact.coversLoc`); the
emission and the demanded flows read the entry pattern with its mark (`PFact.covers`).

### 3.3 Exclusion algebra

* The edge exclusion is the union of what the model stores on the two sides (`SharedExcl.applyEdge_shared_excl`). The
  model stores it on the conclusion.
* `*/Universe` on a conclusion is the correlated empty continuation: `x.p` exactly flows to `y.q` exactly. It is not the
  same as `$` under a `*` premise: `$` there relates EVERY continuation of the premise to `y.q`.
* MERGE RULE 1: two edges with the same premise, the same layer and the same exclusion merge their conclusions (union).
* MERGE RULE 2: two edges with the same premise, the same layer and the same conclusion merge their exclusions by
  INTERSECTION: `admits(E1 ∩ E2, σ) = admits(E1, σ) ∨ admits(E2, σ)`. The union of the two relations is exact.
* A UNION of exclusions happens only along one derivation (a field write after another). A union across two
  different edges is FORBIDDEN: it removes pairs that one of the two edges has (`Subsume.union_loses_pairs`). (The
  current `EdgeNonUniverseExclusionMergingStorage` does that. It was sound only with the old refinement.)

Lean: `Subsume.merge_inter` (rule 2 is exact).

---

## 4. The core operation: `applyEdge` (delta-concat)

### 4.1 Definition

`applyEdge(c, from →_E to)` applies an edge `from → to` with the edge exclusion `E` to the conclusion `c` of a current
edge. `Ec` is the exclusion of the edge of `c`. The applied edge is one of:

* a statement micro edge (§4.2);
* a call binding edge: caller base to callee base, or callee exit base to caller base (§6);
* a callee summary edge `(premise j → conclusion g)` (§6.3).

All flow functions use this ONE operation. Lean: `applyEdge` in `Basic.lean`.

Step 1 — base. If `c.base ≠ from.base`, the result is empty.

Step 2 — position. Compare the paths:

* `below r`: `c.path = from.path ++ r`. The fact is at or below the premise: it is STRONG ENOUGH for the premise.
* `above r`: `from.path = c.path ++ r`, `r ≠ []`. The fact is above the premise: it is NOT STRONG ENOUGH. The result
  loses the correlation.
* `apart`: neither. The result is empty.

Step 3 — overlap and result shape.

Case `below r` (strong enough). The premise must admit `r`: `E` admits `r` for a `*` premise, `r = []` for a `$`
premise; an `[any]` premise admits every `r`. Then:

| `to.tail` | `r` | `c.tail` | result path | result tail | demand step |
|---|---|---|---|---|---|
| `*` | `≠ []` (`E` admits `r`) | any | `to.path ++ r` | `c.tail` (with `Ec`) | no |
| `*` | `[]` | `$` | `to.path` | `$` | no |
| `*` | `[]` | `*/Ec` | `to.path` | `*/(Ec ∪ E)` | no |
| `*` | `[]` | `[any]` | `to.path` | `$` if `E = Universe` | no |
| `*` | `[]` | `[any]` | `to.path` | `[any]` otherwise | yes if `E ≠ {}` |
| `[any]` | any | `*/Ec` | `to.path` | `[any]` | `lostCorr` |
| `[any]` | any | `[any]` or `$` | `to.path` | `[any]` | no |
| `$` | `[]` | `*/Ec` (and `from.tail = $`) | `to.path` | `*/Universe` | no |
| `$` | any | `*/Ec` (other) | `to.path` | `$` | `lostCorr` |
| `$` | any | `[any]` or `$` | `to.path` | `$` | no |

`lostCorr` is true if the correlation of `c` restricts the premise continuation: `Ec ∪ E ≠ {}` for `r = []`,
`Ec ≠ {}` for `r ≠ []`. Otherwise every premise continuation is admitted, and the uncorrelated result is exact
(`Exact.applyEdge_exact`).

Case `above r` (not strong enough). The fact tail must admit `r` (`*/Ec`: `Ec` admits `r`; `[any]`: yes; `$`: no
overlap). The result is not correlated:

| `to.tail` | result tail at `to.path` | demand step |
|---|---|---|
| `*` | `[any]` | yes, except `c.tail = [any]` and `E = {}` |
| `[any]` | `[any]` | yes if `c.tail ≠ [any]` |
| `$` | `$` | yes if `c.tail ≠ [any]` |

Step 4 — mark gate:

| premise mark | fact mark | result |
|---|---|---|
| `*` | any | apply |
| `T` | `T` | apply |
| `T` | `T' ≠ T` | empty (no overlap) |
| `T` | `*` | NO fact. Raise the request `T` on the premise of `c` (§8). |

Step 5 — result mark `out(to.mark, c.mark)`. The result is in the demand layer if `c` is, or if step 3 says "yes".

Step 6 — normal form. If the result has the `*` tail and (a concrete mark, or the demand layer), make it uncorrelated:
`*/Universe` becomes `$`, `*/E` becomes `[any]`, and the edge goes to the demand layer. Summary application applies the
same step after it adds the layer of the summary edge. The step only enlarges the fact (`CoreAux.norm_sound`).

Reference form (the vector tests of §13 compare the tree implementation with it). The edge carries its one exclusion:

```kotlin
enum class Tail { STAR, ANY, EXACT }

data class PathFact(val base: AccessPathBase, val path: List<Accessor>, val tail: Tail, val mark: ApMark)

/** A path edge `from → to` with its ONE exclusion (W1: Empty if no side has the STAR tail). */
data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet)

/** The current conclusion: the fact, the exclusion of its edge, the layer of its edge. */
data class Conclusion(val fact: PathFact, val exclusion: ExclusionSet, val demand: Boolean)

/** The continuations that the edge admits on the premise side (Lean `tailExcl` ∪ the conclusion side). */
private fun PathEdge.premiseExclusion(): ExclusionSet =
    if (from.tail == Tail.EXACT) ExclusionSet.Universe else exclusion

private fun ExclusionSet.admits(r: List<Accessor>): Boolean = r.isEmpty() || r.first() !in this

private class Shape(val path: List<Accessor>, val tail: Tail, val exclusion: ExclusionSet, val demand: Boolean)

/** The correlation restriction that an uncorrelated result forgets (Lean `lostCorr`). */
private fun lostCorr(c: Conclusion, e: ExclusionSet, r: List<Accessor>): Boolean =
    c.fact.tail == Tail.STAR &&
        (if (r.isEmpty()) c.exclusion.union(e) !== ExclusionSet.Empty else c.exclusion !== ExclusionSet.Empty)

/** Case `below r`: the fact is strong enough. */
private fun below(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    val e = edge.premiseExclusion()
    if (!e.admits(r)) return null                         // the premise admits r
    val to = edge.to
    val ck = c.fact.tail
    return when (to.tail) {
        Tail.STAR ->
            if (r.isNotEmpty()) Shape(to.path + r, ck, c.exclusion, demand = false)
            else when (ck) {
                Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, false)
                Tail.STAR -> Shape(to.path, Tail.STAR, c.exclusion.union(e), false)
                Tail.ANY ->
                    if (e === ExclusionSet.Universe) Shape(to.path, Tail.EXACT, ExclusionSet.Empty, false)
                    else Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = e !== ExclusionSet.Empty)
            }
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = lostCorr(c, e, r))
        Tail.EXACT -> when {
            ck == Tail.STAR && edge.from.tail == Tail.EXACT && r.isEmpty() ->
                Shape(to.path, Tail.STAR, ExclusionSet.Universe, false)
            ck == Tail.STAR -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, demand = lostCorr(c, e, r))
            else -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, false)
        }
    }
}

/** Case `above r` (r ≠ []): the fact is not strong enough; the result is uncorrelated. */
private fun above(c: Conclusion, edge: PathEdge, r: List<Accessor>): Shape? {
    val ck = c.fact.tail
    val admitted = when (ck) { Tail.STAR -> c.exclusion.admits(r); Tail.ANY -> true; Tail.EXACT -> false }
    if (!admitted) return null
    val to = edge.to
    return when (to.tail) {
        Tail.STAR -> Shape(to.path, Tail.ANY, ExclusionSet.Empty,
            demand = !(ck == Tail.ANY && edge.premiseExclusion() === ExclusionSet.Empty))
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = ck != Tail.ANY)
        Tail.EXACT -> Shape(to.path, Tail.EXACT, ExclusionSet.Empty, demand = ck != Tail.ANY)
    }
}

sealed interface EdgeOutcome {
    data object None : EdgeOutcome
    data class Fact(val conclusion: Conclusion) : EdgeOutcome
    data class Request(val mark: ApMark) : EdgeOutcome
}

fun applyEdge(c: Conclusion, edge: PathEdge): EdgeOutcome {
    val from = edge.from
    if (c.fact.base != from.base) return EdgeOutcome.None
    val p = from.path
    val q = c.fact.path
    val shape = when {
        q.size >= p.size && q.subList(0, p.size) == p -> below(c, edge, q.drop(p.size))
        p.size > q.size && p.subList(0, q.size) == q -> above(c, edge, p.drop(q.size))
        else -> null
    } ?: return EdgeOutcome.None
    if (!from.mark.isStar) {                                   // the mark gate
        if (c.fact.mark.isStar) return EdgeOutcome.Request(from.mark)
        if (c.fact.mark != from.mark) return EdgeOutcome.None
    }
    val mark = if (edge.to.mark.isStar) c.fact.mark else edge.to.mark
    val fact = PathFact(edge.to.base, shape.path, shape.tail, mark)
    return EdgeOutcome.Fact(normalize(fact, shape.exclusion, c.demand || shape.demand))
}

/** Step 6. */
fun normalize(f: PathFact, exclusion: ExclusionSet, demand: Boolean): Conclusion {
    if (f.tail != Tail.STAR || (f.mark.isStar && !demand)) return Conclusion(f, exclusion, demand)
    val tail = if (exclusion === ExclusionSet.Universe) Tail.EXACT else Tail.ANY
    return Conclusion(f.copy(tail = tail), ExclusionSet.Empty, demand = true)
}
```

Requirements on `ExclusionSet`: an empty `Concrete` set must not exist (make the constructor private and return
`Empty`), otherwise `!== ExclusionSet.Empty` gives a wrong layer; `Universe.contains(a)` is true; keep the excluded
accessors as a CANONICAL (sorted, de-duplicated) `IntArray` of `AccessorIdx`. The edge trees are keyed by the exclusion,
so two equal sets must be equal values.

### 4.2 Statement transfer and the summary builder

A statement summary is `(touched bases, micro edges)` (`StatementSummary`). The transfer of one conclusion `c`:

* If `c.base` is not touched: the result is `c` (`Sequent.Unchanged`).
* Otherwise: the type filters of the base (`BaseTransfer.typeFilters`) remove a fact without a compatible instance
  (S5). The result is the union of `applyEdge(c, e)` over all micro edges `e`, then the field limit (§5). A touched base
  keeps only what an edge regenerates. That is the kill.

The builder (`StatementSummaryBuilder`) emits these micro edges. A micro edge `x.* →_{f} x.*` has the exclusion `{f}`.

| Statement | Micro edges; touched bases | Note |
|---|---|---|
| `a = b` | `b.* → b.*`, `b.* → a.*`; `{a, b}` | |
| `a = b.f` (`a ≠ b`) | `b.* → b.*`, `b.f.* → a.*`; `{a, b}` | A read never changes an exclusion. The current `keepAllExcept` on a read goes. |
| `a = a.f` | `a.f.* → a.*`; `{a}` | no refine-only edge |
| `a.f = b` (`a ≠ b`) | `a.* →_{f} a.*`, `b.* → b.*`, `b.* → a.f.*`; `{a, b}` | strong update: the only exclusion update |
| `a.f = a` | `a.* →_{f} a.*`, `a.* → a.f.*`; `{a}` | no identity edge for `a`: it would bring back the killed `a.f` |
| `a[i] = b` | `a.* → a.*`, `b.* → b.*`, `b.* → a.[e].*`; `{a, b}` | weak update |
| alias `(c, p)` of `a` in `a.f = b` | `b.* → c.p.f.*` | gen only |
| `C.s = b` | `S.* →_{C} S.*`, `S.C.* →_{s} S.C.*`, `b.* → b.*`, `b.* → S.C.s.*`; `{S, b}` | `S` is the `ClassStatic` base, `C` the class accessor (§4.5) |
| `x = C.s` | `S.* → S.*`, `S.C.s.* → x.*`; `{S, x}` | |
| source of `T` at `x` | `zero.$ → zero.$`, `zero.$ → x.$` with the mark `T`, both with the premise mark `zeroMark`; `{zero, x}` | the identity keeps the zero fact; the concrete premise mark makes the record mark-reversible |
| pass rule from `x` to `y` | `x.* → x.*`, `x.* → y.*`; `{x, y}` | a subtree move: delta-concat keeps `[any]` |
| conditional source: `x` carries `T` ⇒ `y` gets `T2` | `x.* → x.*`, `x.$ (T) → y.$ (T2)`; `{x, y}` | the premise mark `T` raises a request on a `*`-mark fact (§8.2) |
| any-field rule (`AssignMarkOnAnyAccessor`) | `zero.$ → x.[any]` with the mark `T` and the premise mark `zeroMark` | an incomplete edge (§2.5) |
| sink | a check (§8.1), not a micro edge | |
| cleaner | §8.4 | |

An external (unresolved) callee has no body. Its summary is the pass rules of its own rules plus the identity edges of
its arguments (as `propagateUnresolvedCallFact` does today). It is a STATEMENT summary: its micro edges apply to the
caller fact directly, in every run, and it is never restricted. In a restricted run no callee summary with a `*`
premise may be made (for example, the precomputed identity summary of an empty method, `EmptyMethodAnalyzer`): an empty
method is analysed like any method from its emitted concrete premise. A `*`-premise callee summary would bring a
correlated `*` conclusion into the restriction, and the agreed rule would drop it (review of version 4, M1).

### 4.3 The cases of bidirectional-task.md §1 (checked by `decide` in `Cases.lean`)

| Statement | Input fact | Result | Layer |
|---|---|---|---|
| `a = b.f` | `(b, .f, *, E, *)` | `(a, ., *, E, *)` | normal |
| `a = b.f` | `(b, ., *, E, *)`, `f ∉ E` | `(a, ., [any], {}, *)` | demand (`~`) |
| `a = b.f` | `(b, ., *, {f}, *)` | nothing for `a` | |
| `a = b.f` | `(b, ., [any], {}, *)` | `(a, ., [any], {}, *)` | layer of the input |
| `a = b.f` | `(b, ., $, {}, *)` | nothing for `a` | |
| `a.f = b` | `(b, .g, *, E, *)` | `(a, .f.g, *, E, *)`; under `L = 1`: `(a, .f, [any], {}, *)` | normal; under the cut: demand |
| `a.f = b` | `(a, .f, *, E, *)` | nothing (strong update) | |
| `a.f = b` | `(a, ., *, E, *)` | `(a, ., *, E ∪ {f}, *)`, no request | normal |

The premise of the edge does not change in any case. Only its layer can change, from normal to demand.

### 4.4 The steps that make an incomplete edge

| Step | Example |
|---|---|
| a correlated `*` fact becomes uncorrelated while a restriction is lost (`above`, `lostCorr`) | `a = b.f` on `(b, ., *, E, *)` |
| the field-limit cut | `b.h = box` with `box.f` tainted, under `L = 1` |
| an `[any]` fact ignores a premise exclusion | `below`, `r = []`, `E ≠ {}` |
| the start of a request answer with the `*` tail and a concrete mark | `(x, .f, *, {}, T)` starts as `(x, .f, [any], {}, T)` |
| the start of an `[any]` premise | |
| the normal form (step 6) | a mark-producing exact rule on a `*` fact |
| a summary edge of the demand layer is applied | the caller edge goes to the demand layer |
| a summary is applied to a fact that is not strong enough (§6.3) | a `*` caller fact above the premise |
| a cleaner keeps a `*`-mark fact at the cleaned position (§8.4) | the kept fact still covers the cleaned mark |
| a rule condition is over-approximated: a conjunction checked literal by literal, a literal that cannot be checked, a negated literal (§8.6) | |
| any operation on a fact in the demand layer | |

Why the layer is necessary (finding F1): an edge without `[any]` can still be an approximation.

```java
static String m(Holder x) {
    Inner a = x.f;
    return tag(a);        // conditional source: if arg(0) carries T, the result gets T2
}
// caller: h.f.g = source(); sink2(m(h));
```

The request on `(x, ., *, {}, *)` is answered with `(x, ., *, {}, T)`, which starts as `(x, ., [any], {}, T)` (W2).
`a = x.f` gives `(a, ., [any], T)`; the condition of `tag` matches through `[any]` and gives `(ret, ., $, T2)`. The summary
`(x, ., *, {}, T) → (ret, ., $, {}, T2)` has no `[any]`, but the flow is false: `T` is on `h.f.g`, not on `h.f`. In the
demand layer the edge is not persisted, and the next runs follow it as a demand. The same happens without a request after a
field-limit cut (`Cases.lean`, "F1").

### 4.5 Static fields

The `ClassStatic` base `S` with the class accessor stays. In run 1 a method that does not touch statics keeps the one
abstract static fact `(S, ., *, {}, *)` exact through an identity summary, which is cheap. In a restricted run a call
whose callee (transitively) touches no static does not touch `S`: the static fact passes over the call (§6.2 step 0)
instead (§4.2). A static write `C.s = v` on that fact
gives `(S, ., *, {C}, *)` (normal) and `(S, .C, [any])` (demand; `Cases.lean`, "two-level strong update"). The next
iteration resolves the demand by the emission (§7.3). The split happens in the method where the static fact is
concrete.

---

## 5. The field limit

A run has the field limit `L`. After each operation that can make a path longer (the statement transfer, the summary
application), the analyzer applies `limit_L`:

* If the path has at most `L` counted accessors, the fact does not change.
* Otherwise, cut the path before the `(L+1)`-th counted accessor. Uncounted accessors before that point stay in the
  prefix. The tail becomes `[any]`, the exclusion Empty, the mark stays, and the edge goes to the demand layer.

Lean: `cutPath`, `limitF`; `limitF_sound` (the cut only enlarges). The `[any]` tail covers every continuation, also
uncounted accessors, so the dropped suffix is covered. There is no `[any]` depth charge (`+10,000` in
`AccessNode.maxDepth`) and no fact-depth gate (`INITIAL_ALLOWED_FACT_DEPTH`): the field limit is the only depth bound.
Each run may have its own limit; the theorems put no condition on the sequence of limits (`RCov.iteration_sound`).

---

## 6. Calls

### 6.1 Concrete semantics (the model)

A call `r = m(a1..an)` has: the touched caller bases (the arguments, the result, the static base), the binding edges
into the callee (`ai.* → argi.*`, `S.* → S.*`, `zero → zero`), and the binding edges back (`argi.* → ai.*`,
`return.* → r.*`, `S.* → S.*`, `zero → zero`). The zero binding back makes the reversed call carry the zero fact into
the callee (§8.5). A caller location on an untouched base passes over the call. A location on a touched base
goes into the callee and comes back through the callee flow. Lean: `Call`, `Flow.pass`, `Flow.call`.

### 6.2 Call processing

For a caller edge `(i, layer) → c` at a call:

0. If `c.base` is not touched: pass `c` (call-to-return).
1. APPLY THE CURRENT SUMMARY EDGES. For each binding edge `e` into the callee, `a = applyEdge(c, e)`. Apply every
   summary edge of the callee whose premise `a` satisfies (§6.3). In a restricted run, apply each summary edge only
   through the restriction by a demand edge of the callee (§6.4). Apply every persisted complete record whose premise
   `a` satisfies (§10.7). Then apply the binding edges back and the field limit.
2. ADD `a` to the added set of the callee, with the caller edge (for request propagation).
3. The CALLEE ABSTRACTION emits the initial facts for `a` (§7): in run 1 the most abstract fact, in a restricted run
   the emission `a ∩ D-c` for each demand edge of the callee (§7.3). Each new initial fact is analysed.
4. NEW SUMMARY EDGES of any initial fact that `a` satisfies are delivered to the caller and applied as in step 1. The
   subscription stands for the whole run.

The result layer is the caller layer, or the summary layer, or a demand step of the application.

### 6.3 Summary application and satisfaction

`applySummary(a, j, g) = applyEdge(a, j → g)`, with the layer of the summary edge added and the normal form. The caller
fact `a` must SATISFY the premise `j`:

* RUN 1: `j` covers `a` (strong enough):

  ```
  applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j.tail = [any] ⇒ a.tail = [any])
  ```

  The application is the case `below` of §4.1, and the mark gate passes (`applicable_mark`). The abstraction of run 1
  covers every added fact (A1, §7.1), so run 1 needs no more. Lean: `coversB`, `applicable`, `applicable_sound`.
* RESTRICTED RUN: the premise lies INSIDE the fact (`a` covers every location of `j`), and the premise mark admits the
  fact mark (`j.mark = *`, or `j.mark = a.mark = T`). Lean: `satI`. This is the reverse of run 1 (there the fact lies inside the premise): the emitted fact is
  `a ∩ D-c` (§7.3), so it always lies inside its added fact (`RCore.emitM_satI`), and it can be smaller than `a` at the
  same path (`(p, [any], T) ∩ (p, $) = (p, $, T)`). `applyEdge` is sound for every overlap (`applyEdge_sound`).
  The overlap test (`satO`) is sound too, but it is worse: a precise fact then reads the summaries of a coarser sibling
  premise (`(x, .g.h, $, T)` reads the demand-layer summary of `(x, .g, [any], T)`), its result stays in the demand
  layer, and a false demand vulnerability survives every run instead of being refuted (review of version 4, M2).

The mark condition makes the mark gate pass: a summary application never raises a request (`Coverage.summary_step`,
`RCov.sat_step`, `RCore.summary_stepR`). The satisfaction contract `SatContract` (no request; an answer keeps the
satisfaction) holds (`RCore.satI_contract`; also `satO_contract`).

* The exclusion of a summary edge is on its conclusion, and it FILTERS the delta: `(x, ., *) → (ret, ., */{f})` applied
  to `(y, ., */{})` gives `(r, ., */{f})`, and applied to `(y, .f.g, $, T)` gives nothing.
* A partial overlap is never applied in run 1. Another initial fact of run 1 serves it.
* Version 3 used `satU`/`satS` (strong enough, or `[any]` / `*` above the premise). The model keeps them as the record
  of the review; they are not spec rules.

### 6.4 Summary restriction (restricted runs)

A restricted run applies a summary edge `S = (S-p → S-c)` of the callee only through a demand edge `d` of the callee.
`d` has the entry pattern `D-c` and the exit pattern `D-p` (§1). The result is `R = (R-p → R-c)`:

* `R-p := S-p` if `S-p` and `D-c` overlap (a common location, marks ignored); else no result. `S-p` is one path, so the
  intersection is all of `S-p` or nothing.
* `R-c := concat(D-p, delta(S-c, D-p))`, by the position of `S-c` against `D-p`:

| `S-c` against `D-p` | `S-c` tail | `R-c` |
|---|---|---|
| at or below (`S-c.path = D-p.path ++ r`), the tail of `D-p` admits `r` | any | `S-c` |
| at or below, the tail of `D-p` does not admit `r` | any | no result |
| above (`D-p.path = S-c.path ++ r`) | `[any]` | `(D-p.path, [any])`, or `(D-p.path, $)` if `D-p` has the `$` tail |
| above | `*/E` | no result (as agreed); it never occurs in a restricted run (no `*` final tail, §7.3) |
| above | `$` | no result |
| apart, or another base | | no result |

* No `D-p` (the demand does not reach the method exit): no result.
* One summary edge can be restricted by several demand edges. The caller applies every result (the union).
* `R` has the layer of `S`. The restriction only removes pairs (`RCore.restrictU_sub`, `RExact.restrictU_sub`).

Why the correlated row needs no repair. A correlated `*` conclusion exists only under a `*`-mark premise. A restricted
run has none (§7.3), so `restrictU` and the version-3 repair `restrictS` agree on every exit edge, and the two runs are
equal (`RExact.restrict_U_eq_S`). The contract holds for `restrictS` (`RCore.restrictS_contract`: every demanded pair
survives, in the same layer); `restrictU` alone does not satisfy it for a `*` conclusion (`RCore.restrictU_fails`).

Program 2 (`RCases`, field limit 3 in the forward run; the backward run cut both demands at 2):

```java
root():  x.h.i.f.k.z = source();  r = c(x);  sink(r.f.k.z);
c(arg):  ret = arg.h.i;  return ret;
```

The demand of `c` is `D-c = (arg, .h.i, [any], T)`, `D-p = (ret, .f.k, [any], T)`. The root fact is cut to
`(x, .h.i.f, [any], T)`. The emission gives the fact itself, the exit fact is `(ret, .f, [any], T)`, and the agreed
restriction moves it to `(ret, .f.k, [any], T)`: the caller gets `(r, .f.k, [any], T)` and the sink triggers
(`p2_found_M`). (In version 3 the emission gave `(arg, .h.i.f, *, *)`, the exit fact was the correlated
`(ret, .f, *)`, and the agreed rule dropped it: `p2_lost_U`.)

Reference form:

```kotlin
/** A demand edge in the orientation of the run: the entry pattern D-c and the exit pattern D-p. */
data class DemandEdge(val entry: PatternFact, val exit: PatternFact?)

/** §6.4. Restrict the summary conclusion `sc` of the premise `sp` by the demand edge `d`. */
fun restrict(sp: InitialAp, sc: Conclusion, d: DemandEdge): Conclusion? {
    val dp = d.exit ?: return null                           // the demand does not reach the exit
    if (!overlap(sp, d.entry)) return null                   // R-p: all of S-p or nothing
    if (sc.fact.base != dp.base) return null
    val p = dp.path
    val q = sc.fact.path
    return when {
        q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null     // at or below D-p
        p.startsWith(q) -> {                                                     // above D-p
            val r = p.drop(q.size)
            when (sc.fact.tail) {
                Tail.STAR -> null                     // as agreed; never occurs in a restricted run
                Tail.ANY -> sc.copy(
                    fact = sc.fact.copy(path = p, tail = if (dp.tail == Tail.EXACT) Tail.EXACT else Tail.ANY),
                    exclusion = ExclusionSet.Empty)
                Tail.EXACT -> null
            }
        }
        else -> null
    }
}
```

---

## 7. Abstraction

### 7.1 Contracts

The abstraction selects the initial facts for an added fact `a` of method `m`. It is a function of `m`, `a` and
constants of the run (the field limit, the demand). It must not depend on the order of events: the run result is then
the least fixed point and does not depend on the schedule.

```
(A1)  run 1:            applicable(α(m, a), a)
(A2)  restricted run:   for every demand edge d of m, every CONCRETE added fact a and every location l (with its
                        mark) that D-c and a both cover, the emission emit(D-c, a) gives an initial fact j that
                        covers l, and a satisfies j
(A3)  restricted run:   the emitted fact has the mark of the added fact
```

The coverage theorem of run 1 needs only (A1). The coverage theorem of a restricted run needs (A2) for the added facts
of the run (`EmitContractOn`), the satisfaction contract (§6.3) and the restriction contract (§6.4). (A3) makes every
added fact of a restricted run concrete (`RCov.concInvR_all`, `RExact.DR_concrete`), so (A2) covers all of them
(`EmitContractConc.on`, `RCov.emitOn_of_conc`). The rules decide the precision and the cost.

### 7.2 Run 1

* The zero fact is served by the zero fact.
* Every other added fact `a` is served by the most abstract fact `(a.base, [], *, {}, *)`.

Lean: `policy1`, `policy_applicable` (A1). The caller gets the marks back through the summary application: a `*`-mark
premise passes the mark of the caller fact through. A sink or a mark-specific rule inside the callee gets the mark
through a request (§8). Run 1 is the ONLY run with requests.

### 7.3 Restricted run: the emission

For the added fact `a` of method `m`, for each demand edge of `m` with the entry pattern `D-c = (b, p, t, M)`, emit
`a ∩ D-c`: the part of `a` that `D-c` covers, with the mark of `a`. The demand mark is a demand for that mark.

Marks:

| `D-c` mark | `a` mark | result |
|---|---|---|
| `T` | `T` | emit |
| `T` | `T' ≠ T` | nothing |
| `T` | `*` | nothing; it never occurs (see "No request" below) |
| `*` | any | emit, with the mark of `a` |

Locations (`a ∩ D-c`):

| `a` against `p` | emitted fact |
|---|---|
| another base, or apart | nothing |
| below (`a.path = p·r`, `r ≠ []`), `t` admits `r` | `a` itself |
| below, `t` does not admit `r` | nothing |
| at `p` | `(b, p, meet(a.tail, t))`: `[any]` gives the other tail; `$` with any tail gives `$`; `*/E1` with `*/E2` gives `*/(E1 ∪ E2)` |
| above (`p = a.path·r`), the tail of `a` admits `r` | `(b, p, t)`: the demand chain and tail |
| above, the tail of `a` does not admit `r` (`$`, or `*/E` with `E` excluding `r`) | nothing |

Properties:

* The emitted fact is EXACTLY `a ∩ D-c` as locations (`RCore.emitM_inter`), with the mark of `a` (`emitM_mark`,
  `emitM_copies`). Nothing is lost when the marks match (`emitM_complete`). Its chain is the chain of `a` or, above `a`,
  the demand chain (`emitM_shape`): never a chain that neither the fact nor the demand has.
* (A2) holds for concrete added facts (`RCore.emitM_contract`). It fails for a `*`-mark added fact under a `T` demand
  (`emitM_not_full`); that does not matter, because there is none.
* NO REQUEST. The mark demand is part of the demand edge. The root starts from the zero fact, every emitted fact copies
  a concrete mark, a concrete-mark premise has only concrete-mark conclusions, and
  a run-1 record applied to a concrete fact gives a concrete result. So every fact of a restricted run has a concrete
  mark, and no request rule can fire: the sink check, the mark gate and the climb all need a `*` mark, and an answer
  needs a request (`RCov.no_reqR`, `RExact.DR_no_request`). Requests, the request store (§10.9) and the answer rule are
  used only in run 1. A restricted run is a CONCRETE run: it has no `*` mark and no `*` final tail
  (`RExact.final_not_star`).
* The zero fact. A demand that covers the zero location with the zero mark emits the zero fact itself.
* Precision. An exact added fact gives an exact concrete initial fact. Its edges are in the normal layer, and a
  vulnerability under it can be confirmed (§8.1). A fact cut to `[any]` gives an `[any]` premise; it starts in the
  demand layer (§7.4).
* Cost. There is NO SHARING: one initial fact per distinct added fact (path, tail, mark). (The version-3 table emitted
  the chain plus one accessor, shared by all facts below it.) The demand bounds which methods are analysed and the
  chain prefix, but NOT the number of contexts below an `[any]` demand chain: each distinct fact there is its own
  context, and the spec sets no cap.
* Confirmation needs the forward limit. A fact cut by the forward field limit is `[any]`, so its premise starts in the
  demand layer and nothing below the cut can be confirmed until a later forward run has a larger limit. The driver
  (outside this spec) must grow the forward limit as well as the backward one.
* Marks. The emission checks the demand mark; the restriction (§6.4) reads `D-p` as locations and ignores its mark.
* R8 (§10.7) applies only when a demand entry pattern IS a run-1 closed initial fact; demand edges come from the
  backward run, so in practice only the zero fact and exact facts meet it.
* A premise `(p, */E, T)` (the meet with a `*/E` demand) starts as `[any]` in the demand layer (§7.4); it makes no
  complete record.

Programs 1 and 2 (§0.3). With this emission the forward run 3 reports both vulnerabilities, with the agreed
restriction (`RCases.p1_found_M`, `p2_found_M`). Program 1 (field limit 3 in the forward run; the backward run cut both
demands at 2: `(x, .g.h, [any], T)` for `c`, `(arg, .f.k, [any], T)` for `m`):

```java
root():  x.g.h.f.k.z = source();  c(x);      // (x, .g.h.f, [any], T) after the cut
c(x):    y = x.g.h;  m(y);                    // c gets (x, .g.h.f, [any], T); then (y, .f, [any], T)
m(arg):  sink(arg.f.k.z);                     // m gets (arg, .f, [any], T) ∩ (arg, .f.k, [any], T)
                                              //       = (arg, .f.k, [any], T): the sink triggers
```

Reference form:

```kotlin
/** §7.3. The part of the added fact `a` that the demand entry pattern `d` covers, with the mark of `a`. */
fun emit(d: PatternFact, a: PathFact, aExclusion: ExclusionSet): InitialAp? {
    if (d.base != a.base) return null
    if (!d.mark.isStar && d.mark != a.mark) return null       // a T demand needs the fact mark T
    val p = d.path
    val q = a.path
    return when {
        q.size > p.size && q.startsWith(p) ->                   // below: the fact itself
            if (d.tailAdmits(q.drop(p.size))) InitialAp(a.base, q, a.tail, aExclusion, a.mark) else null
        q == p -> {                                              // at: the meet of the tails
            val (tail, excl) = meet(a.tail, aExclusion, d.tail, d.exclusion)
            InitialAp(a.base, p, tail, excl, a.mark)
        }
        p.startsWith(q) ->                                       // above: the demand chain and tail
            if (tailAdmits(a.tail, aExclusion, p.drop(q.size))) InitialAp(d.base, p, d.tail, d.exclusion, a.mark)
            else null
        else -> null
    }
}

/** §6.3. The fact `a` satisfies the premise `j`. */
fun satisfies(j: InitialAp, a: PathFact, aExclusion: ExclusionSet, restricted: Boolean): Boolean =
    if (!restricted) applicable(j, a, aExclusion)                              // run 1: strong enough
    else covers(a, aExclusion, j) && (j.mark.isStar || j.mark == a.mark)      // restricted run: j inside a
```

### 7.4 The start fact

| initial fact `i` | start conclusion | layer |
|---|---|---|
| `(x, p, *, {}, *)` | `(x, p, *, {}, *)` (identity) | normal |
| `(x, p, *, {}, T)` | `(x, p, [any], {}, T)` (W2) | demand: the `~` premise |
| `(x, p, [any], m)` | `(x, p, [any], {}, m)` | demand |
| `(x, p, $, m)` | `(x, p, $, {}, m)` | normal |

Lean: `startFact`, `startFact_sound`.

---

## 8. Rules: sinks, marks, requests

### 8.1 Sink check

A sink checks the pattern `s = (v, ρ, $ or [any], T)`. For an edge `(i, layer) → f`:

* If `f` and `s` do not overlap: no effect.
* If the effective mark of `f` is concrete (`f.mark = T'`, or `f.mark = *` and `i.mark = T'`): the sink is TRIGGERED if
  `T' = T`.
* If `f.mark = *` and `i.mark = *`: raise the REQUEST `(m, i, T)`. The exclusion does not change.

This covers bidirectional-task.md §2: `(x,.,$,T)` triggers, `(x,.f,$,T)` does not, `(x,.,[any],T)` triggers,
`(x,.,*,{},*)` raises the request `T`. It also covers: `(x,.,[any],*)` and `(x,.,$,*)` raise the request; `(x,.f,*,*)`
does not overlap the sink pattern `(x, ., $, T)`. Lean: `check`, `check_sound`, `check_request_star`.

A triggered vulnerability is CONFIRMED only if all three hold:

1. the sink edge is complete;
2. its premise is the zero fact or an EXACT concrete fact `(x, p, $, T)`: a request answer in run 1, an emitted fact in
   a restricted run;
3. the premise is SUPPORTED: it is the zero fact of an entry method, or a normal-layer caller edge of a supported premise
   produced, through a normal binding, the zero fact (for the zero premise) or the exact added fact `a`, and the premise
   IS that added fact (same base, same path): the answer of `a` in run 1, the emission `a ∩ D-c = a` in a restricted
   run. The weaker condition "the premise is exact" is not enough: a request on one parameter can then be supported by
   a real fact on another parameter (`Confirmed.weak_support_gap`, a proved counter-example).

Every other triggered vulnerability is a DEMAND vulnerability. Condition 3 is necessary: an incomplete edge in the
caller can feed an added fact whose exact answer starts in the normal layer, so a complete sink edge alone admits a
false positive (review counter-example). `Confirmed.confirmed_real` (run 1) and `RExact.confirmed_realM` (every
restricted run; the support `SupM` accepts the emitted exact fact, `SupR → SupM`) prove that a confirmed vulnerability is
a real concrete vulnerability: there is no false positive inside this scope.

### 8.2 Mark-specific micro edges

A micro edge with a concrete premise mark `T` (a conditional source, a mark-specific pass rule) on a fact with the mark
`*` gives no fact. It raises the request `(m, i, T)` (the mark gate, §4.1 step 4). If it dropped the fact without a
request, the flow would be lost; if it applied the rule anyway, every mark would pass the rule.

### 8.3 Request answer and propagation

A request `(m, i, T)` STANDS for the whole run. On every added fact `a` of `m` that overlaps `i`, also an added fact that
arrives later:

* If `a.mark = T`: ANSWER (bidirectional-task.md §4). If `a` is exact at `i.path`, emit `(i.base, i.path, $, {}, T)`.
  Otherwise emit `(i.base, i.path, i.tail, {}, T)`. It starts per §7.4: a `*` tail starts as `(i.base, i.path, [any],
  {}, T)` in the demand layer; a `$` tail stays `$` in the normal layer. The chain is never deeper than the request.
* If `a.mark = *`: PROPAGATE to every caller edge `(ic → c)` that produced `a`: raise the request `(caller, ic, T)`.

One answer does not stop the request: the answer for one added fact does not serve another added fact. The answered
initial facts are initial facts like every other: callers read their summaries through §6.2 step 4.

Requests exist ONLY in run 1. A restricted run is concrete (§7.3): no request is raised there, and no answer is made
(`RCov.no_reqR`, `RExact.DR_no_request`). The mark that a sink needs is already in the demand edge. Lean: `answerInit`, rules `answer`, `reqUp`; `answerInit_covers`,
`answerInit_applicable`; `SatContract` (an answer keeps the satisfaction).

### 8.4 Cleaners

A cleaner of the mark `T` at a position removes conclusions with the concrete mark `T` there. It keeps conclusions with
the mark `*`, in the DEMAND layer: that is sound (the kept fact covers more than the cleaned value) but it is an
approximation. For precision the analyzer may raise the request `T` first and clean the answer. (Cleaners are outside
the Lean model.)

### 8.5 The backward direction

The backward analysis uses the same facts, `applyEdge`, storages and rules. Only the meaning of a mark and the roles of
the rules change (as on `saloed/backward-main`, `core/docs/backward-analysis.md` §1 and §5):

* A backward fact is a REQUIREMENT: "if a location of this set carries `T` here, a sink is reached".
* The backward premise is at the method exit; the backward summary edge ends at the method entry.
* The statement transfer applies the REVERSED summary: every micro edge is reversed (§10.8), and a target base that the
  statement does not touch (a gen-only target, such as an alias target) gets an identity edge (`Reverse.Stmt.rev`;
  `revNoId_breaks` shows that the identity edge is necessary).
* A call is reversed too: the binding into the callee becomes `r.* → return.*`, `ai.* → argi.*`, `S.* → S.*`,
  `zero → zero`; the binding back becomes `argi.* → ai.*`, `S.* → S.*`, `zero → zero` (`Reverse.Call.rev` reverses
  every binding edge, so the zero and static bindings of §6.1 are kept in both directions).
* The rules swap:

| Forward rule | Backward role |
|---|---|
| unconditional source of `T` at `(v, ρ)` | sink pattern `(v, ρ, $, T)`, AND the reversed micro edge `(v, ρ, $, T) → zero` |
| conditional source (needs `T'`, gives `T`) | micro edge `(v, ρ, $, T) → (u, π, $, T')` |
| sink of `T` at `(v, ρ)` | source: `zero → (v, ρ, $ or [any], T)` (the seed) |
| mark-specific pass rule `T` from `x` to `y` | the reversed micro edge `y → x` with the premise mark `T` |
| unconditional cleaner of `T` | removes the requirement `T` there |

* The demand match across directions: the restriction compares locations only; the emission also compares the mark
  (§7.3).
* SEEDS. A backward run places its seed DIRECTLY at every sink statement where an earlier forward run reported a
  vulnerability: a zero-to-fact edge `Zero → (sink statement, requirement)`. The method of the sink needs no zero fact
  from its exit. So a sink in code that never returns is seeded too: `root() { worker(); }`,
  `worker() { while (true) { b.f = source(); sink(b.f); } }` (review of version 4, H1: a seed that waits for a zero fact
  at the exit is never placed there, and the next forward run would refute a real vulnerability).
* The ZERO DEMAND. A requirement that reaches a source continues to the zero fact (the reversed source edge), and the
  zero fact goes up through the reversed zero bindings. So every method between a source and the sink gets the demand
  edge whose entry pattern is the zero fact, and the next forward run emits the zero fact there (§7.3). Without it, a
  source inside a callee is lost: `root() { r = h(); sink(r); }`, `h() { return source(); }` gives no zero demand for
  `h` (review of version 3, H2).
* Every backward run is a restricted run (the first one, backward-2, follows forward-1). It is concrete too: its seeds
  have the sink marks, and the emission copies the mark (the `*` marks in the demand of backward-2 do not matter: a
  `*` demand mark keeps the concrete mark of the fact). So a backward run raises no request. The emission (§7.3), the
  satisfaction (§6.3) and the restriction (§6.4) apply unchanged, with the entry and the exit swapped: the entry pattern
  of a backward demand edge is at the method exit.
* The backward run between forward run k and forward run k+1 must satisfy the contract B (§11.7).

The backward run is the closure on the reversed program. `Reverse.flow_rev_iff_calls` proves that its flow is the
converse flow, with calls, if every micro edge and every call binding has an exact shape and is mark-reversible
(`RevStmts`, `RevCalls`); `backward_of_forward_calls` applies the forward coverage theorem to it, if moreover every call
binding has a `*` target mark (`BindTargetsStar`, `rev_WF`). The source rule must have the zero mark as its premise mark
(§4.2): then it is mark-reversible.

### 8.6 Conditions with several literals; non-distributive edges

* Each positive literal `ContainsMark(pos, T)` is a sink pattern or a premise mark. A literal on a `*`-mark fact raises a
  request.
* A conjunction is OVER-approximated: each literal is checked on its own, and the rule is evaluated again when a new fact
  arrives at the statement (standing, as `TaintSinkTracker` assumptions are today). A literal that cannot be checked
  counts as true; a negated literal counts as true. Every such over-approximation puts the result in the demand layer.
* A source with several preconditions makes a non-distributive (ND) edge, keyed by the SET of initial facts. The AP
  operations apply to its conclusion without change. The ND store and subscription stay as today with the new fact
  types. ND edges are outside the Lean model.

### 8.7 What replaces the old refinement machinery

| Old mechanism | New AP |
|---|---|
| `SideEffectRequirement`, `refineInitial` | Removed. A premise never changes; a lost correlation gives an incomplete edge. |
| the refinement set of a rule reader (`FactReader`) | The mark request (§8.1, §8.2). |
| `TaintMarkFieldUnfoldRequest`, `[any]` unroll requests | The demand of the previous run (§7.3) and the mark request. |
| call type info through refinement (`CallTypeInfoUtil`) | Type information from the phase-3 prescan; type filters (S5). |
| `FactSideEffect` summaries | The callee summary edges (§6.3). |
| fact-depth gate, `[any]` depth charge | The field limit (§5). |
| union merge of exclusions | Merge rules 1 and 2 (§3.3). |
| `TreeInitialFactAbstraction` | Run 1: the most abstract fact (§7.2); later runs: the emission `a ∩ D-c` (§7.3). |

---

## 9. Representation (the optimization)

The concept of a conclusion is a set of path facts. The representation groups path edges into TREES.

### 9.1 Initial fact

```kotlin
enum class ApTail { STAR, ANY, EXACT }

/** Abstract mark is STAR; a concrete mark is its dense taint-mark index. */
@JvmInline
value class ApMark(val raw: Int) {
    val isStar: Boolean get() = raw == STAR_RAW
    companion object { const val STAR_RAW = -1; val STAR = ApMark(STAR_RAW) }
}

/** The initial fact (premise): one linear path. */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,       // interned, linked from the root; no [any], $ or mark accessors (W4, W5)
    val tail: ApTail,
    val exclusion: ExclusionSet,   // Empty in run 1; a restricted run can emit the exclusion of a `*/E` demand
    val mark: ApMark,
)

/** The key of an analysis context: the premise and the layer. */
data class PremiseKey(val initial: InitialAp?, val demand: Boolean)   // initial == null: the zero fact
```

`PathNode` is the current `AccessPath.AccessNode` without the `[any]`, `$` and mark accessors.

### 9.2 Conclusion trees

One tree per (premise, layer, exclusion). The exclusion belongs to the tree; a `*` leaf is a flag.

```kotlin
/** A set of marks: the abstract mark flag plus sorted concrete mark ids. */
class MarkSet(val star: Boolean, val concrete: IntArray)

/** Payload of one trie node at path p. */
class Payload(
    val star: Boolean,      // the leaf p.* with the tree exclusion and the mark * (W2)
    val any: MarkSet,       // the leaves p.[any] with these marks
    val exact: MarkSet,     // the leaves p.$ with these marks
)

class FactNode(
    val payload: Payload,
    val accessors: IntArray?,       // sorted AccessorIdx, as today
    val children: Array<FactNode>?,
) {
    @JvmField val boundedDepth: Short = ...   // max counted accessors on a path below; O(1) limit check
}

/** One edge group: the conclusions of one premise, one layer and one exclusion, at one statement, for one base. */
class EdgeTree(
    val base: AccessPathBase,
    val exclusion: ExclusionSet,   // the exclusion of the * leaves; normalised to Empty if the tree has no * leaf (W1)
    val demand: Boolean,           // the layer; a demand tree has no * leaf (W2)
    val root: FactNode,
)
```

Rules:

* T1. Merge rule 1: two trees with the same key (premise, layer, exclusion) merge by union.
* T2. Merge rule 2: two trees with the same premise, layer and EQUAL content merge into one tree with the intersection
  of the exclusions. It is not valid for different contents: the intersection then adds pairs (`Tree.lean`).
* T3. No union of exclusions across trees. No merge across layers.
* T4. `add` returns the new part only (the delta), as `mergeAddDelta` does today. Exception: when merge rule 2 shrinks
  the exclusion of a stored tree, the delta is the WHOLE merged tree with the new exclusion. The content is equal, so a
  content delta would be empty, but the pairs of the removed exclusions are new and must be propagated.
* T5. Inside one DEMAND tree, an `[any]` leaf with the mark `m` at `p` may absorb every leaf with the mark `m` below
  `p`. The denotation does not change. A normal tree is never folded: a rule-assigned `[any]` leaf there must not absorb
  complete leaves (they are persisted, and they can confirm a vulnerability).
* T6. Share one empty payload; intern payloads, mark sets and exclusion sets.

### 9.3 `applyEdge` on a tree

The operation of §4.1 on all paths of one tree at once. The results are grouped by their new (layer, exclusion):

1. Walk `from.path` from the root. On each proper prefix node, read its payload as the case `above`: `*` and `[any]`
   leaves give `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer unless §4.1 says otherwise.
2. At the node of `from.path` take the subtree `S`. Filter its root by the premise tail and the edge exclusion.
3. Transform `S` by the target tail. For a `*` target: the child subtrees (`r ≠ []`) keep the tree exclusion and are
   re-rooted under `to.path`; the root `*` leaf (`r = []`) gets the exclusion `Ec ∪ E`, so it goes to another tree.
   `[any]` and `$` targets fold `S` into one uncorrelated payload with the Empty exclusion, except the root `*` leaf
   under a `$` premise and a `$` target: it becomes the correlated `*/Universe` leaf (§4.1), in a tree with the Universe
   exclusion.
4. Apply the mark gate per payload mark, then the target mark.
5. Apply the field limit with `boundedDepth`; cut paths go to the demand tree.
6. Route each result by its own layer bit (§4.1 steps 3, 5, 6 and the cut).

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `S` only. The concept form visits every path
fact (`Tree.lean`).

### 9.4 The restriction on a tree

The restriction of §6.4 applies to all conclusions of one summary tree at once (`RStore.restrictTree`):

1. Walk `D-p.path` from the root. On each proper prefix node: drop the `*` flag (the agreed rule `restrictU`; a
   restricted run has no `*` leaf, and the version-3 form `restrictTree` keeps it); move the `[any]` marks to
   `D-p.path` (as `$` for a `$` exit pattern); drop the `$` marks and every child off the chain.
2. At the node of `D-p.path`, keep the payload, add the moved marks, and keep each child whose accessor the tail of `D-p`
   admits (all children for `[any]`, none for `$`).

The result fits ONE tree: a kept leaf keeps the tree exclusion, a moved leaf has no exclusion, and the layer does not
change (`RStore.restrictTreeE_inv`). The tree form equals the per-path restriction on whole conclusions, fact and layer
(`restrictTreeE_mem_U` for the agreed rule; `restrictTreeE_mem_S`, `restrictTreeE_den_S` for the version-3 form). Cost (`restrictTree_cost`): the walk compares each input cell at
most once, and the operation builds `|D-p.path| + 1 + (kept children at D-p.path)` new cells (counted by the cost
function `newCells`, which follows the walk; it is not derived from the construction itself). The kept subtrees are
SHARED with the input, not copied (`rTree_shape`, `keepKids_children`).

### 9.5 Interning

Tries are hash-consed bottom-up as today; an identity cache memoises the walk of §9.3. `boundedDepth` is part of the
node, not of the hash.

### 9.6 Relation to the current code

The phase-3 prescan still runs the current core. So the new AP lives beside the current types.

| Part | Decision |
|---|---|
| `AccessPath.AccessNode`, accessor interning, `AccessorIdx` | Reuse. |
| `AccessTree` merge, `mergeAddDelta`, interners, identity caches | Reuse the algorithms for `FactNode`. |
| `AccessBasedStorage` trie | Reuse for the path indexes of §10. |
| `EdgeStorage`, `AccessPathBaseStorage`, exact-key subscription maps | Reuse with the new fact types. |
| `StatementSummaryBuilder`, `buildReversed` | Adapt: the read builder (no `keepAllExcept` on a read); the rule rows of §4.2; a reversal for records with the exclusion on the new conclusion (§10.8). |
| `InitialFactAp`, `FinalFactAp`, `ApManager` | New types `InitialAp`, `EdgeTree`. They do not implement the old interfaces. |
| `Edge` (`ZeroToFact` requires Universe) | New edge classes with the layer: `Zero → (layer, statement, fact)`, `(premise, layer) → (statement, fact)`. |
| `FactReader` (mark as accessor suffix) | New reader over `(path, tail, mark)`: `check` (§8.1). |
| `EdgeNonUniverseExclusionMergingStorage` (union merge) | Replace by merge rules 1 and 2. |
| `TaintSinkTracker`, vulnerability records | Add the confirmed/demand state (§10.10). |
| `TreeInitialFactAbstraction` | Replace by §7.2 (run 1) and §7.3 (restricted runs). |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used (§5). |

---

## 10. Storages

Every store has a CONCEPT (a list of records with a filter) and an INDEX. `Store.lean` and `RestrictedStore.lean` prove
that each index returns every record that the filter returns, and give the cost of the lookup. Lifetime: RUN = one run
(one direction, one limit); PERSISTENT = all runs of one analysis.

### 10.1 Method edge store (RUN, per method)

* Key: `(statement, premise, layer, base, exclusion)`. Value: an `EdgeTree`.
* `add(...)` merges by rule 1 or 2 and returns the delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer and one class: a conclusion is dropped if a stored conclusion of the same premise and
  layer subsumes it, and the stored one is complete whenever the dropped one is complete
  (`Subsume.subsumesB`): the same base and mark; `[any]` at `p` subsumes every fact at or below `p`; `*/Es` subsumes
  `*/En` at the same path if `Es ⊆ En`; `$` subsumes `$` and `*/Universe` at the same path. `subsumes_sound` proves that
  every pair of the dropped fact is a pair of the stored fact. Do not use the premise test `coversB` for conclusions.
* An incomplete conclusion (a demand conclusion, or a rule-assigned `[any]` in the normal layer) never subsumes a
  complete one (`Subsume.recordSubsumesLB_layer` for records).
* Unchanged propagation (`Sequent.Unchanged`) may skip the store, as today.
* Queries for the trace resolution (phase 5): `edgesAt(stmt, premise?)`, `edgesAt(stmt, pattern)`, as
  `MethodAnalyzerEdges` and `MethodAnalyzerEdgeSearcher` give today. The store of the last forward run stays until the
  trace resolution ends.

### 10.2 Initial fact store (RUN, per method)

* `initials: Map<InitialAp, Status>`, `Status ∈ {analysing, done}`, with the flags `allComplete` (every edge of the
  initial fact is complete), `hasRequest` and `supported` (§8.1; it is set when a normal-layer caller edge of a
  supported premise delivers the zero fact or the exact answering added fact, and it never goes back).
* `uses: Map<InitialAp, Set<(callee, InitialAp)>>`: the callee initial facts that serve the calls inside each initial
  fact (for the closed marker, R5).

### 10.3 Added fact store (RUN, per method)

* A path trie keyed by `base :: path`, with the caller edges `(caller method, caller premise, layer, call statement)`
  that produced each added fact.
* The standing request match (§8.3) and the subscription (§6.2 step 4) read it with OVERLAP and SATISFIES queries:
  `lookupPrefixes ++ lookupExtensions` of the query path (an added fact above a premise is an extension query from the
  fact's side, a prefix query from the premise's side).

### 10.4 Subscription store (RUN)

* Key: the callee. Value: the caller records `(caller edge, call statement, added fact a)`.
* On a new summary edge of an initial fact `j`: find the subscribed `a` that satisfy `j` (§6.3), restrict the edge by
  each demand edge of the callee (restricted runs, §6.4), and apply.
* On a new subscription: apply every existing summary edge of every initial fact that `a` satisfies.

### 10.5 Run summary store (RUN, per method)

* Key: `(premise, layer, exit kind)`. Value: the exit `EdgeTree`s.
* Complete summary edges go to the persistent record store at the end of the run (§10.7).
* The summary edges on the paths of the vulnerabilities are the input of the next run in the other direction (§10.6).

### 10.6 Demand store (from the previous run, read only)

* Content: the demand edges of the method, in the orientation of this run: the entry pattern `D-c` and the exit pattern
  `D-p` or none (§1). The previous run (the other direction) gives them: the edges of that run on the paths from the
  vulnerabilities of the run before it, incomplete edges, reversed complete records and the zero edges (§8.5, §11.7,
  contract B).
* Index: a path trie keyed by `base :: D-c.path`.
* The query `near(q)`: the prefix walk of `q` (the demand chains at or above `q`), then the subtree strictly below the
  node of `q` (the chains below `q`). It returns the same records as the list filter "the chain is not apart from `q`"
  (`RStore.near_equiv`), and every record it returns is in the store with that chain (`near_sound`).
* Emission query (§7.3), for the added fact `a`: `near(a.path)`. It returns every demand edge for which the emission
  gives a fact (`emit_complete_M`; the version-3 tables: `emit_complete_S`, `emit_complete_U`), so the emission over the
  candidates equals the emission over the whole store (`emit_lookup_equiv_M`, `initR_premise_equiv`).
* Restriction query (§6.4), for the summary premise `j`: `near(j.path)`. It returns every demand edge that can restrict
  a summary edge of `j` (`restrict_complete_S`, `restrict_lookup_equiv_S`, `ret_premise_equiv`).
* Cost (`near_query_cost`): at most `|q| + 1` nodes for the walk, plus `Σ |rel|` over the returned chains strictly below
  `q` (`din.path = q ++ rel`), against `|demand edges|` tests in the list form. The bound "walk + number of results" is
  FALSE for the plain trie (`deep_chain_cost`: one chain of length 8, 1 result, 9 nodes); a path-compressed (radix) trie
  gives it. The key `base :: path` works the same way (`nearK`). For a `$` added fact only the prefix walk can emit
  (§7.3: a `$` fact above the chain emits nothing; `emitM_exact_prefix`), so the subtree part can be skipped.

### 10.7 Persistent complete record store (PERSISTENT)

One direction-neutral store for the forward and the backward analysis:

```kotlin
/** A complete summary edge, in the orientation in which it was derived. */
class CompleteRecord(
    val method: MethodKey,
    val direction: Direction,          // FORWARD: premise = entry fact; BACKWARD: premise = exit fact
    val premise: InitialAp,
    val conclusion: EdgeTree,          // normal layer, no [any]
)

interface CompleteRecordStore {
    fun add(record: CompleteRecord)
    /** Records whose ENTRY fact the caller fact satisfies (forward reading). */
    fun byEntry(method: MethodKey, callerFact: InitialAp): Sequence<CompleteRecord>
    /** Records whose EXIT fact the requirement satisfies (backward reading, reversed). */
    fun byExit(method: MethodKey, requirement: InitialAp): Sequence<CompleteRecord>
    fun markClosed(method: MethodKey, direction: Direction, initial: InitialAp, limit: Int, vulns: List<VulnerabilityRecord>)
    fun closed(method: MethodKey, direction: Direction, fact: InitialAp): ClosedInitial?
}
```

Rules:

* R1. Only complete edges are added.
* R2. `byEntry` is a path trie keyed by `base :: entry path`, `byExit` by `base :: exit path`. The lookup is
  `lookupPrefixes(base :: q)` and then the exact `applicable` filter. `forward_equiv_prefixes` proves the prefix half
  complete for the path key, and `applicable_mem_candidatesB` for the `base :: path` key; the extension half adds nothing
  for this query (`extension_half_redundant`). In a restricted run the satisfaction is an overlap test (§6.3), so the
  lookup needs both halves (prefixes and extensions).
* R3. A reader in the other direction applies the reversal of §10.8. Every complete record whose premise has the Empty
  exclusion and that is mark-reversible reverses exactly (`Reverse.rev_exact_of_empty_premise`).
* R4. Adding complete records to a later run IN THE SAME DIRECTION is always sound: a complete edge of run 1 or of a
  restricted run is exact (`Exact.edge_exact`, `RExact.recs_of_DR`, `recs_of_D`), so it adds no false pair (§6.2
  step 1; rule `retRec`). A reader in the other direction also needs the reversal conditions (R3).
* R5. CLOSED marker: in its run the initial fact reached the fixed point, raised no request, had only complete edges,
  and every initial fact that serves a call inside it is closed (the greatest fixed point over recursion, computed with
  `uses`, §10.2). In run 1 its records are then exactly the concrete flow from its location set to the exit
  (`Closed.closed_records_exact`). In a restricted run they are exact and cover every DEMANDED flow from its location set
  (`RMain.closed_records_exactM`): FlowR ⊆ records ⊆ Flow.
* R6. A closed marker is valid for every later run with a limit at least the limit of the run that set it (argued: a
  complete derivation never used the cut).
* R7. Strict demand: in a restricted run, records never cause an emission. The abstraction emits only through the
  emission (§7.3).
* R8. A demand edge whose entry pattern is an initial fact `j` that was CLOSED IN RUN 1 (the unrestricted run, R5) is
  served by the records of `j` when `j` COVERS the added fact (strong enough): the abstraction emits nothing for this
  demand edge. The records are exactly the concrete flow from the location set of `j` (`closed_records_exact`), and
  the application covers each pair (`Coverage.summary_step`). A record closed in a RESTRICTED run covers only the flows
  of ITS demand (`RMain.closed_records_exactM`); it is only added (R4), never used in place of an emission. The closure
  `DR` does not model the skip; with R8 the forward run passes the segment on through the record, so the backward run
  must read the record (R3) to keep the witness (contract B).

### 10.8 Reversal

The reversal `rev(i, f)` (Lean: `revEdge`) reads a record from the other side. The new premise is the old conclusion;
the exclusion goes to the NEW CONCLUSION, so the new premise has the Empty exclusion and serves the most abstract fact:

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

The new premise mark is `i.mark` if `f.mark = *`, else `f.mark`. The new conclusion mark is `*` if `f.mark = *`, else
`i.mark`. The reversal needs a MARK-REVERSIBLE record: `f.mark = *`, or `i.mark` is concrete. A mark-producing record
under a `*`-mark premise has no reversal (`no_rev_of_star_conc`); conditional sources have concrete premise marks, so
the analysis does not make such records. With the Empty premise exclusion every row is exact
(`rev_exact_of_empty_premise`). Every initial fact of run 1 has the Empty exclusion (`policy_premEmpty`,
`answerInit_premEmpty`). In a restricted run a complete edge has an EXACT premise (`RExact.complete_premise_exact`: a
concrete premise with the `*` or `[any]` tail starts in the demand layer). So every mark-reversible complete record of
every run reverses exactly.

### 10.9 Request store (RUN 1 only, per method)

* Records: `(method, initial fact, mark)` plus the answers already emitted (for deduplication). There is no "answered"
  state: a request stands for the whole run (§8.3).
* Index: a path trie keyed by `method :: base :: path` of the request initial fact. On every new added fact, find ALL
  requests that overlap it (`standing_complete`); answer or propagate each one.

### 10.10 Vulnerability store (PERSISTENT)

* Key: `(rule, statement)` as today. The value keeps today's fields (trigger position, initial-fact groups,
  `EndFactRequirement`, rule assumptions) and adds the state (confirmed or demand) and the run.
* A CONFIRMED vulnerability (§8.1) persists: it is real (`confirmed_real`, `confirmed_real_M`). A run that reuses a closed
  initial fact replays the vulnerabilities found inside it, and their confirmation is evaluated again with the support
  of the new run.
* Every FORWARD run reports every real vulnerability: run 1 alone (`Coverage.vuln_found_policy`), every later forward
  run under the contract B (`RCov.iteration_sound`). So:
  * stopping at any forward run is sound;
  * a DEMAND vulnerability of a forward run that the next forward run does not report is REFUTED: it is not real;
  * the report of the analysis is the confirmed vulnerabilities plus the demand vulnerabilities of the last forward
    run. The vulnerabilities of a backward run only make its demand; they are not reported.

---

## 11. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

### 11.1 Soundness of run 1 — `Coverage.lean`

Hypotheses: the program is well-formed (`Program.WF`: every micro edge reads from a touched base; call bindings are
mark-agnostic) and the abstraction satisfies (A1).

| Theorem | Statement |
|---|---|
| `coverage` | If the value at the entry location `l0` of method `M` flows to `l` at node `n` (`Flow`: statements, calls, call-to-return, nested callee flows), and the initial fact `i` of `M` covers `l0`, then the analysis has an edge `(i → f)` at `n` with `den(i, f)(l0, l)`, OR the request `(M, i, l0.mark)`. |
| `coverage_conc` | If `i` has a concrete mark, the first case holds. |
| `reach_strong`, `vuln_found` | If the zero location of an entry method flows through any chain of calls to a location that a sink pattern covers (`Reach`), the analysis reports the vulnerability at that sink. |
| `coverage_policy`, `vuln_found_policy` | The same for the run-1 policy (`policy1` is `policy` with the empty demand), for every field limit. |
| `edge_conc`, `req_initial_star` | A concrete-mark initial fact has only concrete-mark conclusions; a request is always on a `*`-mark initial fact. |

That is the property "if the fact exists and the data flow exists (intra and inter procedural), the fact reaches the
destination".

### 11.2 Local lemmas — `Core.lean`, `SharedExcl.lean`

| Lemma | Statement |
|---|---|
| `applyEdge_sound` | THE CORE LEMMA: `applyEdge` covers the composition of the fact relation and the edge relation, or raises the request for the premise mark. It holds in both cases, strong enough and not strong enough. |
| `transfer_sound` | The statement transfer covers the statement step. |
| `applySummary_sound` | Summary application covers the composition with the callee flow. |
| `limitF_sound`, `CoreAux.norm_sound` | The field limit and the normal form only enlarge. |
| `startFact_sound` | The start fact covers the identity. |
| `coversB_sound`, `applicable_sound`, `applicable_mark` | The syntactic cover test is sound; an applicable mark-specific premise forces the same mark. |
| `overlapB_of_common` | Two facts with a common location overlap. |
| `check_sound`, `check_request_star` | A covered tainted location triggers the sink or raises the request. |
| `answerInit_covers`, `answerInit_applicable` | The answer covers the requested location and is applicable to the added fact. |
| `policy_applicable` | The run-1 policy satisfies (A1). |
| `SharedExcl.applyEdge_shared_excl`, `den_shared_excl` | ONE exclusion per edge: a correlated edge gives the same result (and the same pairs) when its exclusion is split between premise and conclusion as when the union is on one side. |

### 11.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`

| Theorem | Statement |
|---|---|
| `applyEdge_exact`, `limitF_exact`, `startFact_exact`, `transfer_exact` | A normal-layer result is a real composition; the middle location is computed. |
| `edge_exact`, `complete_exact` | Every pair of a normal-layer (so of every complete) edge is a concrete flow. |
| `closed_exact` | If coverage holds for an initial fact and all its exit edges are in the normal layer, its exit records are EXACTLY the concrete flow from its location set to the exit. |
| `Closed.closed_records_exact` | The same with the coverage hypothesis discharged by "no request on the initial fact" (R5). |
| `final_star_legal` | A `*` conclusion has the mark `*` and is in the normal layer (W2). |
| `star_final_keeps_initial_excl`, `star_initial_complete` | A `*/Ec` conclusion keeps the premise exclusion; a complete conclusion under a `*/Ei` premise has the `*` tail, or `Ei` is empty. |
| `applyEdge_demand_monotone`, `applySummary_demand_monotone`, `limitF_demand_monotone`, `transfer_demand_monotone`, `demand_monotone_ret` | The demand layer never goes back to normal. |
| `Confirmed.confirmed_real` | A CONFIRMED vulnerability (§8.1: complete sink edge, zero or exact-answer premise, normal-layer support chain) is a real concrete vulnerability. |
| `Confirmed.sup_entry`, `entry_reach` | A supported premise is an exact concrete-mark fact whose location is really tainted at the method entry. |
| `Confirmed.weak_support_gap`, `rev2_not_confirmed` | The weaker support condition admits a false positive; the review counter-example is not confirmed under §8.1. |

### 11.4 Concept against optimization — `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean`

| Theorem | Statement |
|---|---|
| `Tree.insert_mem`, `Tree.fromList_mem` | The `EdgeTree` (one premise, layer and exclusion; `*` leaves are flags) holds exactly its path edges. |
| `Tree.rule1_mem`, `Tree.rule1_den` | Merge rule 1 is exact (as membership). |
| `Tree.rule2_den` | Merge rule 2 is exact (on pairs) for EQUAL trees. Two `decide` counter-examples: a union of exclusions across different trees loses a pair; an intersection across different trees adds a pair. |
| `Tree.applyTreeE_mem`, `applyTreeE_den` | The tree form of `applyEdge` (for `*`-to-`*` micro edges with the mark `*`) equals the per-path `applyEdge` on whole conclusions, fact and layer. |
| `Tree.applyTreeE_grouped`, `applyTreeE_inv`, `applyTreeE_star_normal` | The output trees have distinct keys `(exclusion, layer)`; every output tree is well-formed; no demand tree has a `*` leaf. |
| `Tree.fromList_size`, `fan_list`, `fan_tree`, `prepend_shares`, `prepend_list_cost`, `walkSteps_le`, `applyListC_spec` | Cost: size `1 + Σ|path|`; `k·(p+1)` path entries against `p + k + 1` nodes; prepend adds `O(1)` nodes; the walk visits `|from.path| + 1` levels against `|fs|` calls in the list form. |
| `Store.*` | Each index returns every record that the concept filter returns: `forward_equiv_prefixes` (`byEntry`, prefix half), `backward_equiv`, `backward_equiv_prefixes` (`byExit`), `demand_complete`, `standing_complete`; keys `base :: path` (`candidatesB_base`); the split by `complete` loses nothing (`split_perm`, `next_loses_only_demand`); lookup cost `|q| + 1` key-path nodes against `|records|` tests (`prefix_query_cost`). |
| `RStore.near_equiv`, `near_sound`, `emit_complete_S`, `restrict_complete_S`, `emit_lookup_equiv_S`, `restrict_lookup_equiv_S`, `near_query_cost`, `deep_chain_cost` | The demand store (§10.6): the index query equals the list filter; it returns every demand edge for which the emission gives a fact (`emit_complete_M`) and every demand edge that can restrict a summary edge; cost walk + the length of the returned chains below `q`, not walk + count (counter-example). |
| `RStore.restrictTreeE_mem_S`, `restrictTreeE_den_S`, `restrictTreeE_inv`, `restrictTree_cost` | The restriction of a whole tree (§9.4) equals the per-path restriction, fact and layer; the result is one well-formed tree; cost `|D-p.path| + 1 + width` new cells, kept subtrees shared. |
| `Subsume.subsumes_sound` | The conclusion subsumption test of §10.1 is sound. |
| `Subsume.admits_inter`, `Subsume.merge_inter` | Merge rule 2 is exact: the intersection of exclusions denotes the union of the two relations. |
| `Subsume.union_loses_pairs` | A union of exclusions across two different conclusions loses a real pair (the forbidden merge). |
| `Subsume.record_subsumes`, `recordSubsumesB_sound` | A record `(a, p·r) → (b, q·r, */E2)` is subsumed by `(a, p) → (b, q, */E1)` when `E1` admits `r` (`r ≠ []`) or `E1 ⊆ E2` (`r = []`); `recordSubsumesB` is the decidable test. |
| `Subsume.recordSubsumesLB_sound`, `recordSubsumesLB_layer` | The test inside one class (complete with complete, demand with demand). |

### 11.5 Reversal — `Reverse.lean`

| Theorem | Statement |
|---|---|
| `revEdge_sound`, `revEdge_exact`, `rev_exact_of_empty_premise` | §10.8: sound for every mark-reversible record; exact for every mark-reversible record with the Empty premise exclusion. |
| `policy_premEmpty`, `answerInit_premEmpty`, `answerInit_markRev` | Every initial fact that the policy or a request answer emits has the Empty premise exclusion; an answer premise has a concrete mark. |
| `star_exact_no_exact_rev` | The Empty premise exclusion is necessary: `(x, ., */{f}) → (y, ., $)` has no exact reversal. |
| `no_rev_of_star_conc` | A mark-producing record under a `*`-mark premise has no reversal. |
| `Stmt.rev_step_iff` | Under `RevEdges` (every micro edge `ExactShape ∧ MarkRev`): the reversed statement summary is the converse of the statement step. |
| `flow_rev_iff_calls`, `rev_WF`, `backward_of_forward_calls` | Under `RevStmts`, `RevCalls` (and `BindTargetsStar` for `rev_WF`): the reversed program has the converse flow, with calls; it is well-formed; the backward analysis is covered by the forward theorem. |
| `backward_reuse`, `backward_reuse_needs_cover`, `backward_reuse_precise` | Reversed records cover the converse flows from the covered entry locations; the cover condition is necessary; a record without false pairs reverses into a record without false pairs. |

### 11.6 What the proofs do not cover

* The concrete semantics is alias-free and location-level (S1–S6).
* The theorems are about the closures `D` and `DR`. A real run differs from them by optimizations. Each one keeps the
  soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§10.1) | the dropped pairs are pairs of the kept fact (`subsumes_sound`); coverage needs one covering fact | the local step is proved; the composition with `D` is argued |
| merge rules 1 and 2 (§3.3, T1, T2) | exact (`rule1_mem`, `rule2_den`, `merge_inter`); the rule-2 delta re-propagates (T4) | proved |
| the T5 fold | the denotation does not change | argued |
| persisted complete records (§6.2 step 1, R4) | a complete edge has no false pair (`complete_exact`, `recs_of_DR`); adding edges keeps coverage (the rule `retRec` of `DR`) | proved |
| a demand edge served by run-1 closed records (R8) | the records are exactly the concrete flow (`closed_records_exact`), and the application covers each pair (`summary_step`) | the local steps are proved; the composition with `DR` and with B is argued |

* The contract B of the backward run (§11.7) is an assumption of `iteration_sound`. B is about SINK witnesses only:
  a contract over every witness fails even for a program without sinks (`RMain.everyWitness_contract_fails`). The model
  proves that the identity step satisfies B (`backward_identity`), and so does every step that keeps ALL summaries of
  the previous run (`backward_of_superset`). The spec's backward run keeps only the edges on the paths from the sinks
  (§10.6); that it satisfies B is argued, not proved: it is a restricted run on the reversed program, and the model has
  no rule for an unbalanced return (a backward fact that leaves the method of the sink to its callers), so the
  mirrored coverage theorem is not machine-checked. The zero demand (§8.5) is part of B.
* R6 and the greatest-fixed-point rule of R5 are argued in text only.
* The tree theorems cover the `*`-to-`*` micro edges with the mark `*`; other micro edges (rules) use the per-path
  operation on the touched subtree. The field limit inside the tree and the T5 fold are not modelled in `Tree.lean`.
* Cleaners, type filters, conditions with several literals and non-distributive edges are outside the model.

### 11.7 Restricted runs and the iteration — `Restricted*.lean`

The restricted closure `DR` (`Restricted.lean`) has the rules of `D`, with three changes: `initR` (an initial fact only
from the emission and a demand edge), `ret` (a summary edge only through a restriction by a demand edge, and only for a
satisfied premise), and `retRec` (persisted records). A DEMANDED flow (`FlowR`, `ReachR`) is a concrete flow whose
every call step has a demand edge of the callee: `D-c` covers the entry location with its mark, and `D-p` covers the
exit location.

The coverage and iteration theorems are generic over the rules: they hold for every emission, satisfaction and
restriction that satisfy the contracts `EmitContractOn` (the emission contract for the added facts of the run),
`SatContract` and `RestrictContract`.

| Theorem | Statement |
|---|---|
| `RCore.emitM_contract`, `emitM_contract_I`, `emitM_copies`, `satI_contract`, `emitM_satI` | The spec emission satisfies (A2) for concrete added facts (with `satO` and with the spec satisfaction `satI`) and copies the mark (A3); the emitted fact lies inside its added fact; `satI` satisfies its contract (`satO_contract` too). |
| `RCore.emitM_inter`, `emitM_complete`, `emitM_shape`, `emitM_chain_strong`, `emitM_sat` | The emitted fact is exactly `a ∩ D-c`; nothing is lost when the marks match; the chain is the chain of `a` or the demand chain; `a` satisfies the emitted fact. |
| `RCore.emitM_not_full` | (A2) fails for a `*`-mark added fact under a `T` demand: the concreteness of the run is necessary. |
| `RCov.concInvR_all`, `added_concR`, `no_reqR`, `RExact.DR_concrete`, `DR_no_request`, `final_not_star`, `RMain.no_request_M` | A restricted run with a mark-copying emission is CONCRETE: every initial fact, edge and added fact has a concrete mark, no final fact has the `*` tail, and the run has NO request. |
| `RCov.emitOn_of_conc` | (A2) for concrete facts and (A3) give the emission contract of the run. |
| `RExact.restrict_U_eq_S`, `RCore.restrictU_eq_S_nonstar`, `restrictS_contract` | In a concrete run the agreed restriction gives the same run as the version-3 repair, whose contract holds. |
| `RExact.complete_premise_exact` | A complete edge of a concrete run has an exact premise, so its record reverses exactly. |
| `RCases.p1_reachR_M`, `p1_found_M`, `p2_reachR_M`, `p2_found_M` | Programs 1 and 2: the vulnerability is real and demanded, and the version-4 rules (with the agreed restriction) report it in forward run 3. |
| `RCov.coverageR` | THE COVERAGE OF A RESTRICTED RUN: for a demanded flow from a covered entry location, an edge covers the pair or the run has the request; moreover the run's own summaries demand the same flow. |
| `RCov.reach_strongR`, `vuln_foundR` | A restricted run reports every real vulnerability whose witness is demanded, and its own summaries demand the witness again. |
| `RCov.coverageD`, `reach_to_reachR`, `vuln_foundD` | Run 1 reports every real vulnerability, and its summaries demand its witness. |
| `RCov.iteration_sound`, `iteration_sound_conc` | THE ITERATION THEOREM. Run 1 is `D` with `policy1`; run k+1 is `DR` with the demand `dem k`, any field limits, any records. If every backward step satisfies the contract B — `BackwardContract`: every vulnerability witness (a location at a sink that the sink pattern covers) that the summaries of forward run k demand stays demanded by `dem k` — then EVERY forward run reports every real vulnerability. |
| `RMain.vuln_found_M`, `iteration_sound_M`, `iteration_sound_M_identity`, `closed_records_exactM`, `confirmed_real_M` | The theorems instantiated with the spec rules `emitM`, `satI`, `restrictU`. |
| `RCov.backward_identity`, `backward_of_superset`, `iteration_sound_identity` | The identity backward step (the demand of run k+1 is the summaries of run k) satisfies B, and so does every step that keeps at least all those summaries. |
| `RMain.noSink_contract`, `everyWitness_contract_fails` | B is about sink witnesses only: without sinks the empty demand satisfies B; a contract over every witness would fail. |
| `RCov.flowR_mono`, `reachR_mono`, `flowR_flow`, `reachR_reach` | A larger demand keeps a witness; a demanded flow is a flow. |
| `RExact.edge_exactR`, `complete_exactR` | A normal-layer edge of a restricted run denotes only real flows, if the restriction only removes pairs and the reused records are exact. |
| `RExact.recs_of_DR`, `recs_of_D`, `recs_step` | The exit edges of every run are exact records, so persisted records can be reused by every later run. |
| `RExact.closed_exactR` | R5 for a restricted run: with only normal exit edges, demanded flows ⊆ records ⊆ real flows (no request: automatic in a concrete run). |
| `RExact.final_star_legalR`, `star_final_keeps_initial_exclR`, `star_initial_completeR`, `DR_NS` | The invariants of §11.3 hold in every restricted run, with no hypothesis on the rules. |
| `RExact.SupM`, `ConfirmedM`, `sup_entryM`, `confirmed_realM` | A confirmed vulnerability of a restricted run is real; the support accepts the emitted exact fact (`SupR → SupM`). |
| Version 3 (record of the review): `RCore.emitS_contract`, `satS_contract`, `emitU_fails`, `restrictU_fails`; `RCases.p1_found_S`, `p1_lost_U`, `p2_found_S`, `p2_lost_U`; `RMain.iteration_sound_S` | The location-only rules: the agreed rows lose programs 1 and 2; the version-3 repairs report them. |

---

## 12. The formal model

| File | Content |
|---|---|
| `Basic.lean` | All definitions of run 1: locations, facts, `den`, `applyEdge`, the normal form, the field limit, statements, calls, `Flow`, the closure `D`, `Reach`, `answerInit`, `policy`, `revEdge`. |
| `Restricted.lean` | The definitions of the restricted runs: demand edges, the spec emission `emitM` (with `meetK`, `markMatchB`), the spec satisfaction `satI` (and the overlap form `satO`), the restriction `restrictU` (and the version-3 rules `emitU`/`emitS`, `satU`/`satS`, `restrictS`), the closure `DR`, `FlowR`, `ReachR`, the contracts, `summaryDemand`, `BackwardContract`. |
| `Cases.lean`, `RestrictedCases.lean` | The cases of bidirectional-task.md and every decision of the reviews as test vectors, checked by `decide`; programs 1 and 2. |
| `Core.lean`, `SharedExcl.lean`, `RestrictedCore.lean` | The local lemmas (§11.2, §11.7). |
| `Coverage.lean`, `RestrictedCoverage.lean`, `RestrictedMain.lean` | Soundness of run 1 (§11.1) and of the iteration (§11.7); `RestrictedMain` instantiates the generic theorems with the spec rules. |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean`, `RestrictedExact.lean` | Exactness, invariants, closed reuse, confirmed vulnerabilities (§11.3, §11.7). |
| `Tree.lean`, `Store.lean`, `Subsume.lean`, `RestrictedStore.lean` | Concept against optimization (§11.4). |
| `Reverse.lean` | Reversal (§11.5). |

Build and audit:

```
cd spec/lean && lake build 2>&1 | grep "depends on axioms" | sed 's/.*axioms: //' | sort | uniq -c
```

The audit passes when the only sets are `[propext]` and `[propext, Quot.sound]` (and declarations with no axioms).
At the time of writing: 418 audited declarations (239 `[propext, Quot.sound]`, 122 `[propext]`, 57 with no axioms), no
`sorry`, no `native_decide`, and 203 test vectors checked by `decide` (61 in `Cases.lean`, 127 in `RestrictedCases.lean`,
15 in `RestrictedStore.lean`).

---

## 13. Test plan (TDD)

Write the tests first. Each test names the spec item that it checks.

1. Vector tests (`ApplyEdgeVectorsTest`): one test per `example` in `Cases.lean` and `RestrictedCases.lean`, on the
   concept implementation (§4.1 reference form) and on the tree implementation.
2. Equivalence property test (`EdgeTreeEquivalenceTest`): random path facts and micro edges; the tree result denotes the
   same pairs as the concept result, layer included. Check pairs by bounded enumeration of `σ, τ` up to length 3. The
   same for the tree restriction (§9.4).
3. Layer tests: the conditional-source example of §4.4; a cut fact is demand; a demand input gives a demand output; a
   `*` conclusion is never in the demand layer; a `*` fact applied above a premise gives a demand result.
4. Builder tests (`StatementSummaryBuilderTest`): no exclusion update on a read; the self-write; the identity edges of
   source and pass rules; the static write gives the expected demand.
5. Merge tests: rule 1, rule 2, and a test that a union of exclusions is never made.
6. Request tests: the mark gate raises a request; a standing request is answered by a later added fact and by a second
   added fact; propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain.
7. Call tests: the four steps of §6.2; a caller reads the summaries of an answered initial fact (run 1); in a
   restricted run a caller reads the summaries of every premise that overlaps its fact with an admitted mark.
8. Abstraction tests: run 1 emits the most abstract fact; every row of the two tables of §7.3 (marks, locations); the
   emitted fact is exactly `a ∩ D-c` with the mark of `a`; the same result for two insertion orders.
8a. Concreteness tests: in a restricted run no fact has the mark `*`, no final fact has the `*` tail, and no request is
   raised (assert it in the analyzer: a request in a restricted run is a bug).
9. Restriction tests: every row of the table of §6.4; the union over two demand edges; no result without `D-p`.
10. Iteration tests: programs 1 and 2 as analysis tests with a forward limit 3 and a backward limit 2. The vulnerability
    must be reported in every forward run.
11. Store tests: index completeness against a list filter (records, demand edges, requests); split by layer; the closed
    marker only for all-complete initial facts without requests.
12. Reversal tests: every row of §10.8; the forward record and its reversed reading give converse results on the same
    concrete pair.
13. Analysis tests (phase 2 gate): the existing `*AnalysisTest` suites, run with `cleanTest`. A lost finding is a test
    whose message says that no vulnerability reached the sink; read the message, do not count failures.

---

## 14. Decision log

Each line comes from a failed proof, a counter-example checked by `decide`, a review comment, or the design discussion.

| # | Topic | Outcome |
|---|---|---|
| F1 | "No `[any]` ⇒ complete" | Changed: the demand layer (`~`, `Zero~`), set by every approximation step (§2.5, §4.4). |
| F2 | Read builder | Adopted: a read never changes an exclusion (§4.2). |
| F3 | One static base per class | Withdrawn: the class accessor stays; a static write gives a demand that the abstraction resolves (§4.5). |
| F4 | Abstraction determinism | Adopted (§7.1). |
| F5 | Requests for mark-specific rules | Adopted (§8.2). |
| F6 | Callers of an answered initial fact | Requirement: a caller reads every summary whose premise its fact satisfies (§6.2). |
| F7 | Reversed records instead of an analysis | Replaced by the strict demand (R7, R8) and the iteration theorem (§11.7). |
| F8 | Reversal shapes | Assertion: exact for every mark-reversible record with the Empty premise exclusion (§10.8). |
| F9 | Normal form | Adopted (§4.1 step 6). |
| F10 | Exclusion of a reversed record | Adopted: on the new conclusion (§10.8). |
| F11 | Request store index | Adopted: path index, overlap query (§10.9). |
| F12 | Index keys | Adopted: `base :: path`; the forward lookup uses the prefix half (§10.7 R2). |
| F13 | `applicable` | Adopted for run 1: necessary for soundness (§6.3). A restricted run uses the reverse cover (`satI`, F36). |
| F14 | Answer by the meet | Withdrawn: the answer keeps the request chain (§8.3). |
| F15 | Mark of the emitted fact | Run 1: `(x, chain, *, {}, *)`, the task rule (§7.2). A restricted run: the mark of the added fact (F34). |
| F16 | `lostCorr` | Adopted: an uncorrelated result without a lost restriction stays in the normal layer (§4.1). |
| F17 | Standing requests | Adopted (§8.3). |
| F18 | Conclusion subsumption | Adopted: `subsumesB`, not `coversB` (§10.1). |
| F19 | Closed marker | Adopted: no request (R5). |
| F20 | Identity edges of rules | Adopted: source and pass rules keep their premise base; the self-write has none (§4.2). |
| F21 | Zero fact | Adopted: served by the zero fact in run 1 (§7.2); in a restricted run a zero demand emits the zero fact itself (§7.3). |
| D1 | Exclusion | Per path edge, shared by premise and conclusion; merge rules 1 and 2; no union merge (§3.3, §9.2). |
| D2 | Call processing | The four steps (§6.2). |
| D3 | Runs | Superseded by D5. |
| F22 | Confirmation | A complete sink edge is not enough; a confirmed vulnerability needs a normal-layer support chain (§8.1; review counter-example; `confirmed_real`). |
| F23 | Approximating rules | Cleaners that keep `*`-mark facts and over-approximated conditions put the result in the demand layer (§4.4). |
| F24 | Rule-2 delta | Merge rule 2 propagates the whole merged tree (T4). |
| F25 | Fold | The T5 fold only inside demand trees (§9.2). |
| D4 | Record subsumption | `(a, p) → (b, q)` subsumes `(a, p·r) → (b, q·r)` inside the complete layer (§11.4). |
| D5 | Strict demand | Run 1 is unrestricted; every later run emits only through the emission (§7.3) and applies summaries only through the restriction (§6.4). Soundness is iteration-relative: every forward run reports every real vulnerability under the contract B (`iteration_sound`). |
| F26 | One edge exclusion | The tables of §4.1 use ONE exclusion `E` per edge; the model's two-sided storage is equivalent (`applyEdge_shared_excl`). The cases are named "strong enough" (`below`) and "not strong enough" (`above`). |
| F27 | Emission: `*` above the demand chain (version 3) | SUPERSEDED by F34: a restricted run has no `*` added fact. Version-3 text: CHANGED against the agreed table (nothing → the demand chain). Program 1 loses a real vulnerability with the agreed row (`p1_lost_U`, `emitU_fails`). Cost: a flow through this row is applied not strong enough, so it is in the demand layer even from a normal caller fact and cannot be confirmed in that run; it is confirmed only when the backward limit grows enough to make the caller demand deep enough. With `satS`, a `*` fact also reads the summaries of every deeper initial fact on its chain (extra `[any]` demand results). Alternative (B): emit the added fact's own chain `(b, a.path, *, {}, *)`: it is strong enough, the result stays normal, and (A2) holds (the emitted fact covers `a`); but the callee analyses more than the demand asks for. |
| F28 | Restriction: correlated `*` above `D-p` (version 3) | SUPERSEDED by F34: the agreed rule stays (`restrict_U_eq_S`). Version-3 text: CHANGED against the agreed rule (empty → keep the edge). Program 2 loses a real vulnerability with the agreed rule (`p2_lost_U`, `restrictU_fails`). Cost: for the common shape `(arg, ., *) → (ret, ., *)` the edge is kept whole, so the demand does not filter it. Alternative: the exact intersection — the premise moves down, `(x, p·r, *) → (y, q·r, *)`; it filters, but a caller fact at `p` is then not strong enough and gets a demand result (not checked in the model). |
| F29 | Satisfaction (version 3) | SUPERSEDED by F36. Version-3 text: | A fact satisfies a premise if the premise covers it, or (restricted runs) if it is `[any]`, or `*` with an admitting exclusion, above the premise, with an admitted mark (§6.3). The `*` part goes with F27. |
| F30 | Records in restricted runs | Records of every run are exact (`recs_of_DR`) and are added whenever the caller fact satisfies their premise (R4, `retRec`). Only a record closed in run 1 may replace an emission (R8); a closed record of a restricted run covers only the flows of its own demand (`closed_records_exactM`). |
| F31 | Report rule | Every forward run reports every real vulnerability (D5), so a demand vulnerability that the next forward run does not report is refuted (§10.10). |
| F32 | Backward contract | B is about sink witnesses only (review H1; `everyWitness_contract_fails`). |
| F33 | Zero demand | The backward run continues a requirement through the reversed source edge to the zero fact, and keeps the zero and static bindings, so the forward run emits the zero fact where a source needs it (§8.5; review H2). |
| F34 | Mark-aware emission (version 4, the user's rule) | A restricted run emits `a ∩ D-c` with the mark of `a`; a `T` demand needs the fact mark `T` (§7.3). Programs 1 and 2 are reported with the agreed rows (`p1_found_M`, `p2_found_M`). Cost: no sharing between added facts. |
| F35 | No request after run 1 (the user's rule) | A `*` added fact never meets a `T` demand: the run starts from the zero fact and the emission copies the concrete mark, so a restricted run is concrete and raises no request (`no_reqR`, `DR_no_request`, `no_request_M`). Requests and the answer rule are used only in run 1. Condition: no `*`-premise callee summary in a restricted run (§4.2). |
| F36 | Satisfaction in a restricted run | The premise lies inside the fact, with an admitted mark (§6.3, `satI`). The overlap form `satO` is sound but lets a precise fact read a coarser sibling premise (review of version 4, M2). |
| F38 | Backward seeds | A backward run seeds directly at the sink statements of the reported vulnerabilities, not through a zero fact at the method exit (§8.5; review of version 4, H1). |
| F37 | Support in a restricted run | The confirmation accepts the emitted exact concrete fact as a supported premise (`SupM`), since there are no answers (§8.1). |
