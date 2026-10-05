# Access paths and storages — specification

Status: design spec for phase 1 of [bidirectional-task.md](../bidirectional-task.md) ("New AP with all required
storages"), version 2 (after the design review with the user). The formal model is in [`spec/lean`](lean). Every
theorem named here is machine-checked and constructive (§12).

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope

This spec defines:

* the fact representation (the access path, "AP") for the forward and the backward analysis;
* the operations on facts: statement transfer, call binding, summary application, field limit, rule checks, mark
  requests, abstraction, reversal;
* the storages that the analyzer uses in one run and across runs;
* the soundness theorems for these operations and the scope in which they hold.

This spec does not define the analyzer scheduling, the iteration driver or the trace resolution. It defines the
contracts that these parts use.

### 0.1 The restricted scope of the proofs

The theorems hold for this model. Each item is an assumption of the proof, not a property of the code.

| # | Assumption | Who must make it true |
|---|---|---|
| S1 | A statement is described by its summary: the bases that it touches and its micro edges (§4.2). | The summary builder (`JIRStatementSummary`, `GoStatementSummary`). |
| S2 | Aliasing is described by extra micro edges (gen edges to alias paths). The model itself is alias-free. | The alias analysis. |
| S3 | Formal parameters are not reassigned inside the method. | The IR (JIR keeps arguments immutable). |
| S4 | A method has one exit node per exit kind. The model has one exit node. | The CFG normalisation. |
| S5 | A type filter only removes facts that have no concrete instance. | The type checker. |
| S6 | The result of one run is the least fixed point of the rules of §4–§8 (Lean: the inductive predicate `D`). The worklist may compute it in any order. | The analyzer. |

Inside this scope every run is SOUND: an edge covers every concrete flow, and every concrete source-to-sink flow is
reported (§11.1). The theorems are about the closure `D`; §11.6 lists the optimizations of a real run (subsumption,
merges, the fold, record reuse) and why each one keeps the soundness. Inside the smaller scope of COMPLETE edges the
analysis is also EXACT: every pair of a complete edge is a concrete flow (§11.3), and a CONFIRMED vulnerability is a real
one (`Confirmed.confirmed_real`). The field limit and the forward/backward iteration move facts from the first scope into
the second.

### 0.2 Decisions of the design review

The task text is the base. The review with the user refined it as follows (details in §14):

| Topic | Decision |
|---|---|
| Completeness | An edge is complete if it is in the normal layer and its conclusion has no `[any]`. Every approximation step moves the edge to the DEMAND layer (`~`, `Zero~`), also when the result has no `[any]`. |
| Exclusion | One exclusion per path edge, shared by premise and conclusion. Two merge rules (§3.3). A union of exclusions across different conclusions is forbidden. |
| Read | A field read never changes an exclusion. Only a field write does. |
| Statics | One `ClassStatic` base with the class accessor. A static write on the abstract static fact gives a demand that the abstraction resolves. |
| Calls | Four steps: apply the current summaries, add the fact to the callee, the callee abstraction emits per the demand, new summaries are applied (§6.2). A caller reads every summary whose premise its fact satisfies. |
| Requests | The task rule for the answer (no chain deeper than the request). Requests stand for the whole run. Mark-specific rules raise requests too. |
| Runs | Every forward run is sound, so stopping at any run is sound. Confirmed vulnerabilities persist. A vulnerability is confirmed only through a normal-layer support chain (§8.1). |

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
| edge | (premise, layer, statement, conclusion). The zero fact is also a premise. |
| layer | `normal` or `demand`. The demand layer of premise `i` is written `i~`; of the zero fact, `Zero~`. |
| micro edge | One edge of a statement summary (`StatementSummary.Edge`). |
| summary edge, record | An edge whose statement is the method exit. A persisted complete summary edge is a record. |
| complete edge | An edge in the normal layer whose conclusion has no `[any]` tail. |
| demand edge | Every other edge. Its conclusion is a demand final. |
| added fact | A caller fact rebased to the callee bases at a call site. |
| abstraction (α) | The function that selects the initial fact for an added fact. §7. |
| request | A request for a concrete mark on an initial fact. §8. |
| run | One analysis pass in one direction with one field limit `L` (forward-1, backward-2, ...). |
| method key | `MethodEntryPoint` (context plus entry statement), as today. |

---

## 2. The fact (the concept)

### 2.1 The tuple

A fact is `(base, path, tail, exclusion, mark)`:

* `path` — the concrete accessors. It never contains `[any]`, a mark or `$`.
* `tail ∈ {*, [any], $}`.
* `exclusion` — only with the `*` tail.
* `mark ∈ {*, T}` — abstract (pass the mark of the premise through) or concrete.

### 2.2 Edges, layers and exclusions

An edge is `(premise, layer) → (statement, conclusion)`. The zero-to-fact edge is `Zero → (layer, statement, fact)`.

* The EXCLUSION belongs to the path edge. The premise and the conclusion share it: for `(x, p, *) → (y, q, *)` with the
  exclusion `E`, the value at `x.p.σ` flows to `y.q.σ` for every `σ` that `E` admits.
* An uncorrelated conclusion (`$` or `[any]`) has the Empty exclusion.
* Every initial fact that the abstraction emits has the Empty exclusion. So in practice the exclusion is a property of
  the conclusion. It grows only by a field write (a kill).
* The LAYER is part of the edge identity. An edge goes to the demand layer when a step of its derivation
  over-approximates (§4.4). It never goes back (`Invariant.applyEdge_demand_monotone` and the related lemmas).

Lean: `PFact` (a premise or a conclusion; the conclusion `*/E` carries the exclusion of the edge) and `AFact` (a
conclusion plus `demand : Bool`, the layer).

### 2.3 Well-formedness rules

| Rule | Text |
|---|---|
| W1 | A non-`*` tail has the Empty exclusion. |
| W2 | A conclusion with the `*` tail has the mark `*` and is in the normal layer. A premise may have the `*` tail with a concrete mark (a request answer). |
| W3 | A path has at most `L` counted accessors in a run with the field limit `L` (§5). |
| W4 | `[any]` is a tail only. A path has no inner `[any]`. |
| W5 | Marks are not accessors. `TaintMarkAccessor`, `FinalAccessor` and `AnyAccessor` do not occur in a path. |

W2 holds for every derived fact (`Invariant.final_star_legal`).

### 2.4 The zero fact

The zero fact is `(zero, [], $, {}, zeroMark)`. A source rule is a micro edge from the zero fact (§4.2). Zero-to-fact
edges are edges with the zero premise, in the normal or the demand layer.

### 2.5 Classification

* COMPLETE edge: normal layer and no `[any]` in the conclusion (Lean: `AFact.complete`). Complete edges are persisted
  and reused in later runs and in the other direction (§10.7).
* DEMAND edge: every other edge. Demand edges are used in their own run like every edge. Their conclusions at the
  method exit are the DEMAND of the next run (§10.6). They are never persisted and never reversed.
* A rule that assigns a mark on `[any]` makes a demand edge. That is intended. Such a demand cannot go away, so the
  driver stops when the demand set no longer changes (not when it is empty).

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
`PFact.covers`, `den`.

### 3.3 Exclusion algebra

* The effective exclusion of a correlated edge is the union of the premise exclusion and the conclusion exclusion. It
  does not matter on which side it is stored. The model stores it on the conclusion.
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

`applyEdge(c, from → to)` applies an edge `from → to` to the conclusion `c` of a current edge. The edge is one of:

* a statement micro edge (§4.2);
* a call binding edge: caller base to callee base, or callee exit base to caller base (§6);
* a callee summary edge `(premise j → conclusion g)` (§6.3).

All flow functions use this ONE operation. Lean: `applyEdge` in `Basic.lean`.

Step 1 — base. If `c.base ≠ from.base`, the result is empty.

Step 2 — position. Compare the paths:

* `below r`: `c.path = from.path ++ r` (the fact is at or below the premise);
* `above r`: `from.path = c.path ++ r`, `r ≠ []` (the fact is above the premise);
* `apart`: neither. The result is empty.

Step 3 — overlap and result shape. `Ec` is the exclusion of `c` (for a `*` tail), `Ef` the premise exclusion (`*/Ef`
gives `Ef`, `[any]` gives `{}`, `$` gives Universe), `Et` the conclusion exclusion of the edge.

Case `below r`. The premise tail must admit `r` (`*/Ef`: `Ef` admits `r`; `$`: `r = []`). Then:

| `to.tail` | `r` | `c.tail` | result path | result tail | demand step |
|---|---|---|---|---|---|
| `*/Et` | `≠ []` (needs `Et` admits `r`) | any | `to.path ++ r` | `c.tail` | no |
| `*/Et` | `[]` | `$` | `to.path` | `$` | no |
| `*/Et` | `[]` | `*/Ec` | `to.path` | `*/(Ec ∪ Ef ∪ Et)` | no |
| `*/Et` | `[]` | `[any]` | `to.path` | `$` if `Ef ∪ Et = Universe` | no |
| `*/Et` | `[]` | `[any]` | `to.path` | `[any]` otherwise | yes if `Ef ∪ Et ≠ {}` |
| `[any]` | any | `*/Ec` | `to.path` | `[any]` | `lostCorr` |
| `[any]` | any | `[any]` or `$` | `to.path` | `[any]` | no |
| `$` | `[]` | `*/Ec` (and `from.tail = $`) | `to.path` | `*/Universe` | no |
| `$` | any | `*/Ec` (other) | `to.path` | `$` | `lostCorr` |
| `$` | any | `[any]` or `$` | `to.path` | `$` | no |

`lostCorr` is true if the correlation of `c` restricts the premise continuation: `Ec ∪ Ef ≠ {}` for `r = []`,
`Ec ≠ {}` for `r ≠ []`. Otherwise every premise continuation is admitted, and the uncorrelated result is exact
(`Exact.applyEdge_exact`).

Case `above r`. The fact tail must admit `r` (`*/Ec`: `Ec` admits `r`; `[any]`: yes; `$`: no overlap). The result is not
correlated:

| `to.tail` | result tail at `to.path` | demand step |
|---|---|---|
| `*/Et` | `[any]` | yes, except `c.tail = [any]` and `Ef ∪ Et = {}` |
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

Reference form (the vector tests of §13 compare the tree implementation with it):

```kotlin
sealed interface Tail {
    data class Star(val exclusion: ExclusionSet) : Tail
    data object AnyTail : Tail      // not `Any`: that name hides kotlin.Any
    data object Exact : Tail
}

data class PathFact(val base: AccessPathBase, val path: List<Accessor>, val tail: Tail, val mark: ApMark)
data class Conclusion(val fact: PathFact, val demand: Boolean)     // the layer of its edge

fun Tail.admits(r: List<Accessor>): Boolean = when (this) {
    is Tail.Star -> r.isEmpty() || r.first() !in exclusion   // Universe contains every accessor
    Tail.AnyTail -> true
    Tail.Exact -> r.isEmpty()
}

fun Tail.premiseExclusion(): ExclusionSet = when (this) {
    is Tail.Star -> exclusion
    Tail.AnyTail -> ExclusionSet.Empty
    Tail.Exact -> ExclusionSet.Universe
}

private class Shape(val path: List<Accessor>, val tail: Tail, val demand: Boolean)

/** The correlation restriction that an uncorrelated result forgets (Lean `lostCorr`). */
private fun lostCorr(ck: Tail, fk: Tail, r: List<Accessor>): Boolean = when (ck) {
    is Tail.Star ->
        if (r.isEmpty()) ck.exclusion.union(fk.premiseExclusion()) !== ExclusionSet.Empty
        else ck.exclusion !== ExclusionSet.Empty
    else -> false
}

private fun below(ck: Tail, fk: Tail, r: List<Accessor>, to: PathFact): Shape? {
    if (!fk.admits(r)) return null
    return when (val tk = to.tail) {
        is Tail.Star ->
            if (r.isNotEmpty()) {
                if (tk.admits(r)) Shape(to.path + r, ck, demand = false) else null
            } else {
                val ex = fk.premiseExclusion().union(tk.exclusion)
                when (ck) {
                    Tail.Exact -> Shape(to.path, Tail.Exact, false)
                    is Tail.Star -> Shape(to.path, Tail.Star(ck.exclusion.union(ex)), false)
                    Tail.AnyTail ->
                        if (ex === ExclusionSet.Universe) Shape(to.path, Tail.Exact, false)
                        else Shape(to.path, Tail.AnyTail, demand = ex !== ExclusionSet.Empty)
                }
            }
        Tail.AnyTail -> Shape(to.path, Tail.AnyTail, demand = lostCorr(ck, fk, r))
        Tail.Exact -> when {
            ck is Tail.Star && fk == Tail.Exact && r.isEmpty() ->
                Shape(to.path, Tail.Star(ExclusionSet.Universe), false)
            ck is Tail.Star -> Shape(to.path, Tail.Exact, demand = lostCorr(ck, fk, r))
            else -> Shape(to.path, Tail.Exact, false)
        }
    }
}

private fun above(ck: Tail, fk: Tail, r: List<Accessor>, to: PathFact): Shape? {
    if (!ck.admits(r)) return null
    return when (val tk = to.tail) {
        is Tail.Star -> Shape(to.path, Tail.AnyTail,
            demand = !(ck == Tail.AnyTail && fk.premiseExclusion().union(tk.exclusion) === ExclusionSet.Empty))
        Tail.AnyTail -> Shape(to.path, Tail.AnyTail, demand = ck != Tail.AnyTail)
        Tail.Exact -> Shape(to.path, Tail.Exact, demand = ck != Tail.AnyTail)
    }
}

sealed interface EdgeOutcome {
    data object None : EdgeOutcome
    data class Fact(val conclusion: Conclusion) : EdgeOutcome
    data class Request(val mark: ApMark) : EdgeOutcome
}

fun applyEdge(c: Conclusion, from: PathFact, to: PathFact): EdgeOutcome {
    if (c.fact.base != from.base) return EdgeOutcome.None
    val p = from.path
    val q = c.fact.path
    val shape = when {
        q.size >= p.size && q.subList(0, p.size) == p -> below(c.fact.tail, from.tail, q.drop(p.size), to)
        p.size > q.size && p.subList(0, q.size) == q -> above(c.fact.tail, from.tail, p.drop(q.size), to)
        else -> null
    } ?: return EdgeOutcome.None
    if (!from.mark.isStar) {                                   // the mark gate
        if (c.fact.mark.isStar) return EdgeOutcome.Request(from.mark)
        if (c.fact.mark != from.mark) return EdgeOutcome.None
    }
    val mark = if (to.mark.isStar) c.fact.mark else to.mark
    return EdgeOutcome.Fact(normalize(PathFact(to.base, shape.path, shape.tail, mark), c.demand || shape.demand))
}

/** Step 6. */
fun normalize(f: PathFact, demand: Boolean): Conclusion {
    val t = f.tail
    if (t !is Tail.Star || (f.mark.isStar && !demand)) return Conclusion(f, demand)
    val tail = if (t.exclusion === ExclusionSet.Universe) Tail.Exact else Tail.AnyTail
    return Conclusion(f.copy(tail = tail), demand = true)
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

The builder (`StatementSummaryBuilder`) emits these micro edges. A micro edge `x.*/{f} → x.*` has the exclusion `{f}`.

| Statement | Micro edges; touched bases | Note |
|---|---|---|
| `a = b` | `b.* → b.*`, `b.* → a.*`; `{a, b}` | |
| `a = b.f` (`a ≠ b`) | `b.* → b.*`, `b.f.* → a.*`; `{a, b}` | A read never changes an exclusion. The current `keepAllExcept` on a read goes. |
| `a = a.f` | `a.f.* → a.*`; `{a}` | no refine-only edge |
| `a.f = b` (`a ≠ b`) | `a.*/{f} → a.*`, `b.* → b.*`, `b.* → a.f.*`; `{a, b}` | strong update: the only exclusion update |
| `a.f = a` | `a.*/{f} → a.*`, `a.* → a.f.*`; `{a}` | no identity edge for `a`: it would bring back the killed `a.f` |
| `a[i] = b` | `a.* → a.*`, `b.* → b.*`, `b.* → a.[e].*`; `{a, b}` | weak update |
| alias `(c, p)` of `a` in `a.f = b` | `b.* → c.p.f.*` | gen only |
| `C.s = b` | `S.*/{C} → S.*`, `S.C.*/{s} → S.C.*`, `b.* → b.*`, `b.* → S.C.s.*`; `{S, b}` | `S` is the `ClassStatic` base, `C` the class accessor (§4.5) |
| `x = C.s` | `S.* → S.*`, `S.C.s.* → x.*`; `{S, x}` | |
| source of `T` at `x` | `zero.$ → zero.$`, `zero.$ → x.$` with the mark `T`, both with the premise mark `zeroMark`; `{zero, x}` | the identity keeps the zero fact; the concrete premise mark makes the record mark-reversible |
| pass rule from `x` to `y` | `x.* → x.*`, `x.* → y.*`; `{x, y}` | a subtree move: delta-concat keeps `[any]` |
| conditional source: `x` carries `T` ⇒ `y` gets `T2` | `x.* → x.*`, `x.$ (T) → y.$ (T2)`; `{x, y}` | the premise mark `T` raises a request on a `*`-mark fact (§8.2) |
| any-field rule (`AssignMarkOnAnyAccessor`) | `zero.$ → x.[any]` with the mark `T` | a demand edge (§2.5) |
| sink | a check (§8.1), not a micro edge | |
| cleaner | §8.4 | |

An external (unresolved) callee has no body. Its summary is the pass rules of its own rules plus the identity edges of
its arguments (as `propagateUnresolvedCallFact` does today).

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

### 4.4 The steps that make a demand edge

| Step | Example |
|---|---|
| a correlated `*` fact becomes uncorrelated while a restriction is lost (`above`, `lostCorr`) | `a = b.f` on `(b, ., *, E, *)` |
| the field-limit cut | `b.h = box` with `box.f` tainted, under `L = 1` |
| an `[any]` fact ignores a premise exclusion | `below`, `r = []`, `Ef ∪ Et ≠ {}` |
| the start of a request answer with the `*` tail and a concrete mark | `(x, .f, *, {}, T)` starts as `(x, .f, [any], {}, T)` |
| the start of an `[any]` premise | |
| the normal form (step 6) | a mark-producing exact rule on a `*` fact |
| a summary edge of the demand layer is applied | the caller edge goes to the demand layer |
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
demand layer the edge is not persisted, and the next iteration refines it. The same happens without a request after a
field-limit cut (`Cases.lean`, "F1").

### 4.5 Static fields

The `ClassStatic` base `S` with the class accessor stays. A method that does not touch statics keeps the one abstract
static fact `(S, ., *, {}, *)` exact through an identity summary, which is cheap. A static write `C.s = v` on that fact
gives `(S, ., *, {C}, *)` (normal) and `(S, .C, [any])` (demand; `Cases.lean`, "two-level strong update"). The next
iteration resolves the demand by the abstraction. The split happens in the method where the static fact is concrete, so
the refinement goes up the call chain one iteration at a time.

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

---

## 6. Calls

### 6.1 Concrete semantics (the model)

A call `r = m(a1..an)` has: the touched caller bases (the arguments, the result, the static base), the binding edges
into the callee (`ai.* → argi.*`, `S.* → S.*`, `zero → zero`), and the binding edges back (`argi.* → ai.*`,
`return.* → r.*`, `S.* → S.*`). A caller location on an untouched base passes over the call. A location on a touched base
goes into the callee and comes back through the callee flow. Lean: `Call`, `Flow.pass`, `Flow.call`.

### 6.2 Call processing

For a caller edge `(i, layer) → c` at a call:

0. If `c.base` is not touched: pass `c` (call-to-return).
1. APPLY THE CURRENT SUMMARY EDGES. For each binding edge `e` into the callee, `a = applyEdge(c, e)`. Apply every
   summary edge of the callee whose premise `a` satisfies (§6.3): the summaries of every applicable initial fact of this
   run, and every applicable persisted complete record (§10.7). Then apply the binding edges back and the field limit.
2. ADD `a` to the added set of the callee, with the caller edge (for request propagation).
3. The CALLEE ABSTRACTION emits the initial fact for `a` per the demand (§7.2), if it is new.
4. NEW SUMMARY EDGES of any initial fact applicable to `a` are delivered to the caller and applied as in step 1. The
   subscription stands for the whole run.

The result layer is the caller layer, or the summary layer, or a demand step of the application.

### 6.3 Summary application

`applySummary(a, j, g) = applyEdge(a, j → g)`, with the layer of the summary edge added and the normal form. The premise
`j` must be APPLICABLE to `a`:

```
applicable(j, a)  ⇔  covers(j, ·) ⊇ covers(a, ·)  ∧  (j.tail = [any] ⇒ a.tail = [any])
```

The first part is "the fact in the caller context is strong enough to satisfy the premise". The second is the syntactic
`[any]` rule. Lean: `coversB`, `applicable`, `applicable_sound`.

* The premise exclusion is Empty for every emitted initial fact (`Reverse.policy_premEmpty`,
  `Reverse.answerInit_premEmpty`; a reversed premise also has it, §10.8). So the `applicable` test, which reads the
  premise, in effect ignores the edge exclusion. The exclusion of the summary edge is on its conclusion, and it FILTERS
  the delta: `(x, ., *) → (ret, ., */{f})` applied to `(y, ., */{})` gives `(r, ., */{f})`, and applied to
  `(y, .f.g, $, T)` gives nothing.
* Because `j` covers `a`, the application is always the case `below` of §4.1, and the mark gate always passes
  (`applicable_mark`). A partial overlap is never applied.
* The rule `applicable` is necessary for soundness: the analysis has no rule for a request raised by a summary
  application, because `applicable` makes such a request impossible.

---

## 7. Abstraction

### 7.1 Contract

`α(m, a)` is a function of the method `m`, the added fact `a`, and constants of the run (the field limit, the demand of
the previous run, the closed initial facts of earlier runs). It must satisfy:

```
(A1)  applicable(α(m, a), a)
```

The coverage theorem needs only (A1). The policy decides the precision and the cost. `α` must not depend on the order of
events: the run result is then the least fixed point and does not depend on the schedule.

### 7.2 The policy (bidirectional-task.md §4)

For the added fact `a` of method `m` in run `k`:

0. The zero fact is served by the zero fact.
1. DEMAND FIRST: if a demand final `d` of method `m` from run `k-1` (the other direction) overlaps `a` (`overlap(d, a)`,
   marks ignored), emit `(a.base, a.path, *, {}, *)`: the chain of the added fact, the `*` tail, the mark `*`. The chain is
   the chain of an added fact that the demand overlaps; never emit a chain that no demand overlaps.
2. Else, if a CLOSED initial fact of an earlier run in the same direction is applicable to `a`, reuse its records
   (§10.7 R5): nothing is emitted.
3. Else, emit the most abstract fact `(a.base, [], *, {}, *)`.

Steps 0, 1 and 3 satisfy (A1) (Lean: `policy`, `policy_applicable`). Step 2 emits nothing; instead the records of the
closed initial fact are applied, and they cover every flow from `a` (`Closed.closed_records_exact`). The caller gets the marks back through the summary application: a `*`-mark premise passes the mark of the
caller fact through. A sink or a mark-specific rule inside the callee gets the mark through a request (§8).

### 7.3 The start fact

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
2. its premise is the zero fact or an EXACT request answer `(x, p, $, T)`;
3. the premise is SUPPORTED: it is the zero fact of an entry method, or a normal-layer caller edge of a supported premise
   produced, through a normal binding, the zero fact (for the zero premise) or the exact added fact `a` that answered
   the request, and the answer IS that added fact (`answer = a`: same base, same path). The weaker condition "the answer
   is exact" is not enough: a request on one parameter can then be supported by a real fact on another parameter
   (`Confirmed.weak_support_gap`, a proved counter-example).

Every other triggered vulnerability is a DEMAND vulnerability. Condition 3 is necessary: a demand edge in the caller can
feed an added fact whose exact answer starts in the normal layer, so a complete sink edge alone admits a false positive
(review counter-example). `Confirmed.confirmed_real` proves that a confirmed vulnerability is a real concrete
vulnerability: there is no false positive inside this scope.

### 8.2 Mark-specific micro edges

A micro edge with a concrete premise mark `T` (a conditional source, a mark-specific pass rule) on a fact with the mark
`*` gives no fact. It raises the request `(m, i, T)` (the mark gate, §4.1 step 4). If it dropped the fact without a
request, the flow would be lost; if it applied the rule anyway, every mark would pass the rule.

### 8.3 Request answer and propagation

A request `(m, i, T)` STANDS for the whole run. On every added fact `a` of `m` that overlaps `i`, also an added fact that
arrives later:

* If `a.mark = T`: ANSWER (bidirectional-task.md §4). If `a` is exact at `i.path`, emit `(i.base, i.path, $, {}, T)`.
  Otherwise emit `(i.base, i.path, i.tail, {}, T)`; it starts as `(i.base, i.path, [any], {}, T)` in the demand layer
  (§7.3). The chain is never deeper than the request.
* If `a.mark = *`: PROPAGATE to every caller edge `(ic → c)` that produced `a`: raise the request `(caller, ic, T)`.

One answer does not stop the request: the answer for one added fact does not serve another added fact. The answered
initial facts are initial facts like every other: callers read their summaries through §6.2 step 4. Lean: `answerInit`,
rules `answer`, `reqUp`; `answerInit_covers`, `answerInit_applicable`.

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
* A call is reversed too: the binding into the callee becomes `r.* → return.*`, `ai.* → argi.*`; the binding back
  becomes `argi.* → ai.*` (`Reverse.Call.rev`).
* The rules swap:

| Forward rule | Backward role |
|---|---|
| unconditional source of `T` at `(v, ρ)` | sink pattern `(v, ρ, $, T)` |
| conditional source (needs `T'`, gives `T`) | micro edge `(v, ρ, $, T) → (u, π, $, T')` |
| sink of `T` at `(v, ρ)` | source: `zero → (v, ρ, $ or [any], T)` (the seed) |
| mark-specific pass rule `T` from `x` to `y` | the reversed micro edge `y → x` with the premise mark `T` |
| unconditional cleaner of `T` | removes the requirement `T` there |

* The demand match across directions compares LOCATIONS only, not marks.

The backward run is the closure `D` on the reversed program. `Reverse.flow_rev_iff_calls` proves that its flow is the
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
| `SideEffectRequirement`, `refineInitial` | Removed. A premise never changes; a lost correlation gives a demand edge. |
| the refinement set of a rule reader (`FactReader`) | The mark request (§8.1, §8.2). |
| `TaintMarkFieldUnfoldRequest`, `[any]` unroll requests | The demand of the previous run and the mark request. |
| call type info through refinement (`CallTypeInfoUtil`) | Type information from the phase-3 prescan; type filters (S5). |
| `FactSideEffect` summaries | The callee summary edges (§6.3). |
| fact-depth gate, `[any]` depth charge | The field limit (§5). |
| union merge of exclusions | Merge rules 1 and 2 (§3.3). |

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

/** The initial fact (premise): one linear path. Emitted initial facts have no exclusion. */
class InitialAp(
    val base: AccessPathBase,
    val path: PathNode?,       // interned, linked from the root; no [any], $ or mark accessors (W4, W5)
    val tail: ApTail,
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
  `p`. The denotation does not change. The abstraction enumerates the call-site facts, so the fold can only make the
  selected initial facts less specific; (A1) still holds. A normal tree is never folded: a rule-assigned `[any]` leaf
  there must not absorb complete leaves (they are persisted, and they can confirm a vulnerability).
* T6. Share one empty payload; intern payloads, mark sets and exclusion sets.

### 9.3 `applyEdge` on a tree

The operation of §4.1 on all paths of one tree at once. The results are grouped by their new (layer, exclusion):

1. Walk `from.path` from the root. On each proper prefix node, read its payload as the case `above`: `*` and `[any]`
   leaves give `[any]` (or `$` for a `$` target) at `to.path`, in the demand layer unless §4.1 says otherwise.
2. At the node of `from.path` take the subtree `S`. Filter its root by the premise tail and the edge exclusion.
3. Transform `S` by the target tail. For `*/Et`: the child subtrees (`r ≠ []`) keep the tree exclusion and are re-rooted
   under `to.path`; the root `*` leaf (`r = []`) gets the exclusion `E ∪ Ef ∪ Et`, so it goes to another tree. `[any]`
   and `$` targets fold `S` into one uncorrelated payload with the Empty exclusion, except the root `*` leaf under a `$`
   premise and a `$` target: it becomes the correlated `*/Universe` leaf (§4.1), in a tree with the Universe exclusion.
4. Apply the mark gate per payload mark, then the target mark.
5. Apply the field limit with `boundedDepth`; cut paths go to the demand tree.
6. Route each result by its own layer bit (§4.1 steps 3, 5, 6 and the cut).

Cost: the walk visits `|from.path| + 1` nodes; the transformation visits `S` only. The concept form visits every path
fact (`Tree.lean`).

### 9.4 Interning

Tries are hash-consed bottom-up as today; an identity cache memoises the walk of §9.3. `boundedDepth` is part of the
node, not of the hash.

### 9.5 Relation to the current code

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
| `TreeInitialFactAbstraction` | Replace by the policy of §7.2. |
| `MethodAnalyzer` depth gate, `[any]` depth charge | Not used (§5). |

---

## 10. Storages

Every store has a CONCEPT (a list of records with a filter) and an INDEX. `Store.lean` proves that each index returns
every record that the filter returns, and gives the cost of the lookup. Lifetime: RUN = one run (one direction, one
limit); PERSISTENT = all runs of one analysis.

### 10.1 Method edge store (RUN, per method)

* Key: `(statement, premise, layer, base, exclusion)`. Value: an `EdgeTree`.
* `add(...)` merges by rule 1 or 2 and returns the delta (T4), or null if the fact adds nothing.
* Subsumption inside one layer and one class: a conclusion is dropped if a stored conclusion of the same premise and
  layer subsumes it, and the stored one is complete whenever the dropped one is complete
  (`Subsume.subsumesB`): the same base and mark; `[any]` at `p` subsumes every fact at or below `p`; `*/Es` subsumes
  `*/En` at the same path if `Es ⊆ En`; `$` subsumes `$` and `*/Universe` at the same path. `subsumes_sound` proves that
  every pair of the dropped fact is a pair of the stored fact. Do not use the premise test `coversB` for conclusions.
* A non-complete conclusion (a demand conclusion, or a rule-assigned `[any]` in the normal layer) never subsumes a
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
* The standing request match (§8.3) and the subscription (§6.2 step 4) read it with OVERLAP and APPLICABLE queries:
  `lookupPrefixes ++ lookupExtensions` of the query path.

### 10.4 Subscription store (RUN)

* Key: the callee. Value: the caller records `(caller edge, call statement, added fact a)`.
* On a new summary edge of an initial fact `j`: find the subscribed `a` with `applicable(j, a)` and apply.
* On a new subscription: apply every existing summary edge of every initial fact applicable to `a`.

### 10.5 Run summary store (RUN, per method)

* Key: `(premise, layer, exit kind)`. Value: the exit `EdgeTree`s.
* Complete summary edges go to the persistent record store at the end of the run (§10.7).
* Demand summary edges become the DEMAND of the next run (§10.6). They are not persisted and never reversed.

### 10.6 Demand store (from the previous run, read only)

* Key: method, then `base :: path`. Value: the demand finals of the previous run (the conclusions of its demand summary
  edges), in the direction of that run. A forward demand final is at the method exit, a backward one at the method
  entry: the demand of backward-k guides the entry abstraction of forward-(k+1), and the demand of forward-k guides the
  exit abstraction of backward-(k+1).
* Query: `matches(m, a) = ∃ d. overlap(d, a)`, marks ignored. The index answers it with
  `lookupPrefixes ++ lookupExtensions` (`demand_complete`, `demand_completeB`).

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
    /** Records whose ENTRY fact is applicable to the caller fact (forward reading). */
    fun byEntry(method: MethodKey, callerFact: InitialAp): Sequence<CompleteRecord>
    /** Records whose EXIT fact is applicable to the requirement (backward reading, reversed). */
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
  for this query (`extension_half_redundant`).
* R3. A reader in the other direction applies the reversal of §10.8. Every complete record whose premise has the Empty
  exclusion and that is mark-reversible reverses exactly (`Reverse.rev_exact_of_empty_premise`).
* R4. Adding complete records to a later run is always sound: a complete edge is exact (§11.3), so it adds no false pair
  (§6.2 step 1).
* R5. Reusing records INSTEAD of an analysis (§7.2 step 2) needs the CLOSED marker: in its run the initial fact reached
  the fixed point, raised no request, had only complete edges, and every initial fact that serves a call inside it is
  closed (the greatest fixed point over recursion, computed with `uses`, §10.2). Then its records are exactly the
  concrete flow from its location set to the exit (`Closed.closed_records_exact`). The replay restores its confirmed
  vulnerabilities.
* R6. A closed marker is valid for every later run with a limit at least the limit of the run that set it (argued: a
  complete derivation never used the cut).
* R7. Demand first: the abstraction checks the demand before the reuse (§7.2). A complete record never replaces the
  analysis of an added fact that a demand final overlaps.

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
(`rev_exact_of_empty_premise`).

### 10.9 Request store (RUN, per method)

* Records: `(method, initial fact, mark)` plus the answers already emitted (for deduplication). There is no "answered"
  state: a request stands for the whole run (§8.3).
* Index: a path trie keyed by `method :: base :: path` of the request initial fact. On every new added fact, find ALL
  requests that overlap it (`standing_complete`); answer or propagate each one.

### 10.10 Vulnerability store (PERSISTENT)

* Key: `(rule, statement)` as today. The value keeps today's fields (trigger position, initial-fact groups,
  `EndFactRequirement`, rule assumptions) and adds the state (confirmed or demand) and the run.
* A CONFIRMED vulnerability (§8.1) persists. A run that reuses a closed initial fact replays the vulnerabilities found
  inside it, and their confirmation is evaluated again with the support of the new run.
* Every forward run is sound: it reports every concrete source-to-sink flow, for every demand and every field limit
  (`Coverage.vuln_found_policy`, `vuln_sound_two_runs`). So stopping at any run is sound. The intersection of the
  reports of several runs is sound as well (each report contains every real vulnerability); there is no theorem that a
  later run has fewer false positives.

---

## 11. Theorems

All theorems are in `spec/lean/ApSpec`. "Constructive" means: only `propext` and `Quot.sound`, checked with
`#print axioms` after every main theorem. No `sorry`, no `Classical.choice`, no `native_decide`.

### 11.1 Soundness — `Coverage.lean`

Hypotheses: the program is well-formed (`Program.WF`: every micro edge reads from a touched base; call bindings are
mark-agnostic) and `α` satisfies (A1).

| Theorem | Statement |
|---|---|
| `coverage` | If the value at the entry location `l0` of method `M` flows to `l` at node `n` (`Flow`: statements, calls, call-to-return, nested callee flows), and the initial fact `i` of `M` covers `l0`, then the analysis has an edge `(i → f)` at `n` with `den(i, f)(l0, l)`, OR the request `(M, i, l0.mark)`. |
| `coverage_conc` | If `i` has a concrete mark, the first case holds. |
| `reach_strong`, `vuln_found` | If the zero location of an entry method flows through any chain of calls to a location that a sink pattern covers (`Reach`), the analysis reports the vulnerability at that sink. |
| `coverage_policy`, `vuln_found_policy` | The same for `α = policy demand`, for EVERY demand: every forward run is sound. |
| `vuln_sound_each_run`, `vuln_sound_all_runs`, `vuln_sound_two_runs` | Runs with different demands (and, for `vuln_sound_two_runs`, different field limits) all report a concrete vulnerability: stopping at any run is sound. |
| `edge_conc`, `req_initial_star` | A concrete-mark initial fact has only concrete-mark conclusions; a request is always on a `*`-mark initial fact. |

That is the property "if the fact exists and the data flow exists (intra and inter procedural), the fact reaches the
destination".

### 11.2 Local lemmas — `Core.lean`

| Lemma | Statement |
|---|---|
| `applyEdge_sound` | THE CORE LEMMA: `applyEdge` covers the composition of the fact relation and the edge relation, or raises the request for the premise mark. |
| `transfer_sound` | The statement transfer covers the statement step. |
| `applySummary_sound` | Summary application covers the composition with the callee flow. |
| `limitF_sound`, `CoreAux.norm_sound` | The field limit and the normal form only enlarge. |
| `startFact_sound` | The start fact covers the identity. |
| `coversB_sound`, `applicable_sound`, `applicable_mark` | The syntactic cover test is sound; an applicable mark-specific premise forces the same mark. |
| `overlapB_of_common` | Two facts with a common location overlap. |
| `check_sound`, `check_request_star` | A covered tainted location triggers the sink or raises the request. |
| `answerInit_covers`, `answerInit_applicable` | The answer covers the requested location and is applicable to the added fact. |
| `policy_applicable` | The policy of §7.2 satisfies (A1). |

### 11.3 Exactness and invariants — `Exact.lean`, `Invariant.lean`, `Closed.lean`

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

### 11.4 Concept against optimization — `Tree.lean`, `Store.lean`, `Subsume.lean`

| Theorem | Statement |
|---|---|
| `Tree.insert_mem`, `Tree.fromList_mem` | The `EdgeTree` (one premise, layer and exclusion; `*` leaves are flags) holds exactly its path edges. |
| `Tree.rule1_mem`, `Tree.rule1_den` | Merge rule 1 is exact (as membership). |
| `Tree.rule2_den` | Merge rule 2 is exact (on pairs) for EQUAL trees. Two `decide` counter-examples: a union of exclusions across different trees loses a pair; an intersection across different trees adds a pair. |
| `Tree.applyTreeE_mem`, `applyTreeE_den` | The tree form of `applyEdge` (for `*`-to-`*` micro edges with the mark `*`) equals the per-path `applyEdge` on whole conclusions, fact and layer. |
| `Tree.applyTreeE_grouped`, `applyTreeE_inv`, `applyTreeE_star_normal` | The output trees have distinct keys `(exclusion, layer)`; every output tree is well-formed; no demand tree has a `*` leaf. |
| `Tree.fromList_size`, `fan_list`, `fan_tree`, `prepend_shares`, `prepend_list_cost`, `walkSteps_le`, `applyListC_spec` | Cost: size `1 + Σ|path|`; `k·(p+1)` path entries against `p + k + 1` nodes; prepend adds `O(1)` nodes; the walk visits `|from.path| + 1` levels against `|fs|` calls in the list form. |
| `Store.*` | Each index returns every record that the concept filter returns: `forward_equiv_prefixes` (`byEntry`, prefix half), `backward_equiv`, `backward_equiv_prefixes` (`byExit`), `demand_complete`, `standing_complete`; keys `base :: path` (`candidatesB_base`); the split by `complete` loses nothing (`split_perm`, `next_loses_only_demand`); lookup cost `|q| + 1` key-path nodes against `|records|` tests (`prefix_query_cost`). |
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
* The theorems are about the closure `D`. A real run differs from `D` by optimizations. Each one keeps the soundness:

| Optimization | Why it keeps the soundness | Status |
|---|---|---|
| conclusion subsumption (§10.1) | the dropped pairs are pairs of the kept fact (`subsumes_sound`); coverage needs one covering fact | the local step is proved; the composition with `D` is argued |
| merge rules 1 and 2 (§3.3, T1, T2) | exact (`rule1_mem`, `rule2_den`, `merge_inter`); the rule-2 delta re-propagates (T4) | proved |
| the T5 fold | the denotation does not change | argued |
| persisted complete records (§6.2 step 1, R4) | a complete edge has no false pair (`complete_exact`); adding edges keeps coverage | proved |
| closed record reuse (§7.2 step 2, R5) | the records cover every flow from the premise (`closed_records_exact`) | the local step is proved; the composition with `D` is argued |

* The forward/backward iteration invariant (run k+1 leaves a complete record or a demand for every real flow on a
  vulnerability path of run k) is a PROGRESS property: it explains why the iteration adds precision. Soundness does not
  need it. It is argued, not machine-checked.
* R6 and the greatest-fixed-point rule of R5 are argued in text only.
* The tree theorems cover the `*`-to-`*` micro edges with the mark `*`; other micro edges (rules) use the per-path
  operation on the touched subtree. The field limit inside the tree and the T5 fold are not modelled in `Tree.lean`.
* Cleaners, type filters, conditions with several literals and non-distributive edges are outside the model.

---

## 12. The formal model

| File | Content |
|---|---|
| `Basic.lean` | All definitions: locations, facts, `den`, `applyEdge`, the normal form, the field limit, statements, calls, `Flow`, the closure `D`, `Reach`, `answerInit`, `policy`, `revEdge`. |
| `Cases.lean` | The cases of bidirectional-task.md and every decision of the review as test vectors, checked by `decide`. |
| `Core.lean` | The local lemmas (§11.2). |
| `Coverage.lean` | Soundness (§11.1). |
| `Exact.lean`, `Invariant.lean`, `Closed.lean`, `Confirmed.lean` | Exactness, invariants, closed reuse, confirmed vulnerabilities (§11.3). |
| `Tree.lean`, `Store.lean`, `Subsume.lean` | Concept against optimization (§11.4). |
| `Reverse.lean` | Reversal (§11.5). |

Build and audit:

```
cd spec/lean && lake build 2>&1 | grep "depends on axioms" | sed 's/.*axioms: //' | sort | uniq -c
```

The audit passes when the only sets are `[propext]` and `[propext, Quot.sound]`. At the time of writing: 187 audited
declarations (59 `[propext]`, 108 `[propext, Quot.sound]`, 20 with no axioms) and 61 test vectors in `Cases.lean`, all
checked by `decide`.

---

## 13. Test plan (TDD)

Write the tests first. Each test names the spec item that it checks.

1. Vector tests (`ApplyEdgeVectorsTest`): one test per `example` in `Cases.lean`, on the concept implementation (§4.1
   reference form) and on the tree implementation.
2. Equivalence property test (`EdgeTreeEquivalenceTest`): random path facts and micro edges; the tree result denotes the
   same pairs as the concept result, layer included. Check pairs by bounded enumeration of `σ, τ` up to length 3.
3. Layer tests: the conditional-source example of §4.4; a cut fact is demand; a demand input gives a demand output; a
   `*` conclusion is never in the demand layer.
4. Builder tests (`StatementSummaryBuilderTest`): no exclusion update on a read; the self-write; the identity edges of
   source and pass rules; the static write gives the expected demand.
5. Merge tests: rule 1, rule 2, and a test that a union of exclusions is never made.
6. Request tests: the mark gate raises a request; a standing request is answered by a later added fact and by a second
   added fact; propagation to a caller with a `*`-mark call-site fact; the answer chain is the request chain.
7. Call tests: the four steps of §6.2; a caller reads the summaries of an answered initial fact.
8. Abstraction tests: demand first; the emitted fact has the chain of the added fact, `*`, `{}` and `*`; (A1) for every
   selected initial fact; the same result for two insertion orders.
9. Store tests: index completeness against a list filter; split by layer; the closed marker only for all-complete
   initial facts without requests.
10. Reversal tests: every row of §10.8; the forward record and its reversed reading give converse results on the same
    concrete pair.
11. Analysis tests (phase 2 gate): the existing `*AnalysisTest` suites, run with `cleanTest`. A lost finding is a test
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
| F7 | Reversed records instead of an analysis | Replaced by "demand first" (R7) and the iteration invariant (§11.6). |
| F8 | Reversal shapes | Assertion: exact for every mark-reversible record with the Empty premise exclusion (§10.8). |
| F9 | Normal form | Adopted (§4.1 step 6). |
| F10 | Exclusion of a reversed record | Adopted: on the new conclusion (§10.8). |
| F11 | Request store index | Adopted: path index, overlap query (§10.9). |
| F12 | Index keys | Adopted: `base :: path`; the forward lookup uses the prefix half (§10.7 R2). |
| F13 | `applicable` | Adopted: necessary for soundness (§6.3). |
| F14 | Answer by the meet | Withdrawn: the answer keeps the request chain (§8.3). |
| F15 | Mark of the emitted fact | Already in the task rule: `(x, chain, *, {}, *)` (§7.2). |
| F16 | `lostCorr` | Adopted: an uncorrelated result without a lost restriction stays in the normal layer (§4.1). |
| F17 | Standing requests | Adopted (§8.3). |
| F18 | Conclusion subsumption | Adopted: `subsumesB`, not `coversB` (§10.1). |
| F19 | Closed marker | Adopted: no request (R5). |
| F20 | Identity edges of rules | Adopted: source and pass rules keep their premise base; the self-write has none (§4.2). |
| F21 | Zero fact | Adopted: served by the zero fact (§7.2). |
| D1 | Exclusion | Per path edge, shared by premise and conclusion; merge rules 1 and 2; no union merge (§3.3, §9.2). |
| D2 | Call processing | The four steps (§6.2). |
| D3 | Runs | Every forward run is sound, so stopping at any run is sound; confirmed vulnerabilities persist (§10.10). |
| F22 | Confirmation | A complete sink edge is not enough; a confirmed vulnerability needs a normal-layer support chain (§8.1; review counter-example; `confirmed_real`). |
| F23 | Approximating rules | Cleaners that keep `*`-mark facts and over-approximated conditions put the result in the demand layer (§4.4). |
| F24 | Rule-2 delta | Merge rule 2 propagates the whole merged tree (T4). |
| F25 | Fold | The T5 fold only inside demand trees (§9.2). |
| D4 | Record subsumption | `(a, p) → (b, q)` subsumes `(a, p·r) → (b, q·r)` inside the complete layer (§11.4). |
