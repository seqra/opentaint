# IR interpreter — specification

Status: design spec, the companion of [ap.md](ap.md) (version 5). `ap.md` defines the access path
(AP), its operations and its primitives. This document defines how the analyzer interprets the IR of the JVM (JIR) and
of Go (GoIR) with these primitives. The design history is in [ap-history.md](ap-history.md).

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope and relation to ap.md

This document defines:

1. the micro edges of the non-call statements (§2);
2. the micro edges of the call statements: the bindings, the result, the aliases (§3);
3. the order in which the interpreter applies the rules (§4);
4. the points where the interpreter applies the type filter, the cleaner, the ND conjunction and the request (§5).

It does not define the AP operations. It uses them by name:

| ap.md primitive | Function | Used in |
|---|---|---|
| apply a micro edge (`applyEdge`) | one micro edge on one fact; unguarded | §2, §3 (bindings) |
| apply a summary edge | guarded by satisfaction | §3.1 |
| request a mark | run 1 only | §5.4 |
| ND conjunction | an edge keyed by a set of premises | §5.3 |
| `clean(cleaner)` | removes marks at a position | §5.2 |
| `filter(base, may)` | removes the facts of `base` whose path `may` rejects | §5.1 |
| emission, storages | abstraction and stores | not used directly |

Common rules:

| # | Rule |
|---|---|
| I1 | The interpreter gives each statement a STATEMENT SUMMARY: the touched bases, the micro edges, and the type filters of each touched base. The AP applies it (ap.md §4.2, the statement transfer). |
| I2 | Micro edge application is UNGUARDED. The AP applies every micro edge to every fact on its base, in both cases of ap.md §4.1: at or below the premise, and above it. A fact above the premise of a micro edge gives an uncorrelated result in the demand layer. There is no refinement. |
| I3 | A read never changes an exclusion. Only a STRONG WRITE adds the written accessor to the exclusion of the identity edge of the written base: `a.* →_{f} a.*`. |
| I4 | A call binding is a micro edge (I2 applies). A callee summary edge is not a micro edge: it applies only if the caller fact satisfies its premise (ap.md §4.3). |
| I5 | The interpreter is the same in every run. The differences: requests exist only in forward run 1 (§5.4); the static base at calls in restricted runs (§3.3); the backward run reverses the micro edges and applies no type filter (§4.9). |
| I6 | MARK WELL-FORMEDNESS (ap.md S7): no micro edge or binding has a premise mark `*∖X`, and a micro edge with a concrete target mark has a concrete premise mark (a source: `zeroMark`; a conditional source: `T`). Without it a normal-layer edge can claim a cleaned mark. |
| I7 | NO UNIVERSE (ap.md S8): a micro edge with a `$` premise has a concrete premise mark, and no micro edge, binding or initial fact has the kind `*/Universe`. Every exclusion that the interpreter makes is a finite set of accessors. No micro edge has a `$` premise and a `*` target. |
| I8 | NO `*`-PREMISE CALLEE SUMMARY in a restricted run (ap.md §6.3): an empty method is analysed from its emitted concrete premise; an unresolved callee is a statement summary (§3.7). |
| I9 | PRECISE AND COMPLETE MICRO EDGES (ap.md S1, S2, §4.2): every micro edge (a statement edge with its alias edges, or a call binding edge; not a callee summary edge) gives exactly the flows of its statement. A micro edge has NO LAYER: the layer belongs to the propagation edge, and only the AP operations change it (ap.md §2.2). |
| I10 | NO FIELD LIMIT ON A MICRO EDGE: a micro edge keeps its full paths (also an alias path `c.q.p` of any length). The field limit applies to the results of an application (§2.1 step 6, §4.5 step 6). |

### 0.1 Known gaps against ap.md S1, S2 and S5

ap.md S1 asks that the micro edges of a statement give exactly its real flows (S2 the same for the aliases, S5 for the
type filters). The interpreter does not do this at the points below (as today). The soundness theorems of ap.md do not
cover a flow that a soundness gap loses. A precision gap keeps a flow that does not exist in the normal layer, so the
exactness theorems hold only relative to it. ap.md §11.1 lists the expected false-positive sources (G7, G8, and the
type filter on a `*` fact).

| # | Gap | Where | Effect |
|---|---|---|---|
| G1 | No exception flow crosses a call, and a catch block does not read `exc`. Out of scope for now (ap.md §11.2). | §3.4 | a thrown tainted value is lost |
| G2 | The `S` facts that an exit sink read are dropped, and the entry marks on zero-premise `this`/`arg` facts are removed. | §4.7 steps 3, 4 | premise-dependent removals, not an AP primitive |
| G3 | The cleaners run before the callee body. | §4.5 step 5.1 | a sink inside the body of the cleaner method sees the cleaned fact |
| G4 | The rules come from the method that the call names, not from the resolved override. | §3.6 | a sink or source on an override is missed |
| G5 | The static base is not touched at a call in a restricted run when the callee touches no static (D15). | §3.3 | sound only over the final call graph, also the lambdas and closures that §3.9 resolves later |
| G6 | The mark policy and the policy cases of the type filter. | §5.1 | they can drop a real flow (outside ap.md S5) |
| G7 | The write at an alias is weak (A3, C2). | §2.5, §3.8 | precision: the old content of the alias path survives (sound if an alias does not hold); an expected false-positive source (ap.md §11.1) |
| G8 | A constructor call keeps the caller facts that it overwrites. | §3.5 | precision: a weak update of the receiver and the arguments; an expected false-positive source (ap.md §11.1) |

Notation:

| Form | Meaning |
|---|---|
| `x.p.*` | base `x`, path `p`, tail `*`, mark `*` (a micro-edge side or a fact) |
| `x.p.$ (T)`, `x.p.[any] (T)` | the tail `$` or `[any]` with the concrete mark `T` |
| `a →_{f} b` | a micro edge with the exclusion `{f}`; no subscript: the Empty exclusion |
| `[e]`, `<C>`, `#i` | the element accessor, the class accessor of `C`, the tuple slot `i` (Go; written `#i` so that it is not the `$` tail) |
| `{x, y}` | the touched bases of a statement |
| bound fact | a caller fact after the binding edge into the callee (callee coordinates); after the cleaners of the call it is the ADDED FACT of the callee (ap.md §1) |

---

## 1. Bases and positions

### 1.1 Bases

| Base | JVM | Go |
|---|---|---|
| `this` | `JIRThis` | the receiver (parameter 0 of a method); at a dynamic call, the function value |
| `arg(i)` | `JIRArgument(i)` | parameter `i`, counted after the receiver |
| `local(i)` | `JIRLocalVar(i)` | register `i` |
| `const(t, v)` | `JIRConstant` (also `null`) | `GoIRConstValue` |
| `ret` | the return value | the return value; several results: `ret.#i` |
| `exc` | the thrown exception | none |
| `S` | `ClassStatic` | `ClassStatic` (the globals) |
| `zero` | the zero fact | the zero fact |

### 1.2 Accessors

| Accessor | JVM | Go | Counted (field limit) |
|---|---|---|---|
| field `f` | `FieldAccessor(declaring class, name, type)` | `FieldAccessor(struct full name, name, "?")` | yes |
| `[e]` | array element | slice, array, map and channel element | yes |
| `<C>` | `ClassStaticAccessor(C)` | `ClassStaticAccessor(global full name)`, written `<G>` | no |
| `#i` | none | `FieldAccessor("tuple", "$i")` | yes |
| `fv_i` | none | `FieldAccessor(fn, "freeVar$i")`: free variable `i` of closure `fn` | yes |
| `<string-bytes>` | the content of a `String` (a virtual field) | none | yes |
| type info | prescan only | prescan only | no |

### 1.3 Rule positions

A rule names positions in CALLEE coordinates. At a method entry and at a method exit, the positions are in the
coordinates of the method itself.

| Position | Base and path | Note |
|---|---|---|
| `Argument(i)` | `arg(i)` | |
| `This` | `this` | Go: also the target of a dynamic call |
| `Result` | `ret` | at a call: the lhs after the binding back |
| `ClassStatic` (JVM) | `S.<C>` | |
| `PositionWithAccess(P, Field f)` | the path of `P` and `f` | |
| `PositionWithAccess(P, Element)` | the path of `P` and `[e]` | |
| `PositionWithAccess(P, AnyField)` | the path of `P` | sink and condition: the `[any]` pattern; source: the `[any]` tail; cleaner: the reach (§5.2) |

---

## 2. Non-call statements

### 2.1 The statement step

A call statement never uses this step. `x = m(...)` is a call (§3). For a fact `c` on the base `b` at the statement `s`:

1. Liveness (JVM). If `b` is a local that is dead at `s`, drop `c` (`JIRLocalVariableReachability`). Go has no
   liveness step (as today).
2. If `s` does not touch `b`: `c` passes unchanged (`Unchanged`).
3. Apply the operand type filters of `b` (§5.1). A rejected fact is dropped, also on `b` itself.
4. Apply every micro edge of `b` to `c` (I2). The result is the union. A touched base keeps only what an edge
   regenerates: that is the kill.
5. Apply the lhs type filter (§5.1) to the results on the lhs. (On the input it has no effect: the statement kills the
   lhs.)
6. Apply the field limit (ap.md §4.4).

The write rule (I3):

```kotlin
/** A STRONG write of the path a1..an on the base b: keep every prefix of b except the written accessor. */
fun strongKeep(b: Base, path: List<Accessor>): List<MicroEdge> =
    path.indices.map { k -> MicroEdge(star(b, path.take(k)), star(b, path.take(k)), exclusion = setOf(path[k])) }

/** A WEAK write keeps the whole base. A read keeps the whole base and adds no exclusion. */
fun weakKeep(b: Base) = listOf(MicroEdge(star(b), star(b), exclusion = emptySet()))
```

A strong write with an empty path (Go `*p = v`) gives no identity edge: the base is replaced.

### 2.2 JVM

| Statement | Micro edges | Touched | Type filters (§5.1) |
|---|---|---|---|
| `x = y` | `y.* → y.*`, `y.* → x.*` | {x, y} | y: static type of y; x: static type of x |
| `x = (T) y` | as `x = y` | {x, y} | y: `T` (narrows y); x |
| `x = c` (a constant or `null`) | `c.* → c.*`, `c.* → x.*` | {x, c} | c; x |
| `x = y.f`, x ≠ y | `y.* → y.*`, `y.f.* → x.*` | {x, y} | y: static type of y AND declaring class of f; x |
| `x = x.f` | `x.f.* → x.*` | {x} | x: static type of x AND declaring class of f |
| `x = y[i]` | `y.* → y.*`, `y.[e].* → x.*` | {x, y} | y: the array type; x |
| `x = C.s` | `S.* → S.*`, `S.<C>.s.* → x.*`; in run 1 on an abstract static fact: the position request `[<C>, s]` (ap.md §4.10) | {S, x} | x |
| `y.f = x`, y ≠ x | `y.* →_{f} y.*`, `x.* → x.*`, `x.* → y.f.*` | {y, x} | y: static type of y AND declaring class of f; x |
| `y.f = y` | `y.* →_{f} y.*`, `y.* → y.f.*` | {y} | y |
| `y[i] = x` (weak) | `y.* → y.*`, `x.* → x.*`, `x.* → y.[e].*` | {y, x} | y: the array type; x |
| `C.s = x` | `S.* →_{<C>} S.*`, `S.<C>.* →_{s} S.<C>.*`, `x.* → x.*`, `x.* → S.<C>.s.*`; in run 1 the class keep edge on an abstract static fact raises the position request `[<C>]` (ap.md §4.10) | {S, x} | x |
| `x = a op b` | `a.* → a.*`, `a.* → x.*`, `b.* → b.*`, `b.* → x.*` | {x, a, b} | a; b; x |
| `x = new T`, `new T[n]`, `instanceof`, `-a`, `a.length`, phi | none (kill) | {x} | x |
| `return v` | `v.* → v.*`, `v.* → ret.*` | {ret, v} | none |
| `return` (void) | none (kill) | {ret} | none |
| `throw t` | `t.* → t.*`, `t.* → exc.*` | {exc, t} | none |
| any other statement (branch, goto, monitor, catch) | none | {} (all facts pass) | none |

If one base is on both sides (`x = x op b`), the two edges of `x` become the identity `x.* → x.*`. The alias edges of a
write are in §2.5.

### 2.3 Go

Go has no type filters (as today, `FactTypeChecker.Dummy`). The pointer model of today stays: `*y` and `&y.f` do not
add an accessor, so a pointer and its target are one base.

| Statement | Micro edges | Touched |
|---|---|---|
| `x = y` for ChangeType, Convert, MultiConvert, ChangeInterface, MakeInterface, TypeAssert, SliceToArrayPointer, `*y`, Slice, Range | `y.* → y.*`, `y.* → x.*` | {x, y} |
| `x = y.f`, `x = &y.f` | `y.* → y.*`, `y.f.* → x.*` | {x, y} |
| `x = y[i]`, `x = &y[i]`, `x = m[k]`, `x = <-ch` | `y.* → y.*`, `y.[e].* → x.*` | {x, y} |
| the comma-ok form of lookup, type assert and receive | as above; the target is `x.#0.*` | {x, y} |
| `x = extract(t, i)` | `t.* → t.*`, `t.#i.* → x.*` | {x, t} |
| `x = G` (a global) | `S.* → S.*`, `S.<G>.* → x.*` | {S, x} |
| `x = freevar(i)` in closure `fn` | `this.* → this.*`, `this.fv_i.* → x.*` | {x, this} |
| `x = a + b` (string) | `a.* → a.*`, `a.* → x.*`, `b.* → b.*`, `b.* → x.*` | {x, a, b} |
| `x = next(it)` | `it.* → it.*`, `it.[e].* → x.#k.*` for k ∈ {1, 2} (map) or k = 2 (slice, array); no target for other types | {x, it} |
| `x = phi(v1, ..., vn)` | for each `vi`: `vi.* → vi.*`, `vi.* → x.*` | {x, v1..vn} |
| `x = makeClosure(fn, b0..bn)` | for each `i`: `bi.* → bi.*`, `bi.* → x.fv_i.*` | {x, b0..bn} |
| other binary and unary (NOT, NEG, XOR) operations, Alloc, MakeSlice, MakeMap, MakeChan, Select, builtin, function value | none (kill) | {x} |
| `*p = v` | `v.* → v.*`, `v.* → p.*` (strong, empty path: no identity for p) | {p, v} |
| `y.f = v` | `y.* →_{f} y.*`, `v.* → v.*`, `v.* → y.f.*` | {y, v} |
| `y[i] = v` (weak) | `y.* → y.*`, `v.* → v.*`, `v.* → y.[e].*` | {y, v} |
| `m[k] = v` (weak) | `m.* → m.*`, `v.* → v.*`, `v.* → m.[e].*`, `k.* → k.*`, `k.* → m.[e].*` | {m, v, k} |
| `ch <- v` (weak) | `ch.* → ch.*`, `v.* → v.*`, `v.* → ch.[e].*` | {ch, v} |
| `G = v` | `S.* →_{<G>} S.*`, `v.* → v.*`, `v.* → S.<G>.*` | {S, v} |
| `return v` | `v.* → v.*`, `v.* → ret.*` | {ret, v} |
| `return v0, ..., vn` (n ≥ 1) | for each `i`: `vi.* → vi.*`, `vi.* → ret.#i.*` | {ret, v0..vn} |
| any other statement | none | {} |

### 2.4 Pinned examples

| Statement | Today (`StatementSummaryBuilder`) | New |
|---|---|---|
| `x = y.f` | `y\{f} → y`, `y.f → y.f`, `y.f → x` | `y.* → y.*`, `y.f.* → x.*` |
| `y.f = x` | `y\{f} → y`, `x → x`, `x → y.f` | `y.* →_{f} y.*`, `x.* → x.*`, `x.* → y.f.*` |
| `y[i] = x` | `y → y`, `x → x`, `x → y.[e]` | the same |
| `a.f = a` | `a\{f} → a`, `a → a.f` | `a.* →_{f} a.*`, `a.* → a.f.*` |
| `x = x.next` | `x\{next} → null` (refine only), `x.next → x` | `x.next.* → x.*` |
| Go `x, ok = m[k]` | `m\{e} → m`, `m.[e] → m.[e]`, `m.[e] → x.#0` | `m.* → m.*`, `m.[e].* → x.#0.*` |

The effect on facts (the cases of ap.md §4.2):

| Statement | Input fact | Today | New |
|---|---|---|---|
| `x = y.f` | `(y, ., *, E, *)`, f ∉ E | the premise is refined by `{f}`; the abstraction emits `y.f.*` | `(y, ., *, E, *)` normal; `(x, ., [any], {}, *)` demand |
| `x = y.f` | `(y, .f, *, E, *)` | `(x, ., *, E, *)` | the same |
| `y.f = x` | `(y, ., *, E, *)` | `(y, ., *, E ∪ {f}, *)` and a refinement | `(y, ., *, E ∪ {f}, *)`, normal, no request |

### 2.5 Aliases on writes

| Rule | Text |
|---|---|
| A1 | At a write to `b.p` with `b` a local, the alias analysis gives the alias paths `(c, q)` of `b` that hold BEFORE the statement (JVM: `DSUAliasAnalysis`, interprocedural depth 0; Go: `GoDSUAliasAnalysis`). Constant alias bases are skipped. |
| A2 | For each alias `(c, q)` with `c ≠ b` and each value `v` of the write: the micro edge `v.* → c.q.p.*`. |
| A3 | The alias base `c` is NOT touched (a gen-only target). It keeps its old content: the write is weak at the alias (gap G7; an expected false-positive source, ap.md §11.1). |
| A4 | A read uses no alias. A static write and a Go global write have no alias. |
| A5 | Backward run: the alias target gets the identity edge `c.* → c.*` (ap.md §9.2). |
| A6 | The alias edges are precise and complete (I9, ap.md S2). This is a contract on the alias analysis. The paths are not cut (I10). |

---

## 3. Call statements

### 3.1 Bindings

A call `r = m(o, a0, ..., an)`. The touched caller bases: `S` (§3.3), the receiver `o`, every argument `ai`, the lhs
`r`, and in Go the target of a dynamic call. A fact on another base passes over the call. A fact on a touched base
follows the call order of §4.5:

1. the binding edges into the callee (this section);
2. the sinks, the sources and the cleaners of the call (§4.5 steps 3 to 5.1);
3. the callee processing of ap.md §5.3 (add the fact, emit, subscribe, apply the summaries);
4. the summary rewriter (§5.2), the binding edges back, the aliases (§3.8) and the field limit.

| Binding | JVM edge | Go edge | Type filter (JVM, §5.1) |
|---|---|---|---|
| receiver in | `o.* → this.*` | `o.* → this.*` (the effective receiver) | o: declaring class of the method that the call names |
| dynamic target in | none | `v.* → this.*` (`v` = the function value) | none |
| argument in | `ai.* → arg(i).*` | `ai.* → arg(i).*` | ai: static type of `ai` |
| static in | `S.* → S.*` | `S.* → S.*` | none |
| zero in | `zero.* → zero.*` | `zero.* → zero.*` | none |
| receiver back | `this.* → o.*` | `this.* → o.*` and `this.* → v.*` | o: static type of `o` |
| argument back | `arg(i).* → ai.*`; none if `ai` is a constant | `arg(i).* → ai.*` | ai: static type of `ai` |
| result back | `ret.* → r.*`; none without an lhs | `ret.* → r.*` (several results: `r` is the tuple; `extract` reads `#i`) | r: static type of `r` |
| static and constant back | `S.* → S.*`, `const.* → const.*` | the same | none |
| exception back | none (dropped) | none | none |
| local back | none: a `local` fact is not a valid exit fact | none | none |

Every binding edge has the empty `from` path, so a caller fact is always strong enough for it. The AP applies it as a
micro edge (I4). A local passed twice (`m(a, a)`) gets two bindings.

### 3.2 The lhs

The lhs `r` has no binding into the callee. So a fact on `r` before the call is killed (a strong update of `r`). If `r`
is also an argument (`r = m(r)`), its argument binding carries the fact. The lhs gets only what the binding back of
`ret` gives, and the source rules at the call (§4.5).

### 3.3 Statics and the zero fact

* `S.* → S.*` in both directions, with no filter. In run 1 `S` is touched at every call: the static fact comes back
  only through the callee summaries (the identity summary of a callee that does not touch statics). In a restricted
  run `S` is NOT touched when the callee, transitively, touches no static; the static fact then passes over the call.
  This is the deviation D15: in the model call of ap.md §5.1, `S` is always touched. It needs the final call graph: a
  callee that is resolved later (§3.9) can touch a static (G5).
* The zero fact passes over every call (no call touches the zero base), AND it is bound into every resolved callee
  (`zero.* → zero.*`; the zero fact `(zero, [], $, zeroMark)` is below its premise), as today. The `$` form
  `zero.$ → zero.$` is not well formed: a binding into the callee is a `*`-to-`*` edge. There is no binding back for
  the zero fact: the fact that passed over is the same (ap.md §5.1). An unresolved call only passes the zero fact over.

### 3.4 Exceptions

`throw t` moves `t` into `exc` (§2.2). The exceptional exit makes no summary edge (`producesExceptionalControlFlow`).
The binding back has no edge for `exc`. So no exception flow crosses a call, and a catch block does not read `exc`. This
is today's behaviour (the exception tests of `DataFlowBenchFalseNegativeTest` are disabled). It is outside the model
(ap.md S4, §11.2; gap G1). Go has no exception base.

### 3.5 Constructors (JVM)

At a call to `<init>`, every bound caller fact (after the cleaners) also PASSES OVER the call: it keeps its caller base,
and it also enters the callee. This is the ad-hoc rule of today (`isConstructor` in `JIRMethodCallFlowFunction`). A
constructor call is thus a weak update of its receiver and its arguments. It is an expected false-positive source (gap
G8, ap.md §11.1).

### 3.6 Virtual calls and several callees

* JVM: the call resolver gives a set of callees, each with a context (`JIRInstanceTypeMethodContext`: the receiver type;
  `JIRArgumentTypeMethodContext`: the type of one argument), and possibly a resolution failure. Go: the resolved
  callees with `EmptyMethodContext`; an empty set is a failure.
* The relevance check, the sinks, the sources and the cleaners run ONCE per caller fact. They use the rules of the
  method that the call statement names, not of the resolved callee.
* The cleaned bound fact enters EVERY resolved callee. The start fact of each callee is filtered by the context type
  (§5.1).
* The caller gets the union of the summary results of all callees. A failure adds the unresolved path (§3.7) to the
  union.

### 3.7 Unresolved callees

An unresolved callee (no body, a resolution failure, or a lambda or closure that is not yet known) has a STATEMENT
summary (ap.md §4.2: the micro edges of a statement). The AP applies it to each cleaned bound fact `a` at the callee
base `P`, in every run, and never restricts it:

1. Default identity: `P.* → P.*`. The fact passes over the call. The summary rewriter (§5.2) applies to it.
2. Pass rules of the method that the call names (§4.1). JVM: with conditions; Go: unconditional. JVM type filters by
   the declared signature (§5.1).
3. JVM option `defaultGetModel`: the default getter rules join the pass rules (union).
4. The summary rewriter on the pass results, the binding back, the aliases (§3.8).

The lhs gets only what a pass rule writes to `Result`. The external method tracker records the call (no effect on the
facts).

### 3.8 Aliases on call results

| Rule | Text |
|---|---|
| C1 | JVM: for each caller local `x` that a binding back writes (`r`, `o`, `ai`), the alias paths `(b, q)` of `x` that hold BOTH before and after the call (`forEachAliasAfterCallStatement`; constant bases skipped). Go: the heap aliases at the statement (`forEachHeapAliasAtStatement`). |
| C2 | For each alias: the binding-back edge `P.* → b.q.*` beside `P.* → x.*`. The alias base is a gen-only target (weak, gap G7). |
| C3 | The alias edges apply to: summary results with a memory effect (a summary edge whose conclusion is not its premise; a zero summary always); the source results at the call; the end facts of a sink; the pass-rule results. |
| C4 | An identity summary result is not copied to the aliases (as today): the alias already holds the same facts, because the writes keep the aliases (§2.5). |

### 3.9 Lambdas and closures

* JVM: a call to a functional interface method that can target a lambda first takes the unresolved path (§3.7). The
  lambda tracker subscribes the call. When the type info of the prescan names the lambda class, the call becomes a
  resolved call to the lambda method. The prescan runs the current core (ap.md §7.6); the new AP only reads its result.
* Go: a call through a function value is DYNAMIC. The value binds to `this` (§3.1). `makeClosure` writes the free
  variables to `x.fv_i` (§2.3), and the closure body reads `this.fv_i`. If the resolver gives no callee, the call takes
  the unresolved path, and the closure tracker resolves it later from the type info of the prescan.
* Go `go` and `defer`: the interpreter handles them as calls at their statement, with no result.

---

## 4. Rules and their order

### 4.1 Rule kinds

| Kind | JVM | Go | Where | AP form |
|---|---|---|---|---|
| source at a call | `TaintMethodSource` | `Source` | call statement | unconditional: `zero.$ → zero.$`, `zero.$ → P.$ (T)` (`AssignMark`) or `zero.$ → P.[any] (T)` (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`), premise mark zeroMark; conditional: `Q.* → Q.*` and `Q.t' (T') → P.t (T)`, with `t' = $` for `ContainsMark(Q, T')` and `t' = [any]` for `ContainsMarkOnAnyField(Q, T')` (§4.2), and the target tail `t` (`$` or `[any]`) as above; a conjunction over several facts: §5.3 |
| entry-point source | `TaintEntryPointSource` | none | method start, zero | `zero.$ → P.$ (T)`; the condition must be true |
| exit source | `TaintMethodExitSource` | none | normal exit | as a source at a call, in the coordinates of the method |
| read source | `TaintStaticFieldSource` at `x = C.s` | `FieldReadSource` at `x = y.f`, `GlobalReadSource` at `x = G` | the read statement, zero | `zero.$ → x.$ (T)`; the condition must be true |
| sink at a call | `TaintMethodSink` | `Sink` | call statement | the sink check (ap.md §4.9); `trackFactsReachAnalysisEnd` adds end facts as source edges |
| entry sink | `TaintMethodEntrySink` | none | method start, zero | unconditional only (as today) |
| exit sink | `TaintMethodExitSink` | none | normal exit | the sink check (ap.md §4.9) |
| pass rule | `CopyAllMarks`, `CopyMark` | `CopyData`, `CopyTaintMark` | unresolved call | `CopyAllMarks(P → Q)`: `b.* → b.*` (b = base of P), `P.* → Q.*`; `CopyMark(T, P → Q)`: `b.* → b.*`, `P.$ (T) → Q.$ (T)` |
| cleaner | `RemoveMark(T, P, reach)`, `RemoveAllMarks(P)` | `RemoveMark`, `RemoveAllMarks` | call statement | `clean` (§5.2) |
| summary rewriter | user-defined source and cleaner rules | the same | call statement | `clean(P, exact, T)` on the summary results (§5.2) |

### 4.2 Conditions

* The interpreter rewrites each condition to the negation normal form, per call statement (per method for the entry
  and exit rules).
* Non-mark atoms (`IsConstant`, `IsNull`, `ConstantEq/Lt/Gt/Matches`, `TypeMatches`, `IsStaticField`, ...) are
  evaluated statically per statement. The constant atoms use the alias information. A false condition removes the rule.
* A mark atom is a LITERAL. For a sink, `ContainsMark(P, T)` is the pattern `(P, $, T)` and
  `ContainsMarkOnAnyField(P, T)` is the pattern `(P, [any], T)`. For a source or a pass rule, a literal is the premise
  of a micro edge: `ContainsMark(Q, T')` gives the premise `Q.$ (T')`, and `ContainsMarkOnAnyField(Q, T')` gives the
  premise `Q.[any] (T')`. An `[any]` premise admits every fact at or below `Q` (ap.md §4.1). Both premises have a
  concrete mark, so S8 and I7 hold. A literal of a conjunction has the same two forms (ap.md §4.6).
* For a source, a sink or a pass rule, an over-approximation makes the rule fire MORE: a negated literal counts as
  true. `Or` gives one alternative per literal. A conjunction of literals that different facts satisfy (a positive
  literal on another position): a source or a pass rule makes an ND edge (§5.3); a sink records a vulnerability with a
  set of facts (the standing assumptions per rule and statement, as today). The interpreter sets no layer. The layer
  of a result belongs to the propagation edge, and only the AP operations change it (ap.md §2.2): a fact that only
  overlaps a literal gives a demand-layer result (ap.md §4.1, §4.6). A negated literal that counts as true is the
  expected over-approximation of a path-insensitive engine, as the conjunction is (ap.md §4.6, §11.1).
* For a CLEANER the safe direction is the opposite: a cleaner that fires removes real taint. So the interpreter applies
  only the part of a conditional cleaner that the cleaned fact itself DECIDES:
  * a non-mark atom is decided statically: a false atom removes the rule, a true atom drops out of the condition;
  * no mark literal left: the cleaner is unconditional;
  * a positive literal `ContainsMark(P, T)` with an action that removes `T` (or every mark) at the location `P` itself
    (reach `exact` or `atAndBelow` at `P`): a location `P` that carries `T` satisfies the literal and loses `T`. This
    part is the unconditional cleaner `(P, exact, T)`, with the table of ap.md §4.7 (a concrete `(P, ., $, T)` is
    dropped; an abstract fact gets `*∖{T}` and the request `T`);
  * every other literal is not decided by one fact: a negated literal, a literal on another position or another
    location, `ContainsMarkOnAnyField`. A conjunction that contains such a literal is not decided. For `Or`, the
    decided parts of the alternatives are applied, chained.

  Where the condition is not decided, the cleaner does not act, and the propagation edge passes unchanged with its
  layer. This is the expected over-approximation of a fact-local, path-insensitive engine, as the conjunction is
  (ap.md §4.6). Cleaning on a condition that is not decided is unsound.
  Examples: `RemoveMark(T, P) if ContainsMark(P, T)` is the unconditional `(P, exact, T)`.
  `RemoveMark(T, Argument(0)) if Not(ContainsMark(Argument(1), RAW))` never cleans.
* Go pass rules have no condition.

### 4.3 Entry order (method start, as today)

| Language | Fact | Order |
|---|---|---|
| JVM | zero | 1. the zero fact; 2. entry sinks with a true condition (vulnerability, end facts); 3. entry-point sources with a true condition. The marks of step 3 are the ENTRY MARKS (§4.7). |
| JVM | initial fact | 1. the start fact (ap.md §6.5); 2. the filter by the context type (§5.1). |
| Go | zero | the zero fact only (no entry rules). |
| Go | initial fact | the start fact, with no filter. |

### 4.4 Statement order (non-call)

| Fact | Order |
|---|---|
| zero | 1. `zero → zero`; 2. read sources with a true condition (JVM `x = C.s`; Go `x = y.f`, `x = G`); 3. JVM: exit sources with a true condition, at the normal exit. The type info facts (lambda allocations, closures) exist only in the prescan. |
| other | §2.1, steps 1 to 6. |

### 4.5 Call order (a fact)

For the caller edge `(i, layer) → c` at the call statement `s`, in JVM and in Go:

1. RELEVANCE. If `s` does not touch `c.base`, `c` passes over the call. Stop.
2. BINDING IN. Apply the binding edges into the callee, with the caller-side type filters (§3.1). The result is the
   bound facts, one per callee position.
3. SINKS. Check the sink rules on the bound facts: the PRE-CALL, UNCLEANED fact. Requests: §5.4.
4. SOURCES. Apply the source rules on the bound facts; evaluate the ND conjunctions (§5.3). The results go to the
   caller through the binding back and the aliases.
5. PER CALLEE POSITION, for each bound fact `a`:
   1. CLEANERS: `clean` for each cleaner rule, chained (§4.8, §5.2);
   2. RESOLVED callees: the callee processing of ap.md §5.3 for each callee, with the cleaned fact as the added fact
      (events E1 and E2: add, emit, check the standing requests, subscribe, apply the summaries that it satisfies and
      the records that cover it); each new initial fact starts with the context filter (§4.3); JVM constructor: also
      pass over (§3.5);
   3. UNRESOLVED callee: the default identity and the pass rules (§3.7).
6. RETURN. The summary rewriter on the summary results (§5.2), the binding back with its filters, the aliases (§3.8),
   the field limit.

```kotlin
fun callStep(s: CallStmt, i: Premise, c: Conclusion) {
    if (c.fact.base !in s.touched) return passOver(c)                                    // 1
    val bound = s.bindIn.flatMap { b -> applyEdge(filter(b.callerBase, b.may)(c), b) }    // 2
    s.sinks.forEach { check(it, i, bound) }                                              // 3
    s.sources.forEach { applySource(it, i, bound) }                                      // 4
    for (a in bound) {                                                                   // 5
        val cleaned = s.cleaners.fold(listOf(a)) { fs, cl -> fs.flatMap { clean(cl, it) } }
        for (a1 in cleaned) {
            s.resolved.forEach { callee -> callee.enter(i, a1) }                         // ap.md §5.3, E1 and E2
            if (s.isConstructor) passOver(a1.bindBack())
            if (s.hasFailure) applyStatementSummary(s.external, i, a1)                   // §3.7
        }
    }
}   // 6: every callee result: rewriter, bindBack (filters), aliases, limit
```

The order has three effects: a sink sees the fact before the cleaners; the pass rules see the cleaned fact; the summary
rewriter acts only on the results of the call.

### 4.6 Call order (the zero fact)

| Language | Today | New |
|---|---|---|
| JVM | unconditional sinks, unconditional sources, call-to-return zero, call-to-start zero | the same |
| Go | call-to-return zero, call-to-start zero, sinks, sources (one set of outputs) | as JVM; the outputs of one step are a set, so the result does not change |

The zero fact evaluates the sink and source rules with no fact. An unconditional rule fires (also a rule whose mark
literals are all negated, §4.2). The stored assumptions of a rule at the statement can complete a conjunction (as
today). Then the zero fact passes over the call and enters every
resolved callee (§3.3).

### 4.7 Exit order (as today)

JVM, at `JMethodExitNormalInst` (after every `return`), for each fact `f`:

1. The worklist is `f` and the results of the exit sources whose condition `f` satisfies. The results keep the premise
   of `f`.
2. For each item: check the exit sinks. Their end facts join the worklist.
3. Drop the `S` facts that an exit sink read (the "global state" rule of today).
4. For a zero-premise fact on `this` or `arg(i)`: remove the entry marks (§4.3), so that an entry-point source does not
   leak into the callers.
5. Emit the summary edge. Not at the exceptional exit; not for a `local` base.

Go has no exit rules. The summary edge is the fact after each `return`, for a base that is not a `local`.

### 4.8 Several rules of one kind

| Kind | Combination |
|---|---|
| sinks | each rule is checked; the report is the union |
| sources | the union of the results |
| pass rules | the union of the results |
| cleaners | chained: the rules in list order, the actions in order. Each action applies to the survivors of the previous action. The requests are collected. A cleaner only removes locations, so the order does not change the denotation. |
| summary rewriter | chained, as the cleaners |

### 4.9 Backward run

* The micro edges and the bindings are reversed (ap.md §9.2). An alias target gets an identity edge (§2.5 A5). There
  is no type filter and no request.
* The rule roles change as follows: a forward source is a sink pattern and a reversed edge to the zero fact; a
  forward sink is a seed at the sink statement; an unconditional cleaner, and the decided part of a conditional cleaner
  (§4.2), remove the requirement, as in the forward run.
* The call order is reversed: the requirement after the call, the reversed binding back, the callee summaries, the
  CLEANERS on the requirement at the callee start, the reversed binding in, the requirement before the call.
* The SEED of a reported vulnerability at a sink call enters AFTER the reversed cleaners of that call, at the bound
  positions, and goes on through the reversed binding in. This mirrors §4.5, where the sink check (step 3) comes before
  the cleaners (step 5.1). So a method that is both a sink and a cleaner of the same mark does not kill its own seed.

---

## 5. Where the primitives apply

### 5.1 Type filter: `filter(base, may)`

The JVM predicate for the static type `t` is today's `JIRFactTypeChecker`, written as a prefix-closed predicate on the
path:

```kotlin
/** may(t, p): a path p below a value of static type t may exist. Prefix-closed: may(t, p ++ q) ⇒ may(t, p). */
fun may(t: JIRType?, p: List<Accessor>): Boolean {
    if (t == null || p.isEmpty()) return true
    return when (val a = p.first()) {
        is FieldAccessor -> t is JIRRefType &&
            (a.declaringClass == null || typeMayHaveSubtypeOf(t, a.declaringClass))   // deeper accessors: not checked
        ElementAccessor -> t is JIRRefType && typeMayBeArray(t) &&
            (t.elementTypeOrNull()?.let { may(it, p.drop(1)) } ?: true)
        ValueAccessor -> t is JIRPrimitiveType                                           // policy
        else -> true                                                                     // <C>, type info
    }
}

/** The mark policy (not a may-predicate): a concrete mark directly on a primitive or boxed base. */
fun markPolicyKeeps(t: JIRType?, f: Fact): Boolean =
    !(f.path.isEmpty() && f.mark.isConcrete && t?.unboxIfNeeded() is JIRPrimitiveType && !f.mark.isPrimitiveTracking)
```

Rules:

* The filter tests only the concrete path: a fact passes if `may(t, f.path)`. The `*` and `[any]` tails are always
  kept; the filter never changes a tail. The analysis does not store a filter in a fact or an edge, and it does not
  propagate it (ap.md §4.8). So a `*` or `[any]` fact keeps the locations below its path that `t` cannot have: an
  expected false-positive source (ap.md §11.1).
* Policy cases are outside ap.md S5 (they can drop a real flow), as today: the mark policy above; `[e]` on a class type
  other than `Object` (for example `Cloneable`, `Serializable`); `[value]` on a reference type. The mark policy is not a
  type filter: it reads the mark, not only the path, and the model has no mark filter. It is gap G6.
* Two filters on one base are a conjunction.

| Point | Base | Type | Today | New |
|---|---|---|---|---|
| operand of `x = y`, `x = a op b` | y; a, b | the static type of the operand | yes | the same |
| cast `x = (T) y` | y | `T` (narrows y on the normal path) | yes | the same |
| field read or write `y.f` | y | the static type of y AND the declaring class of f | yes | the same |
| array read or write `y[i]` | y | the static type of the array | yes | the same |
| lhs of an assignment | x | the static type of x | yes | the same, on the results (§2.1 step 5) |
| binding in: receiver | o | the declaring class of the method that the call names | yes | the same |
| binding in: argument | ai | the static type of `ai` (caller side) | yes | the same |
| binding back: receiver, argument | o, ai | the static type at the caller | yes | the same |
| binding back: result | r | the static type of the lhs | yes | the same |
| method start | `this`; `arg(k)` | the context type; `this` with no context: the enclosing class | yes | the same |
| pass rule | the from and to positions | the declared types of the positions in the signature of the called method | yes | the same |
| summary application, under a `*` node | caller content | the type of the path to the `*` | yes | none (D13) |
| summary exit, compatibility | summary conclusion | the last field type of the premise | yes | none (D14) |
| backward run | none | none | none | none |
| Go | none | none | none | none |

### 5.2 Cleaner: `clean(cleaner)`

A cleaner is `(base, path, reach, mark)` with `reach ∈ {exact, below, atAndBelow}` and `mark` one mark or all marks
(ap.md §4.7). The interpreter maps the rule actions as follows. The base is in callee coordinates (§1.3).

| Rule action | Cleaner | Note |
|---|---|---|
| `RemoveMark(T, P, Exact)`, P with no `AnyField` | `(P, exact, T)` | |
| `RemoveMark(T, P.AnyField, Exact)` | `(P, below, T)` | today: `cleanAnyFieldMark(keepStart = true)` |
| `RemoveMark(T, P, ExactAndAnyField)` | `(P, atAndBelow, T)` | the meaning of the rule (D9) |
| `RemoveAllMarks(P)` | `(P, atAndBelow, all)` | today: the subtree at P goes |
| `RemoveAllMarks(P.AnyField)` | `(P, below, all)` | today: only an `[any]` child goes (D10) |
| Go `RemoveMark(T, P)`, `RemoveAllMarks(P)` | as the JVM `Exact` rows | P with `AnyAccessor` maps to `below` |
| JVM position of type `String` | also `(P.<string-bytes>, same reach, same mark)` | as today |

The cleaner condition is evaluated on the bound fact by the cleaner rule of §4.2 (a condition that the fact does not
decide does not clean).
The decided literal `ContainsMark(P, T)` raises the request `T` through `clean(P, exact, T)` on an abstract fact
(§5.4); an undecided literal raises no request.

| Point | Facts | Rules | Today | New |
|---|---|---|---|---|
| call, before the callee processing (§4.5 step 5.1) | each bound fact | every cleaner rule of the method that the call names | JVM yes; Go no | JVM and Go (D7) |
| call, unresolved callee | the same cleaned fact feeds the default identity and the pass rules | the same | JVM yes (the step comes before the resolution); Go no | JVM and Go (D7) |
| call, summary rewriter | the summary results and the unresolved results, before the binding back | user-defined source and cleaner rules: `(P, exact, T)` for each mark `T` of the rule and each action position `P` | JVM, Go | the same; it is an interpreter feature |
| backward run | the requirement at the callee start | unconditional cleaners and the decided parts of conditional cleaners (§4.2) | — | §4.9 |

The rewriter makes a user-defined rule replace the callee body for its marks: the callee can neither add nor keep these
marks at the rule positions. A summary result is a caller edge, so a request of the rewriter goes to the CALLER
premise. A cleaner on `Result` acts only through the rewriter (open question Q1).

### 5.3 ND conjunction

* The interpreter evaluates the conjunctive SOURCE rules at step 4 of the call order (§4.5): on every bound,
  uncleaned caller fact, and on the zero fact (§4.6). It evaluates the conjunctive PASS rules (JVM, with a condition)
  at step 5.3, on the cleaned fact.
* Every literal names its mark, so it has a concrete mark (ap.md S9). Its tail is `$` (`ContainsMark`) or `[any]`
  (`ContainsMarkOnAnyField`) (§4.2). ap.md §4.6 sets the layer of the result: normal if both inputs are normal and
  covered by their literals. A normal result is exact against the path-insensitive support semantics (ap.md §4.6,
  `NDExact.nd_edge_exact`).
* A fact that overlaps a literal and passes its mark gate (ap.md §4.6) is an assumption for (rule, statement, literal),
  as today. The interpreter stores it in the conjunction store (ap.md §8.9). The last fact that arrives sees all
  earlier ones, so the result does not depend on the order.
* The number of different premises in a full product decides the edge: 0 a zero-to-fact edge, 1 a plain edge, 2 or
  more an ND edge (ap.md §4.6).
* A literal on a `*`-mark fact raises a request (run 1), not an assumption.
* An ND summary of a callee applies at step 5 of the call order. ap.md §4.6 and §8.9 define how the caller finds the
  facts for the other premises (event E6 of ap.md §5.3).
* Sinks, exit sources and the zero-to-zero step never make an ND edge.

### 5.4 Requests

A request exists only in forward run 1. The interpreter raises it where a rule needs a concrete mark `T` and the fact
has the mark `*` or `*∖X` with `T ∉ X` (and its premise has an abstract mark). The request is on the premise of the
edge. A fact whose mark excludes `T` raises no request for `T`.

| Point | Rule element | Mechanism |
|---|---|---|
| sink at a call, exit sink | `ContainsMark`, `ContainsMarkOnAnyField` | the sink check (ap.md §4.9) |
| source at a call, exit source | the premise mark of a conditional source | the mark gate of `applyEdge` (ap.md §4.1 step 4) |
| pass rule | the premise mark of `CopyMark(T)` | the mark gate |
| cleaner | the decided literal `ContainsMark(P, T)` (§4.2) | `clean` of `(P, exact, T)`, not the mark gate (the gate gives no fact, so it would lose the fact for every mark) |
| cleaner action | one mark, a `*`-mark fact, a partly cleaned position (no request if the fact mark excludes `T`) | `clean` (ap.md §4.7) |
| summary rewriter | as the cleaner action | `clean`, on the caller premise |
| ND source | a literal on a `*`-mark fact | the mark gate |
| static read, static write, sink on `S` | a static position (`[<C>, s]`, the class `[<C>]`, a sink path) below an abstract static fact | the position request (ap.md §4.10); a mark request on a static premise answers with the added fact itself |
| entry rules, read sources | none (unconditional) | none |

In a restricted run and in the backward run no fact has the mark `*`, so no request can occur. The interpreter asserts
this (ap.md §13 item 9).

---

## 6. Deviations from today's code

| # | Topic | Today | New | Why |
|---|---|---|---|---|
| D1 | read `x = y.f` | `y\{f} → y`, `y.f → y.f`, `y.f → x` (keep-except) | `y.* → y.*`, `y.f.* → x.*` | a read never changes an exclusion (I3) |
| D2 | self read `x = x.f` | `x\{f} → null` (refine only), `x.f → x` | `x.f.* → x.*` | no refinement |
| D3 | a fact above a micro-edge premise | the premise is refined (`SideEffectRequirement`, `refineInitial`) | unguarded `applyEdge`: an `[any]` result in the demand layer | no refinement (I2) |
| D4 | mark readers at sinks, sources, cleaners, exits | `FactReader` refinement, any-field unfold requests | the request, run 1 only (§5.4) | ap.md §4.5 |
| D5 | summary application | delta with refinement (`tryApplySummaryEdge`) | guarded by satisfaction | ap.md §4.3 |
| D6 | call bindings | rebase functions (`mapMethodCallToStartFlowFact`, `mapMethodExitToReturnFlowFact`) | binding micro edges (§3.1) | one operation for every flow (I4); same mapping |
| D7 | Go cleaners | only the summary rewriter, only user-defined `RemoveMark` | `clean` at the call site for every cleaner rule, plus the rewriter | decision: the same placement in both languages |
| D8 | cleaner on an abstract fact | `DeepAccessorExclusion` claims; a refinement request on abstract nodes | `clean` (`*∖x` mark; a request on a partly cleaned position) | ap.md §4.7 |
| D9 | reach `ExactAndAnyField` | cleans only through an `[any]` at the position | `atAndBelow` | `[any]` means "any continuation" in the new AP. The cleaner removes a mark only from a fact that lies inside the cleaned locations (ap.md §4.7), so it over-approximates |
| D10 | `RemoveAllMarks(P.AnyField)` | removes only an `[any]` child | `(P, below, all)` | the same meaning of `[any]` |
| D11 | type filter form | `FactTypeChecker` over the tree (Accept, Reject, FilterNext) | `filter(base, may)`, prefix-closed, tails kept, a separate mark policy | the ap.md §4.8 primitive; same predicate |
| D12 | `[any]` fact with a primitive-tracking mark on a primitive base | kept as `$` | kept as `[any]` | the filter never changes a tail (precision only) |
| D13 | filter of the caller content under `*` in the summary application | `AccessTree.concat` filters by the path type | none | the filter acts on bases at fixed points; precision only (Q3) |
| D14 | exit compatibility filter (`JIRMethodSummaryEdgeProcessor`) | removes `*` at incompatible fields | none | the same (Q3) |
| D15 | static base at a call in a restricted run | always touched (as in the model call of ap.md §5.1) | not touched when the callee touches no static (§3.3) | the static fact does not enter a callee that touches no static; needs the final call graph (G5) |
| D16 | depth gate, `[any]` depth charge in the step | `INITIAL_ALLOWED_FACT_DEPTH`, `+10,000` | the field limit only | ap.md §4.4 |

Kept as today (no deviation): the rule order at entry, call and exit; the lhs kill; liveness; the alias analyses and
their use; the constructor rule; the exception rule; the exit rules for `S` and the entry marks; the Go pointer model;
no Go type filter; unconditional Go pass rules; the summary rewriter; the `<string-bytes>` rule; no type filter in the
backward run.

---

## 7. Test plan

### 7.1 Existing tests and the rows they pin

| Test | Rows | Status |
|---|---|---|
| `JIRStatementSummaryTest`: field read, static read, array read | §2.2 reads, D1 | UPDATE: expect `y.* → y.*`, no keep-except |
| `JIRStatementSummaryTest`: self read | §2.2 `x = x.f`, D2 | UPDATE: no refine-only edge |
| `JIRStatementSummaryTest`: field write, static write, array write weak, self write | §2.2 writes, §2.1 write rule | keep (read the exclusion as the edge exclusion) |
| `JIRStatementSummaryTest`: cast, binary, return | §2.2, §5.1 cast filter | keep |
| `JIRStatementSummaryTest`: reversed rows | §4.9 | UPDATE the reversed read |
| `GoStatementSummaryTest`: field store strong | §2.3 `y.f = v` | keep |
| `GoStatementSummaryTest`: comma-ok lookup | §2.3 comma-ok, D1 | UPDATE: `m.* → m.*` |
| `GoSequentExactTest` (copy, field read, phi, alias of an overwritten field) | §2.3, §2.5 | keep; the field read case changes as D1 |
| `GoSequentRoundTripTest`, `GoSequentUnchangedAgreementTest` | §2.1 step 2, §4.9 | keep |
| `AliasSampleTest`, `DSUAliasAnalysisStateTest`, `DSUAliasAnalysisInvalidateOuterHeapAliasesTest`, `GoDSUAliasAnalysisTest`, `GoAliasSampleTest`, `GoAliasFactsTest`, `AliasDirectiveTest` | the alias input of §2.5 and §3.8 | keep |
| `FactCleanerContractTest`, `AnyFieldMarkExclusionTest`, `DeepAccessorExclusionTest` | the old cleaner representation | REPLACE by the vectors of `clean` (ap.md §4.7) and the mapping table of §5.2 |
| `CleanerFieldSensitivityAnalysisTest`, `DeepCleanSummaryAnalysisTest`, `CleanerDslAnalysisTest`, `CleanerDslControlFlowAnalysisTest` | §4.5 order (sinks before cleaners), §5.2 mapping (plain = `exact`, AnyField = `below`), the `Result` cleaner tests | keep (phase-2 gate) |
| `AnyFieldPrimitiveAnalysisTest` | §5.1 mark policy, `[any]` tails, D12 | keep |
| `ExampleTest` `test nd rule` (`PositiveNdRule`, `PositiveNdRule2`) | §5.3 | keep |
| `MultiReturnDataFlowTest` | §4.7, §3.4 (no leak over the exceptional exit) | keep |
| `JavaDataFlowReachabilityTest`, `KotlinDataFlowReachabilityTest` (lambda, stream, collection samples) | §3.6, §3.7, §3.9 | keep |
| `DataFlowBenchFalseNegativeTest` (exception arms disabled) | §3.4 | keep disabled (G1, ap.md §11.2) |
| Go `InterfaceDispatchTest`, `MethodReceiverTest` | §3.1 receiver, §3.6 | keep |
| Go `ClosureTest`, `ClosurePatternTest` | §2.3 closures, §3.9 | keep |
| Go `GlobalTest`, `GlobalSourceTraceTest` | §2.3 globals, read sources | keep |
| Go `MultiReturnTest`, `MultiReturnPatternTest` | §2.3 `ret.#i`, `extract` | keep |
| Go `PointerHeapTest`, `PointerPatternTest` | §2.3 `*p = v`, §2.5 | keep |
| Go `PassThroughTest`, `MapOpsTest`, `ChannelPatternTest`, `CollectionTest`, `SanitizationTest`, `DeferTest`, `GoroutineTest` | §3.7, weak writes, kills, `go`/`defer` | keep |

### 7.2 New tests

1. Builder tests, one per row of §2.2 and §2.3: the edges, the touched bases, the filters.
2. Write rule: the strong write of a two-accessor path (`C.s = x`) gives two identity edges with one exclusion each;
   `*p = v` gives none.
3. Binding tests, one per row of §3.1, JVM and Go, with the filters.
4. Order tests: a sink sees the fact before a cleaner at the same call; a pass rule sees the cleaned fact; a source
   result goes through the aliases; a constructor fact passes over the call.
5. Go cleaner at the call site (D7): a non-user-defined `RemoveMark` rule cleans the argument; the same rule with a
   resolved callee and with an unresolved callee.
6. Cleaner mapping: one test per row of §5.2, including `<string-bytes>`.
7. Type filter placement: one test per row of §5.1; a `*` and an `[any]` fact always pass; the policy drops a mark on
   an `int` base.
8. Requests: one test per row of §5.4 in run 1; no request in a restricted run and in the backward run (assert).
9. ND: the result does not depend on the order in which the two premise facts arrive.

---

## 8. Open questions

The resolved questions (Q4, Q5, Q7, Q8, Q9) are in [`ap-history.md`](ap-history.md) §5.

| # | Question |
|---|---|
| Q1 | A cleaner action on `Result` that is not user-defined has no effect today: no bound fact has the base `ret`. Proposal: apply `clean` to the results on `ret` before the binding back, for every cleaner rule. A decision is necessary. |
| Q2 | Go has no type filter. The placement points of §5.1 fit Go too. Add a Go type checker? |
| Q3 | D13 and D14 drop two precision filters of the summary application. Restore them as a filter on the summary conclusion, or make `may` recurse through the declared field types (prefix-closed too, and it covers most of D13)? |
| Q6 | The summary rewriter can raise a request on the caller premise (§5.2). The alternative is no request and a result in the demand layer. Confirm. |
| Q10 | The gaps G1–G6 (§0.1) lose real flows. Keep them as today, or close some of them (G3: check the sinks of the cleaner method on the uncleaned fact; G4: read the rules of the resolved override too)? |
