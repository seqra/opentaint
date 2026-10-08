# IR interpreter — specification

Status: design spec, the companion of [ap.md](ap.md). This document is normative. `ap.md` defines the access path (AP),
its operations and its primitives. This document defines how the analyzer interprets the IR of the JVM (JIR) and of Go
(GoIR) with these primitives. The two documents together define the analysis. The names of today's code in this
document identify the parts that the implementation reuses or replaces; they are not definitions. The design history
is in [ap-history.md](ap-history.md); it is not normative.

Language: ASD-STE100 Simplified Technical English.

---

## 0. Scope and relation to ap.md

This document defines:

1. the micro edges of the non-call statements (§2);
2. the micro edges of the call statements: the bindings, the result, the aliases (§3);
3. the order in which the interpreter applies the rules, in the forward run and in the backward run (§4);
4. the points where the interpreter applies the type filter, the cleaner, the ND conjunction and the request (§5).

It does not define the AP operations. It uses them by name:

| ap.md operation | Function | Used in |
|---|---|---|
| `concat` as a micro edge (ap.md §4.1, §4.2) | one micro edge on one fact; it applies to every fact on its base that overlaps its premise (I2) | §2, §3 (bindings, the unresolved callee §3.7), §4.1 (the rule statement of a call), §1.4 (the `RemoveAllMarks` kill on `S`) |
| `concat` as a summary edge (ap.md §4.1, §4.3) | only to an added fact that satisfies the premise | §4.5 step 5.2 |
| field limit (ap.md §4.4) | cuts a result, never a micro edge (I10) | §2.1 step 6, §4.3, §4.5 steps 4 and 6, §4.7 |
| mark request (ap.md §4.5) | run 1 only | §5.4 |
| position request (ap.md §4.10) | run 1 only, on the static base | §2.1 step 4 (also for the statement micro edges at a call: §1.4, §3.7, §4.1, §4.5 step 5; and for the rule statement of an exit: §4.7), §5.4 |
| ND conjunction (ap.md §4.6) | an edge keyed by a set of premises | §5.3 |
| `clean` (ap.md §4.7) | removes marks at a position | §5.2 |
| `filter(base, may)` (ap.md §4.8) | removes the facts of `base` whose path `may` rejects | §5.1 |
| sink check (ap.md §4.9) | compares a sink pattern with a fact | §4.1, §5.4 |
| reversal (ap.md §9.1, §9.2) | the backward form of a micro edge | §4.9 |
| emission, storages (ap.md §6, §8) | abstraction and stores | not used directly |

Notation. ap.md §1 defines the common notation: the micro-edge sides `x.p.*`, `x.p.$ (T)` and `x.p.[any] (T)`, the
exclusion subscript `a →_{f} b`, the accessors `[e]` and `<C>`, the fact tuple, the touched-base set `{x, y}` and the
bound fact. This document adds only:

| Form | Meaning |
|---|---|
| `#i` | The tuple slot `i` (Go, §1.2). It is written `#i` so that it is not the `$` tail. |
| `<G>` | The class accessor of the Go global `G` (§1.2). |
| `y\{f}`, `→ null` | Only in a column "Today" (§2.4, §6). An edge of today's `StatementSummaryBuilder` in today's notation: a side `y.f` is the base `y`, the path `.f` and today's abstract tail; `y\{f}` is the part of `y` outside the field `f` (an edge `y\{f} → y` keeps every location of `y` except those at or below `y.f`; today it also refines a premise that does not exclude `f`); `\{e}` is the same for the element accessor; `→ null` is an edge with no target: it only refines the premise. |

Common rules:

| # | Rule |
|---|---|
| I1 | The interpreter gives each statement a STATEMENT SUMMARY: the touched bases, the micro edges, and the type filters of each touched base. The AP applies it (ap.md §4.2, the statement transfer). Every micro edge reads from a touched base (ap.md S10). |
| I2 | Micro edge application is UNGUARDED. The AP applies every micro edge to every fact on its base that overlaps its premise, in both cases of ap.md §4.1: at or below the premise, and above it. A fact above the premise of a micro edge gives an uncorrelated result in the demand layer. There is no refinement. Two exceptions: (1) STATICS IN RUN 1 (§2.1 step 4; the rule is ap.md §4.10 item 1), for a fact `c`: Run 1 only, statement micro edges only: when the edge of `c` is an identity static `*` edge at the root `[]` or at a class `[<C>]`, a micro edge whose premise path `p` lies strictly below `c` (the exclusion of `c` admits the rest) gives no fact and no mark request; it raises the position request for `p` cut to at most two accessors. Below a static field the ordinary rules apply. (2) THE ALIAS EDGES AT A CALL apply only to the results that §3.8 AC3 and AC4 select. |
| I3 | A read never changes an exclusion. Only a STRONG WRITE adds the written accessor to the exclusion of the identity edge of the written base: `a.* →_{f} a.*`. |
| I4 | A call binding is a micro edge (I2 applies). Its premise and its target have the `*` tail and the mark `*` (ap.md S10, S11). A callee summary edge is not a micro edge: it applies only if the added fact satisfies its premise (ap.md §4.3). |
| I5 | The interpreter is the same in every run. The differences: requests exist only in forward run 1 (§5.4). In a forward restricted run, the core fires an unconditional source (a micro edge from the zero fact to another base) only if it is a source seed (ap.md §6.1 rule 6; analyzer-core.md §4.7). The backward run reverses the micro edges and applies no type filter; the core records the sources that it reaches (§4.9). |
| I6 | MARK WELL-FORMEDNESS (ap.md S7): no micro edge or binding has a premise mark `*∖X`, and a micro edge with a concrete target mark has a concrete premise mark (a source: `zeroMark`; a conditional source: `T`). Without it a normal-layer edge can claim a cleaned mark. |
| I7 | NO UNIVERSE (ap.md S8): a micro edge with a `$` premise has a concrete premise mark; a micro edge with a `$` target has a concrete premise mark; no micro edge has a `$` premise and a `*` target; no micro edge, binding or initial fact has the kind `*/Universe`. Every exclusion that the interpreter makes is a finite set of accessors. |
| I8 | NO `*`-PREMISE CALLEE SUMMARY in a restricted run (ap.md §6.3). The interpreter precomputes no callee summary. An EMPTY METHOD is a method with no instruction (JVM: an empty instruction list, for example a native or an abstract method; Go: a function with no body). It is not analysable, and the analysis never analyses it. The call resolver drops an empty method from the callees of a call (§3.6). A call whose every resolution result is an empty method is an UNRESOLVED call (§3.7: the default identity and the pass rules). No summary exists for an empty method, also no identity summary (D28). An unresolved callee is a statement summary (§3.7), not a callee summary. |
| I9 | PRECISE AND COMPLETE MICRO EDGES (ap.md S1, S2, §4.2): every micro edge (a statement edge with its alias edges, or a call binding edge; not a callee summary edge) gives exactly the concrete flows of its statement (ap.md §3.5). A micro edge has NO LAYER: the layer belongs to the propagation edge, and only the AP operations change it (ap.md §2.2). |
| I10 | NO FIELD LIMIT ON A MICRO EDGE: a micro edge keeps its full paths (also an alias path `c.q.p` of any length). The field limit applies to the results of an application (ap.md §4.4 lists the cut points): the statement step, also the read sources (§2.1 step 6, §4.4); the return of a call, also the source results, the end facts of a sink at a call and the pass-rule results (§4.5 steps 4 and 6); the results of the entry rules (§4.3); the results of the exit rules (§4.7); the conjunction result (§5.3); and the backward seed (§4.9). |
| I11 | BACKWARD CONTRACTS (ap.md S11, items (a) to (f)). The interpreter makes these true: (a) every binding has the `*` tail and the mark `*` on both sides (§3.1); (b) every statement micro edge is MARK-REVERSIBLE (ap.md §9.1): its target mark is abstract (`*` or `*∖X`), or its premise mark is concrete. Every row of §2, §1.4 and §4.1 has this form; (c) no call binds the zero base back (§3.3); (d) every statement that touches the zero base has the keep edge `zero.$ (zeroMark) → zero.$ (zeroMark)`, and no other micro edge, no binding back and no conjunction has its target on the zero base (the only binding into the zero base is `zero.* → zero.*`, §3.1; Lean `NDZeroBase.NoZeroGen`): the read statement with a read source (§4.4), the rule statement of a call (§4.1), and the method start and the exits with their sources (§4.3, §4.7); no cleaner acts on the zero base; and no type filter is on the zero base (so a type filter on the zero base accepts the empty path, as ap.md S11 (d) asks); (e) for every method that is a root or the callee of a call, every node on a CFG path from the method entry has a CFG path to the method exit: the implementation wires code that never returns to an exit node (§4.9); (f) every sink pattern has the tail `$` (`ContainsMark`) or `[any]` (`ContainsMarkOnAnyField`) (§4.2). Lean: `Reverse.BindTargetsStar`, `Backward.StmtsMarkRev`, `Backward.NoZeroBack`, `Backward.ZeroKept`, `Backward.ExitReach`. |
| I12 | STATIC CONSTRUCTION RULES (ap.md S12, items (a) to (g); ap.md §4.10). A STATIC POSITION is the premise path of a statement micro edge on `S`, or the path of a sink pattern on `S`, cut to at most two accessors (`[<C>, f]`, `[<C>]`, Go `[<G>]`). The interpreter makes these true. (a) A statement micro edge from `S` to `S` is an identity restriction `S.q.* →_E S.q.*` (the keep edges of a static read, of a static write and of the kill of `RemoveAllMarks`, §1.4, §2.2, §2.3) or a field-to-field edge (a pass rule between static fields, §1.4). (b) A statement micro edge from another base into `S` whose target path lies strictly above a static position has a `$` target and a `$` premise with a concrete mark: a mark on a class position, `zero.$ (zeroMark) → S.<C>.$ (T)` or `Q.$ (T') → S.<C>.$ (T)` (§1.4). A conjunctive micro edge into such a target has a `$` premise with a concrete mark for each literal (§1.4, §5.3). So no rule makes a `*` or an `[any]` fact on a bare class position, and no pass rule reads or writes a bare class position. (c) A call binds `S` only by `S.* → S.*` (§3.1). (d) The field limit of run 1 is at least 1 and the class accessor is not counted, so a cut never stops strictly above a static position. (e) A cleaner on `S` names its mark (§1.4); `RemoveAllMarks` on a position of `S` is not a cleaner. One exception: the WHOLE-BASE CLEANER `(S, atAndBelow, all)` with the empty path (the rule position `AnyClassStatic`, §1.4, §5.2). Every fact on `S` lies inside it, so it drops the fact and never cleans a fact in part; it has the effect of the kill of a strong write of the whole base `S` (no keep edge, §2.1). (f) `S` is not the zero base. (g) The abstraction of run 1 is the policy of ap.md §6.2: run 1 serves an added fact by its root. A rule position can be deeper than a static field: below the static field the ordinary rules apply. Lean: `Statics.SWF` (its parts `ss`, `write`, `toC`, `fromC`, `cut`, `clean`, `base`, `alpha`), `Statics.PosIn`. |
| I13 | VALIDITY (ap.md S13, §4.8). The placement of the type filters (§5.1) makes a validity predicate on locations exist with three properties: every type filter accepts every valid location of its base; the validity goes back along every statement micro edge and along every call binding, into the callee and back (a valid end location comes only from a valid start location); and it goes back from the target of a conjunctive micro edge to each literal (§5.3). A valid location is a location that every type filter accepts (ap.md §4.8). The exactness and confirmation theorems of ap.md hold only for valid end locations. Lean: `Exact.FiltValid`, `Exact.BackOK`, `NDExact.ConjOK`. |

### 0.1 Known gaps against ap.md S1, S2 and S5

ap.md S1 asks that the micro edges of a statement give exactly its real flows (S2 the same for the aliases, S5 for the
type filters). The interpreter does not do this at the points below (as today, except where a row names a deviation of
§6). The soundness theorems of ap.md do not cover a flow that a soundness gap loses. A precision gap adds a flow that
does not exist in the real program. The analysis keeps this flow in the normal layer, so the exactness theorems hold
only relative to the gap. ap.md §11.1 lists the expected false-positive sources (G7, G8, and the type filter on a `*`
fact).

| # | Gap | Where | Effect |
|---|---|---|---|
| G1 | No exception flow crosses a call, and a catch block does not read `exc`. Out of scope (ap.md §11.2). | §3.4 | a thrown tainted value is lost |
| G2 | THE GLOBAL-STATE RULE: at the normal exit, the part of an `S` item on which a mark literal of an exit sink (plain or conjunctive) holds is dropped from the summary edge. A conjunctive exit sink keeps that part as the stored input of the literal (§5.3). Also the entry marks on zero-premise `this`/`arg` facts are removed. | §4.7 steps 3, 4 | premise-dependent removals, not an AP primitive |
| G3 | The cleaners run before the callee body. | §4.5 step 5.1 | a sink inside the body of the cleaner method sees the cleaned fact |
| G4 | The rules come from the method that the call names, not from the resolved override. | §3.6 | a sink or source on an override is missed |
| G6 | The mark policy and the policy cases of the type filter. | §5.1 | they can drop a real flow (outside ap.md S5) |
| G7 | The write at an alias is weak (A3, AC2). | §2.5, §3.8 | precision: the old content of the alias path survives (sound if an alias does not hold); an expected false-positive source (ap.md §11.1) |
| G8 | A constructor call keeps the caller facts that it overwrites. | §3.5 | precision: a weak update of the receiver and the arguments; an expected false-positive source (ap.md §11.1) |
| G9 | A catch handler reads the facts AFTER each statement of the try range: a statement that throws counts as completed (its kill, its writes and the cleaners of a call apply). The catch statement does not kill its local. As today. | §2.2 (catch), §3.4 | a flow on the state before the throwing statement is lost (`try { s = clean(s); } catch (E e) { sink(s); }`); precision: an old fact on the catch local stays |
| G10 | No class initializer (`<clinit>`) is analysed: it has no call site, and it is not a root. As today. | §3.3 | a value that a static initializer writes to a static field is lost (for example a source in `static final String K = System.getenv("K")`) |
| G11 | A pass rule with a mark literal in its condition applies without its mark literals (D24). | §4.2 | precision: the pass edge also fires where the literal is false |

THE ALIAS ANALYSIS is outside the scope of this specification. The analysis uses it as it is and does not change it.
Its settings (the interprocedural depth 0 of A1, the analysis on or off, its time limit) are as configured, and A6
holds relative to them. Under A1 an alias on the static base does not hold after a call, so AC1 gives no alias base on
`S`, and the alias edges of a call keep I12 (c).

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
| `[value]`, type info | not an accessor of the new analysis (ap.md W5): `ValueAccessor` is made by no statement and no rule; the type-info accessors serve only the lambda analysis of the prescan (ap.md §1) | the same | — |

### 1.3 Rule positions

A rule names positions in CALLEE coordinates. At a method entry and at a method exit, the positions are in the
coordinates of the method itself.

| Position | Base and path | Note |
|---|---|---|
| `Argument(i)` | `arg(i)` | |
| `This` | `this` | Go: also the target of a dynamic call |
| `Result` | `ret` | at a call: the lhs after the binding back |
| `ClassStatic(C)` (JVM) | `S.<C>` | a CLASS POSITION: the rules on it follow §1.4 |
| `AnyClassStatic` (JVM) | `S`, the empty path | the WHOLE STATIC BASE: only in a `RemoveAllMarks` action (§1.4, §5.2); in every other rule element it is a rule error |
| `PositionWithAccess(P, Field f)` | the path of `P` and `f` | |
| `PositionWithAccess(P, Element)` | the path of `P` and `[e]` | |
| `PositionWithAccess(P, AnyField)` | the path of `P` | sink and condition: the `[any]` pattern; source target and pass-rule target: the `[any]` tail; pass-rule source: the `[any]` premise (§4.1); cleaner: the reach (§5.2). Go: `AnyAccessor`, the same. |

Two invariants hold for every rule position:

1. it has at most one `AnyField` accessor (Go: `AnyAccessor`);
2. if it has an `AnyField` accessor, this accessor is the LAST accessor: no concrete accessor comes after it.

A rule with a position that breaks an invariant (for example `Argument(0).AnyField.f` or
`Argument(0).AnyField.AnyField`) is a RULE ERROR: the interpreter rejects the rule and logs it once (D29). The builder
of the forms never fails on such a rule.

### 1.4 Rules on a static position (JVM)

A static access in the IR always names a field: the path `[<C>, s]` (§2.2). A CLASS POSITION `S.<C>` holds marks only:
a rule can put a concrete mark on it (for example the state marks that the rule generator puts on a synthetic class),
but not a tree of fields. A rule can also name a static field `S.<C>.s`, and, only in a `RemoveAllMarks` action, the
whole static base `S` (`AnyClassStatic`, the empty path). Go rules have no static position. The
interpreter maps a rule element on a static position as follows, so that the construction rules of I12 hold.

| Rule element on a static position | Interpreter form | Reason |
|---|---|---|
| a source or pass-rule target `[any]` on a class position: `AssignMarkOnAnyAccessor` on `ClassStatic(C)`, or the target `PositionWithAccess(ClassStatic(C), AnyField)` | rule error: the interpreter rejects the rule | a static access always names a field; an `[any]` fact on a bare class lies above every static field of `C` (I12 (b); Lean `Statics.CexAny`) |
| `AssignMark(T)` on `ClassStatic(C)`, with no condition | `zero.$ (zeroMark) → S.<C>.$ (T)` | a concrete mark on a class position (§4.1) |
| a conditional rule whose target is a class position (`AssignMark(T)` on `ClassStatic(C)` with a mark condition) | for each alternative of the condition (§4.2): the premise `Q.$ (T')` for each positive literal `ContainsMark(Q, T')`. An alternative with one positive literal gives the edge `Q.$ (T') → S.<C>.$ (T)` (§4.1); an alternative with two or more positive literals gives a conjunctive micro edge with the target `S.<C>.$ (T)` (an ND edge, §5.3). A `ContainsMarkOnAnyField` literal in such a rule is a rule error: the interpreter rejects the rule | a write above a static position needs a `$` premise with a concrete mark (I12 (b); Lean `Statics.SWF`, part `write`); `ContainsMarkOnAnyField` gives an `[any]` premise |
| `CopyAllMarks` or `CopyMark` FROM or TO a class position `ClassStatic(C)` (no field) | rule error: the interpreter rejects the rule | a pass rule is a handcrafted summary, and no data flows from or to a bare class |
| `CopyAllMarks` or `CopyMark` from a static field to a static field (or between a static field and another base) | the rows of §4.1: `b.* → b.*` (`b` = the base of `P`), `P.* → Q.*` (or `P.$ (T) → Q.$ (T)`) | a field-to-field edge (I12 (a)) |
| `RemoveAllMarks(P)`, `P` on `S` at any depth: a class `ClassStatic(C)`, a static field `S.<C>.f`, or deeper (reach `atAndBelow`) | the KILL of a strong write with no value at `P`: a statement summary that touches `S`, with the keep edges `strongKeep(S, path of P)` of §2.1 and no other micro edge. For a class: `S.* →_{<C>} S.*`. For a static field: `S.* →_{<C>} S.*` and `S.<C>.* →_{f} S.<C>.*` (the row of `C.s = x` in §2.2 without the value edges). Deeper: one identity keep edge per proper prefix of the path, each with the next accessor as its exclusion. In run 1 a keep edge whose premise lies strictly below an identity static `*` edge at the root or at a class raises the position request (§2.1 step 4). At a call the kill applies at the place of the cleaner, in the rule order (§4.5 step 5.1). The backward run applies the same keep edges (their reversal is the same edge) at the place of the reversed cleaners (§4.9 step 6) | a strong update removes every mark at and below `P`; the kill is not a cleaner on `S`, and no mark is enumerated |
| `RemoveAllMarks(P.AnyField)`, `P` on `S`, also a class (reach `below`) | rule error: the interpreter rejects the rule | the kill of a write also removes `P` itself, and a cleaner of every mark on `S` is not allowed (I12 (e)) |
| `RemoveAllMarks(AnyClassStatic)`: the whole static base | the WHOLE-BASE CLEANER `(S, atAndBelow, all)` with the empty path (§5.2): it drops every fact on `S`. As every cleaner, it acts only if its rule is unconditional (§4.2). It raises no request (every fact on `S` lies inside it, ap.md §4.7) | every fact on `S` lies inside the cleaner, so no fact is cleaned in part (I12 (e)); the Spring dispatcher uses it (D27) |
| `AnyClassStatic` in every other rule element (a sink, a condition, a source, a pass rule, `RemoveMark`) | rule error: the interpreter rejects the rule | only the whole-base cleaner has a form on the empty path of `S` |
| `RemoveMark(T, P, reach)`, `P` on `S` | the cleaner `(P, reach, T)` of §5.2 | a cleaner on `S` names its mark (I12 (e)) |
| a sink or a conjunction literal on a static position (`ContainsMark`, `ContainsMarkOnAnyField`) | the rows of §4.1, §4.2 and §5.3: the sink check of ap.md §4.9, or the literal of ap.md §4.6 (a condition of a rule with a class target: the row above) | the ordinary mark request of run 1 (ap.md §4.5); on a static premise its answer is the added fact itself (ap.md §4.10 item 4) |
| the one literal of a conditional source on a static position (at a call, §4.1; at an exit, §4.7) | the premise `Q.t' (T')` of a statement micro edge (§4.1, §4.2) | in run 1 the static exception of §2.1 step 4 applies: below an identity static `*` edge at the root or at a class it raises the position request (ap.md §4.10 item 1), not a mark request |
| every other rule element on a static position | the rows of §4.1, §4.2 and §5.2, with the base and the path of §1.3 | |

A rule position can be deeper than a static field (for example `ClassStatic(C)` with `Field s` and `Field g`): below the
static field the ordinary rules apply, as for an instance field (ap.md §4.10).

---

## 2. Non-call statements

### 2.1 The statement step

A call statement never uses this step. `x = m(...)` is a call (§3). The zero fact uses the order of §4.4. For a fact
`c` that is not the zero fact, on the base `b` at the statement `s`:

1. NO LIVENESS STEP. The step keeps a fact on a local that is dead at `s`, in every run and in both languages (D25).
   The alias analysis is not changed: it keeps its own inputs (§2.5 A1).
2. If `s` does not touch `b`: `c` passes unchanged (`Unchanged`).
3. Apply the operand type filters of `b` (§5.1). A rejected fact is dropped, also on `b` itself.
4. Apply every micro edge of `b` to `c` with `concat` (I2, ap.md §4.2). The result is the union. A touched base keeps
   only what an edge regenerates: that is the kill. STATIC EXCEPTION (the rule is ap.md §4.10 item 1): Run 1 only,
   statement micro edges only: when the edge of `c` is an identity static `*` edge at the root `[]` or at a class
   `[<C>]`, a micro edge whose premise path `p` lies strictly below `c` (the exclusion of `c` admits the rest) gives no
   fact and no mark request; it raises the position request for `p` cut to at most two accessors. Below a static field
   the ordinary rules apply. The other micro edges of the statement apply as usual, so the kill stays. The rows of
   §2.2 and §2.3 name the position request of each static statement. The statement micro edges at a call (the rule
   statement of §4.1, the unresolved callee of §3.7, the `RemoveAllMarks` kill of §1.4) use this step on the bound
   fact or on the added fact: its edge is the caller edge `(i → c)`, and the position request goes to the caller,
   on `i`. The rule statement of an exit (§4.7) uses this step on the fact at the exit, with the edge of that fact.
5. Apply the lhs type filter (§5.1) to the results on the lhs. (On the input it has no effect: the statement kills the
   lhs.)
6. Apply the field limit (ap.md §4.4).

The write rule (I3). The reference form uses the types of ap.md §3.4 and the edge `PathEdge` of ap.md §4.1.
`ExclusionSet.of(a)` makes the Concrete exclusion `{a}`.

```kotlin
/** The micro edge `b.p.* →_E b.p.*`, with the mark `*` on both sides. */
fun keepEdge(b: AccessPathBase, p: List<Accessor>, exclusion: ExclusionSet): PathEdge {
    val side = PathFact(b, p, Tail.STAR, MarkSlot.Star(MarkSet.EMPTY))
    return PathEdge(side, side, exclusion)
}

/** A STRONG write of the path a1..an on the base b: keep every prefix of b except the written accessor. */
fun strongKeep(b: AccessPathBase, path: List<Accessor>): List<PathEdge> =
    path.indices.map { k -> keepEdge(b, path.take(k), ExclusionSet.of(path[k])) }

/** A WEAK write keeps the whole base. A read keeps the whole base and adds no exclusion. */
fun weakKeep(b: AccessPathBase): List<PathEdge> = listOf(keepEdge(b, emptyList(), ExclusionSet.Empty))
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
| `x = C.s` | `S.* → S.*`, `S.<C>.s.* → x.*`. Run 1: on an identity static `*` edge at the root `[]` or at the class `[<C>]`, the read edge raises the position request `[<C>, s]` instead (§2.1 step 4) | {S, x} | x |
| `y.f = x`, y ≠ x | `y.* →_{f} y.*`, `x.* → x.*`, `x.* → y.f.*` | {y, x} | y: static type of y AND declaring class of f; x |
| `y.f = y` | `y.* →_{f} y.*`, `y.* → y.f.*` | {y} | y |
| `y[i] = x` (weak) | `y.* → y.*`, `x.* → x.*`, `x.* → y.[e].*` | {y, x} | y: the array type; x |
| `C.s = x` | `S.* →_{<C>} S.*`, `S.<C>.* →_{s} S.<C>.*`, `x.* → x.*`, `x.* → S.<C>.s.*`. Run 1: on an identity static `*` edge at the root `[]`, the class keep edge raises the position request `[<C>]` instead (§2.1 step 4) | {S, x} | x |
| `x = a op b` | `a.* → a.*`, `a.* → x.*`, `b.* → b.*`, `b.* → x.*` | {x, a, b} | a; b; x |
| `x = new T`, `new T[n]`, `instanceof`, `-a`, `a.length`, phi | none (kill) | {x} | x |
| `return v` | `v.* → v.*`, `v.* → ret.*` | {ret, v} | none |
| `return` (void) | none (kill) | {ret} | none |
| `throw t` | `t.* → t.*`, `t.* → exc.*` | {exc, t} | none |
| any other statement (branch, goto, monitor, catch) | none | {} (all facts pass) | none |

If one base is on both sides (`x = x op b`), the two edges of `x` become the identity `x.* → x.*`. The alias edges of a
write are in §2.5. A read source at `x = C.s` adds the zero base to the touched bases (§4.4).

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
| `x = G` (a global) | `S.* → S.*`, `S.<G>.* → x.*`. Run 1: on an identity static `*` edge at the root path `[]`, the read edge raises the position request `[<G>]` instead (§2.1 step 4) | {S, x} |
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
| `G = v` | `S.* →_{<G>} S.*`, `v.* → v.*`, `v.* → S.<G>.*`. The root keep edge is at the root, so it raises no position request | {S, v} |
| `return v` | `v.* → v.*`, `v.* → ret.*` | {ret, v} |
| `return v0, ..., vn` (n ≥ 1) | for each `i`: `vi.* → vi.*`, `vi.* → ret.#i.*` | {ret, v0..vn} |
| any other statement | none | {} |

### 2.4 Pinned examples

The column "Today" uses today's notation (§0).

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
| A5 | Backward run: the alias target gets the identity edge `c.* → c.*` (§4.9, ap.md §9.2). |
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

Every binding edge has the empty `from` path, the `*` tail and the mark `*` on both sides (I4, I11), so a caller fact
is always strong enough for it. The AP applies it as a micro edge (I4). A local passed twice (`m(a, a)`) gets two
bindings. No binding back has the zero base (I11).

### 3.2 The lhs

The lhs `r` has no binding into the callee. So a fact on `r` before the call is killed (a strong update of `r`). If `r`
is also an argument (`r = m(r)`), its argument binding carries the fact. The lhs gets only what the binding back of
`ret` gives, and the source rules at the call (§4.5).

### 3.3 Statics and the zero fact

* `S.* → S.*` in both directions, with no filter. `S` is touched at every call, in every run, as in the model call
  (ap.md §3.5): the static fact comes back only through the callee summaries. A callee that touches no static gives
  its identity summary. In run 1 it is a normal summary edge, so it is a record in every later run (ap.md §8.7), and
  it gives the static fact back with no special rule at the call.
* The zero fact. No call binding touches the zero base, so the zero fact passes over every call. It is also bound into
  every resolved callee by `zero.* → zero.*` (the zero fact `(zero, [], $, {}, zeroMark)` is below this premise), as
  today. A binding is a `*`-to-`*` edge (I4), so the zero binding is `zero.* → zero.*`. The form
  `zero.$ (zeroMark) → zero.$ (zeroMark)` is not a binding: it is the keep edge of a statement that touches the zero
  base (I11). There is no binding back for the zero fact (I11): the fact that passed over is the same (ap.md §3.5). An
  unresolved call only passes the zero fact over. The sink and source rules of the call read the zero fact through
  the rule statement of the call (§4.1, §4.6).

### 3.4 Exceptions

`throw t` moves `t` into `exc` (§2.2). The exceptional exit makes no summary edge (`producesExceptionalControlFlow`).
The exit rules apply at the exceptional exit too (§4.7): there the rule position `Result` reads `exc`.
The binding back has no edge for `exc`. So no exception flow crosses a call, and a catch block does not read `exc`. This
is today's behaviour (the exception tests of `DataFlowBenchFalseNegativeTest` are disabled). It is outside the model
(ap.md S4, §11.2; gap G1). Go has no exception base.

### 3.5 Constructors (JVM)

At a call to `<init>`, every added fact (the bound fact after the cleaners) also PASSES OVER the call: it keeps its
caller base, and it also enters the callee. This is the ad-hoc rule of today (`isConstructor` in
`JIRMethodCallFlowFunction`). So a constructor call is a weak update of its receiver and its arguments. It is an
expected false-positive source (gap G8, ap.md §11.1). The pass-over result does not take the summary rewriter; it takes
the binding back, the aliases and the field limit (§4.5 step 6).

### 3.6 Virtual calls and several callees

* JVM: the call resolver gives a set of callees, each with a context (`JIRInstanceTypeMethodContext`: the receiver type;
  `JIRArgumentTypeMethodContext`: the type of one argument), and possibly a resolution failure. Go: the resolved
  callees with `EmptyMethodContext`; an empty set is a failure.
* The resolver drops every empty method (I8) from the callees. If every resolution result is an empty method, the call
  is unresolved (§3.7).
* The relevance check, the sinks, the sources and the cleaners run ONCE per caller fact. They use the rules of the
  method that the call statement names, not of the resolved callee.
* The cleaned bound fact enters EVERY resolved callee. The start fact of each callee is filtered by the context type
  (§5.1).
* The caller gets the union of the summary results of all callees. A failure adds the unresolved path (§3.7) to the
  union.

### 3.7 Unresolved callees

A callee is UNRESOLVED if the resolver gives a failure (JVM: the called method, or an override, is outside the analysed
units, `MethodResolutionFailed`; Go: an empty set of callees), or if the call targets a lambda or a closure that is not
yet known (§3.9), or if every resolution result is an empty method (I8: the resolver drops an empty method from the
callees, §3.6). An unresolved callee has a STATEMENT summary (ap.md §4.2: the micro edges of a statement). The AP
applies it to each added fact `a` (the bound fact after the cleaners) at the callee base `P`, in every run, as
statement micro edges (§2.1 step 4), and never restricts it. The fact `a` has the premise set and the layer of its
caller edge `(i → c)`: in run 1 the static exception of §2.1 step 4 tests that caller edge, and a position request goes
to the caller, on `i`:

1. Default identity: `P.* → P.*`. The fact passes over the call. The summary rewriter (§5.2) applies to it (D23).
2. Pass rules of the method that the call names (§4.1). JVM: with conditions; Go: unconditional. JVM type filters by
   the declared signature (§5.1).
3. JVM DEFAULT GETTER RULES (the analysis option `defaultGetModel`; it is on unless the option `disableDefaultGetModel`
   is set; today `JIRMethodGetDefault`): for an instance method whose name starts with `get` and whose class is
   outside the analysed units (not a class of the project), the unconditional pass rule
   `CopyAllMarks(This → Result)`, and, if the return type can be an array (an array type or `Object`), also
   `CopyAllMarks(This → Result.[e])`. They join the pass rules (union).
4. The summary rewriter on the pass results, the binding back, the aliases (§3.8), the field limit.

The lhs gets only what a pass rule writes to `Result`. The external method tracker records the call (no effect on the
facts).

### 3.8 Aliases on call results

| Rule | Text |
|---|---|
| AC1 | JVM: for each caller local `x` that a binding back writes (`r`, `o`, `ai`), the alias paths `(b, q)` of `x` that hold BOTH before and after the call (`forEachAliasAfterCallStatement`; constant bases skipped). Go: the heap aliases at the statement (`forEachHeapAliasAtStatement`). |
| AC2 | For each alias: the binding-back edge `P.* → b.q.*` beside `P.* → x.*`. The alias base is a gen-only target (weak, gap G7). |
| AC3 | The alias edges apply to: every summary result that is not an identity result (AC4), so every demand-layer result and every zero-premise summary result; the source results at the call; the end facts of a sink (§4.1); the pass-rule results. |
| AC4 | An IDENTITY result is a summary result in the NORMAL layer that is equal to the start fact of its premise (ap.md §6.5). It is not copied to the aliases (as today): the alias already holds the same facts, because the writes keep the aliases (§2.5). A demand-layer result is never an identity result: it always goes to the aliases, also when it is equal to its start fact (a demand start fact can be coarser than the premise, so the alias does not hold it). |
| AC5 | AC3 and AC4 are an exception to I2: they select the results to which the alias edges apply. The selection leaves out only the normal-layer identity results, which the alias base already holds. The backward run applies the reversed alias edges to every requirement (§4.9). |

### 3.9 Lambdas and closures

* JVM: the prescan (ap.md §1) runs the current core (ap.md §7.6) and gives the lambda classes that reach each call to a
  functional interface method. The new analysis reads this result before run 1 and has no lambda event. When the call
  resolver gives a `Lambda` result for a call (`JIRCallResolver.MethodResolutionResult.Lambda`), the result is the
  lambda methods that the prescan knows for that call, and nothing else: it has no unresolved path. If the prescan knows
  no lambda for the call, the result is a resolution failure: the unresolved path (§3.7). Today a `Lambda` result
  always adds a resolution failure beside the lambda methods (`JIRMethodCallResolver.kt:184-209`; deviation D19, §6).
  Only this failure goes. A resolution failure that the resolver gives beside the `Lambda` result for its own reason
  (no known override, or a base method outside the analysed units, `JIRCallResolver.kt:160-163, 174-178`) stays: it
  adds the unresolved path. So D19 changes the result only for a functional interface of the project; a call through
  a JDK functional interface (for example `java.util.function.Function.apply`) keeps the unresolved path.
* Go: a call through a function value is DYNAMIC. The value binds to `this` (§3.1). `makeClosure` writes the free
  variables to `x.fv_i` (§2.3), and the closure body reads `this.fv_i`. If the resolver gives no callee, the call takes
  the unresolved path, and the closure tracker resolves it later from the type info of the prescan.
* Go `go` and `defer`: the interpreter handles them as calls at their statement, with no result.

---

## 4. Rules and their order

### 4.1 Rule kinds

| Kind | JVM | Go | Where | AP form |
|---|---|---|---|---|
| source at a call | `TaintMethodSource` | `Source` | call statement (the rule statement, below) | unconditional: `zero.$ (zeroMark) → P.$ (T)` (`AssignMark`) or `zero.$ (zeroMark) → P.[any] (T)` (`AssignMarkOnAnyAccessor`, Go `AnyAccessor`), premise mark `zeroMark`; conditional: `Q.t' (T') → P.t (T)`, with `t' = $` for `ContainsMark(Q, T')` and `t' = [any]` for `ContainsMarkOnAnyField(Q, T')` (§4.2), and the target tail `t` (`$` or `[any]`) as above; a conjunction over several facts: §5.3 |
| entry-point source | `TaintEntryPointSource` | none | method start, zero | `zero.$ (zeroMark) → P.$ (T)`; the condition must be true |
| exit source | `TaintMethodExitSource` | none | every exit (normal and exceptional, §4.7) | as a source at a call, in the coordinates of the method |
| read source | `TaintStaticFieldSource` at `x = C.s` | `FieldReadSource` at `x = y.f`, `GlobalReadSource` at `x = G` | the read statement, zero | `zero.$ (zeroMark) → x.$ (T)`; the condition must be true (§4.4) |
| sink at a call | `TaintMethodSink` | `Sink` | call statement | the sink check (ap.md §4.9); its end facts (below) |
| entry sink | `TaintMethodEntrySink` | none | method start, zero | unconditional only (as today); its end facts |
| exit sink | `TaintMethodExitSink` | none | every exit (normal and exceptional, §4.7) | the sink check (ap.md §4.9); its end facts |
| pass rule | `CopyAllMarks`, `CopyMark` | `CopyData`, `CopyTaintMark` | unresolved call | `CopyAllMarks(P → Q)`: `b.* → b.*` (`b` = the base of `P`), `P.* → Q.*`; `CopyMark(T, P → Q)`: `b.* → b.*`, `P.$ (T) → Q.$ (T)`; with `AnyField` positions: the next table |
| cleaner | `RemoveMark(T, P, reach)`, `RemoveAllMarks(P)` | `RemoveMark`, `RemoveAllMarks` | call statement | `clean` (§5.2) |
| summary rewriter | user-defined source rules whose condition is not statically false, and unconditional user-defined cleaner rules (§5.2) | the same | call statement | `clean(P, exact, T)` on the summary results (§5.2) |

A rule position on `S` follows §1.4 first.

Pass rules with an `AnyField` position (`PositionWithAccess(P, AnyField)`, Go `AnyAccessor`). The field that the rule
skips is not known, so the result is uncorrelated: the target tail is `[any]`. Under W6 every result of such an edge is
in the demand layer (ap.md §2.3), as for an `[any]`-target source.

| Pass rule | AP form (with `b.* → b.*`, `b` = the base of `P`) |
|---|---|
| `CopyAllMarks(P.AnyField → Q)`, `CopyAllMarks(P.AnyField → Q.AnyField)` | `P.[any] → Q.[any]` |
| `CopyAllMarks(P → Q.AnyField)` | `P.* → Q.[any]` |
| `CopyMark(T, P.AnyField → Q)` | `P.[any] (T) → Q.$ (T)` |
| `CopyMark(T, P → Q.AnyField)` | `P.$ (T) → Q.[any] (T)` |
| `CopyMark(T, P.AnyField → Q.AnyField)` | `P.[any] (T) → Q.[any] (T)` |

THE RULE STATEMENT OF A CALL. The source rules of a call statement form a CALL STAGE of their own, beside the bindings
(the sources stage, analyzer-core.md §4.5). A call stage gives only the results of its edges: a fact on a base that no
edge of the stage reads gives no result (it does not pass through the stage). The rule statement reads the bound,
uncleaned facts (callee coordinates) and the zero fact. It touches the zero base and the base of every position that a
source literal reads. Its edges are the keep edge `zero.$ (zeroMark) → zero.$ (zeroMark)` (I11) and the source edges
of the table above. It has no other keep edge: the bound facts go on through the call, not through the rule statement,
so its only results are the zero fact and the source targets. The source targets go to the caller through the binding
back and the aliases (§3.8 AC3), with the field limit, and join the results of the call (union). The zero fact has no
binding back (§3.3): the zero fact of the caller is the one that passes over the call. The sink patterns of the call
read the same facts (§4.5 step 3, §4.6). The call bindings never touch the zero base (§3.3). The source edges are
statement micro edges for §2.1 step 4: in run 1 the static exception applies to a source edge whose premise is on `S`.
The bound fact has the premise set and the layer of its caller edge `(i → c)`, so the test reads that caller edge, and
the position request goes to the caller, on `i`.

END FACTS. A sink rule can have end-fact actions (`trackFactsReachAnalysisEnd`: a list of `AssignMark(T, P)`). When the
sink triggers, the interpreter applies these actions as the targets of a source: each action gives the zero-to-fact edge
`Zero → (sink statement, P.$ (T))`, in the layer of the sink edge (or of the combination, below). At a call it goes to
the caller through the binding
back and the aliases (AC3); at a method start or at the exit it joins the facts there (§4.3, §4.7). The field limit
applies to it in each case (I10).

THE END-FACT STAGE takes no input fact. When a sink triggers (a plain sink on a fact, or a conjunctive sink on the
combination that an item completes, §5.3), the stage applies its edges to the zero fact, in the layer of the sink edge
or of the completed combination (ap.md §2.2, §4.9). At a call this is the end-facts stage of the call plan
(analyzer-core.md §4.5). At a method start and at an exit the same rule gives the end facts that join the facts there.

The interpreter gives the end facts of the vulnerability to the vulnerability store: the sink witness keeps them
(ap.md §8.10; today the end-fact requirement of `TaintSinkTracker`). Today the trace resolution reports such a
vulnerability only if one end fact reaches the end of the analysis (`VulnerabilityChecker`). The trace resolution is
outside this specification (ap.md §8.10 THE TRACES): no part of the analysis checks whether an end fact reaches the
end of the analysis. This is a KNOWN GAP for now: every confirmed vulnerability of a sink rule with end-fact actions is
reported (ap.md §11.1).

### 4.2 Conditions

* The interpreter rewrites each condition to the negation normal form, per call statement (per method for the entry
  and exit rules).
* Non-mark atoms (`IsConstant`, `IsNull`, `ConstantEq/Lt/Gt/Matches`, `TypeMatches`, `IsStaticField`, ...) are
  evaluated statically per statement. The constant atoms use the alias information. A false condition removes the rule.
* A mark atom is a LITERAL. For a sink, `ContainsMark(P, T)` is the pattern `(P, $, T)` and
  `ContainsMarkOnAnyField(P, T)` is the pattern `(P, [any], T)`. For a source, a literal is the premise
  of a micro edge: `ContainsMark(Q, T')` gives the premise `Q.$ (T')`, and `ContainsMarkOnAnyField(Q, T')` gives the
  premise `Q.[any] (T')`. An `[any]` premise covers every fact at or below `Q`; a fact above `Q` also applies, with a
  demand-layer result (I2, ap.md §4.1). Both premises have a concrete mark, so S8 and I7 hold. A literal of a
  conjunction has the same two forms (ap.md §4.6).
* ARRAY ELEMENTS OF A CALL SINK (JVM, as today). For a sink at a call, a positive literal on an argument position
  `arg(i)·ρ` whose argument may be an array is the disjunction of the patterns `(arg(i), ρ, t, T)` and
  `(arg(i), [e]·ρ, t, T)`. The argument may be an array if `typeMayBeArray` (§5.1) holds for the static type of the
  argument value at the call (today `JIRFactTypeChecker.callArgumentMayBeArray` and `arrayElementConditionReaders`,
  `JIRMethodCallTaintUtil.kt:186-203`). `Or` gives one alternative per pattern, so a conjunctive sink gets one
  alternative per choice. This holds only for the argument positions of a sink at a call: not for the receiver, not for
  `Result`, not for the entry and exit sinks. The sink seeds of the backward run follow the alternatives (§4.9).
* For a source or a sink, an over-approximation makes the rule fire MORE: a negated literal counts as true. `Or` gives
  one alternative per literal. A conjunction of literals that different facts satisfy (a positive literal on another
  position): a source makes an ND edge (§5.3); a sink is a CONJUNCTIVE SINK (ap.md
  §4.9, §5.3). The interpreter sets no layer. The layer of a result belongs to the propagation edge, and only
  the AP operations change it (ap.md §2.2): a fact that only overlaps a literal gives a demand-layer result (ap.md
  §4.1, §4.6). A negated literal that counts as true is the expected over-approximation of a path-insensitive engine,
  as the conjunction is (the reference semantics of rules, ap.md §3.5; ap.md §4.6, §11.1).
* THE SINK ALTERNATIVES. The interpreter numbers the alternatives of one sink rule at one place (each one disjunct of
  the condition with one choice of the array patterns) in a fixed order. The number is the SINK ALTERNATIVE of ap.md
  §1. It is the same in every run and in every context (I5). The vulnerability store keeps the witnesses of two
  alternatives apart, and the conjunction store keeps their literals apart (ap.md §8.9, §8.10).
* A PASS RULE (`CopyAllMarks`, `CopyMark`) has no mark-dependent condition: after the static evaluation of the non-mark
  atoms, its condition has no mark literal. The copied mark of `CopyMark(T, P → Q)` is not a condition: it is the
  premise `P.t (T)` of the pass edge (§4.1). A pass rule is a handcrafted summary of an unresolved callee, and a mark
  literal has no exact form for it: `CopyAllMarks` has the target mark `*`, so a concrete premise mark would make an
  edge that is not mark-reversible (I11 (b)), and an ND edge needs a concrete target mark (ap.md W7). The interpreter
  reports a pass rule with a mark literal as a rule error and applies it without its mark literals (it fires more; this
  is sound, but not precise: gap G11). So a pass rule never makes an ND edge.
* For a CLEANER the safe direction is the opposite: a cleaner that fires removes real taint. So the interpreter applies
  only the UNCONDITIONAL cleaners:
  * a non-mark atom is decided statically: a false atom removes the rule, a true atom drops out of the condition;
  * if no mark literal is left, the cleaner is unconditional, and it applies (§5.2);
  * if a mark literal is left (positive or negated, on any position, `ContainsMark` or `ContainsMarkOnAnyField`), the
    cleaner does not act and raises no request: the propagation edge passes unchanged with its layer.

  A cleaner that does not act only keeps more taint, so this is sound. It is the expected over-approximation of a
  fact-local, path-insensitive engine, as the conjunction is (ap.md §4.6). Cleaning on a condition that the fact does
  not decide is unsound. Today the condition is evaluated on the fact (`TaintFactAwareConditionEvaluator`); this is
  deviation D20 (§6).
  Examples: `RemoveMark(T, P)` with no condition is `(P, exact, T)`. `RemoveMark(T, P) if ContainsMark(P, T)` and
  `RemoveMark(T, Argument(0)) if Not(ContainsMark(Argument(1), RAW))` never clean.
  The summary rewriter (§5.2) is not a cleaner placement, and D20 does not govern it. It selects a user-defined
  cleaner rule only if the rule is unconditional, so a conditional user-defined cleaner does not act through it either.
* Go pass rules have no condition.

### 4.3 Entry order (method start, as today)

| Language | Fact | Order |
|---|---|---|
| JVM | zero | 1. the zero fact; 2. entry sinks with a true condition (vulnerability, end facts); 3. entry-point sources with a true condition. The marks of step 3 are the ENTRY MARKS (§4.7). The field limit applies to the end facts of step 2 and to the results of step 3 (ap.md §4.4). |
| JVM | initial fact | 1. the start fact (ap.md §6.5); 2. the filter by the context type (§5.1). |
| Go | zero | the zero fact only (no entry rules). |
| Go | initial fact | the start fact, with no filter. |

### 4.4 Statement order (non-call)

| Fact | Order |
|---|---|
| zero | 1. `zero → zero`; 2. read sources with a true condition (JVM `x = C.s`; Go `x = y.f`, `x = G`); 3. JVM: exit sources with a true condition, at each exit (§4.7). A statement with a read source touches the zero base: its summary has the keep edge `zero.$ (zeroMark) → zero.$ (zeroMark)` and the source edge (I11). Every other non-call statement does not touch the zero base, so the zero fact passes unchanged. The type info facts (lambda allocations, closures) exist only in the prescan. |
| other | §2.1, steps 1 to 6. |

### 4.5 Call order (a fact)

This order is for a caller fact that is not the zero fact. The zero fact uses §4.6. For the caller edge
`(i, layer) → c` at the call statement `s`, in JVM and in Go:

1. RELEVANCE. If `s` does not touch `c.base`, `c` passes over the call. Stop.
2. BINDING IN. Apply the binding edges into the callee, with the caller-side type filters (§3.1). The result is the
   bound facts, one per callee position.
3. SINKS. Check the sink rules on the bound facts: the PRE-CALL, UNCLEANED fact. Requests: §5.4. End facts: §4.1;
   they go to the caller as the source results of step 4.
4. SOURCES. Apply the rule statement of the call (§4.1) to the bound facts, as statement micro edges (§2.1 step 4,
   with the static exception on the caller edge); evaluate the ND conjunctions (§5.3). The results go to the caller
   through the binding back and the aliases (no rewriter), then the field limit.
5. PER CALLEE POSITION, for each bound fact `a`:
   1. CLEANERS: `clean` for each cleaner rule, chained in the rule order (§4.8, §5.2). A `RemoveAllMarks` rule on a
      position of `S` applies at its place in this order as the kill of §1.4, not as a cleaner: a statement summary
      that touches only `S` (§2.1 steps 2 to 4). A bound fact on another base passes the kill unchanged; a bound fact
      on `S` keeps only what a keep edge gives (with the static exception on the caller edge). The whole-base cleaner
      of `AnyClassStatic` is a cleaner (§1.4, §5.2);
   2. RESOLVED callees: the callee processing of ap.md §5.3 for each callee, with the cleaned fact as the added fact
      (events E1 and E2: add, emit, check the standing requests, subscribe, apply the summaries that it satisfies and
      the records that cover it); each new initial fact starts with the context filter (§4.3); JVM constructor: the
      cleaned fact also passes over the call (§3.5);
   3. UNRESOLVED callee: the default identity and the pass rules (§3.7), as statement micro edges on the added fact
      (§2.1 step 4, with the static exception on the caller edge).
6. RETURN. For every result of step 5 (a summary result, an unresolved result): the summary rewriter in callee
   coordinates (§5.2), then the binding back with its filters, then the aliases (§3.8), then the field limit. A
   constructor pass-over result skips the rewriter.

The order has three effects: a sink sees the fact before the cleaners; the pass rules see the cleaned fact; the summary
rewriter acts only on the results of the call.

APPLICATION MODES. A CALL STAGE gives only the results of its edges: the binding in, the rule statement of the call
(§4.1), the unresolved callee (§3.7), the constructor pass-over (§3.5), the binding back and the aliases (§3.8). A
bound fact on a base that no edge of a stage reads gives no result in that stage. The `RemoveAllMarks` kill on `S` is
a statement summary that touches only `S`: a fact on another base passes it unchanged (§2.1 step 2). The end-fact stage
takes no input fact (§4.1).

### 4.6 Call order (the zero fact)

| Language | Today | New |
|---|---|---|
| JVM | unconditional sinks, unconditional sources, call-to-return zero, call-to-start zero | the same |
| Go | call-to-return zero, call-to-start zero, sinks, sources (one set of outputs) | as JVM; the outputs of one step are a set, so the result does not change |

The zero fact evaluates the sink rules and the rule statement of the call (§4.1) with no fact. An unconditional rule
fires (also a rule whose mark literals are all negated, §4.2). The stored assumptions of a conjunctive micro edge or
of a sink alternative at the statement can complete a conjunction (§5.3, as today). The source results go to the
caller through the binding back and the aliases (AC3), then the field limit. Then the zero fact passes over the call
and enters every resolved callee (§3.3). The zero fact takes no cleaner, no pass rule and no rewriter.

### 4.7 Exit order

JVM, at `JMethodExitNormalInst` (after every `return`) and at `JMethodExitExceptionalInst` (after every `throw` and
every exception that leaves the method), for each fact `f`. At the exceptional exit the rule position `Result` reads
the exception base `exc` (the thrown value), as today (`JIRMethodSequentFlowFunction.kt:120-126`). Steps 1 and 2 apply
at both exits; steps 3 to 5 apply only at the normal exit, because only the normal exit makes a summary edge (§3.4).
The order of the steps is as today. The exit sources of an exit form the RULE STATEMENT OF THE EXIT: its edges are
statement micro edges for §2.1 step 4, so in run 1 a conditional exit source whose premise is on `S` takes the static
exception on the edge of `f` (§1.4).

THE UNCONDITIONAL EXIT RULES (the unconditional exit sources and the unconditional exit sinks) fire on the zero fact at
BOTH exits (§4.4; D22). This is a deviation from today (D26): today they fire only at the normal exit
(`JIRMethodSequentFlowFunction.kt:228-233`). So an unconditional exit sink can report at both exits of one method;
this double report is accepted.

1. The worklist is `f` and the results of the exit sources whose condition `f` satisfies, after the field limit (ap.md
   §4.4). The results keep the premise of `f`.
2. For each item: check the exit sinks. Their end facts (§4.1), after the field limit, join the worklist. A literal of
   a conjunctive exit sink stores its input in the conjunction store (§5.3).
3. THE GLOBAL-STATE RULE: if a mark literal (`ContainsMark`, `ContainsMarkOnAnyField`) of an exit sink holds on a part
   of an item on `S`, drop that part from the summary edge. This applies to a plain and to a conjunctive exit sink. The
   rest of the item stays. The dropped part is not lost for the sink: for a conjunctive exit sink, step 2 stored it as
   the input of that literal. So it stays an assumption for the next evaluation attempts of the sink, and a later item
   can complete the combination with it. Today the `ClassStatic` facts that the exit sink condition read are dropped
   (`JIRMethodSequentFlowFunction.kt:186-188`). The rule generator keeps the state of a rule as a mark on a synthetic
   class position (§1.4); the exit sink consumes it. This is gap G2.
4. For a zero-premise fact on `this` or `arg(i)`: remove the entry marks (§4.3), so that an entry-point source does not
   leak into the callers (gap G2).
5. Emit the summary edge. Not at the exceptional exit (its facts end there); not for a `local` base.

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

The backward run applies the AP rules of ap.md §9.2 to the reversed program. This section gives the interpreter part.
The interpreter gives only the forward forms; the analyzer core makes the backward forms by a reversal: the reversed
statement summary, the reversed entry and exit rules, and the reversed call plan (analyzer-core.md §4.5, §4.9). The
call order below is the reversal of the forward call order of §4.5, stage by stage; the reversal drops every type
filter and every forward-only guard (the alias selection AC3, AC4; the sink trigger of the end facts).
The backward run is a restricted run (ap.md §6.1). Every fact is concrete and there is no request, because the seeds
have concrete marks (ap.md §9.2; Lean `BExact.DB_concrete`, `DB_no_request`).
The implementation asserts both (§5.4).

STATEMENTS. The reversed statement summary of a non-call statement (ap.md §9.1, §9.2; Lean `Reverse.Stmt.rev`):

* the touched bases: the forward touched bases and every target base of a forward micro edge;
* the micro edges: the reversal of every forward micro edge (ap.md §9.1), and the identity edge `b.* → b.*` for every
  target base `b` that the forward statement does not touch (a gen-only alias target, A5);
* a conjunctive edge `L1 ∧ … ∧ Lk → z` reverses into the k plain edges `rev(Lj, z)` (an OR of the requirements,
  ap.md §9.2). The backward run makes no ND edge;
* no type filter, no mark policy, no request (and no liveness step, as in the forward run, §2.1 step 1);
* the zero fact: a forward statement that touches the zero base keeps it (I11), so its reversal keeps it too.

RULE ROLES (ap.md §9.2 gives the AP rules):

| Forward rule | Backward role |
|---|---|
| source (at a call, entry-point, exit, read), end-fact action | its reversed edge: a requirement on its target continues to the zero fact (unconditional source: the zero demand of ap.md §9.2) or to its read position (conditional source). When the reversed edge of an unconditional source applies, the backward run records a SOURCE HIT: a source seed of the next forward run (ap.md §8.11, §9.2). The backward run has no sink check, so a forward source is not a backward sink (ap.md §9.2). |
| sink (at a call, entry, exit) of a vulnerability that the previous forward run reported | a SEED (below). A sink with several positive literals seeds one requirement per literal. A sink with no positive literal seeds no requirement: the zero demand covers its witness. |
| other sinks | none |
| pass rule, default getter rule | its reversed edges (from and to swapped) |
| cleaner (an unconditional cleaner, §4.2, also the whole-base cleaner of `AnyClassStatic`, §1.4), summary rewriter | the same cleaner: a cleaner is its own reversal (ap.md §9.2) |
| the `RemoveAllMarks` kill on `S` (§1.4) | the same keep edges: the reversal of a keep edge is the same edge (ap.md §9.2); at the place of the reversed cleaners (step 6 below) |
| the global-state rule and the removal of the entry marks (G2) | none |
| type filter, mark policy | none |

CALL ORDER (the mirror of §4.5). For a requirement `c` after the call statement `s`:

1. RELEVANCE. The reversed call touches the forward touched bases of `s` and the alias bases of §3.8. If it does not
   touch `c.base`, `c` passes over the call.
2. REVERSED BINDING BACK. The converse of each forward binding back and of each call alias edge (`b.q.* → P.*`, §3.8),
   into callee coordinates at the forward exit. An alias base also keeps the requirement (`b.* → b.*`, A5). No filter.
3. REVERSED SOURCES. The reversed source edges of the rule statement of `s` (§4.1) and the reversed end-fact edges, on
   the result of step 2. A requirement that reaches an unconditional source continues to the zero fact. A conditional
   source gives a requirement at its read position; it enters at step 7.
4. REVERSED REWRITER. The summary rewriter (§5.2) on the result of step 2.
5. CALLEES, on the result of step 4:
   1. RESOLVED callees: the requirement enters each callee at its forward exit (the callee processing of ap.md §5.3 in
      the backward orientation); the backward summaries of the callee bring it to the forward entry of the callee;
   2. UNRESOLVED callee: the reversal of the statement summary of §3.7 (the default identity, the reversed pass rules
      and default getter rules);
   3. JVM CONSTRUCTOR (§3.5): a requirement on the receiver or on an argument also goes from step 2 directly to
      step 6 (the reversal of the pass-over; it skips the rewriter and the callee).
6. REVERSED CLEANERS. The cleaners of `s` on the requirement at the callee start (callee coordinates): the
   unconditional cleaners (§4.2), and the keep edges of a
   `RemoveAllMarks` kill on `S` (§1.4), in the rule order.
7. SEEDS AND READ POSITIONS. Here the seeds of the sinks of `s` and the requirements of step 3 at the read positions
   enter, at the bound positions.
8. REVERSED BINDING IN. The converse of each forward binding into the callee, to the caller before the call. No filter.
9. The field limit of the backward run on every result (ap.md §4.4).

THE ZERO FACT. The backward run starts at each root with the zero fact. The zero fact enters a method at every forward
exit node (the normal exit and the exceptional exit, ap.md S4). It passes over every call. It also enters every
resolved callee DIRECTLY: it is an initial fact of the callee at the forward exit of the callee, with no emission and
no demand pattern (ap.md §9.2; Lean `Backward.DB`, rule `zin`). This entry is not a binding and not the reversal of a
binding. Each caller applies a zero-premise backward summary of the callee to its own zero fact at the call site (the
balanced return; ap.md §9.2). The implementation wires a node that reaches no exit node to an exit node (I11 (e)), so
the zero fact reaches every node on a CFG path from the method entry (the backward reference branch does this with
`JIRBackwardExitWiringGraph`, which wires the node to the exceptional exit).

SEEDS. The seed of a reported vulnerability is the zero-to-fact edge `Zero → (sink statement, requirement)` where the
zero fact reaches the sink statement (ap.md §9.2). The requirement is the sink pattern, cut by the field limit of the
backward run (ap.md §4.4; Lean `Backward.DB`, rule `seed`). At a sink call the seed enters AFTER the reversed cleaners
of that call (step 7), at the bound positions, and goes on through the reversed binding in. This mirrors §4.5, where
the sink check (step 3) comes before the cleaners (step 5.1). So a method that is both a sink and a cleaner of the same
mark does not kill its own seed. The seed of an exit sink enters at the forward exit (normal or exceptional) where the sink is (§4.7). There it takes
the reversed exit sources of that exit, as the start fact does: forward, the exit sources (§4.7 step 1) come before the
exit sinks (step 2), so an exit sink can read the result of an exit source. A source hit there is recorded (§4.9 RULE
ROLES). An entry sink is
unconditional (§4.1), so it seeds no requirement.

---

## 5. Where the primitives apply

### 5.1 Type filter: `filter(base, may)`

The JVM predicate for the static type `t` is today's `JIRFactTypeChecker`, written as a prefix-closed predicate on the
path. The reference form below uses these helpers:

| Helper | Value |
|---|---|
| `typeMayHaveSubtypeOf(t, c)` | true if a value of the static type `t` can be an instance of the class `c` (today's test in `JIRFactTypeChecker`): for a class type, one of the two types is assignable to the other; for an interface, an implementation can be a subtype of `c`; for a type variable, every bound passes |
| `typeMayBeArray(t)` | true if `t` is an array type, `Object`, or a type variable or wildcard whose bounds allow an array |
| `t.elementTypeOrNull()` | the element type of an array type `t`, else `null` |
| `t.unboxIfNeeded()` | the primitive type of a boxed type `t` (for example `int` for `Integer`), else `t` |
| `a.declaringClass` | the class that declares the field accessor `a`, `null` if it is not known |

The filters also make the validity condition I13 (ap.md S13) true: the exactness and confirmation theorems read only
the locations that every filter accepts, and this placement owns that condition.

```kotlin
/** may(t, p): a path p below a value of static type t may exist. Prefix-closed: may(t, p ++ q) ⇒ may(t, p). */
fun may(t: JIRType?, p: List<Accessor>): Boolean {
    if (t == null || p.isEmpty()) return true
    return when (val a = p.first()) {
        is FieldAccessor -> t is JIRRefType &&
            (a.declaringClass == null || typeMayHaveSubtypeOf(t, a.declaringClass))   // deeper accessors: not checked
        ElementAccessor -> t is JIRRefType && typeMayBeArray(t) &&
            (t.elementTypeOrNull()?.let { may(it, p.drop(1)) } ?: true)
        else -> true                                                                     // <C> (ap.md W5: no other accessor)
    }
}

/** The mark policy (not a may-predicate): it drops a concrete mark directly on a value of a primitive or boxed type,
 *  unless the mark is primitive-tracking. It reads the type at the root (`t`) and below each `[e]` (the element type),
 *  as today (`JIRFactTypeChecker` gives `FilterNext` with the element type at `[e]`). Below a field accessor it reads
 *  no type. Types of ap.md §3.4. */
fun markPolicyKeeps(t: JIRType?, f: PathFact): Boolean {
    val m = f.mark
    if (m !is MarkSlot.Concrete) return true
    var type: JIRType = t ?: return true
    for (a in f.path) {
        if (a != ElementAccessor) return true                  // below a field or a class: no type is read
        type = type.elementTypeOrNull() ?: return true         // the element type is not known
    }
    return type.unboxIfNeeded() !is JIRPrimitiveType || isPrimitiveTracking(m.mark)
}

/** A PRIMITIVE-TRACKING mark is a mark of a rule with the option `primitive-tracking: true`. Today the rule loader
 *  adds the suffix `%%primitive%%` to the name of each such mark (`PrimitiveTaintExt`). */
fun isPrimitiveTracking(mark: TaintMark): Boolean = mark.name.endsWith("%%primitive%%")
```

Rules:

* The filter tests only the concrete path: a fact passes if `may(t, f.path)`. The `*` and `[any]` tails are always
  kept; the filter never changes a tail. The analysis does not store a filter in a fact or an edge, and it does not
  propagate it (ap.md §4.8). So a `*` or `[any]` fact keeps the locations below its path that `t` cannot have: an
  expected false-positive source (ap.md §11.1).
* Policy cases are outside ap.md S5 (they can drop a real flow), as today: the mark policy above; `[e]` on a class type
  other than `Object` (for example `Cloneable`, `Serializable`). The mark policy is not a
  type filter: it reads the mark, not only the path, and the model has no mark filter. It is gap G6.
* THE APPLICATION POINT OF THE MARK POLICY: at every point of the table below where the analyzer applies a type filter
  to a base with the static type `t`, it also applies `markPolicyKeeps(t, ·)` to the same facts, after the filter (as
  today: the policy is part of `JIRFactTypeChecker`). Go and the backward run apply no mark policy.
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
(ap.md §4.7). The interpreter maps the rule actions as follows. The base is in callee coordinates (§1.3). A cleaner on
a static position follows §1.4 first.

| Rule action | Cleaner | Note |
|---|---|---|
| `RemoveMark(T, P, Exact)`, P with no `AnyField` | `(P, exact, T)` | |
| `RemoveMark(T, P.AnyField, Exact)` | `(P, below, T)` | today: `cleanAnyFieldMark(keepStart = true)` |
| `RemoveMark(T, P, ExactAndAnyField)` | `(P, atAndBelow, T)` | the meaning of the rule (D9) |
| `RemoveMark(T, P.AnyField, ExactAndAnyField)` | `(P, below, T)` | every location at or below a field of `P` is strictly below `P` |
| `RemoveAllMarks(P)` | `(P, atAndBelow, all)` | today: the subtree at P goes |
| `RemoveAllMarks(P.AnyField)` | `(P, below, all)` | today: only an `[any]` child goes (D10) |
| `RemoveAllMarks(AnyClassStatic)` (JVM) | `(S, atAndBelow, all)`, the empty path: the whole-base cleaner | every fact on `S` goes; the only all-marks cleaner on `S` (§1.4, I12 (e)); the Spring dispatcher (D27) |
| Go `RemoveMark(T, P)`, `RemoveAllMarks(P)` | as the JVM `Exact` rows | P with `AnyAccessor` maps to `below` |
| JVM position of type `String` | also `(P.<string-bytes>, same reach, same mark)` | as today |

The non-mark atoms of a cleaner condition are evaluated statically (§4.2). Only an unconditional cleaner acts. A
cleaner with a mark literal in its condition does not act and raises no request.

| Point | Facts | Rules | Today | New |
|---|---|---|---|---|
| call, before the callee processing (§4.5 step 5.1) | each bound fact | every cleaner rule of the method that the call names | JVM yes; Go no | JVM and Go (D7) |
| call, unresolved callee | the same cleaned fact feeds the default identity and the pass rules | the same | JVM yes (the step comes before the resolution); Go no | JVM and Go (D7) |
| call, summary rewriter | the summary results and the unresolved results, in callee coordinates, before the binding back | the user-defined source rules and the unconditional user-defined cleaner rules of the call (below) | JVM, Go; also the conditional user-defined cleaner rules | the same, without the conditional cleaner rules (D23); it is an interpreter feature |
| backward run | the requirement after the reversed binding back (the rewriter) and at the callee start (the cleaners) | unconditional cleaners (§4.2); the rewriter | — | §4.9 |

USER-DEFINED RULE. A rule is user-defined if it comes from the rule set of the user and not from the library
configuration (today: its `info` implements `UserDefinedRuleInfo`, JVM, or `GoUserDefinedRuleInfo`, Go; for example a
rule that the Semgrep rule loader makes). It names a set of RELEVANT MARKS (`relevantTaintMarks`).

THE SUMMARY REWRITER acts at a call to a method that user-defined rules cover. Its purpose is RULE-GUIDED FLOW: the
rule overrides the real data flow of the callee for its marks, so the callee can neither add nor keep these marks at
the rule positions. RULE SELECTION (the non-mark atoms are evaluated statically, §4.2):

* every user-defined SOURCE rule of the call whose condition is not statically false;
* every user-defined CLEANER rule of the call whose condition is statically true (an unconditional cleaner).

For each selected rule, each relevant mark `T` of the rule and each action position `P` of the rule (a source: the
positions of its `AssignMark` actions; a cleaner: the positions of its `RemoveMark` actions), the rewriter applies
`clean(P, exact, T)`, chained (§4.8). The rewriter is an override by design, not a cleaner placement: D20 does not
govern it. A conditional user-defined cleaner does not act through the rewriter, as it does not act at the call (§4.2,
D20). The rewriter applies to every summary result and to every unresolved result, also to a zero-premise summary
result and to the default identity (D23). A summary result is a caller edge, so a request of the rewriter goes to the
CALLER premise (§5.4). A cleaner on `Result` acts only through the rewriter (open question Q1).

### 5.3 ND conjunction

* The interpreter evaluates the conjunctive SOURCE rules at step 4 of the call order (§4.5): on every bound fact
  before the cleaners, and on the zero fact (§4.6). A pass rule makes no conjunction (§4.2).
* An edge whose premise set has two or more members is an ND edge and a TAINT edge (ap.md §4.6, §7.2): no member is
  the zero fact, every member has a concrete mark, and the conclusion has a concrete mark.
* Every literal names its mark, so it has a concrete mark (ap.md S9). Its tail is `$` (`ContainsMark`) or `[any]`
  (`ContainsMarkOnAnyField`) (§4.2). ap.md §4.6 sets the layer of the result: normal if every input is normal and
  covered by its literal. A normal result is exact against the path-insensitive support semantics, under ap.md S7,
  S9, S10 and S13 (ap.md §4.6; `NDExact.nd_edge_exact`, the valid form `nd_edge_exact_valid`). The target of a
  conjunctive micro edge has a concrete mark and no `*` tail (ap.md S10, W7), and it is not on the zero base (I11 (d)).
* A fact that overlaps a literal and passes its mark gate (ap.md §4.6) is an assumption for (conjunctive micro edge
  or sink alternative, statement, literal index), as today. The key names one alternative of the condition (§4.2), so
  the literals of two alternatives of one rule never combine. The interpreter stores the assumption in the conjunction
  store (ap.md §8.9). The last fact that arrives sees all earlier ones, so the result does not depend on the order.
* The result has the union of the premise sets of the inputs without the zero fact, or `{zero}` if every input has
  `{zero}` (ap.md §4.6). The number of the members names the edge: `{zero}` a zero-to-fact edge, one member a
  fact-to-fact edge, two or more an ND edge. The field limit applies to the result.
* A literal on a `*`-mark fact raises a request (run 1), not an assumption.
* A sink whose condition has positive literals on several positions is a CONJUNCTIVE SINK. Each literal is a sink
  pattern; the same conjunction store combines the sink edges of the literals (ap.md §4.9, §8.9). The interpreter
  evaluates it at the same points as the other sinks (§4.5 step 3, §4.6, §4.7). Each literal raises its own request in
  run 1 (§5.4). At the normal exit, the part of an `S` item on which a literal holds is the stored input of that
  literal, and the global-state rule drops it from the summary edge (§4.7 step 3).
* A callee summary with several premises (an ND summary) applies at step 5 of the call order.
  ap.md §4.6 and §8.9 define how the caller finds the links for the other premises (event E6 of ap.md §5.3).
* Sinks, exit sources and the zero-to-zero step never make an ND edge (a conjunctive sink makes a vulnerability, not
  an edge).
* The backward run reverses a conjunctive edge into one plain edge per literal (§4.9).

### 5.4 Requests

A request exists only in forward run 1. The interpreter raises a MARK REQUEST where a rule needs a concrete mark `T`
and the fact has the mark `*` or `*∖X` with `T ∉ X` (and its premise has an abstract mark). The request is on the
premise of the edge. A fact whose mark excludes `T` raises no request for `T`. On the static base the static exception
of §2.1 step 4 raises a POSITION REQUEST instead (ap.md §4.10).

| Point | Rule element | Mechanism |
|---|---|---|
| sink at a call, exit sink | `ContainsMark`, `ContainsMarkOnAnyField` | the sink check (ap.md §4.9) |
| conjunctive sink (§5.3) | each positive literal on a `*`-mark fact | the sink check of the literal (ap.md §4.9); one request per literal |
| source at a call, exit source | the premise mark of a conditional source | the mark gate of `concat` (ap.md §4.1 step 4) |
| pass rule | the premise mark of `CopyMark(T)` | the mark gate |
| cleaner action | one mark, a `*`-mark fact, a partly cleaned position (no request if the fact mark excludes `T`) | `clean` (ap.md §4.7) |
| summary rewriter | as the cleaner action | `clean`, on the caller premise |
| ND source | a literal on a `*`-mark fact | the mark gate of the literal |
| a statement micro edge on `S` | its premise path lies strictly below an identity static `*` edge at the root `[]` or at a class `[<C>]` (a static read `[<C>, s]`, Go `[<G>]`; the class keep edge `[<C>]` of a static write or of a `RemoveAllMarks` kill; a conditional source at a call or at an exit, or a pass rule, on a static field) | the position request for the path cut to at most two accessors (§2.1 step 4; ap.md §4.10) |
| a sink or a conjunction literal on `S` | the ordinary sink check or literal (ap.md §4.9, §4.6) | the mark request; on a static premise it is answered by the added fact itself (ap.md §4.10 item 4) |
| entry rules, read sources | none (unconditional) | none |

In a restricted run (forward or backward) no fact has the mark `*`, so no request can occur (ap.md §6.1).
The interpreter asserts this in every restricted run (ap.md §13 item 9).

---

## 6. Deviations from today's code

The columns "Today" use today's notation (§0).

| # | Topic | Today | New | Why |
|---|---|---|---|---|
| D1 | read `x = y.f` | `y\{f} → y`, `y.f → y.f`, `y.f → x` (keep-except) | `y.* → y.*`, `y.f.* → x.*` | a read never changes an exclusion (I3) |
| D2 | self read `x = x.f` | `x\{f} → null` (refine only), `x.f → x` | `x.f.* → x.*` | no refinement |
| D3 | a fact above a micro-edge premise | the premise is refined (`SideEffectRequirement`, `refineInitial`) | unguarded `concat`: an `[any]` result in the demand layer | no refinement (I2) |
| D4 | mark readers at sinks, sources, cleaners, exits | `FactReader` refinement, any-field unfold requests | the request, run 1 only (§5.4) | ap.md §4.5 |
| D5 | summary application | delta with refinement (`tryApplySummaryEdge`) | guarded by satisfaction | ap.md §4.3 |
| D6 | call bindings | rebase functions (`mapMethodCallToStartFlowFact`, `mapMethodExitToReturnFlowFact`) | binding micro edges (§3.1) | one operation for every flow (I4); same mapping |
| D7 | Go cleaners | only the summary rewriter, only user-defined `RemoveMark` | `clean` at the call site for every cleaner rule, plus the rewriter | the same cleaner placement in both languages |
| D8 | cleaner on an abstract fact | `DeepAccessorExclusion` claims; a refinement request on abstract nodes | `clean` (`*∖x` mark; a request on a partly cleaned position) | ap.md §4.7 |
| D9 | reach `ExactAndAnyField` | cleans only through an `[any]` at the position | `atAndBelow` | `[any]` means "any continuation" in the new AP. The cleaner removes a mark only from a fact that lies inside the cleaned locations (ap.md §4.7), so it over-approximates |
| D10 | `RemoveAllMarks(P.AnyField)` | removes only an `[any]` child | `(P, below, all)` | the same meaning of `[any]` |
| D11 | type filter form | `FactTypeChecker` over the tree (Accept, Reject, FilterNext) | `filter(base, may)`, prefix-closed, tails kept, a separate mark policy | the ap.md §4.8 primitive; same predicate |
| D12 | `[any]` fact with a primitive-tracking mark on a primitive base | kept as `$` | kept as `[any]` | the filter never changes a tail (precision only) |
| D13 | filter of the caller content under `*` in the summary application | `AccessTree.concat` filters by the path type | none | the filter acts on bases at fixed points; precision only (Q3) |
| D14 | exit compatibility filter (`JIRMethodSummaryEdgeProcessor`) | removes `*` at incompatible fields | none | the same (Q3) |
| D16 | depth gate, `[any]` depth charge in the step | `INITIAL_ALLOWED_FACT_DEPTH`, `+10,000` | the field limit only | ap.md §4.4 |
| D17 | rules on a static position (JVM) | applied as written | the mapping of §1.4: an `[any]` target on a class position, a pass rule from or to a class position, a `ContainsMarkOnAnyField` literal in a rule with a class target, and `RemoveAllMarks(P.AnyField)` on `S` are rule errors; `RemoveAllMarks` on `S`, at any depth, is the kill of a strong write | a static access always names a field, a pass rule is a handcrafted summary, and the construction rules of I12 must hold |
| D18 | pass rule with an `AnyField` position | the content below the any-field node of `P` is copied below `Q` | an `[any]` premise or target (§4.1): an uncorrelated result in the demand layer (W6) | the field that the rule skips is not known, so a correlated edge does not cover the flow; precision only |
| D19 | a `Lambda` result of the call resolver (§3.9) | a resolution failure (the unresolved path) beside the lambda methods (`JIRMethodCallResolver.kt:184-209`) | the lambda methods of the prescan only; a resolution failure only if the prescan knows no lambda | the prescan resolves every lambda before run 1 (analyzer-core.md §9); fewer findings are possible (user decision, 2026-10-07) |
| D20 | a cleaner with a mark literal in its condition (§4.2) | the condition is evaluated on the fact (`TaintFactAwareConditionEvaluator`): a negated literal counts as true, and a literal can hold on the cleaned fact | the cleaner does not act | only an unconditional cleaner is sound for a fact-local engine; more findings are possible (user decision, 2026-10-07) |
| D21 | exit sinks (§4.7) | the production rule provider applies them only on zero-premise edges (`JIRMethodExitRuleProvider.kt:18-19`) | every fact at the exit | the sink check of ap.md §4.9 on every fact; more findings are possible (user decision, 2026-10-07) |
| D22 | an unconditional exit sink | no effect (`applyUnconditionalSinks` is a stub, `JIRMethodSequentFlowFunction.kt:191-200`) | it fires on the zero fact at both exits (ap.md §4.9; D26) | the same rule as every unconditional sink; more findings are possible (user decision, 2026-10-07) |
| D23 | the summary rewriter (§3.7, §5.2) | the rule selection: every user-defined source rule and every user-defined cleaner rule whose condition is not statically false (`JIRMethodCallRuleBasedSummaryRewriter.kt:67-85`); not applied on a zero-premise summary result and on the default identity of an unresolved callee (`JIRMethodCallSummaryHandler.kt:29-38, 71-90`) | the rule selection: every user-defined source rule whose condition is not statically false, and every user-defined cleaner rule whose condition is statically true; applied on every summary result and unresolved result | rule-guided flow: the rule overrides the callee for its marks; one rule for every result of the call; a conditional cleaner does not act (as D20). Fewer findings are possible (the results), more are possible (the cleaner selection) (user decisions, 2026-10-07 and `ap-history.md` F67) |
| D24 | a pass rule (`CopyAllMarks`, `CopyMark`) with a mark literal in its condition (§4.2) | the condition is evaluated on the fact | a rule error; the rule applies without its mark literals; a pass rule makes no ND edge | a pass rule has no mark-dependent condition (user decision, 2026-10-08); no exact form (gap G11) |
| D25 | liveness (§2.1 step 1) | the method analyzer drops an edge whose fact is on a local that is dead at the statement, also at a call (`MethodAnalyzer.kt:296`; JVM `JIRLocalVariableReachability`; Go: no drop) | no liveness step: the statement step keeps a fact on a dead local; the alias analysis keeps its own inputs | today's liveness goes backward from the exits of the forward graph, so in code that reaches no exit (a worker loop that never returns) every local is dead and its facts go. A dead local is not read again, so elsewhere the effect is more facts only; more findings are possible (`ap-history.md` F67) |
| D26 | the unconditional exit rules at the exceptional exit (§4.7) | the unconditional exit sources fire only at the normal exit (`JIRMethodSequentFlowFunction.kt:228-233`) | the unconditional exit sources and the unconditional exit sinks fire on the zero fact at both exits; an unconditional exit sink can report at both exits (accepted) | the exit rules act at both exits: the two exits are the one virtual exit of the model (ap.md S4); expected, more findings are possible (user decision, `ap-history.md` F67) |
| D27 | the Spring dispatcher cleanup (`__cleanup__`, §1.4, §5.2) | a fact-dependent cleaner: the rule provider builds it from the fact, for a fact on `S` the action `RemoveAllMarks(ClassStatic(C))` for each class of the fact except the registry class `__spring_registry__` (`SpringRuleProvider.kt:104-143`) | the generated dispatcher saves and restores the registry around each `__cleanup__()` call: for each static field `f` of `__spring_registry__` (one field per component, `SpringWebProject.kt:160-200`), `%reg_f = __spring_registry__.f` before the call and `__spring_registry__.f = %reg_f` after it (`ndMethodDispatch`, `SpringWebProject.kt:311`). The rule of `__cleanup__` is the fact-free unconditional whole-base cleaner `RemoveAllMarks(AnyClassStatic)`, that is `(S, atAndBelow, all)`: the rule provider gives it for a query with no fact; a query with a fact (the current core of the prescan) keeps today's cleaner | no rule of the new analysis needs the fact; the effect is the same: the static content outside the registry goes, and the registry stays (`ap-history.md` F67) |
| D28 | an empty method (I8) | a resolved callee; its analyzer publishes the identity summary of the most abstract premise `(b, [], *, {}, *)` (`EmptyMethodAnalyzer`, `MethodAnalyzerStorage.kt:19-31`) | never a callee: the resolver drops it; a call whose every resolution result is an empty method is unresolved (§3.7: the default identity and the pass rules) | an empty method is not analysable; the unresolved path is the summary of a callee with no body; more findings are possible (the pass rules apply) (`ap-history.md` F67) |
| D29 | a rule position with an inner or a repeated `AnyField` (§1.3) | handled by the fact readers (`FactReaderUtils.kt:54-138`) | a rule error: the interpreter rejects the rule and logs it once | `[any]` is a tail only (ap.md W4); fewer findings are possible (`ap-history.md` F67) |

Kept as today (no deviation): the rule order at entry, call and exit; the lhs kill; the alias analyses and their use;
the constructor rule; the exception rule; the conditional exit rules at both exits, with `Result` read as `exc` at the
exceptional exit (§4.7; the unconditional exit rules: D26); the exit rules for `S` and the entry marks; the array
elements of a call sink argument (§4.2); the primitive mark policy at the root and below each `[e]` (§5.1); the Go
pointer model; no Go type filter; unconditional Go pass rules; the summary rewriter (except D23); the
`<string-bytes>` rule; the default getter rules; no type filter in the backward run.

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
| `CleanerFieldSensitivityAnalysisTest`, `DeepCleanSummaryAnalysisTest`, `CleanerDslAnalysisTest`, `CleanerDslControlFlowAnalysisTest` | §4.5 order (sinks before cleaners), §5.2 mapping (plain = `exact`, AnyField = `below`), the `Result` cleaner tests | keep (a gate of the new analyzer) |
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
8. Requests: one test per row of §5.4 in run 1, also the static rows (JVM `x = C.s`, `C.s = x`, Go `x = G`, a sink on
   `S`); no request in a restricted run and in the backward run (assert).
9. ND: the result does not depend on the order in which the two premise facts arrive; a conjunctive sink reports only
   a full combination.
10. The rule statement of a call (§4.1): the zero fact keeps itself; a conditional source gives only its target, and
    the read fact does not pass over the call.
11. Static positions: one test per row of §1.4, also the rule errors.
12. Contracts: a check over the statement summaries, the call stages and the bindings of a program for every item of
    I11 and I12, and for the interpreter duties of ap.md S9 and S10: every literal has a concrete mark (S9); the
    premise base of every micro edge is a touched base (I1, S10); the target of a conjunctive micro edge has a concrete
    mark and no `*` tail (S10, W7). Also I6 and I7 (also the clause: a micro edge with a `$` target has a concrete
    premise mark). The builder of a statement summary asserts the same.
13. Backward run: the reversed touched set and the identity edge of an alias target (§4.9); the call order of §4.9,
    with a reversed source, a rewriter, an unresolved callee and a constructor; a seed after the reversed cleaners is
    not killed; a seed is cut by the field limit; the seed of an exit sink at the exceptional exit.
14. Array elements of a call sink (§4.2): a sink `ContainsMark(Argument(0), T)` on an `Object[]` argument triggers on
    `arg(0).[e].$ (T)`, and on a `String` argument it does not; its backward run seeds both alternatives.
15. Exit rules at the exceptional exit (§4.7): an exit sink on `Result` triggers on the thrown tainted value; an exit
    source at the exceptional exit adds no summary edge; an unconditional exit source and an unconditional exit sink
    fire at both exits, and the unconditional exit sink reports at both exits (D26).
16. Cleaners (§4.2, D20): `RemoveMark(T, P) if ContainsMark(P, T)` and a cleaner with a negated literal do not clean;
    the same cleaner with no condition cleans.
17. Lambdas (§3.9, D19): a call through a functional interface of the project, with a lambda that the prescan knows,
    has no unresolved path; the same call with no known lambda takes the unresolved path; a call through a JDK
    functional interface (`java.util.function.Function.apply`) with a known lambda keeps the unresolved path of the
    resolver's own failure.
18. No liveness (§2.1 step 1, D25): in `void serve() { while (true) { String req = in.readLine(); exec(req); } }` the
    fact on `req` reaches the sink `exec`; a fact on a dead local is not dropped.
19. Rule positions (§1.3, D29): `Argument(0).AnyField.f` and `Argument(0).AnyField.AnyField` are rule errors, logged
    once, and the forms of the other rules of the method are built; `Argument(0).AnyField` is accepted.
20. The whole-base cleaner (§1.4, §5.2, D27): `RemoveAllMarks(AnyClassStatic)` drops every fact on `S`, also `S.*` in
    run 1, with no request; `AnyClassStatic` in another rule element is a rule error. The Spring dispatcher: a static
    value that one dispatched controller taints does not reach the next one, and the registry fields keep their facts
    across `__cleanup__()`.
21. Empty methods (I8, D28): a call to a native method of the project takes the unresolved path (the pass rules and
    the default identity apply); a call with an empty and a non-empty resolution result enters only the non-empty
    callee; no summary exists for the empty method.
22. Aliases on call results (§3.8 AC3 to AC5): a normal-layer result equal to its start fact is not copied to the
    aliases; a demand-layer result equal to its start fact is copied (a run-1 answer for the premise
    `(x, [], *, {}, T)` with the demand start fact `(x, [], [any], {}, T)`).
23. The global-state rule (§4.7 step 3, G2): a plain exit sink on `S.<C>.$ (ST)` drops that part from the summary
    edge. For the conjunctive exit sink `ContainsMark(ClassStatic(C), ST) and ContainsMark(Result, T)` with an
    untainted `Result`, the `S` part is dropped and stored; a later item with a tainted `Result` completes the
    combination with the stored part.
24. The mark policy below `[e]` (§5.1): a mark that is not primitive-tracking on `b.[e]` of a `byte[]` and of an
    `Integer[]` value is dropped; on `b.[e]` of a `String[]` value it stays; below a field no type is read.
25. End facts (§4.1): a sink with an end-fact action that triggers on a demand-layer bound fact gives a demand-layer
    zero-to-fact edge; a conjunctive sink gives its end facts when an item completes the combination, in the layer of
    the combination.

---

## 8. Open questions

The resolved questions are in [`ap-history.md`](ap-history.md) (§5 and the end of the file). Each open question
states the current rule; the implementation follows it until the user decides.

| # | Question | Current rule |
|---|---|---|
| Q1 | A cleaner action on `Result` that is not user-defined has no effect today: no bound fact has the base `ret`. Proposal: apply `clean` to the results on `ret` before the binding back, for every cleaner rule. A decision is necessary. | As today: it has no effect. The rewriter applies an unconditional user-defined cleaner on `Result` (§5.2). |
| Q2 | Go has no type filter. The placement points of §5.1 fit Go too. Add a Go type checker? | No Go type filter (§2.3). |
| Q3 | D13 and D14 drop two precision filters of the summary application. Restore them as a filter on the summary conclusion, or make `may` recurse through the declared field types (prefix-closed too, and it covers most of D13)? | No summary-side filter (D13, D14). |
| Q10 | The gaps G1–G4, G6, G9 and G10 (§0.1) lose real flows. Keep them as today, or close some of them (G3: check the sinks of the cleaner method on the uncleaned fact; G4: read the rules of the resolved override too)? | All gaps stay as today. |
