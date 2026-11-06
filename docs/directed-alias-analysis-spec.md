# Directed local alias analysis — compact specification

This document specifies the proposed JVM local alias analysis. It is self-contained. The full design proposal, with the proofs and the measurements, is `directed-alias-analysis-design.md`. The implementation proposal is `directed-alias-analysis-impl.md`.

## 1. Purpose

The analysis answers one question for the taint analysis: at a statement, which access paths may hold the same value as a local variable `x`?

A value is an object or a null. A null has an identity: the null that a read finds in a cell is the same null for each reader of that cell. So `a = x.f` makes `a` alias `x.f`, also when `x.f` is null.

The analysis is intra-procedural, flow-sensitive and path-insensitive. It runs one time for each method. A callee body can be inlined to depth 1. Every other call is an unresolved call.

## 2. The relation

The analysis keeps an order `⊒` on values. `p ⊒ q` means: "`p` may hold each value that `q` may hold". The notation `p → q` means the same.

The order has four properties:

| Property | Meaning |
|---|---|
| Reflexive | `p ⊒ p` |
| Antisymmetric | `u ⊒ v` and `v ⊒ u` give `u = v`, for the nodes of §4 |
| Transitive | `p ⊒ q` and `q ⊒ r` give `p ⊒ r` |
| Congruent | `p ⊒ q` gives `p.f ⊒ q.f`, for each field `f` |

May-alias is derived from the order. It is not stored. Two paths may alias if one origin is below both of them. May-alias is symmetric, but it is not transitive:

```
if (c) a = x; else a = y;      a → x,  a → y
x ~ a,  a ~ y,  but not x ~ y
```

## 3. Origins

An origin is an abstract value. The value of a path is a finite set of origins. In a reachable state, the set is never empty (§5).

| Origin | Meaning | Unique |
|---|---|---|
| `⟨r.q⟩` | The value at path `q` below the entry root `r` (an argument, `this`, or the static holder of a class). `q` has at most K cells. `⟨r⟩` is the root itself. It also names each value that a callee writes into cell `q`. | yes, if `q` has no array cell (strong-update rule: §5.3) |
| `⟨s.q⟩` | The value at path `q` below the result of the unresolved call or unknown expression at site `s`. A catch variable is such a result. `q` has at most K cells. | yes, if site `s` is not in a loop and `q` has no array cell |
| `new(s)` | The most recent object of the allocation site `s` | yes |
| `old(s)` | All older objects of the allocation site `s` | no |
| `⟨@s.c.q⟩` | The value in cell `c` of an object of the allocation site `s` (for `q` empty): the default null of the cell, or a value that a callee writes there. For `q` not empty, the value at path `q` below it. `q` has at most K cells. | no |
| `null(i)` | The null of the null assignment at site `i` (`x = null`, or `x.f = null` through a local) | no |
| `deep(b)` | All values deeper than K below the base `b`: a root, a result site, or `@s.c` | no |
| `const(v)` | An interned constant: a string value (key: the value), a box of a constant value (key: the box type and the value, as `Integer.valueOf(1)`), a class literal (key: the class). The JVM can share one object for all sites. | no |
| `box(s)` | A box of a value that is not a constant (`Integer.valueOf(n)`) at site `s` | no |

A unique origin denotes at most one live value. Only a unique origin can get a strong update, and §5.3 adds two more conditions.

`null(i)` is never reported as an allocation. One origin for all nulls would make each null alias each other null, so each null site has its own origin.

A cell is `f` (an instance field, or a static field on the static holder) or `[]` (all elements of an array).

Default content. A cell that the method did not write holds its default content. The default content is never empty:

| Origin | Default content of cell `c` |
|---|---|
| `⟨b.q⟩` | `{⟨b.q.c⟩}` if `q.c` has at most K cells, else `{deep(b)}` |
| `deep(b)` | `{deep(b)}` |
| `new(s)`, `old(s)` | `{⟨@s.c⟩}`: the field of a new object holds a null, and this null has the name of its cell |
| `⟨@s.c.q⟩` | `{⟨@s.c.q.c'⟩}` at cell `c'` if `q.c'` has at most K cells, else `{deep(@s.c)}` |
| `null(i)`, `const(v)`, `box(s)` | an own child origin, never unique; a read through a null throws, so this content is never observed for a null |

Assumptions. The analysis is sound if these seven statements are true:

1. **Entry heap is a tree.** Two different entry roots are different objects. Two different entry paths below the roots are different objects. Aliases that the callers make between arguments are not visible.
2. **Callees reach only their arguments and the statics, and do not make aliases.** An unresolved call can reach the values reachable from its arguments (the receiver included) and from the static holders. It can overwrite a cell of such an object, or keep the cell. Each overwritten cell gets its own new value (a new object, or a new null). The call does not store an existing value into a cell. The taint analysis models those effects with its own summaries.
3. **Depth limit.** Values deeper than K are summarized by `deep`.
4. **Definite assignment.** Each local is assigned before it is used. The JVM verifier guarantees this for bytecode.
5. **Static fields keep their initial value for the method.** A read of a static field gives the value that the field had before the method. The method does not see its own static writes, and an unresolved call does not reach a value only because the method stored it in a static field. The taint analysis tracks static fields on its own (by decision; this is a known gap of the local analysis).
6. **A caught exception is an unknown object.** A catch variable does not hold a value that a `throw` of the analyzed code throws. The taint analysis moves exception facts on its own (by decision; known gap: `e = new E(); try { throw e; } catch (E c) { c.f = v; } t = e.f` has the real alias `t ~ v`, and the analysis does not find it).
7. **A box of a non-constant value is not a box of another site.** The JVM box cache can return one object for `Integer.valueOf(n)` and `Integer.valueOf(1)` if `n == 1`. The analysis does not relate them (by decision, as main).

## 4. State

The analysis stores one state before and one state after each statement.

```
State
  env   : Var            -> NodeId     absent key: unassigned
  heap  : (Origin, Cell) -> NodeId     absent key: default content
  Etree : NodeId                       the origins that a call reached (§5.6); node 0 at entry
  Eval  : NodeId                       the origins found in a cell of a reached origin at a call; node 0 at entry
```

In an implementation, `Etree` and `Eval` are two reserved keys of `env`. So they need no own join or comparison.

A node is one origin set in canonical form. All states of one method share one node table:

```
NodeTable
  node  : NodeId -> sorted array of origin ids     node 0 is the empty set
  union : (NodeId, NodeId) -> NodeId              memoized, symmetric
```

Rules:

- The table interns each set one time. Two node ids are equal if and only if their sets are equal.
- A union node is above its two child nodes in the order. The nodes and the union edges form a directed acyclic graph. The origins of a node are the leaves below it.
- Normal form: `heap` does not store an entry equal to the default content of its cell. Dead variables are removed from `env` (§5.5).
- In normal form, two states are equal if and only if their maps are equal. The comparison is one integer comparison for each key.

Notation in this document. `pts(x)` is the set of node `env[x]`. `H(o, c)` is the set of node `heap[(o, c)]`, or the default content.

## 5. Operations

### 5.1 Assignments

| Statement | Effect |
|---|---|
| `x = y` | `env[x] := env[y]` (the same node id; no copy) |
| `x = null` at null site `i` | `env[x] := {null(i)}` |
| `x = new T()` at site `s` | `retire(s)`, then `env[x] := {new(s)}` |
| `x = "abc"`, `x = Integer.valueOf(1)`, `x = T.class` | `env[x] := {const(v)}` |
| `x = Integer.valueOf(n)`, `n` not a constant, at site `s` | `env[x] := {box(s)}` |
| `x = (T) y` | as `x = y` |
| `x = <unknown expression>` at site `s` | `env[x] := {⟨s⟩}` |

`retire(s)` runs before each new object of site `s`. The old most recent object becomes an older object:

1. In each node of `env`, `heap`, `Etree` and `Eval`, replace `new(s)` by `old(s)`.
2. For each cell `c`: `H(old(s), c) := H(old(s), c) ∪ H(new(s), c)`, then remove the entry `(new(s), c)`. So the new object starts with its default content `{⟨@s.c⟩}`.

### 5.2 Field read: `x = y.f`

```
pts(x) := ⋃ { H(o, f) : o ∈ pts(y) }
```

The read does not change `heap`. The reader gets the origins of the cell, so it aliases the cell, also when the value is a null. A read of an unwritten cell gives its default content.

An array read `x = y[i]` is the same rule with the cell `[]`.

A static read `x = C.f` always gives `{⟨C.f⟩}`: the default content of cell `f` of the static holder `⟨C⟩`, as if the field was not initialized (assumption 5). The static holders keep their default content, because static writes are ignored (§5.3).

### 5.3 Field write: `x.f = y`

The write is strong if all these conditions are true. Else it is weak.

1. `pts(x) = {o}`: one origin.
2. `o` is unique (§3).
3. No proper prefix of `o` is in `Etree`. A call that reached `⟨b.p⟩` can put a new value into a cell below it. That value has the name of the cell, so `⟨b.p.q⟩` can denote two values.
4. `o ∉ Eval`. A call that reached the cell that held `o` can put a new value into that cell. A later read of the cell returns `o` for this new value, so `o` can denote two values.

```
strong:   H(o, f) := pts(y)
weak:     H(o, f) := H(o, f) ∪ pts(y)    for each o ∈ pts(x)
```

- A strong update removes the old content of the cell. A weak update keeps it and adds the new value.
- If `H(o, f) ⊆ pts(y)`, the two updates give the same result. Then the test is not necessary. This is true, for example, for the first write of a value that the cell already holds.
- An array write `x[i] = y` is always a weak update.
- A static write `C.f = y` is ignored: the state does not change (assumption 5).

A write goes down the order. After `a.f = z`, each `x` with `a ⊒ x` reads `z` at `f`.

### 5.4 Join

At a node with two or more predecessors, the state is the pointwise union. For each key, `Etree` and `Eval` included, the join does one memoized union of the two node ids. The join also gives a change bit: true if some key now holds a node that is not its old node.

### 5.5 Loops and the fixpoint

1. Iterate the control-flow graph in weak topological order.
2. At a loop head, the new state is `join(old head state, incoming state)`. So a head state only grows.
3. If the change bit of the head join is false, the loop is stable.
4. An inner loop restarts at each iteration of its outer loop.

The transfer is not monotone, because a strong update can remove content. The accumulation at the heads makes the iteration terminate. There is a finite number of origins: entry paths up to K, sites, null sites, cells.

Exceptions: the state on an edge to a catch handler is `join(state before, state after)` of each instruction that can throw to it (the throwers of the JIR graph, not only the throwers that the taint graph keeps). For a call to an inlined callee, each callee instruction is such an instruction. The catch variable gets `{⟨s⟩}` (assumption 6).

A back edge to the first instruction makes it a loop head: its state joins the initial state and the back edge.

Dead variables. A variable is live at a statement if a later statement can read it before a write. An exception happens before the write of the statement. So a variable that a handler reads is live at each thrower of the handler, also if the thrower writes it:

```
live_in(v) = use(v) ∪ ⋃ normal successors w: (live_in(w) \ def(v)) ∪ ⋃ handlers h of v: live_in(h)
```

The analysis removes a variable from `env` only where it is not live. `Etree` and `Eval` are never removed.

### 5.6 Unresolved call: `x = m(a1, ..., an)` at site `s`

The call does not change the alias graph. It only prohibits strong updates later.

1. **Start set.** `R := pts(a1) ∪ ... ∪ pts(an) ∪ {⟨r⟩ : r a static holder}`. The receiver is an argument. For a constructor call, it is the new object. The static holders have no written cells, so they add only their symbolic descendants: after any call, `⟨C.f…⟩` has the reached prefix `⟨C⟩`.
2. **Closure.** An origin is covered if it is in `R` or below an origin of `R` (a symbolic descendant, or an allocation child `⟨@t.c…⟩` of `new(t)` or `old(t)`). Add to `R` the content of each written cell of each covered origin. Repeat until `R` does not grow. If the closure does not stop within its limit, put each origin into both sets.
3. **Record.** `Etree := Etree ∪ R`. `Eval := Eval ∪ { contents of the cells of the covered origins }`.
4. **Result.** `env[x] := {⟨s⟩}`.

The call writes no heap entry and changes no variable except `x`, `Etree` and `Eval`.

Why this is enough:

- A callee can keep a cell, so the old content stays.
- A callee can write a new value into a reached cell. Each later reader of that value reads the same cell and gets its content. That content is never empty, so all readers share an origin, and they alias.
- The new value has the name of the cell content. The strong-update conditions 3 and 4 of §5.3 stop a write through such a name from removing content that another value with the same name still holds.

Examples:

- `n = new N(); m(n); a = n.f; b = n.f`. If `m` writes one new object into `n.f`, then `a` and `b` are that object. Both reads get `{⟨@5.f⟩}`, so `a ~ b`.
- `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. If `m` puts a new object into `x.f`, then `t` is that object, and `w.g` is still `e`. `pts(t) = {⟨x.f⟩}`, and `⟨x⟩ ∈ Etree`, so `t.g = z` is a weak update, and `w.g ~ e` stays.
- `z = new Box(); z.g = e; x.f = z; m(x); t = x.f; t.g = v`. If `m` puts a new object into `x.f`, then `t` is that object, and `z.g` is still `e`. `pts(t) = {new(s)}`, and `new(s) ∈ Eval`, so `t.g = v` is a weak update, and `z.g ~ e` stays.
- `t = this.box; touch(); t.value = v`. `touch()` has no arguments, so `⟨this⟩` is not reached, and `t.value = v` is a strong update.

Accepted precision losses. The strong-update test is coarse in two shapes:

| Program | The analysis says | Concrete fact |
|---|---|---|
| `t = x.f; m(x); t.g = z` | `t.g = z` is a weak update | `t` was read before the call, so it holds one object; the update could be strong |
| `this.box = b; touch(this); b.value = v` | `b.value = v` is a weak update | `b` holds one object; the update could be strong |

A modeled library call (a pass-through rule `from → to`) is a weak copy: `to ∪= from`.

An inlined callee (depth 1) runs in the caller state. Its locals are in a new context. They are removed when the callee returns. Its unresolved calls are calls of the caller. A `return` of a constant or of `null` assigns that value to the result.

### 5.7 Query

`findAlias(x, statement)` reads the state before the statement:

- Each path `v.c1...cn` with `n ≤ D` and `pts(v.c1...cn) ∩ pts(x) ≠ ∅`. The root `v` is a live local, an argument, `this` or a static holder. The path `x` itself is not in the answer.
- Each allocation site `s` with `new(s)` or `old(s)` in `pts(x)`. `null(i)` and `⟨@s.c.q⟩` are not allocations.

The query is a backward search, and it is lazy:

1. Start from the origins of `pts(x)`.
2. Step to the holders of each origin: the variables whose node holds it, and the cells `(o', c)` whose content holds it. Default content counts.
3. Prefix the cell to the path, up to D cells.
4. Never follow the self cells of `deep(b)`.

A query for a heap path `x.c1...cm` is the same search. Its start set is the value of the path: read the cells `c1...cm` from `pts(x)` (§5.2). The answer is each path `v.c1'...cn'` (`n ≤ D`) that shares an origin with this value, except the queried path. The answer cannot be derived from `findAlias(x)`. After `x.f = z`, the path `z` aliases `x.f`, but `z` does not alias `x`.

A query for the elements of an array `x[*]` (the variable-argument conditions of the taint rules) is a heap-path query. It also reports the allocation sites and the constants of its start set, as `findAlias` does for a variable.

Queries do not change the node table.

## 6. Examples

`x`, `y`, `z`, `w`, `h` are arguments. So `pts(x) = {⟨x⟩}` at entry, and the same for the others.

### 6.1 Assignment and join

```java
if (c) a = x; else a = y;
```

| | `pts` |
|---|---|
| `x` | `{⟨x⟩}` |
| `y` | `{⟨y⟩}` |
| `a` | `{⟨x⟩, ⟨y⟩}` |

Order: `a ⊒ x` and `a ⊒ y`. `x` and `y` are not ordered.

Queries: `findAlias(x) = {a}`, `findAlias(y) = {a}`, `findAlias(a) = {x, y}`.

### 6.2 Field write through the join, then reassignment

```java
if (c) a = x; else a = y;
a.f = z;        // pts(a) has two origins: weak update
a = w;
```

| Key | Content after `a.f = z` | Content after `a = w` |
|---|---|---|
| `env[a]` | `{⟨x⟩, ⟨y⟩}` | `{⟨w⟩}` |
| `heap[(⟨x⟩, f)]` | `{⟨x.f⟩, ⟨z⟩}` | `{⟨x.f⟩, ⟨z⟩}` |
| `heap[(⟨y⟩, f)]` | `{⟨y.f⟩, ⟨z⟩}` | `{⟨y.f⟩, ⟨z⟩}` |

Queries after `a = w`:

- `findAlias(z) = {x.f, y.f}`. Both fields may hold `z`.
- `findAlias(x) = {}`. There is no relation between `x` and `y`, and no relation between `x` and `a`.
- `findAlias(x.f) = {z, y.f}`. This is a heap-path query (§5.7). Its start set is `H(⟨x⟩, f) = {⟨x.f⟩, ⟨z⟩}`.
- `x.f` and `y.f` may alias, because both may hold `⟨z⟩`. The analysis is path-insensitive, so this is expected.

### 6.3 Strong update

```java
b = x.f;        // pts(b) = {⟨x.f⟩}
x.f = z;        // pts(x) = {⟨x⟩}, unique, no call: strong update
t = x.f;        // pts(t) = {⟨z⟩}
```

After the write, `H(⟨x⟩, f) = {⟨z⟩}`. `findAlias(t) = {x.f, z}`. `b` no longer aliases `x.f`.

With a loop allocation:

```java
while (c) {
  n = new Node();   // site 7: retire(7), pts(n) = {new(7)}, H(new(7), f) = {⟨@7.f⟩}
  n.f = x;          // new(7) is unique: strong update
  n.f = y;          // strong update again
}
```

At the end of the body, `H(new(7), f) = {⟨y⟩}`. So `n.f` aliases `y`, and it does not alias `x`. At the next `new`, `retire(7)` moves this content into `H(old(7), f)`. So the objects of earlier iterations keep `⟨y⟩`.

### 6.4 Field read

```java
if (c) a = x; else a = y;
t = a.f;        // pts(t) = H(⟨x⟩, f) ∪ H(⟨y⟩, f) = {⟨x.f⟩, ⟨y.f⟩}
```

Both cells hold their default content. `findAlias(t) = {a.f, x.f, y.f}`.

### 6.5 Loop over a list

```java
x = h;
while (c) { x = x.next; }
```

The head state of `pts(x)` grows by one origin in each iteration. It is stable when the chain reaches `deep(h)`. Example for K = 2:

| Iteration | `pts(x)` at the loop head |
|---|---|
| 1 | `{⟨h⟩}` |
| 2 | `{⟨h⟩, ⟨h.next⟩}` |
| 3 | `{⟨h⟩, ⟨h.next⟩, ⟨h.next.next⟩}` |
| 4 | `{⟨h⟩, ⟨h.next⟩, ⟨h.next.next⟩, deep(h)}`, stable (the `next` cell of `deep(h)` holds `deep(h)`) |

`x ~ x.next`, `x ~ h` and `x ~ h.next.next.next.next.next` are true. `h ~ h.next` is false, because the entry heap is a tree (§3, assumption 1). The summary `deep(h)` makes a finite cycle that stands for the infinite chain.

### 6.6 Reads of nulls

```java
x = new X();    // site 5: H(new(5), f) = {⟨@5.f⟩}
a = x.f;        // pts(a) = {⟨@5.f⟩}
p = null;       // null site 0: pts(p) = {null(0)}
q = null;       // null site 1: pts(q) = {null(1)}
r = p;          // pts(r) = {null(0)}
```

- `findAlias(a) = {x.f}`. `a` holds the null of the cell `x.f`, with or without a call.
- `p ~ q` is false: two null assignments give two different nulls.
- `p ~ r` is true: `r` is a copy of `p`.

### 6.7 Unresolved call

```java
w = x.f;        // pts(w) = {⟨x.f⟩}
m(x);           // site 9: Etree = {⟨x⟩ and the origins below it}; Eval = the contents of their cells, ⟨x.f⟩ included; the heap does not change
u = x.f;        // pts(u) = {⟨x.f⟩}
v = y.g;        // pts(v) = {⟨y.g⟩}
u.h = z;        // ⟨x.f⟩ has the reached prefix ⟨x⟩: weak update
```

`w ~ x.f` stays true, because `m` can keep the cell. `u ~ w` is true. `u ~ v` is false: `m` does not reach `y`, and the two cells have different names. The write `u.h = z` is weak, because `u` can hold the old object or the new object of `m`.

With a new object and an explicit null:

```java
n = new N();    // site 5: pts(n) = {new(5)}, H(new(5), f) = {⟨@5.f⟩}
n.g = null;     // null site 0: H(new(5), g) := {null(0)} (strong)
m(n);           // the heap does not change
a = n.f;        // {⟨@5.f⟩}
b = n.f;        // {⟨@5.f⟩}
c = n.g;        // {null(0)}
d = n.g;        // {null(0)}
```

`a ~ b` and `c ~ d` are true. If `m` writes new objects into `n.f` and `n.g`, the readers of each cell get the same object.

### 6.8 Static fields

```java
C.f = v;        // ignored: the state does not change
t = C.f;        // pts(t) = {⟨C.f⟩}
u = C.f;        // pts(u) = {⟨C.f⟩}
t.g = z;        // ⟨C.f⟩ is unique, and no call came before: strong update
m();            // the static holder ⟨C⟩ is reached
u.g = w;        // ⟨C.f⟩ has the reached prefix ⟨C⟩: weak update
```

- `t ~ u` is true: both read the static field.
- `t ~ v` is false: the static write is ignored (assumption 5).

## 7. Parameters

| Parameter | Proposed value | Status |
|---|---|---|
| K, the origin depth | 7 (K ≥ D + 1) | open |
| D, the query depth | 6 cells | open |
| Recency (`new` / `old`) | on | open (only this form is proved) |
| Strong update on entry roots | on | decided |
| Alias removal at calls | none | decided |
| Read rule | a read aliases the cell, nulls included (§5.2, §6.6) | decided |
| Static fields | writes ignored; a read gives `{⟨C.f⟩}` (§5.2, §5.3, §6.8) | decided |
| Call rule | no change of the alias graph; it only prohibits strong updates (§5.6) | decided |
| Strong-update test after calls | the sets `Etree` and `Eval` (§5.6); an on-demand test is recorded in the design, §7.6 | decided |
| Constants | strings by value, boxes by type and constant value, `box(s)` for other boxes | decided |
| Catch variable | `{⟨s⟩}` (assumption 6) | decided |
| Alias answer volume control | to choose after the measurement | open |

## 8. Guarantees

The Lean model in `formal/directed-alias` proves these facts for a structured version of the language of §5. The proofs are constructive. The concrete semantics gives each null an identity, so "the same value" covers nulls.

| Fact | Lean theorem |
|---|---|
| The analysis is sound under the assumptions of §3: each alias of one execution (the same object or the same null) is a may-alias. Assumption 5 is a concrete semantics in which the static writes of the method have no effect. Assumption 6 is a semantics in which each `throw` of the method throws an unknown exception. Assumption 7 is outside the model. | `csoundVS`; with the static rule: `csoundVSS`, `execA5_iff`; with exceptions: `csoundCfgA6`, `reach_a6` |
| On a control-flow graph, each post-fixpoint of the transfer is sound: each iteration order, irreducible loops, exception edges, dead-variable removal with the rule of §5.5, and inlined callees as a part of the graph. | `csoundCfg`, `csoundKill`, `csoundEngineCfg` |
| Assumption 6 is a real restriction: a locally thrown value can alias the catch variable. A dead-variable rule that removes the written variable also at handlers loses a real alias. | `catch_gap`, `live_spec_unsound` |
| A static read gives exactly `{⟨C.f⟩}`: the cells of a static holder keep their default content. | `static_read`, `SCInv_analyze` |
| Assumption 5 is a real restriction: without it, `C.f = v; t = C.f` has the alias `t ~ v`, and a value stored only into a static field can lose an alias after a call. | `gapA`, `gapB` |
| It stays sound if a callee also writes new nulls. | `csoundVS_W` |
| Assumption 4 is necessary: with a local that is used before it is assigned, a real alias is lost. | `siteless_unsound` |
| The node representation gives the same answers as the set semantics. | `mayProgVSO_eq`, `csoundVSO`; with the static rule: `mayProgVSSO_eq`, `csoundVSSO` |
| A call writes no heap entry, and changes only the result and the two sets. | `callVSO_heap_frame`, `callVSO_frame` |
| `x = new X(); a = x.f` gives `a ~ x.f`, with and without a call, and the alias is real. | `user_answers`, `user_real`, `user_call_real` |
| The cases of §5.6 and §6.7 are found and real: the empty field, the join and loop cases, the null store. | `empty_answersVS`, `bo0_cases_VS`, `bo0_cases_realV`, `nullStore_answers`, `nullStore_real` |
| Two null sites do not alias, and this is exact. A copy of a null aliases it. | `nulls_answers`, `nulls_exact` |
| The two accepted losses of §5.6 are real losses: no execution has these aliases. | `losses_VS`, `losses_noneV` |
| The order is reflexive, transitive, antisymmetric on nodes and congruent. | `above_refl`, `above_trans`, `node_antisymm`, `path_mono` |
| A write goes down the order. | `store_down` |
| May-alias is a common origin below both paths. | `may_iff_common_lower` |
| No transitive relation that is sound can keep `x` and `y` apart in §6.1. | `transitive_sound_relates_x_y` |
| The backward search gives the same paths as an enumeration of all paths. | `findAlias_iff` |
| The search for a heap path gives the same paths as an enumeration. | `heapAliases_iff` |

Argued, not proved: the termination of the iteration of §5.5, the mapping of JIR statements to the rules of §5, and definite assignment in the JIR form of the bytecode. The implementation proofs (engine state, call closure, control-flow graph) are listed in `directed-alias-analysis-impl.md`, §7.
