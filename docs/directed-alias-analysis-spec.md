# Directed local alias analysis — compact specification

This document specifies the proposed JVM local alias analysis. It is self-contained. The full design proposal, with the proofs, the measurements and the implementation plan, is `directed-alias-analysis-design.md`.

## 1. Purpose

The analysis answers one question for the taint analysis: at a statement, which access paths may refer to the same object as a local variable `x`?

The analysis is intra-procedural, flow-sensitive and path-insensitive. It runs one time for each method. A callee body can be inlined to depth 1. Every other call is an unresolved call.

## 2. The relation

The analysis keeps an order `⊒` on values. `p ⊒ q` means: "`p` may hold each object that `q` may hold". The notation `p → q` means the same.

The order has four properties:

| Property | Meaning |
|---|---|
| Reflexive | `p ⊒ p` |
| Antisymmetric | `u ⊒ v` and `v ⊒ u` give `u = v`, for the nodes of §4 |
| Transitive | `p ⊒ q` and `q ⊒ r` give `p ⊒ r` |
| Congruent | `p ⊒ q` gives `p.f ⊒ q.f`, for each field `f` |

May-alias is derived from the order. It is not stored. Two paths may alias if one object origin is below both of them. May-alias is symmetric, but it is not transitive:

```
if (c) a = x; else a = y;      a → x,  a → y
x ~ a,  a ~ y,  but not x ~ y
```

## 3. Origins

An origin is an abstract object. A value is a finite set of origins. The empty set means "always null".

| Origin | Meaning | Unique |
|---|---|---|
| `⟨r.q⟩` | The object at path `q` below the entry root `r` (an argument, `this`, or the static holder of a class). `q` has at most K cells. `⟨r⟩` is the root itself. It also names each object that a callee writes into cell `q` (§5.6). | yes, if `q` has no array cell and is not below an exposed origin (§4) |
| `⟨s.q⟩` | The object at path `q` below the result of the unresolved call or unknown expression at site `s`. A catch variable is such a result. `q` has at most K cells. | yes, if site `s` is not in a loop, `q` has no array cell, and `q` is not below an exposed origin |
| `⟨@s.c.q⟩` | The object that a callee writes into cell `c` of an object of the allocation site `s` (for `q` empty), or the object at path `q` below it. `q` has at most K cells. | no |
| `deep(b)` | All objects deeper than K below the base `b`: a root, a result site, or `@s.c` (an allocation site and the first cell) | no |
| `new(s)` | The most recent object of the allocation site `s` | yes |
| `old(s)` | All older objects of the allocation site `s` | no |
| `const(v)` | An interned constant: a string value, a boxed value type, a class literal. The JVM can share one object for all sites. | no |

A unique origin denotes at most one live object. Only a unique origin can get a strong update.

Below an exposed origin. `⟨b.q⟩` is below an exposed origin if `exposed` (§4) holds `⟨b.p⟩` for a proper prefix `p` of `q`. A call that reaches `⟨b.p⟩` can put a new object into a cell below it. That object has the same name, so the name can denote two objects. The origin `⟨b.p⟩` itself stays unique: a callee cannot replace the value of a variable.

A cell is `f` (an instance field, or a static field on the static holder) or `[]` (all elements of an array).

Default content. A cell that the method did not write holds its default content:

| Origin | Default content of cell `c` |
|---|---|
| `⟨b.q⟩` | `{⟨b.q.c⟩}` if `q.c` has at most K cells, else `{deep(b)}` |
| `deep(b)` | `{deep(b)}` |
| `new(s)`, `old(s)` | `{}` (null) |
| `⟨@s.c.q⟩` | `{⟨@s.c.q.c'⟩}` at cell `c'` if `q.c'` has at most K cells, else `{deep(@s.c)}` |
| `const(v)` | `{}` |

Assumptions. The analysis is sound if these three statements are true:

1. **Entry heap is a tree.** Two different entry roots are different objects. Two different entry paths below the roots are different objects. Aliases that the callers make between arguments are not visible.
2. **Callees reach only their arguments and the statics, and do not make aliases.** An unresolved call can reach the objects reachable from its arguments (the receiver included) and from the static holders. It can overwrite a cell of such an object, or keep the cell. Each overwritten cell gets its own new object. The call does not store an existing object into a cell. The taint analysis models those effects with its own summaries.
3. **Depth limit.** Objects deeper than K are summarized by `deep`.

## 4. State

The analysis stores one state before and one state after each statement.

```
State
  env     : Var            -> NodeId     absent key: null
  heap    : (Origin, Cell) -> NodeId     absent key: default content
  exposed : NodeId                       the origins that a call reached (§5.6); node 0 at entry
```

In an implementation, `exposed` is one reserved key of `env`. So it needs no own join or comparison.

A node is one origin set in canonical form. All states of one method share one node table:

```
NodeTable
  node  : NodeId -> sorted array of origin ids     node 0 is the empty set
  union : (NodeId, NodeId) -> NodeId              memoized, symmetric
```

Rules:

- The table interns each set one time. Two node ids are equal if and only if their sets are equal.
- A union node is above its two child nodes in the order. The nodes and the union edges form a directed acyclic graph. The origins of a node are the leaves below it.
- Normal form: `heap` does not store an entry equal to the default content of its cell. Dead variables are removed from `env`.
- In normal form, two states are equal if and only if their maps are equal. The comparison is one integer comparison for each key.

Notation in this document. `pts(x)` is the set of node `env[x]`. `H(o, c)` is the set of node `heap[(o, c)]`, or the default content. `E` is the set of node `exposed`.

## 5. Operations

### 5.1 Assignments

| Statement | Effect |
|---|---|
| `x = y` | `env[x] := env[y]` (the same node id; no copy) |
| `x = null` | remove `x` from `env` |
| `x = new T()` at site `s` | `retire(s)`, then `env[x] := {new(s)}` |
| `x = "abc"`, `x = Integer.valueOf(1)`, `x = T.class` | `env[x] := {const(v)}` |
| `x = (T) y` | as `x = y` |
| `x = <unknown expression>` at site `s` | `env[x] := {⟨s⟩}` |

`retire(s)` runs before each new object of site `s`. The old most recent object becomes an older object:

1. In each node of `env` and `heap`, replace `new(s)` by `old(s)`.
2. For each cell `c`: `H(old(s), c) := H(old(s), c) ∪ H(new(s), c)`, then reset `H(new(s), c)` to null.

### 5.2 Field read: `x = y.f`

```
pts(x) := ⋃ { H(o, f) : o ∈ pts(y) }
```

The read does not change `heap`. A read of an unwritten cell gives its default content. This content can name a new symbolic origin, for example `⟨y.f⟩`.

An array read `x = y[i]` is the same rule with the cell `[]`.

### 5.3 Field write: `x.f = y`

```
if pts(x) = {o} and o is unique:     H(o, f) := pts(y)              strong update
else:                                H(o, f) := H(o, f) ∪ pts(y)    weak update, for each o ∈ pts(x)
```

- A strong update removes the old content of the cell.
- A weak update keeps the old content and adds the new value.
- If `pts(x)` is empty, the write has no effect. The real write would throw.
- An array write `x[i] = y` is always a weak update.
- A static write `C.f = y` is a write of cell `f` of the static holder of `C`.

A write goes down the order. After `a.f = z`, each `x` with `a ⊒ x` reads `z` at `f`.

### 5.4 Join

At a node with two or more predecessors, the state is the pointwise union. For each key, `exposed` included, the join does one memoized union of the two node ids. The join also gives a change bit: true if some key now holds a node that is not its old node.

### 5.5 Loops and the fixpoint

1. Iterate the control-flow graph in weak topological order.
2. At a loop head, the new state is `join(old head state, incoming state)`. So a head state only grows.
3. If the change bit of the head join is false, the loop is stable.
4. An inner loop restarts at each iteration of its outer loop.

The transfer is not monotone, because a strong update can remove content. The accumulation at the heads makes the iteration terminate. There is a finite number of origins: entry paths up to K, sites, cells.

Exceptions: the state on an edge to a catch handler is `join(state before, state after)` of the instruction that throws.

### 5.6 Unresolved call: `x = m(a1, ..., an)` at site `s`

The rule names each unknown object by the cell where it is found. The name of the object that a callee can write into cell `c` of origin `o` is `name(o, c)`:

| `o` | `name(o, c)` |
|---|---|
| `⟨b.q⟩` | `⟨b.q.c⟩` (`deep(b)` beyond K): the default content of the cell |
| `deep(b)` | `deep(b)` |
| `new(t)`, `old(t)` | `⟨@t.c⟩` (the same name for both, so `retire` does not rename it) |
| `⟨@t.c0.q⟩` | `⟨@t.c0.q.c⟩` (`deep(@t.c0)` beyond K) |

Steps:

1. **Start set.** `R := pts(a1) ∪ ... ∪ pts(an) ∪ {⟨r⟩ : r a static holder}`. The receiver is an argument; for a constructor call it is the new object.
2. **Closure.** An origin is covered if it is in `R` or below an origin of `R`. Add to `R` the content of each written cell of each covered origin. Repeat until `R` does not grow. Unwritten cells need no step: their default content is below a covered origin.
3. **Weak havoc by name.** For each written cell `(o, c)` of a covered origin: `H(o, c) := H(o, c) ∪ {name(o, c)}`. For each covered allocation origin `o` and each cell `c`: the same. The old content stays. An unwritten cell of a covered symbolic origin needs no work: its default content already is `{name(o, c)}`.
4. **Exposure.** `E := E ∪ R`.
5. **Result.** `env[x] := {⟨s⟩}`.

The call creates no origin. Its cost is the closure over written cells, plus one union for each written cell of a covered origin and for each cell of a covered allocation.

Why each part is necessary:

- The old content stays, because the callee can keep a cell.
- Step 3 adds the cell name, because the callee can write a new object. Example: `n = new N(); m(n); a = n.f; b = n.f`. If `m` writes one new object into `n.f`, then `a` and `b` are that object. Without step 3, `n.f` stays null, and `a` and `b` do not alias.
- Step 4 removes uniqueness below a reached object, because the cell name now can denote the old object and a new one. Example: `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. If `m` puts a new object into `x.f`, then `w.g` is still `e`. `pts(t) = {⟨x.f⟩}`, but `⟨x.f⟩` is below the exposed `⟨x⟩`, so `t.g = z` is a weak update, and `w.g ~ e` stays.
- The narrow start set keeps precision: a call that does not reach an object does not change it. Example: `t = this.box; touch(); t.value = v`. `touch()` has no arguments, so `⟨this⟩` is not exposed, and `t.value = v` is a strong update.

Accepted precision losses. A cell name stands for the entry object and for each object that any callee writes into the cell. So the analysis cannot tell these objects apart:

| Program | The analysis says | Concrete fact |
|---|---|---|
| `t = x.f; m(x); t.g = z` | `t.g = z` is a weak update | `t` holds one object, so the update could be strong |
| `w = x.f; x.f = b; m(x); t = x.f` | `t ~ w` | `t` is `b` or a new object; it is never the old object in `w` |
| `x.f = b1; m(x); a = x.f; x.f = b2; m(x); c = x.f` | `a ~ c` | the two calls write two different new objects |

A modeled library call (a pass-through rule `from → to`) is a weak copy: `to ∪= from`.

An inlined callee (depth 1) runs in the caller state. Its locals are in a new context. They are removed when the callee returns.

### 5.7 Query

`findAlias(x, statement)` reads the state before the statement:

- Each path `v.c1...cn` with `n ≤ D` and `pts(v.c1...cn) ∩ pts(x) ≠ ∅`. The root `v` is a live local, an argument, `this` or a static holder. The path `x` itself is not in the answer.
- Each allocation site `s` with `new(s)` or `old(s)` in `pts(x)`.

The query is a backward search, and it is lazy:

1. Start from the origins of `pts(x)`.
2. Step to the holders of each origin: the variables whose node holds it, and the cells `(o', c)` whose content holds it. Default content counts.
3. Prefix the cell to the path, up to D cells.
4. Never follow the self cells of `deep(b)`.

A query for a heap path `x.c1...cm` is the same search. Its start set is the value of the path: read the cells `c1...cm` from `pts(x)` (§5.2). The answer is each path `v.c1'...cn'` (`n ≤ D`) that shares an origin with this value, except the queried path. The answer cannot be derived from `findAlias(x)`. After `x.f = z`, the path `z` aliases `x.f`, but `z` does not alias `x`. If the value is empty, the answer is empty.

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
x.f = z;        // pts(x) = {⟨x⟩}, unique: strong update
t = x.f;        // pts(t) = {⟨z⟩}
```

After the write, `H(⟨x⟩, f) = {⟨z⟩}`. `findAlias(t) = {x.f, z}`. `b` no longer aliases `x.f`.

With a loop allocation:

```java
while (c) {
  n = new Node();   // site 7: retire(7), pts(n) = {new(7)}
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

### 6.6 Unresolved call

```java
w = x.f;        // pts(w) = {⟨x.f⟩}
m(x);           // site 9: R = {⟨x⟩}, E = {⟨x⟩}; the cell (⟨x⟩, f) is unwritten: no work
u = x.f;        // pts(u) = {⟨x.f⟩}
v = y.g;        // pts(v) = {⟨y.g⟩}
u.h = z;        // ⟨x.f⟩ is below the exposed ⟨x⟩: weak update
```

`w ~ x.f` stays true, because `m` can keep the cell. `u ~ w` is true. `u ~ v` is false: `m` does not reach `y`, and the two cells have different names. The write `u.h = z` is weak, because `u` can hold the old object or the new object of `m`.

With a new object:

```java
n = new N();    // site 5: pts(n) = {new(5)}
m(n);           // R = {new(5)}: H(new(5), f) := {⟨@5.f⟩} for each cell f
a = n.f;        // pts(a) = {⟨@5.f⟩}
b = n.f;        // pts(b) = {⟨@5.f⟩}
```

`a ~ b` is true: both loads find the object of `m` by the name of its cell.

## 7. Parameters

| Parameter | Proposed value | Status |
|---|---|---|
| K, the origin depth | 7 (K ≥ D + 1) | open |
| D, the query depth | 6 cells | open |
| Recency (`new` / `old`) | on | open |
| Strong update on entry roots | on | decided |
| Alias removal at calls | none: weak havoc | decided |
| Call rule | narrow reach, unknown objects named by their cell, `exposed` set (§5.6) | decided |
| Alias answer volume control | to choose after the measurement | open |

## 8. Guarantees

The Lean model in `formal/directed-alias` proves these facts for a structured version of the language of §5. The proofs are constructive.

| Fact | Lean theorem |
|---|---|
| The analysis is sound under the assumptions of §3: each alias of one execution is a may-alias. | `csoundCN` |
| The node representation gives the same answers as the set semantics. | `mayProgCNO_eq`, `csoundCNO` |
| Both parts of assumption 2 are necessary: with every object reachable, or with one object in two cells, the rule misses aliases. | `generous_reach_breaks_CN`, `generous_havoc_breaks_CN` |
| The call rule keeps the examples of §5.6: the empty cell and the later update are found, the call that reaches nothing keeps the strong update, two different cells do not alias. | `need_answersCN`, `gain_answersCN`, `spread_goneCN`, `dead_answerCN` |
| The three accepted losses of §5.6 are real losses: no execution has these aliases. | `losses_CN`, `loss1_noneN`, `loss2_noneN`, `loss3_noneN` |
| The order is reflexive, transitive, antisymmetric on nodes and congruent. | `above_refl`, `above_trans`, `node_antisymm`, `path_mono` |
| A write goes down the order. | `store_down` |
| May-alias is a common origin below both paths. | `may_iff_common_lower` |
| No transitive relation that is sound can keep `x` and `y` apart in §6.1. | `transitive_sound_relates_x_y` |
| The backward search gives the same paths as an enumeration of all paths. | `findAlias_iff` |
| The search for a heap path gives the same paths as an enumeration. | `heapAliases_iff` |

The fixpoint strategy of §5.5, the exception rule and the query normal form are argued, not proved.
