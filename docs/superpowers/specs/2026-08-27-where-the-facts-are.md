# Where the facts are, what they look like, and why absorption does not save us

Three questions, answered from engine output rather than from inference. Every number is from the
conductor scoped arm (one entry point `WorkflowResource#rerun`, one rule, frontier flags
`anyUnrollLimit=100 / rescore / bfs`, 8 GB, 300 s IFDS budget). Every render is printed by the
engine.

New instrumentation for this round: `edgeStore premiseTrieNodes` (distinct nodes created in the
premise trie) and `edgeStore bigFact` (a top-6 hall of fame of the largest stored facts, summarised
structurally — `AccessNode.toString()` emits one line per PATH, so a 17,612-path fact cannot be
printed).

---

## 0. The three mechanisms, and what each actually did

| | claim | verdict |
|---|---|---|
| **TIFA never unrolls** | a fact reaching through an `[any]` gets the premise `p.[any]`, not concrete `p.a` | **worked.** The premise population fell 4.4x |
| **literal `[any]` matching in delta** | a premise matches only a literal edge, or the `[any]`'s zero-step child; never a synthesised one | **worked.** The premise-ladder product is gone — flat, see §3 |
| **the `[any]` unroll manager** | bounds how many concrete sequences one `[any]` origin may materialise | **idle.** 604 mints and 368 transitions in a whole run, one pot of 298 crossing `L` |

The manager is idle *because* the first two worked: literal matching deleted `getChild`'s synthesis
arm, which is the only call site that spends the pot. It is not bounding the explosion because there
is nothing left for it to bound.

---

## 1. Premises or facts? — **facts, decisively**

| | **literal (shipped)** | denotational (pre-2026-08-27) | literal + sibling absorption |
|---|---:|---:|---:|
| premise trie nodes | **119,408** | 523,493 | 76,066 |
| slots opened (premise × statement) | 423,309 | 1,871,362 | 268,270 |
| store mass (paths held) | 42,785,976 | 70,387,880 | 2,685,575 |
| **mass per slot** | **101** | 37.6 | 10.0 |
| **largest single fact** | **17,612 paths** | 2,897 | 732 |
| propagated mass | **443,273,157** | 198,793,908 | 7,130,545 |
| growths | 505,918 | 1,730,519 | 134,739 |
| **propagated per growth** | **333.28** | 49.67 | 8.87 |
| root breadth mean / max | 2.19 / 55 | 1.57 / 31 | 1.38 / 20 |
| depth gate reached | 76 | 9 | 91 |
| findings | **2** | 2 | **0** |

**There is no premise problem.** The shipped mode holds **4.4x fewer** premise trie nodes and 4.4x
fewer slots than the engine it replaced. The mass moved to the other side of the arrow: 2.7x more
mass per slot, a 6.1x bigger largest fact, and 2.2x more total propagated mass produced by **3.4x
fewer** operations.

`propagatedPerGrowth = 333` is the number that kills the run, and it is a consequence of the storage
contract, not of the analysis. The per-statement store is **not a set of facts**: it holds ONE MERGED
TREE per slot, and `add` returns *the whole merged tree* whenever the merge changed anything. That
returned tree — not the edge that was offered — is enqueued, propagated to every CFG successor, and
grafted through `concat`.

The `bigFact` hall of fame shows it directly. The top four entries:

```
#1 paths=17612 nodes=827 maxDepth=108 rootBreadth=4
#2 paths=17604 nodes=823 maxDepth=108 rootBreadth=4
#3 paths=17602 nodes=823 maxDepth=108 rootBreadth=4
#4 paths=17599 nodes=823 maxDepth=108 rootBreadth=4
```

Identical level census, identical sample paths, identical deepest prefix: these are almost certainly
one slot at four successive growths. **Each growth added about three paths and re-shipped about
seventeen thousand six hundred.**

---

## 2. What the huge facts look like

### 2.1 The shipped (literal) mode — verbatim engine output

```
edgeStore bigFact #1 paths=17612 nodes=827 maxDepth=108 rootBreadth=4
  levels (depth: nodes/withAny  edges any,covered,other):
    d0:1/0   0,0,4     d1:4/0   0,8,0     d2:8/0    0,10,0    d3:10/2  2,25,0
    d4:24/15 15,99,0   d5:61/50 50,303,0  d6:93/85  85,496,0  d7:102/100 100,475,0
    d8:86/80 80,532,0  d9:100/98 98,619,0 d10:109/107 107,586,0  d11:94/93 93,500,0
  sample paths:
    <static>(com.netflix.conductor.core.events.ScriptEvaluator).SOURCE_CACHE.MapKey.[any]/*
    <static>(com.netflix.conductor.core.events.ScriptEvaluator).SOURCE_CACHE.MapKey.Value.[any]/*
    <static>(com.netflix.conductor.core.events.ScriptEvaluator).SOURCE_CACHE.MapKey.name.[any]/*
    <static>(__spring_registry__).com.netflix.conductor.redis.jedis.JedisCommands.strings.MapValue.role.[any]/*
  deepest sampled prefix:
    <static>(__spring_registry__).com.netflix.conductor.service.WorkflowService.workflowExecutor
      .metadataMapperService.metadataDAO.conductorProperties.stack.buffer.Element.Element.inputParameters
```

Read off it:

- **The root is a static.** `<static>(__spring_registry__)` is the Spring bean registry — one global
  node every bean hangs off. `d0` is the only level with `other` edges (4 of them) and they are the
  statics; everything below is fields and collection accessors.
- **827 distinct nodes carry 17,612 paths.** A 21x sharing factor: the fact is a DAG, and `size`
  (path multiplicity) overstates the object count by that factor. Both matter — `size` is what gets
  re-propagated, `countNodes` is what occupies heap.
- **~12 structural levels, ~5 covered edges per node.** 500-600 covered edges spread over ~100 nodes
  at each of d5..d11.
- **`maxDepth = 108` is a CHARGE, not a depth.** Every node owning an `[any]` adds
  `ANY_ACCESSOR_DEPTH_CHARGE = 10`. Twelve structural levels, most of them `[any]`-owning, price at
  108 — which is why the depth gate ratchets from 3 to 76 and why it is the only thing bounding the
  population at all.
- **Where is the `[any]`? On almost every node below depth 3.** d7: **100 of 102** nodes own one.
  d10: **107 of 109**. Every sample path ends `.[any]/*`.

### 2.2 The denotational mode, same program, for contrast

```
edgeStore bigFact #1 paths=2897 nodes=186 maxDepth=15 rootBreadth=3
  levels: d0:1/0 0,3,0  d1:3/0 0,3,0  d2:3/0 0,3,0  d3:3/0 0,49,0  d4:34/0 0,98,0
          d5:46/0 0,208,0  d6:57/0 0,164,0  d7:13/0 0,80,0 ...
  sample paths:
    .workflowStatusListener.blockingQueue.Element.<get-default>/*
    .workflowStatusListener.blockingQueue.Element.MapKey.<get-default>/*
    .workflowStatusListener.blockingQueue.Element.entries.<get-default>/*
    .taskStatusListener.blockingQueue.Element.outputData.<get-default>/*
```

**`withAny = 0` and `anyEdges = 0` at every single level.** Same program, same product over
`Element` / `MapKey` / `entries` / fields, and not one `[any]` in the biggest fact.

> The product over the collection model exists in **both** modes. What literal matching adds is an
> `[any]` hanging off nearly every node of it.

And that is exactly why the sibling census reads 100%: `[any].*` at a node denotes every path below
that node, so every concrete sibling of such an `[any]` is denotationally redundant against it.

---

## 3. Where the product comes from — a correction

The natural reading of "the fact is a product" is that facts get big by accumulating siblings. **That
is measurably false.** Accumulating covered accessors into one slot the way `MethodEdgesFinalTreeApSet`
does is strictly linear:

```
ARM A -- k covered accessors merged as siblings at the root, no [any]
  k=1  size=2  countNodes=2  maxDepth=1  rootBreadth=1
  k=5  size=6  countNodes=2  maxDepth=1  rootBreadth=5
  k=6  size=7  countNodes=2  maxDepth=1  rootBreadth=6   (the 6th is [*])
  render: .f1/* .f2/* .f3/* [*]/* .f4/* .f5/*
```

`size = k + 1`, `countNodes` pinned at **2** (every open leaf is the same interned abstract node).
Seeding the accumulator with `this.[any].*` adds exactly **+1 to size and +10 to maxDepth**, and
nothing to growth.

The product lives in the **premise ladder closure** — `register → emit → refine → register` — and
that is what literal matching killed. Driving the closure from `this.[any].![m]` over a growing
alphabet:

```
literalAnyMatch = FALSE                                    literalAnyMatch = TRUE
 |alphabet|  size  countNodes  premises  growth              size  countNodes  premises  growth
     2          8       4          7       --                  2       2          1        --
     3         26      11         25      x3.25                2       2          1       x1.00
     4        106      42        105      x4.08                2       2          1       x1.00
     5        532     207        531      x5.02                2       2          1       x1.00
     6       3194    1238       3193      x6.00                2       2          1       x1.00
```

The growth factor **is the alphabet size**: `size(m) ≈ m · size(m−1)`, and the concrete-premise count
is exactly `Σ m!/(m−k)!` — 4, 15, 64, 325, 1956. Under literal matching the whole thing is flat at 2.
The n=2 accumulator, rendered:

```
.f2/*       .f2.f1/*     .f2.f1[*]/*   .f2.f1.[any]/*   .f2[*]/*     .f2[*].f1/*
.f2[*].[any]/*  .f2.[any]/*  .f1/*     .f1.f2/*         .f1.f2[*]/*  .f1.f2.[any]/*
.f1[*]/*    .f1[*].f2/*  .f1[*].[any]/*  .f1.[any]/*    [*]/*        [*].f2/*
[*].f2.f1/* [*].f2.[any]/*  [*].f1/*  [*].f1.f2/*       [*].f1.[any]/*  [*].[any]/*
.[any]/*
```

So the 17,612-path fact in §2.1 is **not** ladder growth and **not** sibling accumulation. What
remains is **summary application**: `concat` grafts the callee's delta onto every abstract leaf of the
receiver, and under literal matching that is 11.02 graft points per call and 88.59 nodes created per
call, against 2.49 and 21.65 before — measured in
`2026-08-27-literal-any-fact-explosion-anatomy.md` §4. Bigger, `[any]`-terminated facts have more
abstract leaves to graft onto, and the store hands the whole grafted tree back every time.

---

## 4. Why absorption does not save us

Sibling absorption `N{ f -> T , [any] -> S } ==> N{ [any] -> (S | T) }` **fixes the size problem
completely** — see the third column of §1: largest fact 17,612 → 732 paths (24x), store mass 16x
down, `propagatedPerGrowth` 333 → 8.9 (37x), and the run converges in ~45 s instead of dying of
memory at ~160 s.

It also finds **nothing**. Here is the whole reason, end to end, in engine output.

```
1) the fact   N{ f -> {[any] -> *} , [any] -> * }
   render      : <this>.f.[any]/*   <this>.[any]/*
   size(paths)=4  countNodes=3  maxDepth=22  rootBreadth=2

2) premises TIFA emits for it (literalAnyMatch = true)
   premise = <this>.[any].*      entryFact = <this>.[any]/*
   premise = <this>.f.*          entryFact = <this>.f/*          <-- names f

3) compressAbsorbCoveredSiblings()
   render      : <this>.[any]/*
   size(paths)=2  countNodes=2  maxDepth=11  rootBreadth=1

4) premises TIFA emits for the FOLDED fact (same mode)
   premise = <this>.[any].*      entryFact = <this>.[any]/*      <-- and that is all

5) delta(fact, premise <this>.f.*)
   BEFORE fold : [node{.[any]/*}]
   AFTER  fold : []                 <-- EMPTY: the premise no longer selects the fact

6) driven to CLOSURE, every premise the ladder ever hands out
   UNFOLDED (3):  <this>.[any].*  |  <this>.f.*  |  <this>.f.[any].*      names f? YES
   FOLDED   (1):  <this>.[any].*                                          names f? NO
```

**Premise emission is syntactic.** TIFA walks the fact's LITERAL edges: R2 over literal children, R3b
over the uncovered accessors one level below an `[any]`. The folded fact still *denotes* `f` — `[any]`
is zero-or-more covered steps — but denotation is not what the emitter reads. Delete the edge and the
name is gone; nothing ever demands `f` again.

The control in the same run isolates it to the matching reader, not to the fold:

```
   the SAME two deltas under literalAnyMatch = false:
   BEFORE fold delta(f): [node{.[any]/*}]
   AFTER  fold delta(f): [node{.[any]/*}]      <-- unchanged; getChild synthesises f back out
```

### 4.1 And the escape route is closed

If the fold is harmless under the denotational reader, run it there. Measured, with counters at the
fold's own decision point:

| | literal | denotational |
|---|---:|---:|
| store merges the fold saw carrying an `[any]` | 52% | **0.048%** |
| node visits at an `[any]`-owning node | 38% | **0.014%** |
| folds performed | 886,394 | **24** |

**In the mode where it is sound, there is nothing to fold.** The denotational reader comes with the
R3c/R4 ladder, which emits *concrete* entry facts and out-populates the `[any]`-carrying ones. A
controlled 2×2 (`2026-08-27-pot-cost-and-matching-mode.md` §6.2) separates on the PREMISES axis, not
the reader: the mixed cell — denotational reader, literal premises — is 63% `[any]`-dense and folds
1.9 M times, and its own no-absorption control already reports zero findings.

### 4.2 The one-sentence version

> Absorption's saving **is** the deletion of the literal edges: the covered branch merges into
> `[any].*`, where `*` denotes everything and the branch's mass disappears. Premise emission reads
> those same literal edges. **The names and the mass are the same object**, so there is no fold that
> keeps one and drops the other.

---

## 5. What is actually left

1. **Nothing bounds breadth.** `accessorCount()` is compared against no threshold anywhere. Root
   breadth mean 2.19, max 55.
2. **The depth gate is the only live bound, and it is a scheduling artefact.** It starts at 3, rises
   only when a unit runs out of work, and prices an `[any]` at 10 — so every `[any]`-carrying fact is
   parked on arrival and the limit ratchets to 76 over 9,264 raises. Re-pricing it (`charge 1`,
   `ceiling 9`) is still the only lever measured to converge conductor **with** its findings.
3. **The store re-propagates the whole tree.** 333 nodes shipped per growth that added ~3. Any fix
   that returns a delta rather than the merged tree attacks this directly, and nothing tried so far
   has touched it.
4. **The premise names must be recorded outside the fact.** Until R2/R3b can name an accessor without
   reading a literal edge, no fact-side compression is adoptable, however sound.
