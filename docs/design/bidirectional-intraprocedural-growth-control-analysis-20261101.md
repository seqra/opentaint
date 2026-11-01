# Intra-procedural path growth: candidate controls

Date: 1 November 2026. Status: design analysis, not a selected specification.
No analyzer implementation change or new project run is included.

Reference runtime: `c4a71246519ee5432879ce82518823f1703f3aa4`.
Latest reached/completed/accepted iterations: Stirling-PDF **run-8/7/7**,
conductor **run-4/3/3**, thingsboard **run-2/1/1**, OWASP **run-5/5/5**.

Read this with the [backward-work investigation](../reports/bidirectional-backward-work-amplification-20261101.md)
and the selected [summary restriction spec](../../spec/demand-relative-summary-restriction.md).
The earlier investigation describes raw NORMAL persistence in its measured
runtime. That is not a requirement for this new analysis: the selected
summary spec replaces it with admitted-only persistence.

## 1. What the evidence establishes

Loops are a confirmed source of distinct backward requirements. They are
not yet proved to be the largest source in the slow projects.

```java
Node walk(Node p) {
    Node x = p;
    while (choose()) {
        x = choose() ? x.left : x.right;
    }
    return x;
}
```

Backward transfer adds fields. At a repeated point it can generate:

```text
x.$/T
x.left.$/T, x.right.$/T
x.left.left.$/T, x.left.right.$/T, ...
```

These paths differ. The existing post-statement deduplication cannot
remove them as equal facts. The production reduced control has 3, 15,
63, and 255 raw leaves at field limits 1, 3, 5, and 7, with one admitted
key and one selected outgoing demand leaf. It terminates at each fixed
limit; this is not evidence of an infinite loop.

An identity loop already stabilizes under the current output store. The
important condition is a cycle that grows the fact image, not simply a
CFG back edge. Recursion can cause related inter-method growth. Acyclic
branching and call composition can also create wide results.

The project profiles establish other multipliers. Stirling run-6/run-8
spend 81.3%/83.9% of Java samples in direct reversed-call processing outside
saved replay. Conductor run-4 spends 72.3% in current-summary delivery.
Those samples do not record the originating CFG cycle or AP values.
They cannot assign a percentage of project cost to loops.

## 2. Candidate A: repeated-path widening

The proposed local rule can be stated as:

```text
At one program boundary:
    an existing compatible path is a.x
    a new path is a.x.y.x
    retain the new edge's original premise
    collapse its conclusion to a.x.[any], DEMAND
```

This can stop repeated path growth earlier than the global field limit.
It is a semantic abstraction change. A NORMAL candidate that loses its
suffix must become DEMAND. Keep its full mark and protection.

Two limits matter:

1. Repeated accessors do not prove repeated execution. Straight-line code
   can read `p.left.right.left`. A field identity is not a CFG-cycle identity.
2. A permanent collapse point can prevent later refinement. If every run
   maps `p.left.right.left` to `p.left.[any]`, a larger global field limit
   does not expose the lost suffix. A finite real path can stay provisional.

Thus a full design needs a per-iteration progress rule, not only a
repeat-pattern test. It also needs a canonical merge policy: arrival order
must not decide whether a precise candidate survives or is widened.
Retraction of already published work does not undo its earlier effects.

Widening at a CFG cycle cut point makes the triggering reason clearer.
It still needs the progress argument. This candidate is not selected here.

## 3. Candidate B: previous-run local fact guidance

The useful part of the second idea is to give body propagation a local
budget before it reaches the summary gate:

```text
guide = previous run's conclusion envelope at the same physical boundary
        // union over original premises; do not retain all old edges

current A -> B
    -> choose a local field budget from guide
    -> collapse B with the existing field cut
    -> current post-statement store
    -> propagate its fresh delta
```

Ignoring old premises for budget selection is reasonable. It makes the
guide less restrictive and can save substantial state. It must not erase
the current A, weaken a current ND premise, or combine caller support.
The current edge remains `A -> collapse(B)`.

For a fixed guide with depth zero, an allowance of one new field can
stop the binary loop at a shallow prefix family. This controls body work,
whereas summary-only restriction runs after that work has occurred.

### 3.1 Start with collapse, not a new admission filter

The simplest candidate is a budget-only policy:

```kotlin
fun collapseAt(boundary, fact): Facts {
    val previousDepth = previousEnvelope.maxFieldDepth(boundary, fact.base)
        ?: return existingGlobalCut(fact)
    val budget = min(run.fieldLimit, previousDepth + 1)
    return existingFieldCut(fact, budget)
}
```

This maximum is local to the method, physical boundary, and base. It is
not a maximum over the whole method or project. It does not inspect or
copy an old premise or mark. A branch-specific path-trie guide can later
give tighter budgets; it needs a separately specified matching and union
rule. The maximum-depth candidate avoids that extra policy for now.

If old depth already reaches the preceding global limit, `+1` can equal
the new global limit and save no work. This is a useful measurement to
make before selecting the policy. A shallow forward envelope followed
by a deep backward requirement is the promising case.

A missing method/base/point guide means unknown, not impossible. Use the
ordinary global limit there. This policy does not reject a new fact merely
because the old run did not store a matching fact.

### 3.2 Literal initial emission is not fact collapse

Initial emission selects a method template. It can change the mark slot,
reject a non-refining offer, or emit a more specific provisional location.
Those actions need not be correct for a continuing local fact.

```text
old guide:        x.[any]/FLOW
current result:   x.f.g.$/T, NORMAL

literal C2 image: x.f.*/FLOW
desired collapse under a one-field budget:
                 x.f.[any]/T, DEMAND
```

The current concrete T must remain T. The lost suffix must cause DEMAND.
Similarly, the later-run C2 rule that rejects a descendant answer to a
requested STAR is not a general reason to discard local propagation.

Reuse the field-counting and first-new-field ideas. Use the existing
field cut for the actual collapse. Do not use the whole C2 operation as
an unreviewed local transfer function.

### 3.3 Compare the same physical side of an instruction

Current storage holds results after the statement in the active direction.
Opposite runs therefore use opposite physical sides:

```text
Forward OUT(S)  corresponds to Backward IN(S)
Forward IN(S)   corresponds to Backward OUT(S)
```

For a mutable-local instruction:

```java
// Forward input:  x.f.$/T
x = x.f;                       // S
// Forward output: x.$/T
```

Backward processing starts with `x.$/T` after S and produces `x.f.$/T`
before S. Testing that result against forward OUT(S) uses the wrong
physical boundary. This is an abstract instruction example, not a claim
about the exact register allocation of a captured JVM method.

The new guide needs an explicit IN/OUT boundary convention. CFG delivery
also skips neutral statements, so absence of a post-statement row is not
proof that no fact crossed that program point. Preserve sparse-envelope
coverage or use the unknown fallback. Do not retain both complete old
method stores simply to solve this alignment issue.

## 4. Where to place a local gate

Keep the selected output organization:

```text
process S and its required observations
    -> collapse completed output for S
    -> edges.add(S, currentOriginal, collapsed)
    -> deliver only the fresh delta to successors
```

Store at S, not at its successors. Identity output must use the same gate
so it cannot bypass the policy. Keep current layer/protection upgrade
handling. A lost suffix uses MAY/DEMAND and empty field E; marks, FLOW mark
exclusions, and protection follow the existing cut operation.

This can reduce repeat trips around a CFG cycle and later call inputs.
It does not coalesce equal branches inside a single call's shared action
suffix. A call-stage policy would need stage boundaries and preserve all
current observation/resume state. Do not claim that a post-statement gate
alone removes the measured intra-call duplicate work.

ZERO and Target remain typed controls, not depth-zero DATA. Local writer
effects and accepted source callbacks must not disappear due to output
deduplication. Summary admission still uses the separately selected paired
restriction; a local budget guide does not replace it.

## 5. Finite model of the possible work reduction

An executable word-generation model repeatedly prepends `left` or `right`
and applies the existing-style overflow cut. The set keeps exact and MAY
states separately. It has the following fixed points:

| Local budget | Distinct prefixes | Annotated states | Transfer offers |
|---:|---:|---:|---:|
| 1 | 3 | 5 | 10 |
| 3 | 15 | 23 | 46 |
| 5 | 63 | 95 | 190 |
| 7 | 255 | 383 | 766 |

This is a small language model, not a modified analyzer test or a project
benchmark. Its exact/MAY states differ from the production control's
raw-leaf accounting. The prefix count demonstrates the opportunity:
bounding depth at the cycle point can avoid generating deeper paths.

The model is reproducible with:

```python
from collections import deque

def fixed_point(budget):
    seen = {((), "exact")}
    queue = deque(seen)
    offers = 0
    while queue:
        path, tail = queue.popleft()
        for field in ("left", "right"):
            offers += 1
            child = (field,) + path
            result = ((child, tail) if len(child) <= budget
                      else (child[:budget], "any"))
            if result not in seen:
                seen.add(result)
                queue.append(result)
    return len({p for p, _ in seen}), len(seen), offers
```

## 6. Recommended next design scope

Develop previous-run local guidance first. Start by assessing loop-header
or cycle-cut boundaries in backward runs. Every CFG cycle must cross a
selected gate to obtain a cycle-growth bound; one arbitrary header per
large irreducible component is not automatically sufficient. All-point
guidance is a separate space/work tradeoff.

Before selection, prove:

- local over-approximation, retained original/marks/protection, and no
  new NORMAL result from a lost suffix;
- physical-boundary and neutral-delivery alignment;
- missing-guide behavior, multiple guide handling, and stable output
  independent of arrival order;
- progress across alternating runs, including two-field construction/read
  helpers, conditional sources, exact demands, native replay, and Targets;
- reference equivalence for any sparse or shared guide representation.

The method actors currently release MethodEdgeStore during freeze. A new
guide must be extracted or accumulated before that release. Keep only the
required premise-free projection and account for its peak size. Reusing
the whole old store would retain the state that this work aims to reduce.

The next workload measurement should assign **fresh path growth** and
transfer work to CFG cycle components, separately from direct call-stage
fan-out and equal-result convergence. Also measure the fraction of local
points where `previousDepth+1` is below the new global limit. This will
show both whether loops dominate and whether this local policy has room
to reduce the real workload.

Neither candidate has a general refinement-progress proof yet. This note
does not select a permanent widening rule or authorize a runtime change.
