# Why the later backward runs do much more work

Date: 1 November 2026. Runtime:
`c4a71246519ee5432879ce82518823f1703f3aa4`.
The current HEAD adds documentation only. This investigation uses the
closed FULL, 16 GiB campaign, with field limits `1,1,2,3,…`.

Stirling-PDF reached **run-8**, completed **run-7**, and accepted its
run-7 report. Conductor reached **run-4**, completed **run-3**, and accepted
its run-3 report. Both stopped on timeout, without OOM.

## 1. Answer

The small demand frontier does not bound the work inside an admitted
method. Backward transfer expands one required result into its possible
producers. Field transfers can add prefixes repeatedly. Call processing
also expands reverse aliases before callee demand selection. Some paths
are different requirements; other paths converge to the same requirement.
The implementation can execute the shared call stages again for those
convergent paths before output storage rejects the duplicate.

Forward transfer has a different shape. It starts with a particular
producer, consumes field prefixes, and can transfer a packed result in one
operation. Its NORMAL identity call results also skip the alias branch.
Thus fast forward runs before and after a slow backward run are consistent
with the current algorithm.

These are reproducible mechanisms in the production AP and call engine.
The project evidence confirms much more backward call work and identifies
its hot paths. The saved recordings do not contain the method/fact values
needed to assign an exact share of each project timeout to each mechanism.
In particular, the native-record scalarization below is a real multiplier,
but it is not the principal sampled Stirling lane.

## 2. What the completed runs show

| Project / run | Direction / limit | Engine, s | Incoming explicit demand rows | Incoming Target count | Call offers | Saved matches |
|---|---|---:|---:|---:|---:|---:|
| Stirling run-5 | F / 4 | 3.496 | 26,134 | 80 | 120,742 | 248,037 |
| Stirling run-6 | B / 5 | 312.047 | 9,848 | 66 | 2,734,302 | 2,846,347 |
| Stirling run-7 | F / 6 | 3.528 | 9,286 | 55 | 163,695 | 438,948 |
| Stirling run-8 | B / 7 | 716.925, timeout | 12,895 | 73 | 6,455,872 | 6,564,500 |
| conductor run-3 | F / 2 | 14.714 | 153,939 | 360 | 564,162 | 647,594 |
| conductor run-4 | B / 3 | 1,009.021, timeout | 21,757 | 1,483 | 4,373,189 | 7,978,859 |

Incoming counts are from the preceding completed frontier. They describe
boundary permissions, not the number of facts processed. Demand rows
include typed control rows. Target counts are a separate diagnostic, not
a disjoint population to add to demand rows. Saved matches count callbacks,
not distinct resulting facts. Timeout rows contain partial-run counters.

Stirling run-6 has 22.6 times the call offers of run-5 and 16.7 times those
of run-7. It takes about 89 times their engine time. The operation count
increases, and less work runs in parallel:

| Stirling phase | Estimated allocation, GiB | Approximate process CPU, s | Mean process cores |
|---|---:|---:|---:|
| run-5 | 20.942 | 14.78 | 4.92 |
| run-6 | 950.702 | 383.07 | 1.23 |
| run-7 | 15.457 | 30.90 | 7.71 |
| run-8, incomplete | 2,160.443 | 1,454.93 | 2.03 |

Short forward CPU windows use nearest resource samples, with about one
second of possible boundary error. Allocation weights estimate cumulative
allocation, not live heap. One worker has 97.3% of run-6 Java execution
samples and 91.3% of run-8 samples. More parallel capacity alone cannot
remove the work concentrated in that worker.

Run-6 has 7,333,906 CFG-delivery cache hits and 36,395 searches. Run-7 has
440,157 hits and 37,141 searches. The structural search count is similar;
delivery work grows greatly. This is not repeated BFS construction.

Run-6 ends with 18,832 compact and 46,292 full scalar-store cells. Run-7
has 77,350 compact and 76,560 full cells. A cell can contain a packed field
tree with many memberships and many successive deltas. Fewer cells do not
imply fewer operations. Delivery occurs only after a fresh post-statement
delta, so the millions of deliveries cannot all be identical stored outputs.

## 3. Where the demand bounds apply

The selected call pipeline is:

```text
process the reversed call's binding / alias / action stages
  reach the callee stage
    replay saved NORMAL summaries on every original offer
      apply each match and resume the caller stages
    C2: find current admitted initials from demand
    if none: skip current callee analysis and subscription
    otherwise: replay / subscribe to current summaries

at method summary publication:
  C5: intersect the complete summary with paired demand
```

C2 prevents unnecessary current callee starts. It does not undo the work
done before it. C5 selects method results after internal propagation. It
does not constrain every intermediate fact to an endpoint demand path.

For Stirling run-6, 2,704,176 of 2,734,302 call offers have empty current
demand: **98.90%**. Run-8 has 6,422,511 empty offers: **99.48%**. They still
run saved-summary replay, and the preceding reverse call stages have
already run. This explains how a small current-demand frontier can coexist
with millions of call offers.

Replaying saved summaries before demand is the selected behavior. Empty
current demand is not permission to delete that replay. A NORMAL result
can be useful without starting a new callee analyzer.

Only run-2 can use the run-1 static-completion graph. These three slow runs
use local demand lookup. Static closure construction and terminal graph
search are not their cause. Ordinary static facts can still be processed;
the recordings do not provide a static/nonstatic fact census here.

## 4. A fixed one-row frontier can cause exponential backward field work

The reduced control uses ordinary field reads in a loop:

```java
class Node { Node left, right; }

Node walk(Node p) {
    Node x = p;
    while (moreSteps()) {
        if (pickLeft()) x = x.left;
        else            x = x.right;
    }
    return x;
}
```

Treat the Boolean choices as unconstrained; both branches are possible.
The lowered CFG control runs the production AP and method engine with one
admitted concrete EXACT/DEMAND key. It selects one outgoing boundary-demand
leaf. It does not run a JVM prescan or the JVM alias enumerator.

```text
Backward input: ret.$/T, DEMAND

0 inverse reads: x.$/T
1 inverse read:  x.left.$/T OR x.right.$/T
2 inverse reads: x.left.left.$/T OR x.left.right.$/T
                OR x.right.left.$/T OR x.right.right.$/T
...
At the field budget: deeper requirements become bounded ANY demands.
```

The inverse reads add concrete prefixes. The engine processes each
generated delta. C5 selects the wanted endpoint after this internal work.
The control results are:

| Backward field limit | Admitted keys | Selected outgoing demand leaves | Raw summary leaves | Processed items |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 3 | 21 |
| 3 | 1 | 1 | 15 | 81 |
| 5 | 1 | 1 | 63 | 321 |
| 7 | 1 | 1 | 255 | 1,281 |

The raw leaves follow `1 + 2 + … + 2^L = 2^(L+1) - 1`. They include the
zero-read route and the bounded boundary layer. Most are different paths;
an exact duplicate set cannot remove them.
All raw edges are DEMAND. Depths 0 through L-1 have EXACT tails, with
`2^d` leaves at depth d. Depth L has `2^L` ANY leaves. There is no STAR
tail in this backward control.

The corresponding forward control has one NORMAL uniform-taint input:

```text
Forward input: p.[any-taint]/T, NORMAL
x = p:        x.[any-taint]/T
x = x.left:  x.[any-taint]/T
x = x.right: x.[any-taint]/T
```

Reads consume the selected prefix. The broad uniform image stabilizes.
At limits 2, 4, and 6 the separate forward control stays at 17 processed
items and two raw summary leaves. It reproduces a stable forward image
while the backward query grows. The probe does not execute a full driver
sequence of adjacent iterations. It does not fit the project times to a
theoretical branching factor. The two directions start with different
directional requirements; this is not an equal-input speedup benchmark.

Later-run queues dispatch generated deltas separately. The special FULL
batch worklist is run-1 only. Trie traversal already memoizes shared nodes;
the problem in this control is the generated requirement space, not a
naive repeated traversal of a shared DAG.

## 5. Backward call paths also repeat an identical shared suffix

Forward call processing expands aliases after callee application. Its
MemoryEffect guard skips aliases for a NORMAL identity result. A DEMAND
result can bypass this forward guard.

Backward plan construction reverses ALIASES before the callee stage,
removes the forward guard, and can add a direct PASS_OVER route. Thus
several alias paths can map a single broad requirement to the same bound
callee fact before saved replay and C2.

An illustrative alias family is:

```java
Box x = obtainBox();
holder.a = x;
holder.b = x;
// ... more aliases to x ...
identity(x);
```

At the call, the reduced control supplies:

```text
Backward actual: holder.[any]/T, DEMAND

inverse alias holder.a.* -> arg0.*: arg0.[any]/T, DEMAND
inverse alias holder.b.* -> arg0.*: arg0.[any]/T, DEMAND
...
```

Each route can execute the same action/callee suffix. The production
`flow` stack has no invocation-wide set of visited `(point, state)` values.
Its post-statement store rejects duplicates after the suffix completes.
The scalar reference evaluator does have a point/item seen set.
The control supplies the lowered alias edges directly and uses an ordinary
unresolved identity transfer. It measures repeated shared-stage execution;
it does not measure the JVM alias enumerator or a real project's callee
replay count.

The production-path control gives:

| Alias paths | Backward call finishes | Backward stored output leaves | Forward NORMAL identity finishes |
|---:|---:|---:|---:|
| 1 | 2 | 2 | 1 |
| 2 | 3 | 2 | 1 |
| 4 | 5 | 2 | 1 |
| 16 | 17 | 2 | 1 |
| 64 | 65 | 2 | 1 |

The additional backward finish is the pass-over route. All alias routes
produce the same callee-side MAY image. The forward control has one stored
leaf at all widths. This is avoidable repeated work, separate from the
distinct field paths in section 4.

Safe coalescing must retain full premise, layer, protection, call point,
identity classification, pending demotion, and observation effects. Plain
Facts equality omits protection. A set keyed only by that equality would
not be a correct fix.

## 6. Reverse saved records lose the forward packed transfer

This method naturally produces a packed FLOW result:

```java
Pair dup(Box p) {
    Pair r = new Pair();
    r.a = p;
    r.b = p;
    return r;
}
// NORMAL FLOW record: p.* -> {ret.a.*, ret.b.*}
```

Same-direction replay applies the packed conclusion. Opposite-direction
replay enumerates scalar reversed exit views:

```text
Backward actual: {ret.a.h.[any]/T, ret.b.h.[any]/T}, DEMAND

view 1: ret.a.*/FLOW -> p.*/FLOW
        result: p.h.[any]/T, DEMAND
        resume caller actions / binding / cut / output storage

view 2: ret.b.*/FLOW -> p.*/FLOW
        result: p.h.[any]/T, DEMAND
        resume the same suffix again
        output storage finally rejects the duplicate
```

`seenViews` retains both views because their premises differ. It does not
coalesce their equal applied results. The control confirms two reverse
view callbacks and two call finishes, with one stored result. Forward
replay has one packed callback and one finish, retaining both output paths.
Both views retain the same complete caller original. The protected-input
variant also passes and retains its mask. Any coalescing must preserve
mask upgrades and separate NORMAL/DEMAND memberships.

There is also repeated selection. For every offered input leaf, the
reverse reader scans the candidate record's complete exit leaves before
prefix filtering. With L input leaves and M record leaves, this can require
L*M leaf visits. In the N-field convergent example, that is N² visits and
N caller-suffix executions. Same-direction replay has a per-offer record
seen set and applies the packed record once.

This can amplify backward work, but its project share has a bound from the
captured stacks: saved replay, including its callbacks, appears in about
15.3% of Stirling run-6 Java samples and 13.0% of run-8. It cannot by itself
explain all of either slow run.

## 7. Which mechanisms the projects actually exercise

### Stirling run-6 and run-8

Deep-stack classification finds:

| Captured Java scope | run-6 | run-8 |
|---|---:|---:|
| Direct call processing outside saved replay | 81.3% | 83.9% |
| Saved replay, including its callbacks | 15.3% | 13.0% |
| Ordinary non-call statement processing | 2.8% | 2.6% |

About 79% and 83% of edge-store samples are inside that direct call
processing scope. Thus the principal captured lane is the reversed call
plan, not current-summary notifications and not saved replay alone.
The existing stages expand requirements, run action chains, and reach
output storage before most current-demand lookups reject callee starts.

The per-stage kind and fact values were not recorded. These stacks do not
establish how many of the real call paths are inverse aliases, bypasses,
source branches, or wide field images. The controls demonstrate the exact
implementation mechanisms; they do not measure their real alias widths.

### Conductor run-4

Here the largest lane is current-summary delivery. `onDelivery` appears in
72.3% of the whole run-4 Java samples and 93.7% in its final 60 seconds.
Line-specific sampling identifies ordinary FLOW-conclusion grafts, not
source-to-ZERO discharge.

Backward inversion can turn selective producers into a common-result join:

```java
Box pick(Node p, int k) {
    if (k == 0) return p.left;
    if (k == 1) return p.right;
    return p.parent;
}
```

```text
Forward relations use selective premises:
  p.left.* -> ret.*
  p.right.* -> ret.*
  p.parent.* -> ret.*

Backward relations share the result premise:
  ret.* -> {p.left.*, p.right.*, p.parent.*}

Caller actual {ret.a.*, ret.b.*} can produce:
  {p.left.a.*, p.left.b.*, p.right.a.*, p.right.b.*,
   p.parent.a.*, p.parent.b.*}
```

The current input index scans descendant actual paths for a broad
FLOW/STAR premise. Every fresh publication reads the matching cumulative
caller groups and then applies the relation and caller suffix. This
repeatedly joins producer alternatives, actual suffixes, and caller origins.

The run-4 counters support this shape:

| Counter | Forward run-3 | Backward run-4 |
|---|---:|---:|
| New caller groups | 190,754 | 51,427 |
| New input-path index postings | 246,460 | 875,749 |
| New postings / new group | 1.29 | 17.03 |
| Accepted deltas that grow existing groups | 13.3% | 93.5% |
| Java samples at FLOW graft lambda | 5 / 1,100 | 1,619 / 14,278 |

This is structural membership growth, not proof that every admitted path
is semantically necessary. Existing-group growth can also add marks or
protection; the separate postings counter measures new indexed positions.
Postings/group is a cumulative creation ratio, not a retained-tree census.
The source accumulator preserves exact actual
positions. It is not an AP-prefix-subsuming set. The recordings do not
identify the real `pick` method or its field names; the code above is a
reduced legal example of the sampled mechanism.

## 8. What these results rule out

There is no evidence that a small number of demand lookups are individually
slow. The demand-query family is below 0.4% of Stirling run-6/run-8 Java
samples and about 2.0% of conductor run-4 samples.

There is no proof of an infinite loop. The reproduced controls terminate,
but their backward path counts grow exponentially with the field limit.
Stirling run-6 does finish, and conductor completes some long delivery
handlers during run-4. Field limits bound depth; they do not make the
number of paths small.

Ordinary and protection deltas are already incremental. The implementation
does not return the whole merged tree for every protection change. Trie
walks also memoize shared nodes. Those possible explanations are ruled out
by the current source.

Naive pruning of covered caller inputs is unsafe. The extra control stores
`ret.[any]/T` and then `ret.f.[any]/T` in the same caller group. Ordinary
AP subsumption says the ancestor covers the child, but C2 against an ANY
demand produces different refinement images: the root ANY image and the
child STAR image. Removing the child solely from ordinary AP coverage
would change initial admission.

The whole issue is not GC. Stirling's late run-8 capture has substantial
native GC CPU, but it is processing the allocation generated by the
expanded work. Conductor has about 5 GiB used heap after late young GCs
while still spending a long time in delivery. Neither has an OOM.

## 9. Implication for the next design

The main design target is to avoid producing or executing irrelevant
backward preimages before the gates that can reject them. It is not enough
to make demand lookup faster or count the final demand rows.

There are two different reductions to design:

1. Preserve set-level call processing: coalesce equal intermediate states
   and applied reverse-record results before the shared action suffix.
   This removes convergent duplicate work without deleting a distinct
   requirement. Keep replay on every original offer.
2. Limit the inverse requirement space with a proved boundary/observation
   feasibility test. In the read-only loop control, a nonempty prefix can
   never return to the sole permitted empty-path endpoint, because every
   reverse read only adds fields. Such a branch can be rejected early.
   This early rejection is valid in the control's all-DEMAND, read-only
   scope without internal observations. A general method needs field-write,
   callee, source, and Target effects in that proof. It must also preserve
   raw NORMAL records that are persisted before C5, including records not
   selected for current publication. C5 alone, at method publication, is
   too late to save the already performed internal work.

The second target can reduce distinct path work. The first cannot remove
the 255 different paths in the loop control. Conversely, field-path pruning
alone does not fix the 64 identical alias suffixes. These must not be
presented as one cache optimization.

No analyzer modification or project rerun was made for this investigation.
Six external production-path controls pass. The data files retain the
counter calculations, source bindings, probe code, and evidence limits:

- [Per-run work counters](data/bidirectional-backward-work-amplification-20261101.json)
- [Conductor causal evidence](data/bidirectional-conductor-backward-causal-analysis-20261101.json)
- [Call-stack evidence](data/bidirectional-slow-backward-causal-analysis-20261101.json)
- [Reduced production-path controls](data/bidirectional-backward-design-controls-20261101.json)

The exact project AP shapes and per-stage branch widths remain the next
measurement gap. Any claim that one of these changes alone removes a
specific percentage of a project timeout needs that measurement.
