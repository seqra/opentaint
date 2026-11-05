# Reduce field-path work with relation groups and canonical facts

4 November 2026. Investigation and design candidates. No analyzer change
is selected or implemented here. Runtime:
`52f32dd437d438aec4a700a02c18d94c31d58093`.

The [5 November follow-up](../reports/bidirectional-normal-star-subsumption-direction-policy-20261105.md)
proves the aligned NORMAL STAR relation inclusion constructively. The old
extra ANY/DEMAND result is not a semantic counterexample to that rule.
It also tests direction-limited STAR matching and states its remaining
correctness and workload limits. Runtime implementation remains unchanged.

Latest original campaign reached / completed / accepted:
Stirling-PDF **run-9 / run-8 / run-7**; Conductor **run-6 / run-5 / run-5**.
No new project performance run was made. The additional finite controls
and their scope are listed below.

Use the [field-path investigation](../reports/bidirectional-field-path-demand-witnesses-20261104.md)
for actual relation examples and diagnostic inventory limits. The main
findings are:

- STAR `inside` can add a deep MAY result from a short input. Equal-length
  and shrinking stored relations bypass the current loop gate. Field depth
  alone does not bound the number of distinct paths.
- Many reverse reader positions give the same result on an ancestor input.
  They can be processed as one matching group, without deleting `inside`.
- Same-premise MUST and MAY facts have useful prefix coverage. But the
  current C2 policy is not invariant under that coverage. Removing a covered
  leaf can remove a distinct refinement initial.
- A group of NORMAL relations can justify removal of future work only if
  it replaces the complete transfer and its future discovery. Output shape
  coverage, or unchanged demand counts, is not sufficient.

## 1. What must stay unchanged

Keep instruction transfers, sources, sinks, cleaners, field writes, aliases,
primitive rules, FULL marks, protection flags, complete ND joins, typed
ZERO/Targets, static handling, field limits and physical control ports.
Keep the ordinary caller order: saved replay, demand admission, current
summaries and subscription.

Do not disable STAR `inside` globally. The current native counterexample
has a concrete STAR/DEMAND input at the match. Removing only that cell loses
a run-5 finding by stopping in run-3. MAY and MUST also have necessary cases.
EXACT adds no strict-descendant match beyond `applicable`.

The original NORMAL ancestor STAR/FLOW cell is still not proved necessary
in isolation. This is a reason to investigate that cell, not a proof that
it can be removed. A broad switch can change both actual execution and
the loop observer's view of future use.

These candidates have different semantic scope:

| Candidate | Current → proposed | Semantic scope |
| --- | --- | --- |
| Group repeated ancestor reader applications | One native transfer/C5 query per matched output position → one per identical transfer group | Intended exact optimization in the pure observer; native equivalence must be proved |
| Canonical MUST/MAY spatial data | Keep covered leaves in some packet/order cases → retain a spatial antichain | Existing scalar coverage, but C2 and demand progress need a separate contract |
| Discharge correlated NORMAL relation families | Keep a shorter relation and its covered specializations, including derived demand → keep a proved sufficient relation basis | New relation-level reduction; current exact observer and handoff behavior can change |
| Change the loop growth gate or stop on stable groups | Bypass all equal/shrinking rows; continue with nonempty demand → a new progress policy | Major semantic change; not selected by this proposal |

No grounding-support label, raw fact history, weak cache, or extra analysis
service is introduced to make these candidates appear safe.

## 2. Can STAR inside amplify a loop?

Yes. Consider a saved NORMAL FLOW reader:

```text
I = p.f.g.* -> O = p.a.b.*
actual = p.*/FLOW, NORMAL
```

The native ancestor branch can produce `p.a.b.[any]/FLOW`, DEMAND.
The stored input and output both have two fields. `loopSummaryGrows` says
false, so the result bypasses loop demand restriction. Its actual known
output prefix is longer than the offered input prefix.

The measured Stirling inventory has a related, executed native case:

```text
same complete P = var23.Matcher.pattern.Pattern.regex.MUST/FLOW

short NORMAL output = var18.CharSequence.<rule-storage>.MUST/FLOW
long NORMAL output  = var18.CharSequence.<rule-storage>
                          .String.<string-bytes>.MUST/FLOW

reverse short view: depth1 STAR -> depth2 ANY, DEMAND; classified growing
reverse long view:  depth2 STAR -> depth2 ANY, DEMAND; classified non-growing
```

Both views produce the same result on the tested ancestor input. The
post-run-5 diagnostic inventory has 456 covered memberships with this
classification split. This is evidence of a representation-sensitive gate,
not an attribution of every run-6 operation to those 456 members.

Even a fixed depth can have large width. An instructive finite mechanism is
a prefix rewrite system over two fields, `0` and `1`:

```text
seed: 0^L.[any]/FLOW
for k = 0..L-1:
    stored input  = 1^k 0 .*
    stored output = 0^k 1 .*
```

These are binary-increment prefix rewrites. Every row preserves field
length, yet repeated application can visit all `2^L` words of length L.
An ancestor STAR match can create the deep seed from a deep identity reader.
This explains why a loop policy that checks only increasing length cannot
provide a width bound. It is a mechanism example, not a claim that a project
contains this binary-counter code.

A bounded native AP/loop-gate control executes this mechanism for L=1..8.
It visits 2..256 distinct depth-L paths. Every tested stored row is
non-growing, and the consumer-observation callback is never called. The
control injects legal NORMAL records into separate first-entry and repeat
scopes: the deep seed belongs to first entry only, and the equal-length
rewrites belong to repeat. It is not a code-to-record or complete project
reproduction.

Do not replace the gate with `actualOutputFL > actualInputFL` without a proof.
Saved shrinking transfers can need several passes before an after-block
consumer accepts the result. The selected loop design deliberately preserves
that case. A different growth or progress measure is a new analyzer policy.

## 3. Avoid repeated ancestor transfers before changing matching

The first exact target is the pure `LoopConsumerObservation`. It does no
source execution, subscriptions, alias expansion or publication. It replays
saved DATA, then performs the enclosing C5 query.

For a fixed saved premise P, a packed NORMAL output can have many positions:

```text
P -> q.a.MUST/FLOW
P -> q.a.b.MUST/FLOW
P -> q.a.c.MUST/FLOW
P -> q.a.d.MUST/FLOW
```

Their backward views all return the same constant `P.[any]/FLOW` on an
admitted strict ancestor input such as `q.*/FLOW`. A generic STAR reader
family can have the same constant-result case. The unknown suffix is lost
by the ancestor transfer in each application.

Today each matching position can repeat native transfer, packing and C5.
Instead, find whether the position group has any valid strict-ancestor
match and apply one native witness:

```kotlin
observeSavedData(actualScalar, callerOriginal, frozenView) {
    for (group in reverseReaderGroups(frozenView)) {
        // Exact owner/context, P, direction, exit and native header are fixed.
        witness = group.findNativeStrictAncestorMatch(actualScalar)
        if (witness != null) {
            value = nativeApply(witness, actualScalar, callerOriginal)
            observeEnclosingC5Once(group.exit, callerOriginal, value)
        }
        // These positions can preserve different suffixes. Keep their native path.
        for (position in group.positionsWhereActualIsAtOrBelowPremise(actualScalar))
            observeNativePosition(position, actualScalar, callerOriginal)
    }
}
```

First support plain nonzero FLOW DATA and actual STAR/MAY scalar inputs.
Keep actual exclusions, complete full-mark masks, output tail, control port,
mode and complete parent original in the group. One output geometry alone
is not a group key. Exclude unsupported ZERO/Target, ND, static and protected
variants until their effect equivalence is proved.

Use a trie existence query for strict-descendant positions; do not enumerate
all positions merely to deduplicate the equal results afterward. A first
implementation can group selected positions and measure the avoided AP/C5
work, then replace enumeration with the proved trie query.

For k matching positions in one eligible group, the transfer/C5 part changes
from k executions to one. This is an algorithmic reduction in operation count.
It is not a measured whole-program speedup. Stirling run-7's decoder performs
70.33 million saved selections, 27.05 million reverse views and 28.38 million
prepared C5 queries in the original campaign. Direct replay is part of the
selection total and is not automatically eligible. Measure the actual group
widths and saved operations before predicting a total improvement.

Do not confuse output-position grouping with historical record-object
grouping. A separate post-run-5 diagnostic census groups 1,165 eligible
nonstatic FLOW record objects into 1,021 exact premise/header groups, with
at most two objects per group. That reduction alone is too small to explain
or resolve the main workload. Multiple output positions within one record
are a different dimension.

The complete post-run-5 loop-repeat inventory has 951 strict-descendant
positions across 251 reverse-reader header groups for the constrained
decoder context, with maximum width 33. Its backward adjacent before-block
inventory has 25 positions across seven groups, with maximum width 10.
These are stored opportunities under hypothetical legal root inputs, not
observed query frequencies. The post-run-6 saved inventory was not captured,
so do not extrapolate these widths to every run-7 observer query.

The observer does not run a growth test per adjacent saved position. Actual
loop-body replay does. If this grouping is later used for real body replay,
retain separate growing and non-growing classes and both resulting paths.
Do not let one witness arbitrarily select the other class's behavior.

Native controls confirm four descendant views giving four identical full
outputs for both generic STAR and FLOW-MUST records on ancestor STAR or
MAY inputs. At-path results and excluded-first-field controls remain
distinct. The [source, outputs and manifests](../reports/data/bidirectional-star-inside-loop-grouping-controls-20261104.json)
record the bounded test domain. A universal grouping theorem and a native
trie-selection proof are still required before implementation.

## 4. Use the same prefix machinery for MUST and MAY data

Fix the complete premise P, owner, direction, exact entry/exit, base, layer
and compatible headers. Then these are useful scalar laws:

```text
MUST:
    P -> x.u.[any-taint]/FLOW, NORMAL
      covers
    P -> x.u.r.[any-taint]/FLOW, NORMAL
    if the ancestor exclusion admits r and its mx covers the child mx.

MAY:
    P -> x.u.[any]/FLOW, DEMAND
      covers
    P -> x.u.r.[any]/FLOW, DEMAND
    under the ordinary same-layer mark-coverage rule.
```

The traversal can be shared. The tail-specific coverage rule cannot be
erased. MUST does not generally cover EXACT or STAR under the selected
scalar law. A MAY demand does not establish a NORMAL uniform-taint witness.
Concrete protected memberships require protected coverage.

Canonicalization must handle both:

```text
one arriving packet:      {x.ANY, x.f.ANY} -> {x.ANY}
later broader arrival:   old{x.f.ANY} + new{x.ANY} -> {x.ANY}
```

For MUST, keep its field-exclusion descent guards. A shared DAG must be
visited with the relevant ancestor coverage state; sharing one node does
not mean that it has the same covering ancestors at every path.

Measured diagnostic opportunities:

| Inventory | Covered memberships |
| --- | --- |
| Stirling run-5 current NORMAL MUST | 919 / 1,220 (75.33%) |
| Stirling post-run-5 saved NORMAL MUST | 1,057 / 1,330 (79.47%) |
| Stirling run-7 current NORMAL MUST | 2,830 / 3,490 (81.09%) |
| Stirling run-6 current DEMAND ANY | 3,294 / 7,795 (42.26%) |

Of the last row, 3,004 covered memberships coexist with their ancestor
inside the same packet. These are membership counts in the diagnostic,
not application counts or predicted time savings. Historical indexed
records also need an effective canonical view; compacting only new current
packets does not remove old replay alternatives.

### 4.1 Do not silently remove refinement information

Native controls expose a design issue in the current C2 policy:

```text
demand Dc = x.[any]/FLOW
MAY actual packet: {x.[any], x.f.[any]}, DEMAND

C2 with both:   {x.[any]/FLOW D, x.f.*/FLOW N}
C2 root only:  {x.[any]/FLOW D}

MUST actual packet: {x.MUST, x.f.MUST}, NORMAL

C2 with both:   {x.MUST/FLOW N, x.f.*/FLOW N}
C2 root only:  {x.MUST/FLOW N}
```

Thus a spatially covered leaf can cause a distinct canonical initial.
The current packed leak is not a promised feature, but it can carry
refinement that depends on arrival order. Prefix subtraction already
removes some such leaves across packets.

A complete antichain design must separate two questions:

```text
data coverage:       does this leaf add a possible flow?
refinement coverage: does it add a required C2 initial or paired C5 image?
```

One conservative design keeps a canonical data view and preserves required
refinement labels at existing admission/handoff boundaries. Another redesigns
C2 so coverage-equivalent data has complete equivalent refinement behavior.
The latter is a major semantic change. Neither design is implemented or
silently assumed here. Do not add an unbounded raw-history store to avoid
specifying this contract.

The [five native controls](../reports/data/bidirectional-grouped-demand-c2-controls-20261104.json)
contain exact admission patterns and layers, source, commands and pins.
They validate the C2 difference, not an end-to-end antichain proof.

## 5. Group demand by the complete relation, not independent endpoints

Yes, previous demand, current NORMAL relations and current unresolved demand
can be analyzed together at the handoff. The objective is to discharge a
task because retained transfers handle every required case. It is not to
stop merely because a demand repeats.

An attractive first relation family is:

```text
NORMAL S: p.u.*   -> q.v.*
NORMAL L: p.u.r.* -> q.v.r.*
```

The same residual r occurs on both sides. Every concrete pair in L is in S:
choose S's suffix as `r + suffixOfL`. Growth classification is identical,
because r adds the same counted length to both endpoints. This is a
relation-level law; isolated NORMAL STAR output prefixes do not have that
fact-subsumption law.

The Conductor trace contains actual examples of this family. It also
contains real growing writers `p.* -> q.f.*`, which are not covered by
`p.* -> q.*`. Likewise, `p.f.* -> q.*` removes f and is not covered by
identity. No universal identity-removal heuristic is justified.

For an ancestor STAR input, L can produce an extra ANY/DEMAND approximation
while S keeps NORMAL correlation. This does not disprove concrete relation
inclusion. It means that suppressing the extra demand is a new relation-level
discharge rule. Prove its future source, Target, admission and observer
coverage; do not cite ordinary fact subsumption as that proof.

A simple group algorithm is:

```kotlin
atSuccessfulHandoff() {
    kept = freezeAvailableNormalTransfers()
    for (group in groupUnresolvedRelationsByExactInterface()) {
        candidate = findNormalRelationCover(group, kept)
        if (candidate != null && provesCompleteReplacement(candidate, group))
            omitFromNextDemand(group)
        else
            retainCurrentHandoff(group)
    }
}
```

`provesCompleteReplacement` must preserve complete premises and paired
routes, actual admission/delivery, output/layer/protection, and every required
source/Target/control effect. Its witness must use retained NORMAL transfers
only. Two removed groups cannot justify each other.

Use previous demand as a candidate index and proof context. Do not union
stale demand back into the current frontier. Do not implement a second
general analyzer at the barrier; start with a small proved relation family.
Unknown cases keep their ordinary next demand.

### 5.1 Two reasons ordinary prefix coverage is insufficient

First, a deeper demand can make more progress:

```text
actual: x.f.g.$/T, NORMAL

Dc = x.[any]/T:    C2 emits x.f.*/T,   DEMAND
Dc = x.f.[any]/T:  C2 emits x.f.g.$/T,  NORMAL
```

Second, C5 also depends on `FL(Dp)+1`. A shallower output selector may cut a
result to DEMAND where a deeper selector retains it NORMAL. Do not combine
the entry permission from one demand row with the exit permission or budget
from another row.

The selected restriction proofs already have a case where one precise
NORMAL result and another row's capped DEMAND result both remain. Removing
the latter is not licensed by the current row-union contract. A transition
replacement theorem must justify the deliberate change.

The [group-discharge audit](../reports/data/bidirectional-demand-group-discharge-audit-20261104.json)
contains six finite countermodels, eight positive closure checks, 378
correlated-STAR checks, source snippets and existing proof receipts.
These checks identify candidate laws. They are not a general Lean or native
transition proof. A sufficient finite proof shape is that each removed whole
rule's outputs and effects are derivable from its complete premise using
retained rules only. Native C2/C5 and driver adapters remain required.

## 6. Suggested investigation order

1. **Group strict-ancestor reader applications in the pure observer.** This
   avoids repeated matching/application/C5 for identical results. Measure
   group width and avoided operations. It preserves matching and demand.
2. **Design MUST/MAY antichains with an explicit refinement contract.** The
   inventories show substantial covered geometry. Verify both record
   directions, C2 progress, C5 budgets, exclusions and observer behavior before
   removing it from all stores or handoff views.
3. **Try correlated NORMAL relation discharge.** Start with empty E/mx,
   singleton nonstatic FLOW STAR relations and identical correlated residuals.
   Add a constructive relation and transition proof before pruning next demand.
4. **Reassess the loop progress gate with operation traces.** Identify real
   ancestor-created results, equal-depth rewrite width and bypass outcomes.
   Do not infer uselessness solely from depth, repeat-only support or stable
   demand counts.

After selection, follow [proof-guide.md](../../spec/proof-guide.md) and
[impl-proposal-guide.md](../../spec/impl-proposal-guide.md). Report any major
semantic change before implementation. Measure unique output and continuation
groups, actual instruction packets, saved matches/views, C2 labels, C5 outputs,
Target/source permissions, demand frontiers, memory and latest reached run.
Keep main performance measurements separate from bounded diagnostic controls.
