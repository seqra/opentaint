# Demand trie for loop restriction

**8 November 2026 integration:** apply the selected
[own-ZERO loop bypass](edge-subsumption-initial-emission-demand-intersection.md#63-zero-premise-loop-output-bypass)
before invoking this trie-based extra restriction. DATA-row queries and
first-safe-prefix behavior below remain unchanged. Plain/protected result
memberships stay separate under section 2.1 of the combined spec.


The current [unified loop proposal](../docs/design/bidirectional-loop-propagation-demand-trie-proposal-20261104.md)
is the single design entry point. This document retains the detailed trie
contracts and proof obligations.

4 November 2026. Design proposal. No Kotlin implementation is selected or changed.

Reference runtime: `e558b496acf82de6ff136325d58f3d90ee5b8559`.
Use this design with the [loop pipeline and complexity design](../docs/design/bidirectional-loop-edge-pipeline-and-complexity-20261104.md).
The latest measurements remain Conductor reached run-6 / complete run-5 /
accepted run-5, and Stirling-PDF reached run-8 / complete run-7 / accepted run-7.
No new project experiment is part of this proposal.

## 1. Result and semantic scope

The trie has two operations:

1. Select demand payloads for ordinary C2 admission or prepared C5 restriction.
2. Follow a scalar fact's field path to find a useful precision boundary.

The second operation does not enumerate every nested demand. For:

```text
fact:     x.f.g.h.k.* / T
demands:  x.f.[any] / T
          x.f.g.[any] / T
```

the precision walk returns `x.f.g.h`, so the proposed proper cut is
`x.f.g.h.[any]/T`, DEMAND. The shorter demand adds no further depth requirement.
Both terminal demand payloads remain stored and active.

Selected major semantic changes: **none**. Preserve:

- Native initial emission and paired summary intersection, including current
  same-prefix ANY admission and exact/concrete DEMAND behavior.
- The first-safe-prefix loop policy, its full observation and baseline-empty
  drop. Do not choose a different cut merely because it is also sound.
- Whole originals, actual scope/ports, full marks, field and mark exclusions,
  layers, protection, ND execution, Target rules and source permissions.
- Saved replay before current admission, real rules/requests, post-statement
  storage and ordinary routing/deduplication.

The trie selects candidates and precision constraints. A trie terminal is not
permission to emit an initial, publish a summary or report a sink.
New metadata belongs to private trie/cursor types. It does not change equality
or hashing of Facts, PremiseKey, Record or demand patterns.

## 2. Context and authoritative data

Each frozen trie belongs to one immutable demand snapshot and exact context:

```text
C2 context: method + BlockScope(block, entry) + direction + admission policy
C5 context: method + BlockScope + actual exit + normalized whole original
            + admission policy + accepted entry-plan identity
```

Public method contexts use their existing root identity. Do not combine them
with local entries. One loop query can consult several adjacent/repeat entry
contexts; their labels remain distinct even if their paths are equal.

The authoritative objects remain the existing demand patterns and paired rows.
Trie payloads refer to them. Do not copy a second complete demand relation or
add a global store of raw facts.

| Trie | Terminal payload | Construction |
| --- | --- | --- |
| C2 entry trie | Distinct full entry Pattern ID | Build with the incoming frozen snapshot; include entries from DATA rows and DATA-entry control/Target rows |
| Prepared C5 output trie | Output-program ID | Build lazily after each paired entry decision has passed, for this exact whole original and exit |

An output program retains the full exit Pattern, its existing field budget and
accepted source-row provenance. Equal full output functions can share one
program only after their own entry checks. Keep the existing ordinal order
and per-program pack-before-cut semantics.

Run-2 static completion and unsupported control/native cells keep their
existing lookup path. This design does not eagerly expand static compositions.

## 3. Trie organization

Use the same frozen demand-specific node shape for entry and output tries:

```kotlin
class DemandNode {
    val children: IntToNodeMap       // actual AccessorIdx -> immutable child
    val terminalsByMark: Map<MarkSlot, IntArray>
    val anyWitnessByMark: Map<MarkSlot, Int>
}

class DemandTrie<P> {
    val roots: Map<AccessPathBase, DemandNode>
    val presentMarkProfiles: MarkProfileDirectory
    val payloads: List<P>            // references to existing immutable objects
}
```

Geometry is shared across mark profiles. Terminal arrays select payloads for
one required-mark profile at exactly this path. Each array is in the original
first-insertion ordinal order.

`anyWitnessByMark` is a subtree summary for precision lookup. It names a real ANY
constraint with empty field exclusion. It is not the list of all descendants.
Choose its first insertion ordinal deterministically during construction.
At a node containing a terminal and children, keep both. A terminal does not
stop traversal and does not remove descendants.

Every payload enters one required-mark bucket. A FLOW bucket is shared across
compatible actual marks; it is not expanded into one copy per full mark.
Use existing immutable MarkSlot keys. No new MarkTable or rule census is needed.

Subtree witness maps add metadata, bounded by the sum of inserted ANY path
lengths plus their root entries. Report nodes, terminal references and witness-map entries separately;
this metadata is not a free memory saving. No field-prefix subtree is copied
per mark. Do not build a full-mark × all-demands matrix.

### Mark selection is role-specific

Use native compatibility when selecting bucket roots:

```text
C2: markSub(required entry mark, actual mark)
C5: marksMeet(required exit mark, actual mark)
```

For ordinary FULL concrete T, relevant C2 buckets are exact T and compatible
FLOW buckets. Group selectors, where present, use the existing catalog test;
do not expand them into all full marks.

For an abstract FLOW actual, C2 does not select concrete-mark entries. C5 is
different: a concrete T exit can meet FLOW if T is not excluded. Reusing the
C2 bucket selector for C5 would miss results.

Treat root selection as an explicit cost. An exact concrete bucket is a map
lookup; abstract/group selector profiles can require visiting their present
bucket descriptors. Never claim constant cost for all mark profiles.

## 4. Ordinary payload lookup

The full trie query returns candidates in native order. Native predicates
still check tails, marks, exclusions, layers and exact policy.

```text
visitCandidates(actual):
    choose compatible bucket roots for this role
    visit terminal payloads on prefixes of actual.path
    visit descendant payloads below actual.path when this native case needs them
    deduplicate exact payload/ordinal occurrences
    restore existing query order
    invoke the unchanged C2 emitter or C5 output program
```

Keep C2's native common-geometry child traversal order. At a node, merge the
compatible terminal arrays by their original insertion ordinal. Its merge can
cost O(c log(1+r)) for c selected payloads from r profiles. C5 instead restores
its prepared program order; retain that sorting/bit-set cost. Neither payload
order nor a successful predicate is inferred from the required-mark profile.

These are candidate visits, not a new AP matching rule. A conservative
superset is permitted if the final native predicate rejects the extra rows.
A missing native-compatible payload is not permitted.

For C2 ANY entries, the native table gives useful pruning:

| Actual scalar tail | Strict descendant ANY entry paths |
| --- | --- |
| EXACT | Cannot emit an initial |
| STAR | Cannot emit an initial |
| ANY | Can emit the entry's ANY initial |
| ANY_TAINT | Can emit the existing MUST image when legal for this direction |

This table does not authorize skipping descendant STAR or EXACT entries for
a STAR actual. Apply it only to the matching terminal class. The remaining
native cases retain their original candidate traversal.

C5 output selection uses its already eligible program trie. It does not read
owner-wide output-row IDs and then scan all entry-plan decisions. Select
scalar/program cells, keep separate program buckets, pack and transport
protection as before, then apply each program's field limit and final union.

## 5. Precision lookup: one path walk

The first supported precision case uses compatible ANY constraints, ordinary
nonstatic counted fields/array elements, and scalar FULL facts. Unsupported
static anchors or accessor forms keep the reference path until their adapter
is proved. The general payload index can still store them.

A precision forest is a list of read-only cursors into the relevant adjacent
and repeat tries. A cursor is `(node, requiredMarkProfile, scope, family)`.
Filter out cursors without an eligible witness for their profile. Every
child step checks that same profile's witness map.

Apply the existing native pre-admission guards before including a scope. In
particular, a local that is dead at an adjacent/repeat interface has no cursor
for that interface, even if its frozen demand trie contains an old entry.
Cuts retain the base, so the existing route/base liveness guard is stable.
An unknown guard without this guarantee supplies no rejection witness.

```text
precisionBoundary(forest, rawPath):
    if forest is empty: return NoAnyConstraint
    cursors = forest.roots
    for i, field in rawPath:
        next = children(field) from cursors that have an ANY witness below
        if next is empty:
            return Boundary(
                retainedPrefix = rawPath.take(i+1),
                witness = one current cursor's profile-specific ANY witness)
        cursors = next
    return ReachedRawEnd(one current cursor's anyWitness)
```

The first missing field is retained. Do not stop before it. If the walk
reaches the raw end, keep the original tail/layer; do not turn the same full
path into ANY. An empty precision forest is not proof that the full loop
observation is empty.

For a nonempty set of compatible paths D and raw path q, the geometric result
has length:

```text
b = min(length(q), 1 + max { commonPrefixLength(q, d) | d in D })
```

This is a longest shared demand prefix along q. It is not the globally deepest
demand and not only the deepest terminal that already matches q.

### Nested demands

```text
          root
            f  [D1: f.ANY]
            |
            g  [D2: f.g.ANY]

raw: f.g.h.k.STAR
walk: f -> g -> missing h
keep: f.g.h.ANY, DEMAND
```

The walk does not enumerate D1 and D2 to compare two depths. Terminal payload
lookup still produces both required initials:

```text
D1 -> f.g.STAR
D2 -> f.g.h.STAR
```

### A sibling demand is also relevant to precision

```text
demands: f.ANY, f.g.z.ANY
raw:     f.g.h.k.STAR
```

The second demand does not match the raw h branch. Still retain h:
`f.g.h.ANY`. Cutting to `f.g.ANY` would create a provisional z admission.
Do not build the precision forest only from terminals that matched the raw
fact. Its edges must include compatible currently nonmatching demands too.

## 6. Connect the trie to the current loop gate

The current gate compares the complete observation for the raw fact and each
ascending prefix cut. Preserve that behavior. Direct C2 precision alone does
not describe saved AL/BL composition or Target effects.

Use the trie to produce an exact early-rejection certificate for a range of
budgets. This avoids treating a geometric proposal as full-loop permission.

The rejection-witness trie can contain only the certified direct local ANY
entries. It need not materialize every virtual or composed consumer. Native
C2 adds these local admissions before later lookup paths and does not remove
them. Omitting other constraints can weaken the skipped range, but cannot
invalidate a witnessed extra admission. This is different from authoritative
candidate lookup, which must not omit a native-compatible payload.

### 6.1 One witness can reject all shorter budgets

Suppose the precision walk gives budget b. Let m=b-1. Its witness has an ANY
demand path d with:

```text
rawPath.take(m) is a prefix of d
```

For every positive budget j<b, the cut is an ANY fact at rawPath.take(j).
That path is a prefix of d. The native ANY-entry cell emits the same key at
all these budgets:

```text
InitialEmission(d.path, ANY, native bound output mark, DEMAND)
```

First call the real `policy.emitAdmission` for this witness and a representative
cut. If it returns no result, no certificate is available. Require the fixed
base/mark/policy/budget conditions of the constant-emission lemma; otherwise
use the ordinary gate. The initial command is compared as Pattern plus layer;
do not intern a hypothetical InitialAp just to test it.
Use the mark returned by that native call. A GROUP requirement matched by a
FULL T can render T instead of the required group. Do not construct the key
by copying the requirement's mark slot.

If that exact key, with its scope/family label, is absent from the raw full
baseline's C2 admissions, every earlier cut would add it. A union cannot
remove that extra admission. Therefore every budget j<b fails complete
observation equality. One witness and one membership test certify the range.

Different scope labels are not interchangeable. Use the full baseline family
set, including all its native demand lookup paths. Do not establish absence
from one row's result or from an incomplete set of consumers.
Only the native observer adapter with these exact labelled admissions can
provide this certificate. Unknown/custom views use the ordinary gate.

### 6.2 Preserve the first-safe-prefix decision

```text
restrictScalar(raw):
    baseline = nativeCompleteObserve(raw)
    if baseline.empty: return Drop
    if raw.countedDepth <= 1: return raw

    boundary = demandTrie.precisionBoundary(raw.path)
    if certifyEarlierBudgetsDiffer(boundary, raw, baseline):
        first = boundary.retainedDepth
    else:
        first = 1

    for budget = first .. raw.countedDepth-1:
        candidate = nativeLimit(raw, budget)
        observation = nativeCompleteObserve(candidate)
        if observation == baseline: return candidate
    return raw
```

The baseline includes adjacent C2, saved adjacent summary/Target handling with
enclosing C5, repeat C2 and all scope labels/protection. The candidate at b
still passes this full check. If it fails, continue in order. With a certificate,
earlier budgets are proved failures; without one, start at 1 as before.

This design does not need an AL preimage oracle to be correct. It works with
the existing full observer. Later native adapters can certify more cases,
but cannot remove a consumer merely because its path is shorter.

### 6.3 Why a certificate can fail legitimately

```text
raw:     f.g.ANY / T, DEMAND
demand:  f.g.ANY / T
cut:     f.ANY / T, DEMAND
```

Current C2 emits `f.g.ANY/T`, DEMAND, from both raw and cut. The witness key
is already in the baseline, so the absence test fails. The trie must not
claim that retaining the whole raw path is the first safe choice. Native
ascending search remains necessary unless another valid certificate applies.

No new blanket refinement or initial-emission rule is introduced to eliminate
this case.

## 7. Saved summaries and C5 requirements

Keep direct-entry and composed-output coordinates separate:

```text
saved R:       x.k.STAR/FLOW -> ret.STAR/FLOW, NORMAL
enclosing X:   ret.f.ANY/T
raw:           x.k.f.g.h.EXACT/T
```

R removes k before enclosing C5. Its output budget is 2, but preserving that
precision on the input can require `x.k.f.g.ANY/T`, depth 3. Applying the
output depth directly to the input overcuts it. The direct trie does not
replace this composition.

A future compiled simple prefix relation can attach a guarded requirement
to the trie:

```text
R: a.p.STAR/FLOW -> b.q.STAR/FLOW
X: b.d.ANY/T, with paired entry already admitted

if d = q ++ v: mapped input anchor = p ++ v
if q = d ++ v: mapped input anchor = p
```

This requires native input matching, a direct NORMAL STAR/STAR singleton
relation, empty E/mx, supported counted nonstatic geometry, identity boundary
metadata and a proof of layer/cut preservation. Broadening can also activate
a previously unmatched saved read. Retain its matching guard and divergent-field
barrier. A positive mapped path alone is not a complete constraint.

This mapped-path compiler is **not required by the initial trie design**.
Reverse/MUST views, multi-output records, real ND Target joins, method boundary
metadata, static completion and unsupported constraints keep the full observer.
They remain visible when the trie certifies skipping only earlier C2-failing
budgets.

## 8. Costs and lifetime

Let H be the total inserted path lengths, U the number of payload references,
h the queried path length, r the compatible bucket/context roots, c the
candidate postings visited, and k the output programs in a prepared plan.

| Operation | Cost |
| --- | --- |
| Frozen construction | Expected O(H+U), plus exact mark-bucket directory work |
| Memory | O(number of prefix nodes + U + bucket descriptors), at most O(H+U) |
| Precision boundary | Expected O(r·h), no subtree or terminal-list enumeration |
| Boundary witness | O(1) after the cursor walk |
| Range certificate | One native scalar emission and exact baseline-key membership, including path/key costs |
| General neighborhood lookup | O(r·h + visited descendant nodes + c), plus stable-order restoration |
| Prepared output lookup | Same bound over the eligible k-program trie, not all owner rows |
| Exact C2/C5 work | Native operation cost per selected candidate/cell; tree width and output count remain explicit |

The range certificate can remove b-1 complete prefix observations. If it
fails, it removes none. The raw baseline and accepted-candidate full check
remain. This is not a claim that all loop queries become O(h).

Own C2 tries with the immutable DemandStore snapshot. Own output tries with
the existing bounded prepared-plan lifetime. Own precision cursors, witnesses,
baseline keys and scalar/program buckets with one synchronous restriction
session. Preserve cancellation and ordinary work accounting. No new global
raw-fact history, watcher, weak cache or separate mark manager is added.

For multiple scalar facts, preserve each exact mark/layer/protection membership.
Reuse immutable tries; do not select one common deepest cut for an arbitrary
packed tree. Keep the original scalar gate and per-program packing contracts.

## 9. Proofs and implementation gates

The [constructive model](lean/proposals/demand-trie-loop-restriction-20261104/README.md)
provides a checked finite reference. Its receipt separates geometry, abstract
C2 cells and prefix-search certificates from unproved native adapters.
It passes 46 theorems and audits 73 declarations. This does not verify the
Kotlin implementation, native mark/scope adapter or the complete observer.

Required invariants are:

1. Every native demand payload remains reachable in the correct context and
   compatible mark bucket. Shorter terminals are never deleted by deeper paths.
2. Precision traversal equals maximum shared prefix plus one distinguishing
   field, capped by raw depth. It retains an actual raw prefix and no new field.
3. The witness names a real ANY entry from the same labelled native C2 family.
4. Candidate pruning preserves exact native answers; field geometry alone
   cannot decide full AP compatibility.
5. Constant ANY-ancestor emission plus baseline absence implies inequality
   for every skipped budget. Skipping certified failures preserves the exact
   first accepted prefix, or the same raw fallback.
6. Every emitted cut uses native limiting: ANY/DEMAND, empty field E, unchanged
   full mark/FLOW mx and exact transported protection.
7. Output-program selection preserves paired entry eligibility, actual ports,
   program order, full exclusions and pack-before-cut semantics.
8. The full observer still validates saved composition and typed Targets.
   A pure query never performs actual execution effects.

Native oracle controls must include the nested example; sibling nonmatches;
same-path ANY certificate failure; exact input at the last new field; several
scope/family labels; FLOW and concrete mark compatibility differences; C2
DATA-entry control rows; field/mx exclusions; protected memberships; arrays;
static anchors; run-2 completion; unsupported tails; candidate-order and
capacity fallback; saved reads that remove prefixes; and previously unmatched
reads activated by a broad cut. No semantic policy change is selected to make
an unsupported proof pass.

After implementation, measure Conductor run-4/run-6 and Stirling run-6/run-7/
run-8 separately: trie nodes/payloads, selected roots, child probes, payload
visits, successful range certificates, skipped prefix budgets, full observer
calls, eligible output programs, AP cells and actual admitted results. Compare
exact output annotations, demand frontiers and report identities under the
existing FULL/16 GiB configurations. Do not infer a speedup from trie node
counts alone.
