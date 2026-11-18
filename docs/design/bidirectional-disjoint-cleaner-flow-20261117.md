# Preserve FLOW outside a selected cleaner's region

17 November 2026. Proposal repair. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md).
[Consolidated contract](bidirectional-demand-termination-approach-20261115.md).
[Original failure and cold trace](../reports/bidirectional-cleaner-getter-soundness-gap-20261117.md).
Production is unchanged.

**Result:** the repaired reference retains the NORMAL observation and stops
naturally at **run-3**. Native components confirm the run-2 C5 publication
and the run-3 saved-summary application. The unchanged production driver
still reproduces the original loss at run-3; this is not an integrated
implementation result.

## 1. Selected semantic change

Change only an **executed selected-mark cleaner on nonstatic FLOW in FULL
mode**, in either direction and in every run. If the whole suffix region
of a FLOW path is disjoint from the cleaner, preserve that path with its
original mx. Otherwise, use the old selected FLOW cleaner.

| Part | Before | After |
|---|---|---|
| FLOW at p.g, exact-root T cleanup at p | Add T to mx, although no suffix below p.g is cleaned | Keep its existing mx |
| FLOW at p or an ancestor of the cleaned path | Add T to mx | Same |
| Concrete-mark cleanup, including protection and same-head MUST | Current selected rules | Same |
| Run-1 cleaner mark requests | Emit the existing selected requests | Same, including the preserved FLOW part |
| C2, C5 and saved replay | Current contract | Same; an unmasked FLOW result can now pass C5 and serve the later call |
| Field limits and keys | Current contract | Same; no exception or new key |

Keep field writes, aliases, ND conditions, typed Targets, source permissions,
static cleanup, RemoveAll, GROUP, the schedule and all other proposal rules.
A conditional cleaner must first pass its existing rule guard. This rule
adds no new guard evaluation. It does not remove an exclusion already in mx.
It does not give a concrete mark to FLOW or turn DEMAND into NORMAL.

## 2. Complete guard

Let h be the FLOW path and c the cleaned path, on the same nonstatic base.
Let `prefix(x,y)` mean `y = x ++ suffix`, including an empty suffix.
Use the **whole suffix region** `Cone(h) = {h ++ s | s is any field chain}`.
Do not use only the raw tail or an empty-suffix test.

```text
safeCone(h,c,EXACT) = NOT prefix(h,c)
safeCone(h,c,AT_AND_BELOW or BELOW) =
    NOT prefix(h,c) AND NOT prefix(c,h)
```

For EXACT cleanup, h can be a strict descendant of c or an incomparable
path. For the two subtree modes, require incomparable paths. The BELOW
test is conservative. Do not add an E-based shortcut in this change.

| FLOW head h | Cleaner c / reach | Preserve mx? | Reason |
|---|---|---|---|
| p.g | p / EXACT | yes | Every suffix remains strictly below p |
| p.g | p.f / any reach; f != g | yes | Incomparable paths |
| p | p / EXACT | no | The suffix can be empty |
| p | p.f / EXACT | no | The suffix can start with f |
| p.g | p / BELOW or AT_AND_BELOW | no | The subtree includes p.g |
| p.$ / FLOW | p.f / EXACT | no | Its later STAR normalization can include f |

The last row is essential. A raw exact root can be outside the cleaned
point while its public normalized STAR region overlaps that point.
Checking only raw EXACT geometry would create an invalid NORMAL summary.

## 3. Transfer, packed paths and requests

```text
cleanSelectedFLOW(input, cleaner, selectedMarks, mode):
    if mode != FULL or input.base is static or input.base != cleaner.base:
        return existingClean(input, cleaner, selectedMarks, mode)

    // Same request obligation as the old selected FLOW operation.
    if mode.run1:
        request(selectedMarks)  // once; do not remove incoming mx members

    (safe, other) = partitionExistingFLOWPaths(input,
        h -> safeCone(h, cleaner.path, cleaner.reach))

    if safe is nonempty:
        emit(input with tree=safe)             // retain all headers and mx
    if other is nonempty:
        emit(input with tree=other,
             mx=input.mx UNION selectedMarks)  // old selected FLOW result
```

This applies to both the scalar selected cleaner and its existing FULL-mask
batch form. Do not interpret a null selected mark as an empty set: that is
RemoveAll and stays on its current path. A batch must have the same cleaner
geometry for all selected marks, as in the existing batch contract.

Partition every path of a packed tree. A safe child cannot authorize an
unmasked root or a different child. E stays at its own head. Keep path,
tail, base, layer, mx, original premise and literal protection memberships.
An incoming DEMAND FLOW remains DEMAND. Preserve existing request ownership
and callback deduplication. The concrete cleaner branch is unchanged.

There are at most two output masks for one input packet. Each old path
appears in exactly one partition, with no new field chain. Equal masks can
reuse the existing canonical union. A native implementation can split along
the existing cleaner spine and share untouched subtrees; it need not enumerate
all leaves as the simple test adapter does.

## 4. Repaired trace

Use the original code. Only the annotated FLOW cleanup changes.

```java
void main() {
    Box a = new Box();
    markGH(a);                  // T at a.g.h.MUST.
    Box r = helper(a);
    observeTBelow(r);            // CM(r.M,T).
}
Box helper(Box p) {
    clearRootT(p);               // EXACT root, selected T.
    return p.g;
}
```

Run-1/limit 1 is unchanged: p.* intersects the cleaned root. Its marked
return is `p.*/T -> ret.M/T,D,H=1`; the root has DemandTarget. Its local source
is cut to `a.g.NE/T,D`. The same run-2 demand and actual are therefore used.

```java
// Run-2 backward published summaries:
//   ret.$/T    -> p.g.$/T,D,H=1
//   ret.*/T    -> p.g.*/T,D,H=1
//   ret.*/FLOW -> p.g.*/FLOW,N       // NEW: no T in mx.
Box helper(Box p) {
    clearRootT(p);
    // Backward FLOW is p.g.*/FLOW,N. Cone(p.g) cannot include p.
    // Preserve it. Concrete survivor handling stays unchanged.
    return p.g;
}
// Previous (entry Dc; paired exit Dp): (ret.M/T; p.*/T).
// Submitted: ret.M/T,D.
// Initials: ret.$/T,D; ret.*/T,D; ret.*/FLOW,N. No new query.
```

The existing C5 raw-entry test admits the authorized FLOW companion. Its
output now intersects the paired T selector because mx does not exclude T.
Its field length is 1, exactly the existing `FL(Dp)+1` output bound and global
limit. The record is stored NORMAL in its native backward direction. No
synthetic summary is injected.

```java
// Run-3 forward: main source now supplies a.g.h.MUST/T,N.
// helper submitted: p.g.h.MUST/T,N.
// Relevant demand: p.g.$/T -> ret.$/T; p.g.*/T -> ret.*/T.
// Saved NORMAL replay comes first:
//   reverse(ret.*/FLOW -> p.g.*/FLOW)
//     = p.g.*/FLOW -> ret.*/FLOW,N.
// Applied to actual: ret.h.MUST/T,N.
// C2 still rejects the deeper actual for both precise marked demands.
// No current query is needed.
Box helper(Box p) {
    clearRootT(p);
    return p.g;
}
// No current marked summary is published here.
// main receives r.h.MUST/T,N and publishes ZERO -> NormalTarget(id),N.
// No outgoing refinement demand; natural completion at run-3.
```

The same NORMAL relation transports **any** submitted suffix after p.g. It
uses the saved relation's correlation, without an unrolled suffix archive.
A DEMAND actual still gives a DEMAND result. No existing Target is canceled.

## 5. Constructive proofs

[Proof package](../../spec/lean/proposals/disjoint-cleaner-flow-20261117/README.md).

1. **Whole-region disjointness.** For EXACT cleanup, a cleaned point in
   `h ++ s` would prove `prefix(h,c)`, contradicting the guard. For subtree
   cleanup, a common point would make h and c comparable. Both prefix cases
   contradict the guard. The Lean witness proof covers arbitrary paths.
2. **No invalid NORMAL mark transport.** At every suffix in an admitted
   safe region, the concrete selected cleaner is identity for every full
   mark, including T. A preserved FLOW relation is therefore valid on the
   whole suffix region. An existing E or mx only restricts that region.
   This is valid forward and backward. EXACT-to-STAR normalization is
   covered by the same whole-region proof, not an empty-point argument.
3. **No removed concrete derivation.** Concrete cleanup, its H and the
   request plane are unchanged. The changed FLOW branch retains more valid
   mark transport. Its safe region is unchanged by the concrete operation;
   all other regions retain the old transfer. New NORMAL service cannot
   falsely confirm a DEMAND actual because application still joins layers.
   Existing positive rules/complete ND joins can use that valid service.
4. **Limits and packed membership.** The safe result equals the input at
   every coordinate. The other result has the old path coordinates. The
   partition retains every old path once. No new initial, field product,
   stored evidence or cap exception is introduced.
5. **The failed example.** The executable reference computes run-1,
   complete run-2 C2, both marked C5 rows and the new NORMAL FLOW row.
   Saved application constructs the run-3 NORMAL observation. Precise STAR
   rejection stays in effect. The empty frontier has a report-preserving
   uncapped quiet suffix. No hard iteration limit appears in this proof.

This closes the named counterexample and proves the changed local transfer.
It does not discharge the audit's general native correspondence, handoff
or whole-analyzer termination obligations.

## 6. Cost and validation limits

Direct transfer work changes from one header update to a path partition.
With a shared trie this follows the cleaner spine, sharing off-spine trees.
No individual path gets two outputs. Across many cleaners, the number of
mask classes can grow with the already present path heads; the two-packet
bound is per operation, not a bound on an entire method or scan.

The new NORMAL record may be retained where only a masked record existed.
That adds a useful relation. It replaces no budget with full path enumeration
and requests no additional initial family. Saved replay still obeys the
ordinary call/field limits. Downstream workload is not proved to decrease
on every program; measure mask classes and NORMAL/DATA publications when
this change is implemented.

The earlier 252-case no-cleaner family and its seven service references use
unchanged transfer definitions. Their hash-checked proofs remain valid at
their stated scopes: stops by run-9, diagnostic scan through run-25. The
same-head concrete MUST rule and all concrete cleaner rows are unchanged.
Native tests separately check root/subtree controls, genuine-cut layers,
real E/mx, the exact-prefix normalization hazard and the new C5/replay route.
Production remains unchanged; no integrated or project timing is claimed.
