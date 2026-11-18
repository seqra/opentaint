# Progressive input partitions

15 November 2026. Investigation proposal under
[proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
This replaces the **withdrawn wrapper-owner solution**. Methods keep their
owners, entry abstraction, summary stores and paired exit restriction.

Use one persistent input partition for an owner, rather than rebuilding
independent shallow query families on every iteration. Refine this partition
at an observed field-loss operation. A field read and an application of a
saved NORMAL reader use the same child-case cover.

The checked positive references finish at **run-3 through run-15**, including
wrappers with ordinary operations and two inner calls. These are formal
reference runs, not new project measurements. See the
[results and proof scope](../reports/bidirectional-progressive-input-partition-20261115.md).

**Workload issue found during review:** one split per handoff bounds trie
metadata, not resulting propagation. A new ordinary-code reference has
18 executable summary rows instead of 2 at run-8, with both policies
finishing at run-11. This proposal is not ready for activation. The replacement is [existing prepared-child routing](bidirectional-prepared-child-saved-replay-20261115.md).
It needs no new trie or dynamic initial origins.

## 1. Problem and semantic changes

The previous bounded plan can keep opening the same case:

```text
actual input:                      x.f.g.MUST/T,N
owned conditional input:           x.f.STAR/FLOW,N
saved opposite-direction reader:   x.f.f.STAR/FLOW -> ret.STAR/FLOW,N
owned-query replay result:         ret.MAY/FLOW,D
```

The real input does not satisfy the reader: g differs from f. The conditional
STAR query has lost this distinction. Its coarse result recreates a broad
DEMAND summary, which can be applied to the real input again. Adding a field
operation around the call does not change the cause.

| Part | Earlier bounded plan | Proposed change |
| --- | --- | --- |
| Input plan | Separate one-step families, rebuilt from current rows | One persistent prefix partition, shared by compatible raw initials |
| Input refinement budget | At most `FL(external Dc)+1` | A derived local cell may use `FL(local Dc)+1`, within the global limit |
| Output permission | The original paired Dp | **Unchanged**, including its `FL(Dp)+1` cap |
| Unknown ordinary read | Delegate only through its current one-level family | Delegate through the complete frozen partition child case |
| Saved NORMAL replay inside an owned query | Can regenerate the delegated coarse MAY result | Use the same supported child-case routing |
| Saved NORMAL replay on the real caller offer | Before demand lookup | **Unchanged**, including empty-demand calls |
| Handoff | Refined demand rows, but no persistent input plan | Also install at most one observed missing trie edge per owner/direction |

**Major semantic changes:** the local C2/C5 entry permission can refine
beyond the external row's first new field; some owned-query DEMAND
contributions are replaced by complete child services. Intermediate demand
and confirmation timing can differ. This is not a storage-only optimization.

Keep all real truncations, FULL marks, actual input layers, literal protection,
real field/mark exclusions, paired output restriction, NORMAL subsumption,
MUST handling, selected cleaner behavior, source permissions and ZERO/Target
rules. No MAY/NE premise, new tail, artificial exclusion, grounding label,
unbounded evidence composition, owner fusion or iteration cap is added.

## 2. State and partition

Use the qualified method/block input frame: owner, direction, physical port,
base and native mark/protection/exclusion compatibility. A partition must not
borrow output permission from another row. It can share its prefix structure
across compatible rows, but each cell retains its own **complete original Dp**.

```text
persistent[frame]: prefix trie T
pending[frame]:    zero or one missing trie edge
run-local:        frozen cells, query bindings, safe common routing masks
```

An installed trie edge is one observed accessor. Store parent-node and
accessor identifiers. Do not store the original truncated suffix, caller input
history, a product of call paths or the result of full field-sensitive replay.

For a node h and its installed children G:

```text
h.MAY = {h.$}
        union {h.f.MAY | f in G}
        union {h.s | s is nonempty and first(s) not in G}
```

The last region is a local residual service. Its raw AP is still `h.STAR`
with its **real E unchanged**. G is frozen routing metadata, not an exclusion
or a property propagated to another owner. NE omits the original h.$ case;
a strict descendant can still end at that descendant's point.

Every concrete suffix has a computable owner: empty, one named child, or
residual. A child contains both its point and longer suffixes. The cover
therefore works for any continuation, not just for equal abstract outputs.

## 3. C2 and C5

For an external row `[Dc ; Dp]`, visit its compatible installed descendant
nodes. At Dc keep its selected MAY/NE kind. A strict child is a local MAY
selector: descent already satisfies a parent's nonempty requirement.

Apply the existing C2 table at each local selector, with these rules:

- Keep the dedicated forward MUST query. Do not split an admitted MUST
  family into point/STAR families.
- Keep the selected concrete projection layers and FLOW companions.
- If an actual lies under an installed child, delegate its corresponding
  first-field start to that child; do not also reopen the ancestor family.
- Keep the existing conditional EXACT/FLOW prefix probe where legal. It is
  not concrete-mark evidence.
- Precise STAR/EXACT demands retain their old table. They do not gain
  uncertain-child admission. An incompatible sharing consumer disables a
  routing mask instead of losing its result.
- Respect the global field limit. If a child cannot be prepared, its coarse
  contribution remains enabled.

For every prepared cell:

```text
cell = (original row, local input selector, raw initial, routing mask)

FL(raw initial) <= min(global limit, FL(local selector)+1)
C5 entry witness = this cell's constructive C2 result, before normalization
C5 output selector = original row.Dp
FL(published conclusion) <= min(global limit, FL(original row.Dp)+1)
```

No local cell becomes a new inferred external demand row merely because the
planner created it. A new demand row must still be produced by analysis and
pass the original paired output intersection. No raw-candidate archive is
needed.

## 4. Propagation and call handling

```text
offer(owner, original):
    replies = replaySavedNormal(owner, original)          // unchanged, first
    cells = prepareFrozenPartition(owner, ownDemand, original)
    if cells.empty: return replies
    installFreshRawInitials(cells)                       // existing entry dedup
    return replies + applyAndSubscribeCurrent(cells, original)

processOwnedQuery(q, operation, fact):
    outputs = nativeTransferOrSummaryApplication(operation, fact)
    // Enroll callee work and process observations normally, even if a result
    // below is delegated. Removing an output is not skipping a call.
    for contribution in outputs:                         // per derivation
        loss = firstUnknownCorrelatedSuffixField(q, operation, fact)
        if contribution is coarse MAY/DEMAND and loss is supported:
            pending = leastFreshMissingEdge(pending, T, q.head + loss.field)
            if every consumer sharing q has a complete prepared child service:
                omit only this coarse contribution
                continue
        enqueue(contribution)                           // ordinary result/layer

onRawSummary(cell, candidate):
    processObservationsAsBefore()
    if legalRetainedNormalServiceCovers(candidate): return
    result = pairedC5(cell.rawC2Witness, candidate, cell.originalRow.Dp)
    applyExistingSameLaneCoverageAndReplyFolding(result)
    publishAndCaptureRefinementHeadsAsBefore(result)

handoff(owner, direction):
    persistNormalAndBuildDemandAsBefore()
    installAtMostOneFreshEdge(T, pending)                // used next same-dir run
    pending = empty
```

Supported loss operations in this proof scope are positive unary prefix
reads and saved opposite-direction NORMAL STAR-to-STAR readers. They retain
suffix correlation before the loss. Known-path reads, writes and definite
MUST results run normally. The result of a cut/MAY operation is not treated
as a correlated STAR suffix.

For a saved reader `a.u.* -> b.v.*`, an owned STAR fact whose head is a proper
prefix of `a.u` contributes the **first unknown accessor**. Do not copy u's
whole suffix into evidence. Its child queries replay the native record and
then continue normally. A remaining unknown accessor is a later loss event.

Keep every other derivation of the same abstract result. Do not delete by
output equality. Current/DEMAND records keep their explicit query bindings;
they are not silently treated as NORMAL readers. Cleaners, rule checks,
mark changes, aliases, ND and unsupported correlation use ordinary processing
unless their complete child service is separately established. In particular,
a trie field is never permission to make a condition false or skip a cleaner.

The cover must hold for every row/offer sharing a raw initial. Freeze the
intersection of safe masks **before** processing that initial. Do not revise
its mask after deduplication. The partition replaces overlapping coarse plans;
it does not add child queries while retaining an unmasked copy of the same
coarse case.

## 5. Progress and cost

After a supported loss, select the first missing edge on its observed input
head plus one accessor. Among events, keep the smallest `(depth, field order)`.
Install at most one edge across the owner's input frames for that direction's handoff, not one per row, mark or base.
An installed edge is never removed when demand disappears. It creates no
query without active demand and input.

For a finite guard whose loss is observed infinitely often, an unsplit next
field cannot lose forever: only finitely many fresh edges have smaller priority. Each winning
installation removes one from that finite set. Handoffs without this event
cannot add an element back; the same argument applies to its active subsequence. Once the guard's fields are
split, its old unknown-prefix contribution cannot recur from those cells.
The EXACT child prevents losing the endpoint while the suffix child refines.

This proves progress of a recurring supported loss. It does **not** infer
redundancy from repeated counts, absence of new NORMAL records, or run-11.
Unsupported losses remain visible. A universal native termination theorem
has not been proved.

With t handoffs in one direction and owner:

```text
new installed trie edges <= t
pending evidence          <= 1 edge
prepared cells per offer  = O(number of own rows * (1 + installed nodes))
new-node storage          = O(t), with parent/accessor interning
```

Existing demand anchors and legal C2 first-field outputs are not unbounded
loss evidence. The reference stores literal paths for kernel evaluation;
the implementation should reuse trie nodes. Field transfers and every C5
output still use the original global/relative cuts. No eager `k^limit` trie
or untruncated call relation is built. This bounds the new planning state;
it does not promise a polynomial bound for the whole analyzer.

## 6. Required safety and proof scope

The [Lean package](../../spec/lean/proposals/progressive-input-partition-20261115/README.md)
checks constructive suffix ownership, point/suffix completeness, transfer
image coverage, paired-exit preservation, monotone one-edge installation and
finite-priority progress. Full cold reference states check actual offers,
raw initials, current summaries, installed trees, backward producer permission,
per-run quiescence and empty DATA/Target frontiers.

It also checks that dedicated MUST admission is independent of every trie,
including the selected cleaner source families; the older protected/cleaner
coverage and wrapper repair packages are rechecked. Unsupported operation
results and the saved service on original offers are unchanged.

This is not a correspondence proof for all native aliases, rules, ports and
ND machinery. Integration must verify the correlation and complete-child
service predicates before enabling a suppression. Otherwise keep the native
contribution. The exploratory differential screen exposes a limitation shared
with its older reference model; the report records it. Do not present the
screen as a proof of whole-core completeness.
