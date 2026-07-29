# BaseOnly Conductor trace-resolution mitigation

## Key idea

Treat an already resolved BaseOnly trace boundary with an implicit-any field as
the canonical representative of otherwise identical concrete-field boundaries.

The boundary quotient has three parts:

1. Resolve less field-specific boundaries first.
2. Memoize intra-procedural start-to-final resolution.
3. Reuse a successfully resolved implicit-any result for a concrete-field
   request only when the method, statement, trace kind, edge shape, base,
   static slot, exclusions, suffix, taint mark, and value-suffix mode are
   identical. Only the field slot may change from implicit-any to concrete.

An empty result is not used to cover another request. Non-BaseOnly facts and
non-deterministic edges require exact equality.

This removes repeated traversal of the same summary graph for boundaries that
represent the same BaseOnly suffix semantics. It does not generalize stored
forward facts or summary edges.

The quotient depends on the trace representation and BaseOnly trace invariants
that were present in the successful experimental worktree but were accidentally
omitted from commit `89cddda88`:

1. Equivalent action edges are stored once, with action alternatives kept as
   variants outside the graph entry.
2. BaseOnly backward trace facts have empty exclusions. Forward exclusions are
   applied by `FinalFactAp.contains` when matching an entry; copying them into
   backward facts multiplies semantically equivalent trace states.
3. A concrete-field call summary is discarded only when an applicable
   implicit-any summary with the same conclusion covers it.
4. BaseOnly containment checks the first concrete accessor after an abstraction
   point against the forward fact's exclusions.
5. `ActionVariant` caches its immutable edge set and structural hash.
   `createActionOrContinuationEntry` receives an already deduplicated set and
   copies it directly instead of calling `distinct()` and deeply hashing every
   variant a second time.

The complete mitigation requires these invariants as well as the boundary
quotient. Testing the quotient on top of an unstaged worktree masked this
dependency during the original commit validation.

## Isolation and repeated-run result

The projected call-summary shortcut, caller-trace antichain, F2F field
generalizer changes, and summary-storage changes were removed.

The first clean candidate exposed two errors in the earlier validation:

- without the omitted prerequisites, the committed quotient remained slow;
- after restoring them, rule-search trace resolution was stable, but path
  resolution still depended on hash-derived action-variant order;
- experimentally preferring a non-summary variant reduced typical time but did
  not eliminate the timeout without diagnostic logging, so that behavior
  change was removed from the final patch.

A thread dump from the remaining 18/19 stall showed the only running worker in
`MethodTraceResolver.TraceBuilder#createActionOrContinuationEntry`. It had used
about 146 CPU-seconds inside `variants.distinct()`, recomputing
`ActionVariant -> Sequential -> Set<TraceEdge>` hashes. The argument was already
a `LinkedHashSet`, so this was duplicate work rather than semantic
deduplication.

After removing the redundant `distinct()` and caching immutable variant state,
two independent no-probe Conductor scans of the final hash-only candidate
completed without timeout or OOM. Each produced 19 shallow discoveries and
completed all four relevant batches:

| run | rule-search trace | actionable entries | final trace | path trace |
|---|---:|---:|---:|---:|
| 1 | 19/19 | 19/19 | 19/19 | 19/19 |
| 2 | 19/19 | 19/19 | 19/19 | 19/19 |

Path resolution completed in 23.3 s and 10.0 s respectively.

## False-negative analysis

The change should not introduce a false negative if the BaseOnly abstraction
obeys its intended ordering: for the same suffix semantics, an implicit-any
field boundary covers every concrete-field boundary. Resolving the covering
boundary is then an over-approximation of resolving the covered boundary.
Scheduling and exact memoization do not change reachability.

Caching the hash and edge set does not change equality, and replacing
`variants.distinct()` with `variants.toList()` does not change membership:
the caller constructs and passes a `Set<ActionVariant>`. These changes remove
only repeated computation.

The implementation deliberately prevents the known unsafe variants:

- it never drops or changes the suffix, taint mark, or value-suffix mode;
- it never generalizes static access;
- it never changes edge arity or pairs different statements/methods;
- it does not use an empty weak result to suppress concrete resolution;
- it reuses only a weak boundary that was actually resolved, rather than
  synthesizing one.

The remaining semantic dependency is monotonicity of backward trace transfer:
every concrete-field predecessor/action must also be present when resolving the
covering implicit-any boundary. If a future operation treats implicit-any more
narrowly than a concrete field, reuse could hide that concrete trace. The
field-generalization law tests protect the boundary relation itself; scenario
tests should continue comparing BaseOnly reachability and collected actions
against Tree for field-sensitive flows.
