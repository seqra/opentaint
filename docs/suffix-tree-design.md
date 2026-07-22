# SuffixTree dataflow facts

Status: living design and implementation record for `dvvrd/suffix`

Implemented as of the current stage: the canonical suffix relation, edge-level bundles,
`ApMode.SuffixTree`, lazy seam canonicalization, suffix-native intra-method F2F storage, persistent
F2F summary storage, and F2F caller-subscription storage. Legacy flow functions, serialization, and
trace queries materialize diagonal slices at explicit boundaries. Tree remains the default mode.

## 1. Scope and terminology

OpenTaint's forward IFDS analysis propagates Hoare-style implications. In Tree mode, the
distributive implication is represented by `Edge.FactToFact(initialFactAp, factAp)`, where the
initial fact is a linear access path and the final fact is an access tree. This document specifies
`ApMode.SuffixTree`, which represents a set of diagonal implications as one value:

```
(initialPrefix, finalPrefixTree, suffixTree)
```

For every suffix branch `s` and every leaf `v` of the final prefix tree, the value denotes

```
initialPrefix.s -> v.s
```

The same `s` is used on both sides. This is diagonal composition, not the cross product
`initialPrefix.* -> finalPrefixTree.*`.

The proof-of-concept terminology is normalized here to initial prefix, final prefix, and suffix.

The first implementation covers the forward analysis. Cactus and Automata are outside its kernel.
Serialization and trace queries currently use explicit materialization adapters; they are not
allowed to constrain the kernel representation.

## 2. Current Tree implementation

### 2.1 Alphabet and facts

`Accessors.kt` defines the accessor alphabet:

- fields and array elements;
- taint marks and mark values;
- the final marker;
- field/element wildcard (`AnyAccessor`);
- static roots;
- type-information group and concrete type accessors.

`AccessPathBase` supplies roots such as `this`, argument, local, return, exception, constant, and
static state. `AccessorInterner` maps accessors to integer indices.

Tree mode uses:

- `AccessPath`: base, a linear accessor chain, and an `ExclusionSet`; this is an initial fact;
- `AccessTree`: base, an immutable accessor trie, and an `ExclusionSet`; this is a final fact;
- `AccessTree.AccessNode`: sorted child indices and nodes, `isAbstract`, `isFinal`, and cached shape
  metadata;
- `AccessTreeInterner` and `AccessTreeSoftInterner`: structural sharing for immutable trees.

An abstract fact `x.*\{f}` denotes the still-abstract part under `x` after the `f` branch has been
peeled and scheduled separately.

### 2.2 Termination invariant

Within one access path/tree branch, the same field accessor is not retained twice. Prepending an
already present field collapses the older occurrence. Consecutive element access is separately
bounded. `AccessPath.AccessNode.addParent` and the corresponding `AccessTree.AccessNode` operations
enforce these rules.

SuffixTree relaxes the invariant only in storage: the initial prefix, final prefix, and suffix are
each canonical independently, while their conceptual concatenation may temporarily repeat a field.
Every observable traversal across a prefix/suffix boundary must restore the invariant lazily with
the existing field/element limiting rules.

### 2.3 Abstraction and worklist events

`TreeInitialFactAbstraction` holds two structures per base:

- an `added` access tree containing concrete context facts;
- an `analyzed` access-path trie recording emitted abstract paths, exclusions, and already requested
  `AnyAccessor` unwindings.

Reads and writes peel an accessor from an abstract fact and propagate the residual exclusion. The
current `dvvrd/deabstr-query` preparation adds pending transfers: if a generalized edge has already
subsumed a concrete edge, the concrete context event can still replay the generalized edge with the
new delta. Therefore queue coverage may safely reject `x.f -> x.f` when `x.* -> x.*` is present.

### 2.4 The four storage roles

All representations are selected through `ApManager`.

1. `MethodAnalyzerEdges` stores intra-method path edges, partitioned by statement and bases. The Tree
   F2F cell is a trie of initial paths whose values are statement-indexed merged final trees.
2. `SummaryEdgeStorageWithSubscribers` stores method summaries and emits only storage deltas to
   subscribers. The Tree F2F summary store treats identity and non-identity conclusions separately
   and merges conclusion trees per initial path.
3. `SummaryEdgeSubscriptionManager` stores caller facts waiting for callee summaries. Tree mode uses
   a reverse access-tree index after a size threshold to find conclusions starting with a summary
   initial path.
4. `TreeInitialFactAbstraction` stores and lazily unwinds method-context facts as described above.

The stores have different indexing for their hot queries, but all encode a relation from initial
paths to final trees and all must preserve the same delta/event contract.

## 3. Formal SuffixTree semantics

### 3.1 Suffix cones

A suffix terminal is `(p, E)`, where `p` is an accessor chain and `E` is an exclusion set. It denotes
the cone

```
Cone(p, E) = { p.s | s is empty or first(s) is not in E }
```

A suffix tree denotes the union of its terminal cones. Exclusion belongs to the terminal, not to the
whole tree, because different suffix branches may have different exclusions.

For an initial prefix `u`, final-prefix tree `V`, and suffix tree `S`:

```
Language(u, V, S) = {
    (dedupConcat(u, s), dedupConcat(v, s))
    | s in Language(S), v in leaves(V)
}
```

`dedupConcat` is the existing lazy field/element canonicalization, not raw concatenation.

### 3.2 Maximal factoring

For a concrete pair of paths, remove their longest common accessor suffix. The remaining paths are
the initial and final prefixes; the removed path becomes the suffix. Factoring must be maximal.
Otherwise coverage can cross prefix pairs and the POC's per-prefix coverage theorem does not hold.

For a final tree, factoring is performed per final leaf, then leaves with compatible initial prefix
and suffix cones are grouped. No algorithm may invent a common suffix shorter than the maximum merely
to simplify storage.

### 3.3 Canonical cone union

For a fixed pair of initial and final prefixes, suffix cones are canonicalized using these relation
rules:

- cones at the same suffix path merge by intersecting exclusions;
- a cone removes descendants reached through non-excluded accessors;
- an excluded child that is a full wildcard removes that exclusion and is absorbed;
- the same absorption is repeated upward;
- dead nodes are removed without affecting other final prefixes.

Annihilation is bidirectional and insertion-order independent. A mutable prototype implementation is
acceptable inside one analysis store; published suffix values are immutable snapshots or interned
nodes.

## 4. Kernel representation

### 4.1 Edge-level ownership

The suffix is owned by the F2F edge/bundle, not independently by its two facts. This is required for
diagonal semantics. If a final-side read selects suffix branch `f`, the initial side must select the
same branch in the same operation.

The kernel type is conceptually:

```
SuffixFactToFact(
    methodEntryPoint,
    statement,
    initialBase,
    initialPrefix,
    finalBase,
    finalPrefixTree,
    suffixTree,
)
```

Plain `FactToFact` is the degenerate adapter with one empty suffix cone. Z2F and ND edges do not have a
diagonal pair and remain on the existing fact representation initially.

### 4.2 Legacy operation boundary

Existing flow functions operate on independent `InitialFactAp` and `FinalFactAp` values. Passing a
branched suffix through that API is unsafe because a final operation can select a branch without
communicating that selection to the initial fact.

The first correct integration therefore uses a synchronized cursor:

1. Unchanged CFG propagation keeps the bundle intact.
2. Before an operation that reads/unwinds the initial prefix, traverse the initial prefix first; at
   its end, split or filter suffix branches.
3. Before an operation that reads the final fact, traverse the final-prefix tree to its leaves; then
   split or filter suffix branches.
4. Materialize only the selected diagonal slices as legacy fact pairs, using `dedupConcat` at both
   seams.
5. Feed results back through the SuffixTree store, which maximally factors and re-bundles them.

This boundary is a correctness scaffold. Hot operations can later become suffix-native without
changing storage semantics.

### 4.3 Required structural invariant

For a fixed statement and pair of bases, every identity relation with a common initial/final prefix
must be represented by one suffix tree. For example:

```
x.f -> x.f
x.g -> x.g
```

has one bundle with initial prefix `x`, final prefix `x`, and a suffix tree branching to `f` and `g`.
Returning two single-generator edges from a compressed store does not satisfy this invariant even if
the store itself uses a trie.

## 5. Storage layout and queries

The common logical layout is:

```
bases / statement or exit point
  -> initial-prefix trie
    -> suffix cone trie
      -> final-prefix tree/set at each suffix terminal
```

The concrete nesting may be transposed for a store's hot query, but the canonical language and
bundle emission must be identical.

### 5.1 Intra-method edges

`add` decomposes the incoming final tree into leaves, maximally factors each pair, inserts cones, and
returns only newly observable delta bundles. The stored view first canonicalizes the suffix language
for each exact prefix pair, then merges final prefixes into one access tree only when their complete
suffix languages are equal. This preserves correlation while allowing both the final-prefix tree and
the suffix tree to branch. Publishing the incoming language delta avoids rebuilding and reprocessing
the complete accumulated suffix tree after every insertion. A newly encountered initial premise must
surface its context obligation once even when its relation is covered; subsequent covered relations
are suppressed. The pending-transfer preparation handles later concrete unwind events.

Collection by statement emits grouped bundles, not individual generators. Exact initial-prefix
matches are preferred, then covering prefix bundles are considered, matching Tree mode's relaxed
containment behavior.

### 5.2 Summary storage

Summary cells are additionally partitioned by exit statement and bases. Adds are synchronized with
reads because the summary manager can publish concurrently. Deltas are grouped suffix bundles.
When annihilation widens a stored cone, the incoming cone is the additive worklist obligation: the
previous cone has already propagated and their union is the broadened stored language. The full
canonical bundle is returned by store queries, while subscribers receive only the new delta.

Tree summaries also perform final-side-only squashing for a fixed premise. The suffix summary store
reproduces it with a compact, prefix-sharing premise trie. Each terminal retains only its merged
non-identity final-prefix node and intersected exclusion; identity-shaped branches go directly to
the diagonal suffix relation. A widened exclusion republishes every retained final branch, while an
ordinary tree union publishes only `mergeAddDelta`. There is no production Tree summary overlay.
Final-prefix states reuse Tree's cycle-compression safeguard after 10,000 nodes and share one soft
interner per summary cell, so preserving that scale bound does not duplicate the Tree premise/index
hierarchy.

The complete Tree implementation is instantiated only when the opt-in verifier is enabled and is
then compared with the suffix relation after every insertion.

### 5.3 Subscriptions

Subscriptions index final-prefix paths and suffix branches together. Matching a summary initial fact
walks the final prefix, then the suffix. A reverse index may retain the current threshold strategy,
but its indexed identity is the bundle, not an expanded suffix leaf.

### 5.4 Initial fact abstraction

The abstraction store remains responsible for deciding which concrete context branches need
unwinding. Its existing `added` access tree and `analyzed` path trie remain single-side structures:
they answer context queries without representing a paired implication. In SuffixTree mode each
unwinding/refinement result is collected by base, converted to a diagonal identity relation, and
emitted as grouped bundles. The complete batch therefore reaches the method queue without first
becoming one edge per path. Tree mode retains the original per-path emission.

## 6. Correctness instrumentation

Instrumentation is enabled by JVM properties and records canonical languages at summary commit
boundaries. `opentaint.suffix.verify=true` maintains a debug-only Tree summary shadow and checks the
language relations after every insertion. `opentaint.suffix.logShapes=true` logs the first non-empty,
branching, and branching-identity canonical stored shape observed in each relation.
`SuffixTreeDiagnostics.snapshot()` separates delta-publication counters from canonical stored-shape
counters: publication deltas are intentionally often one cone even when the accumulated store is a
branching suffix tree.

Required checks:

1. For every method, every Tree summary is covered by the SuffixTree summary language.
2. If no cone annihilation occurred in a compared cell, the two languages are equal.
3. Every identity group for a common base/prefix is emitted as exactly one bundle.
4. Every initial prefix, final prefix branch, and suffix branch is internally field-unique.
5. Every materialized prefix-plus-suffix path is field-unique after lazy concatenation.
6. At least one integration fixture produces a non-empty suffix.
7. At least one fixture produces a branching suffix tree, proving the representation is not merely a
   renamed access path.

The standalone cone trie is checked against an independent bounded-language oracle, including
idempotency, insertion-order independence, downward closure, bidirectional annihilation, and a fresh
accessor outside all exclusions.

## 7. Implementation stages

1. Land this documentation, a `SuffixTree` value type, maximal factoring, cone canonicalization, and
   oracle/property tests. No engine behavior changes.
2. Add `ApMode.SuffixTree`, edge bundles, diagonal materialization, and the intra-method F2F store.
   Keep Tree as the default and run all dataflow tests in both modes.
3. Port F2F summary storage and subscription storage, with Tree-subsumption/equality instrumentation.
4. Integrate the initial-fact abstraction boundary. Its existing context access tree remains the
   single-side concrete-fact store; identity implications emitted from it are folded by the
   suffix-native method queue. Replace more of its internals only if retained-heap profiles show it
   remains material after the paired stores are compressed.
5. Add compatibility adapters for Z2F, ND, serialization, and trace-disabled analysis. Cactus and
   Automata may explicitly reject SuffixTree-only values.
6. Run Java/Kotlin reachability, SARIF, and query tests. Findings, not trace shapes, are the gate.
7. Run Tree and SuffixTree on the existing StirlingPDF and thingsboard code models without rebuilding
   them. Compare normalized finding sets, post-GC live heap, peak RSS, wall time, and propagated bundle
   counts over repeated runs.

## 8. Verification completed so far

The cone relation has deterministic examples plus randomized comparison against an independent
bounded-language oracle. Store-level tests exercise all three paired stores. A 132-edge diagonal
family is retained as one stored bundle with a branching suffix tree, while Tree mode retains 132
individual implications. A seam test deliberately repeats a field across both prefix/suffix seams
and verifies that materialization restores field uniqueness on both sides.

The complete `opentaint-dataflow` module test suite passes. The 38 Java reachability fixtures also
pass in `SuffixTree` mode with `opentaint.suffix.verify=true`; these fixtures are the current non-empty
finding-set differential gate, including summary-language shadow checks. Tree remains the default
mode and its tests pass unchanged.

### 8.1 ThingsBoard measurement

On 2026-07-22, both modes analyzed the existing ThingsBoard code model (it was not rebuilt) with the
valid `java/security/ssrf.yaml:ssrf` filter, which generated 38 taint rules. This is one macOS
`/usr/bin/time -l` run per mode, so it is an engineering checkpoint rather than a statistically
stable benchmark:

| Metric | Tree | SuffixTree | Change |
| --- | ---: | ---: | ---: |
| IFDS time | 57.656 s | 14.305 s | 4.03x faster |
| Total wall time | 76.57 s | 32.24 s | 2.38x faster |
| Propagation steps | 7,765,917 | 1,184,641 | 6.56x fewer |
| Peak memory footprint | 22.260 GB | 15.669 GB | 29.6% lower |
| Maximum resident set | 15.767 GB | 13.419 GB | 14.9% lower |

Both measured runs reported zero findings. Their SARIF semantic diff is empty; the sole byte-level
difference is a trailing slash on the `%SRCROOT%` URI caused by the two CLI invocations. The table
uses production settings. A separate SuffixTree run with the complete Tree summary shadow enabled
finished without an invariant failure in 17.983 seconds of IFDS time and produced the same SARIF.
The zero-finding result means the measurement is useful for workload, language-equivalence
instrumentation, and output stability, but repeated runs remain required before treating the
numbers as statistically stable performance data.

### 8.2 Non-empty finding and trace differential

The existing Dynamic-TP compiled model was analyzed from the explicitly selected
`test.DtpNotifierSsrfTest#vulnerable` entry point with its current
`dtp-notifier-ssrf-hutool` rule. Tree and SuffixTree each reported exactly one finding with the same
rule ID. Trace generation succeeded in both modes, and the complete SARIF files are byte-identical.
SuffixTree ran with the summary verifier enabled. This supplements the 38 reachability fixtures with
an E2E non-empty SARIF and post-analysis trace-resolution gate.

The checkout contains a StirlingPDF source tree and earlier reports but no existing code model, so
the requested no-rebuild constraint currently prevents that E2E run.

## 9. Reuse and rejected shortcuts

Reusable material from `origin/dvvrd/suffix-wip` includes maximal factoring, the proof-of-concept
suffix-cone algorithms and oracle tests, broadening-event plumbing, diagnostics, and benchmark fixtures.
It is not merged wholesale because it is based on an older tree and generally slices the compressed
trie back into one generator per edge. That preserves many findings and compresses storage, but it
does not meet edge-level bundling or the mandatory grouped-identity invariant.

Rejected shortcuts:

- two independent suffix fact wrappers: branch selection can desynchronize the edge;
- eager expansion at every CFG hop: correct but destroys the main propagation win;
- reconstructing a merged final tree on every add: earlier experiments caused severe CPU and heap
  regressions;
- silent annihilation: derived work can be stranded unless broadening is published;
- changing Tree mode's default or semantics: Tree remains the differential baseline.
