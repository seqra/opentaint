# Global access-tree canonicalization

## Result

Conductor retained many equal access-tree nodes in different storage slots. It also retained two one-element arrays for most path nodes. This state caused the low-memory stop.

The implementation now does these operations:

- It canonicalizes every tree that enters an edge, summary, or final-fact storage.
- It uses one bounded canonical index for each `TreeApManager`.
- It includes all semantic fields in equality and hashing.
- It shares one-element accessor-label arrays by accessor index.
- It stores child state in one tagged field: `null`, one child, or a child array.
- It reuses the first canonical node. It does not copy a tree only to mark it canonical.

The implementation does not remove a fact path. It does not change premise emission, `[any]` matching, cleaners, summaries, exclusions, or the fixed-point operation.

## Evidence

The semantic prototypes did not give a safe change:

- The `[any]` manager limited an operation that created only a small part of the node mass.
- TIFA-no-unroll removed copies, but it kept the same premise family.
- Literal `[any]` matching removed the premise family, but it also removed the mark-naming premise and lost the conductor findings.
- Sibling absorption converged, but it deleted literal names and lost the same findings.

A conductor heap census found 20.7 million live `AccessNode` objects. A cross-slot sample found 29,009 node occurrences and 11,119 structurally different nodes. The measured sharing factor was 2.61 in that sample.

The fact tree was load-bearing in two ways. Its shape represented taint semantics. Its concrete premise names also selected the TIFA rules that produced the finding. Therefore, the mitigation changes representation only.

## Formal scope

The Lean scope contains all finite, immutable access trees used by this representation. A node contains these values:

- the abstract flag;
- the final flag;
- the deep field exclusion;
- an ordered list of accessor and child pairs.

The model includes fields, elements, marks, static accessors, value accessors, final accessors, type groups, type values, and `[any]`. Its deep exclusion value has the production depth-0 and depth-1 lists. The executable matcher uses fuel to give a finite observation. The implementation does not need fuel because it returns the same tree.

The practical scope is exact for these trees. The canonical index can discard an old batch at its retention bound. This action can reduce later sharing. The bounded model proves that it cannot change an input value. Therefore, it cannot change matching or a finding.

## Constructive proof

The Lean model is in `formal/fact-explosion`.

`Concept.lean` defines the baseline tree, its shape rules, node count, subtree list, and executable matching.

`Canonical.lean` constructs the set of all different semantic subtrees. It also proves the lookup and cost properties that the indexed encoder uses.

`Indexed.lean` defines the production-shaped optimization. An indexed row contains flags, exclusions, and a list of `(edge, child-index)` pairs. It does not contain a recursive `AccessTree`. An `IndexedDag` contains the flat row table and the root indices. Its encoder, decoder, matcher, and shape checker are executable. The main results are these theorems:

- `encodeIndexedRoot_witness` returns a concrete root index and an exact decoded tree.
- `encodedRoot_sound` proves that each stored root index comes from an input fact and decodes to it.
- `encodedDag_references_valid` proves that each child index resolves to a row.
- `indexed_accepts_exactly` proves the same match result for each matcher fuel and path.
- `indexed_wellFormed_exactly` proves that encoding keeps the full shape result.
- `indexedNodes_nodup` proves that the flat row table has no equal rows.
- `indexedNodeCost_le_occurrenceCost` proves that indexed row count is not larger than baseline node-object count.

`Complexity.lean` separates the concept from both layout optimizations.

- For `n + 1` equal facts, the baseline stores `n + 1` node occurrences. The indexed representation stores one flat row and `n + 1` root references.
- For `n + 1` singleton nodes with one repeated accessor, the baseline uses `2 * (n + 1)` label and child arrays. The optimized representation uses one shared label array and no child arrays.
- For `n` nodes, split singleton and array storage uses `2 * n` child-reference slots. The tagged union uses `n` slots.

The slot result is a representation invariant, not a shallow-size claim. A Java instrumentation measurement on the test VM reports 56 bytes for an `AccessNode` before and after the tagged-union change. HotSpot object alignment consumes the removed four-byte compressed reference on this layout.

`Bounded.lean` models the production retention policy. A hit returns the stored equal tree. A miss clears a full cache and inserts the input tree. The proofs show these properties:

- each returned value equals its input tree;
- a sequence returns the exact input values;
- a positive limit bounds the cache after each operation and sequence;
- `n + 1` repeated equal trees keep one representative for every positive limit.

The model does not use `Classical.choice`, excluded middle, `sorry`, or an application axiom. Each existence result gives an executable witness. `Audit.lean` prints the axiom set of the main theorems. It contains only Lean proposition and quotient extensionality support.

## CEGAR counterexample

The first key omitted the deep exclusion because the old `AccessTreeInterner` equality also omitted it.

`Counterexample.lean` constructs two abstract nodes. They have the same flags and children. One excludes field 0 and one excludes field 1. The incomplete key treats them as equal, but the executable matcher returns different results for field 0.

`exclusion_must_be_in_key` rejects that key. The production key includes the deep exclusion. This is a correctness repair and a performance change.

The old node hash also omitted accessor labels. Unrelated nodes could enter the same bucket. The new ordered hash includes each accessor label and its child hash. A hash collision still uses full structural equality.

## Production design

`TreeApManager` owns a synchronized canonical index with at most 250,000 entries. Storage wrappers for that manager use the same index. Managers do not share nodes.

The key contains these values:

- abstract flag;
- final flag;
- deep exclusion;
- ordered accessor labels;
- corresponding child trees.

Global canonicalization first checks for a known root. A hit returns the known tree without walking its children. A miss canonicalizes children from the bottom up and keeps the first root object. Operation-local interning stays separate, so a local marker cannot prevent later manager-wide canonicalization.

Each one-child node gets its label array from a manager flyweight table. One private `Any?` field represents the child union. It is `null` for no children, an `AccessNode` for one child, and an `Array<AccessNode>` for two or more children. Utility methods expose indexed access and an array view to the existing algorithms.

The storage identity rule stays valid. A merge that adds no information still returns the stored object. Canonicalization can select an older equal object only at a storage write point that already accepts an equal replacement.

## TDD coverage

The focused tests cover these properties:

- wrappers under one manager select one canonical node;
- the first write to a small storage is canonicalized;
- operation-local nodes are canonicalized again at a global boundary;
- different managers stay isolated;
- deep exclusions remain part of identity, including a colliding-hash example;
- accessor labels affect the hash;
- concurrent wrappers select one representative;
- the retention bound discards an old batch safely;
- reference cleanup does not remove the manager index;
- singleton labels share one array;
- child storage is `null` for leaves;
- singleton children are stored directly and reject an out-of-range index;
- multiple children use an array;
- `AccessNode` has one child-storage field;
- first-time global canonicalization keeps the original object.

The full dataflow module suite must also pass.

## Practical CEGAR record

All star runs used the same generated project, rules, 3 GiB heap, and finding check from `saloed/41-repro-base-oom`. Production work started from `saloed/5-default-get`.

| Revision | Exact refinement | Star result | Finding | Decision |
| --- | --- | ---: | ---: | --- |
| Base | Storage-local, threshold interning | 253 at about 235 s | 1 | Counterexample |
| 1 | Manager-wide index at old thresholds | 253 at 189 s | 1 | Counterexample |
| 2 | Canonicalize every storage write | 253 at 235 s | 1 | Counterexample |
| 3 | Weak manager index | 253 at 229 s | 1 | Counterexample |
| 4 | Separate local and global state | 253 at 247 s | 1 | Counterexample |
| 5 | Bound the strong index | 253 at 227 s | 1 | Counterexample |
| 6 | Share singleton label arrays | 254, then 253 | 1, 1 | Variance counterexample |
| 7 | Store singleton children without arrays | 253 at 248 s | 1 | Counterexample |
| 8 | Do not clone first canonical trees | 254, 254, 254 at about 245 s | 1, 1, 1 | Accepted |
| 9 | Use one tagged child-storage field | 254 at 246 s | 1 | Accepted |

Return code 254 is the configured IFDS timeout. It is not a low-memory stop. All three accepted star runs recorded zero low-memory stops and retained the finding. Their progress values were 39,777, 39,821, and 39,797 events. The concrete-chain arm returned 0 in about 6.1 seconds and retained its finding.

The tagged-union JAR was checked again at the same budget. Its star arm returned 254 at 245.7 seconds with zero low-memory stops, 39,739 progress events, and one finding. Its chain arm returned 0 at 6.1 seconds with one finding.

This result mitigates the fact-explosion memory failure. It does not prove that the star fixed point converges inside the current time limit.

## Completion evidence

- The feature branch and `saloed/5-default-get` have the same merge base: `4c358d2e16450b3bdb4254955be5cbda61e9cb7c`.
- `lake build` completes the executable model and all proofs.
- `lake env lean FactExplosion/Audit.lean` shows only `propext` and `Quot.sound`. A source scan finds no `sorry`, `axiom`, `Classical`, `classical`, or `noncomputable` term.
- The dataflow module has 162 tests. It has zero failures, zero errors, and zero skipped tests.
- `projectAnalyzerJar` succeeds. The tagged-union JAR hash prefix is `3cabd8e8489b520d`.
- The chain and star regression runs use this JAR hash and retain their findings.
- `git diff --check` succeeds.

The formal equivalence scope is all finite trees in the production accessor and exclusion data model. The formal matcher is a finite observation of these trees. The proof first reconstructs the complete source tree. Therefore, each pure tree observation has the same input after decoding. The practical gate also checks the production matcher, premise selection, and finding output on conductor.
