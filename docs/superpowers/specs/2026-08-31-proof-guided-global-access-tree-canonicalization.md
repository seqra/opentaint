# Fact-explosion mitigation after global access-tree canonicalization

## Outcome

Conductor retained many equal access-tree nodes in different storage slots. It also retained two one-element arrays for most path nodes. This state was investigated as a possible cause of the low-memory stop.

Global canonicalization and the compact child representation are insufficient on their own. Revisions 1 through 10 of the synthetic star arm ended with status 253 or 254. Status 253 is an out-of-memory stop. Status 254 is an IFDS timeout. Neither status is a successful analysis.

The accepted synthetic mitigation stops materializing concrete branches out of `[any]` in TIFA. It emits the same demanded premise and virtually descends through `AccessNode.getChild` on later rounds. A per-walk identity memo also prevents the `[any]` suffix matcher from evaluating a shared DAG subtree once per incoming path.

With these changes, two star replicates completed with status 0 in 8.1 and 8.3 seconds, and two concrete-chain replicates completed with status 0 in 5.8 seconds. Every run retained its one SARIF finding. The star live-heap floor was 24 and 163 MiB, with no low-memory stop or soft-reference cleanup.

The latest available conductor e2e run predates this TIFA change. Build `ee45055c9` exited with status 253 after 946.6 seconds, peaked at 8.44 GB, and wrote a partial report with 3 findings. The e2e base completed in 182.1 seconds at 7.89 GB with 7 findings. That run rejects canonicalization as a mitigation; it does not validate or reject the demand-only TIFA implementation. A current conductor rerun remains required.

The attempted implementation does these operations:

- It canonicalizes every tree that enters an edge, summary, or final-fact storage.
- It uses one bounded canonical index for each `TreeApManager`.
- It includes all semantic fields in equality and hashing.
- It shares one-element accessor-label arrays by accessor index.
- It stores child state in one tagged field: `null`, one child, or a child array.
- It reuses the first canonical node. It does not copy a tree only to mark it canonical.

Canonicalization does not intentionally remove a fact path. The final TIFA change preserves the demanded premise family while removing the stored carrier copies that repeatedly reintroduced `[any]`. The fixed point now completes on the existing star repro without losing its finding.

## Evidence

The investigation separated insufficient or unsound changes from the accepted one:

- The `[any]` manager limited an operation that created only a small part of the node mass.
- Matcher memoization reduced repeated DAG work but did not change the star timeout.
- Demand-only TIFA keeps the same premise family and removes the stored copies; this is the change that made the star arm converge.
- Literal `[any]` matching removed the premise family, but it also removed the mark-naming premise and lost the conductor findings.
- Sibling absorption converged, but it deleted literal names and lost the same findings.

A conductor heap census found 20.7 million live `AccessNode` objects. A cross-slot sample found 29,009 node occurrences and 11,119 structurally different nodes. The measured sharing factor was 2.61 in that sample.

The e2e comparison establishes a branch-level failure, not the sole cause of that failure. Its base is `17eb0feda`, its new build is `ee45055c9`, and the revisions diverge at `cbe3b3ffc`. Many changes exist on the new branch after that merge base. A same-parent conductor comparison is required to attribute the regression specifically to global canonicalization.

The fact tree was load-bearing in two ways. Its shape represented taint semantics. Its concrete premise names also selected the TIFA rules that produced the finding. The accepted change therefore preserves concrete premise names and changes only how TIFA reaches them: virtual reads replace mutations of the accumulated fact.

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
| 8 | Do not clone first canonical trees | 254, 254, 254 at about 245 s | 1, 1, 1 | Rejected: timeout |
| 9 | Use one tagged child-storage field | 254 at 246 s | 1 | Rejected: timeout |
| 10 | Memoize `[any]` suffix matching over the fact DAG | 254 at the 90 s checkpoint | 1 | Rejected: timeout |
| 11 | Emit demand without materializing `[any]` branches in TIFA | 0 at 8.1 s, 0 at 8.3 s | 1, 1 | Accepted on synthetic gate |

Return code 254 is the configured IFDS timeout. It is distinct from the low-memory stop, but it is still a failed analysis. The three revision-8 star runs recorded zero low-memory stops and retained one finding, but none completed. Their progress values were 39,777, 39,821, and 39,797 events. The concrete-chain arm returned 0 in about 6.1 seconds and retained its finding; that control does not establish success on the exploding input.

The tagged-union JAR was checked again at the same budget. Its star arm returned 254 at 245.7 seconds with 39,739 progress events and one finding. This result is rejected. Its chain arm returned 0 at 6.1 seconds with one finding.

The memoized-matcher checkpoint returned 254 after 18,392 progress events, effectively equal to the 18,408 and 18,432 controls. Demand-only TIFA then completed the same input with 4,815 progress events in both full-budget replicates. The chain control remained at 2,248 progress events and kept its finding.

This is an accepted mitigation for the existing synthetic gate. The available real conductor e2e run still describes the pre-fix branch state, so no current conductor result is claimed.

## Verification evidence

- The feature branch and `saloed/5-default-get` have the same merge base: `4c358d2e16450b3bdb4254955be5cbda61e9cb7c`.
- `lake build` completes the executable model and all proofs.
- `lake env lean FactExplosion/Audit.lean` shows only `propext` and `Quot.sound`. A source scan finds no `sorry`, `axiom`, `Classical`, `classical`, or `noncomputable` term.
- The dataflow module has 163 tests. It has zero failures, zero errors, and zero skipped tests.
- `projectAnalyzerJar` succeeds. The accepted JAR hash prefix is `2d69f3cbc05252d7`.
- Two chain and two star regression runs use this JAR hash. All four return 0 and retain one SARIF finding.
- The latest conductor e2e new build uses `ee45055c9`, exits 253, and produces a partial report. It predates the demand-only TIFA change.
- `git diff --check` succeeds.

The formal equivalence scope is all finite trees in the production accessor and exclusion data model. The formal matcher is a finite observation of these trees. The proof first reconstructs the complete source tree. Therefore, each pure tree observation has the same input after decoding. These proofs establish semantic preservation and abstract cost bounds for canonicalization only. TIFA premise preservation is covered by the cross-backend scenario suite and the finding-preserving synthetic gate.
