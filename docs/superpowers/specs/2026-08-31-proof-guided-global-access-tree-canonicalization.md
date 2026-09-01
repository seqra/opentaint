# Fact-explosion mitigation after global access-tree canonicalization

## Outcome

Conductor retained many equal access-tree nodes in different storage slots. It also retained two one-element arrays for most path nodes. This state was investigated as a possible cause of the low-memory stop.

Global canonicalization and the compact child representation are insufficient on their own. Revisions 1 through 10 of the synthetic star arm ended with status 253 or 254. Status 253 is an out-of-memory stop. Status 254 is an IFDS timeout. Neither status is a successful analysis.

The synthetic mitigation stops materializing concrete branches out of `[any]` in TIFA. It emits the same demanded premise and virtually descends through `AccessNode.getChild` on later rounds. A per-walk identity memo also prevents the `[any]` suffix matcher from evaluating a shared DAG subtree once per incoming path.

With these changes, two star replicates completed with status 0 in 8.1 and 8.3 seconds, and two concrete-chain replicates completed with status 0 in 5.8 seconds. Every run retained its one SARIF finding. The star live-heap floor was 24 and 163 MiB, with no low-memory stop or soft-reference cleanup.

The current local conductor run rejects this mitigation. Build `77005d447` reached the low-memory guard 4 minutes 57 seconds into the full phase with peak RSS 9,712,704 KiB under an 8 GiB Java heap. The six vulnerabilities counted before cancellation are partial output. Trace generation also hit the guard and did not complete. A memory guard, status 253, and status 254 are all failures; none establish a fixed point.

Two exact retention refinements also fail the conductor gate. Sparse instruction rows, sparse prefix indices, and lazy child maps reached 7,734,532,832 bytes at a 7,730,941,132-byte guard. Packing five `AccessNode` metadata fields into one integer and removing storage-local interner wrappers then reached 7,732,343,416 bytes at the same guard. Both runs were stopped at the first guard event and are counterexamples, not successful mitigations.

The attempted implementation does these operations:

- It canonicalizes every tree that enters an edge, summary, or final-fact storage.
- It uses one bounded canonical index for each `TreeApManager`.
- It includes all semantic fields in equality and hashing.
- It shares one-element accessor-label arrays by accessor index.
- It stores child state in one tagged field: `null`, one child, or a child array.
- It reuses the first canonical node. It does not copy a tree only to mark it canonical.

Canonicalization does not intentionally remove a fact path. The TIFA change preserves the demanded premise family while removing stored carrier copies that repeatedly reintroduced `[any]`. The synthetic fixed point completes, but conductor proves that removing this producer does not bound total retained facts.

## Evidence

The investigation separated insufficient or unsound changes from the accepted one:

- The `[any]` manager limited an operation that created only a small part of the node mass.
- Matcher memoization reduced repeated DAG work but did not change the star timeout.
- Demand-only TIFA keeps the same premise family and removes the stored copies; this made the star arm converge but did not prevent the conductor memory guard.
- Literal `[any]` matching removed the premise family, but it also removed the mark-naming premise and lost the conductor findings.
- Sibling absorption in premise and edge stores deleted literal names and lost the same findings.
- Summary-only sibling absorption is a separate widening: summary readers resolve a covered literal through `[any]`, while the storage publishes the exact unfurled arrival as its delta.

A conductor heap census found 20.7 million live `AccessNode` objects. A cross-slot sample found 29,009 node occurrences and 11,119 structurally different nodes. The measured sharing factor was 2.61 in that sample.

The e2e comparison establishes a branch-level failure, not the sole cause of that failure. Its base is `17eb0feda`, its new build is `ee45055c9`, and the revisions diverge at `cbe3b3ffc`. Many changes exist on the new branch after that merge base. A same-parent conductor comparison is required to attribute the regression specifically to global canonicalization.

The fact tree was load-bearing in two ways. Its shape represented taint semantics. Its concrete premise names also selected the TIFA rules that produced the finding. The exact TIFA refinement therefore preserves concrete premise names and changes only how TIFA reaches them: virtual reads replace mutations of the accumulated fact.

The next refinement is representation-only retention compression. Premise-trie child maps are allocated only when a child exists, per-instruction facts are keyed by occupied instruction coordinates, and access-tree prefix indices store the exact ascending member indices sparsely before promoting to a dense set. No premise, fact, exclusion, summary, or subscription is removed.

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

`Retention.lean` records all three conductor counterexamples: zero TIFA carrier copies is compatible with retained fact growth, and the baseline, structural-retention, and packed-metadata runs each exceed their configured guard. Its refined executable representation keeps the same index-member list across sparse-to-dense promotion. The cost theorems state the exact-retention invariant: instruction storage scales with occupied coordinates and sparse prefix-index storage scales with exact membership population, each bounded by its dense coordinate space. The packed metadata round trip proves that the layout change preserves all five values.

The next CEGAR model separates retained summaries from published deltas. `SummaryBranches.absorb` moves one covered concrete branch into `[any]`. `absorb_preserves_late_queries` proves that every fact visible to a late query before the fold remains visible afterward. `storeAndPublish` retains the widened value but returns the original arrival, and `honest_delta_publication` proves that publication is exact.

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

Only final-fact summary storages apply covered-sibling absorption. They merge with `foldToAny = false`, retain the folded tree, and accumulate the unfurled merge delta. Premise, edge, TIFA, and subscription stores do not use this widening. A late summary subscriber calls the same denotational `getChild` reader modeled in Lean, which combines the concrete branch with the `[any]` branch for covered accessors.

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
- covered-sibling absorption reaches a fixpoint by object identity;
- a late literal query reads an absorbed summary branch through `[any]`;
- summary retention folds the stored value while delta publication keeps the exact literal arrival.
- subscription row storage uses `null`, a singleton row index, or a primitive row list without changing row membership;
- JVM wildcard unrolling materializes only fields resolved by exact class, name, and type, while unknown classes retain the conservative behavior.

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
| 11 | Emit demand without materializing `[any]` branches in TIFA | 0 at 8.1 s, 0 at 8.3 s | 1, 1 | Synthetic pass; conductor counterexample |
| 12 | Same build on local conductor | memory guard at 4m57, peak 9,712,704 KiB | 6 partial | Rejected |
| 13 | Sparse occupied-coordinate storage and lazy maps | memory guard at 7,734,532,832 bytes | not completed | Rejected |
| 14 | Packed node metadata and manager-owned interner use | memory guard at 7,732,343,416 bytes | not completed | Rejected |
| 15 | Summary-only covered-sibling absorption with honest delta | memory guard at 7,747,749,408 bytes | not completed | Rejected |

The final local-conductor CEGAR loop used the generated Conductor project with 24,860 loaded rules, an 8 GiB heap, a 7,730,941,132-byte measured-heap guard, and the configured 1080-second IFDS timeout. Status 253 is the guard stop and status 254 is the analyzer timeout; neither is accepted.

| Refinement | Status / elapsed | Peak measured heap | Traces / SARIF | Decision |
| --- | ---: | ---: | ---: | --- |
| Incremental TIFA replay | 254 / 948 s | 7,708,332,032 | 8 / 8 | Rejected: timeout |
| Publish requirements only for newly retained summary edges | 0 / 135 s | 7,543,865,242 | 0 / 0 | Rejected: semantic counterexample |
| Exact delayed-depth frontier scheduling | 254 / 928 s | 7,706,509,312 | 8 / 8 | Rejected: timeout |
| Summary compression threshold 100 | 253 / 839 s | 7,746,922,906 | incomplete | Rejected: guard |
| Summary compression threshold 10 | 253 / 850 s | 7,827,762,483 | incomplete | Rejected: guard |
| Tagged subscription rows, threshold 100 | 254 / 931 s | 7,714,125,824 | 8 / 8 | Rejected: timeout |
| Same representation with 90% full-scan share | 254 / 1,029 s | 7,727,392,973 | 8 / 8 | Rejected: timeout |
| Concrete-field-only JVM wildcard unrolling | 0 / 139 s | 7,537,366,938 | 8 / 8 | Accepted |
| Identical replicate | 0 / 141 s | 7,380,570,624 | 8 / 8 | Accepted |

Return code 254 is the configured IFDS timeout. It is distinct from the low-memory stop, but it is still a failed analysis. The three revision-8 star runs recorded zero low-memory stops and retained one finding, but none completed. Their progress values were 39,777, 39,821, and 39,797 events. The concrete-chain arm returned 0 in about 6.1 seconds and retained its finding; that control does not establish success on the exploding input.

The tagged-union JAR was checked again at the same budget. Its star arm returned 254 at 245.7 seconds with 39,739 progress events and one finding. This result is rejected. Its chain arm returned 0 at 6.1 seconds with one finding.

The memoized-matcher checkpoint returned 254 after 18,392 progress events, effectively equal to the 18,408 and 18,432 controls. Demand-only TIFA then completed the same input with 4,815 progress events in both full-budget replicates. The chain control remained at 2,248 progress events and kept its finding.

The accepted refinement reduces full-scan work from 4,549,826 events at the last timeout to 340,173 completed events. Both accepted runs report `TraceGenerationStats(total=8, simple=4, generatedSuccess=4, generationFailed=0)` and eight SARIF results.

## Verification evidence

- The feature branch and `saloed/5-default-get` have the same merge base: `4c358d2e16450b3bdb4254955be5cbda61e9cb7c`.
- `lake build FactExplosion.Audit` completes the executable model and all proofs.
- `lake env lean FactExplosion/Audit.lean` shows only `propext` and `Quot.sound`. A source scan finds no `sorry`, `axiom`, `Classical`, `classical`, or `noncomputable` term.
- The dataflow module, including the summary-retention tests, has zero failures, zero errors, and zero skipped tests.
- `projectAnalyzerJar` succeeds. The accepted JAR SHA-256 is `056236fda7541ffdfacef953a760302c09be7f048370208a32a86586cdfaaa9d`.
- Two identical local-conductor runs use this JAR hash. Both return 0, stay below the guard, preserve the exact trace statistics, and emit eight SARIF results.
- `git diff --check` succeeds.

The formal equivalence scope is all finite trees in the production accessor and exclusion data model. The formal matcher is a finite observation of these trees. The proof first reconstructs the complete source tree. Therefore, each pure tree observation has the same input after decoding. The retention model additionally proves incremental replay equivalence, exact tagged-row membership, and equality between wildcard denotation and concrete-field unrolling. TIFA premise preservation is covered by the cross-backend scenario suite and the two accepted conductor gates.
