# Loop fragments and feedback projection: proof dossier

Date: 2 November 2026. Status: scoped local proofs for the selected design.
No runtime implementation is changed.

Read [the specification](loop-fragments-and-demand-collapse.md),
[method-owned loop blocks](method-owned-loop-blocks.md),
[the model package](lean/proposals/loop-fragments-and-demand-collapse-20261102/README.md),
and [proof-guide.md](proof-guide.md). The receipt lists the exact checked
sources, theorem inventory, hashes and allowed logical dependencies.

## 1. Selected rule

One method analyzer owns an internal tree of sequential/loop blocks.
They share method registers, not edge stores. For one applied traversal
summary arm `I -> C`, at either repeat or leave output:

```text
FL(Zero) = 0
if FL(C) <= FL(I): propagate its result unchanged
otherwise: retain the union of images selected by
    (1) AL demand,
    (2) B demand after F is composed with persisted AL summaries,
    (3) next-body L demand.
Drop only when all three families reject the value.
```

The FL comparison uses the summary's fields in the current direction.
ZERO remains a typed endpoint. Whole ND execution remains AND; unary
arms are only restriction metadata. Saved replay uses the existing call
machinery. There is no new NORMAL reachability service.

## 2. Kernel results and their limits

`Control` has an executable finite source graph, a node partition, an
explicit feedback predicate and exact `(source,target,kind)` ports.
Every crossing or feedback edge routes through an exit and entry port.
Synthetic steps have no physical operation ID. Induction on finite walks
lifts each source path and erases each fragment path with the same ordered
physical trace. Reversing those transitions gives the backward theorem.
A rank certificate excludes positive closed internal body walks. A
same-owner one-node self-loop uses ports and has an acyclic body.
Composition of exact-factorization contracts supports recursive splitting.
These results do not construct or verify the Kotlin block decomposition.

`Geometry` uses finite field/base/full-mark namespaces and scalar EXACT/MAY
values with a layer and protection bit. Demand paths denote a trie. The
projection follows the trie and retains one distinguishing field before
cutting an unused suffix. Induction on the raw path proves prefix coverage
and the `min(global,maxDemandDepth+1)` depth bound. Base, mark and protection
stay equal. A lossy result is MAY/DEMAND; a NORMAL result is unchanged.
Reprojection is idempotent. An executable directory witnesses the finite
image. Binary words give the exponential Boolean-keep counterexample and
an eight-to-two projection witness. This is a direct-consumer proof; it
does not transport precision through arbitrary AL summary applications.

`selectProject` drops a value if eligibility is false. The former forced
fallback is retained only as `rejectedForcedProject`, a counterexample.
It is not selected behavior.

`Admission` copies the concrete-FULL EXACT/MAY C2 cells, including the
first-new-field rule and provisional MAY-to-EXACT DEMAND admission.
Kernel reduction checks binary paths within global limits 1, 2 and 3,
both tails/layers, and a demand directory containing the checked demand
plus zero or one extra guide. It checks 32,224 cells in 25 named chunks.
The certificate preserves the complete emitted initial and its layer.
It is a finite adapter check, not a theorem for arbitrary tries,
FLOW/STAR/MUST inputs, E/mx, statics or packed trees. Its exact-ancestor
example proves that forcing an unmatched exact value to MAY can add a
new provisional initial.

The Admission checker uses 2,048 MiB and one worker. An isolated check
used about 846 MiB. These are proof-verification resources, not analyzer
memory measurements.

`Guidance` constructs one unary restriction row per real ND member and
retains the complete executable edge. Its generic matching theorem takes
the existing match predicate. A metadata match cannot execute an
incomplete AND. Empty members do not become an unconditional ZERO rule.
Actual results retain the full original, conclusion, layer and protection.
The direction adapter orients each row with the existing opposite-run
entry/exit law. The finite example has two relevant arms, but only the
complete two-member input emits the result.

`Shape` defines typed ZERO depth as zero and DATA depth as counted path
length. It proves the strict growth classifier, equal/shrinking bypass,
and ZERO-to-field versus ZERO-to-root examples. Exact suffix application
has the same length delta as its summary. Equal/shrinking summaries do
not increase such a definite matched input. Separate executable ancestor
MAY cells show why that statement cannot be generalized to all inputs:
a root MAY input can gain a concrete output prefix even from an equal or
shrinking summary. ND arm classification retains the whole executable
edge and does not change its execution.

`Protocol` carries the complete original as an opaque identity. Projection
cannot change the owner, semantic context or port, or manufacture NORMAL
evidence. Producer observations stay before value projection. Publication
separately requires one complete row matching the original, port and exit
predicate. Geometry success cannot supply a missing row. The model does
not prove that a Kotlin callback has the required placement or that an
opaque identifier encodes each member of an ND binding.

`Restriction` gives an executable conservative reference for a fixed pure
complete observer. Its components include AL C2, native AL composition
plus full-B paired C5, L C2 and ND metadata. It tests proper positive
prefix cuts, shortest first, and accepts a MAY/DEMAND cut only if the
complete observation is unchanged. If no cut passes, it retains the raw
value. If the complete observation is empty, it drops the value. It
proves coverage, metadata preservation, no new NORMAL evidence,
determinism, idempotence, finite trial selection and shortest accepted
cut. A read-f example needs two fields: a one-field cut loses the B image.
The model assumes the observer adapter; it does not prove or implement
its production AP enumeration. Exact signature preservation is a
sufficient conservative reference, not a claim that every useful value
can be shortened.

`Feedback` models the exact single-field source/read/sink example.
A source at depth two followed by one read produces depth one without a
root sink hit. A second iteration preserves the old depth-one mark and
reads it to the root. The ZERO-to-depth-one summary is growing. Empty
AL/B-DATA consumers drop the needed intermediate value under the rejected
two-test rule. Adding the successful L check retains it and preserves the
second-iteration observation. Union theorems show that the three-family
check rejects exactly when all reject, and retains every old positive
two-family answer. This is an exact-path reference counterexample and
repair, not a complete outlined-driver theorem.

`Decomposition` constructs an ordered-region tree. It splits at the first
loop, retains the prefix as BL, and recursively places the complete
remaining sequence under AL. Structural induction proves that flattening
the tree gives the exact original segment list, preserving order and
multiplicity. An arbitrary supplied ordered interpretation therefore
stays equal. The model handles empty prefixes and proves that AL depth
accounts for every successive loop. Its executable two-loop example is
`(prefix, loop1, ({}, loop2, suffix))`. Loop atoms are opaque selected
regions; general CFG detection, inner-body extraction and AP summary
composition remain outside this local theorem.

`Blocks` models a supplied containment layout under one method owner.
Its parent-depth certificate rules out every positive containment cycle.
Each instruction has one lowest owner. Blocks address identical original
register IDs, and identity boundary transport keeps the entire opaque AP
payload. An alias request retains the same method, original instruction
and value. Indexed updates change only the selected block and processed
point, not another block or a successor's store. Direction-labelled
repeat/leave routing is symmetric. Both loop output categories invoke the
strict shape gate; sequential output bypasses it. Retained results keep
the actual port and destination. Child composition keeps the parent
original, and only root rows use the public summary interface. Every
selected internal refinement row appears in the method's tagged frontier;
an empty collected frontier cannot hide an admitted internal row.
These are local ownership/transport laws for supplied valid metadata.
They do not implement the decomposition, actual alias query, AP C5 or
counted-work scheduler.

`Usefulness` is an earlier reference investigation, not a selected runtime
component. For a supplied finite graph it proves executable certified
NORMAL reachability. The selected design instead reuses native saved
replay. Do not infer an AP graph service, cache or pending graph-scope
decision from this retained model.

## 3. Native evidence for the next-body case

The [native control record](lean/proposals/loop-fragments-and-demand-collapse-20261102/controls.md)
embeds the code-under-analysis, principal trace, selected native output,
repeat command and limits. Its linked test source is part of this package.
Two finite fixture tests passed on analyzer `8213756108af9cd278668db871fc77428caec64a`.
The whole-loop FULL test completed **run-3**, with one report and no
outgoing demand, under limits `1,1,2,…`.

One test uses the real driver and source/sink call stages to establish the
internal two-iteration path. A separate test uses production DemandStore
C2/C5 to establish a legal growing body result. The separate pair is not
claimed to be a recorded synthetic-body handoff from the first test.
No method-owned block runtime or new gate has been executed. These controls support
the counterexample's premises without presenting local checks as an
end-to-end implementation proof.

## 4. Remaining implementation correspondence obligations

Before runtime implementation, establish:

1. The method-owned layout builder constructs the finite block tree,
   instruction partition, exact ports and body rank certificate, including
   nested, self and irreducible loops. It reuses stable IDs across runs.
2. Original instruction/rule identities, aliases, mutable arguments and
   exceptional/nonreturning observations implement the control contract.
   Original boundary rules execute once at the real method boundary.
   Blocks use original register IDs and original alias queries; internal
   transitions do not add call bindings or alias expansion.
3. Three consumer adapters use the correct direction, port and complete
   original. The direction-appropriate AL/BL composition constructs a
   full enclosing-B edge. L guidance includes
   the required next-body admission; it is not replaced by B exit demand.
4. Precision transport preserves each selected C2/composed-C5 image.
   A prefix-trie geometry match alone is not that proof. Every actual
   publication still requires one complete paired C5 row.
5. FLOW, STAR/MUST, static anchors, E/mx and packed protection masks satisfy
   the stated scalar projection and typed-control contracts.
6. Every relevant cut has the ordinary summary/Target handoff needed for
   later refinement. Local finite feedback does not prove a driver
   iteration will occur, or prove general convergence.
7. Method work and handoff collect pending internal delivery and selected
   block refinement. Local summary rows do not leak into the external
   method interface; CFG delivery cannot bypass a block-output gate.
8. Production tests cover the selected rule before fixed project
   measurements. Report the latest reached/completed/accepted iteration.

The proof package deliberately reports local-model PASS. It does not claim
whole-analyzer soundness, finding-set equality, universal termination or
a measured speedup. The newly selected restriction can delay findings;
exact CFG equivalence alone does not justify those approximation changes.
