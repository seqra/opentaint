# Checked proposal model: input admission

This package is **proposal and formal model only**. It changes no analyzer
implementation. The base runtime is
`edb2e06cdb17eecafbe03415236bf56c57910239`.
The next proposal is
[bidirectional-input-admission-delivery-next-iteration-20261030.md](../../../../docs/design/bidirectional-input-admission-delivery-next-iteration-20261030.md).
The checker binds the proposal hash. Run the checker again after the proposal
or model changes.

```sh
python3 spec/lean/proposals/input-admission-next-20261030/check.py
```

Use `leanprover/lean4:v4.33.1`. The checker uses one CPU, one Lean worker,
a 768 MiB memory limit and a 90-second bound for each command. It audits all
public definitions and named theorems, rejects proof holes and noncomputable
source, and records kernel axiom dependencies. Generated logs stay under
ignored `spec/lean/.lake/verification/input-admission-next-20261030/`.

The current model has **28 named theorems and 55 audited declarations**. The only
audited axiom dependencies are `propext` and `Quot.sound`. It uses no custom
axiom or Classical.choice. Executable finite controls return actual roots
and optional delta values.

## Exact merge kernel

A coordinate is a full field path, EXACT/ANY leaf kind and full mark. Roots
are finite Boolean functions. Set difference is literal coordinate difference,
not AP prefix coverage. Let:

```text
R0 = old ordinary root        P0 = old protected mask, P0 ⊆ R0
R1 = offered ordinary root    P1 = offered protected mask, P1 ⊆ R1
D  = R1 \ R0                 dP = P1 \ P0
Q  = D ∪ dP                  P  = P0 ∪ P1
```

The model proves:

- P is included in R0∪R1.
- P∩Q=dP, and dP is included in Q.
- If D and dP are empty, both retained annotated state and absent delta are
  equal to the old state and absent delta.
- The full reference merge and proposed merge return equal annotated stored
  trees and optional delta trees.
- Header canonicalization is the same supplied function in both constructors.
- General trimming still produces an included mask outside these proved paths.

The no-op theorem uses an already-canonical old header. This is an existing
factory invariant, not a new semantic input filter. Both inputs have the same
complete typed header as required by the current merge operation.

The cost model counts normalization calls, not trie-node visits or elapsed
time. A protected merge can remove one stored-tree normalization call and,
when a delta exists, one delta-tree normalization call. A no-op constructs no
new tree. A normalization call may already be cheap when its mask is the same
object as its ordinary root. No whole-engine speedup follows from this model.

The retained negative control is:

```text
old R={a/T}, P={a/T}
offered R={a/T,b/U}, P={a/T}
delta R={b/U}, P={}
```

The merged mask is not a valid delta mask. The proposed algorithm uses dP,
which is empty here. Additional executable controls cover exact duplicates,
ordinary growth, annotation-only growth, and attempted annotation downgrade.

## Fresh links and the source adapter

`imageRows` executes a finite leafwise transfer. `image_distributes` proves
literal union distributivity. `old_and_delta_cover_union` proves
R0∪Q=R0∪R1. `fresh_link_observations_exact` combines these facts: after prior
input is delivered, linking Q gives the same cumulative output observations
as linking the complete offered root.

This is a constructive finite kernel, not an axiom that the Kotlin C2
implementation is distributive. A future implementation must establish:

1. `LeafAlgebra.mergeAddDelta` returns exact coordinate difference. Matched
   child accessors recurse; incoming-only children are delta children; each
   leaf delta is incoming-minus-old. The same-node shortcut has no delta.
2. `minusNode` subtracts exact coordinates for annotationDelta.
3. Current `limit` followed by full initial emission is a leafwise image for
   a fixed run, direction, field limit, method, demand snapshot and mark table.
   Keep exact/ANY parents and children; use no AP-coverage compaction.
4. Delta header canonicalization preserves the emitted leaf shapes. A fresh
   exact-only delta can have canonical Empty E/ANY_TAINT even when its parent
   stored group retains E and another any-tail.
5. The actual C2 algorithm returns the complete leafwise image, including
   its local and static completion searches and its coverage-based stop.
6. Every admitted fresh delta is linked by the existing required send path.
   An incomplete/cancelled send is not a successful fixed point.

The fresh-link change is for restricted runs only. Run-1 input/request/static
logic stays as it is. Keep each caller subscription, its full CallerRef,
ND bindings, replay and summary delivery. Only the callee-analysis link uses
the admitted fresh delta. A normal input with a ZERO origin is not a
zero-only control port. The explicit backward ZeroIn path stays unchanged.

## Limits

The checker binds reviewed runtime source hashes. It does not verify Kotlin,
IR transfer, field-limit or emitter adapters, publication ordering, reports,
cancellation, concurrency or runtime performance. No new field/mark/layer
semantics, input filter, support label, semantic-key flag or storage cache is
authorized by the kernel proofs. Runtime implementation and differential
adapter/interleaving tests remain future work.
