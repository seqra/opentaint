# Constant filtering and Target-guided ZERO: implementation proofs

Date: 31 October 2026. This package checks the selected implementation
proposal. It does not change or verify the Kotlin runtime.

- [Specification](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md)
- [Implementation proposal](../../../../docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md)
- [Proof guide](../../../proof-guide.md)

The specification SHA-256 is
`8ae901c30188e81a09030491291dbb86a749e017a6d0b4b3218664821494c21a`.
The reviewed runtime is based on
`e090118e5f9603f1973c0578a3e04998035f4508`.

## Reproduce the check

From the repository root, run:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/check.py
```

Use Lean `leanprover/lean4:v4.33.1`. The checker selects this toolchain
through `ELAN_TOOLCHAIN`. It compiles one module at a time with one worker,
one CPU, a 768 MiB Lean memory limit, and a 90-second command timeout.
It needs no project build or project analysis.

The package has 12 modules, 193 theorems, 174 public executable
definitions, and 2 public abbreviations. The checker audits all 369
explicit public declarations. Only `propext` and `Quot.sound` are permitted. No classical
choice, `sorryAx`, custom axiom, `noncomputable`, `unsafe`, or `partial`
declaration is permitted. A compiler warning fails the check.

The generated [checks.json](checks.json) records the result, every audited
declaration, the toolchain, input hashes, and log locations. The checker
binds the specification, implementation proposal, this README, its own
code, the models, and the reviewed runtime source files. Generated logs
and `.olean` files go to the ignored
`spec/lean/.lake/verification/constant-filter-target-zero-implementation-v2-20261031/`
directory. They are not maintained proof inputs.

## Selected rules

```text
Constant in runtime data or any premise member -> reject the whole packet
EXACT demand + submitted ANY at any prefix     -> no initial
all current offers fail admission             -> no extra action

complete NORMAL sink binding -> NormalTarget(id)
complete DEMAND sink binding -> DemandTarget
accepted actual reverse GEN  -> DemandTarget

NormalTarget + complete all-NORMAL support -> same NormalTarget(id)
NormalTarget + DEMAND or native demotion    -> no result
NormalTarget in backward                   -> ignored
DemandTarget + permitted complete support  -> anonymous DemandTarget

persisted full owned NORMAL key -> no new owned emission/publication
persisted ZERO -> NormalTarget  -> skip replay; keep the settled report

final report <- configured-root ZERO -> NormalTarget(id)
next-run Target guidance <- DemandTarget only
```

Target is a terminal conclusion outside AP facts. C2 control admission
uses an actual ZERO. C5 tests the actual premise against `D_c` and the
actual conclusion against `D_p`, using one demand row. A ZERO `D_p`
accepts ZERO and either exact Target label. AP `D_p` rejects Target.
Handoff keeps complete `(Target, original member)` pairs, including a
ZERO original. Ordinary NORMAL ND and backward-ZERO **AP** selection
remain. NormalTarget never becomes guidance through those exceptions.

The package has no withdrawn NORMAL-to-DEMAND promotion policy and no
withdrawn NormalTarget source-permission workaround.

## Proof map

| Module | Main checked obligation |
|---|---|
| [SelectedCore](SelectedCore.lean) | Typed control C2/C5, raw NORMAL publication, paired handoff, source scope, continuation, and root report extraction |
| [ConstantBoundary](ConstantBoundary.lean) | Whole-packet rejection, no ND weakening, no rejected callback, constant-free store closure, and preservation of routes whose intermediate packets are in the selected domain |
| [TargetZeroRegistry](TargetZeroRegistry.lean) | Stable exact sink-key interning, distinct keys, and executable ID witnesses |
| [InitialEmissionExact](InitialEmissionExact.lean) | Directed ANY/EXACT correction at every path; existing EXACT/MUST/other-cell, mark and budget guards remain |
| [UnansweredDemand](UnansweredDemand.lean) | One rejected offer or an all-rejected batch changes no post-replay state or observation; no automatic Target or ZERO |
| [TargetZeroND](TargetZeroND.lean) | Finite all-NORMAL support, complete binary origin union, and independent seed memberships |
| [SelectedTargetApplication](SelectedTargetApplication.lean) | Complete admitted NORMAL-only forward application, exact ID preservation, native-demotion rejection, anonymous DEMAND, and backward ignore |
| [TargetJoin](TargetJoin.lean) | Arbitrary-arity complete bucket products, exact call/slot keys, full origins, selected result generation, and executable complete-tuple witnesses |
| [OwnedDelta](OwnedDelta.lean) | Full owned-key retained/seen suppression equals logical set extension; pending work and independent seeds remain |
| [TerminalProtocol](TerminalProtocol.lean) | Register, replay, start, publication and receipt invariants; failed sends keep required work; successful flush publishes every seen row |
| [ZeroSettlement](ZeroSettlement.lean) | Constructive finite settlement of every exposed ZERO row and atomic completed record/report snapshots |
| [ProducerDomain](ProducerDomain.lean) | Held REACH/TAINT plus K6 excludes FLOW premise members; actual reverse GEN has the same law; run-1 static layer and original descriptors remain |

Important general results include:

```text
OwnedDelta.full_relation_membership_after_offer
OwnedDelta.batch_preserves_relation
OwnedDelta.pending_never_erased_by_offer
TerminalProtocol.successful_flush_publishes_every_seen
TerminalProtocol.missing_receipt_prevents_completion
TargetJoin.product_member_iff_complete
TargetJoin.full_origin_zero_iff_every_origin_zero
TargetJoin.every_complete_permitted_match_is_emitted
ZeroSettlement.committed_zero_invariant
```

`TargetJoin` proves the product/join boundary for arbitrary finite arity.
An executable witness contains the complete tuple, its arity, every
call/slot key, and the selected result. The three-slot control keeps the
nonzero middle origin even when the last origin is ZERO. Empty slots,
cross-call bindings, and wrong arity cannot produce a terminal. The
existing `arityAllowed` policy controls zero-arity behavior.

`ZeroSettlement` does not assume that a new nonroot ZERO row is already
reported. `processReceipts` executes exact owned-key admission. Completed
receipts and required publication establish parent-row closure. `settle`
then follows a finite `FirstAdmissionRoute` to a configured root or an
old settled row. It returns the actual stop witness and report membership.
`committed_zero_invariant` covers all exposed ZERO rows. The concrete
`0 -> 1 -> root 2` control evaluates a `configuredRoot 2` witness.

`TerminalProtocol` does not equate seen keys with delivered work. Its
invariant keeps each required delivery pending or received. A failed
send retains the obligation. Missing receipts prevent completion.
Only a complete barrier exposes a new record/report snapshot.

## Runtime adapter obligations and scope

1. Map full method/premise keys, original caller support, AP geometry,
   fields, marks, exclusions, type/protection masks, and native MUST
   classification to the model inputs. The package does not verify
   Kotlin AP matching geometry.
2. Apply the corrected full C2 query before current starts. Protocol
   subscriptions cover admitted/prepared calls. No new subscription is
   promised for an offer that has no current demand. Saved replay stays
   before this admission gate.
3. Map Kotlin locks, immutable messages, required sends, and actor
   completion to the protocol transitions. Cancellation or a failed send
   must not erase pending work. An incomplete run cannot commit a new
   snapshot.
4. Obtain each ZERO admission route from a configured root or an earlier
   actual NORMAL-ZERO caller with a prepared subscription and complete
   NORMAL support. Detached/imported rows have no such witness. No
   runtime grounding label or field-transfer change is proposed.
5. Process every relevant received terminal and flush every owned
   publication before completion. Lean evaluation does not prove JVM
   scheduling fairness or production fixed-point detection.
6. Place constant-domain checks before all callbacks, packed paths and
   storage. Keep literal IR effects and STATIC fields. Preserve actual
   source-action permissions and producer kind checks.
7. Preserve configured sink/rule identity, catalog lifetime, and atomic
   retained-record/report snapshots. Keep source/sink seed occurrence
   membership separate from anonymous Target deduplication.
8. Populate general join buckets from complete existing same-call,
   same-slot matches with full original support. The model does not
   verify Kotlin `KaryJoin` internals or permit removing a missing slot.
9. Keep the selected run-1 static known-input/pool-interest route. Carry
   its selected STATIC original into terminal matching. Do not replace
   it with ZERO or introduce an abstract FLOW Target branch.

This is a constructive protocol and boundary proof package. It does not
prove whole-Kotlin refinement, unchanged findings for constant-bearing
derivations, whole-project no-FN, convergence, complexity, or measured
speedup. Runtime adapter tests and the selected project campaign remain
implementation obligations.
