# Checked models: identity storage, owner visibility and protection admission

Status: checked models with runtime adapter tests. The selected runtime
implementation is in `LiteralInitialImage.kt`, `MethodEdges.kt`,
`FrozenOwnerVisibility.kt`, `StaticGuidance.kt` and `Groups.kt`.
Base analyzer: `c98d12582a138d5898e94908ee6690dda73998ca`.

Read the [implementation proposal](../../../../docs/design/bidirectional-identity-owner-protection-implementation-20261030.md)
for the runtime adapters, code snippets, unchanged contracts and tests.
Use [checks.json](checks.json) for source hashes and the proof receipt.
The checker binds current runtime source bytes. It does not verify Kotlin.
Differential tests compare literal admission and protection with the previous
scalar groups. Independent BFS tests check the SCC and packed-word adapter.

From the repository root:

```sh
python3 spec/lean/proposals/identity-owner-protection-20261030/check.py
```

Use `leanprover/lean4:v4.33.1`. The checker builds only these models and their
one existing dependency. It uses one CPU, one Lean worker, a 768 MiB Lean
limit and a 90-second timeout per command. Generated files and logs stay under
the ignored `spec/lean/.lake/verification` directory. It runs no analyzer,
Kotlin compilation or project campaign.

| Source | Named theorems | Audited public definitions/theorems |
|---|---:|---:|
| Existing CachedCfgDelivery dependency | 12 | 29 |
| [IdentityCells.lean](IdentityCells.lean) | 14 | 30 |
| [OwnerVisibility.lean](OwnerVisibility.lean) | 14 | 38 |
| [ProtectionAdmission.lean](ProtectionAdmission.lean) | 18 | 27 |
| Total | 58 | 124 |

There are 46 new named theorems. Anonymous examples and executable guards are
additional controls. The only audited axiom dependencies are `propext` and
`Quot.sound`. The checker rejects proof holes, custom axioms, noncomputable
source and `Classical.choice` dependencies. It audits public definitions as
well as theorems and checks source stability during the run.

## Identity storage

The model separates ABSENT, PRESENT and PROTECTED. Its reference stores the
ordinary and protected membership bits for one complete coordinate. It proves
equality of state and emitted delta, including the first plain result, exact
duplicates and protection-only upgrades. Layers and producing keys remain
separate. Event-list induction proves equality of every returned delta.

Promotion restores the exact current identity snapshot, then calls the same
supplied scalar group operation. The generic delegation theorem proves that
promotion does not re-emit restored values. A full point continues to use that
operation. This does not model an arbitrary AP tree as a single coordinate.

The runtime recognition adapter must validate the whole path, leaf kind,
singleton mark, complete header and mask. Unsupported cases use the scalar
fallback. Exact leaves use the canonical ANY_TAINT header without becoming
must leaves. Tests must bind this adapter to the production group algebra.

## Owner visibility

The model reuses the existing total finite search for original graph paths.
It has an executable partition/quotient certificate verifier. Each accepted
certificate carries internal paths and actual original edges. A false merge
of disconnected vertices is rejected by an executable control.

Path projection and lifting prove original/quotient correspondence. The DAG
reference recurses on a strictly smaller child rank. The dynamic table writes
each component once; its prefix theorem proves equality to the reference.
Soundness and completeness relate every family bit to an actual reachable
owner. `ownerWitness` extracts that owner, list membership and original path
by finite search. The outside-owner OR is preserved exactly.

The certificate verifier is a formal/reference control. It is not a proposed
expensive runtime validation pass. The package does not prove Kotlin's SCC
implementation or machine-word packing. The implementation must establish the
explicit component/rank certificate invariants and pass independent BFS tests.
It must keep exact LOCAL ownership and full-MethodKey W/R attachments. Two
methods in one SCC do not become the same local owner.

## Protection admission

The model uses finite exact coordinates, including path, EXACT/ANY leaf kind
and mark. It proves coordinate union inclusion, subtraction/delta inclusion,
invariance under coordinate-equivalent interning, and equality of old trimmed
construction and the certified constructor. Header canonicalization is the
same supplied function on both sides.

A negative control proves that protection valid for a merged root can be
invalid for an ordinary delta. Another distinguishes equal ordinary values
with different protection. These prevent a general unchecked constructor or
ordinary-equality duplicate guard from entering this selected change.

## Limits

This is a proof of the selected finite semantic kernels and an implementation
contract. It is not a proof of the full analyzer, JVM/AP adapter code, SCC
machine code, resource behavior or vulnerability completeness. The source
hashes bind the reviewed baseline and proposal. Runtime tests, adapter checks
and the authorized project measurements remain required before implementation
can be accepted. No field/mark/rule policy may change to satisfy this model.
