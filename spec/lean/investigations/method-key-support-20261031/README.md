# Constructive later-run method support kernel

This package abstracts the support-preserving boundaries of production
`e090118e5f9603f1973c0578a3e04998035f4508`. It adds no runtime implementation.

`MethodSupport.lean` contains **43 explicit theorems**. Its adapter assumptions
are listed at the top of the source: run >=3, immutable incoming explicit
snapshot, no virtual static completion/carry, all nonzero starts from local C2,
all ordinary publications from paired local C5, backward ZERO as the sole
bypass, and same-owner projection/normalization. C2/C5 payload checks remain
abstract predicates. This proves the support consequences of those boundaries;
it does not verify Kotlin callback integration or AP semantics.

The main results are:

- `analysed_subset_incoming`: every nonzero-initial method has an incoming row.
- `forward_outgoing_subset_incoming`: every forward outgoing method has an
  incoming row.
- `new_backward_publication_is_zero`: every backward publication owned by a
  method absent from incoming support has a ZERO premise.
- `new_backward_outgoing_has_zero_witness` and
  `new_backward_outgoing_is_zero_only`: a new outgoing owner has a selected
  ZERO witness and cannot have a nonzero C2 initial.
- `projection_preserves_owner` and `dedup_support_iff`: handoff/dedup do not
  manufacture method owners.
- `stored_support_arbitrarily_grows`: a sink-seeded identity-binding call chain
  can create arbitrarily large new outgoing support from one unrelated incoming
  owner, after exact row dedup. Every generated summary is NORMAL/ZERO, and the
  implicit ZERO→ZERO rows are suppressed.
- `unseeded_chain_no_explicit_rows`: traversing the same ZERO chain without a
  sink seed creates no explicit outgoing demand.

The chain's terminal packet contains the sink requirement. Each surrounding
method returns it through a balanced ZERO call, with an identity argument
binding. It is a finite protocol instance. It does not establish that the
particular Java sketch in the investigation report was executed by production, nor does it
prove global iteration preservation, termination or whole-program narrowing.

Validation used Lean **4.33.1**, with a **2 GB / 60 second** cap per command.
The clean receipt is `kernel-validation.json`; stdout is in `kernel-audit.log`.
All **337 owned declarations**, including **135 theorem declarations counting
generated helpers**, were transitively audited. There are **zero unexpected
axioms**. The axiom union is exactly `propext` and `Quot.sound`; there is no
`Classical.choice`, custom axiom, `sorry`, or `noncomputable` declaration.

Executable controls passed for chain lengths **2, 10 and 1,000**. In each case,
incoming support is 1, nonzero-initial support is 0, seeded outgoing support is
2/10/1,000, and unseeded outgoing support is 0. Six separate exact controls also
passed. Audit peak child RSS was **1,559,572 KiB**. The initial 1 GB cap was too
small for Lean's audit/evaluation compiler; the final receipt records only the
successful bounded recipe.

To reproduce from this directory with the installed elan toolchain:

```sh
timeout 60s lean +leanprover/lean4:v4.33.1 -M2048 -o MethodSupport.olean MethodSupport.lean
LEAN_PATH=. timeout 60s lean +leanprover/lean4:v4.33.1 -M2048 Audit.lean
```

`validate_kernel.py` reproduces the same recipe using the exact installed
4.33.1 binary and writes source hashes, command output, timing and RSS into the
receipt. No Lake project build, Gradle command, analyzer execution, or project
rerun was performed.

For real-project evidence, root's separately parsed closed DEBUG frontiers are
in the [investigation data](../../../../docs/reports/data/bidirectional-backward-demand-delivery-investigation-20261031.json).
The checked source-derived support laws pass in every available local-only
transition. Stirling run-6's 252 added outgoing names are exactly its 252
ZERO-only outgoing names. This external kernel explains the mechanism and
checks the conditional support laws; it does not assign individual real-project
rows to specific seeds, AP demotions or record applications.

Package files: `MethodSupport.lean`, `Audit.lean`, `README.md`,
`validate_kernel.py`, `kernel-validation.json`, `lean-version.log`,
`kernel-compile.log`, and `kernel-audit.log`. Other external scratch/probe files are not part of this package.
