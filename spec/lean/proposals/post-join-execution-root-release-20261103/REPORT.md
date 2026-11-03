# Lifecycle model validation report

Status: **UNSELECTED CONDITIONAL MODEL**. Reference runtime is
`050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

The [checker](check.py) compiles [PostJoinRelease.lean](PostJoinRelease.lean) using
Lean 4.33.1, one worker and a 768 MiB compiler limit, then audits every explicit
public definition/theorem: 35 theorems and 48 declarations. The [receipt](checks.json), [axiom audit](audit.txt)
and [source pins](reference-source-pins.json) record the final checked scope.

The central equality compares complete immutable outputs and final publication
after a successful join, completed snapshots, J-only binding and final cleanup.
Retained read projections and snapshots stay equal, including raw IDs, owners,
ports and marks. Live work/local publication/delivery is closed after join;
early release before snapshot capture is denied; failure cannot publish a new
handoff. Final release and early detachment are idempotent.

These are interface/lifecycle laws. Actual Kotlin read closure, thread/event
quiescence, canonical reference identity and native adapters remain unproved.
The model explicitly demonstrates that retained aliases can keep data reachable,
and that a binder reading execution data can invalidate release equivalence.
No collector reachability, freed bytes, retained-memory saving or speedup follows.
No runtime or native implementation is selected or changed.
