# Acyclic non-empty-MAY counterexample

The [report](../../../../docs/reports/bidirectional-non-empty-may-acyclic-nontermination-20261113.md)
contains the program, rule configuration, run-1/run-2 bootstrap, per-run
annotations and the unbounded induction. This adds no production behavior
to [the selected spec](../../../non-empty-may.md).

`Cycle.lean` imports the actual `Policy` and `Restriction` reference modules.
It constructs the first call's partial query, applies its loss summary to
the actual source and uses that result to admit the second call. It checks
the reverse chain too. No repeating boundary packet is an independent
assumption. Generic positive field limits include the increasing schedule.

Twenty-one declarations in `Cycle.lean` are audited. The induction describes retained
cycle witnesses; the report supplies their control/compaction embedding.
It is not a complete IR, scheduler or production implementation proof.
Additional NORMAL records are allowed, rather than erased between rounds.
Aliases are disabled for this counterexample. No statics, ND or cleaner
semantics is involved. The tail domain and its selected rules are unchanged.

```sh
python3 spec/lean/proposals/non-empty-may-acyclic-cycle-20261113/check.py \
    --out /tmp/non-empty-may-acyclic-cycle-check
```

The [BB retrace](../../../../docs/reports/bidirectional-non-empty-may-basic-block-retrace-20261113.md)
adds `BbTrace.lean` with 25 declarations. BB-local refinement reaches a
NORMAL read relation at run-4. The witness then tracks method C5 producing
an actual NE input that restarts a STAR query and saved opposite read.
The later method-demand recurrence is checked at arbitrary growing limits.
No extra loop gate or new subsumption is assumed.

The checker compiles the four reference modules and both witness modules in
a fresh external directory. It records source/object hashes and audits
axioms. No iteration cap occurs in the model or its proof. Compiled data
and receipts stay outside the repository.
The combined check passes 125 audited declarations. The original 100-check
receipt remains `proofs-v1/receipt.json`; the BB extension's successful
receipt is `bb-proofs-v2/receipt.json` in the external case directory.
