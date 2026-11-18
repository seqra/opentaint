# Uniform-source exact-root cleaner: historical cycle and selected revision

The new decision preserves same-head MUST and its layer. The example is
therefore **withdrawn as a counterexample under the updated specification**:
it stops at run-1. Production still has the old rule measured below.
`RootCleanerPolicy.lean` checks the revision separately and exposes its
exact-root NORMAL false-positive consequence under the old concrete
cleaner meaning. The historical proof is retained, not rewritten as if
the old measurements had used the new rule.

[Code, rules, per-run annotations and proof](../../../../docs/reports/bidirectional-uniform-root-cleaner-nontermination-20261114.md).

No loops, recursion or pass rules. The only analyzed block contains an
ordinary whole-object source, a selected exact-root T cleaner, and an
ordinary whole-object T sink. No concrete field is cut. The retained
partial cleaner loses NORMAL support, and backward MAY propagation renews
the same source permission forever.

`RootCleanerCycle.lean` imports the complete preceding proposal, including
NORMAL uniform NE coverage. It proves all forward/backward handoffs contain
the same `ZERO -> DemandTarget`, including run-3/run-5 and arbitrarily later
rounds. It checks actual cleaner/mark/control cases, no-limit dependence,
permission renewal, and the absence of NormalTarget.

```sh
python3 spec/lean/proposals/uniform-root-cleaner-cycle-20261114/check.py \
  --out /tmp/uniform-root-cleaner-proof
```

Historical check: **PASS**, 18 modules, 312 audited declarations including
20 cycle claims. All earlier 292 declarations are rechecked first. Axiom
closure permits only `propext` and `Quot.sound`; no classical/custom axiom
or proof hole is accepted. Receipt:
`uniform-ne-counterexample-20261114/proofs-v2/receipt.json` in the external
report-data archive.

The updated checker adds **9 policy claims**, for **321 declarations in
19 modules**. Receipt:
`uniform-ne-counterexample-20261114/must-preserving-policy-v1/receipt.json`.
It proves NORMAL stays NORMAL, DEMAND stays DEMAND, non-MUST rows are
unchanged, the whole-object example has no outgoing demand at run-1, and
an exact-root sink can now report normally despite actual root cleaning.

Native reproduction reaches **run-21**, stopping at its explicit test
ceiling. Five new tests and five prior selected-cleaner tests pass. The
native core has no NE implementation; no new-tail operation applies to
this example, and the full proposed model supplies the uncapped proof.
Production code and selected semantics are unchanged.
