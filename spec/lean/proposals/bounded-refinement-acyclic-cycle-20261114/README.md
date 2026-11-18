# Uncapped intrinsic-MAY counterexample

[Code, annotated runs and proof](../../../../docs/reports/bidirectional-bounded-refinement-acyclic-nontermination-20261114.md).
Counterexample to global termination under non-empty MAY plus bounded
refinement, including the latest no-artificial-E local routing proposal.
Production remains unchanged.

`IntrinsicMay.lean` imports `LocalRouting` and models one analyzable,
straight-line root. Its allowed `CopyMark` pass rule has an `AnyField`
target and an exact input. The rule always produces MAY/DEMAND; its reverse
also stays DEMAND. Neither the forbidden AnyField pass-input shape nor a
predefined method summary is used.

The model constructs both runs, exact source matches, source-permission
renewal, typed ZERO/Target admission and paired C5. The invariant is:

```text
for every r>=1: outgoingDemand(run-r) = {ZERO -> DemandTarget, DEMAND}
```

The source permission is recomputed, not assumed. There is no iteration
limit, archived demand, DATA MAY/NE initial or field cut. The forward source
is already NORMAL and exact. The only marked producer of the sink argument
is the uncertain pass; no future NORMAL witness is silently excluded.

```sh
python3 spec/lean/proposals/bounded-refinement-acyclic-cycle-20261114/check.py \
  --out /tmp/bounded-refinement-acyclic-cycle-proof
```

The checker first verifies the 12 proposal/reference modules, then the
counterexample. It rejects proof holes, compiler warnings, custom axioms
and axiom dependencies other than `propext` and `Quot.sound`. Compiler logs
and source hashes go to the external output directory.

Checked: **13 modules, 220 audited declarations**, including 21 new cycle
claims and 199 imported proposal/reference claims. External receipt:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/bounded-refinement-acyclic-cycle-20261114/proofs-v3/receipt.json`.

Scope: constructive scalar AP action/control proofs and a closed uncapped
program trace. This is not a JVM implementation test. It refutes global
termination in the permitted rule language, not termination of every
ordinary field-only program or the already resolved two-call reference.
