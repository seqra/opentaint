# Termination catalogue checks

The [report](../../../../docs/reports/bidirectional-termination-fix-validation-20261117.md)
states the witness scope and natural stop for each example. These checks
use the [specification](../../../demand-refinement-and-termination.md).
The intrinsic MAY pass fixture is excluded.

- [TerminalReplay](TerminalReplay.lean) checks the frozen root Target
  certificate with all required binding receipts. It keeps the provisional
  replies in the three saved-MUST fixtures. For the alternating fixture it
  checks all eight call routes from the actual retained run-3 state, then
  checks the within-run fixed points and the empty run-7 frontier.
- [BoundReplay](BoundReplay.lean) gives the complete three-call route
  traversal and a checker for each bound hop. The generated controls keep
  the transfer rules, paired guidance and saved-first application.
  They forward every applicable reply and use the same root certificate.
  They check the cold states, including each active run's fixed point, and
  prove inactivity after completion for the checked shapes.
- [Catalogue](Catalogue.lean) loads the previously checked termination proofs
  for the other entries. It also runs the shallow and deep exclusion cases
  with optional uniform value folding withheld.

The input directory has the comparative audit receipt and the
`GuardedTermination` receipt from the [prior audit](../demand-no-loss-audit-20261117/README.md).
The checker validates their source hashes, compiles in Lean 4.35.0 and
audits the transitive axioms of the added claims.

```sh
python3 spec/lean/proposals/termination-catalogue-verification-20261117/check.py \
  --audit /absolute/archive/termination-fix-validation-20261117 \
  --out /absolute/archive/termination-catalogue-verification-20261117/verified
```

The cold replays count a stop only after the complete forward frontier
is empty. The finite checking horizon is a test expectation. It does not
change the analysis transition or the stopping rule.
