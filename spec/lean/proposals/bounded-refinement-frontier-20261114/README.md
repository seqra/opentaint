# Bounded refinement frontier

[Approach](../../../../docs/design/bidirectional-bounded-demand-refinement-20261114.md).
Design reference; production unchanged. Existing global and paired relative
field cuts are preserved.

- `Frontier.lean`: complete one-level logical region covers, `2+2k` query bound,
  linear routing of an already matched cube, identical paired output
  permission, both original initial bounds, no MAY/NE premises,
  concrete guessed-point support and retained deeper refinement heads.
- `Pipeline.lean`: historical E-based trace; run-1 writer witness and a
  backward plan with four
  bounded EXACT/STAR queries; run-2 cut frontier; run-3 NORMAL reader
  derived without assuming it beforehand; unchanged real global cut;
  run-4 source permissions; normal run-5 replay and natural stopping.
  The BB variant includes the native weak reverse view of the forward
  MUST record and its extra run-4 demand. Longer reads retain the same
  one-field cut and use the existing uniform query without path unfolding.
- `Binding.lean`: uncertain STAR descent only for MAY/NE, retained precise
  selector rejection, marks/E/limits, DEMAND guessed points, no NORMAL
  Target confirmation and no application of unrelated current premises or
  owner/port frames.
- `Subsumption.lean`: parent MAY semantically covers a deeper NE but
  cannot supply its two-field initial under the parent's unchanged bound;
  same-head NE plan coverage; removal by an actual NORMAL service;
  transitive service coverage and arrival-independent captured heads.
- `Publication.lean`: compact caller-visible MAY/NE delivery while keeping
  both callee refinement rows; coarse MAY and STAR can still admit the
  child query; NORMAL refinements and distinct protection/mark memberships
  are retained. A final batch's visible basis is arrival-independent.
- `LocalRouting.lean`: current replacement for artificial field exclusions.
  Initial facts and keys retain ordinary E. Frozen local plan commands
  delegate only covered unknown-STAR MAY results to complete child queries.
  Every emitted result is unchanged from ordinary transfer; NORMAL outputs
  are forwarded. Checks include the STAR-only empty-case rejection, the
  full NORMAL g reader and its f descendant, the old promotion-ban middle
  branch, safe sharing of raw initials, and both run-5 natural-stop traces.

The imported selected references are unchanged. The older `Partition.lean`
provides logical region predicates; its old full-guard admission prototype
is not imported. Logical region exclusions and the old `projected` /
`oneFieldPlan` constructors are not the current AP fact encoding.
`LocalRouting` uses ordinary facts, not `E=G`. No full suffix evidence is
stored or composed.

```bash
python3 spec/lean/proposals/bounded-refinement-frontier-20261114/check.py \
  --out /tmp/bounded-refinement-frontier-proof
```

The checker rejects admitted/custom/classical axioms, audits all declarations,
and saves source hashes and compiler output outside the repository. The
permitted axiom dependencies are `propext` and `Quot.sound` only.

Checked: **12 modules, 199 audited declarations** (90 new, 109 imported).
External receipt:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/bounded-refinement-frontier-20261114/proofs-v11/receipt.json`.

These are AP concept proofs and a scoped executable trace. They are not a
proof of Kotlin correspondence, arbitrary alias/ND delegation services, or universal
termination for recursive programs. Native implementation and experiments
are separate work after selection of the semantic changes in the approach.
