# Handoff MAY-exclusion counterexample

The [investigation](../../../../docs/reports/bidirectional-handoff-may-exclusion-20261113.md)
traces the clarified candidate: exclude f from the broad MAY demand while
retaining the child f.NE demand. Its exact f point is uncovered. The
loop-free program derives both same-premise rows and needs that point.

`Exclusion.lean` imports the selected non-empty-MAY C2/C5 and the acyclic
prefix-transfer model. The new candidate is modeled only on the reached
strict-descendant exclusion cell; it is not a complete new C2 policy.
No canonical spec or production behavior is changed.

```sh
python3 spec/lean/proposals/handoff-may-exclusion-20261113/check.py \
    --out /tmp/handoff-may-exclusion-check
```

The checker compiles dependencies in a fresh external directory and audits
19 new declarations plus 100 reference/cycle declarations. It rejects
custom axioms, classical choice and unfinished proofs. Source hashes, Lean
logs, objects and receipt stay outside the repository.

The complete-driver code/Target embedding is a mathematical trace in the
report; it is not claimed as a mechanized JVM/driver execution. The core
finding is constructive: the exact `ret.f` offer has no admitted query after
the rewrite, and the old query has a specific NORMAL read-provider witness.

The [NORMAL-only investigation](../../../../docs/reports/bidirectional-handoff-normal-summary-exclusions-20261113.md)
adds `NormalOnly.lean` and 12 checks. A one-field write supplies a genuine
NORMAL child. Saved reverse replay returns the input root point, while
the real source lies under g and requires the other branch's reader.
NORMAL alone is not a complete field-coverage certificate.
Run this extension with `check.py --normal-only --out <fresh external dir>`.
It passes 131 declarations across seven modules; its successful receipt is
`normal-proofs-v2/receipt.json` in the external case directory.

The [STAR-only refinement](../../../../docs/reports/bidirectional-handoff-star-only-exclusions-20261113.md)
adds `StarOnly.lean` with 27 checks. Concrete-field commands, EXACT probes
and MUST starts remain unmasked. This fixes the preceding exact-input
counterexample. A wrapper can instead supply only a same-head STAR command;
the masked NORMAL reader misses the real sink when its path is representable
at run-3. The run-4 exact-offer check is a separate probe, not an assumed seed.
The model grants the candidate a consistent updated raw-image C5 check.
Run `check.py --star-only --out <fresh external dir>` to include this case.
The combined result is 158 declarations in eight modules; the receipt is
`star-only-proofs-v3/receipt.json` in the external case directory.

The latest clarification is a [separate promotion ban](../../../../docs/reports/bidirectional-handoff-promotion-ban-20261113.md),
not a semantic E exclusion. `PromotionBan.lean` preserves C2 keys and E
and omits only the banned unknown-STAR-read result. It repairs the old
clipped reader. Its 34 additional checks show a different-branch coverage
gap when a NORMAL writer is used to ban all reads of that field. Both the
root and child MAY demands are retained in the updated checks: the child
recovers the reader from a MAY offer, but C2 rejects an ancestor STAR offer.
Run `check.py --promotion-ban --out <fresh external dir>` to include it.
The combined result is 192 declarations in nine modules; the successful
receipt is `promotion-ban-proofs-v3/receipt.json` in the external case directory.
