# Complete NORMAL service for one current return reply

Constructive Lean 4.35.0. Production is unchanged.
[Selected contract, examples and costs](../../../../docs/design/bidirectional-reply-scoped-point-service-20261116.md).
[Complete updated trace](../../../../docs/reports/bidirectional-reply-scoped-point-service-trace-20261116.md).

- `ReplyCore`: conservative overlap cannot miss a common concrete location;
  full internal closure with a selected terminal predicate; whole native
  service/receipt witnesses; arbitrary relevant continuation observations.
- `ReplyBody`: same six-rule h-read program and unchanged C2/C5/transfers;
  current-owner NORMAL-closed status and on-demand reply-specific selection.
  No per-region or negative cache. Queries and body facts are not altered.
- `ReplyCold`: complete cold states, per-run within-run fixed points,
  natural run-5 stop, NORMAL observation, uncapped quiet suffix from run-6.
- `ReplyOldExact`, `ReplyOldMark` and their `Cold` modules: rerun the old
  four-rule exact-input and six-rule V-return cases with the same coordinator.
- `ReplyProof`: full leaf closure, actual native receipts, same-mark h/k
  distinction, root/k rejection, missing relevant service, ancestor MUST,
  E/NE controls, vacuous terminal region with mandatory closure, H/N guards.
- `ReplyRegression`: generic old-guard bridge and packet identity; all 18 old
  ordinary references and older hole/alternating guard checks retained;
  FLOW/MUST/DEMAND actuals ineligible. Erasing coordinator-only metadata gives
  identical old exact/V semantic cold states, including findings and stops.
- `ReplyBounds`: existing-query keys only; complete uncut NORMAL boundary
  state; selected replies are a subset; unchanged C2/C5 budgets; no k archive,
  no falsely granted whole/mark flag; accumulating Target controls.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/reply-scoped-point-service-20261116/check.py \
  --out /tmp/reply-scoped-proofs
```

Optional `--dependencies` reuses a completed
`unadmitted-field-cycle-20261116/check.py` output after verifying every
source hash. The checker source-compares unchanged program/admission/transfer/
C5/completion/persistence/control functions, builds these ten modules and
independently audits their 152 claims. **5,918 cumulative claims in 303 modules**.
Only `propext` and `Quot.sound` are allowed. No custom axioms, holes,
classical choice or native evaluator are used.

All 46 selected native tests pass, including eight new reply-specific
controls. The unchanged full-program diagnostic reaches **run-31/POLICY**,
with zero NORMAL reports; the proposal reference retains its NORMAL
observation at run-5. These component tests do not install the complete
NE/completion proposal or establish full-engine/JVM/alias equivalence.
The largest retained old ordinary reference stops at run-15. No universal
termination or project-performance claim is made.

No new query, propagated summary/path, region table or cap exception is
introduced. Unsupported or incomplete closure/native coverage retains the
ordinary path. Full captures, test XML, compiled proofs and audit receipts
remain outside the repository.
