# Concrete DEMAND guidance: local models

This directory contains separate models with different scopes. The 58-lemma
model below is the historical MAY-only proposal. Its receipt records the
selection state when root checked it. Do not use that receipt as a proof of
the later all-header protection contract or of program recovery.

- `ConcreteGuidance.lean`: 58 checked local MAY laws and unchanged C2 cells.
- `AllProtectionRetention.lean`: 35 checked incremental H/MAY laws. DATA
  admission is a parameter; no global DATA normal form is assumed.
- `EmbedRawProtectionOrdered.lean`: 50 checked ordered-bag placement and
  H-retention laws. Native DAG and mutable-loop refinement remain explicit.
- `PassProtectionPolicy.lean`: 24 checked pass-classification and transport
  laws. A pass keeps existing protection and cannot introduce protection.
- `NormalStarFlowAdmissionGap.lean`: 12 checked current-policy countermodel
  lemmas. The receipt is `normal-star-gap-checks.json`. It does not select
  an admission change or prove termination.

The [current implementation draft](../../../../docs/design/bidirectional-concrete-demand-guidance-implementation-20261106.md)
states the selected behavior and the remaining native acceptance gates.

## Historical MAY-only model

This is an unselected proposal under `spec/lean/proposals/`. It does not change
production or the user's formal specification. The preparer did not run Lean or
this checker. Root then compiled the corrected model: all 58 lemmas pass, with
the executable witness and dependency audit in `checks.json`. The first root
attempt had one nested-record layout parse error, not a behavior counterexample.
The correction changes only line layout. `preparation.json` retains the original
source-preparation hashes; `checks.json` binds the corrected checked model.

The candidate restores only effective MAY coordinates: concrete TAINT,
DEMAND layer, ANY packet header, empty field exclusions, and an `any` leaf-mask
membership for one full mark. It restores explicit root and child positions
separately. A mixed packet's EXACT mask is not a MAY guide merely because its
packet header is ANY. The candidate keeps the current canonical data result's
EXACT coordinates unchanged. There is no blanket packet passthrough.

Each coordinate contains the complete opaque original identity, method, block,
entry port, exit port, typed header, path, full mark, leaf mask and support channel.
Ordinary and protected support are independent streams. Native payload is their
union; a protected membership does not create an ordinary origin, and ordinary
coverage does not create a protected bit. This is an abstract stream adapter,
not a claim that native `value.root` excludes its protected mask.

The `restore` algebra receives a current DATA state and already supplied input
coordinates. It adds only selected MAY coordinates. The general laws establish
exact-coordinate union/freshness, no delta for duplicates, no origin products,
and invariance of the complete old EXACT view in either channel. The finite
packet adapter checks a cold packet and both arrival orders, multiple full marks,
and protected support. It does not retain or require a producer history.

The cold-packet bridge is checked per Boolean full-mark slot. With original
EXACT bit E, original local MAY bit N and inherited MAY support A, the old exact
result `(E \ A) \ (N \ A)` equals the candidate `(E \ A) \ N`, namely
`E && !A && !N`. MAY changes from `N \ A` to N. The lemma is universal over the
three bits and is applied independently to ordinary and protected streams.
Both adapters must propagate ABOVE from the original local node, before
subtraction; that source-adapter requirement is explicit in the model.

For warm states, restoring an Empty-E MAY position under an equal-mark/channel
MAY ancestor leaves its DATA denotation unchanged. The finite checks cover three
ordinary/protected/mixed-mark packets, six paths, two full marks and both channels.
A separate universal slot lemma states that unchanged MAY support leaves
`exactBit && !maySupport` unchanged. These local checks do not prove all of native
`canonicalRegions`, E-hole filling or T4 mixed-header behavior. MUST/E processing
is outside the selected guide cohort and is not replaced by these definitions.

`currentCovers` is a narrow counterexample recognizer for the same-header,
FULL/DEMAND/ANY/Empty-E cell. Its root MAY/T covers the supplied child MAY/T, so
the current finite packet/arrival models drop the child. The candidate restores
it. The PZERO/root coordinate uses the captured producer shape: method identity1,
block3, entry-2, exit7; handoff reverses it to block3/entry7/exit-2. These numeric
identities are finite labels, not a new native identifier assignment. Root's
actual root capture establishes the root row. The paired child is a conditional
supplied-row witness here; this model does not prove the native first removing
transaction or that each producer actually offered that child.

The model imports the existing scalar C2 module without modification and uses
its selected budget adapter at limit2. For concrete full T and counted f/g:

| Guide | Actual | Existing admission |
| --- | --- | --- |
| s.ANY/T | s.f.g.EXACT/T NORMAL | s.f.STAR/T DEMAND |
| s.ANY/T | s.f.ANY/T DEMAND | s.f.STAR/T DEMAND |
| s.f.ANY/T | s.f.g.EXACT/T NORMAL | s.f.g.EXACT/T NORMAL |
| s.f.ANY/T | s.f.ANY/T DEMAND | s.f.ANY/T DEMAND |

The finite layer adapter is FULL-only, with legal empty-E scalar views. It does
not replace native C2 or introduce a first-field MUST emitter. Paired-image
checks retain the same complete original and reversed owner/ports; they cannot
borrow another scope, exit, or original. The adapter projects extra restored MAY
rows only. Existing EXACT-data handoff, C5 admission and ND member export remain
separate obligations. Protection is not added as a new demand-row field.

Field exclusion scope is explicit. An ANY packet with nonempty E is rejected,
not silently normalized. An EXACT leaf reads Empty E even inside another mixed
header. A STAR/must sibling may carry its own E; the model checks only its local
next-field exclusion predicate. It does not prove E intersection/weakening,
T4 mixed-header joins, static anchors or the general spatial canonicalizer.

One semantic cell stays open by design: same-head MAY/T and EXACT/T guides have
different C2 images on a MAY input. Restoring only MAY positions preserves the
old EXACT pruning and therefore does not repair that cell. The theorem
`same_head_MAY_EXACT_cell_is_not_repaired` records it. A requirement to preserve
every supplied guide's complete C2 image would need a further behavioral decision;
it cannot be claimed from this proposal's MAY-only lemmas.

No STAR, MUST, NORMAL, real FLOW, packed FLOW surrogate, GROUP mark, rule effect,
alias, call, manager-role or field-processing repair is selected. Negative FLOW
kind tests are guard tests on the abstract coordinate type, not native
FLOW/full-mark packet constructions. The old data state is a parameter to the
general restoration laws; the finite current recognizer is not a replacement
for those other native policies.

Root-only check from the repository root:

```bash
python3 spec/lean/proposals/concrete-demand-guidance-retention-20261106/check.py \
  --output spec/lean/proposals/concrete-demand-guidance-retention-20261106/checks.json
```

The checker compiles the unchanged scalar module and this model into a temporary
directory with a 2 GiB Lean bound. It requires one printed dependency audit per
theorem and the executable finite witness. It rejects incomplete proofs,
nonconstructive shortcuts and explicit new assumptions; only the existing
`propext`/`Quot.sound` foundations are permitted. Its receipt says local proposal
PASS only. It cannot establish native producer equivalence, shared-loop recovery,
all adapters, or full-project quality.

Native source anchors and preparation hashes are in `preparation.json`. The
existing FLOW proposal is the model reference; its selected behavior and checked
39 lemmas are not proof that this concrete proposal has been selected or checked.
