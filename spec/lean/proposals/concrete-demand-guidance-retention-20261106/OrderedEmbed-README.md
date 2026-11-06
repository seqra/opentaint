# Ordered raw-protection embedding model

This is a new, separate model of `SpatialCanonical.kt::embedRawProtection`.
The preparer has not run Lean or this checker. Existing models and receipts
are unchanged. `ordered-embed-preparation.json` pins the prepared source and
the actual Kotlin function body. Root alone runs the command below.

Root checked the corrected model: all 50 lemmas and the executable witness
pass. [ordered-embed-checks.json](ordered-embed-checks.json) binds the exact
model, checker and native-function hashes. Only propext and Quot.sound occur
in the dependency audit. The original attempt had four tactic failures;
`ordered-embed-correction-1.json` records proof-body corrections with unchanged
definitions and theorem statements. The rejected source was archived before
correction. Model PASS does not close the native gaps listed below.

The model takes arbitrary ordered DATA rows. It does not call, assume a
normal form for, or change DATA normalization. One invocation fixes native
owner, full P, base and layer. An unbounded Nat coordinate is an opaque
complete `(path, full mark)` identity within that fixed context. It is not
a numeric runtime AP ID. Header has ANY/Empty, MUST/E and STAR/E forms; E is
an opaque canonical identity, with 0=Empty. EXACT keys ignore their wrapper.

The executable ordered-bag algorithm includes:

1. Collect the literal protected EXACT inventory, deduplicated by coordinate.
2. Scan DATA in order and remove only repeated protected EXACT payload slots.
3. Keep raw span flags under each supplied tail/E, omitting empty span writes.
4. Place EXACT flags at the first matching remaining DATA coordinate.
5. Otherwise choose the first original source with that flag and an existing
   cohort after DATA and span writes; otherwise use exact-only fallback.
6. Coalesce writes by complete header while keeping first-header order.
   Payload includes each flag carrier before the final mask-clipping view.

The model defers exact flag writes after recording their selected DATA/original
header. This makes their allocation count explicit. The actual Kotlin writes
them during its scans. Native refinement of those presentations is an adapter
obligation; the model does not hide that gap in a DATA confluence assumption.

Universal laws range over unbounded finite ordered lists, coordinate identities
and E identities. They prove literal protected EXACT/span inventory, no
invented flags, payload inclusion, harmless modeled mask clipping, effective
EXACT wrapper independence, first DATA/source/fallback priority, exact flag
allocation at most once, and coalescing membership/count preservation.
The executable example contains two DATA cohorts, a repeated exact DATA slot,
three protected sources, raw span flags, original-cohort restoration and fallback.

Scope limits stay explicit:

* Native DATA exact-only packets use the canonical exact-only wrapper. The
  model's `dataHeader` uses that invariant. Kotlin's generic add helper also
  handles a noncanonical exact-only input when its old cohort has spans;
  that broader malformed/noncanonical adapter case is not proved here.
* Nat coordinates do not model accessor-index DAG walks, field masks, mark-set
  implementation, interning, reference identity, cancellation or allocation.
* Ordered bag union is interpreted by membership. Native tree/map/leaf-set
  representation and the deferred-write refinement need native checks/proof.
* No theorem proves the old DATA admission law, packet serialization order,
  delta delivery, call/ND/source effects, C2/C5 completeness, convergence,
  program recovery or project quality.

The model contains no classical choice, new axioms or proof placeholders.
The checker permits only `propext`/`Quot.sound`, prints a dependency audit for
every theorem, verifies the executable witness and checks input stability.
It produces a new model-only receipt; it must not replace old proof receipts.

Root-only command from the repository root:

```bash
python3 spec/lean/proposals/concrete-demand-guidance-retention-20261106/check-ordered-embed.py \
  --root-owned-execution \
  --output spec/lean/proposals/concrete-demand-guidance-retention-20261106/ordered-embed-checks.json
```

Expected preparation state is PREPARED_NOT_LEAN_RUN. A later model PASS is
conditional local evidence and must retain the native gaps above.
