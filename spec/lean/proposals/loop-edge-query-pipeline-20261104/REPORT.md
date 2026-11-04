# Finite output-row batching proof report

Status: **PROPOSAL MODEL ONLY — no Kotlin implementation**.

No major semantic change is selected by this package. It proves a structural
factorization relative to the **same** opaque native cell selector, complete
paired-row entry predicate, row pack/cut and final ordered union. It does not
introduce field transfer, source authority, ZERO/Target, ND join, mark grouping,
static guidance or alias policy. No runtime, build, analyzer or profiling work
is part of this proof package.

## Kernel-checked claims

- Candidate pruning is exact when every omitted `(whole row, scalar)` cell
  has native selection `none`. No converse is required.
- Scalar-column assembly preserves each row's exact input-order `filterMap`.
  Row buckets are positional; no equality quotient merges payloads or ordinals.
- Entry-mask filtering removes only entire rejected paired rows and preserves
  row order. An accepted entry from one row cannot supply another row's exit.
- The unchanged opaque `packCut` receives the same row and complete ordered
  list of selected parts, exactly once. Hence complete result lists and any
  identical downstream ordered union are equal.
- Plan postings are an ordered filtered sublist of owner postings. Their
  number `k` is at most owner count `N`, for one lookup and for a finite sequence
  of scalar lookups. All-eligible rows give no posting reduction; a concrete
  mixed-entry example gives a strict reduction.

The posting bound uses the same whole-row/member-ordinal occurrence universe
on both sides. If a native method index stores raw IDs once but a plan expands
one ID into several ND member ordinals, its raw-ID count is a different
denominator. The model does not bound plan ordinals by distinct method IDs.

The proof uses only `Std`. There are no unchecked proof placeholders,
classical choice, extra asserted algebraic laws or AP distributivity axioms.
The source scanner and transitive axiom audit enforce this in `check.py`.

## Constructive regression witnesses

`distinct_nd_ordinals_retained` retains ordinals 7 and 8 with equal payload 4.
`scalar_input_order_retained` maps `[3,4,5]` to `[3,5]` in that order.
`pack_cut_need_not_distribute` shows a whole-bucket length cut differs from
cutting singleton buckets and concatenating them. `rejected_row_does_not_pack_empty`
uses a pack function that emits 99 even on empty input, proving why entry
rejection must omit the row rather than merely empty its bucket.
`dropping_live_candidate_changes_answer` is a finite witness against a lookup
that omits a selected cell. The posting controls cover both no saving and a
strict practical saving.

## Native adapter obligations, not proved here

1. Show that actual `EntryRestrictionTicket.restrict(raw)` is represented by
   the modeled native `select` plus the modeled single complete-row `packCut`.
   This includes all AP base/path/tail/exclusions, FLOW mx, layers, full
   protection and normalization. The model does not assume an arbitrary native
   conclusion equivalence or that native restriction distributes over leaves.
2. Prove the plan output index enumerates exactly an eligible sublist or a
   conservative superset filtered by the same final native predicates. It must
   cover every actual scalar path neighborhood, preserve complete paired rows,
   ND member ordinals, scope, physical exit, policy and frozen-view identity.
3. Prove a sparse posting implementation realizes the reference buckets with
   the same scalar order and one bucket per exact plan ordinal. Duplicate
   physical postings require deduplication by exact row/scalar cell; separate
   ND ordinals must survive. Native AP callbacks retain their ordinary order.
4. Apply the identical complete-row packing, transport and demand-specific
   `min(global FL, exit FL+1)` cut **after** complete row selection. Preserve
   the existing ordered result union and full annotated equality.
5. Retain native handling for unsupported/static/control/ZERO/Target cases.
   Prove cancellation, owner-quantum cleanup, capacity fallbacks and actual
   source/mark-request effects separately. Immutable observer work must not
   replace mutable current input/publication joins or complete ND execution.

No complete loop-observation equality, prefix-choice theorem, whole-driver
convergence, native index completeness, resource-limit outcome, memory saving,
project coverage or speedup is established by this package. Dense reference
transpose cost is not presented as the sparse index's complexity. The posting
bound alone omits native AP and output-sensitive work and cannot establish a
whole-project improvement. Current source pins are context, not a Kotlin proof.
