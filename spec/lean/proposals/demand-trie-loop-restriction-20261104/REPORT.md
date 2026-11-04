# Demand-trie proposal proof report

Status: **PROPOSAL MODEL ONLY — no Kotlin implementation**.

This package selects no major semantic change. It models geometric candidate
preparation and a restricted C2 image certificate. Native AP transfer, sources,
layers, marks, protection, aliases, complete ND execution, Target handling,
physical routes and first accepted prefix selection remain native obligations.

## Proved geometry

The reused `Geometry.lean` node walk follows every matching branch of the
compatible demand directory and retains the first raw field after that walk
stops. The new independently executable `maxLcp` reference scans all demanded
paths. Lean proves their path and length equality for arbitrary finite lists.
Every demand's `raw.take(LCP(raw,d)+1)` is a prefix of the retained path, so
sibling distinctions survive. Requested path prefixes are identities and the
projection is idempotent. Retained depth is at most deepest demand depth plus
one. No arbitrary global cap is claimed to preserve a deeper distinction.
`boundaryWitness` constructs a demanded path attaining the maximum LCP with
this raw path and proves that it shares that entire raw prefix. It does not
select by global terminal depth.

Terminal payload selection is independent of traversal precision. The ordered
payload list at a shorter terminal is not erased by a longer terminal, and the
longer terminal retains its own payload. The nested and sibling examples are
kernel-reduced concrete witnesses. Additional witnesses reject keeping only
the deepest matching terminal and keeping one globally longest demand path.

`children` is an executable prefix-list representation, not an efficient
production child map. These proofs do not establish a production trie's
construction cost or an O(h) runtime bound for this list implementation.

## Proved conditional C2 image preservation

`StrictCutCertificate` requires an actual strict prefix, the first new field
for each demand that prefixes raw, and continued incomparability for every
other demand. These are geometric predicates, not assumed output equality.
The finite `certificateCheck` checks all these predicates and constructively
produces the certificate. Under it, the modeled scalar C2 image is identical
for every demanded path and both EXACT/ANY demand tails, including emitted
initial tails and layers. The ordered per-row image is preserved as a whole.
Base, concrete mark and the carried protection bit are retained separately.

Both requested examples pass this certificate. There is deliberately no
general theorem here that every geometric trie projection passes the complete
certificate. The universally proved distinguishing-field property is separate
from that connection. Native code must validate the applicable certificate or
retain the current full native query. Scope/mark selection completeness is
also a prerequisite, not a theorem about the Kotlin indexes.

The native adapter must include the pre-admission guards before constructing
its precision forest. `MethodBlockRuntime.initials` invokes
`keepLocalConclusion(scope.block, scope.entry, actual, count=false)` before
the `DemandStore` query. For a rejected dead-local scope, a stored ANY entry
cannot witness a new candidate C2 key: the runtime never makes that query.
Raw-baseline key absence alone is therefore insufficient. Apply the same
existing guard per exact `(scope, base)` and include only accepted scoped
rows. The cuts preserve base, so guard stability can be checked at that
ownership boundary; do not infer it for an unknown wrapper or guard view.
Unknown views cannot issue a certificate and retain native fallback. The
pinned `MethodBlockRuntime.kt` and `BlockBoundaryDemandView.kt` are context
for this adapter obligation, not a native guard-equivalence proof.

The model assumes matching concrete FULL base/mark rows, valid bounded inputs,
empty E, and exclusively counted nonstatic fields. It omits FLOW, STAR/MUST
actuals, mark-group expansion, mx, arrays with uncounted prefixes, static
anchors, ZERO/Reach/Target, root metadata, packed forests, real complete ND
originals and actual AP interners. It neither proves Kotlin
`RestrictedInitialPolicy` correspondence nor copies its native source as an
axiom. Source pins are review context only.

## Preservation is not minimality

For raw `f.g/ANY`, demand `f.g/ANY`, the trie keeps the whole `f.g` path. A
shorter `f/ANY` has the same modeled C2 image, namely `f.g/ANY` at DEMAND.
`may_geometry_is_not_always_minimal` checks this counterexample. No universal
first-cut/minimality result is claimed, especially for raw MAY.

The local `any_demand_may_ancestor_constant` theorem proves that an ANY demand
emits the same `(demand path, MAY, DEMAND)` key from every MAY ancestor,
including equality. `shared_prefix_constant_any_range` proves this for all
budgets `b ≤ m` that shorten raw, when `raw.take(m)` prefixes the demand. The
corresponding family theorem proves this witness belongs to each candidate's
complete modeled C2 family.

`absent_witness_rejects_range` proves that this witness's absence from the raw
baseline, plus its presence throughout an earlier range, certifies rejection
of the whole range when acceptance allows no new C2-family key.
`skip_only_certified_rejected_prefix` and `skip_absent_witness_range` prove that
omitting such an earlier ordered prefix preserves the first accepted budget.
The raw MAY counterexample has the constant witness already in its baseline,
so that absence certificate cannot apply. There is no global raw EXACT/STAR
minimality claim. Native label/scope/mark identity and correspondence remain
adapter obligations. General cases keep the original ascending search and
first accepting choice. C2 preservation alone does not establish the full
adjacent/enclosing/repeat/labelled LoopObservation equality: AL and Target
consumers still require candidate checking and native fallback.

No Kotlin change, analyzer/build/profile run, full-observation equality,
convergence, report coverage, timeout equivalence, memory saving or speedup
is part of this package. Imported old geometric coverage does not imply C2
preservation; the new image theorem has its explicit geometric certificate.
