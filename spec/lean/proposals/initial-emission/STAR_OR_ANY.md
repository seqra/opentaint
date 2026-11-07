# Local STAR_OR_ANY model

Run `python3 spec/lean/proposals/initial-emission/check-star-or-any.py` from
the repository. The checker compiles eight pinned modules in a temporary
directory. It requires the repository's existing Lean toolchain and launches
no JVM or analyzer. Only `propext` and `Quot.sound` are accepted.

The two helper modules retain their checked prototype names and exact bytes.
They model the earlier MAY-to-plain-STAR candidate. Its local image/layer
proofs did not prevent the demonstrated nested-call coverage loss. They do
not assert the new feature is globally sound.

`StarOrAnyDesignProofFixed.lean` contains 29 local laws for the selected new
tail: STAR-first admission with an E-gated MAY fallback for ANY demands,
minimal minting/marker inheritance, raw/stored image witnesses, public marker
erasure, retained archived point inputs and arbitrary-count wrapper induction.

`StarOrAnyObligationsProofFixed.lean` adds 10 checked local laws. Together the
two new modules have 39 laws. The supplement proves:

- Normalize each ND member and remove exact duplicate normalized members:
  the conjunction of STAR-geometric predicates stays equal. Live C2
  capability is outside that predicate class.
- Every bounded earlier Empty-E MAY cut gives the same SOA seed and intrinsic
  layer at the witness. Scope, family, original and exit labels stay equal.
  This is the local witness law for an adapted loop certificate.
- A separate frontier of exact SOA Facts preserves each supplied C2 effect
  in both arrival orders and with duplicate offers. Its keys include the
  whole pattern, E, mark, layer and literal protection. DATA canonicalization
  is a function parameter over erased geometry.

`StaticCarryC5Preimage.lean` adds 13 positive local adapter laws. At a saturated
one-field static slot, a concrete stored STAR key fails the direct STAR carry
entry. It has an accepted SOA preimage under the existing same-slot MAY family.
The C5-only helper uses that pair only after the unchanged `canStoreInitial`
test permits it. It keeps accepted legacy pairs, non-STAR keys and refused
alternatives. Both paired endpoints keep the same owner, field and mark.
The scalar output law proves equal restriction for STAR/EmptyE and MAY at the
same query position, with supplied layer, mark and literal H retained. It does
not clear actual E or change C2. The STATIC anchor is an explicit counted-slot
projection; native STATIC, packed and protection adapters still need tests.

`PublicDemandHandoffCounterexample.lean` contains eight separate negative
handoff checks. It uses the checked C2 and public normalizer. A singleton
concrete SOA/T DATA row keeps its DEMAND layer when both P and C normalize to
STAR. Backward-to-forward handoff uses C as the next entry and P as the paired
exit. The next run-3 STAR/T demand rejects a child EXACT/T NORMAL actual. The
old MAY/T demand admits that actual at the terminal child EXACT position.
Same-head and run-2 controls do not change this run-3 descendant rejection.

The counterexample has an executable actual witness. Its raw row is an
explicit finite model input, not a claim about native row construction or
recorded physical ports. It shows a missing next-C2 route under public
normalization. It does not select a repair, prove a complete native first
loss, or prove whole-program failure by itself. It does not contradict the
39 scoped laws: STAR-geometric equality and local wrapper capability do not
prove preservation through this public handoff.

`SavedRepeatObserverCountermodelProofFixed.lean` adds nine separate conditional
counterexample laws for the second Deep case. The model supplies a ZERO-origin
`x.f^3.EXACT/T,NORMAL` offer and three empty observer-family responses at that
offer. A supplied saved NORMAL FLOW row `x.f.STAR -> x.STAR` uses the existing
AP summary operation to remove one field while retaining EXACT/T,NORMAL.
Its first output is nongrowing; a finite replay under output budget 2 computes
`f^3 -> f^2 -> f -> root` and reaches the modeled sink. The empty three-family
projection drops the offer and misses that observation. This is not a proof
of native record eligibility, physical routing, target permission or a complete
observer repair. The raw offer and saved row are explicit model inputs, not
new native guidance. It resolves neither pending behavior question.

The finite tags are symbolic templates, not a proof of every legal native
Facts constructor. The ND law does not prove native premise rebuilding or
complete C5. The certificate law does not prove equality with the complete
native trial or all loop observations. The point algebra specifies what a
backend must retain; it does not prove producer arrival, native fresh deltas,
mixed-header adapters or packed/scalar agreement. Physical ports, arbitrary
static/GROUP/mx/E/noncounted/ZERO adapters, whole-program recovery, global
source/sink soundness and termination remain open. These limits must stay
visible beside native validation.

The original external attempts and proof-only syntax corrections are retained
in the investigation evidence. The copied files are the exact checked fixed
versions; theorem statements and selected definitions were not weakened to
turn a failed check green. The checker reports 39 design laws and 13 adapter
laws as positive local results. It separately reports eight public-handoff
and nine conditional saved-repeat counterexample laws. Each category has its
own counts and axiom audit. The 69 audited statements are not 69 proofs of
soundness. Only the stated foundation
axioms are allowed. The earlier 26- and 12-law prototype dependencies are not
counted as new SOA laws. The native coverage gap and behavior decision remain
open; a successful checker result does not close them.
