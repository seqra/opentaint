# Directional strict-ancestor STAR matching

5 November 2026. SELECTED DESIGN; NOT IMPLEMENTED.

`Matching.lean` is a finite executable model of the selected matching delta.
An invocation supplies CURRENT, SAVED_DIRECT or OPPOSITE explicitly. The new
filter removes a native-eligible STAR leaf only when its path is a strict
ancestor of the query path and the role is not OPPOSITE. There is no run1,
NORMAL-layer, concrete-mark or query-tail exemption. Equal-path AT, below,
EXACT/MAY/MUST and native header checks remain unchanged.

The finite envelope retains complete path, owner, entry/exit ports, full mark
profile, E/mx, layer and protection IDs. It does not model their native
eligibility computation. The executable ordered product models complete ND
bindings after every arm has passed the same selected predicate. It proves
no partial binding, native binding inclusion, native opposite-role equality,
ordered filtering, idempotence and exact payload retention. It also proves
that an empty query path cannot have a strict ancestor. This last law maps
to ordinary run1 current-summary premises: `validateRun1Initial` requires
nonstatic ordinary initials to have an empty path. Static prefix handling
still needs a native adapter test; no complete JVM grammar theorem is made.

Run `python3 matching-check.py`. The isolated receipt authenticates only this
module, this README, its checker, proof guide and immutable reference source
pins. It does not import the sibling canonicalization/relation modules. The
three component models need a separate integration argument and native gates.

Required native adapter and CEGAR gates:

1. Match each native scalar membership through explicit role, keep the same
   `summaryPart` AT/below rules and protection reattachment.
2. Propagate OPPOSITE from the record producer/reader directions through the
   actual saved matcher and pure observer. Never infer it from `record=true`.
3. Use CURRENT for current AP/Target/ND/static binding; use SAVED_DIRECT for
   direct saved AP and saved forward NormalTargets. Persistent normal Targets
   are forward-only; no direction field or equality change is required.
4. Preserve native MUST definite/provisional lane selection. Its internal
   `record=false` query is not a current-publication role inference.
5. Keep microedges, predefined edges, checkMark, run1 request slot matching,
   C2/C5 admission, source permissions and full ND join semantics separate.
6. Match actual execution, saved replay and complete loop observation under
   the same role policy. Candidate indexes may remain native supersets; the
   selected matcher must validate every delivered member.
7. Repeat the existing 8 complete-driver restricted-run controls, the 36
   scalar controls and the opposite-seeded width control; add all-run1/native
   scoped/Target/ND/static tests before claiming a production implementation.

Proof limits: no Kotlin correspondence, whole-engine equivalence, universal
safety, convergence, report equivalence or project performance theorem. The
policy is an explicit selected matching change, not an exact optimization of
the old broader matcher. Eight finite positive driver outcomes do not prove
that every same-direction STAR ancestor transfer can be removed safely.

The separately selected reverse-MUST overlap correction is not proved by
`opposite_exact_list`. That theorem is relative to the supplied eligibility
envelope. A trusted transient MUST provenance constructor and the pure region
model must justify any added eligibility. The native bridge must then check
matching plus application on the projected same-path STAR piece. Concrete
EXACT-to-MUST inverses retain their native result/layer; no general DEMAND
rewrite is authorized by the matching model.
