# Scalar application, continuation service and handoff

[ScalarApplication.lean](ScalarApplication.lean) checks the scalar rules in
§2 and §3 of the [specification](../../../demand-refinement-and-termination.md).

- An independent NE result preserves its head, mark and H for every
  matched residual. It has DEMAND support.
- An NE offer cannot bind an exact premise at the same head. Transport
  preserves NE behind a known suffix. Selecting a strict descendant
  inside the unknown suffix can leave an empty residual.
- The possible STAR case supplies DEMAND binding support even when the
  original STAR was NORMAL.
- Any entry-depth overrun in the checked base family requires the R08
  certificate. The run-2 relay keeps the ordinary cap. An R08 entry
  cannot relax its paired C5 output cap.
- The example checks cover the full R07/R08 identity families, including
  the three-field MUST offer, its controls and the NE variant. They check
  the nested-write keep results for R13 and the published sets for
  representative raw C5 point, STAR and FLOW-companion inputs.

The scalar NE checks start after the ordinary base, mark, role and
port checks. The [bounded child proofs](../bounded-refinement-frontier-20261114/README.md)
cover one-field preparation. The native adapter still has the
correspondence obligations in §7 of the specification.

Use the source-hash-checked `two-sided-field-cycle-20261117/checked-proofs`
receipt as the dependency directory. Compile with Lean 4.35.0. Keep
build output in the external data archive.

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 LEAN_PATH="$dependency_dir" \
  lean -o "$out/ScalarApplication.olean" \
  spec/lean/proposals/demand-spec-clarification-20261118/ScalarApplication.lean
```

[ServiceAndHandoff.lean](ServiceAndHandoff.lean) checks the clarified
service boundary separately from the scalar rules. The checks cover
R17's retained-basis recipe and missing source permission, R19's raw
closure and committed bound service, the typed C5 pair gate, and the
two-ID R37 trace through run-5. The example proof reuses the four-field
marking action and three ordinary field reads. It assumes the sole root
ZERO guide activates the reverse observer and its source permission.
Complete native extraction of uses and transfers remains a prerequisite
for activating a certificate.

Compile with the checked outputs from
`demand-no-loss-audit-20261117`, `demand-refinement-spec-20261117` and
`two-sided-field-cycle-20261117` on `LEAN_PATH`.

[NativeOutputFilter.lean](NativeOutputFilter.lean) checks the analyzer
rule in §4.1. The worklist's first relevant destinations are the
input list. A touched base with no outgoing edge, conjunction, source
or static operation has no effect in the modeled ordinary statement.
The check rejects calls, boundaries and any live destination in the
list. The module compiles independently on Lean 4.35.0.

The broader service and terminal checks in `ServiceAndHandoff` remain
proof models. The implementation in §7 uses existing analyzer operations
and keeps live DEMAND replies and anonymous Targets.
