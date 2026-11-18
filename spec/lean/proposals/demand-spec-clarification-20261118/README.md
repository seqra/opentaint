# Scalar NE application and field limits

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
correspondence obligations in §6 of the specification.

Use the source-hash-checked `two-sided-field-cycle-20261117/checked-proofs`
receipt as the dependency directory. Compile with Lean 4.35.0. Keep
build output in the external data archive.

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 LEAN_PATH="$dependency_dir" \
  lean -o "$out/ScalarApplication.olean" \
  spec/lean/proposals/demand-spec-clarification-20261118/ScalarApplication.lean
```
