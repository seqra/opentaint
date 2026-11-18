# Soundness checks after possible DIRECT replay

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
Follow [proof-guide.md](../../../proof-guide.md).
[Report, controls, counts and limits](../../../../docs/reports/bidirectional-post-direct-soundness-audit-20261117.md).
[Consolidated contract](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

**8 new claims; 7,245 cumulative audited claims in 422 checked modules.**

- `PostDirectReference`: a harness around the selected R34 unary prefix
  reference. A new observation changes the backward question, within the
  field limit. Forward completion includes provisional results reaching
  that observation, rather than testing return-DATA demand alone. Forward
  sources are granted optimistically. This is not a new analyzer policy or
  a complete typed Target/source-permission model.
- `PostDirectChecks` (8): pending observation demand prevents stopping; the
  pack control distinguishes DATA emptiness from frontier emptiness and
  retains NORMAL service at run-3; generic first-field MUST handling uses
  STAR; current full-mark companion layers, same-head MUST and forbidden
  backward MUST remain explicit constructive witnesses.

Four finite checks compare with uncapped ordinary AP return execution:
384 prefix controls (through run-7), 5,660 branch/observation configurations
(through run-7), 5,258 three-owner configurations (through run-11), and
2,302 ordinary overwrite configurations (through run-7). All fixed points
finish; there are no mismatches or diagnostic cutoffs. The screens overlap.
These are executable checks, not 13,604 universal theorem declarations.

Nine new native cold controls pass, through run-9; the combined targeted
suite has 92 passing tests. No prototype adapter is installed in these
new controls. They do not establish whole-engine NE/R34 integration.
The old production loss controls remain expected-broken.

```bash
python3 spec/lean/proposals/post-direct-soundness-audit-20261117/check.py \
  --out /tmp/post-direct-soundness-proofs
# Optional source-identical parent cache:
#   --dependencies /path/to/saved-direct-possible-proof-output
```

The checker verifies parent hashes, compiles the two modules, audits all
transitive theorem axioms, and executes each finite check. It fails on a
mismatch, unfinished fixed point, early exit or warning. Only `propext` and
`Quot.sound` are allowed. All generated data stays outside Git.

No additional concrete soundness counterexample was found in this scope.
G1–G4 remain open. ND, aliases, static behavior, physical loop ports, complete
source permissions and all combined completion histories require wider proofs.
