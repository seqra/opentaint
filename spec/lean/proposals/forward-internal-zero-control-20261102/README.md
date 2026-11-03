# Conditional forward internal ZERO control model

Date: 2 November 2026. Status: **DRAFT / UNSELECTED**.
The user decision is pending. No candidate runtime implementation is selected.

Read [the draft spec](../../../forward-internal-zero-control.md) and
[the proof guide](../../../proof-guide.md).

```sh
python3 spec/lean/proposals/forward-internal-zero-control-20261102/check.py
```

The checker uses Lean 4.33.1 with one worker. It audits every explicit public
definition and theorem. It permits only `propext` and `Quot.sound`; it rejects
choice, unproved declarations and native evaluation proofs. The
[receipt](checks.json) records exact model/spec/reference inputs and their hashes.
The [portable axiom audit](audit.txt) lists every checked declaration.
This package is separate from the selected loop-block implementation proof
package and does not update its source pins.

`Control.lean` first models actual root admission and Type-valued existing
CFG paths. It models the two conditional interfaces: internal ZERO admission
and control-only identity completion after ordinary C5 rejection. It also
checks a one-cell/one-standing-link executable rendezvous for late replay.
The ordinary C2/C5 views, source permissions and record APIs are distinct.
The direct check covers 57 theorems and 100 explicit public declarations.

The finite Target-probe example proves why a virtual ZERO/ZERO demand is
unsafe. The admission-only pipeline proves why C2 bypass alone is incomplete.
Concrete root/path witnesses give a positive pipeline with no added Target
permission. The model also checks whole origin, exact ports, input/output
layers, original-ZERO guards, complete ND, no invented return, owner Work
reservation at late delivery and the two-per-scope layer-admission bound.

The no-new-record law applies to the control-cache operation. It does not
claim equal final stores: extra actual control can infer a legitimate new
AP result through ordinary C5. A separate model cell demonstrates that case.
A finite source-action family also shows why bounded control admission does
not bound all rule work.

The checked reference source hashes identify the existing interfaces and
counterexample fixture. They are not evidence that this draft is implemented
or that Kotlin routing, complete AP matching, source effects, whole-driver
convergence or project quality are proved. The actual parent/port mapping
and complete rule/source/layer adapters still need native correspondence
if the behavior is selected. The current measured 6052 attempt reached OWASP
run-5 with 18 missing identities and conductor run-2 FAILED; it is not an
accepted four-project campaign.
