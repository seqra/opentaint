# Block alias and definition-witness boundary

13 November 2026. This audit concerns current target `1025a197…`; it does not
classify that row or prove whole FLOW-family retirement. The compatible OWASP
project capture still reached/completed/accepted run-11. No project scan was made.

The selected alias model in `ApSpec/CorrelatedConcreteImplementation.lean`
proves semantic fact coverage under define, transport, mark, clean and identity
steps. It does not model C2's per-base restart or source/Target observation
services. Native `initialFacts` starts one base; `offerChild` does not expand
that initial to its aliases. Thus, full owned-block alias closure cannot simply
be imported from that model.

The native C2 check supplies X/T and Y/T to one block view with only an X demand.
It emits one X initial, no Y initial, and starts only X. Common original and
same-cell aliasing are explicit assumptions of the small interface model,
not properties recovered by the native probe.

A different uniform adapter can address genuine alias observations:

```text
genuine required use of LocalVar X at target t
  -> X has an initialized value on a finite valid execution prefix
  -> explicit assignment/catch definition of X on that prefix
  -> a finite reverse-CFG path from t to a mention of X
  -> backward no-kill liveness keeps X at t
  -> X's own canonical-port offer registers t, at the same scope/C2
```

The Lean module gives executable definition/mention witnesses for the finite
initialization model and proves that any mention path is live under a closed
backward mask. It also checks the simple alias-name projection counterexample.
All eight axiom lists are empty. It does not kernel-verify JIR well-formedness,
the native bitset solver, or the complete frontend/alias adapter.

The source audit found no implicit-local exception in the inspected paths:

| Case | Source correspondence |
| --- | --- |
| Assignment and call result | JIRAssignInst includes LHS and RHS operands. |
| Catch local | JIRCatchInst includes its throwable operand. |
| Phi local | Phi is an expression under an ordinary assignment. |
| Parameters and this | JIRArgument/JIRThis map to nonlocal AP bases. |
| Eliminated raw copy | The frame reuses the existing RHS value; it does not create an undefined local. |
| Lambda/string/array/Spring temporaries | Inspected generators add explicit JIRAssignInst definitions. |
| Exceptional and discovery routes | Backward graph retains reversed real edges and adds discovery edges. |

Actual pinned JIR constructor/extractor tests cover copy, phi, catch and formal
projection. The native definition-control fixture adds X=Y before the loops;
X then reaches both reverse targets and the source hit exists before FLOW in
both variants. This removes the earlier dead-local callback difference. It is
not a whole-driver valid-sink-loss example or a proof for arbitrary plugins.

A false over-approximate alias need not have the genuine definition witness.
Its callbacks can differ. A source-hit set is source permission state, and a
Target is routing/report state; neither is merely a batch-dependent diagnostic
count. Their loss needs a semantic replacement argument before a retirement
rule can be accepted.

The global edge-only NoLocalInterface candidate fails this corpus: OWASP H11
has 0 local entries and 207 local exits; Conductor H7 has 76,221/81,660;
Stirling H9 has 161/294. Entry-only absence does not close future handoffs.
These are counts from the complete original post-handoff snapshots, not new
project scans.

For a same-C2-entry retained sibling, the first post-cut admissions and their
shared registration/carrier effects remain equal. Later coarse-query refinement
and publication still need a separate proof. No source, CFG or JVM predicate
is added to eligibility.

External evidence is under `redundant-demand-rows-20261112/cases/`:

```text
block-alias-closure-audit-v1/
dead-local-alias-definition-control-v1/
jir-local-mention-exceptions-v1/
```

Use the receipts for source/build pins and exact limits. The previous fan-out
and dead-local wake-up packages are unchanged.
