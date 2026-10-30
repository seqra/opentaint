# Checked models for the three selected changes

Status: checked models for the selected implementation. The checker verifies
the models and source hashes only. It does not certify runtime tests or project measurements.

Read the [implementation proposal](../../../../docs/design/bidirectional-demand-stop-static-labels-cfg-delivery-implementation-20261030.md)
for source bindings, APIs, required tests, and the limits of these models.
The selected contracts are:

1. Use empty selected outgoing demand to stop a complete restricted forward run.
2. Select necessary static-demand labels before decoding and owner checks.
3. Cache first-relevant CFG destinations by instruction and base. Store a
   completed statement result under its producer S.

The first contract changes termination. The other two must preserve semantic
results within each executed run. Callback counts can change.

## Reproduce

From the repository root:

```sh
python3 spec/lean/proposals/selected-work-20261030/check.py
```

Use the installed `leanprover/lean4:v4.33.1` toolchain. The checker verifies the
pin, builds the models from source, audits public theorem and definition axiom
dependencies, and writes [checks.json](checks.json). It uses one CPU, one Lean
worker, a 768 MiB Lean limit, and a 90-second timeout for each command. Generated
objects and logs stay under the ignored `spec/lean/.lake/verification` directory.
The checker does not build or run the analyzer.

## Checked scope

| Source | Named theorems | Audited public declarations | Main result |
|---|---:|---:|---|
| Existing [CurrentDemandFrontier](../../ApSpec/CurrentDemandFrontier.lean) | 11 | 19 | Normalized insertion and count support |
| [SelectedStop](SelectedStop.lean) | 23 | 34 | Complete-barrier decisions and payload preservation |
| [SelectedStaticLabels](SelectedStaticLabels.lean) | 21 | 45 | Necessary selectors preserve complete rows and final results |
| [CachedCfgDelivery](CachedCfgDelivery.lean) | 12 | 29 | Total finite BFS, path witnesses, cache agreement and post-S admission |
| Total | 67 | 127 | All checks pass |

There are 56 new named theorems. Anonymous executable examples are additional
controls and are not included in that number. The only audited axiom
dependencies are Lean's `propext` and `Quot.sound`. The checker rejects proof
holes, custom axioms, noncomputable source, and `Classical.choice` dependencies.
Source hashes bind the receipt to the checked models and reviewed runtime files.

### Stop

The model derives empty method-key support from the normalized builder. It
checks report-empty precedence, the new outgoing-demand stop, run-1 exclusion,
backward continuation, observed-counter independence, and cancellation/failure
precedence. Report, persisted-record, and frontier payloads remain intact.
The recorded OWASP demand sequence has an executable run-5 stop control.

The support theorem binds to the production `HandOff.of` builder. It does not
validate arbitrary manually constructed HandOff values. It does not claim that
a skipped backward run could produce no work.

### Static labels

The model distinguishes FULL, GROUP, and a genuine ZERO endpoint. It proves
directional coverage and symmetric nonzero composition selection. Selected
rows retain their original complete relation, geometry, ordinal, and owner.
A necessary selector before a final predicate preserves its final row list.
Controls retain FLOW repair and show why source preflight must use `All`.

The owner-cache result assumes truthful completed Boolean answers. Query-order
tests must bind that condition to the unchanged production owner algorithm.
Unknown atom cases use the old scan. They are not new rejected inputs.

### CFG delivery

The finite BFS terminates by a decreasing finite search state. Each target has
an executable path through neutral predecessors. The closure proof gives
completeness, including cycles and empty frontiers. Cache agreement does not
depend on a depth cutoff.

The producer-keyed result model proves identity idempotence, isolation of other
producers, protection upgrades, complete fresh-result fanout, and identity-loop
suppression. It has computed diamond, identity-loop, empty-cycle, and first-entry
controls. Its two fresh annotation levels are not a project-wide work bound.

## Required implementation connection

These models do not prove JVM/AP neutrality, all field/mark annotation cases,
or the complete analyzer scheduler. Before implementation can pass, prove and
test the adapters in proposal section 6.4: frontend relevance, completed output
preservation, path simulation, late standing dependencies, observations, and
counted completion. Preserve ordinary return transfer before boundary rules.
Initial or resumed inputs must not prepopulate post-statement result rows.

Extend the model if those tests expose a finite counterexample. Do not change
field transfer, rule semantics, or static supply to satisfy a narrower model.
