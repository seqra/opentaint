# Demand guidance retention: finite model

Selected behavior: keep STAR and repair demand guidance. The model imports the
existing scalar C2 model without changes. It does not use the rejected
first-field MUST emitter.

Run from the repository root:

```bash
python3 spec/lean/proposals/demand-guidance-retention-20261106/check.py
```

The checker compiles the existing scalar model into a temporary directory,
then checks this model. It checks every printed axiom dependency. It permits
only the existing constructive foundations `propext` and `Quot.sound`. It
does not write to `formal/` or change the scalar model.

The first 16 lemmas prove finite C2-image and paired-label properties. Exact row
union keeps root and child demand positions in either arrival order. Data
prefix removal can lose the child's C2 image. The model also checks the
existing handoff selector, MUST-to-ANY guidance projection, and a same-point
concrete MAY/EXACT counterexample. Exit labels are complete opaque identities.
The model cannot borrow an exit from a different row.

`ProducerGuidance.lean` adds 23 lemmas for exact coordinate add/delta,
freshness, duplicates, both arrival orders, and the handoff of already supplied
paired coordinates. It also checks the existing same-head mx intersection:
the allowed T/U request set is the union of its inputs in the finite FULL
table. A separate counterexample shows why equal projected demand rows alone
do not prove equal runtime requests. The same-head exact-input cell is checked
too: its existing EXACT/FLOW initial can appear beside the parent's STAR/FLOW
initial. The checker runs all 39 lemmas.

The scope is FULL scalar facts, ordinary nonstatic bases, counted fields,
empty field exclusions, and finite lists. No production C5 restriction,
field-budget cut, alias transfer, static flow, ND transfer, or ZERO transfer
is proved. ZERO and ND occur only in the handoff selector table.

These proofs start with available exact rows. They do not prove that all
producer paths retain those rows before publication. The late-store example
shows why that distinction matters. Role transitions, engine adapters, and
the required source/sink effects remain open. These local lemmas do not prove
final Conductor recovery or whole-engine correctness.

The [design draft](../../../../docs/design/bidirectional-demand-guidance-retention-implementation-20261106.md)
and [complete local Conductor snapshot](../../../../docs/reports/bidirectional-conductor-must-demand-snapshot-20261106.md)
state the implementation and evidence limits.
