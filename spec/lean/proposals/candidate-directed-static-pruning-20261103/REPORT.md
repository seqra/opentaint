# Finite model validation report

Status: **UNSELECTED CONDITIONAL MODEL PASS**. Reference runtime:
`050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

The [checker](check.py) compiles [CandidateStaticPruning.lean](CandidateStaticPruning.lean)
with Lean 4.33.1, one worker and a 768 MiB compiler limit. It audits 40 theorems
and all 66 explicit public definitions/theorems. The final kernel dependency set
is `propext` and `Quot.sound`; no choice, unproved declarations or native-evaluation
proofs are admitted. See the [receipt](checks.json), [axiom audit](audit.txt) and
[eight reference source pins](reference-source-pins.json).

The main theorem preserves the entire ordered frozen result under the explicit
`OracleEquivalent` prerequisite, required only on C. Ordered observed/lost raw IDs
and peak metadata are unchanged, including distinct raw rows that normalize to
one key. Both NORMAL/DEMAND rows and protection produce the old guidance
membership. Executable witnesses cover FLOW exact-pair normalization, dropped
FLOW mark exclusions, abstract MUST to ANY, and a missing colored row that stays
lost despite a surviving FLOW row. No FLOW coverage oracle is substituted.

The empty-C branch makes no common/private-B enumeration request, candidate-row
lookup or oracle call in the finite plan. The old finite caller plan materializes
n+m eligible survivor rows; the candidate caller plan has two actions per raw ID
and no full-view enumeration action. Both empty and nonempty examples have
strictly fewer unrelated caller materializations. These counts concern supplied
finite eligible scalar snapshots, not all allocations made by Kotlin `all()`.
Oracle-internal materializations remain an explicit unknown cost: the model
requires a separate cost law before claiming zero total unrelated work.

**Kotlin exact-oracle equivalence is not proved.** No concrete store query,
packed-store adapter, lifecycle/cancellation/exception equivalence, native test,
runtime implementation, project speedup or retained-memory reduction is verified.
The executable reference oracle enumerates the old survivors and demonstrates
consistency without an efficiency benefit. The [proposal](PROPOSAL.md) preserves
the existing semantics and stays unselected. Heap dominance and optimization
ranking remain separate evidence.
