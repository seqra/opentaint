# Call-stage result merging: local design proof dossier

Date: 1 November 2026. Status: finite local models PASS; future candidate not selected.
No analyzer implementation or optimization selection is part of this work.
Use [proof-guide.md](proof-guide.md).

The [model package](lean/proposals/call-stage-result-merging-analysis-20261101/README.md)
contains executable finite keys, an exact result collection, a protected
observation model, and a local continuation-work model. The
[receipt](lean/proposals/call-stage-result-merging-analysis-20261101/checks.json)
records **44 checked theorems**, **76 audited public declarations**, and
`propext` as the only axiom dependency. The checker rejects classical
choice, unproved declarations, warnings and source changes during the check.
The verification ran after all selected project analyzer processes stopped;
it did not compete with the project timing campaign.

## 1. Candidate and unchanged behavior

Current call stages collect duplicate outputs in lists. Some run-1
cleaner steps already merge equal ordinary keys and OR protection.
The candidate extends that exact result merge to more materialized stage
boundaries, including later runs. It aims to execute a shared suffix once
for equal continuation values.

The candidate changes no field, mark, demand, rule, cleaner, alias,
Target, source-permission or summary-intersection rule. Every producer
still executes its current effects before its returned values merge.
Different originals, layers, control flags, scopes and ordinary payloads
remain distinct. No actor-wide completed-state cache is modeled.

This local proof work does not authorize implementation. A new spec and
runtime adapter review are required before selection.

## 2. Finite model and invariants

`Scope` contains actor/run identity, call site, program point, the complete
original ID, tri-state identity classification, fact layer, caller layer,
and pending demotion. The program point represents a stage or a specific
cleaner step/phase. The complete original ID is opaque: no ND member can
replace the original.

`Payload` contains an explicit REACH/FLOW/TAINT kind, base, geometry, tail,
field exclusions, mark exclusions, a mark symbol (ZERO, FLOW, or one full
mark), and a four-slot ordinary membership mask. The finite IDs
are reference identities. A runtime adapter must injectively map the
relevant concrete keys into the modeled scope; the model does not assert
that all project keys fit its small numeric bounds.

`Row.key` contains all that ordinary state. Protection is a separate
four-slot value. A protected membership requires both an ordinary member
and its protection bit. This prevents a stray annotation bit from creating
a fact. Only equal complete keys can merge; protection then joins by OR.
Different full marks and different fact kinds are never merged. This is a
finite generic collection model. It does not prove runtime AP shape/K6
validation or a refinement for arbitrary packed multi-mark Kotlin trees;
a TAINT payload in this model has one full-mark symbol.

`insert` uses an executable list lookup. `collect` consumes inputs in
order and retains the first position of an equal key. This is a reference
relation, not a proof of the Kotlin LinkedHashMap implementation or cost.

## 3. Checked theorem groups

| Module | Checked local property |
|---|---|
| `Keys` | Pointwise protection OR; equal-key joined observation equals the union of both observations |
| `Results` | Each insert/collection preserves ordinary and protected membership; unprotected duplicates cannot clear protection; different marks/kinds/scopes cannot replace each other |
| `Suffix` | A fixed deterministic suffix that preserves equal-key protection OR has the same output observation set before and after merge |
| `Work` | Executable 64 equal alias outputs become one continuation; a distinct identity branch remains, so total 65 becomes 2; control flags and full originals remain necessary keys |

The suffix theorem states its required OR law explicitly. It does not
assume that all stateful rule/ND/request callbacks are pure. An executable
observation-renaming suffix witnesses that contract. Before implementation,
prove or test the same law for the selected AP/cleaner/guard operations
and prove that all producer effects happen before the merger.

The model checks set observations. It does not preserve repeated callback
counts or establish a whole-driver scheduler simulation. Existing semantic
report/rule/source IDs must remain; batch-dependent diagnostic counts can
change only within the already selected observation contract.

## 4. Work result and its limits

The local control has 64 equal alias results and one distinct pass-through.
The checked executable witnesses give 64 -> 1 executions of the equal-result
suffix, total 65 -> 2 continuations, and equal ordinary/protected
observation sets within the finite model.
The 64 producer applications are still required in this candidate.

The symbolic cost model includes one collection cost for every offered
alias result. It does not assert an unconditional speedup. A cost win
requires saved suffix work to exceed the added collection cost. No project
speedup, current profile share, heap reduction, or general asymptotic
analyzer bound follows from this small control.

Separate `applyRecordView` callbacks start separate flow invocations. This
local merge does not combine them. Batching those callbacks needs another
scope/effect-order proof. The model also does not cover a global point
cache, prefix subsumption, distinct geometry union, group-mark rewriting,
new NORMAL/DEMAND conversions, or new source guidance.

## 5. Required runtime correspondence evidence

Before implementation acceptance, verify:

- Exact runtime equality includes every modeled control and payload field.
- Protection OR survives transport through every selected downstream step.
- All source/action, static-operation, request, seed, rule and Target effects
  occur before equal results merge, with the same semantic identities.
- Cleaner phases and stage order remain unchanged; INPUT/READ/CLEAN/WRITE
  resumptions cannot share a collection until their program points match.
- NORMAL/DEMAND, caller layers, pending native demotion, and null/true/false
  identity states stay separate.
- Complete ND originals are preserved, and source/Target observations are
  idempotent under repeated equal continuation input.
- Production differential controls match final facts, protection, reports,
  summaries, demand frontiers, and source-hit identities.

No runtime file is changed by this package. The checker can bind the
reviewed source context, but its mathematical proof is not Kotlin
verification. Current project status must come from the separate campaign
report, including the latest reached/completed/accepted run labels.
