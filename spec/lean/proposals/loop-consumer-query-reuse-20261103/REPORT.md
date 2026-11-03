# Query reuse design validation

Status: **SELECTED DESIGN MODEL**; no runtime implementation or project experiment.
Reference source is `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

The checker compiles the constructive Lean model on one CPU with a 900 MiB limit
and audits every explicit public definition/theorem. The receipt, axiom audit and
immutable source pins record the exact scope. The design links all native API
choices and test gates. Ordinary AP transfer, protection transport, preimages,
paired C5 selection, saved native application and Target policy are unchanged.

Proofs cover fixed-entry factoring, ordered native row equality, FL+1 budget,
C2 labelled/unlabelled projections, complete observation, memo answer/invariant/
capacity/reference-count laws, bounded admission gates, adaptive restriction-decision
programs and unchanged work state. Pattern-template equality has an explicit
DATA kind guard. The empty-plan shortcut proves empty observer contribution
under no-Target capability and all-port empty certificates. Reach-to-Target and
unknown-kind examples require native fallback. CEGAR examples expose the main
invalid coarser designs.
Complexity counts isolate duplicate C2 work and fixed-original entry checks even
when full output keys are unique. They make no hit-rate or project speedup claim.
An all-miss witness also shows that eager entry preparation can add work.

Kotlin adapter correctness, read-only snapshot/identity realization, native AP
semantics and coroutine ownership remain implementation validation obligations.
No unproved preimage oracle is assumed: the design uses the existing exact
canStoreInitial and restrictConclusionOnly bodies with explicit native fallback.
