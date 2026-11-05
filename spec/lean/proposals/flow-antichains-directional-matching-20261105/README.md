# Canonical facts and directional matching: proposal models

Status: **selected implementation proposal; analyzer implementation unchanged**.

The [proposal](../../../../docs/design/bidirectional-canonical-facts-normal-relations-directional-inside-implementation-20261105.md)
states current/new behavior, storage ownership, native adapter gates and future
project experiments. Runtime reference:
`52f32dd437d438aec4a700a02c18d94c31d58093`.

```sh
python3 spec/lean/proposals/flow-antichains-directional-matching-20261105/check.py
```

The checker uses Lean 4.33.1, one worker per compiler and a bounded memory limit.
It checks every module and audits the explicit public definitions and theorems.
No `Classical`, choice, unchecked axiom, `sorry`, native evaluation or unsafe
declaration is permitted. `propext` and `Quot.sound` are the only allowed kernel
dependencies. [checks.json](checks.json) pins sources, proposal, toolchain and
unchanged runtime context. [audit.txt](audit.txt) records the declaration audit.
Standalone component checks are also retained; the combined checker does not
rewrite earlier investigation evidence.

| Module | Constructive scope |
|---|---|
| [Canonical.lean](Canonical.lean) | Same-tail compatible spatial cells; executable prefix coverage; cross-E region union; complete immediate-child fill; no invalid fill; terminating pair reduction, fixed point and idempotence; header-bucket query equivalence; explicit overlap witness |
| [Relations.lean](Relations.lean) | Concrete correlated NORMAL STAR relations; exact common-suffix factor and residual-prefix cover query; online antichain, no invented row, concrete relation-union preservation; below-prefix payload application and forward/reverse growth |
| [Matching.lean](Matching.lean) | Explicit producer/reader roles; ordered filtering of native-eligible leaves; only opposite records allow strict-ancestor incoming STAR; AT/non-STAR preservation; complete ND binding products; empty-query run-1 vacuity |
| [Reachability.lean](Reachability.lean) | Concrete finite-path composition of the proved NORMAL relation basis; the same intermediate positions, full marks and endpoint predicates remain witnesses |

The models distinguish the concept from its implementation:

- The spatial scalar reducer preserves concrete-location union. Its exact-key
  bucket query has the same answers and avoids unrelated header candidates.
  Native production code uses packed tries, not pair enumeration or MarkTable
  atomization. FLOW's cofinite representation limits partial mark fills.
- The aligned relation index has the same cover query as the executable
  specialization relation. A trie is the production index; the finite list
  implementation is the semantic oracle. Only an actually inserted row creates
  a terminal. A family key never authorizes a fabricated weaker row.
- Matching proves the newly selected filter, relative to supplied native
  eligibility. It does not claim equality with the previous broader policy.
  C2 uses canonical facts only, as selected by the user; the old extra refinement
  initials are deliberately not preserved.

The native adapter must still verify immutable packed DAG/mask correspondence,
catalog-aware exclusions, protection, typed reverse-MUST application, exact
ports, publication settlement and persistent index lifecycle. In particular,
the overlap geometry theorem is not permission to change generic forward
matching or to promote a DEMAND result to NORMAL.

The [native overlap evidence](native-overlap-evidence.json) embeds the source,
full output and provenance for seven standalone controls on the unchanged
runtime. Three FLOW controls and four concrete controls pass. They check the
projected selector/application bridge, incoming layers, full marks and
protection. See [the adapter](native-overlap-adapter.md) for the exact transient
MUST-conclusion capability and legacy-plus-projected-lane design. These controls
do not run the full driver or verify packed actor integration.

The concrete path theorem does not prove that the approximate engine discovers
every concrete witness after the matching narrowing. No model here verifies
the full C2/C5/loop observer/handoff fixed point, Kotlin implementation, project
quality, termination under resource limits, or speedup. Native finite-driver
regressions and the selected real-project campaign are required implementation
gates. A missing whole-driver theorem must not be reported as already proved
by antichain inclusion or filter-subset laws.

Existing campaign labels remain: OWASP **run-5/run-5/run-5**, Conductor
**run-6/run-5/run-5**, Thingsboard **run-1/none/none**, Stirling-PDF
**run-9/run-8/run-7** (reached/completed/accepted). No project was rerun for this
proposal. The prior bounded direction controls complete/accept **run-7**; those
finite programs do not establish whole-project equivalence.


## Implementation follow-up

The user requires transitive subsumption in both arrival orders. The native
implementation uses packed input-prefix candidates and DAG suffix grafts, with
native output-mx subset checks. It does not allocate one index row per output
path. `Implementation.lean` adds 13 constructive laws (17 declarations) for
prefix eligibility, transitive marked coverage with no retained intermediate,
protection/excluded-mark negatives and exact cofinite support union.

Run `python3 implementation-check.py`. It checks all five modules: 175 theorems
and 249 declarations. `implementation-checks.json` pins the current proposal,
checker and native source snapshot. The kernel verifies the models and their
bridge laws; the source pins do not prove the Kotlin adapter. Native tests and
real-project quality checks remain required. There is no whole-engine finding,
scheduling, convergence or resource theorem.

The original `check.py` and `checks.json` retain the unchanged `52f32dd` source
boundary. Use that checker in the reference tree. Do not replace its archived
source pins to claim that the implemented Kotlin code has a kernel proof.
