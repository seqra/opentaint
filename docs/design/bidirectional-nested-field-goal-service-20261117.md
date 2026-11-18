# R40 [REC] Nested field-path goal service

R40 extends the regular field-path certificate in [R39](bidirectional-regular-field-goal-service-20261117.md).
The [counterexample and validation](../reports/bidirectional-two-sided-field-search-20261117.md)
show a recursive reader with a field read on each side of its recursive call.

| Part | R39 | R40 |
| --- | --- | --- |
| Complete pure FLOW route slice | Both sides need validated regular languages | One side can have a nested prefix and suffix around a recursive call. The other side needs a validated regular language. |
| Origin service | A retained valid NORMAL witness or a proved empty intersection | Also accept the empty intersection proved by the state pair check below |
| Engine operations | Direct DATA propagation and the existing terminal handoff | Apply the same operations. Use the added certificate at the existing terminal handoff. |

The major semantic change is the set of origins that can close an anonymous
root Target. All origin and observer checks from R38 and R39 apply. A
certificate established at a completed forward seal enters a later forward
snapshot. Use it only for that snapshot's configured root ZERO → DemandTarget
handoff. The check creates no report or source permission. It adds no field
limit exception, emitted fact, summary, subscription or suffix evidence.

## Clause extraction and word order

The grammar has finite method owners and two clause forms. A normalized
branch returns either a base word or a word around exactly one child result.

```text
A → base
A → prefix · B · suffix

valid exact relation:
    writerWord · sourceFields = readerWord · observerFields
```

A reader reads prefix before the call and suffix after it. A writer that
prepends fields before and after a call puts the **after-call** fields first
in the word. Use the same complete route slice, physical ports, field IDs,
all-origin catalogue, alias proof and semantic observer coordinates as R39.
Use Unknown when a route, rule effect, binding or port lacks a complete
model. Two nested languages, an unspecified competing effect, and multiple
nested results on one branch are outside this rule.

Include the regular side's source or observer fields in its automaton.
Check the nested side's source or observer fields after the complete
derived word. For example, if a writer derives `g.f` and the source is at
`h.$`, the written path is `g.f.h`. Attaching `h` to the recursive base
would give `g.h.f` and can reject a valid read.

## Finite check

Let `step(p, word)` return the states reached when the regular side starts
at state `p` and reads `word`. Each cell records only two states and an owner.

```text
cells = empty set

for every A → base:
    for p in states:
        for q in step(p, base):
            add (A, p, q)

for each newly added (B, m, n):
    for every A → prefix · B · suffix:
        for p where m in step(p, prefix):
            for q in step(n, suffix):
                add (A, p, q)

if the complete clause set or closure check is unavailable:
    return Unknown

if there is (startOwner, regularStart, q)
   and step(q, nestedSideOuterSuffix) reaches a regular accepting state:
    return Possible

return NoRoute
```

Validate closure against every supplied clause. Validate clause completeness
against the code slice separately. Failure to validate either yields Unknown.
Use normal root service for other already confirmed origins and keep a root
Target if any origin or observer predicate under that key is unserved.

## Proof and cost

Each actual word derivation gives a cell in any checked closed set.
Induct on the derivation. A base clause adds its endpoints. For a nested
clause, split the regular word path into prefix, child and suffix. The child
cell exists by induction, so closure adds the outer endpoints. Then consume
the outer source or observer suffix. A real exact relation gives an accepting
endpoint, which contradicts NoRoute. No step depends on iteration number,
field limit or recursion depth. To use the theorem for program code, the
caller must validate the complete extraction for the selected origin and
observer. If it cannot prove coverage, it must keep the guidance.

With `M` owners, `Q` automaton states and `C` clauses, the worklist adds at
most `M·Q²` cells. Given precomputed prefix and suffix relations, each
recursive clause can examine at most `Q⁴` combinations in the dense case.
Index by child owner and state endpoints. Compute the small query only for
eligible unresolved goals, reuse immutable regular automata, and retain only
the existing closed-goal result after the seal. A query budget may return
Unknown. There is no expansion of recursive field words. This is bounded
additional proof work. The fixture measures fewer runs with the certificate.
Project workload and whole-engine extraction and closure obligations remain
open. [Lean proofs and reproducible search](../../spec/lean/proposals/two-sided-field-cycle-20261117/README.md).
