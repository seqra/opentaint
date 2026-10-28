# Demand storage and predefined summaries: local validation

Date: 28 October 2026. The implementation follows the
[selected proposal](../design/bidirectional-demand-storage-predefined-summaries-implementation-20261028.md).
The [committed-source project campaign](bidirectional-demand-storage-predefined-performance-20261028.md)
is complete. This document records local validation; the linked report records
project performance and the remaining strict finding differences.

## Implemented scope

| Part | Before | After |
|---|---|---|
| Initial admission | Build paired demand candidates and then read their entries | Read distinct entries; use a marked-output witness search for skipped static paths |
| Summary restriction | The method actor collects and restricts paired candidates | Demand storage selects correlated entry/exit rows and keeps protection masks |
| Static completion | One paired traversal serves both operations | Direct local rows, local composition, then visible callee rows; C2 uses two frontiers and C5 keeps labelled pairs |
| Snapshot life | Static completion belongs to incoming run-2 | This remains explicit: run-3 and later use direct local demand only |
| Spring cleanup | Save every registry field, clean all statics, restore every saved field | Apply one complete registry-preserving model at the call |
| Modeled method | Analyze the body and method boundary rules | Create no body actor or subscription; skip entry and exit rules |

The last row includes the selected semantic change. A generic exit sink
inside modeled cleanup can stop reporting. Call-site rules remain active.
Controllers keep their normal analysis and annotation checks. The legacy
Spring generator keeps its save/restore code and cleaners.

AP transfer, field limits, native NORMAL persistence, actual-input mark
checks, immediate static write supply, and the backward original-ZERO
exception remain unchanged. No StrongQueries, grounding support, cache policy
or IR storage change is included.

The production paired `near`/`covering` APIs, old closure walk and actor
`restrictBy` helper are removed. The exhaustive relation adapter remains
in test sources only.

## Local evidence

| Suite | Tests | Failures | Skipped |
|---|---:|---:|---:|
| Common dataflow | 2,015 | 0 | 0 |
| JVM dataflow | 445 | 0 | 0 |
| Go dataflow | 1,323 | 0 | 0 |
| Java rule provider | 218 | 0 | 26 |
| Application, final observer layout | 1,045 | 8 | 13 |

The independent finite demand test checks all 64 directed three-method
call graphs. It compares both operations with a separately saturated seed
relation. Cases include FLOW and mapped cycles, FULL/GROUP compatibility,
real ZERO writers, field exclusions, EXACT class markers, context ownership,
ND originals and protection. A negative color query also checks that coverage
does not intern hypothetical initials. Adapter spies reject paired C2 work
and graph traversal after complete direct local coverage.

The predefined tests check schema filtering in both directions, exclusions,
layers, protection, explicit ZERO control, mixed target dispatch, registered
identity selection, and a reversed call-site source with a `T -> ZERO`
result. Real Spring tests check both generation policies and the exported
prescan graph. They reach, complete and accept **run-3**. Cleaner precision
checks reach, complete and accept **run-9**.

All 126 selected Lean audits pass without axioms. Their EntryProjection
dependency passes another 20 audits. These are local models. Kotlin adapter
and JVM behavior are checked by tests; this is not a whole-JVM proof.

The broad command uses the existing Go server artifact with
`-x :opentaint-ir:go:buildGoServer`: the local protoc cannot rebuild that
unrelated server. Go dataflow tests still run. No project analyzer heap or
timeout is changed.

## Repairs found by validation

The first common pass found that diagnostics traversed a canceled demand
index and changed TIMEOUT into FAILED. Store row counts at snapshot build
time; diagnostics now read counts without traversing canceled state.
The final common suite includes the timeout and cancellation checks.

The first broad pass found a test observer which cast the new method demand
index to the removed trie layout. All 20 extra application failures had
that cast exception. Update the test observer to read the immutable paired
rows. Do not change production behavior or expected finding IDs for this
test repair.

The final application rerun has only the eight older cleaner precision
failures. Each has exactly the saved missing and extra ID sets: zero missing
IDs and 26 extra IDs in total. No new failure remains. Test expectations
remain intact. This is not an all-green application result.

The [validation receipt](data/bidirectional-demand-storage-predefined-validation-20261028.json)
contains test totals, exact precision differences, proof source hashes and
changed source hashes. Production source hashes match the successful module
checks and final application check.

Logs, JUnit XML, source hashes and proof outputs are stored under
`/drive-testcomp/opentaint-go-rules/demand-storage-predefined-20261028/local-validation`.
The project campaign used the committed implementation and the four fixed
configurations in `task.md`, with the saved `f945f92` baseline. It did not rerun
the baseline.
