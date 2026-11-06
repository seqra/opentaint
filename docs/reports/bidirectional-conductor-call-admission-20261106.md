The recorded run-3 calls show no returned-initial difference for the 1,218 matching full input keys. Every matching key has the same returned initial set and recorded ordering in Current and the proper-prefix-off control B. This result applies to structurally equal normalized packets with equal original premises, contexts, layers, and call identity. It does not resolve C2 behavior for packets that have equal denotation but different retained coordinates.

Both diagnostic commands stopped at native run-4 START. Both reached run 4, completed run 3, and accepted the forward run-3 report. Each forward report has five findings. This is a call-boundary diagnostic, with no full quality, convergence, or performance claim.

| Recorded evidence | Current | Control B |
| --- | ---: | ---: |
| Complete call events | 1,359 | 1,899 |
| Unique full input keys | 1,240 | 1,688 |
| Returned initials | 2,437 | 4,055 |
| Complete empty returned lists | 12 | 12 |
| Invalid events or source DROP notices | 0 | 0 |
| Three-argument callee offers | 753 | 1,123 |
| Four-argument callee offers | 606 | 776 |

The [evidence JSON](data/bidirectional-conductor-call-admission-20261106.json) embeds all 1,218 matched-key comparisons, all unmatched-key references, the decoder and audit source, both full control audits, and four exact raw event pairs. It retains hashes for the full analyzer and class-load logs. The four displayed pairs can be checked from the embedded records. Rechecking all 1,218 comparisons needs the full capture logs at their pinned paths. No production source or analyzer storage changed.

The four focus queries call `DeciderService#getTasksToBeScheduled(WorkflowModel, WorkflowTask, int, String)` from its three-argument overload. They use physical call index 0, stage ordinal 3, and ROOT scope `(0, -1)`. The original premise and actual input are root `arg1.ANY`; the actual input is DEMAND with empty field exclusions. Each actual DAG is a single leaf with no protection. FLOW also has an empty mark-exclusion set. Context labels describe native keys, not source-level type claims.

| Input and native context | Current sequence | B sequence | Returned initials in both |
| --- | ---: | ---: | --- |
| FLOW, Empty | 152 | 139 | root `arg1.ANY/FLOW`, DEMAND |
| FLOW, exact HashMap argument 1 | 164 | 150 | root `arg1.ANY/FLOW`, DEMAND |
| Graal FULL, exact HashMap argument 1 | 1227 | 1155 | root `arg1.ANY/FLOW` and `arg1.ANY/Graal`, both DEMAND |
| Graal FULL, Empty | 1233 | 1035 | root `arg1.ANY/FLOW` and `arg1.ANY/Graal`, both DEMAND |

The Graal label is the full logical source atom from `graaljs-polyglot-code-injection.yaml`; the evidence retains its complete name and native context bytes. Field IDs use full typed descriptors. Initial IDs, DAG IDs, mark handles, and identity hashes remain local to their JVM. Shared DAGs are hashed structurally without logical-path expansion. A field descriptor without its type invalidates the whole event. No B-only STAR, EXACT, or MUST initial occurs on the 1,218 matching offers. That is a per-offer result, not global callee input history.

There are 22 Current-only input keys and 470 B-only input keys. All 470 B-only keys use a boundary family that also occurs in Current. Here, a boundary family retains caller/callee methods and contexts, entry indices, physical call index, scope, stage, hook, configuration, and zero-only flag. It removes the original premise, actual facts, and caller/actual/link layers.

The narrower comparisons matter. No B-only key matches a Current key after removing only actual facts. None matches after removing only the ordinary/protection root digests. Thus, these unmatched records supply no pair with all premise/header/layer metadata fixed and only the actual DAG root changed. Sixteen match after removing only the original premise. These populations do not isolate whether retained descendants are semantically redundant or operationally required.

The B-only actual inputs are mainly `arg0`: 149 NORMAL FLOW STAR keys, 112 NORMAL FLOW MUST-header keys, 107 DEMAND FLOW ANY keys, and 35 DEMAND TAINT ANY keys. Smaller `arg1`, static, and marked families remain in the evidence. These are packet headers; the complete ordinary/protection DAG, E, and mx remain part of each input key. The counts do not establish a causal path to missing reports.

Independent read-only audits pass 115 checks for Current and 130 for B. They bind every positive event to raw logs and expected class origins. The original runner flags arose from JVM hidden-lambda source labels and two oversized ordinary DEBUG frontier lines in each run. Those lines contain no admission markers. Raw and extracted marker counts agree: 1,359/1,899 captures, 11/15 settings checkpoints, and zero drops. External audit receipts resolve only these two flags; sealed manifests remain unchanged. The decoder stays fail-closed without the explicit receipts. Unrecorded or unmatched inputs remain unknown.

The [prefix reproducer](bidirectional-canonical-prefix-refinement-reproducer-20261106.md) proves a specific refinement mechanism: parent-prefix removal deletes a finer demand coordinate, changes C2 refinement, and delays its exact observation from F3 to F5. It does not prove a permanent false negative or the Conductor cause. The [shared loop reproducer](bidirectional-loop-boundary-normality-loss-20261106.md) misses a feasible exact T observation in both Current and B. It shows a separate shared coverage defect.

The first required fact lost on the missing Conductor paths is still not identified. Equal returned lists on structurally matching inputs do not resolve other effects of prefix removal or packet representation. P0 remains open. No analyzer fix is proposed or applied by this report.
