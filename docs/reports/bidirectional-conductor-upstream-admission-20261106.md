A real Conductor run-3 C2 query loses a stronger initializer on the workflow-definition source path. For the same complete NORMAL `arg0.workflowDefinition.MUST/Graal` input, Current returns a STAR/FLOW initializer; the proper-prefix-off control B also returns a MUST/FLOW initializer. B later uses that exact initial identity as the original premise of a ROOT-scope call to `createAndEvaluateWithLock`.

This proves a local admission precision difference and later use of the stronger initial. It does not yet prove that this difference causes either missing Conductor finding. P0 remains open; no analyzer fix is included.

| Diagnostic evidence | Current | Control B |
| --- | ---: | ---: |
| Reached / completed / accepted run | 4 / 3 / 3 | 4 / 3 / 3 |
| Complete recorded calls | 12,558 | 15,418 |
| Distinct structural admission queries | 5,518 | 6,507 recorded |
| Invalid event records | 0 | 0 |
| Observed whole-event DROP notices | 0 | 1, at the total-output cap |

Both commands stopped at native run-4 START. B reached the 128 Mi-character output cap at attempted sequence 15,419, with reason `TOTAL_OUTPUT_CHARS_CAP`. The positive witnesses below precede that drop. B's later inputs and apparent absences remain unknown. This is not a full-run quality, convergence, or performance result.

The [evidence JSON](data/bidirectional-conductor-upstream-admission-20261106.json) embeds three exact Current/B witness pairs, two exact ROOT consumer records, complete typed catalogs and native input DAGs, the decoder and extraction source, both manifests and runtime checks, source pins, and 37 source-route snippets. These selected pairs can be checked from the embedded records. Rechecking all 5,025 matched queries needs the full capture logs at their pinned paths. Full log files are hash-bound; they are not embedded.

The query key contains run, direction, field limit, mark mode, full callee method/context/entry key, and complete structural actual facts with layer, E, mx and protection. It omits caller P and callsite because `emitRestrictedInitials` does not take those arguments. Among 5,025 matching query keys, 181 have different returned sets. There are no within-variant query ambiguities. Twenty-one differences have actual TAINT DAGs that contain the Graal FULL atom. Structural equality does not stand in for a general denotational-equivalence test.

The main witness is `WorkflowExecutorOps#createAndEvaluate(WorkflowModel)`, in Empty context, forward run 3 at field limit 2. Current sequence 1,534 and B sequence 777 both come from `WorkflowExecutorOps#startWorkflow(StartWorkflowInput)`, physical call 9, stage 3, ROOT scope `(0,-1)`.

| Boundary | Complete result |
| --- | --- |
| Submitted in both | `arg0.<WorkflowModel.workflowDefinition:WorkflowDef>.MUST/Graal`, NORMAL |
| Current returned list | `wfDef.STAR/FLOW`, NORMAL; `wfDef.STAR/Graal`, DEMAND |
| B returned list | The same two entries, plus `wfDef.MUST/FLOW`, NORMAL |

Here `wfDef` abbreviates the full typed field above. The actual DAG has an empty root, one workflowDefinition edge, and a terminal leaf with `exact=[]`, `any=[Graal]`. The packet header is `ANY_TAINT`; E is empty and protection is null. Thus MUST support is present at the workflowDefinition coordinate, not inferred from the header alone. The full logical Graal source name is retained in the evidence.

B's additional initial has local ID 4784. At B sequence 1,403, a later call from `createAndEvaluate` to `createAndEvaluateWithLock` has original P equal to that ID and full MUST/FLOW pattern, with the same caller method/context/entry key and ROOT scope. The earlier returned ID and later premise ID belong to the same B JVM. The raw consumer is JSONL line 1,414. This proves that the initial identity is used as a call premise. It does not identify a unique delivery event, since another route may admit the same interned initial.

A second witness submits NORMAL FLOW at `arg0.workflowDefinition.tasks.STAR` to the same callee: Current sequence 1,772 and B sequence 932. Current returns only `wfDef.STAR/FLOW`, NORMAL. B also returns `wfDef.tasks.STAR/FLOW`, NORMAL, local ID 4856. B sequence 1,366 uses that exact stronger pattern and ID as original P in the ROOT call to `createAndEvaluateWithLock`; its raw consumer is JSONL line 1,377. Field descriptors retain `WorkflowModel.workflowDefinition:WorkflowDef` and `WorkflowDef.tasks:java.util.List` in full.

The third embedded witness is a getTasks four-argument query with the same submitted Graal packet. B adds `arg1.<WorkflowTask.taskDefinition:TaskDef>.ANY/FLOW`, DEMAND. No captured ROOT consumer association is asserted for that entry. The taskDefinition field is distinct from the WorkflowTask expression field.

The native policy explains how these results can differ. With an ANY demand at the root and an actual fact under workflowDefinition, `RestrictedInitialPolicy.emit` advances one field and emits STAR. With an ANY demand at the workflowDefinition coordinate and the actual MUST fact at that same coordinate, it can preserve MUST. This is a source-based explanation. The specific frozen B2 row that supplied the stronger emission was not captured in this run, so it is not reported as an observed B2 normalization transaction.

The source route continues through `createAndEvaluateWithLock`, Ops `decide`, Decider scheduling, TaskMapper, and an evaluator. SwitchTaskMapper passes WorkflowTask expression and task input to the evaluator. Python also places task-input map keys into its generated global declaration. These source checkpoints guide the interpretation; they are not an executed proof from the stronger initial to a final target. The current record establishes the first ROOT consumer above. A required-fact chain to either missing finding remains unresolved.

The earlier [getTasks-only report](bidirectional-conductor-call-admission-20261106.md) found equal returned lists for its 1,218 matching full caller/P/call keys. The wider method scope and pure query key here answer a different question. The earlier negative result remains limited to its recorded full-key matches.

The [uniform-MUST reproducer](bidirectional-uniform-prefix-refinement-reproducer-20261106.md) matches this operation directly. Current admits `p.f.STAR/FLOW`; reading `g` yields ANY in DEMAND. B admits `p.f.MUST/FLOW`; reading `g` preserves MUST in NORMAL and reaches the normal observation. Current first reports in F5 and B in F3; both naturally complete F5 with one finding. This is a refinement delay, not a permanent false negative.

The earlier [prefix reproducer](bidirectional-canonical-prefix-refinement-reproducer-20261106.md) also proves a bounded F3-to-F5 delay. The [shared loop reproducer](bidirectional-loop-boundary-normality-loss-20261106.md) shows a separate coverage defect in both variants. The new Conductor witness confirms an operational C2 precision difference on a real source route. Neither the real witness nor these small tests yet prove the cause of the final missing Conductor findings.
