# Run-1 processing work before and after correlated concrete initials

The fresh run-1 diagnostic compares 583a58063 with fcfe2e905 at the same four fixed configurations. All four engines completed and accepted run-1. Baseline Thingsboard has an outer HARD_TIMEOUT; its census is valid but its primary SARIF export is unavailable.

| Project | Actors before → after | Scalar before → after | Packed calls before → after | Packed credits before → after | Physical before → after | Physical change |
|---|---:|---:|---:|---:|---:|---:|
| thingsboard | 73,669 → 73,669 | 173,959,542 → 140,288,224 | 3,887,632 → 3,618,887 | 7,831,446 → 6,789,565 | 177,847,174 → 143,907,111 | -19.08% |
| conductor | 17,465 → 17,465 | 6,635,946 → 6,609,819 | 41,079 → 42,373 | 43,246 → 44,206 | 6,677,025 → 6,652,192 | -0.37% |
| Stirling-PDF | 7,258 → 7,258 | 5,336,767 → 5,562,833 | 6,264 → 7,048 | 8,133 → 9,002 | 5,343,031 → 5,569,881 | +4.25% |
| OWASP | 12,083 → 12,083 | 63,013,546 → 62,969,407 | 3,539 → 4,019 | 3,840 → 4,318 | 63,017,085 → 62,973,426 | -0.07% |

Scheduling and batching can change observed counts between invocations. This is one source-bound diagnostic per lane, with different instrumentation, not a statistical timing estimate.

Physical method-edge invocations = actor.steps − packed mark credits + packed calls. This counts scalar processing and certified packed processing once. It excludes resume callbacks and does not count inner trie/rule/call operations. Scalar payload width can change.

| Project | Fresh timed R1 before → after | Engine time change | Physical work change |
|---|---:|---:|---:|
| thingsboard | 632.912s → 592.191s | -6.43% | -19.08% |
| conductor | 23.583s → 20.501s | -13.07% | -0.37% |
| Stirling-PDF | 42.851s → 33.255s | -22.39% | +4.25% |
| OWASP | 174.991s → 226.948s | +29.69% | -0.07% |

OWASP physical method-edge work changed by -43,659 (-0.07%), while the separate fresh timed run-1 increased by 51.957s (+29.69%). This directly measures the outer operation-volume change. It does not assign the wall-time difference to that volume: the runs have different diagnostic instrumentation, and inner work, payload width, GC/JIT and CPU availability are not equalized by these counters.

OWASP has no aggregate outer-operation explosion in these captures. Its 40 common top method keys include 38 unchanged keys and 2 decreases; that bounded set covers only 7.67% of total work. Stored raw TAINT is also almost flat (111,133→111,025), with flags 413→460. These endpoint counts do not measure live/intermediate payload or protection work.

Actual packed-credit compression is negligible on OWASP: 301 fewer physical calls than step credits before and 299 after. That is not enough to explain the timing change. Current pure-untouched scalar processing is 28,618,850 events (45.45% of all physical method-edge invocations); baseline has no paired counter and no skip proof follows from this classification.

Exact method comparisons use the intersection of the two bounded top 40 physical/credit lists. Missing entries are censored; the JSON includes thresholds/bounds and full signatures/context. The following are measured common-key changes, not a complete decomposition.

thingsboard: 36 exact common observed method keys cover 25.10% of baseline and 26.08% of current physical invocations.
- `org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#processUplinkMsg(org.thingsboard.server.gen.edge.v1.UplinkMsg) [{}]`: 16,992,464 → 14,676,377 (-2,316,087).
- `org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.server.dao.resource.BaseResourceService$processResources_fc592dee$jIR_lambda$18/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]`: 1,445,685 → 989,330 (-456,355).
- `org.thingsboard.server.transport.coap.client.DefaultCoapClientContext$CoapSessionListener#onToDeviceRpcRequest(java.util.UUID, org.thingsboard.server.gen.transport.TransportProtos$ToDeviceRpcRequestMsg) [{}]`: 633,465 → 638,181 (+4,716).

conductor: 39 exact common observed method keys cover 50.44% of baseline and 50.45% of current physical invocations.
- `com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF(java.lang.String, java.lang.String, java.util.Map, java.util.Map, java.lang.String) [{}]`: 142,233 → 131,173 (-11,060).
- `com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{this is com.netflix.conductor.grpc.ProtoMapper}]`: 47,672 → 39,204 (-8,468).
- `com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{}]`: 38,695 → 48,084 (+9,389).
- `com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]`: 204,245 → 209,410 (+5,165).

Stirling-PDF: 38 exact common observed method keys cover 60.14% of baseline and 62.67% of current physical invocations.
- `stirling.software.SPDF.service.PdfJsonConversionService#regeneratePageContent(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDPage, java.util.List, java.util.List, java.util.Map, java.util.List, int, org.apache.pdfbox.pdmodel.PDPageContentStream$AppendMode) [{arg(2) == java.util.ArrayList} & {arg(3) == java.util.ArrayList} & {arg(5) == java.util.ArrayList}]`: 286,392 → 267,214 (-19,178).
- `stirling.software.SPDF.service.PdfJsonConversionService#exportUpdatedPages(java.lang.String, stirling.software.SPDF.model.json.PdfJsonDocument) [{}]`: 45,999 → 43,463 (-2,536).
- `stirling.software.SPDF.controller.api.pipeline.PipelineProcessor#runPipelineAgainstFiles(java.util.List, stirling.software.SPDF.model.PipelineConfig) [{}]`: 718,061 → 1,013,971 (+295,910).
- `stirling.software.SPDF.service.PdfJsonConversionService#convertPdfToJson(org.springframework.web.multipart.MultipartFile, java.util.function.Consumer, boolean) [{}]`: 37,502 → 40,441 (+2,939).

OWASP: 40 exact common observed method keys cover 7.67% of baseline and 7.67% of current physical invocations.
- `org.owasp.benchmark.testcode.BenchmarkTest00578#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]`: 136,438 → 135,382 (-1,056).
- `org.owasp.benchmark.testcode.BenchmarkTest01452#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]`: 117,672 → 116,784 (-888).

Timed cohort latest reached/completed/accepted: thingsboard run-2/run-1/run-1 → run-2/run-1/run-1; conductor run-2/run-1/run-1 → run-2/run-1/run-1; Stirling-PDF run-2/run-1/run-1 → run-2/run-1/run-1; OWASP run-10/run-9/run-9 → run-9/run-8/run-7.

Current-only nested work is not filled with baseline zeros. Pure untouched scalar counts, TAINT scalar counts and resume events are included in JSON with baseline state BASELINE_NOT_INSTRUMENTED. They describe measured candidates; no skip soundness is asserted.

| Project | Raw stored TAINT before → after | Raw protection annotations before → after | Retained only by protection, own policy, before → after |
|---|---:|---:|---:|
| thingsboard | 2,081,189 → 1,800,397 | 943,790 → 1,737,136 | 130,921 → 901,285 |
| conductor | 20,236 → 16,750 | 20 → 22 | 0 → 1 |
| Stirling-PDF | 24,774 → 24,479 | 2,249 → 2,273 | 15 → 26 |
| OWASP | 111,133 → 111,025 | 413 → 460 | 0 → 8 |

The outer baseline queue wrapper reports FAILED because it required status OK for every leaf; the actual child cohort is CLOSED with four valid accepted run-1 captures. The Thingsboard HARD_TIMEOUT and unavailable export are preserved. This report validates the captures without relabeling the outer outcome or rerunning a project.

Coverage and protection counters count logical output-path×mark memberships, not physical rows or operations. Their predicate changes between old ANY/alias-guard and current STAR/ANY normalization, so they are not a common-policy causal decomposition.

The JSON binds both campaigns, every project completion record, source/core/patch and model/config/catalog guards, fresh control receipts, summaries, logs and census files by hash. Diagnostic work and the separately linked timed measurements must remain distinct. Latest reached/completed/accepted for every diagnostic comparison: run-1/run-1/run-1.

Evidence files outside the repository are relative links into the retained campaign directory. The [performance report](bidirectional-correlated-concrete-performance-20261026.md) separates timed results and these diagnostic captures.
