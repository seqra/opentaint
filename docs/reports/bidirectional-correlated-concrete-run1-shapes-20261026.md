# Fresh run-1 shape and coverage comparison

Latest reached/completed/accepted iteration for every available census: **run-1 / run-1 / run-1**. These are separate joined diagnostics, not timed performance runs. State: **VALIDATED_FOUR_PROJECT_BEFORE_AFTER**; 4/4 projects have both source-bound censuses. [Complete machine evidence](bidirectional-correlated-concrete-run1-shapes-20261026.json) records all shape keys, both owners, hashes, controls and 564 checks.

**Before:** `583a58063ab67ad18b8664d45badee065e68fd85`, core `e3ede1a36d3b04d79a23cc93285f385ecd968dbf`, `baseline-any-alias-guard-v1`: own ANY-only runtime normalizer and original alias-effect guard. **After:** `fcfe2e90558665d813bd74207832d4ae3fc83aec`, core `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`, `correlated-star-any-v1`: selected STAR+ANY replacement without the alias exception. These are deliberately different predicates. Each column reports its own policy, not a hypothetical reclassification of the other runtime.

Each capture follows a COMPLETE forward limit-1 engine, joined/frozen runners, accepted report and completed persistence/handoff barrier. Models, test revision, heap/timeout, Java17, FULL mode, enabled statics and default aliases are checked. The five old-policy controls and seven final-policy controls pass; source/read-only binding is recorded. No project/JVM was started by this report.

## Capture status

| Project | Before command / SARIF | After command / SARIF | Census progress |
|---|---|---|---|
| thingsboard | HARD_TIMEOUT / unavailable | OK / available | run-1 complete/accepted |
| conductor | OK / available | OK / available | run-1 complete/accepted |
| Stirling-PDF | OK / available | OK / available | run-1 complete/accepted |
| OWASP | OK / available | OK / available | run-1 complete/accepted |

Thingsboard baseline ends HARD_TIMEOUT after its completed run-1 census and accepted report. It has no SARIF export. The census is valid; no finding count of zero or successful outer completion is inferred. A strict outer all-OK queue gate can fail independently of census validity. Do not restart this measured execution.

## Retained output memberships and coverage

| Project | Owner | Before TAINT | After TAINT | Before protected | After protected | Before protection-only | After protection-only | Before other | After other |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| thingsboard | raw | 2,081,189 | 1,800,397 | 943,790 | 1,737,136 | 130,921 | 901,285 | 1,950,268 | 899,112 |
| thingsboard | selected | 2,081,189 | 1,800,397 | 943,791 | 1,737,136 | 130,921 | 901,285 | 1,950,268 | 899,112 |
| conductor | raw | 20,236 | 16,750 | 20 | 22 | 0 | 1 | 20,236 | 16,749 |
| conductor | selected | 20,236 | 16,750 | 20 | 22 | 0 | 1 | 20,236 | 16,749 |
| Stirling-PDF | raw | 24,774 | 24,479 | 2,249 | 2,273 | 15 | 26 | 24,759 | 24,453 |
| Stirling-PDF | selected | 24,774 | 24,479 | 2,249 | 2,273 | 15 | 26 | 24,759 | 24,453 |
| OWASP | raw | 111,133 | 111,025 | 413 | 460 | 0 | 8 | 111,133 | 111,017 |
| OWASP | selected | 111,133 | 111,025 | 413 | 460 | 0 | 8 | 111,133 | 111,017 |

Every available owner has **0 removable-now**; protection-only + other equals its TAINT total. Every retained TAINT membership is DEMAND. No retained nonempty run-1 E, static→static shape, or unexplained normalizer mismatch is recorded. Raw and selected are never added. The baseline Thingsboard selected owner has one more protected membership than raw; both have the same total and coverage partition. Exact full shape/flag differences remain in JSON.

| Project | Before raw protected share | After raw protected share | Before protection-only share | After protection-only share | Before FLOW | After FLOW |
|---|---:|---:|---:|---:|---:|---:|
| thingsboard | 45.35% | 96.49% | 6.29% | 50.06% | 246,970 | 226,209 |
| conductor | 0.10% | 0.13% | 0.00% | 0.01% | 36,815 | 36,751 |
| Stirling-PDF | 9.08% | 9.29% | 0.06% | 0.11% | 4,876 | 4,876 |
| OWASP | 0.37% | 0.41% | 0.00% | 0.01% | 11,235 | 11,235 |

## Removal events

| Project | Owner | Before covered-offer membership events | After covered-offer membership events | Before stored compaction membership events | After stored compaction membership events |
|---|---|---:|---:|---:|---:|
| thingsboard | raw | 5,802,160 | 7,327,506 | 2,473 | 102 |
| thingsboard | selected | 0 | 0 | 2,473 | 102 |
| conductor | raw | 21,207 | 28,733 | 35 | 0 |
| conductor | selected | 0 | 0 | 35 | 0 |
| Stirling-PDF | raw | 188 | 788 | 0 | 0 |
| Stirling-PDF | selected | 0 | 0 | 0 | 0 |
| OWASP | raw | 44 | 786 | 0 | 0 |
| OWASP | selected | 0 | 0 | 0 | 0 |

These count removed output-path/tail/layer/atom memberships at offers or stored compaction events. Repeated offers count repeatedly. They are not distinct removed edges and cannot be subtracted from retained totals to reconstruct a fact history.

## Complete tail-pair histograms

The following table includes every observed concrete input→output tail pair. Raw and selected tail-pair totals agree in these captures; the JSON retains both owners and every finer base/layer/flag/depth shape key. `ANY_TAINT` is the existing must tail; EXACT-only tree canonical headers do not change an EXACT leaf into must.

| Project | Input→output tail | Before raw | After raw |
|---|---|---:|---:|
| thingsboard | `EXACT->ANY` | 45,240 | 50,468 |
| thingsboard | `EXACT->ANY_TAINT` | 10,666 | 10,839 |
| thingsboard | `EXACT->EXACT` | 14,606 | 14,977 |
| thingsboard | `STAR->ANY` | 2,009,184 | 1,722,623 |
| thingsboard | `STAR->EXACT` | 1,493 | 1,460 |
| thingsboard | `STAR->STAR` | 0 | 30 |
| conductor | `EXACT->ANY` | 9,785 | 9,422 |
| conductor | `EXACT->ANY_TAINT` | 1,275 | 1,279 |
| conductor | `EXACT->EXACT` | 5,300 | 5,398 |
| conductor | `STAR->ANY` | 3,239 | 6 |
| conductor | `STAR->EXACT` | 637 | 637 |
| conductor | `STAR->STAR` | 0 | 8 |
| Stirling-PDF | `EXACT->ANY` | 1,252 | 1,235 |
| Stirling-PDF | `EXACT->ANY_TAINT` | 3,017 | 3,017 |
| Stirling-PDF | `EXACT->EXACT` | 18,805 | 18,816 |
| Stirling-PDF | `STAR->ANY` | 1,574 | 1,213 |
| Stirling-PDF | `STAR->EXACT` | 126 | 126 |
| Stirling-PDF | `STAR->STAR` | 0 | 72 |
| OWASP | `EXACT->ANY` | 1,700 | 1,534 |
| OWASP | `EXACT->ANY_TAINT` | 107 | 107 |
| OWASP | `EXACT->EXACT` | 108,551 | 109,041 |
| OWASP | `STAR->ANY` | 608 | 77 |
| OWASP | `STAR->EXACT` | 167 | 167 |
| OWASP | `STAR->STAR` | 0 | 99 |

## All primary other-reason counts

Primary reasons sum exactly to the corresponding other partition. Their priority and predicates belong to each runtime. Secondary failures overlap and are retained separately in JSON. In particular, old ALIAS_EFFECT_CLASS is tested before candidate geometry: its old count does not prove that the same rows were covered in the new run. A dash means the classifier name is not defined by that version; a numeric zero means no retained membership receives that defined primary reason.

| Project | Exact primary reason | Before own policy | After own policy |
|---|---|---:|---:|
| thingsboard | `ALIAS_EFFECT_CLASS` | 702,038 | — |
| thingsboard | `CROSS_ATOM` | 809,230 | 817,618 |
| thingsboard | `MARK_EXCLUDED` | 4,950 | 3,934 |
| thingsboard | `NO_ANNOTATED_ANY_PREFIX` | 151,922 | 0 |
| thingsboard | `NO_FLOW_COUNTERPART` | 119,081 | 54 |
| thingsboard | `OUTPUT_BASE_MISMATCH` | 67,779 | 108 |
| thingsboard | `OUTPUT_TAIL_MISMATCH` | 23,627 | 18 |
| thingsboard | `UNSUPPORTED_INITIAL` | 27,410 | 33,195 |
| thingsboard | `UNSUPPORTED_OUTPUT` | — | 1,096 |
| thingsboard | `UNSUPPORTED_OUTPUT_TAIL` | 1,129 | — |
| thingsboard | `ZERO_INITIAL` | 43,102 | 43,089 |
| conductor | `ALIAS_EFFECT_CLASS` | 2,492 | — |
| conductor | `CROSS_ATOM` | 15 | 15 |
| conductor | `MARK_EXCLUDED` | 6 | 13 |
| conductor | `NO_ANNOTATED_ANY_PREFIX` | 680 | 0 |
| conductor | `OUTPUT_TAIL_MISMATCH` | 61 | 0 |
| conductor | `UNSUPPORTED_INITIAL` | 10,721 | 10,679 |
| conductor | `UNSUPPORTED_OUTPUT` | — | 622 |
| conductor | `UNSUPPORTED_OUTPUT_TAIL` | 622 | — |
| conductor | `ZERO_INITIAL` | 5,639 | 5,420 |
| Stirling-PDF | `ALIAS_EFFECT_CLASS` | 294 | — |
| Stirling-PDF | `CROSS_ATOM` | 113 | 113 |
| Stirling-PDF | `MARK_EXCLUDED` | 1,193 | 1,254 |
| Stirling-PDF | `NO_ANNOTATED_ANY_PREFIX` | 8 | 0 |
| Stirling-PDF | `OUTPUT_TAIL_MISMATCH` | 59 | 0 |
| Stirling-PDF | `UNSUPPORTED_INITIAL` | 2,137 | 2,139 |
| Stirling-PDF | `UNSUPPORTED_OUTPUT` | — | 18 |
| Stirling-PDF | `UNSUPPORTED_OUTPUT_TAIL` | 18 | — |
| Stirling-PDF | `ZERO_INITIAL` | 20,937 | 20,929 |
| OWASP | `ALIAS_EFFECT_CLASS` | 371 | — |
| OWASP | `CROSS_ATOM` | 86 | 86 |
| OWASP | `MARK_EXCLUDED` | 28 | 154 |
| OWASP | `NO_ANNOTATED_ANY_PREFIX` | 52 | 0 |
| OWASP | `OUTPUT_TAIL_MISMATCH` | 143 | 0 |
| OWASP | `UNSUPPORTED_INITIAL` | 16,919 | 17,241 |
| OWASP | `UNSUPPORTED_OUTPUT` | — | 95 |
| OWASP | `UNSUPPORTED_OUTPUT_TAIL` | 95 | — |
| OWASP | `ZERO_INITIAL` | 93,439 | 93,441 |

The selected owner has the same primary-reason totals in these captures. Both full owner maps remain in JSON. Changes mix changed production geometry, propagation/admission, flags and changed classification gates. They are not a per-edge migration or an isolated causal attribution.

## Stored endpoint shapes and measured work

| Project | Endpoint bases | Before TAINT | After TAINT |
|---|---|---:|---:|
| thingsboard | `NS->NS` | 780,032 | 13,893 |
| thingsboard | `NS->S` | 882,429 | 1,640,454 |
| thingsboard | `S->NS` | 375,626 | 102,961 |
| thingsboard | `Z->NS` | 23,057 | 23,044 |
| thingsboard | `Z->S` | 20,045 | 20,045 |
| conductor | `NS->NS` | 5,468 | 2,289 |
| conductor | `NS->S` | 1,287 | 1,280 |
| conductor | `S->NS` | 7,842 | 7,761 |
| conductor | `Z->NS` | 3,424 | 3,205 |
| conductor | `Z->S` | 2,215 | 2,215 |
| Stirling-PDF | `NS->NS` | 554 | 279 |
| Stirling-PDF | `NS->S` | 36 | 26 |
| Stirling-PDF | `S->NS` | 3,247 | 3,245 |
| Stirling-PDF | `Z->NS` | 5,936 | 5,928 |
| Stirling-PDF | `Z->S` | 15,001 | 15,001 |
| OWASP | `NS->NS` | 17,398 | 17,286 |
| OWASP | `NS->S` | 296 | 298 |
| OWASP | `Z->NS` | 91,673 | 91,673 |
| OWASP | `Z->S` | 1,766 | 1,768 |

### Static versus nonstatic outputs, with protection

| Project | Owner | Output base | Before memberships | After memberships | Before protected | After protected |
|---|---|---|---:|---:|---:|---:|
| thingsboard | raw | static | 902,474 | 1,660,499 | 889,558 | 1,649,206 |
| thingsboard | raw | nonstatic | 1,178,715 | 139,898 | 54,232 | 87,930 |
| thingsboard | selected | static | 902,474 | 1,660,499 | 889,558 | 1,649,206 |
| thingsboard | selected | nonstatic | 1,178,715 | 139,898 | 54,233 | 87,930 |
| conductor | raw | static | 3,502 | 3,495 | 0 | 0 |
| conductor | raw | nonstatic | 16,734 | 13,255 | 20 | 22 |
| conductor | selected | static | 3,502 | 3,495 | 0 | 0 |
| conductor | selected | nonstatic | 16,734 | 13,255 | 20 | 22 |
| Stirling-PDF | raw | static | 15,037 | 15,027 | 19 | 19 |
| Stirling-PDF | raw | nonstatic | 9,737 | 9,452 | 2,230 | 2,254 |
| Stirling-PDF | selected | static | 15,037 | 15,027 | 19 | 19 |
| Stirling-PDF | selected | nonstatic | 9,737 | 9,452 | 2,230 | 2,254 |
| OWASP | raw | static | 2,062 | 2,066 | 44 | 44 |
| OWASP | raw | nonstatic | 109,071 | 108,959 | 369 | 416 |
| OWASP | selected | static | 2,062 | 2,066 | 44 | 44 |
| OWASP | selected | nonstatic | 109,071 | 108,959 | 369 | 416 |

**Thingsboard population mix matters.** Raw static outputs increase **902,474 → 1,660,499** (+758,025), while nonstatic outputs decrease **1,178,715 → 139,898** (−1,038,817). Static outputs already have 98.57% protection before and 99.32% after. Their share of all retained concrete outputs rises 43.36% → 92.23%. Thus the overall protected share mixes a large change in the retained output population with changes inside each category; it is not simply a count of newly added flag operations.

The old own-policy `ALIAS_EFFECT_CLASS` primary count is 702,038. Old same-base/same-path marked identity-class retention is part of that policy; the final checker has no such exception. Nonstatic→nonstatic outputs fall 780,032 → 13,893. This counterweights the net retained-membership reduction: static output population grows substantially. The counts do not match individual old/new edges or prove which producer/flag transition caused the shift. A static output is a summary endpoint, not evidence of intraprocedural static propagation.

| Project | Before physical method-edge dispatches | After physical method-edge dispatches | Before explicit handoff demand patterns | After explicit handoff demand patterns |
|---|---:|---:|---:|---:|
| thingsboard | 177,847,174 | 143,907,111 | 2,380,049 | 2,078,059 |
| conductor | 6,677,025 | 6,652,192 | 72,918 | 69,644 |
| Stirling-PDF | 5,343,031 | 5,569,881 | 36,774 | 36,468 |
| OWASP | 63,017,085 | 62,973,426 | 133,966 | 133,858 |

Both work totals use frozen actor arithmetic: physical dispatches = steps − packed mark credits + packed invocations. The baseline reads existing actor counters without a hot observer. This is an operation-count comparison, not an elapsed-time comparison or a pure static-work counter. Handoff totals count successful exact normalized explicit DemandPattern insertions after deduplication; implicit static completion remains a symbolic policy and is not added as a method×field product. Retained selected TAINT counts measure current marked publication state, not publication callbacks or the marked-only handoff split.

## Representative facts, full FLOW candidates and ANY origin

[The current 17-example report](../../../correlated-concrete-20261026/validation/final-run1-shapes/report.md) links actual code and complete fact/flag/owner records. Every matching-initial FLOW list is untruncated. The following files preserve all candidates; atom numbers are local to that capture.

* [PROTECTION_ONLY — getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_PROTECTION_ONLY-0.json)
* [PROTECTION_ONLY — getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_PROTECTION_ONLY-1.json)
* [UNSUPPORTED_INITIAL — checkActivateToken(java.lang.String) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_INITIAL-0.json)
* [UNSUPPORTED_INITIAL — checkResetToken(java.lang.String) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_INITIAL-1.json)
* [CROSS_ATOM — getAppleAppSiteAssociation() [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_CROSS_ATOM-0.json)
* [CROSS_ATOM — getAssetLinks() [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_CROSS_ATOM-1.json)
* [NO_FLOW_COUNTERPART — parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_NO_FLOW_COUNTERPART-0.json)
* [NO_FLOW_COUNTERPART — evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_NO_FLOW_COUNTERPART-1.json)
* [MARK_EXCLUDED — getActiveSessions(java.lang.String) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_MARK_EXCLUDED-0.json)
* [MARK_EXCLUDED — getAllSessions(java.lang.String) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_MARK_EXCLUDED-1.json)
* [OUTPUT_BASE_MISMATCH — parseValues(com.google.gson.JsonObject) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_BASE_MISMATCH-0.json)
* [OUTPUT_BASE_MISMATCH — parseProtoValues(com.google.gson.JsonObject) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_BASE_MISMATCH-1.json)
* [ZERO_INITIAL — redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_ZERO_INITIAL-0.json)
* [ZERO_INITIAL — checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_ZERO_INITIAL-1.json)
* [UNSUPPORTED_OUTPUT — logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_OUTPUT-0.json)
* [UNSUPPORTED_OUTPUT — saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_OUTPUT-1.json)
* [OUTPUT_TAIL_MISMATCH — getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]](../../../correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_TAIL_MISMATCH-0.json)

[Four actual AP replay controls](../../../correlated-concrete-20261026/validation/cassandra-regex-ap-replay/report.json) use fcfe operators and a corrected summary owner. They prove a source-valid regex-model field-cut mechanism: `arg0/*/FLOW → var17.Matcher.group.String.content/*/FLOW`, limit 1 cuts to `var17.Matcher.group/[any]/FLOW` DEMAND, then the group output maps to `ret/[any]/FLOW`. The supplied mark exclusions match the sample; their producer is not replayed. Protected concrete transport retains its flag through the same cut.

The owner/order controls also show that stored same-layer ANY FLOW can reject a later STAR FLOW, while marked STAR remains outside ANY-only same-tail replacement. Reversed order can retain both FLOW tails; a weak DEMAND FLOW cannot replace NORMAL TAINT. These are actual operator/admission controls, not proof of the historical offer order or first ANY producer for the captured `CassandraToSqlColumn.getColumnValue` row. The original snapshot has no per-edge history. [Source trace and explicit origin limit](../../../correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/report.json) remain part of the evidence.

The largest nonstatic→static aggregate is still a shape population; no exact producer/pair is invented. The before/after classification now uses fresh fixed-budget runs, rather than the older 16 GiB category report. All available partition, source/configuration, completion, read-only-control and invariant checks pass. No coverage rule was weakened to force removable-now to zero.

Evidence files outside the repository are relative links into the retained campaign directory. The [performance report](bidirectional-correlated-concrete-performance-20261026.md) separates timed results and these diagnostic captures.
