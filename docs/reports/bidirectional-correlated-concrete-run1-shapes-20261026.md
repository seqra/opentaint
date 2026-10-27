# Fresh run-1 shape and coverage comparison

This report is self-contained. It includes the complete comparison JSON, all 17 original examples, their actual code, the source/model replay, its four test results, and census control receipts. Expand the sections below for the full data. Original paths and hashes are source labels, not required external links.

Latest reached/completed/accepted iteration for every available census: **run-1 / run-1 / run-1**. These are separate joined diagnostics, not timed performance runs. State: **VALIDATED_FOUR_PROJECT_BEFORE_AFTER**; 4/4 projects have both source-bound censuses. [Complete machine evidence, embedded below](#inline-comparison-data) records all shape keys, both owners, hashes, controls and 564 checks.

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

All 17 complete records are [embedded below](#inline-examples), with [actual method bodies](#inline-example-source), full initial/output headers, all matching FLOW candidates and complete protection masks. No candidate list is truncated. Atom numbers are local to the captured run-1 invocation.

* [PROTECTION_ONLY — getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]](#example-01)
* [PROTECTION_ONLY — getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]](#example-02)
* [UNSUPPORTED_INITIAL — checkActivateToken(java.lang.String) [{}]](#example-03)
* [UNSUPPORTED_INITIAL — checkResetToken(java.lang.String) [{}]](#example-04)
* [CROSS_ATOM — getAppleAppSiteAssociation() [{}]](#example-05)
* [CROSS_ATOM — getAssetLinks() [{}]](#example-06)
* [NO_FLOW_COUNTERPART — parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]](#example-07)
* [NO_FLOW_COUNTERPART — evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]](#example-08)
* [MARK_EXCLUDED — getActiveSessions(java.lang.String) [{}]](#example-09)
* [MARK_EXCLUDED — getAllSessions(java.lang.String) [{}]](#example-10)
* [OUTPUT_BASE_MISMATCH — parseValues(com.google.gson.JsonObject) [{}]](#example-11)
* [OUTPUT_BASE_MISMATCH — parseProtoValues(com.google.gson.JsonObject) [{}]](#example-12)
* [ZERO_INITIAL — redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]](#example-13)
* [ZERO_INITIAL — checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]](#example-14)
* [UNSUPPORTED_OUTPUT — logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]](#example-15)
* [UNSUPPORTED_OUTPUT — saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]](#example-16)
* [OUTPUT_TAIL_MISMATCH — getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]](#example-17)

[Four actual AP replay controls, with source and results below](#inline-ap-replay) use fcfe operators and a corrected summary owner. They prove a source-valid regex-model field-cut mechanism: `arg0/*/FLOW → var17.Matcher.group.String.content/*/FLOW`, limit 1 cuts to `var17.Matcher.group/[any]/FLOW` DEMAND, then the group output maps to `ret/[any]/FLOW`. The supplied mark exclusions match the sample; their producer is not replayed. Protected concrete transport retains its flag through the same cut.

The owner/order controls also show that stored same-layer ANY FLOW can reject a later STAR FLOW, while marked STAR remains outside ANY-only same-tail replacement. Reversed order can retain both FLOW tails; a weak DEMAND FLOW cannot replace NORMAL TAINT. These are actual operator/admission controls, not proof of the historical offer order or first ANY producer for the captured `CassandraToSqlColumn.getColumnValue` row. The original snapshot has no per-edge history. [Source trace and explicit origin limit, embedded below](#inline-source-trace) remain part of the evidence.

The largest nonstatic→static aggregate is still a shape population; no exact producer/pair is invented. The before/after classification now uses fresh fixed-budget runs, rather than the older 16 GiB category report. All available partition, source/configuration, completion, read-only-control and invariant checks pass. No coverage rule was weakened to force removable-now to zero.

This file contains the full evidence used for its tables and examples. Paths inside the records are provenance labels. You do not need those directories to read the records or repeat the table arithmetic. Raw heaps and profiles are outside this shape report. The separate performance report keeps timed results separate.

## Inline evidence

The before runtime is `583a58063ab67ad18b8664d45badee065e68fd85`; the after runtime is `fcfe2e90558665d813bd74207832d4ae3fc83aec`. Every census below reaches, completes and accepts run-1. Baseline Thingsboard has an outer HARD_TIMEOUT and no SARIF export. Its valid census does not change that outcome.

The dominant nonstatic-to-static matrix still has no captured exact producer/pair. The 17 examples cover measured rejection categories. They do not establish the cause of the additional protected matrix. The separate ANY replay does not establish a historical first producer.

- [Complete comparison and all shape/reason histograms](#inline-comparison-data)
- [Current support counts and work partitions](#inline-current-support-data)
- [All 17 full example records](#inline-examples)
- [Actual source for all 17 methods](#inline-example-source)
- [Additional recorded source excerpts](#inline-recorded-source-excerpts)
- [Source/model trace and bytecode](#inline-source-trace)
- [Actual AP replay and controls](#inline-ap-replay)
- [Recorded commands and census controls](#inline-capture-controls)

For each owner, the three coverage counts sum to retained TAINT. The complete TAINT shape histogram gives the same total. Primary other-reason counts sum to the other partition. Protected annotations are a separate count. A share is count divided by that owner's total. Physical dispatches equal actor steps minus packed mark credits plus packed invocations. Do not add raw and selected, or mix physical rows with logical memberships.

<a id="inline-comparison-data"></a>
### Complete before/after comparison JSON

<details>
<summary>Full record; SHA-256 b4c9e1a096f997e8b7875c7d884c40ea9ca76c2b3e31220141190eef5b116a57</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/opentaint-w3/docs/reports/bidirectional-correlated-concrete-run1-shapes-20261026.json`.

```json
{
  "state": "VALIDATED_FOUR_PROJECT_BEFORE_AFTER",
  "generated_utc": "2026-10-27T00:15:21.680181+00:00",
  "latest_reached": "run-1",
  "latest_completed": "run-1",
  "latest_accepted_forward": "run-1",
  "projects_with_both_valid_censuses": 4,
  "sources": {
    "before": {
      "directory": "baseline-shape-probe-results",
      "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
      "core": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
      "checker": "baseline-any-alias-guard-v1",
      "policy": "Old runtime ANY-only normalizer, canonical run-1 FULL/Empty-E initial cell, original alias-effect identity guard; old primary-reason order."
    },
    "after": {
      "directory": "shape-probe-results",
      "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
      "core": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
      "checker": "correlated-star-any-v1",
      "policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order."
    }
  },
  "projects": {
    "thingsboard": {
      "before": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "baseline-shape-probe-results",
          "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
          "core": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
          "checker": "baseline-any-alias-guard-v1",
          "policy": "Old runtime ANY-only normalizer, canonical run-1 FULL/Empty-E initial cell, original alias-effect identity guard; old primary-reason order."
        },
        "input": {
          "path": "baseline-shape-probe-results/thingsboard/bidi/shapes/run1-shapes.json",
          "sha256": "f2d5d5d96fc8d76c7305d4f5e79e77a82ef7c0286b3d303a25b8c25c9fb835b0"
        },
        "manifest": {
          "path": "baseline-shape-probe-results/thingsboard/bidi/manifest.json",
          "sha256": "44d6e6de74b0e73607df8db7c049e329f3114fa2a5d1cc66b54a9f52f333ecec"
        },
        "summary": {
          "path": "baseline-shape-probe-results/thingsboard/bidi/summary.json",
          "sha256": "9d4429ca5f5589218a60898eef2841d9a1846f818b39f32117bf806bac48d118"
        },
        "command_status": "HARD_TIMEOUT",
        "SARIF_available": false,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "23:46:37.794 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=12m 54.441923249s markMode=FULL",
          "end_line": "23:58:40.655 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=12m 2.861678039s",
          "barrier_line": "23:59:23.601 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=42.891509624s iterationTime=12m 45.808016954s"
        },
        "accepted_forward_frontier": "23:59:22.561 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 38017, demand edges 2380049 in 73599 method keys, left 44, record crossings 0, DEMAND 102187, CONFIRMED 0, seeds 154881, zero only 35652 (258412 edges)",
        "explicit_handoff_demand_patterns": 2380049,
        "demand_method_keys": 73599,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "583 runtime normalizer unchanged: ANY-only, same-base identity arms retained by alias-effect guard",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
          "memory": "12g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
        "owners": {
          "raw": {
            "FLOW_memberships": 246970,
            "TAINT_memberships": 2081189,
            "protected_memberships": 943790,
            "protected_share": 0.45348596403305996,
            "coverage": {
              "removable_now": 0,
              "protection_only": 130921,
              "other": 1950268
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.06290682874068622,
              "other": 0.9370931712593138
            },
            "removal_events": {
              "covered_offer_rejections": 5802160,
              "stored_compaction_memberships": 2473
            },
            "primary_other_reasons": {
              "NO_ANNOTATED_ANY_PREFIX": 151922,
              "ALIAS_EFFECT_CLASS": 702038,
              "OUTPUT_TAIL_MISMATCH": 23627,
              "OUTPUT_BASE_MISMATCH": 67779,
              "NO_FLOW_COUNTERPART": 119081,
              "UNSUPPORTED_INITIAL": 27410,
              "CROSS_ATOM": 809230,
              "MARK_EXCLUDED": 4950,
              "ZERO_INITIAL": 43102,
              "UNSUPPORTED_OUTPUT_TAIL": 1129
            },
            "secondary_failures_nonadditive": {
              "NO_ANNOTATED_ANY_PREFIX": 220717,
              "OUTPUT_TAIL_MISMATCH": 69926,
              "OUTPUT_BASE_MISMATCH": 196345,
              "ALIAS_EFFECT_CLASS": 702038,
              "NO_FLOW_COUNTERPART": 119081,
              "UNSUPPORTED_INITIAL": 27410,
              "CROSS_ATOM": 809230,
              "MARK_EXCLUDED": 17493,
              "ZERO_INITIAL": 43102,
              "UNSUPPORTED_OUTPUT_TAIL": 1129
            },
            "TAINT_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 760869,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 202702,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 36924,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 6538,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 387,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=1": 88866,
              "STAR->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 778176,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 98167,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1514,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 1534,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 1548,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 17064,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2772,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 15492,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10743,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10468,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 14,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 591,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 7652,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 815,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 11241,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 416,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=0": 24,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 360,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 756,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1028,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 798,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1673,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 55,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 9,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 2456,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2120,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 19,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1764,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 210,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 235,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 29,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 72,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 45,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 16,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 11112,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 72,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 144,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 576,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 72,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 109,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=1": 4,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1656,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 360,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 270,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 252,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 1
            },
            "FLOW_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|depth=1": 30610,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 5885,
              "STAR->STAR|NS->NS|NORMAL|depth=0": 69198,
              "STAR->ANY|S->NS|DEMAND|depth=1": 51118,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 11779,
              "STAR->ANY|S->NS|DEMAND|depth=0": 4741,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 7924,
              "STAR->ANY|NS->S|DEMAND|depth=2": 65330,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 384,
              "STAR->STAR|NS->S|DEMAND|depth=2": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 45240,
                "EXACT->ANY_TAINT": 10666,
                "EXACT->EXACT": 14606,
                "STAR->ANY": 2009184,
                "STAR->EXACT": 1493
              },
              "base_pairs": {
                "NS->NS": 780032,
                "NS->S": 882429,
                "S->NS": 375626,
                "Z->NS": 23057,
                "Z->S": 20045
              },
              "layers": {
                "DEMAND": 2081189
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 872411,
                "diagonal": 1208778
              },
              "flags": {
                "false": 1137399,
                "true": 943790
              },
              "output_depth": {
                "0": 994057,
                "1": 185414,
                "2": 901718
              },
              "output_bases": {
                "NS": 1178715,
                "S": 902474
              },
              "protected_output_bases": {
                "NS": 54232,
                "S": 889558
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 159723,
                "STAR->STAR": 87247
              },
              "base_pairs": {
                "NS->NS": 125780,
                "NS->S": 65331,
                "S->NS": 55859
              },
              "layers": {
                "DEMAND": 165993,
                "NORMAL": 80977
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 87748,
                "1": 93891,
                "2": 65331
              },
              "output_bases": {
                "NS": 181639,
                "S": 65331
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=2)": 1928808,
              "GroupId(value=8)": 58888,
              "GroupId(value=7)": 10243,
              "GroupId(value=11)": 10276,
              "GroupId(value=5)": 10596,
              "GroupId(value=6)": 10242,
              "GroupId(value=4)": 11041,
              "GroupId(value=9)": 10244,
              "GroupId(value=10)": 10305,
              "GroupId(value=12)": 10257,
              "GroupId(value=13)": 10288,
              "GroupId(value=0)": 1
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 80711,
              "diagonal_mark_rows": 1126203,
              "scalar_concrete_rows": 18882
            },
            "protection_tree_counts": {
              "none": 1073978,
              "full_structural_only": 67686,
              "full_identity": 2986,
              "partial": 435
            },
            "protection_tree_memberships": {
              "none": 1130626,
              "full_structural_only": 928956,
              "full_identity": 3020,
              "partial": 18587
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.thingsboard.server.controller.TelemetryController#deleteAttributes(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.AttributeScope, java.util.List) [{}]",
                2027
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{}]",
                1955
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.ArrayList} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1955
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.HashSet} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1955
              ],
              [
                "org.thingsboard.server.controller.TelemetryController#lambda$saveTelemetry$8(long, org.thingsboard.server.service.security.model.SecurityUser, java.util.List, org.springframework.web.context.request.async.DeferredResult, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId) [{}]",
                1890
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#lambda$onDeviceClaimJson$12(java.util.Map$Entry, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean, org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext) [{}]",
                1854
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#processClaimDeviceMsg(org.thingsboard.server.transport.mqtt.session.MqttDeviceAwareSessionContext, com.google.gson.JsonElement, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean) [{arg(0) is org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext}]",
                1854
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processArgumentValuesUpdate(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback, java.util.Map, java.util.UUID, org.thingsboard.server.common.data.msg.TbMsgType) [{}]",
                1711
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processArgumentValuesUpdate(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback, java.util.Map, java.util.UUID, org.thingsboard.server.common.data.msg.TbMsgType) [{arg(1) == java.util.HashSet} & {arg(2) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1711
              ],
              [
                "org.thingsboard.server.transport.lwm2m.server.ota.DefaultLwM2MOtaUpdateService#onTargetSoftwareUpdate(org.thingsboard.server.transport.lwm2m.server.client.LwM2mClient, java.lang.String, java.lang.String, java.util.Optional, java.util.Optional) [{}]",
                1668
              ],
              [
                "org.thingsboard.server.service.cf.AbstractCalculatedFieldProcessingService#sendMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.msg.queue.TbCallback, org.thingsboard.server.common.msg.TbMsg) [{}]",
                1653
              ]
            ],
            "top_fields": [
              [
                "NS:",
                994057
              ],
              [
                "S:<static>(org.thingsboard.server.common.data.id.TenantId)/TenantId#tenants",
                66906
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.event.EventService",
                64341
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbCallback)/TbCallback#EMPTY",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.edge.EdgeService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.rpc.TbCoreDeviceRpcService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.cluster.TbClusterService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.nosql.CassandraBufferedRateWriteExecutor",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.timeseries.TimeseriesService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.apiusage.TbApiUsageStateService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.ruleengine.RuleEngineCallService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.session.DeviceSessionCacheService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.transport.TbCoreToTransportService",
                64049
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbMsgCallback)/TbMsgCallback#EMPTY",
                64049
              ],
              [
                "S:<static>(org.thingsboard.rule.engine.math.TbMathNode)/TbMathNode#locks",
                64049
              ],
              [
                "NS:DefaultTransportService$StatsCallback#callback",
                7140
              ],
              [
                "NS:MultipleTbQueueCallbackWrapper#callback",
                6956
              ],
              [
                "NS:DefaultCalculatedFieldQueueService$FutureCallbackWrapper#callback",
                6843
              ],
              [
                "NS:ValidationCallback#action",
                6482
              ],
              [
                "NS:SimpleTbQueueCallback#onSuccess",
                4743
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 246970,
            "TAINT_memberships": 2081189,
            "protected_memberships": 943791,
            "protected_share": 0.4534864445276234,
            "coverage": {
              "removable_now": 0,
              "protection_only": 130921,
              "other": 1950268
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.06290682874068622,
              "other": 0.9370931712593138
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 2473
            },
            "primary_other_reasons": {
              "NO_ANNOTATED_ANY_PREFIX": 151922,
              "ALIAS_EFFECT_CLASS": 702038,
              "OUTPUT_TAIL_MISMATCH": 23627,
              "OUTPUT_BASE_MISMATCH": 67779,
              "NO_FLOW_COUNTERPART": 119081,
              "UNSUPPORTED_INITIAL": 27410,
              "CROSS_ATOM": 809230,
              "MARK_EXCLUDED": 4950,
              "ZERO_INITIAL": 43102,
              "UNSUPPORTED_OUTPUT_TAIL": 1129
            },
            "secondary_failures_nonadditive": {
              "NO_ANNOTATED_ANY_PREFIX": 220717,
              "OUTPUT_TAIL_MISMATCH": 69926,
              "OUTPUT_BASE_MISMATCH": 196345,
              "ALIAS_EFFECT_CLASS": 702038,
              "NO_FLOW_COUNTERPART": 119081,
              "UNSUPPORTED_INITIAL": 27410,
              "CROSS_ATOM": 809230,
              "MARK_EXCLUDED": 17493,
              "ZERO_INITIAL": 43102,
              "UNSUPPORTED_OUTPUT_TAIL": 1129
            },
            "TAINT_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 760869,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 202702,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 36925,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 6538,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 387,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=1": 88865,
              "STAR->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 778176,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 98167,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1514,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 1534,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 1548,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 17064,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2772,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 15492,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10743,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10468,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 14,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 591,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 7652,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 815,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 11241,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 416,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=0": 24,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 360,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 756,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1028,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 798,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1673,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 55,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 9,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 2456,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2120,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 19,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1764,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 210,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 235,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 29,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 72,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 45,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 16,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 11112,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 72,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 144,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 576,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 72,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 109,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=1": 4,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1656,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 360,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 270,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 252,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 1
            },
            "FLOW_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|depth=1": 30610,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 5885,
              "STAR->STAR|NS->NS|NORMAL|depth=0": 69198,
              "STAR->ANY|S->NS|DEMAND|depth=1": 51118,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 11779,
              "STAR->ANY|S->NS|DEMAND|depth=0": 4741,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 7924,
              "STAR->ANY|NS->S|DEMAND|depth=2": 65330,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 384,
              "STAR->STAR|NS->S|DEMAND|depth=2": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 45240,
                "EXACT->ANY_TAINT": 10666,
                "EXACT->EXACT": 14606,
                "STAR->ANY": 2009184,
                "STAR->EXACT": 1493
              },
              "base_pairs": {
                "NS->NS": 780032,
                "NS->S": 882429,
                "S->NS": 375626,
                "Z->NS": 23057,
                "Z->S": 20045
              },
              "layers": {
                "DEMAND": 2081189
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 872411,
                "diagonal": 1208778
              },
              "flags": {
                "false": 1137398,
                "true": 943791
              },
              "output_depth": {
                "0": 994057,
                "1": 185414,
                "2": 901718
              },
              "output_bases": {
                "NS": 1178715,
                "S": 902474
              },
              "protected_output_bases": {
                "NS": 54233,
                "S": 889558
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 159723,
                "STAR->STAR": 87247
              },
              "base_pairs": {
                "NS->NS": 125780,
                "NS->S": 65331,
                "S->NS": 55859
              },
              "layers": {
                "DEMAND": 165993,
                "NORMAL": 80977
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 87748,
                "1": 93891,
                "2": 65331
              },
              "output_bases": {
                "NS": 181639,
                "S": 65331
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=2)": 1928808,
              "GroupId(value=8)": 58888,
              "GroupId(value=7)": 10243,
              "GroupId(value=11)": 10276,
              "GroupId(value=5)": 10596,
              "GroupId(value=6)": 10242,
              "GroupId(value=4)": 11041,
              "GroupId(value=9)": 10244,
              "GroupId(value=10)": 10305,
              "GroupId(value=12)": 10257,
              "GroupId(value=13)": 10288,
              "GroupId(value=0)": 1
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 80711,
              "diagonal_mark_rows": 1126203,
              "scalar_concrete_rows": 18882
            },
            "protection_tree_counts": {
              "none": 1073977,
              "full_structural_only": 67687,
              "full_identity": 2986,
              "partial": 435
            },
            "protection_tree_memberships": {
              "none": 1130625,
              "full_structural_only": 928957,
              "full_identity": 3020,
              "partial": 18587
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.thingsboard.server.controller.TelemetryController#deleteAttributes(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.AttributeScope, java.util.List) [{}]",
                2027
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1962
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{}]",
                1955
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.ArrayList} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1955
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.HashSet} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1955
              ],
              [
                "org.thingsboard.server.controller.TelemetryController#lambda$saveTelemetry$8(long, org.thingsboard.server.service.security.model.SecurityUser, java.util.List, org.springframework.web.context.request.async.DeferredResult, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId) [{}]",
                1890
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1854
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#lambda$onDeviceClaimJson$12(java.util.Map$Entry, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean, org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext) [{}]",
                1854
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#processClaimDeviceMsg(org.thingsboard.server.transport.mqtt.session.MqttDeviceAwareSessionContext, com.google.gson.JsonElement, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean) [{arg(0) is org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext}]",
                1854
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processArgumentValuesUpdate(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback, java.util.Map, java.util.UUID, org.thingsboard.server.common.data.msg.TbMsgType) [{}]",
                1711
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processArgumentValuesUpdate(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback, java.util.Map, java.util.UUID, org.thingsboard.server.common.data.msg.TbMsgType) [{arg(1) == java.util.HashSet} & {arg(2) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                1711
              ],
              [
                "org.thingsboard.server.transport.lwm2m.server.ota.DefaultLwM2MOtaUpdateService#onTargetSoftwareUpdate(org.thingsboard.server.transport.lwm2m.server.client.LwM2mClient, java.lang.String, java.lang.String, java.util.Optional, java.util.Optional) [{}]",
                1668
              ],
              [
                "org.thingsboard.server.service.cf.AbstractCalculatedFieldProcessingService#sendMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.msg.queue.TbCallback, org.thingsboard.server.common.msg.TbMsg) [{}]",
                1653
              ]
            ],
            "top_fields": [
              [
                "NS:",
                994057
              ],
              [
                "S:<static>(org.thingsboard.server.common.data.id.TenantId)/TenantId#tenants",
                66906
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.event.EventService",
                64341
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbCallback)/TbCallback#EMPTY",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.edge.EdgeService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.rpc.TbCoreDeviceRpcService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.cluster.TbClusterService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.nosql.CassandraBufferedRateWriteExecutor",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.timeseries.TimeseriesService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.apiusage.TbApiUsageStateService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.ruleengine.RuleEngineCallService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.session.DeviceSessionCacheService",
                64049
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.transport.TbCoreToTransportService",
                64049
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbMsgCallback)/TbMsgCallback#EMPTY",
                64049
              ],
              [
                "S:<static>(org.thingsboard.rule.engine.math.TbMathNode)/TbMathNode#locks",
                64049
              ],
              [
                "NS:DefaultTransportService$StatsCallback#callback",
                7140
              ],
              [
                "NS:MultipleTbQueueCallbackWrapper#callback",
                6956
              ],
              [
                "NS:DefaultCalculatedFieldQueueService$FutureCallbackWrapper#callback",
                6843
              ],
              [
                "NS:ValidationCallback#action",
                6482
              ],
              [
                "NS:SimpleTbQueueCallback#onSuccess",
                4743
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "TAINT.shape.STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=1": {
            "raw": 88866,
            "selected": 88865
          },
          "TAINT.shape.STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": {
            "raw": 36924,
            "selected": 36925
          },
          "TAINT.protection_tree_memberships.full_structural_only": {
            "raw": 928956,
            "selected": 928957
          },
          "TAINT.protection_trees.none": {
            "raw": 1073978,
            "selected": 1073977
          },
          "TAINT.flag_annotations": {
            "raw": 943790,
            "selected": 943791
          },
          "TAINT.protection_trees.full_structural_only": {
            "raw": 67686,
            "selected": 67687
          },
          "TAINT.protection_tree_memberships.none": {
            "raw": 1130626,
            "selected": 1130625
          },
          "event.covered_offer_rejections": {
            "raw": 5802160,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-cold-actors-v1",
          "totals": {
            "scalar_headers": 173959542,
            "packed_invocations": 3887632,
            "packed_mark_credits": 7831446,
            "physical_method_edge_invocations": 177847174
          },
          "actor_totals": {
            "actors": 73669,
            "steps": 181790988,
            "neutralBatchApplications": 3887632,
            "neutralBatchMemberships": 7831446
          },
          "top_methods": [
            {
              "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#processUplinkMsg(org.thingsboard.server.gen.edge.v1.UplinkMsg) [{}]",
              "step_credits": 17006067,
              "scalar_headers": 16933657,
              "packed_invocations": 58807,
              "packed_mark_credits": 72410,
              "physical_method_edge_invocations": 16992464
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.common.util.JacksonUtil$replaceAllByMapping_27c33466$jIR_lambda$0/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 2362451,
              "scalar_headers": 2344947,
              "packed_invocations": 13928,
              "packed_mark_credits": 17504,
              "physical_method_edge_invocations": 2358875
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.server.dao.resource.BaseResourceService$processResources_fc592dee$jIR_lambda$18/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 1447587,
              "scalar_headers": 1436787,
              "packed_invocations": 8898,
              "packed_mark_credits": 10800,
              "physical_method_edge_invocations": 1445685
            },
            {
              "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#lambda$scheduleDownlinkMsgsPackSend$5(int) [{}]",
              "step_credits": 1230873,
              "scalar_headers": 1217661,
              "packed_invocations": 12239,
              "packed_mark_credits": 13212,
              "physical_method_edge_invocations": 1229900
            },
            {
              "method": "org.thingsboard.server.service.entitiy.queue.DefaultTbQueueService#updateQueuesByTenants(java.util.List, org.thingsboard.server.common.data.TenantProfile, org.thingsboard.server.common.data.TenantProfile) [{}]",
              "step_credits": 1022081,
              "scalar_headers": 1004273,
              "packed_invocations": 8278,
              "packed_mark_credits": 17808,
              "physical_method_edge_invocations": 1012551
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{}]",
              "step_credits": 1001305,
              "scalar_headers": 993547,
              "packed_invocations": 5925,
              "packed_mark_credits": 7758,
              "physical_method_edge_invocations": 999472
            },
            {
              "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{}]",
              "step_credits": 992099,
              "scalar_headers": 984481,
              "packed_invocations": 4994,
              "packed_mark_credits": 7618,
              "physical_method_edge_invocations": 989475
            },
            {
              "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{arg(2) == (lambda: org.thingsboard.server.service.sync.ie.importing.impl.RuleChainImportService$saveOrUpdate_3af00c54$jIR_lambda$15/java.util.function.Function#apply(java.lang.Object))}]",
              "step_credits": 966808,
              "scalar_headers": 959777,
              "packed_invocations": 4774,
              "packed_mark_credits": 7031,
              "physical_method_edge_invocations": 964551
            },
            {
              "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{arg(0) is org.thingsboard.server.actors.ruleChain.DefaultTbContext}]",
              "step_credits": 954528,
              "scalar_headers": 946858,
              "packed_invocations": 5429,
              "packed_mark_credits": 7670,
              "physical_method_edge_invocations": 952287
            },
            {
              "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{}]",
              "step_credits": 953865,
              "scalar_headers": 946195,
              "packed_invocations": 5890,
              "packed_mark_credits": 7670,
              "physical_method_edge_invocations": 952085
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceAll(com.fasterxml.jackson.databind.JsonNode, java.lang.String, java.util.function.BiFunction) [{arg(2) == (lambda: org.thingsboard.server.dao.resource.BaseImageService$convertToImageUrls_69156998$jIR_lambda$2/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 822337,
              "scalar_headers": 811096,
              "packed_invocations": 10103,
              "packed_mark_credits": 11241,
              "physical_method_edge_invocations": 821199
            },
            {
              "method": "org.thingsboard.server.gen.edge.v1.DownlinkMsg#getSerializedSize() [{}]",
              "step_credits": 739513,
              "scalar_headers": 737659,
              "packed_invocations": 1839,
              "packed_mark_credits": 1854,
              "physical_method_edge_invocations": 739498
            },
            {
              "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{arg(2) == (lambda: org.thingsboard.server.service.rule.DefaultTbRuleChainService$saveRuleChainMetaData_a3fba5fa$jIR_lambda$7/java.util.function.Function#apply(java.lang.Object))}]",
              "step_credits": 728097,
              "scalar_headers": 723100,
              "packed_invocations": 2648,
              "packed_mark_credits": 4997,
              "physical_method_edge_invocations": 725748
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 673322,
              "scalar_headers": 661475,
              "packed_invocations": 4556,
              "packed_mark_credits": 11847,
              "physical_method_edge_invocations": 666031
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm}]",
              "step_credits": 671348,
              "scalar_headers": 659429,
              "packed_invocations": 4323,
              "packed_mark_credits": 11919,
              "physical_method_edge_invocations": 663752
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 661245,
              "scalar_headers": 649722,
              "packed_invocations": 4290,
              "packed_mark_credits": 11523,
              "physical_method_edge_invocations": 654012
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo}]",
              "step_credits": 653318,
              "scalar_headers": 641471,
              "packed_invocations": 4555,
              "packed_mark_credits": 11847,
              "physical_method_edge_invocations": 646026
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain}]",
              "step_credits": 650970,
              "scalar_headers": 638904,
              "packed_invocations": 4552,
              "packed_mark_credits": 12066,
              "physical_method_edge_invocations": 643456
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard}]",
              "step_credits": 650138,
              "scalar_headers": 638200,
              "packed_invocations": 4307,
              "packed_mark_credits": 11938,
              "physical_method_edge_invocations": 642507
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 649397,
              "scalar_headers": 637575,
              "packed_invocations": 4543,
              "packed_mark_credits": 11822,
              "physical_method_edge_invocations": 642118
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile}]",
              "step_credits": 649397,
              "scalar_headers": 637579,
              "packed_invocations": 4537,
              "packed_mark_credits": 11818,
              "physical_method_edge_invocations": 642116
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile}]",
              "step_credits": 649397,
              "scalar_headers": 637579,
              "packed_invocations": 4537,
              "packed_mark_credits": 11818,
              "physical_method_edge_invocations": 642116
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device}]",
              "step_credits": 649371,
              "scalar_headers": 637553,
              "packed_invocations": 4529,
              "packed_mark_credits": 11818,
              "physical_method_edge_invocations": 642082
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView}]",
              "step_credits": 649371,
              "scalar_headers": 637553,
              "packed_invocations": 4529,
              "packed_mark_credits": 11818,
              "physical_method_edge_invocations": 642082
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 649371,
              "scalar_headers": 637553,
              "packed_invocations": 4306,
              "packed_mark_credits": 11818,
              "physical_method_edge_invocations": 641859
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 641931,
              "scalar_headers": 630480,
              "packed_invocations": 4544,
              "packed_mark_credits": 11451,
              "physical_method_edge_invocations": 635024
            },
            {
              "method": "org.thingsboard.server.transport.coap.client.DefaultCoapClientContext$CoapSessionListener#onToDeviceRpcRequest(java.util.UUID, org.thingsboard.server.gen.transport.TransportProtos$ToDeviceRpcRequestMsg) [{}]",
              "step_credits": 634244,
              "scalar_headers": 627281,
              "packed_invocations": 6184,
              "packed_mark_credits": 6963,
              "physical_method_edge_invocations": 633465
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel}]",
              "step_credits": 639783,
              "scalar_headers": 627751,
              "packed_invocations": 4122,
              "packed_mark_credits": 12032,
              "physical_method_edge_invocations": 631873
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 636956,
              "scalar_headers": 625534,
              "packed_invocations": 4485,
              "packed_mark_credits": 11422,
              "physical_method_edge_invocations": 630019
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 636917,
              "scalar_headers": 625495,
              "packed_invocations": 4489,
              "packed_mark_credits": 11422,
              "physical_method_edge_invocations": 629984
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 630386,
              "scalar_headers": 619260,
              "packed_invocations": 4069,
              "packed_mark_credits": 11126,
              "physical_method_edge_invocations": 623329
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(1) is org.thingsboard.server.common.data.TbResourceInfo}]",
              "step_credits": 626395,
              "scalar_headers": 614879,
              "packed_invocations": 4157,
              "packed_mark_credits": 11516,
              "physical_method_edge_invocations": 619036
            },
            {
              "method": "org.thingsboard.server.controller.NotificationController#getNotificationRequestPreview(org.thingsboard.server.common.data.notification.NotificationRequest, int, org.thingsboard.server.service.security.model.SecurityUser) [{}]",
              "step_credits": 616591,
              "scalar_headers": 612559,
              "packed_invocations": 3387,
              "packed_mark_credits": 4032,
              "physical_method_edge_invocations": 615946
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 621653,
              "scalar_headers": 609685,
              "packed_invocations": 4152,
              "packed_mark_credits": 11968,
              "physical_method_edge_invocations": 613837
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 621640,
              "scalar_headers": 609674,
              "packed_invocations": 4150,
              "packed_mark_credits": 11966,
              "physical_method_edge_invocations": 613824
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(1) is org.thingsboard.server.common.data.TbResourceInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 611551,
              "scalar_headers": 600431,
              "packed_invocations": 4144,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 604575
            },
            {
              "method": "org.thingsboard.server.common.adaptor.JsonConverter#parseProtoValues(com.google.gson.JsonObject) [{}]",
              "step_credits": 604102,
              "scalar_headers": 600502,
              "packed_invocations": 3347,
              "packed_mark_credits": 3600,
              "physical_method_edge_invocations": 603849
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{}]",
              "step_credits": 604089,
              "scalar_headers": 593518,
              "packed_invocations": 3847,
              "packed_mark_credits": 10571,
              "physical_method_edge_invocations": 597365
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId}]",
              "step_credits": 599101,
              "scalar_headers": 588553,
              "packed_invocations": 3824,
              "packed_mark_credits": 10548,
              "physical_method_edge_invocations": 592377
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 596633,
              "scalar_headers": 586091,
              "packed_invocations": 3547,
              "packed_mark_credits": 10542,
              "physical_method_edge_invocations": 589638
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 722.861678039
      },
      "after": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "shape-probe-results",
          "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
          "core": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
          "checker": "correlated-star-any-v1",
          "policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order."
        },
        "input": {
          "path": "shape-probe-results/thingsboard/bidi/shapes/run1-shapes.json",
          "sha256": "806e5bba1c968f9c6861d94a608e1688c42829fc020ca44f81e9b74cd818d0c9"
        },
        "manifest": {
          "path": "shape-probe-results/thingsboard/bidi/manifest.json",
          "sha256": "6229ecfb67891c062c2395ae31fe77a98f66e59577aed7a056414f162e774648"
        },
        "summary": {
          "path": "shape-probe-results/thingsboard/bidi/summary.json",
          "sha256": "6657d9fbe3dabd8c3c5c51e062326579114d85657082748a17eefa48a45ead6c"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "21:46:47.222 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=13m 49.668124305s markMode=FULL",
          "end_line": "21:57:40.335 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=10m 53.113238125s",
          "barrier_line": "21:58:18.077 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=37.693793067s iterationTime=11m 30.855869341s"
        },
        "accepted_forward_frontier": "21:58:17.231 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 37378, demand edges 2078059 in 73599 method keys, left 34, record crossings 0, DEMAND 95058, CONFIRMED 0, seeds 141974, zero only 36291 (185513 edges)",
        "explicit_handoff_demand_patterns": 2078059,
        "demand_method_keys": 73599,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order.",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
          "memory": "12g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
        "owners": {
          "raw": {
            "FLOW_memberships": 226209,
            "TAINT_memberships": 1800397,
            "protected_memberships": 1737136,
            "protected_share": 0.9648627497157571,
            "coverage": {
              "removable_now": 0,
              "protection_only": 901285,
              "other": 899112
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.5006034780106832,
              "other": 0.4993965219893168
            },
            "removal_events": {
              "covered_offer_rejections": 7327506,
              "stored_compaction_memberships": 102
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 33195,
              "CROSS_ATOM": 817618,
              "NO_FLOW_COUNTERPART": 54,
              "MARK_EXCLUDED": 3934,
              "OUTPUT_BASE_MISMATCH": 108,
              "ZERO_INITIAL": 43089,
              "UNSUPPORTED_OUTPUT": 1096,
              "OUTPUT_TAIL_MISMATCH": 18
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 33195,
              "CROSS_ATOM": 817618,
              "NO_FLOW_COUNTERPART": 54,
              "MARK_EXCLUDED": 3934,
              "OUTPUT_BASE_MISMATCH": 2541,
              "NO_ANNOTATED_ANY_PREFIX": 3002,
              "OUTPUT_TAIL_MISMATCH": 1606,
              "STAR_PATH_INEQUALITY": 10,
              "ZERO_INITIAL": 43089,
              "UNSUPPORTED_OUTPUT": 1096
            },
            "TAINT_full_shape_histogram": {
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 42518,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 387,
              "STAR->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 778176,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 857848,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 162,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 4814,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 12,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 9828,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 10674,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1872,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10916,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10641,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 7676,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 967,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 87,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 416,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 360,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 756,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1868,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1026,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 60,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 11217,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 16,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 2465,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2232,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 19,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 201,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1764,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 235,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 67,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 72,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 13932,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 25002,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1530,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 14,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 13,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 6,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 109,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=false|depth=0": 18,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 16,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 1,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=0": 2
            },
            "FLOW_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|depth=1": 29413,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 5631,
              "STAR->STAR|NS->NS|NORMAL|depth=0": 66464,
              "STAR->ANY|S->NS|DEMAND|depth=1": 36744,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 11489,
              "STAR->ANY|S->NS|DEMAND|depth=0": 2527,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 7755,
              "STAR->ANY|NS->S|DEMAND|depth=2": 65843,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 342,
              "STAR->STAR|NS->S|DEMAND|depth=2": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 50468,
                "EXACT->ANY_TAINT": 10839,
                "EXACT->EXACT": 14977,
                "STAR->ANY": 1722623,
                "STAR->EXACT": 1460,
                "STAR->STAR": 30
              },
              "base_pairs": {
                "NS->NS": 13893,
                "NS->S": 1640454,
                "S->NS": 102961,
                "Z->NS": 23044,
                "Z->S": 20045
              },
              "layers": {
                "DEMAND": 1800397
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 887050,
                "diagonal": 913347
              },
              "flags": {
                "false": 63261,
                "true": 1737136
              },
              "output_depth": {
                "0": 25333,
                "1": 115321,
                "2": 1659743
              },
              "output_bases": {
                "NS": 139898,
                "S": 1660499
              },
              "protected_output_bases": {
                "NS": 87930,
                "S": 1649206
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 142282,
                "STAR->STAR": 83927
              },
              "base_pairs": {
                "NS->NS": 121094,
                "NS->S": 65844,
                "S->NS": 39271
              },
              "layers": {
                "DEMAND": 148256,
                "NORMAL": 77953
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 82377,
                "1": 77988,
                "2": 65844
              },
              "output_bases": {
                "NS": 160365,
                "S": 65844
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=8)": 50938,
              "GroupId(value=2)": 1717165,
              "GroupId(value=5)": 2929,
              "GroupId(value=6)": 3666,
              "GroupId(value=7)": 3667,
              "GroupId(value=4)": 3674,
              "GroupId(value=9)": 3666,
              "GroupId(value=10)": 3683,
              "GroupId(value=11)": 3666,
              "GroupId(value=12)": 3676,
              "GroupId(value=13)": 3666,
              "GroupId(value=0)": 1
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 25820,
              "diagonal_mark_rows": 176807,
              "scalar_concrete_rows": 18239
            },
            "protection_tree_counts": {
              "full_structural_only": 182426,
              "none": 12199,
              "full_identity": 61,
              "partial": 360
            },
            "protection_tree_memberships": {
              "full_structural_only": 1720875,
              "none": 47295,
              "full_identity": 61,
              "partial": 32166
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.thingsboard.server.service.security.AccessValidator#validate(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                7139
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateApiUsageState(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                6692
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateAssetProfile(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4492
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateDeviceProfile(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4492
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateOtaPackage(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4287
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.ArrayList} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.HashSet} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.controller.TelemetryController#lambda$saveTelemetry$8(long, org.thingsboard.server.service.security.model.SecurityUser, java.util.List, org.springframework.web.context.request.async.DeferredResult, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#lambda$onDeviceClaimJson$12(java.util.Map$Entry, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean, org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#processClaimDeviceMsg(org.thingsboard.server.transport.mqtt.session.MqttDeviceAwareSessionContext, com.google.gson.JsonElement, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean) [{arg(0) is org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext}]",
                3192
              ]
            ],
            "top_fields": [
              [
                "S:<static>(org.thingsboard.server.common.data.id.TenantId)/TenantId#tenants",
                121135
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbCallback)/TbCallback#EMPTY",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.edge.EdgeService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.event.EventService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.rpc.TbCoreDeviceRpcService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.cluster.TbClusterService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.nosql.CassandraBufferedRateWriteExecutor",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.timeseries.TimeseriesService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.apiusage.TbApiUsageStateService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.ruleengine.RuleEngineCallService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.session.DeviceSessionCacheService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.transport.TbCoreToTransportService",
                118211
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbMsgCallback)/TbMsgCallback#EMPTY",
                118211
              ],
              [
                "S:<static>(org.thingsboard.rule.engine.math.TbMathNode)/TbMathNode#locks",
                118211
              ],
              [
                "NS:",
                25333
              ],
              [
                "NS:ValidationCallback#action",
                7165
              ],
              [
                "NS:DefaultTransportService$StatsCallback#callback",
                6851
              ],
              [
                "NS:MultipleTbQueueCallbackWrapper#callback",
                6644
              ],
              [
                "NS:DefaultCalculatedFieldQueueService$FutureCallbackWrapper#callback",
                6529
              ],
              [
                "NS:SimpleTbQueueCallback#onSuccess",
                4794
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 226209,
            "TAINT_memberships": 1800397,
            "protected_memberships": 1737136,
            "protected_share": 0.9648627497157571,
            "coverage": {
              "removable_now": 0,
              "protection_only": 901285,
              "other": 899112
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.5006034780106832,
              "other": 0.4993965219893168
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 102
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 33195,
              "CROSS_ATOM": 817618,
              "NO_FLOW_COUNTERPART": 54,
              "MARK_EXCLUDED": 3934,
              "OUTPUT_BASE_MISMATCH": 108,
              "ZERO_INITIAL": 43089,
              "UNSUPPORTED_OUTPUT": 1096,
              "OUTPUT_TAIL_MISMATCH": 18
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 33195,
              "CROSS_ATOM": 817618,
              "NO_FLOW_COUNTERPART": 54,
              "MARK_EXCLUDED": 3934,
              "OUTPUT_BASE_MISMATCH": 2541,
              "NO_ANNOTATED_ANY_PREFIX": 3002,
              "OUTPUT_TAIL_MISMATCH": 1606,
              "STAR_PATH_INEQUALITY": 10,
              "ZERO_INITIAL": 43089,
              "UNSUPPORTED_OUTPUT": 1096
            },
            "TAINT_full_shape_histogram": {
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 42518,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 387,
              "STAR->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 778176,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 857848,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 162,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 4814,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 12,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 9828,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 10674,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1872,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10916,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 10641,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 7676,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 967,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 87,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 416,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 360,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 756,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1868,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 1026,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 60,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 11217,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 16,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 2465,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2232,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 19,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 201,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1764,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 235,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 67,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 72,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 198,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 13932,
              "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 25002,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1530,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 14,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 13,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 6,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 109,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=false|depth=0": 18,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 16,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 1,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=0": 2
            },
            "FLOW_full_shape_histogram": {
              "STAR->ANY|NS->NS|DEMAND|depth=1": 29413,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 5631,
              "STAR->STAR|NS->NS|NORMAL|depth=0": 66464,
              "STAR->ANY|S->NS|DEMAND|depth=1": 36744,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 11489,
              "STAR->ANY|S->NS|DEMAND|depth=0": 2527,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 7755,
              "STAR->ANY|NS->S|DEMAND|depth=2": 65843,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 342,
              "STAR->STAR|NS->S|DEMAND|depth=2": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 50468,
                "EXACT->ANY_TAINT": 10839,
                "EXACT->EXACT": 14977,
                "STAR->ANY": 1722623,
                "STAR->EXACT": 1460,
                "STAR->STAR": 30
              },
              "base_pairs": {
                "NS->NS": 13893,
                "NS->S": 1640454,
                "S->NS": 102961,
                "Z->NS": 23044,
                "Z->S": 20045
              },
              "layers": {
                "DEMAND": 1800397
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 887050,
                "diagonal": 913347
              },
              "flags": {
                "false": 63261,
                "true": 1737136
              },
              "output_depth": {
                "0": 25333,
                "1": 115321,
                "2": 1659743
              },
              "output_bases": {
                "NS": 139898,
                "S": 1660499
              },
              "protected_output_bases": {
                "NS": 87930,
                "S": 1649206
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 142282,
                "STAR->STAR": 83927
              },
              "base_pairs": {
                "NS->NS": 121094,
                "NS->S": 65844,
                "S->NS": 39271
              },
              "layers": {
                "DEMAND": 148256,
                "NORMAL": 77953
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 82377,
                "1": 77988,
                "2": 65844
              },
              "output_bases": {
                "NS": 160365,
                "S": 65844
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=8)": 50938,
              "GroupId(value=2)": 1717165,
              "GroupId(value=5)": 2929,
              "GroupId(value=6)": 3666,
              "GroupId(value=7)": 3667,
              "GroupId(value=4)": 3674,
              "GroupId(value=9)": 3666,
              "GroupId(value=10)": 3683,
              "GroupId(value=11)": 3666,
              "GroupId(value=12)": 3676,
              "GroupId(value=13)": 3666,
              "GroupId(value=0)": 1
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 25820,
              "diagonal_mark_rows": 176807,
              "scalar_concrete_rows": 18239
            },
            "protection_tree_counts": {
              "full_structural_only": 182426,
              "none": 12199,
              "full_identity": 61,
              "partial": 360
            },
            "protection_tree_memberships": {
              "full_structural_only": 1720875,
              "none": 47295,
              "full_identity": 61,
              "partial": 32166
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.thingsboard.server.service.security.AccessValidator#validate(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                7139
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateApiUsageState(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                6692
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateAssetProfile(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4492
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateDeviceProfile(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4492
              ],
              [
                "org.thingsboard.server.service.security.AccessValidator#validateOtaPackage(org.thingsboard.server.service.security.model.SecurityUser, org.thingsboard.server.service.security.permission.Operation, org.thingsboard.server.common.data.id.EntityId, com.google.common.util.concurrent.FutureCallback) [{}]",
                4287
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.ArrayList} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.HashSet} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.controller.TelemetryController#lambda$saveTelemetry$8(long, org.thingsboard.server.service.security.model.SecurityUser, java.util.List, org.springframework.web.context.request.async.DeferredResult, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.HashSet} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
                3192
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#lambda$onDeviceClaimJson$12(java.util.Map$Entry, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean, org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext) [{}]",
                3192
              ],
              [
                "org.thingsboard.server.transport.mqtt.session.AbstractGatewaySessionHandler#processClaimDeviceMsg(org.thingsboard.server.transport.mqtt.session.MqttDeviceAwareSessionContext, com.google.gson.JsonElement, java.lang.String, int, java.util.concurrent.atomic.AtomicInteger, java.util.concurrent.atomic.AtomicBoolean) [{arg(0) is org.thingsboard.server.transport.mqtt.session.AbstractGatewayDeviceSessionContext}]",
                3192
              ]
            ],
            "top_fields": [
              [
                "S:<static>(org.thingsboard.server.common.data.id.TenantId)/TenantId#tenants",
                121135
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbCallback)/TbCallback#EMPTY",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.edge.EdgeService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.event.EventService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.rpc.TbCoreDeviceRpcService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.cluster.TbClusterService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.nosql.CassandraBufferedRateWriteExecutor",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.timeseries.TimeseriesService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.apiusage.TbApiUsageStateService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.ruleengine.RuleEngineCallService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.session.DeviceSessionCacheService",
                118211
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.transport.TbCoreToTransportService",
                118211
              ],
              [
                "S:<static>(org.thingsboard.server.common.msg.queue.TbMsgCallback)/TbMsgCallback#EMPTY",
                118211
              ],
              [
                "S:<static>(org.thingsboard.rule.engine.math.TbMathNode)/TbMathNode#locks",
                118211
              ],
              [
                "NS:",
                25333
              ],
              [
                "NS:ValidationCallback#action",
                7165
              ],
              [
                "NS:DefaultTransportService$StatsCallback#callback",
                6851
              ],
              [
                "NS:MultipleTbQueueCallbackWrapper#callback",
                6644
              ],
              [
                "NS:DefaultCalculatedFieldQueueService$FutureCallbackWrapper#callback",
                6529
              ],
              [
                "NS:SimpleTbQueueCallback#onSuccess",
                4794
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 7327506,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-v2",
          "totals": {
            "scalar_headers": 140288224,
            "packed_invocations": 3618887,
            "packed_mark_credits": 6789565,
            "resume_events": 1011222,
            "physical_method_edge_invocations": 143907111,
            "statement_untouched_from_process": 86690000,
            "statement_pure_untouched_from_process": 71897409,
            "statement_untouched_from_resume": 0,
            "statement_pure_untouched_from_resume": 0,
            "packed_untouched_callbacks": 3164550,
            "packed_untouched_mark_credits": 5954705,
            "scalar_taint_headers": 128093674,
            "scalar_fully_protected_identity_headers": 275612,
            "packed_fully_protected_identity_invocations": 2787,
            "packed_fully_protected_identity_mark_credits": 7233,
            "resume_taint_headers": 1006505,
            "resume_fully_protected_identity_headers": 0
          },
          "actor_totals": {
            "actors": 73669,
            "steps": 147077789,
            "neutralBatchApplications": 3618887,
            "neutralBatchMemberships": 6789565
          },
          "top_methods": [
            {
              "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#processUplinkMsg(org.thingsboard.server.gen.edge.v1.UplinkMsg) [{}]",
              "step_credits": 14688616,
              "scalar_headers": 14623519,
              "packed_invocations": 52858,
              "packed_mark_credits": 65097,
              "physical_method_edge_invocations": 14676377,
              "edge_delta_credits": 106552,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.common.util.JacksonUtil$replaceAllByMapping_27c33466$jIR_lambda$0/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 1910552,
              "scalar_headers": 1896198,
              "packed_invocations": 10977,
              "packed_mark_credits": 14354,
              "physical_method_edge_invocations": 1907175,
              "edge_delta_credits": 20910,
              "neutral_scalar_store_fallback_credits": 116
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.server.dao.resource.BaseResourceService$processResources_fc592dee$jIR_lambda$18/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 991079,
              "scalar_headers": 983465,
              "packed_invocations": 5865,
              "packed_mark_credits": 7614,
              "physical_method_edge_invocations": 989330,
              "edge_delta_credits": 10923,
              "neutral_scalar_store_fallback_credits": 36
            },
            {
              "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#lambda$scheduleDownlinkMsgsPackSend$5(int) [{}]",
              "step_credits": 823616,
              "scalar_headers": 815532,
              "packed_invocations": 7186,
              "packed_mark_credits": 8084,
              "physical_method_edge_invocations": 822718,
              "edge_delta_credits": 19965,
              "neutral_scalar_store_fallback_credits": 109
            },
            {
              "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{}]",
              "step_credits": 750609,
              "scalar_headers": 744753,
              "packed_invocations": 5483,
              "packed_mark_credits": 5856,
              "physical_method_edge_invocations": 750236,
              "edge_delta_credits": 11309,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{arg(0) is org.thingsboard.server.actors.ruleChain.DefaultTbContext}]",
              "step_credits": 750037,
              "scalar_headers": 744181,
              "packed_invocations": 5483,
              "packed_mark_credits": 5856,
              "physical_method_edge_invocations": 749664,
              "edge_delta_credits": 11329,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.gen.edge.v1.DownlinkMsg#getSerializedSize() [{}]",
              "step_credits": 739513,
              "scalar_headers": 737659,
              "packed_invocations": 1836,
              "packed_mark_credits": 1854,
              "physical_method_edge_invocations": 739495,
              "edge_delta_credits": 6638,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{}]",
              "step_credits": 738854,
              "scalar_headers": 733010,
              "packed_invocations": 3907,
              "packed_mark_credits": 5844,
              "physical_method_edge_invocations": 736917,
              "edge_delta_credits": 11977,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{arg(2) == (lambda: org.thingsboard.server.service.sync.ie.importing.impl.RuleChainImportService$saveOrUpdate_3af00c54$jIR_lambda$15/java.util.function.Function#apply(java.lang.Object))}]",
              "step_credits": 713692,
              "scalar_headers": 708352,
              "packed_invocations": 3824,
              "packed_mark_credits": 5340,
              "physical_method_edge_invocations": 712176,
              "edge_delta_credits": 11052,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceAll(com.fasterxml.jackson.databind.JsonNode, java.lang.String, java.util.function.BiFunction) [{arg(2) == (lambda: org.thingsboard.server.dao.resource.BaseImageService$convertToImageUrls_69156998$jIR_lambda$2/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
              "step_credits": 679878,
              "scalar_headers": 670491,
              "packed_invocations": 8504,
              "packed_mark_credits": 9387,
              "physical_method_edge_invocations": 678995,
              "edge_delta_credits": 13305,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.entitiy.queue.DefaultTbQueueService#updateQueuesByTenants(java.util.List, org.thingsboard.server.common.data.TenantProfile, org.thingsboard.server.common.data.TenantProfile) [{}]",
              "step_credits": 662738,
              "scalar_headers": 651683,
              "packed_invocations": 7312,
              "packed_mark_credits": 11055,
              "physical_method_edge_invocations": 658995,
              "edge_delta_credits": 13754,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 661821,
              "scalar_headers": 650672,
              "packed_invocations": 4200,
              "packed_mark_credits": 11149,
              "physical_method_edge_invocations": 654872,
              "edge_delta_credits": 15658,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.transport.coap.client.DefaultCoapClientContext$CoapSessionListener#onToDeviceRpcRequest(java.util.UUID, org.thingsboard.server.gen.transport.TransportProtos$ToDeviceRpcRequestMsg) [{}]",
              "step_credits": 638960,
              "scalar_headers": 631979,
              "packed_invocations": 6202,
              "packed_mark_credits": 6981,
              "physical_method_edge_invocations": 638181,
              "edge_delta_credits": 12786,
              "neutral_scalar_store_fallback_credits": 319
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 641744,
              "scalar_headers": 630048,
              "packed_invocations": 3930,
              "packed_mark_credits": 11696,
              "physical_method_edge_invocations": 633978,
              "edge_delta_credits": 15399,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain}]",
              "step_credits": 638013,
              "scalar_headers": 626893,
              "packed_invocations": 4172,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 631065,
              "edge_delta_credits": 14822,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile}]",
              "step_credits": 638013,
              "scalar_headers": 626893,
              "packed_invocations": 4165,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 631058,
              "edge_delta_credits": 14822,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile}]",
              "step_credits": 638013,
              "scalar_headers": 626893,
              "packed_invocations": 4159,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 631052,
              "edge_delta_credits": 14822,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard}]",
              "step_credits": 637987,
              "scalar_headers": 626867,
              "packed_invocations": 3919,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 630786,
              "edge_delta_credits": 14822,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 637974,
              "scalar_headers": 626854,
              "packed_invocations": 3909,
              "packed_mark_credits": 11120,
              "physical_method_edge_invocations": 630763,
              "edge_delta_credits": 14819,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{}]",
              "step_credits": 591877,
              "scalar_headers": 581975,
              "packed_invocations": 3512,
              "packed_mark_credits": 9902,
              "physical_method_edge_invocations": 585487,
              "edge_delta_credits": 13200,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId}]",
              "step_credits": 590607,
              "scalar_headers": 580158,
              "packed_invocations": 3252,
              "packed_mark_credits": 10449,
              "physical_method_edge_invocations": 583410,
              "edge_delta_credits": 13625,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 588152,
              "scalar_headers": 577703,
              "packed_invocations": 3243,
              "packed_mark_credits": 10449,
              "physical_method_edge_invocations": 580946,
              "edge_delta_credits": 13618,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm}]",
              "step_credits": 581782,
              "scalar_headers": 570561,
              "packed_invocations": 3807,
              "packed_mark_credits": 11221,
              "physical_method_edge_invocations": 574368,
              "edge_delta_credits": 15406,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo}]",
              "step_credits": 561991,
              "scalar_headers": 551346,
              "packed_invocations": 4059,
              "packed_mark_credits": 10645,
              "physical_method_edge_invocations": 555405,
              "edge_delta_credits": 14147,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{}]",
              "step_credits": 553290,
              "scalar_headers": 548718,
              "packed_invocations": 2889,
              "packed_mark_credits": 4572,
              "physical_method_edge_invocations": 551607,
              "edge_delta_credits": 6313,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device}]",
              "step_credits": 556990,
              "scalar_headers": 546374,
              "packed_invocations": 4056,
              "packed_mark_credits": 10616,
              "physical_method_edge_invocations": 550430,
              "edge_delta_credits": 14004,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView}]",
              "step_credits": 556990,
              "scalar_headers": 546374,
              "packed_invocations": 4036,
              "packed_mark_credits": 10616,
              "physical_method_edge_invocations": 550410,
              "edge_delta_credits": 14003,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 548347,
              "scalar_headers": 538170,
              "packed_invocations": 3732,
              "packed_mark_credits": 10177,
              "physical_method_edge_invocations": 541902,
              "edge_delta_credits": 14325,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge}]",
              "step_credits": 536632,
              "scalar_headers": 526664,
              "packed_invocations": 4104,
              "packed_mark_credits": 9968,
              "physical_method_edge_invocations": 530768,
              "edge_delta_credits": 13355,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 531805,
              "scalar_headers": 521628,
              "packed_invocations": 3736,
              "packed_mark_credits": 10177,
              "physical_method_edge_invocations": 525364,
              "edge_delta_credits": 13640,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 526817,
              "scalar_headers": 516669,
              "packed_invocations": 3709,
              "packed_mark_credits": 10148,
              "physical_method_edge_invocations": 520378,
              "edge_delta_credits": 13495,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 526804,
              "scalar_headers": 516656,
              "packed_invocations": 3701,
              "packed_mark_credits": 10148,
              "physical_method_edge_invocations": 520357,
              "edge_delta_credits": 13496,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 523047,
              "scalar_headers": 513475,
              "packed_invocations": 3705,
              "packed_mark_credits": 9572,
              "physical_method_edge_invocations": 517180,
              "edge_delta_credits": 12918,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo}]",
              "step_credits": 503044,
              "scalar_headers": 492780,
              "packed_invocations": 3450,
              "packed_mark_credits": 10264,
              "physical_method_edge_invocations": 496230,
              "edge_delta_credits": 13286,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(1) is org.thingsboard.server.common.data.TbResourceInfo}]",
              "step_credits": 500948,
              "scalar_headers": 490684,
              "packed_invocations": 3456,
              "packed_mark_credits": 10264,
              "physical_method_edge_invocations": 494140,
              "edge_delta_credits": 13279,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 485708,
              "scalar_headers": 476488,
              "packed_invocations": 3466,
              "packed_mark_credits": 9220,
              "physical_method_edge_invocations": 479954,
              "edge_delta_credits": 12886,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel}]",
              "step_credits": 485695,
              "scalar_headers": 476475,
              "packed_invocations": 3433,
              "packed_mark_credits": 9220,
              "physical_method_edge_invocations": 479908,
              "edge_delta_credits": 12884,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 469127,
              "scalar_headers": 459907,
              "packed_invocations": 3375,
              "packed_mark_credits": 9220,
              "physical_method_edge_invocations": 463282,
              "edge_delta_credits": 12205,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 469127,
              "scalar_headers": 459907,
              "packed_invocations": 3375,
              "packed_mark_credits": 9220,
              "physical_method_edge_invocations": 463282,
              "edge_delta_credits": 12205,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
              "step_credits": 469114,
              "scalar_headers": 459894,
              "packed_invocations": 3385,
              "packed_mark_credits": 9220,
              "physical_method_edge_invocations": 463279,
              "edge_delta_credits": 12203,
              "neutral_scalar_store_fallback_credits": 0
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 653.113238125
      },
      "raw_comparison": {
        "TAINT_memberships": {
          "before": 2081189,
          "after": 1800397,
          "change": -280792
        },
        "protected_memberships": {
          "before": 943790,
          "after": 1737136,
          "change": 793346
        },
        "FLOW_memberships": {
          "before": 246970,
          "after": 226209,
          "change": -20761
        }
      }
    },
    "conductor": {
      "before": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "baseline-shape-probe-results",
          "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
          "core": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
          "checker": "baseline-any-alias-guard-v1",
          "policy": "Old runtime ANY-only normalizer, canonical run-1 FULL/Empty-E initial cell, original alias-effect identity guard; old primary-reason order."
        },
        "input": {
          "path": "baseline-shape-probe-results/conductor/bidi/shapes/run1-shapes.json",
          "sha256": "e8480ce429204ae4c8e2a808a15793b51a6dcaacdbbc679d694dfd06a7f9b57f"
        },
        "manifest": {
          "path": "baseline-shape-probe-results/conductor/bidi/manifest.json",
          "sha256": "3951f18782122720dabb5f583bb44eda249ddb67720eacf659180e605caf2f62"
        },
        "summary": {
          "path": "baseline-shape-probe-results/conductor/bidi/summary.json",
          "sha256": "df3eabd153e7f8455d3c1b1eabf58747e3068fe7e89496492af700dafbea41d2"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "00:02:48.180 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=17m 1.692031116s markMode=FULL",
          "end_line": "00:03:17.447 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=29.267341348s",
          "barrier_line": "00:03:19.632 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=2.151842737s iterationTime=31.453163914s"
        },
        "accepted_forward_frontier": "00:03:19.398 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 11224, demand edges 72918 in 17417 method keys, left 41, record crossings 0, DEMAND 44, CONFIRMED 0, seeds 60, zero only 6241 (20777 edges)",
        "explicit_handoff_demand_patterns": 72918,
        "demand_method_keys": 17417,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "583 runtime normalizer unchanged: ANY-only, same-base identity arms retained by alias-effect guard",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
          "memory": "8g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
        "owners": {
          "raw": {
            "FLOW_memberships": 36815,
            "TAINT_memberships": 20236,
            "protected_memberships": 20,
            "protected_share": 0.0009883376161296698,
            "coverage": {
              "removable_now": 0,
              "protection_only": 0,
              "other": 20236
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0,
              "other": 1.0
            },
            "removal_events": {
              "covered_offer_rejections": 21207,
              "stored_compaction_memberships": 35
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 10721,
              "ALIAS_EFFECT_CLASS": 2492,
              "OUTPUT_TAIL_MISMATCH": 61,
              "NO_ANNOTATED_ANY_PREFIX": 680,
              "UNSUPPORTED_OUTPUT_TAIL": 622,
              "ZERO_INITIAL": 5639,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 6
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 10721,
              "ALIAS_EFFECT_CLASS": 2492,
              "OUTPUT_BASE_MISMATCH": 652,
              "OUTPUT_TAIL_MISMATCH": 500,
              "NO_ANNOTATED_ANY_PREFIX": 698,
              "UNSUPPORTED_OUTPUT_TAIL": 622,
              "ZERO_INITIAL": 5639,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 15
            },
            "TAINT_full_shape_histogram": {
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 3416,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 728,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1236,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2057,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 2951,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 7,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 745,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 622,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 624,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 417,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 112,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1279,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 47,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 46,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 247,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 13,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 22,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 79,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 9,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1182,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1179,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 1,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 358,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 493,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 2,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 109,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 95,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 9,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 2136,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 16142,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 3945,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 7275,
              "STAR->ANY|NS->S|DEMAND|depth=2": 1691,
              "STAR->ANY|S->NS|DEMAND|depth=1": 2630,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 2223,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 2580,
              "STAR->ANY|S->NS|DEMAND|depth=0": 234,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 72,
              "STAR->STAR|NS->S|DEMAND|depth=2": 20,
              "STAR->STAR|S->NS|DEMAND|depth=1": 2,
              "STAR->STAR|S->NS|DEMAND|depth=0": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 9785,
                "EXACT->ANY_TAINT": 1275,
                "EXACT->EXACT": 5300,
                "STAR->ANY": 3239,
                "STAR->EXACT": 637
              },
              "base_pairs": {
                "NS->NS": 5468,
                "NS->S": 1287,
                "S->NS": 7842,
                "Z->NS": 3424,
                "Z->S": 2215
              },
              "layers": {
                "DEMAND": 20236
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 13091,
                "diagonal": 7145
              },
              "flags": {
                "false": 20216,
                "true": 20
              },
              "output_depth": {
                "0": 9672,
                "1": 7141,
                "2": 3423
              },
              "output_bases": {
                "NS": 16734,
                "S": 3502
              },
              "protected_output_bases": {
                "NS": 20
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 14410,
                "STAR->STAR": 22405
              },
              "base_pairs": {
                "NS->NS": 32237,
                "NS->S": 1711,
                "S->NS": 2867
              },
              "layers": {
                "DEMAND": 16728,
                "NORMAL": 20087
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 21180,
                "1": 13924,
                "2": 1711
              },
              "output_bases": {
                "NS": 35104,
                "S": 1711
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=1)": 9534,
              "GroupId(value=2)": 3699,
              "GroupId(value=5)": 915,
              "GroupId(value=7)": 1323,
              "GroupId(value=4)": 1312,
              "GroupId(value=9)": 1279,
              "GroupId(value=6)": 699,
              "GroupId(value=0)": 776,
              "GroupId(value=8)": 699
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 2120,
              "diagonal_mark_rows": 3239,
              "scalar_concrete_rows": 6694
            },
            "protection_tree_counts": {
              "none": 9914,
              "full_structural_only": 9,
              "partial": 7,
              "full_identity": 3
            },
            "protection_tree_memberships": {
              "none": 20164,
              "full_structural_only": 9,
              "partial": 60,
              "full_identity": 3
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
                243
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#executeWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.String, java.lang.Integer, java.lang.String, org.conductoross.conductor.model.WorkflowSignalReturnStrategy, com.netflix.conductor.common.metadata.workflow.StartWorkflowRequest) [{}]",
                166
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                160
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminate(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.core.exception.TerminateWorkflowException) [{}]",
                157
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                145
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskSync(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                140
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.Integer, java.util.Map) [{}]",
                136
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#rerunWorkflow(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                126
              ],
              [
                "com.netflix.conductor.service.TaskServiceImpl#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                120
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                118
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, int, java.util.Map) [{}]",
                117
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#testWorkflow(com.netflix.conductor.common.run.WorkflowTestRequest) [{}]",
                114
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                113
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(java.lang.String) [{}]",
                106
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#rerun(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                103
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF(java.lang.String, java.lang.String, java.util.Map, java.util.Map, java.lang.String) [{}]",
                101
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskV2(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                100
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowMessageQueueResource#pushMessage(java.lang.String, java.util.Map) [{}]",
                99
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateRemove(java.lang.String, java.lang.String, boolean) [{}]",
                96
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
                93
              ]
            ],
            "top_fields": [
              [
                "NS:",
                9672
              ],
              [
                "S:<static>(com.netflix.conductor.sdk.workflow.executor.task.TaskContext)/TaskContext#TASK_CONTEXT_INHERITABLE_THREAD_LOCAL",
                610
              ],
              [
                "S:<static>(com.netflix.conductor.core.events.ScriptEvaluator)/ScriptEvaluator#SOURCE_CACHE",
                609
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#amqpConnection",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#retrySettings",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#subscriberReservedChannelPool",
                607
              ],
              [
                "NS:Iterable#Element",
                406
              ],
              [
                "NS:*",
                268
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.service.WorkflowService",
                216
              ],
              [
                "NS:SearchResult#results",
                195
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.core.execution.WorkflowExecutor",
                159
              ],
              [
                "NS:BaseStream#Element",
                150
              ],
              [
                "NS:Map#MapValue",
                112
              ],
              [
                "NS:WorkflowExecutorOps#workflowStatusListener",
                112
              ],
              [
                "NS:WorkflowServiceImpl#workflowExecutor",
                100
              ],
              [
                "NS:WorkflowExecutorOps#executionLockService",
                98
              ],
              [
                "NS:BulkResponse#bulkSuccessfulResults",
                92
              ],
              [
                "NS:TaskModel#reasonForIncompletion",
                91
              ],
              [
                "NS:WorkflowModel#tasks",
                86
              ],
              [
                "NS:Map#MapKey",
                84
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 36815,
            "TAINT_memberships": 20236,
            "protected_memberships": 20,
            "protected_share": 0.0009883376161296698,
            "coverage": {
              "removable_now": 0,
              "protection_only": 0,
              "other": 20236
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0,
              "other": 1.0
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 35
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 10721,
              "ALIAS_EFFECT_CLASS": 2492,
              "OUTPUT_TAIL_MISMATCH": 61,
              "NO_ANNOTATED_ANY_PREFIX": 680,
              "UNSUPPORTED_OUTPUT_TAIL": 622,
              "ZERO_INITIAL": 5639,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 6
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 10721,
              "ALIAS_EFFECT_CLASS": 2492,
              "OUTPUT_BASE_MISMATCH": 652,
              "OUTPUT_TAIL_MISMATCH": 500,
              "NO_ANNOTATED_ANY_PREFIX": 698,
              "UNSUPPORTED_OUTPUT_TAIL": 622,
              "ZERO_INITIAL": 5639,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 15
            },
            "TAINT_full_shape_histogram": {
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 3416,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 728,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1236,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2057,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 2951,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 7,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 745,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 622,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 624,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 417,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 112,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1279,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 47,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 46,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 247,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 13,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 22,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 79,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 9,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1182,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1179,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 1,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 358,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 493,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 2,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 109,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 95,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 9,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 2136,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 16142,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 3945,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 7275,
              "STAR->ANY|NS->S|DEMAND|depth=2": 1691,
              "STAR->ANY|S->NS|DEMAND|depth=1": 2630,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 2223,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 2580,
              "STAR->ANY|S->NS|DEMAND|depth=0": 234,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 72,
              "STAR->STAR|NS->S|DEMAND|depth=2": 20,
              "STAR->STAR|S->NS|DEMAND|depth=1": 2,
              "STAR->STAR|S->NS|DEMAND|depth=0": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 9785,
                "EXACT->ANY_TAINT": 1275,
                "EXACT->EXACT": 5300,
                "STAR->ANY": 3239,
                "STAR->EXACT": 637
              },
              "base_pairs": {
                "NS->NS": 5468,
                "NS->S": 1287,
                "S->NS": 7842,
                "Z->NS": 3424,
                "Z->S": 2215
              },
              "layers": {
                "DEMAND": 20236
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 13091,
                "diagonal": 7145
              },
              "flags": {
                "false": 20216,
                "true": 20
              },
              "output_depth": {
                "0": 9672,
                "1": 7141,
                "2": 3423
              },
              "output_bases": {
                "NS": 16734,
                "S": 3502
              },
              "protected_output_bases": {
                "NS": 20
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 14410,
                "STAR->STAR": 22405
              },
              "base_pairs": {
                "NS->NS": 32237,
                "NS->S": 1711,
                "S->NS": 2867
              },
              "layers": {
                "DEMAND": 16728,
                "NORMAL": 20087
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 21180,
                "1": 13924,
                "2": 1711
              },
              "output_bases": {
                "NS": 35104,
                "S": 1711
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=1)": 9534,
              "GroupId(value=2)": 3699,
              "GroupId(value=5)": 915,
              "GroupId(value=7)": 1323,
              "GroupId(value=4)": 1312,
              "GroupId(value=9)": 1279,
              "GroupId(value=6)": 699,
              "GroupId(value=0)": 776,
              "GroupId(value=8)": 699
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 2120,
              "diagonal_mark_rows": 3239,
              "scalar_concrete_rows": 6694
            },
            "protection_tree_counts": {
              "none": 9914,
              "full_structural_only": 9,
              "partial": 7,
              "full_identity": 3
            },
            "protection_tree_memberships": {
              "none": 20164,
              "full_structural_only": 9,
              "partial": 60,
              "full_identity": 3
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
                243
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#executeWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.String, java.lang.Integer, java.lang.String, org.conductoross.conductor.model.WorkflowSignalReturnStrategy, com.netflix.conductor.common.metadata.workflow.StartWorkflowRequest) [{}]",
                166
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                160
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminate(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.core.exception.TerminateWorkflowException) [{}]",
                157
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                145
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskSync(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                140
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.Integer, java.util.Map) [{}]",
                136
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#rerunWorkflow(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                126
              ],
              [
                "com.netflix.conductor.service.TaskServiceImpl#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                120
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                118
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, int, java.util.Map) [{}]",
                117
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#testWorkflow(com.netflix.conductor.common.run.WorkflowTestRequest) [{}]",
                114
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                113
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(java.lang.String) [{}]",
                106
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#rerun(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                103
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF(java.lang.String, java.lang.String, java.util.Map, java.util.Map, java.lang.String) [{}]",
                101
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskV2(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                100
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowMessageQueueResource#pushMessage(java.lang.String, java.util.Map) [{}]",
                99
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateRemove(java.lang.String, java.lang.String, boolean) [{}]",
                96
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
                93
              ]
            ],
            "top_fields": [
              [
                "NS:",
                9672
              ],
              [
                "S:<static>(com.netflix.conductor.sdk.workflow.executor.task.TaskContext)/TaskContext#TASK_CONTEXT_INHERITABLE_THREAD_LOCAL",
                610
              ],
              [
                "S:<static>(com.netflix.conductor.core.events.ScriptEvaluator)/ScriptEvaluator#SOURCE_CACHE",
                609
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#amqpConnection",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#retrySettings",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#subscriberReservedChannelPool",
                607
              ],
              [
                "NS:Iterable#Element",
                406
              ],
              [
                "NS:*",
                268
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.service.WorkflowService",
                216
              ],
              [
                "NS:SearchResult#results",
                195
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.core.execution.WorkflowExecutor",
                159
              ],
              [
                "NS:BaseStream#Element",
                150
              ],
              [
                "NS:Map#MapValue",
                112
              ],
              [
                "NS:WorkflowExecutorOps#workflowStatusListener",
                112
              ],
              [
                "NS:WorkflowServiceImpl#workflowExecutor",
                100
              ],
              [
                "NS:WorkflowExecutorOps#executionLockService",
                98
              ],
              [
                "NS:BulkResponse#bulkSuccessfulResults",
                92
              ],
              [
                "NS:TaskModel#reasonForIncompletion",
                91
              ],
              [
                "NS:WorkflowModel#tasks",
                86
              ],
              [
                "NS:Map#MapKey",
                84
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 21207,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-cold-actors-v1",
          "totals": {
            "scalar_headers": 6635946,
            "packed_invocations": 41079,
            "packed_mark_credits": 43246,
            "physical_method_edge_invocations": 6677025
          },
          "actor_totals": {
            "actors": 17465,
            "steps": 6679192,
            "neutralBatchApplications": 41079,
            "neutralBatchMemberships": 43246
          },
          "top_methods": [
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
              "step_credits": 290837,
              "scalar_headers": 288088,
              "packed_invocations": 2709,
              "packed_mark_credits": 2749,
              "physical_method_edge_invocations": 290797
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#decide(com.netflix.conductor.model.WorkflowModel, java.util.List) [{arg(1) == java.util.LinkedList}]",
              "step_credits": 274780,
              "scalar_headers": 273906,
              "packed_invocations": 815,
              "packed_mark_credits": 874,
              "physical_method_edge_invocations": 274721
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
              "step_credits": 204266,
              "scalar_headers": 201984,
              "packed_invocations": 2261,
              "packed_mark_credits": 2282,
              "physical_method_edge_invocations": 204245
            },
            {
              "method": "org.conductoross.conductor.ai.tasks.mapper.ChatCompleteTaskMapper#getHistory(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, org.conductoross.conductor.ai.models.ChatCompletion) [{}]",
              "step_credits": 174908,
              "scalar_headers": 174908,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 174908
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowTask) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 143877,
              "scalar_headers": 143877,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 143877
            },
            {
              "method": "com.netflix.conductor.proto.TaskPb$Task$Builder#mergeFrom(com.netflix.conductor.proto.TaskPb$Task) [{}]",
              "step_credits": 143696,
              "scalar_headers": 143696,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 143696
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF(java.lang.String, java.lang.String, java.util.Map, java.util.Map, java.lang.String) [{}]",
              "step_credits": 142385,
              "scalar_headers": 140504,
              "packed_invocations": 1729,
              "packed_mark_credits": 1881,
              "physical_method_edge_invocations": 142233
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowTask) [{}]",
              "step_credits": 131725,
              "scalar_headers": 131725,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 131725
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.tasks.Task) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 130248,
              "scalar_headers": 130248,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 130248
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.tasks.Task) [{}]",
              "step_credits": 128198,
              "scalar_headers": 128198,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 128198
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
              "step_credits": 127100,
              "scalar_headers": 125545,
              "packed_invocations": 1500,
              "packed_mark_credits": 1555,
              "physical_method_edge_invocations": 127045
            },
            {
              "method": "com.netflix.conductor.proto.WorkflowTaskPb$WorkflowTask$Builder#mergeFrom(com.netflix.conductor.proto.WorkflowTaskPb$WorkflowTask) [{}]",
              "step_credits": 116759,
              "scalar_headers": 116759,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116759
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#scheduleTask(com.netflix.conductor.model.WorkflowModel, java.util.List) [{}]",
              "step_credits": 94508,
              "scalar_headers": 93086,
              "packed_invocations": 1324,
              "packed_mark_credits": 1422,
              "physical_method_edge_invocations": 94410
            },
            {
              "method": "com.netflix.conductor.core.execution.AsyncSystemTaskExecutor#execute(com.netflix.conductor.core.execution.tasks.WorkflowSystemTask, java.lang.String) [{}]",
              "step_credits": 92445,
              "scalar_headers": 91456,
              "packed_invocations": 989,
              "packed_mark_credits": 989,
              "physical_method_edge_invocations": 92445
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.DoWhile#execute(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{arg(2) is com.netflix.conductor.core.execution.WorkflowExecutorOps}]",
              "step_credits": 92382,
              "scalar_headers": 91477,
              "packed_invocations": 797,
              "packed_mark_credits": 905,
              "physical_method_edge_invocations": 92274
            },
            {
              "method": "com.netflix.conductor.core.execution.mapper.ForkJoinDynamicTaskMapper#getMappedTasks(com.netflix.conductor.core.execution.mapper.TaskMapperContext) [{}]",
              "step_credits": 76529,
              "scalar_headers": 75967,
              "packed_invocations": 562,
              "packed_mark_credits": 562,
              "physical_method_edge_invocations": 76529
            },
            {
              "method": "io.orkes.conductor.scheduler.service.SchedulerService#handleSchedules(java.util.List) [{}]",
              "step_credits": 74048,
              "scalar_headers": 73959,
              "packed_invocations": 89,
              "packed_mark_credits": 89,
              "physical_method_edge_invocations": 74048
            },
            {
              "method": "com.netflix.conductor.rest.controllers.WorkflowResource#findBlockingTasks(com.netflix.conductor.model.WorkflowModel, java.lang.String[]) [{}]",
              "step_credits": 63802,
              "scalar_headers": 63093,
              "packed_invocations": 708,
              "packed_mark_credits": 709,
              "physical_method_edge_invocations": 63801
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.SubWorkflow#start(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{arg(2) is com.netflix.conductor.core.execution.WorkflowExecutorOps}]",
              "step_credits": 57140,
              "scalar_headers": 56654,
              "packed_invocations": 486,
              "packed_mark_credits": 486,
              "physical_method_edge_invocations": 57140
            },
            {
              "method": "com.netflix.conductor.service.ExecutionService#poll(java.lang.String, java.lang.String, java.lang.String, int, int) [{}]",
              "step_credits": 54248,
              "scalar_headers": 54119,
              "packed_invocations": 129,
              "packed_mark_credits": 129,
              "physical_method_edge_invocations": 54248
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowDef) [{}]",
              "step_credits": 53229,
              "scalar_headers": 53229,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 53229
            },
            {
              "method": "org.conductoross.conductor.core.execution.WorkflowSweeper#sweep(java.lang.String) [{}]",
              "step_credits": 51640,
              "scalar_headers": 51292,
              "packed_invocations": 348,
              "packed_mark_credits": 348,
              "physical_method_edge_invocations": 51640
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowDef) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 48509,
              "scalar_headers": 48509,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 48509
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 47672,
              "scalar_headers": 47672,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 47672
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#cancelNonTerminalTasks(com.netflix.conductor.model.WorkflowModel, boolean) [{}]",
              "step_credits": 47061,
              "scalar_headers": 46210,
              "packed_invocations": 831,
              "packed_mark_credits": 851,
              "physical_method_edge_invocations": 47041
            },
            {
              "method": "org.conductoross.conductor.ai.LLMHelper#chatComplete(org.springframework.ai.chat.model.ChatModel, org.springframework.ai.chat.prompt.ChatOptions, org.conductoross.conductor.ai.models.ChatCompletion) [{}]",
              "step_credits": 41131,
              "scalar_headers": 41084,
              "packed_invocations": 47,
              "packed_mark_credits": 47,
              "physical_method_edge_invocations": 41131
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.DoWhile#execute(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{}]",
              "step_credits": 41089,
              "scalar_headers": 40902,
              "packed_invocations": 187,
              "packed_mark_credits": 187,
              "physical_method_edge_invocations": 41089
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.SubWorkflow#start(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{}]",
              "step_credits": 40033,
              "scalar_headers": 39827,
              "packed_invocations": 206,
              "packed_mark_credits": 206,
              "physical_method_edge_invocations": 40033
            },
            {
              "method": "com.netflix.conductor.proto.TaskPb$Task$Builder#buildPartial0(com.netflix.conductor.proto.TaskPb$Task) [{}]",
              "step_credits": 39681,
              "scalar_headers": 39681,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 39681
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{}]",
              "step_credits": 38695,
              "scalar_headers": 38695,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 38695
            },
            {
              "method": "com.netflix.conductor.proto.WorkflowDefPb$WorkflowDef$Builder#mergeFrom(com.netflix.conductor.proto.WorkflowDefPb$WorkflowDef) [{}]",
              "step_credits": 37361,
              "scalar_headers": 37361,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 37361
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateAndPushParents(com.netflix.conductor.model.WorkflowModel, java.lang.String) [{}]",
              "step_credits": 37143,
              "scalar_headers": 36699,
              "packed_invocations": 436,
              "packed_mark_credits": 444,
              "physical_method_edge_invocations": 37135
            },
            {
              "method": "com.netflix.conductor.proto.TaskDefPb$TaskDef$Builder#mergeFrom(com.netflix.conductor.proto.TaskDefPb$TaskDef) [{}]",
              "step_credits": 36160,
              "scalar_headers": 36160,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 36160
            },
            {
              "method": "org.conductoross.conductor.ai.pdf.PdfDocumentRenderer#renderTextRunsWithOffset(java.util.List, float, float) [{}]",
              "step_credits": 35148,
              "scalar_headers": 35148,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 35148
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#retry(com.netflix.conductor.model.WorkflowModel) [{}]",
              "step_credits": 34382,
              "scalar_headers": 33851,
              "packed_invocations": 497,
              "packed_mark_credits": 531,
              "physical_method_edge_invocations": 34348
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#restart(java.lang.String, boolean) [{}]",
              "step_credits": 32064,
              "scalar_headers": 31302,
              "packed_invocations": 752,
              "packed_mark_credits": 762,
              "physical_method_edge_invocations": 32054
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.LinkedHashMap} & {arg(2) == java.util.ArrayList}]",
              "step_credits": 31494,
              "scalar_headers": 31280,
              "packed_invocations": 214,
              "packed_mark_credits": 214,
              "physical_method_edge_invocations": 31494
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.ArrayList} & {arg(2) == java.util.ArrayList}]",
              "step_credits": 31214,
              "scalar_headers": 31000,
              "packed_invocations": 214,
              "packed_mark_credits": 214,
              "physical_method_edge_invocations": 31214
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.ArrayList} & {arg(2) == java.util.LinkedHashMap}]",
              "step_credits": 31168,
              "scalar_headers": 30954,
              "packed_invocations": 214,
              "packed_mark_credits": 214,
              "physical_method_edge_invocations": 31168
            },
            {
              "method": "com.netflix.conductor.core.events.SimpleActionProcessor#completeTask(com.netflix.conductor.common.metadata.events.EventHandler$Action, java.lang.Object, com.netflix.conductor.common.metadata.events.EventHandler$TaskDetails, com.netflix.conductor.model.TaskModel$Status, java.lang.String, java.lang.String) [{}]",
              "step_credits": 31011,
              "scalar_headers": 30831,
              "packed_invocations": 180,
              "packed_mark_credits": 180,
              "physical_method_edge_invocations": 31011
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 29.267341348
      },
      "after": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "shape-probe-results",
          "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
          "core": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
          "checker": "correlated-star-any-v1",
          "policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order."
        },
        "input": {
          "path": "shape-probe-results/conductor/bidi/shapes/run1-shapes.json",
          "sha256": "9576fc6ad578b1bfd1557653ca2095b86d941059beacdefd85f34e688f19f0a3"
        },
        "manifest": {
          "path": "shape-probe-results/conductor/bidi/manifest.json",
          "sha256": "c7db5b79b5b829fb89f839cde8c68ba80404466857f0582ed72c8f1a06616f02"
        },
        "summary": {
          "path": "shape-probe-results/conductor/bidi/summary.json",
          "sha256": "7c8753bf19392ddcc95d76df0a7c6fd1ec933b53eb5da2df4dac35ca19c8550a"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "22:02:15.042 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=17m 4.882771931s markMode=FULL",
          "end_line": "22:02:42.040 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=26.999125953s",
          "barrier_line": "22:02:45.024 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=2.956081669s iterationTime=29.983165182s"
        },
        "accepted_forward_frontier": "22:02:44.778 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 11224, demand edges 69644 in 17417 method keys, left 41, record crossings 0, DEMAND 44, CONFIRMED 0, seeds 60, zero only 6241 (20447 edges)",
        "explicit_handoff_demand_patterns": 69644,
        "demand_method_keys": 17417,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order.",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
          "memory": "8g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
        "owners": {
          "raw": {
            "FLOW_memberships": 36751,
            "TAINT_memberships": 16750,
            "protected_memberships": 22,
            "protected_share": 0.0013134328358208956,
            "coverage": {
              "removable_now": 0,
              "protection_only": 1,
              "other": 16749
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 5.9701492537313435e-05,
              "other": 0.9999402985074627
            },
            "removal_events": {
              "covered_offer_rejections": 28733,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 10679,
              "UNSUPPORTED_OUTPUT": 622,
              "ZERO_INITIAL": 5420,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 13
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 10679,
              "UNSUPPORTED_OUTPUT": 622,
              "ZERO_INITIAL": 5420,
              "CROSS_ATOM": 15,
              "OUTPUT_BASE_MISMATCH": 13,
              "STAR_PATH_INEQUALITY": 6,
              "MARK_EXCLUDED": 13,
              "OUTPUT_TAIL_MISMATCH": 7
            },
            "TAINT_full_shape_histogram": {
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 3633,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 660,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1251,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2059,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 903,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 694,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 417,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 181,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 112,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1279,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 47,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 46,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 18,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 79,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 6,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1186,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1183,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 1,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 491,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 133,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 2,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 109,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 95,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 9,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 2136,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 3
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 16142,
              "STAR->ANY|NS->S|DEMAND|depth=2": 1626,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 7263,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 3945,
              "STAR->ANY|S->NS|DEMAND|depth=1": 2642,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 2223,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 2580,
              "STAR->ANY|S->NS|DEMAND|depth=0": 234,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 73,
              "STAR->STAR|NS->S|DEMAND|depth=2": 20,
              "STAR->STAR|S->NS|DEMAND|depth=1": 2,
              "STAR->STAR|S->NS|DEMAND|depth=0": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 9422,
                "EXACT->ANY_TAINT": 1279,
                "EXACT->EXACT": 5398,
                "STAR->ANY": 6,
                "STAR->EXACT": 637,
                "STAR->STAR": 8
              },
              "base_pairs": {
                "NS->NS": 2289,
                "NS->S": 1280,
                "S->NS": 7761,
                "Z->NS": 3205,
                "Z->S": 2215
              },
              "layers": {
                "DEMAND": 16750
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 13038,
                "diagonal": 3712
              },
              "flags": {
                "false": 16728,
                "true": 22
              },
              "output_depth": {
                "0": 5835,
                "1": 7499,
                "2": 3416
              },
              "output_bases": {
                "NS": 13255,
                "S": 3495
              },
              "protected_output_bases": {
                "NS": 22
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 14345,
                "STAR->STAR": 22406
              },
              "base_pairs": {
                "NS->NS": 32226,
                "NS->S": 1646,
                "S->NS": 2879
              },
              "layers": {
                "DEMAND": 16664,
                "NORMAL": 20087
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 21180,
                "1": 13925,
                "2": 1646
              },
              "output_bases": {
                "NS": 35105,
                "S": 1646
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=1)": 9051,
              "GroupId(value=2)": 1810,
              "GroupId(value=7)": 1029,
              "GroupId(value=4)": 1035,
              "GroupId(value=9)": 1029,
              "GroupId(value=5)": 630,
              "GroupId(value=6)": 699,
              "GroupId(value=0)": 768,
              "GroupId(value=8)": 699
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 14,
              "diagonal_mark_rows": 14,
              "scalar_concrete_rows": 6364
            },
            "protection_tree_counts": {
              "none": 6357,
              "full_structural_only": 9,
              "partial": 7,
              "full_identity": 5
            },
            "protection_tree_memberships": {
              "none": 16676,
              "full_structural_only": 9,
              "partial": 60,
              "full_identity": 5
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
                210
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#executeWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.String, java.lang.Integer, java.lang.String, org.conductoross.conductor.model.WorkflowSignalReturnStrategy, com.netflix.conductor.common.metadata.workflow.StartWorkflowRequest) [{}]",
                161
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskSync(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                139
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                132
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                117
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.Integer, java.util.Map) [{}]",
                115
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminate(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.core.exception.TerminateWorkflowException) [{}]",
                110
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                110
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#testWorkflow(com.netflix.conductor.common.run.WorkflowTestRequest) [{}]",
                108
              ],
              [
                "com.netflix.conductor.service.TaskServiceImpl#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                107
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, int, java.util.Map) [{}]",
                103
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskV2(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                100
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowMessageQueueResource#pushMessage(java.lang.String, java.util.Map) [{}]",
                95
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#rerun(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                94
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#rerunWorkflow(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                92
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
                87
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                87
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#skipTaskFromWorkflow(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.workflow.SkipTaskRequest) [{}]",
                86
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#getExternalStorageLocation(java.lang.String, java.lang.String, java.lang.String) [{}]",
                83
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                83
              ]
            ],
            "top_fields": [
              [
                "NS:",
                5835
              ],
              [
                "S:<static>(com.netflix.conductor.sdk.workflow.executor.task.TaskContext)/TaskContext#TASK_CONTEXT_INHERITABLE_THREAD_LOCAL",
                610
              ],
              [
                "S:<static>(com.netflix.conductor.core.events.ScriptEvaluator)/ScriptEvaluator#SOURCE_CACHE",
                609
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#amqpConnection",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#retrySettings",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#subscriberReservedChannelPool",
                607
              ],
              [
                "NS:Iterable#Element",
                407
              ],
              [
                "NS:*",
                268
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.service.WorkflowService",
                216
              ],
              [
                "NS:SearchResult#results",
                195
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.core.execution.WorkflowExecutor",
                159
              ],
              [
                "NS:BaseStream#Element",
                150
              ],
              [
                "NS:WorkflowExecutorOps#workflowStatusListener",
                147
              ],
              [
                "NS:WorkflowExecutorOps#executionLockService",
                128
              ],
              [
                "NS:WorkflowExecutorOps#taskStatusListener",
                128
              ],
              [
                "NS:Map#MapValue",
                112
              ],
              [
                "NS:WorkflowModel#status",
                107
              ],
              [
                "NS:WorkflowModel#tasks",
                104
              ],
              [
                "NS:WorkflowServiceImpl#workflowExecutor",
                100
              ],
              [
                "NS:WorkflowModel#reasonForIncompletion",
                95
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 36751,
            "TAINT_memberships": 16750,
            "protected_memberships": 22,
            "protected_share": 0.0013134328358208956,
            "coverage": {
              "removable_now": 0,
              "protection_only": 1,
              "other": 16749
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 5.9701492537313435e-05,
              "other": 0.9999402985074627
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "UNSUPPORTED_INITIAL": 10679,
              "UNSUPPORTED_OUTPUT": 622,
              "ZERO_INITIAL": 5420,
              "CROSS_ATOM": 15,
              "MARK_EXCLUDED": 13
            },
            "secondary_failures_nonadditive": {
              "UNSUPPORTED_INITIAL": 10679,
              "UNSUPPORTED_OUTPUT": 622,
              "ZERO_INITIAL": 5420,
              "CROSS_ATOM": 15,
              "OUTPUT_BASE_MISMATCH": 13,
              "STAR_PATH_INEQUALITY": 6,
              "MARK_EXCLUDED": 13,
              "OUTPUT_TAIL_MISMATCH": 7
            },
            "TAINT_full_shape_histogram": {
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 3633,
              "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 660,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1251,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2059,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 903,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 694,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 417,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 181,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0": 112,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 1279,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 47,
              "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1": 46,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 18,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 79,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 6,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1186,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1183,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 1,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 491,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 133,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 2,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 109,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 95,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 9,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 3,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 2136,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 1,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 3
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 16142,
              "STAR->ANY|NS->S|DEMAND|depth=2": 1626,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 7263,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 3945,
              "STAR->ANY|S->NS|DEMAND|depth=1": 2642,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 2223,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 2580,
              "STAR->ANY|S->NS|DEMAND|depth=0": 234,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 73,
              "STAR->STAR|NS->S|DEMAND|depth=2": 20,
              "STAR->STAR|S->NS|DEMAND|depth=1": 2,
              "STAR->STAR|S->NS|DEMAND|depth=0": 1
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 9422,
                "EXACT->ANY_TAINT": 1279,
                "EXACT->EXACT": 5398,
                "STAR->ANY": 6,
                "STAR->EXACT": 637,
                "STAR->STAR": 8
              },
              "base_pairs": {
                "NS->NS": 2289,
                "NS->S": 1280,
                "S->NS": 7761,
                "Z->NS": 3205,
                "Z->S": 2215
              },
              "layers": {
                "DEMAND": 16750
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 13038,
                "diagonal": 3712
              },
              "flags": {
                "false": 16728,
                "true": 22
              },
              "output_depth": {
                "0": 5835,
                "1": 7499,
                "2": 3416
              },
              "output_bases": {
                "NS": 13255,
                "S": 3495
              },
              "protected_output_bases": {
                "NS": 22
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 14345,
                "STAR->STAR": 22406
              },
              "base_pairs": {
                "NS->NS": 32226,
                "NS->S": 1646,
                "S->NS": 2879
              },
              "layers": {
                "DEMAND": 16664,
                "NORMAL": 20087
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 21180,
                "1": 13925,
                "2": 1646
              },
              "output_bases": {
                "NS": 35105,
                "S": 1646
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=1)": 9051,
              "GroupId(value=2)": 1810,
              "GroupId(value=7)": 1029,
              "GroupId(value=4)": 1035,
              "GroupId(value=9)": 1029,
              "GroupId(value=5)": 630,
              "GroupId(value=6)": 699,
              "GroupId(value=0)": 768,
              "GroupId(value=8)": 699
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 14,
              "diagonal_mark_rows": 14,
              "scalar_concrete_rows": 6364
            },
            "protection_tree_counts": {
              "none": 6357,
              "full_structural_only": 9,
              "partial": 7,
              "full_identity": 5
            },
            "protection_tree_memberships": {
              "none": 16676,
              "full_structural_only": 9,
              "partial": 60,
              "full_identity": 5
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
                210
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#executeWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.String, java.lang.Integer, java.lang.String, org.conductoross.conductor.model.WorkflowSignalReturnStrategy, com.netflix.conductor.common.metadata.workflow.StartWorkflowRequest) [{}]",
                161
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskSync(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                139
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                132
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                117
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, java.lang.Integer, java.util.Map) [{}]",
                115
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminate(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.core.exception.TerminateWorkflowException) [{}]",
                110
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                110
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#testWorkflow(com.netflix.conductor.common.run.WorkflowTestRequest) [{}]",
                108
              ],
              [
                "com.netflix.conductor.service.TaskServiceImpl#updateTask(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.tasks.TaskResult$Status, java.lang.String, java.util.Map) [{}]",
                107
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#startWorkflow(java.lang.String, java.lang.Integer, java.lang.String, int, java.util.Map) [{}]",
                103
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTaskV2(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                100
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowMessageQueueResource#pushMessage(java.lang.String, java.util.Map) [{}]",
                95
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#rerun(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                94
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#rerunWorkflow(java.lang.String, com.netflix.conductor.common.metadata.workflow.RerunWorkflowRequest) [{}]",
                92
              ],
              [
                "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
                87
              ],
              [
                "com.netflix.conductor.service.WorkflowServiceImpl#terminateWorkflow(java.lang.String, java.lang.String) [{}]",
                87
              ],
              [
                "com.netflix.conductor.rest.controllers.WorkflowResource#skipTaskFromWorkflow(java.lang.String, java.lang.String, com.netflix.conductor.common.metadata.workflow.SkipTaskRequest) [{}]",
                86
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#getExternalStorageLocation(java.lang.String, java.lang.String, java.lang.String) [{}]",
                83
              ],
              [
                "com.netflix.conductor.rest.controllers.TaskResource#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
                83
              ]
            ],
            "top_fields": [
              [
                "NS:",
                5835
              ],
              [
                "S:<static>(com.netflix.conductor.sdk.workflow.executor.task.TaskContext)/TaskContext#TASK_CONTEXT_INHERITABLE_THREAD_LOCAL",
                610
              ],
              [
                "S:<static>(com.netflix.conductor.core.events.ScriptEvaluator)/ScriptEvaluator#SOURCE_CACHE",
                609
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#amqpConnection",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#retrySettings",
                607
              ],
              [
                "S:<static>(com.netflix.conductor.contribs.queue.amqp.AMQPConnection)/AMQPConnection#subscriberReservedChannelPool",
                607
              ],
              [
                "NS:Iterable#Element",
                407
              ],
              [
                "NS:*",
                268
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.service.WorkflowService",
                216
              ],
              [
                "NS:SearchResult#results",
                195
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#com.netflix.conductor.core.execution.WorkflowExecutor",
                159
              ],
              [
                "NS:BaseStream#Element",
                150
              ],
              [
                "NS:WorkflowExecutorOps#workflowStatusListener",
                147
              ],
              [
                "NS:WorkflowExecutorOps#executionLockService",
                128
              ],
              [
                "NS:WorkflowExecutorOps#taskStatusListener",
                128
              ],
              [
                "NS:Map#MapValue",
                112
              ],
              [
                "NS:WorkflowModel#status",
                107
              ],
              [
                "NS:WorkflowModel#tasks",
                104
              ],
              [
                "NS:WorkflowServiceImpl#workflowExecutor",
                100
              ],
              [
                "NS:WorkflowModel#reasonForIncompletion",
                95
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 28733,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-v2",
          "totals": {
            "scalar_headers": 6609819,
            "packed_invocations": 42373,
            "packed_mark_credits": 44206,
            "resume_events": 16767,
            "physical_method_edge_invocations": 6652192,
            "statement_untouched_from_process": 3654116,
            "statement_pure_untouched_from_process": 2915724,
            "statement_untouched_from_resume": 0,
            "statement_pure_untouched_from_resume": 0,
            "packed_untouched_callbacks": 36783,
            "packed_untouched_mark_credits": 38421,
            "scalar_taint_headers": 3291538,
            "scalar_fully_protected_identity_headers": 283,
            "packed_fully_protected_identity_invocations": 41,
            "packed_fully_protected_identity_mark_credits": 41,
            "resume_taint_headers": 15197,
            "resume_fully_protected_identity_headers": 0
          },
          "actor_totals": {
            "actors": 17465,
            "steps": 6654025,
            "neutralBatchApplications": 42373,
            "neutralBatchMemberships": 44206
          },
          "top_methods": [
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#decide(com.netflix.conductor.model.WorkflowModel) [{}]",
              "step_credits": 288841,
              "scalar_headers": 285929,
              "packed_invocations": 2882,
              "packed_mark_credits": 2912,
              "physical_method_edge_invocations": 288811,
              "edge_delta_credits": 10644,
              "neutral_scalar_store_fallback_credits": 236
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#decide(com.netflix.conductor.model.WorkflowModel, java.util.List) [{arg(1) == java.util.LinkedList}]",
              "step_credits": 278193,
              "scalar_headers": 277262,
              "packed_invocations": 834,
              "packed_mark_credits": 931,
              "physical_method_edge_invocations": 278096,
              "edge_delta_credits": 3542,
              "neutral_scalar_store_fallback_credits": 6
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#terminateWorkflow(com.netflix.conductor.model.WorkflowModel, java.lang.String, java.lang.String) [{}]",
              "step_credits": 209429,
              "scalar_headers": 206280,
              "packed_invocations": 3130,
              "packed_mark_credits": 3149,
              "physical_method_edge_invocations": 209410,
              "edge_delta_credits": 14432,
              "neutral_scalar_store_fallback_credits": 16
            },
            {
              "method": "org.conductoross.conductor.ai.tasks.mapper.ChatCompleteTaskMapper#getHistory(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, org.conductoross.conductor.ai.models.ChatCompletion) [{}]",
              "step_credits": 168590,
              "scalar_headers": 168590,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 168590,
              "edge_delta_credits": 1283,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowTask) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 143988,
              "scalar_headers": 143988,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 143988,
              "edge_delta_credits": 3116,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.proto.TaskPb$Task$Builder#mergeFrom(com.netflix.conductor.proto.TaskPb$Task) [{}]",
              "step_credits": 143696,
              "scalar_headers": 143696,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 143696,
              "edge_delta_credits": 3979,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowTask) [{}]",
              "step_credits": 132413,
              "scalar_headers": 132413,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 132413,
              "edge_delta_credits": 3096,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#rerunWF(java.lang.String, java.lang.String, java.util.Map, java.util.Map, java.lang.String) [{}]",
              "step_credits": 131300,
              "scalar_headers": 129398,
              "packed_invocations": 1775,
              "packed_mark_credits": 1902,
              "physical_method_edge_invocations": 131173,
              "edge_delta_credits": 7410,
              "neutral_scalar_store_fallback_credits": 34
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.tasks.Task) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 130451,
              "scalar_headers": 130451,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 130451,
              "edge_delta_credits": 3707,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.tasks.Task) [{}]",
              "step_credits": 128957,
              "scalar_headers": 128957,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 128957,
              "edge_delta_credits": 3559,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateTask(com.netflix.conductor.common.metadata.tasks.TaskResult) [{}]",
              "step_credits": 127931,
              "scalar_headers": 126333,
              "packed_invocations": 1545,
              "packed_mark_credits": 1598,
              "physical_method_edge_invocations": 127878,
              "edge_delta_credits": 8182,
              "neutral_scalar_store_fallback_credits": 30
            },
            {
              "method": "com.netflix.conductor.proto.WorkflowTaskPb$WorkflowTask$Builder#mergeFrom(com.netflix.conductor.proto.WorkflowTaskPb$WorkflowTask) [{}]",
              "step_credits": 116759,
              "scalar_headers": 116759,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116759,
              "edge_delta_credits": 4925,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.AsyncSystemTaskExecutor#execute(com.netflix.conductor.core.execution.tasks.WorkflowSystemTask, java.lang.String) [{}]",
              "step_credits": 95432,
              "scalar_headers": 94168,
              "packed_invocations": 1264,
              "packed_mark_credits": 1264,
              "physical_method_edge_invocations": 95432,
              "edge_delta_credits": 4907,
              "neutral_scalar_store_fallback_credits": 32
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.DoWhile#execute(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{arg(2) is com.netflix.conductor.core.execution.WorkflowExecutorOps}]",
              "step_credits": 92086,
              "scalar_headers": 91245,
              "packed_invocations": 835,
              "packed_mark_credits": 841,
              "physical_method_edge_invocations": 92080,
              "edge_delta_credits": 2506,
              "neutral_scalar_store_fallback_credits": 6
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#scheduleTask(com.netflix.conductor.model.WorkflowModel, java.util.List) [{}]",
              "step_credits": 88451,
              "scalar_headers": 87074,
              "packed_invocations": 1296,
              "packed_mark_credits": 1377,
              "physical_method_edge_invocations": 88370,
              "edge_delta_credits": 3228,
              "neutral_scalar_store_fallback_credits": 66
            },
            {
              "method": "com.netflix.conductor.core.execution.mapper.ForkJoinDynamicTaskMapper#getMappedTasks(com.netflix.conductor.core.execution.mapper.TaskMapperContext) [{}]",
              "step_credits": 80917,
              "scalar_headers": 80341,
              "packed_invocations": 543,
              "packed_mark_credits": 576,
              "physical_method_edge_invocations": 80884,
              "edge_delta_credits": 2096,
              "neutral_scalar_store_fallback_credits": 28
            },
            {
              "method": "io.orkes.conductor.scheduler.service.SchedulerService#handleSchedules(java.util.List) [{}]",
              "step_credits": 72858,
              "scalar_headers": 72761,
              "packed_invocations": 97,
              "packed_mark_credits": 97,
              "physical_method_edge_invocations": 72858,
              "edge_delta_credits": 902,
              "neutral_scalar_store_fallback_credits": 1
            },
            {
              "method": "com.netflix.conductor.rest.controllers.WorkflowResource#findBlockingTasks(com.netflix.conductor.model.WorkflowModel, java.lang.String[]) [{}]",
              "step_credits": 67848,
              "scalar_headers": 67027,
              "packed_invocations": 820,
              "packed_mark_credits": 821,
              "physical_method_edge_invocations": 67847,
              "edge_delta_credits": 1742,
              "neutral_scalar_store_fallback_credits": 66
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.SubWorkflow#start(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{arg(2) is com.netflix.conductor.core.execution.WorkflowExecutorOps}]",
              "step_credits": 57167,
              "scalar_headers": 56690,
              "packed_invocations": 477,
              "packed_mark_credits": 477,
              "physical_method_edge_invocations": 57167,
              "edge_delta_credits": 2270,
              "neutral_scalar_store_fallback_credits": 12
            },
            {
              "method": "com.netflix.conductor.service.ExecutionService#poll(java.lang.String, java.lang.String, java.lang.String, int, int) [{}]",
              "step_credits": 53777,
              "scalar_headers": 53649,
              "packed_invocations": 128,
              "packed_mark_credits": 128,
              "physical_method_edge_invocations": 53777,
              "edge_delta_credits": 926,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowDef) [{}]",
              "step_credits": 51903,
              "scalar_headers": 51903,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 51903,
              "edge_delta_credits": 1482,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.conductoross.conductor.core.execution.WorkflowSweeper#sweep(java.lang.String) [{}]",
              "step_credits": 49611,
              "scalar_headers": 49312,
              "packed_invocations": 299,
              "packed_mark_credits": 299,
              "physical_method_edge_invocations": 49611,
              "edge_delta_credits": 1543,
              "neutral_scalar_store_fallback_credits": 80
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{}]",
              "step_credits": 48084,
              "scalar_headers": 48084,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 48084,
              "edge_delta_credits": 1572,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.metadata.workflow.WorkflowDef) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 47586,
              "scalar_headers": 47586,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 47586,
              "edge_delta_credits": 1414,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#cancelNonTerminalTasks(com.netflix.conductor.model.WorkflowModel, boolean) [{}]",
              "step_credits": 40857,
              "scalar_headers": 40068,
              "packed_invocations": 789,
              "packed_mark_credits": 789,
              "physical_method_edge_invocations": 40857,
              "edge_delta_credits": 2047,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.conductoross.conductor.ai.LLMHelper#chatComplete(org.springframework.ai.chat.model.ChatModel, org.springframework.ai.chat.prompt.ChatOptions, org.conductoross.conductor.ai.models.ChatCompletion) [{}]",
              "step_credits": 40853,
              "scalar_headers": 40806,
              "packed_invocations": 47,
              "packed_mark_credits": 47,
              "physical_method_edge_invocations": 40853,
              "edge_delta_credits": 555,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.DoWhile#execute(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{}]",
              "step_credits": 40775,
              "scalar_headers": 40621,
              "packed_invocations": 154,
              "packed_mark_credits": 154,
              "physical_method_edge_invocations": 40775,
              "edge_delta_credits": 1228,
              "neutral_scalar_store_fallback_credits": 1
            },
            {
              "method": "com.netflix.conductor.core.execution.tasks.SubWorkflow#start(com.netflix.conductor.model.WorkflowModel, com.netflix.conductor.model.TaskModel, com.netflix.conductor.core.execution.WorkflowExecutor) [{}]",
              "step_credits": 40498,
              "scalar_headers": 40307,
              "packed_invocations": 191,
              "packed_mark_credits": 191,
              "physical_method_edge_invocations": 40498,
              "edge_delta_credits": 1632,
              "neutral_scalar_store_fallback_credits": 4
            },
            {
              "method": "com.netflix.conductor.proto.TaskPb$Task$Builder#buildPartial0(com.netflix.conductor.proto.TaskPb$Task) [{}]",
              "step_credits": 39681,
              "scalar_headers": 39681,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 39681,
              "edge_delta_credits": 762,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.grpc.AbstractProtoMapper#toProto(com.netflix.conductor.common.run.Workflow) [{this is com.netflix.conductor.grpc.ProtoMapper}]",
              "step_credits": 39204,
              "scalar_headers": 39204,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 39204,
              "edge_delta_credits": 1390,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.proto.WorkflowDefPb$WorkflowDef$Builder#mergeFrom(com.netflix.conductor.proto.WorkflowDefPb$WorkflowDef) [{}]",
              "step_credits": 37361,
              "scalar_headers": 37361,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 37361,
              "edge_delta_credits": 1996,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#updateAndPushParents(com.netflix.conductor.model.WorkflowModel, java.lang.String) [{}]",
              "step_credits": 37308,
              "scalar_headers": 36858,
              "packed_invocations": 442,
              "packed_mark_credits": 450,
              "physical_method_edge_invocations": 37300,
              "edge_delta_credits": 1658,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.proto.TaskDefPb$TaskDef$Builder#mergeFrom(com.netflix.conductor.proto.TaskDefPb$TaskDef) [{}]",
              "step_credits": 36160,
              "scalar_headers": 36160,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 36160,
              "edge_delta_credits": 1545,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.conductoross.conductor.ai.pdf.PdfDocumentRenderer#renderTextRunsWithOffset(java.util.List, float, float) [{}]",
              "step_credits": 35148,
              "scalar_headers": 35148,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 35148,
              "edge_delta_credits": 613,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#retry(com.netflix.conductor.model.WorkflowModel) [{}]",
              "step_credits": 34804,
              "scalar_headers": 34237,
              "packed_invocations": 540,
              "packed_mark_credits": 567,
              "physical_method_edge_invocations": 34777,
              "edge_delta_credits": 1710,
              "neutral_scalar_store_fallback_credits": 12
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.LinkedHashMap} & {arg(2) == java.util.ArrayList}]",
              "step_credits": 32105,
              "scalar_headers": 31863,
              "packed_invocations": 242,
              "packed_mark_credits": 242,
              "physical_method_edge_invocations": 32105,
              "edge_delta_credits": 1881,
              "neutral_scalar_store_fallback_credits": 35
            },
            {
              "method": "com.netflix.conductor.core.execution.WorkflowExecutorOps#restart(java.lang.String, boolean) [{}]",
              "step_credits": 31945,
              "scalar_headers": 31170,
              "packed_invocations": 759,
              "packed_mark_credits": 775,
              "physical_method_edge_invocations": 31929,
              "edge_delta_credits": 3209,
              "neutral_scalar_store_fallback_credits": 59
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.ArrayList} & {arg(2) == java.util.ArrayList}]",
              "step_credits": 31825,
              "scalar_headers": 31583,
              "packed_invocations": 242,
              "packed_mark_credits": 242,
              "physical_method_edge_invocations": 31825,
              "edge_delta_credits": 1866,
              "neutral_scalar_store_fallback_credits": 35
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.LinkedHashMap} & {arg(2) == java.util.LinkedHashMap}]",
              "step_credits": 31824,
              "scalar_headers": 31582,
              "packed_invocations": 242,
              "packed_mark_credits": 242,
              "physical_method_edge_invocations": 31824,
              "edge_delta_credits": 1868,
              "neutral_scalar_store_fallback_credits": 35
            },
            {
              "method": "com.netflix.conductor.core.execution.DeciderService#retry(com.netflix.conductor.common.metadata.tasks.TaskDef, com.netflix.conductor.common.metadata.workflow.WorkflowTask, com.netflix.conductor.model.TaskModel, com.netflix.conductor.model.WorkflowModel) [{arg(0) == java.util.ArrayList} & {arg(2) == java.util.LinkedHashMap}]",
              "step_credits": 31795,
              "scalar_headers": 31553,
              "packed_invocations": 242,
              "packed_mark_credits": 242,
              "physical_method_edge_invocations": 31795,
              "edge_delta_credits": 1862,
              "neutral_scalar_store_fallback_credits": 35
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 26.999125953
      },
      "raw_comparison": {
        "TAINT_memberships": {
          "before": 20236,
          "after": 16750,
          "change": -3486
        },
        "protected_memberships": {
          "before": 20,
          "after": 22,
          "change": 2
        },
        "FLOW_memberships": {
          "before": 36815,
          "after": 36751,
          "change": -64
        }
      }
    },
    "Stirling-PDF": {
      "before": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "baseline-shape-probe-results",
          "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
          "core": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
          "checker": "baseline-any-alias-guard-v1",
          "policy": "Old runtime ANY-only normalizer, canonical run-1 FULL/Empty-E initial cell, original alias-effect identity guard; old primary-reason order."
        },
        "input": {
          "path": "baseline-shape-probe-results/Stirling-PDF/bidi/shapes/run1-shapes.json",
          "sha256": "468ca78501bbfb08ca7a5900fc98a2424bd91d571e7d36940e03a70cc10e647a"
        },
        "manifest": {
          "path": "baseline-shape-probe-results/Stirling-PDF/bidi/manifest.json",
          "sha256": "a458128c467492f4cc07f35d90bde2ef5f7e7b4026258f2bca47423a47b592d9"
        },
        "summary": {
          "path": "baseline-shape-probe-results/Stirling-PDF/bidi/summary.json",
          "sha256": "d61023d04372bf96c6d4da94375d5216cad94b1ea44ce16248bae8744d39c916"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "00:05:06.231 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=17m 25.557892926s markMode=FULL",
          "end_line": "00:05:45.178 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=38.948377692s",
          "barrier_line": "00:05:46.696 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=1.501914786s iterationTime=40.466133783s"
        },
        "accepted_forward_frontier": "00:05:46.644 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 2269, demand edges 36774 in 7258 method keys, left 0, record crossings 0, DEMAND 973, CONFIRMED 0, seeds 1012, zero only 4989 (36495 edges)",
        "explicit_handoff_demand_patterns": 36774,
        "demand_method_keys": 7258,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "583 runtime normalizer unchanged: ANY-only, same-base identity arms retained by alias-effect guard",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
          "memory": "8g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
        "owners": {
          "raw": {
            "FLOW_memberships": 4876,
            "TAINT_memberships": 24774,
            "protected_memberships": 2249,
            "protected_share": 0.09078065714055057,
            "coverage": {
              "removable_now": 0,
              "protection_only": 15,
              "other": 24759
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0006054734802615645,
              "other": 0.9993945265197385
            },
            "removal_events": {
              "covered_offer_rejections": 188,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 20937,
              "UNSUPPORTED_INITIAL": 2137,
              "MARK_EXCLUDED": 1193,
              "ALIAS_EFFECT_CLASS": 294,
              "OUTPUT_TAIL_MISMATCH": 59,
              "CROSS_ATOM": 113,
              "NO_ANNOTATED_ANY_PREFIX": 8,
              "UNSUPPORTED_OUTPUT_TAIL": 18
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 20937,
              "UNSUPPORTED_INITIAL": 2137,
              "MARK_EXCLUDED": 1236,
              "ALIAS_EFFECT_CLASS": 294,
              "OUTPUT_BASE_MISMATCH": 233,
              "OUTPUT_TAIL_MISMATCH": 129,
              "CROSS_ATOM": 113,
              "NO_ANNOTATED_ANY_PREFIX": 160,
              "UNSUPPORTED_OUTPUT_TAIL": 18
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2767,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2660,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 13527,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1116,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 846,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 1090,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 762,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 16,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 375,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 31,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 78,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 285,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 384,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 312,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 10,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 13,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 36,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 18,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 57,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 43,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 9,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 2,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 23,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 35,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 77,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 1,
              "STAR->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 9,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 42,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 14,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 81,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 14,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 12,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 2,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 4
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 2431,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 384,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 552,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 262,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 832,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 9,
              "STAR->ANY|S->NS|DEMAND|depth=1": 318,
              "STAR->STAR|NS->S|DEMAND|depth=2": 10,
              "STAR->ANY|NS->S|DEMAND|depth=2": 32,
              "STAR->ANY|S->NS|DEMAND|depth=0": 42,
              "STAR->STAR|S->NS|DEMAND|depth=0": 4
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1252,
                "EXACT->ANY_TAINT": 3017,
                "EXACT->EXACT": 18805,
                "STAR->ANY": 1574,
                "STAR->EXACT": 126
              },
              "base_pairs": {
                "NS->NS": 554,
                "NS->S": 36,
                "S->NS": 3247,
                "Z->NS": 5936,
                "Z->S": 15001
              },
              "layers": {
                "DEMAND": 24774
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 23095,
                "diagonal": 1679
              },
              "flags": {
                "false": 22525,
                "true": 2249
              },
              "output_depth": {
                "0": 7177,
                "1": 16087,
                "2": 1510
              },
              "output_bases": {
                "NS": 9737,
                "S": 15037
              },
              "protected_output_bases": {
                "NS": 2230,
                "S": 19
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 1776,
                "STAR->STAR": 3100
              },
              "base_pairs": {
                "NS->NS": 4470,
                "NS->S": 42,
                "S->NS": 364
              },
              "layers": {
                "DEMAND": 2061,
                "NORMAL": 2815
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 3571,
                "1": 1263,
                "2": 42
              },
              "output_bases": {
                "NS": 4834,
                "S": 42
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=4)": 603,
              "GroupId(value=6)": 605,
              "GroupId(value=7)": 539,
              "GroupId(value=8)": 646,
              "GroupId(value=9)": 1016,
              "GroupId(value=5)": 606,
              "GroupId(value=10)": 605,
              "GroupId(value=1)": 1736,
              "GroupId(value=0)": 16498,
              "GroupId(value=11)": 635,
              "GroupId(value=12)": 619,
              "GroupId(value=13)": 606,
              "GroupId(value=16)": 22,
              "GroupId(value=14)": 36,
              "GroupId(value=2)": 2
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 518,
              "diagonal_mark_rows": 1540,
              "scalar_concrete_rows": 2248
            },
            "protection_tree_counts": {
              "none": 1583,
              "partial": 836,
              "full_structural_only": 1182,
              "full_identity": 187
            },
            "protection_tree_memberships": {
              "none": 21218,
              "partial": 2158,
              "full_structural_only": 1211,
              "full_identity": 187
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
                289
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeUsername(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                210
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePassword(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordOnLogin(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
                196
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
                185
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
                172
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
                171
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
                170
              ],
              [
                "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeRole(java.lang.String, java.lang.String, java.lang.Long, org.springframework.security.core.Authentication) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingsSection(java.lang.String, boolean) [{}]",
                155
              ],
              [
                "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                150
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingValue(java.lang.String) [{}]",
                141
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ExtractCSVController#pdfToCsv(stirling.software.SPDF.model.api.PDFWithPageNums) [{}]",
                138
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertWebsiteToPDF#urlToPdf(stirling.software.SPDF.model.api.converters.UrlToPdfRequest) [{}]",
                136
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#updateUserSettings(java.util.Map, java.security.Principal) [{}]",
                136
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbrToPdf(stirling.software.SPDF.model.api.converters.ConvertCbrToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbzToPdf(stirling.software.SPDF.model.api.converters.ConvertCbzToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertPdfToCbr(stirling.software.SPDF.model.api.converters.ConvertPdfToCbrRequest) [{}]",
                127
              ]
            ],
            "top_fields": [
              [
                "NS:",
                7177
              ],
              [
                "NS:HttpEntity#Body",
                2176
              ],
              [
                "S:<static>(java/security/unvalidated-redirect.yaml:unvalidated-redirect#sink#1;2;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_135;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/sensitive-data-exposure.yaml:url-rewriting;6;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.web.multipart.MultipartFile",
                372
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_35;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_25;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_26;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_31;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_29;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_24;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_28;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_27;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.security.core.Authentication",
                216
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#stirling.software.proprietary.security.database.repository.UserRepository",
                189
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_13;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_23;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_19;_<S>_;pos)",
                180
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 4876,
            "TAINT_memberships": 24774,
            "protected_memberships": 2249,
            "protected_share": 0.09078065714055057,
            "coverage": {
              "removable_now": 0,
              "protection_only": 15,
              "other": 24759
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0006054734802615645,
              "other": 0.9993945265197385
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 20937,
              "UNSUPPORTED_INITIAL": 2137,
              "MARK_EXCLUDED": 1193,
              "ALIAS_EFFECT_CLASS": 294,
              "OUTPUT_TAIL_MISMATCH": 59,
              "CROSS_ATOM": 113,
              "NO_ANNOTATED_ANY_PREFIX": 8,
              "UNSUPPORTED_OUTPUT_TAIL": 18
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 20937,
              "UNSUPPORTED_INITIAL": 2137,
              "MARK_EXCLUDED": 1236,
              "ALIAS_EFFECT_CLASS": 294,
              "OUTPUT_BASE_MISMATCH": 233,
              "OUTPUT_TAIL_MISMATCH": 129,
              "CROSS_ATOM": 113,
              "NO_ANNOTATED_ANY_PREFIX": 160,
              "UNSUPPORTED_OUTPUT_TAIL": 18
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2767,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2660,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 13527,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1116,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 846,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 1090,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 762,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 16,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 375,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 31,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 78,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 285,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 384,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 312,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 10,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 13,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 36,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 18,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 57,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 43,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 9,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 2,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 23,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 35,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 77,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0": 1,
              "STAR->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 9,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 42,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 14,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 81,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 14,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 12,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 2,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 4
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 2431,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 384,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 552,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 262,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 832,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 9,
              "STAR->ANY|S->NS|DEMAND|depth=1": 318,
              "STAR->STAR|NS->S|DEMAND|depth=2": 10,
              "STAR->ANY|NS->S|DEMAND|depth=2": 32,
              "STAR->ANY|S->NS|DEMAND|depth=0": 42,
              "STAR->STAR|S->NS|DEMAND|depth=0": 4
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1252,
                "EXACT->ANY_TAINT": 3017,
                "EXACT->EXACT": 18805,
                "STAR->ANY": 1574,
                "STAR->EXACT": 126
              },
              "base_pairs": {
                "NS->NS": 554,
                "NS->S": 36,
                "S->NS": 3247,
                "Z->NS": 5936,
                "Z->S": 15001
              },
              "layers": {
                "DEMAND": 24774
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 23095,
                "diagonal": 1679
              },
              "flags": {
                "false": 22525,
                "true": 2249
              },
              "output_depth": {
                "0": 7177,
                "1": 16087,
                "2": 1510
              },
              "output_bases": {
                "NS": 9737,
                "S": 15037
              },
              "protected_output_bases": {
                "NS": 2230,
                "S": 19
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 1776,
                "STAR->STAR": 3100
              },
              "base_pairs": {
                "NS->NS": 4470,
                "NS->S": 42,
                "S->NS": 364
              },
              "layers": {
                "DEMAND": 2061,
                "NORMAL": 2815
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 3571,
                "1": 1263,
                "2": 42
              },
              "output_bases": {
                "NS": 4834,
                "S": 42
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=4)": 603,
              "GroupId(value=6)": 605,
              "GroupId(value=7)": 539,
              "GroupId(value=8)": 646,
              "GroupId(value=9)": 1016,
              "GroupId(value=5)": 606,
              "GroupId(value=10)": 605,
              "GroupId(value=1)": 1736,
              "GroupId(value=0)": 16498,
              "GroupId(value=11)": 635,
              "GroupId(value=12)": 619,
              "GroupId(value=13)": 606,
              "GroupId(value=16)": 22,
              "GroupId(value=14)": 36,
              "GroupId(value=2)": 2
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 518,
              "diagonal_mark_rows": 1540,
              "scalar_concrete_rows": 2248
            },
            "protection_tree_counts": {
              "none": 1583,
              "partial": 836,
              "full_structural_only": 1182,
              "full_identity": 187
            },
            "protection_tree_memberships": {
              "none": 21218,
              "partial": 2158,
              "full_structural_only": 1211,
              "full_identity": 187
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
                289
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeUsername(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                210
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePassword(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordOnLogin(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
                196
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
                185
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
                172
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
                171
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
                170
              ],
              [
                "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeRole(java.lang.String, java.lang.String, java.lang.Long, org.springframework.security.core.Authentication) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingsSection(java.lang.String, boolean) [{}]",
                155
              ],
              [
                "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                150
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingValue(java.lang.String) [{}]",
                141
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ExtractCSVController#pdfToCsv(stirling.software.SPDF.model.api.PDFWithPageNums) [{}]",
                138
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertWebsiteToPDF#urlToPdf(stirling.software.SPDF.model.api.converters.UrlToPdfRequest) [{}]",
                136
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#updateUserSettings(java.util.Map, java.security.Principal) [{}]",
                136
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbrToPdf(stirling.software.SPDF.model.api.converters.ConvertCbrToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbzToPdf(stirling.software.SPDF.model.api.converters.ConvertCbzToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertPdfToCbr(stirling.software.SPDF.model.api.converters.ConvertPdfToCbrRequest) [{}]",
                127
              ]
            ],
            "top_fields": [
              [
                "NS:",
                7177
              ],
              [
                "NS:HttpEntity#Body",
                2176
              ],
              [
                "S:<static>(java/security/unvalidated-redirect.yaml:unvalidated-redirect#sink#1;2;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_135;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/sensitive-data-exposure.yaml:url-rewriting;6;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.web.multipart.MultipartFile",
                372
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_35;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_25;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_26;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_31;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_29;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_24;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_28;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_27;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.security.core.Authentication",
                216
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#stirling.software.proprietary.security.database.repository.UserRepository",
                189
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_13;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_23;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_19;_<S>_;pos)",
                180
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 188,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-cold-actors-v1",
          "totals": {
            "scalar_headers": 5336767,
            "packed_invocations": 6264,
            "packed_mark_credits": 8133,
            "physical_method_edge_invocations": 5343031
          },
          "actor_totals": {
            "actors": 7258,
            "steps": 5344900,
            "neutralBatchApplications": 6264,
            "neutralBatchMemberships": 8133
          },
          "top_methods": [
            {
              "method": "stirling.software.SPDF.controller.api.security.GetInfoOnPDF#getPdfInfo(stirling.software.common.model.api.PDFFile) [{}]",
              "step_credits": 943062,
              "scalar_headers": 943026,
              "packed_invocations": 4,
              "packed_mark_credits": 36,
              "physical_method_edge_invocations": 943030
            },
            {
              "method": "stirling.software.SPDF.controller.api.pipeline.PipelineProcessor#runPipelineAgainstFiles(java.util.List, stirling.software.SPDF.model.PipelineConfig) [{}]",
              "step_credits": 718061,
              "scalar_headers": 717394,
              "packed_invocations": 667,
              "packed_mark_credits": 667,
              "physical_method_edge_invocations": 718061
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#regeneratePageContent(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDPage, java.util.List, java.util.List, java.util.Map, java.util.List, int, org.apache.pdfbox.pdmodel.PDPageContentStream$AppendMode) [{arg(2) == java.util.ArrayList} & {arg(3) == java.util.ArrayList} & {arg(5) == java.util.ArrayList}]",
              "step_credits": 286429,
              "scalar_headers": 285707,
              "packed_invocations": 685,
              "packed_mark_credits": 722,
              "physical_method_edge_invocations": 286392
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 134766,
              "scalar_headers": 134762,
              "packed_invocations": 4,
              "packed_mark_credits": 4,
              "physical_method_edge_invocations": 134766
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#buildFontRuns(org.apache.pdfbox.pdmodel.PDDocument, java.util.Map, java.util.List, int, org.apache.pdfbox.pdmodel.font.PDFont, java.lang.String, stirling.software.SPDF.model.json.PdfJsonTextElement) [{arg(2) == java.util.ArrayList}]",
              "step_credits": 118111,
              "scalar_headers": 117882,
              "packed_invocations": 229,
              "packed_mark_credits": 229,
              "physical_method_edge_invocations": 118111
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#preflightTextElements(org.apache.pdfbox.pdmodel.PDDocument, java.util.Map, java.util.List, java.util.List, int) [{arg(2) == java.util.ArrayList} & {arg(3) == java.util.ArrayList}]",
              "step_credits": 69166,
              "scalar_headers": 68998,
              "packed_invocations": 168,
              "packed_mark_credits": 168,
              "physical_method_edge_invocations": 69166
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#createFontFromModel(org.apache.pdfbox.pdmodel.PDDocument, stirling.software.SPDF.model.json.PdfJsonFont, java.lang.String) [{arg(1) == java.util.ArrayList}]",
              "step_credits": 54486,
              "scalar_headers": 54213,
              "packed_invocations": 263,
              "packed_mark_credits": 273,
              "physical_method_edge_invocations": 54476
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#createFontFromModel(org.apache.pdfbox.pdmodel.PDDocument, stirling.software.SPDF.model.json.PdfJsonFont, java.lang.String) [{}]",
              "step_credits": 54485,
              "scalar_headers": 54212,
              "packed_invocations": 263,
              "packed_mark_credits": 273,
              "physical_method_edge_invocations": 54475
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AdminLicenseController#uploadLicenseFile(org.springframework.web.multipart.MultipartFile) [{}]",
              "step_credits": 51461,
              "scalar_headers": 51223,
              "packed_invocations": 226,
              "packed_mark_credits": 238,
              "physical_method_edge_invocations": 51449
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#exportUpdatedPages(java.lang.String, stirling.software.SPDF.model.json.PdfJsonDocument) [{}]",
              "step_credits": 46019,
              "scalar_headers": 45792,
              "packed_invocations": 207,
              "packed_mark_credits": 227,
              "physical_method_edge_invocations": 45999
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#extractSinglePage(java.lang.String, int) [{}]",
              "step_credits": 45137,
              "scalar_headers": 45002,
              "packed_invocations": 135,
              "packed_mark_credits": 135,
              "physical_method_edge_invocations": 45137
            },
            {
              "method": "stirling.software.SPDF.controller.api.SettingsController#updateConnectionsSettings(java.util.Map) [{}]",
              "step_credits": 43820,
              "scalar_headers": 43820,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 43820
            },
            {
              "method": "stirling.software.SPDF.controller.api.MergeController#mergePdfs(stirling.software.SPDF.model.api.general.MergePdfsRequest, java.lang.String) [{}]",
              "step_credits": 43314,
              "scalar_headers": 43304,
              "packed_invocations": 1,
              "packed_mark_credits": 10,
              "physical_method_edge_invocations": 43305
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#changeUserEnabled(java.lang.String, boolean, org.springframework.security.core.Authentication) [{}]",
              "step_credits": 43039,
              "scalar_headers": 43029,
              "packed_invocations": 10,
              "packed_mark_credits": 10,
              "physical_method_edge_invocations": 43039
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AdminSettingsController#updateSettingsSection(java.lang.String, java.util.Map) [{}]",
              "step_credits": 37762,
              "scalar_headers": 37762,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 37762
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#convertPdfToJson(org.springframework.web.multipart.MultipartFile, java.util.function.Consumer, boolean) [{}]",
              "step_credits": 37512,
              "scalar_headers": 37391,
              "packed_invocations": 111,
              "packed_mark_credits": 121,
              "physical_method_edge_invocations": 37502
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 37206,
              "scalar_headers": 37202,
              "packed_invocations": 4,
              "packed_mark_credits": 4,
              "physical_method_edge_invocations": 37206
            },
            {
              "method": "stirling.software.SPDF.controller.api.SplitPDFController#splitPdf(stirling.software.SPDF.model.api.PDFWithPageNums) [{}]",
              "step_credits": 36057,
              "scalar_headers": 36017,
              "packed_invocations": 8,
              "packed_mark_credits": 40,
              "physical_method_edge_invocations": 36025
            },
            {
              "method": "stirling.software.SPDF.controller.api.misc.ScannerEffectController#scannerEffect(stirling.software.SPDF.model.api.misc.ScannerEffectRequest) [{}]",
              "step_credits": 34394,
              "scalar_headers": 34374,
              "packed_invocations": 4,
              "packed_mark_credits": 20,
              "physical_method_edge_invocations": 34378
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 31694,
              "scalar_headers": 31693,
              "packed_invocations": 1,
              "packed_mark_credits": 1,
              "physical_method_edge_invocations": 31694
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#collectFontsFromResources(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDResources, int, java.util.Map, java.util.Map, java.util.Set, java.lang.String, java.util.Map, java.lang.String) [{arg(7) == java.util.IdentityHashMap}]",
              "step_credits": 29975,
              "scalar_headers": 29826,
              "packed_invocations": 149,
              "packed_mark_credits": 149,
              "physical_method_edge_invocations": 29975
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#collectFontsFromResources(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDResources, int, java.util.Map, java.util.Map, java.util.Set, java.lang.String, java.util.Map, java.lang.String) [{arg(3) == java.util.LinkedHashMap} & {arg(4) == java.util.HashMap} & {arg(7) == java.util.IdentityHashMap}]",
              "step_credits": 29574,
              "scalar_headers": 29425,
              "packed_invocations": 149,
              "packed_mark_credits": 149,
              "physical_method_edge_invocations": 29574
            },
            {
              "method": "stirling.software.proprietary.controller.api.ProprietaryUIDataController#getAdminSettingsData(org.springframework.security.core.Authentication) [{}]",
              "step_credits": 28905,
              "scalar_headers": 28887,
              "packed_invocations": 18,
              "packed_mark_credits": 18,
              "physical_method_edge_invocations": 28905
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#exportAuditData(java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 28841,
              "scalar_headers": 28801,
              "packed_invocations": 40,
              "packed_mark_credits": 40,
              "physical_method_edge_invocations": 28841
            },
            {
              "method": "stirling.software.proprietary.controller.api.AuditRestController#getAuditEvents(int, int, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 24243,
              "scalar_headers": 24243,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 24243
            },
            {
              "method": "stirling.software.SPDF.controller.api.misc.ConfigController#getAppConfig() [{}]",
              "step_credits": 21090,
              "scalar_headers": 21087,
              "packed_invocations": 3,
              "packed_mark_credits": 3,
              "physical_method_edge_invocations": 21090
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
              "step_credits": 20036,
              "scalar_headers": 20030,
              "packed_invocations": 6,
              "packed_mark_credits": 6,
              "physical_method_edge_invocations": 20036
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
              "step_credits": 18993,
              "scalar_headers": 18984,
              "packed_invocations": 9,
              "packed_mark_credits": 9,
              "physical_method_edge_invocations": 18993
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
              "step_credits": 18922,
              "scalar_headers": 18922,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 18922
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
              "step_credits": 18725,
              "scalar_headers": 18724,
              "packed_invocations": 1,
              "packed_mark_credits": 1,
              "physical_method_edge_invocations": 18725
            },
            {
              "method": "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 17661,
              "scalar_headers": 17642,
              "packed_invocations": 2,
              "packed_mark_credits": 19,
              "physical_method_edge_invocations": 17644
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#getAuditData(int, int, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 17376,
              "scalar_headers": 17376,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 17376
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#exportAuditDataJson(java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 17251,
              "scalar_headers": 17197,
              "packed_invocations": 54,
              "packed_mark_credits": 54,
              "physical_method_edge_invocations": 17251
            },
            {
              "method": "stirling.software.SPDF.controller.api.security.RedactController#redactFoundText(org.apache.pdfbox.pdmodel.PDDocument, java.util.List, float, java.awt.Color, boolean) [{arg(1) == java.util.ArrayList}]",
              "step_credits": 17180,
              "scalar_headers": 17072,
              "packed_invocations": 96,
              "packed_mark_credits": 108,
              "physical_method_edge_invocations": 17168
            },
            {
              "method": "stirling.software.SPDF.controller.api.SettingsController#updateGeneralSettings(java.util.Map) [{}]",
              "step_credits": 15523,
              "scalar_headers": 15523,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 15523
            },
            {
              "method": "stirling.software.SPDF.controller.api.security.WatermarkController#addTextWatermark(org.apache.pdfbox.pdmodel.PDPageContentStream, java.lang.String, org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDPage, float, int, int, float, java.lang.String, java.lang.String) [{}]",
              "step_credits": 14971,
              "scalar_headers": 14971,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14971
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.proprietary.security.controller.api.UserController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14885,
              "scalar_headers": 14885,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14885
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.SPDF.controller.api.SettingsController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14757,
              "scalar_headers": 14757,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14757
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__init__() [{}]",
              "step_credits": 14737,
              "scalar_headers": 14737,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14737
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.SPDF.controller.web.MetricsController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14693,
              "scalar_headers": 14693,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14693
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 38.948377692
      },
      "after": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "shape-probe-results",
          "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
          "core": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
          "checker": "correlated-star-any-v1",
          "policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order."
        },
        "input": {
          "path": "shape-probe-results/Stirling-PDF/bidi/shapes/run1-shapes.json",
          "sha256": "a66a4cab122b9e1fc836d96d3e4fe1f743aaf77f19030c741e0a52bafbf6432b"
        },
        "manifest": {
          "path": "shape-probe-results/Stirling-PDF/bidi/manifest.json",
          "sha256": "9ea54005c6a11d55bdcb91c4a359a2e6b22c467391e46dac7a950cc8a2a0ea07"
        },
        "summary": {
          "path": "shape-probe-results/Stirling-PDF/bidi/summary.json",
          "sha256": "2a049c96bd39e049b4ca420679559b60e056af62b5d89de19863a8a33ba07ff9"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "22:04:24.290 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=17m 26.971480007s markMode=FULL",
          "end_line": "22:05:07.551 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=43.262338608s",
          "barrier_line": "22:05:09.598 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=2.028123930s iterationTime=45.309299013s"
        },
        "accepted_forward_frontier": "22:05:09.497 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 2269, demand edges 36468 in 7258 method keys, left 0, record crossings 0, DEMAND 973, CONFIRMED 0, seeds 1012, zero only 4989 (36483 edges)",
        "explicit_handoff_demand_patterns": 36468,
        "demand_method_keys": 7258,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order.",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
          "memory": "8g",
          "timeout": 1080,
          "outer_timeout": 1200
        },
        "model_sha256": "b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
        "owners": {
          "raw": {
            "FLOW_memberships": 4876,
            "TAINT_memberships": 24479,
            "protected_memberships": 2273,
            "protected_share": 0.09285510029004453,
            "coverage": {
              "removable_now": 0,
              "protection_only": 26,
              "other": 24453
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0010621348911311736,
              "other": 0.9989378651088688
            },
            "removal_events": {
              "covered_offer_rejections": 788,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 20929,
              "UNSUPPORTED_INITIAL": 2139,
              "MARK_EXCLUDED": 1254,
              "CROSS_ATOM": 113,
              "UNSUPPORTED_OUTPUT": 18
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 20929,
              "UNSUPPORTED_INITIAL": 2139,
              "MARK_EXCLUDED": 1254,
              "CROSS_ATOM": 113,
              "OUTPUT_BASE_MISMATCH": 229,
              "OUTPUT_TAIL_MISMATCH": 84,
              "NO_ANNOTATED_ANY_PREFIX": 148,
              "STAR_PATH_INEQUALITY": 25,
              "UNSUPPORTED_OUTPUT": 18
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2768,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2660,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 13527,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1116,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 846,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 1090,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 762,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 16,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 375,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 31,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 73,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 384,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 312,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 36,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 57,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 4,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 43,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 10,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 2,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 1,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 11,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 41,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 21,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 25,
              "STAR->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 9,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 40,
              "STAR->STAR|S->NS|DEMAND|diagonal|flag=true|depth=0": 36,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 42,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 14,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 81,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 14,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 2,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 4
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 2431,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 384,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 552,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 262,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 832,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 9,
              "STAR->ANY|S->NS|DEMAND|depth=1": 318,
              "STAR->STAR|NS->S|DEMAND|depth=2": 10,
              "STAR->ANY|NS->S|DEMAND|depth=2": 32,
              "STAR->ANY|S->NS|DEMAND|depth=0": 42,
              "STAR->STAR|S->NS|DEMAND|depth=0": 4
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1235,
                "EXACT->ANY_TAINT": 3017,
                "EXACT->EXACT": 18816,
                "STAR->ANY": 1213,
                "STAR->EXACT": 126,
                "STAR->STAR": 72
              },
              "base_pairs": {
                "NS->NS": 279,
                "NS->S": 26,
                "S->NS": 3245,
                "Z->NS": 5928,
                "Z->S": 15001
              },
              "layers": {
                "DEMAND": 24479
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 23087,
                "diagonal": 1392
              },
              "flags": {
                "false": 22206,
                "true": 2273
              },
              "output_depth": {
                "0": 6873,
                "1": 16106,
                "2": 1500
              },
              "output_bases": {
                "NS": 9452,
                "S": 15027
              },
              "protected_output_bases": {
                "NS": 2254,
                "S": 19
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 1776,
                "STAR->STAR": 3100
              },
              "base_pairs": {
                "NS->NS": 4470,
                "NS->S": 42,
                "S->NS": 364
              },
              "layers": {
                "DEMAND": 2061,
                "NORMAL": 2815
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 3571,
                "1": 1263,
                "2": 42
              },
              "output_bases": {
                "NS": 4834,
                "S": 42
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=4)": 561,
              "GroupId(value=6)": 605,
              "GroupId(value=7)": 620,
              "GroupId(value=8)": 878,
              "GroupId(value=5)": 605,
              "GroupId(value=9)": 605,
              "GroupId(value=1)": 1736,
              "GroupId(value=0)": 16434,
              "GroupId(value=11)": 620,
              "GroupId(value=12)": 610,
              "GroupId(value=13)": 606,
              "GroupId(value=10)": 539,
              "GroupId(value=16)": 22,
              "GroupId(value=14)": 36,
              "GroupId(value=2)": 2
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 315,
              "diagonal_mark_rows": 1250,
              "scalar_concrete_rows": 2239
            },
            "protection_tree_counts": {
              "none": 1267,
              "partial": 836,
              "full_structural_only": 1201,
              "full_identity": 185
            },
            "protection_tree_memberships": {
              "none": 20899,
              "partial": 2158,
              "full_structural_only": 1237,
              "full_identity": 185
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
                289
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeUsername(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                209
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePassword(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordOnLogin(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
                196
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
                184
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
                172
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
                171
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
                170
              ],
              [
                "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeRole(java.lang.String, java.lang.String, java.lang.Long, org.springframework.security.core.Authentication) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingsSection(java.lang.String, boolean) [{}]",
                155
              ],
              [
                "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                150
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingValue(java.lang.String) [{}]",
                141
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ExtractCSVController#pdfToCsv(stirling.software.SPDF.model.api.PDFWithPageNums) [{}]",
                138
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertWebsiteToPDF#urlToPdf(stirling.software.SPDF.model.api.converters.UrlToPdfRequest) [{}]",
                136
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#updateUserSettings(java.util.Map, java.security.Principal) [{}]",
                135
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbrToPdf(stirling.software.SPDF.model.api.converters.ConvertCbrToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbzToPdf(stirling.software.SPDF.model.api.converters.ConvertCbzToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertPdfToCbr(stirling.software.SPDF.model.api.converters.ConvertPdfToCbrRequest) [{}]",
                127
              ]
            ],
            "top_fields": [
              [
                "NS:",
                6873
              ],
              [
                "NS:HttpEntity#Body",
                2196
              ],
              [
                "S:<static>(java/security/unvalidated-redirect.yaml:unvalidated-redirect#sink#1;2;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_135;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/sensitive-data-exposure.yaml:url-rewriting;6;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.web.multipart.MultipartFile",
                372
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_35;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_25;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_26;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_31;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_29;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_24;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_28;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_27;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.security.core.Authentication",
                216
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#stirling.software.proprietary.security.database.repository.UserRepository",
                189
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_13;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_23;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_19;_<S>_;pos)",
                180
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 4876,
            "TAINT_memberships": 24479,
            "protected_memberships": 2273,
            "protected_share": 0.09285510029004453,
            "coverage": {
              "removable_now": 0,
              "protection_only": 26,
              "other": 24453
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0010621348911311736,
              "other": 0.9989378651088688
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 20929,
              "UNSUPPORTED_INITIAL": 2139,
              "MARK_EXCLUDED": 1254,
              "CROSS_ATOM": 113,
              "UNSUPPORTED_OUTPUT": 18
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 20929,
              "UNSUPPORTED_INITIAL": 2139,
              "MARK_EXCLUDED": 1254,
              "CROSS_ATOM": 113,
              "OUTPUT_BASE_MISMATCH": 229,
              "OUTPUT_TAIL_MISMATCH": 84,
              "NO_ANNOTATED_ANY_PREFIX": 148,
              "STAR_PATH_INEQUALITY": 25,
              "UNSUPPORTED_OUTPUT": 18
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2768,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2660,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 13527,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1116,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 846,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1": 1090,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 762,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 16,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 375,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 31,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 73,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 384,
              "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 312,
              "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 36,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 1,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 4,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 57,
              "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 4,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 43,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 10,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 2,
              "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 1,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 11,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 41,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 6,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 21,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 25,
              "STAR->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 9,
              "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0": 40,
              "STAR->STAR|S->NS|DEMAND|diagonal|flag=true|depth=0": 36,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 42,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 2,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 14,
              "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 81,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 3,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 14,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 2,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 4,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 4
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 2431,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 384,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 552,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 262,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 832,
              "STAR->STAR|NS->NS|DEMAND|depth=1": 9,
              "STAR->ANY|S->NS|DEMAND|depth=1": 318,
              "STAR->STAR|NS->S|DEMAND|depth=2": 10,
              "STAR->ANY|NS->S|DEMAND|depth=2": 32,
              "STAR->ANY|S->NS|DEMAND|depth=0": 42,
              "STAR->STAR|S->NS|DEMAND|depth=0": 4
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1235,
                "EXACT->ANY_TAINT": 3017,
                "EXACT->EXACT": 18816,
                "STAR->ANY": 1213,
                "STAR->EXACT": 126,
                "STAR->STAR": 72
              },
              "base_pairs": {
                "NS->NS": 279,
                "NS->S": 26,
                "S->NS": 3245,
                "Z->NS": 5928,
                "Z->S": 15001
              },
              "layers": {
                "DEMAND": 24479
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 23087,
                "diagonal": 1392
              },
              "flags": {
                "false": 22206,
                "true": 2273
              },
              "output_depth": {
                "0": 6873,
                "1": 16106,
                "2": 1500
              },
              "output_bases": {
                "NS": 9452,
                "S": 15027
              },
              "protected_output_bases": {
                "NS": 2254,
                "S": 19
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 1776,
                "STAR->STAR": 3100
              },
              "base_pairs": {
                "NS->NS": 4470,
                "NS->S": 42,
                "S->NS": 364
              },
              "layers": {
                "DEMAND": 2061,
                "NORMAL": 2815
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 3571,
                "1": 1263,
                "2": 42
              },
              "output_bases": {
                "NS": 4834,
                "S": 42
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=4)": 561,
              "GroupId(value=6)": 605,
              "GroupId(value=7)": 620,
              "GroupId(value=8)": 878,
              "GroupId(value=5)": 605,
              "GroupId(value=9)": 605,
              "GroupId(value=1)": 1736,
              "GroupId(value=0)": 16434,
              "GroupId(value=11)": 620,
              "GroupId(value=12)": 610,
              "GroupId(value=13)": 606,
              "GroupId(value=10)": 539,
              "GroupId(value=16)": 22,
              "GroupId(value=14)": 36,
              "GroupId(value=2)": 2
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 315,
              "diagonal_mark_rows": 1250,
              "scalar_concrete_rows": 2239
            },
            "protection_tree_counts": {
              "none": 1267,
              "partial": 836,
              "full_structural_only": 1201,
              "full_identity": 185
            },
            "protection_tree_memberships": {
              "none": 20899,
              "partial": 2158,
              "full_structural_only": 1237,
              "full_identity": 185
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
                289
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeUsername(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                209
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePassword(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordOnLogin(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                197
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
                196
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
                184
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
                172
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
                171
              ],
              [
                "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
                170
              ],
              [
                "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#changeRole(java.lang.String, java.lang.String, java.lang.Long, org.springframework.security.core.Authentication) [{}]",
                159
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingsSection(java.lang.String, boolean) [{}]",
                155
              ],
              [
                "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
                150
              ],
              [
                "stirling.software.proprietary.security.controller.api.AdminSettingsController#getSettingValue(java.lang.String) [{}]",
                141
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ExtractCSVController#pdfToCsv(stirling.software.SPDF.model.api.PDFWithPageNums) [{}]",
                138
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertWebsiteToPDF#urlToPdf(stirling.software.SPDF.model.api.converters.UrlToPdfRequest) [{}]",
                136
              ],
              [
                "stirling.software.proprietary.security.controller.api.UserController#updateUserSettings(java.util.Map, java.security.Principal) [{}]",
                135
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbrToPdf(stirling.software.SPDF.model.api.converters.ConvertCbrToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertCbzToPdf(stirling.software.SPDF.model.api.converters.ConvertCbzToPdfRequest) [{}]",
                127
              ],
              [
                "stirling.software.SPDF.controller.api.converters.ConvertImgPDFController#convertPdfToCbr(stirling.software.SPDF.model.api.converters.ConvertPdfToCbrRequest) [{}]",
                127
              ]
            ],
            "top_fields": [
              [
                "NS:",
                6873
              ],
              [
                "NS:HttpEntity#Body",
                2196
              ],
              [
                "S:<static>(java/security/unvalidated-redirect.yaml:unvalidated-redirect#sink#1;2;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_135;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(java/security/sensitive-data-exposure.yaml:url-rewriting;6;_<S>_;pos)",
                525
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.web.multipart.MultipartFile",
                372
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_35;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_25;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_26;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_31;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_29;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_24;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_28;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_27;_<S>_;pos)",
                345
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#org.springframework.security.core.Authentication",
                216
              ],
              [
                "S:<static>(__spring_registry__)/__spring_registry__#stirling.software.proprietary.security.database.repository.UserRepository",
                189
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_13;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_23;_<S>_;pos)",
                180
              ],
              [
                "S:<static>(java/security/xss.yaml:xss#sink#1;sink_19;_<S>_;pos)",
                180
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 788,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-v2",
          "totals": {
            "scalar_headers": 5562833,
            "packed_invocations": 7048,
            "packed_mark_credits": 9002,
            "resume_events": 9676,
            "physical_method_edge_invocations": 5569881,
            "statement_untouched_from_process": 4161211,
            "statement_pure_untouched_from_process": 2804145,
            "statement_untouched_from_resume": 0,
            "statement_pure_untouched_from_resume": 0,
            "packed_untouched_callbacks": 6251,
            "packed_untouched_mark_credits": 7592,
            "scalar_taint_headers": 3101198,
            "scalar_fully_protected_identity_headers": 261713,
            "packed_fully_protected_identity_invocations": 959,
            "packed_fully_protected_identity_mark_credits": 977,
            "resume_taint_headers": 5856,
            "resume_fully_protected_identity_headers": 0
          },
          "actor_totals": {
            "actors": 7258,
            "steps": 5571835,
            "neutralBatchApplications": 7048,
            "neutralBatchMemberships": 9002
          },
          "top_methods": [
            {
              "method": "stirling.software.SPDF.controller.api.pipeline.PipelineProcessor#runPipelineAgainstFiles(java.util.List, stirling.software.SPDF.model.PipelineConfig) [{}]",
              "step_credits": 1013971,
              "scalar_headers": 1012973,
              "packed_invocations": 998,
              "packed_mark_credits": 998,
              "physical_method_edge_invocations": 1013971,
              "edge_delta_credits": 4118,
              "neutral_scalar_store_fallback_credits": 30
            },
            {
              "method": "stirling.software.SPDF.controller.api.security.GetInfoOnPDF#getPdfInfo(stirling.software.common.model.api.PDFFile) [{}]",
              "step_credits": 943269,
              "scalar_headers": 943215,
              "packed_invocations": 6,
              "packed_mark_credits": 54,
              "physical_method_edge_invocations": 943221,
              "edge_delta_credits": 2120,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#regeneratePageContent(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDPage, java.util.List, java.util.List, java.util.Map, java.util.List, int, org.apache.pdfbox.pdmodel.PDPageContentStream$AppendMode) [{arg(2) == java.util.ArrayList} & {arg(3) == java.util.ArrayList} & {arg(5) == java.util.ArrayList}]",
              "step_credits": 267251,
              "scalar_headers": 266529,
              "packed_invocations": 685,
              "packed_mark_credits": 722,
              "physical_method_edge_invocations": 267214,
              "edge_delta_credits": 2273,
              "neutral_scalar_store_fallback_credits": 2
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.InviteLinkController#generateInviteLink(java.lang.String, java.lang.String, java.lang.Long, java.lang.Integer, boolean, java.security.Principal, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 135384,
              "scalar_headers": 135380,
              "packed_invocations": 4,
              "packed_mark_credits": 4,
              "physical_method_edge_invocations": 135384,
              "edge_delta_credits": 2629,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#buildFontRuns(org.apache.pdfbox.pdmodel.PDDocument, java.util.Map, java.util.List, int, org.apache.pdfbox.pdmodel.font.PDFont, java.lang.String, stirling.software.SPDF.model.json.PdfJsonTextElement) [{arg(2) == java.util.ArrayList}]",
              "step_credits": 117958,
              "scalar_headers": 117728,
              "packed_invocations": 230,
              "packed_mark_credits": 230,
              "physical_method_edge_invocations": 117958,
              "edge_delta_credits": 882,
              "neutral_scalar_store_fallback_credits": 2
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#preflightTextElements(org.apache.pdfbox.pdmodel.PDDocument, java.util.Map, java.util.List, java.util.List, int) [{arg(2) == java.util.ArrayList} & {arg(3) == java.util.ArrayList}]",
              "step_credits": 69146,
              "scalar_headers": 68980,
              "packed_invocations": 166,
              "packed_mark_credits": 166,
              "physical_method_edge_invocations": 69146,
              "edge_delta_credits": 638,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#createFontFromModel(org.apache.pdfbox.pdmodel.PDDocument, stirling.software.SPDF.model.json.PdfJsonFont, java.lang.String) [{arg(1) == java.util.ArrayList}]",
              "step_credits": 54948,
              "scalar_headers": 54646,
              "packed_invocations": 294,
              "packed_mark_credits": 302,
              "physical_method_edge_invocations": 54940,
              "edge_delta_credits": 922,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#createFontFromModel(org.apache.pdfbox.pdmodel.PDDocument, stirling.software.SPDF.model.json.PdfJsonFont, java.lang.String) [{}]",
              "step_credits": 54947,
              "scalar_headers": 54645,
              "packed_invocations": 294,
              "packed_mark_credits": 302,
              "physical_method_edge_invocations": 54939,
              "edge_delta_credits": 921,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AdminLicenseController#uploadLicenseFile(org.springframework.web.multipart.MultipartFile) [{}]",
              "step_credits": 51461,
              "scalar_headers": 51223,
              "packed_invocations": 226,
              "packed_mark_credits": 238,
              "physical_method_edge_invocations": 51449,
              "edge_delta_credits": 1669,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#extractSinglePage(java.lang.String, int) [{}]",
              "step_credits": 45137,
              "scalar_headers": 45002,
              "packed_invocations": 135,
              "packed_mark_credits": 135,
              "physical_method_edge_invocations": 45137,
              "edge_delta_credits": 451,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.SettingsController#updateConnectionsSettings(java.util.Map) [{}]",
              "step_credits": 43820,
              "scalar_headers": 43820,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 43820,
              "edge_delta_credits": 2438,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#exportUpdatedPages(java.lang.String, stirling.software.SPDF.model.json.PdfJsonDocument) [{}]",
              "step_credits": 43483,
              "scalar_headers": 43233,
              "packed_invocations": 230,
              "packed_mark_credits": 250,
              "physical_method_edge_invocations": 43463,
              "edge_delta_credits": 1066,
              "neutral_scalar_store_fallback_credits": 12
            },
            {
              "method": "stirling.software.SPDF.controller.api.MergeController#mergePdfs(stirling.software.SPDF.model.api.general.MergePdfsRequest, java.lang.String) [{}]",
              "step_credits": 43314,
              "scalar_headers": 43304,
              "packed_invocations": 1,
              "packed_mark_credits": 10,
              "physical_method_edge_invocations": 43305,
              "edge_delta_credits": 612,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#changeUserEnabled(java.lang.String, boolean, org.springframework.security.core.Authentication) [{}]",
              "step_credits": 43039,
              "scalar_headers": 43029,
              "packed_invocations": 10,
              "packed_mark_credits": 10,
              "physical_method_edge_invocations": 43039,
              "edge_delta_credits": 1132,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#convertPdfToJson(org.springframework.web.multipart.MultipartFile, java.util.function.Consumer, boolean) [{}]",
              "step_credits": 40451,
              "scalar_headers": 40297,
              "packed_invocations": 144,
              "packed_mark_credits": 154,
              "physical_method_edge_invocations": 40441,
              "edge_delta_credits": 809,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AdminSettingsController#updateSettingsSection(java.lang.String, java.util.Map) [{}]",
              "step_credits": 37762,
              "scalar_headers": 37762,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 37762,
              "edge_delta_credits": 2014,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.AuthController#login(stirling.software.proprietary.security.model.api.user.UsernameAndPass, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 37206,
              "scalar_headers": 37202,
              "packed_invocations": 4,
              "packed_mark_credits": 4,
              "physical_method_edge_invocations": 37206,
              "edge_delta_credits": 1143,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.misc.ScannerEffectController#scannerEffect(stirling.software.SPDF.model.api.misc.ScannerEffectRequest) [{}]",
              "step_credits": 34394,
              "scalar_headers": 34374,
              "packed_invocations": 4,
              "packed_mark_credits": 20,
              "physical_method_edge_invocations": 34378,
              "edge_delta_credits": 301,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#inviteUsers(java.lang.String, java.lang.String, java.lang.Long, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 31642,
              "scalar_headers": 31641,
              "packed_invocations": 1,
              "packed_mark_credits": 1,
              "physical_method_edge_invocations": 31642,
              "edge_delta_credits": 973,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#collectFontsFromResources(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDResources, int, java.util.Map, java.util.Map, java.util.Set, java.lang.String, java.util.Map, java.lang.String) [{arg(7) == java.util.IdentityHashMap}]",
              "step_credits": 29975,
              "scalar_headers": 29826,
              "packed_invocations": 149,
              "packed_mark_credits": 149,
              "physical_method_edge_invocations": 29975,
              "edge_delta_credits": 699,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.service.PdfJsonConversionService#collectFontsFromResources(org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDResources, int, java.util.Map, java.util.Map, java.util.Set, java.lang.String, java.util.Map, java.lang.String) [{arg(3) == java.util.LinkedHashMap} & {arg(4) == java.util.HashMap} & {arg(7) == java.util.IdentityHashMap}]",
              "step_credits": 29574,
              "scalar_headers": 29425,
              "packed_invocations": 149,
              "packed_mark_credits": 149,
              "physical_method_edge_invocations": 29574,
              "edge_delta_credits": 691,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.api.ProprietaryUIDataController#getAdminSettingsData(org.springframework.security.core.Authentication) [{}]",
              "step_credits": 28930,
              "scalar_headers": 28912,
              "packed_invocations": 18,
              "packed_mark_credits": 18,
              "physical_method_edge_invocations": 28930,
              "edge_delta_credits": 823,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#exportAuditData(java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 28841,
              "scalar_headers": 28801,
              "packed_invocations": 40,
              "packed_mark_credits": 40,
              "physical_method_edge_invocations": 28841,
              "edge_delta_credits": 768,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.api.AuditRestController#getAuditEvents(int, int, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 24243,
              "scalar_headers": 24243,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 24243,
              "edge_delta_credits": 581,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.misc.ConfigController#getAppConfig() [{}]",
              "step_credits": 21090,
              "scalar_headers": 21087,
              "packed_invocations": 3,
              "packed_mark_credits": 3,
              "physical_method_edge_invocations": 21090,
              "edge_delta_credits": 197,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.InviteLinkController#acceptInvite(java.lang.String, java.lang.String, java.lang.String) [{}]",
              "step_credits": 20098,
              "scalar_headers": 20092,
              "packed_invocations": 6,
              "packed_mark_credits": 6,
              "physical_method_edge_invocations": 20098,
              "edge_delta_credits": 909,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#changePasswordForUser(java.lang.String, java.lang.String, boolean, boolean, boolean, boolean, jakarta.servlet.http.HttpServletRequest, org.springframework.security.core.Authentication) [{}]",
              "step_credits": 19106,
              "scalar_headers": 19097,
              "packed_invocations": 9,
              "packed_mark_credits": 9,
              "physical_method_edge_invocations": 19106,
              "edge_delta_credits": 802,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#saveUser(java.lang.String, java.lang.String, java.lang.String, java.lang.Long, java.lang.String, boolean) [{}]",
              "step_credits": 18745,
              "scalar_headers": 18744,
              "packed_invocations": 1,
              "packed_mark_credits": 1,
              "physical_method_edge_invocations": 18745,
              "edge_delta_credits": 784,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__() [{}]",
              "step_credits": 18542,
              "scalar_headers": 18542,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 18542,
              "edge_delta_credits": 342,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.api.AuditRestController#exportAuditData(java.lang.String, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 17661,
              "scalar_headers": 17642,
              "packed_invocations": 3,
              "packed_mark_credits": 19,
              "physical_method_edge_invocations": 17645,
              "edge_delta_credits": 781,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#exportAuditDataJson(java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate) [{}]",
              "step_credits": 17485,
              "scalar_headers": 17413,
              "packed_invocations": 72,
              "packed_mark_credits": 72,
              "physical_method_edge_invocations": 17485,
              "edge_delta_credits": 889,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.AuditDashboardController#getAuditData(int, int, java.lang.String, java.lang.String, java.time.LocalDate, java.time.LocalDate, jakarta.servlet.http.HttpServletRequest) [{}]",
              "step_credits": 17376,
              "scalar_headers": 17376,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 17376,
              "edge_delta_credits": 629,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.security.RedactController#redactFoundText(org.apache.pdfbox.pdmodel.PDDocument, java.util.List, float, java.awt.Color, boolean) [{arg(1) == java.util.ArrayList}]",
              "step_credits": 17180,
              "scalar_headers": 17072,
              "packed_invocations": 96,
              "packed_mark_credits": 108,
              "physical_method_edge_invocations": 17168,
              "edge_delta_credits": 438,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.SettingsController#updateGeneralSettings(java.util.Map) [{}]",
              "step_credits": 15523,
              "scalar_headers": 15523,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 15523,
              "edge_delta_credits": 1221,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.SPDF.controller.api.security.WatermarkController#addTextWatermark(org.apache.pdfbox.pdmodel.PDPageContentStream, java.lang.String, org.apache.pdfbox.pdmodel.PDDocument, org.apache.pdfbox.pdmodel.PDPage, float, int, int, float, java.lang.String, java.lang.String) [{}]",
              "step_credits": 14971,
              "scalar_headers": 14971,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14971,
              "edge_delta_credits": 151,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.security.controller.api.UserController#changeUsername(java.security.Principal, java.lang.String, java.lang.String, jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 14857,
              "scalar_headers": 14855,
              "packed_invocations": 2,
              "packed_mark_credits": 2,
              "physical_method_edge_invocations": 14857,
              "edge_delta_credits": 734,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "stirling.software.proprietary.controller.api.AuditRestController#getAuditCharts(java.lang.String) [{}]",
              "step_credits": 14579,
              "scalar_headers": 14579,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14579,
              "edge_delta_credits": 197,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.proprietary.security.controller.api.UserController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14401,
              "scalar_headers": 14401,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14401,
              "edge_delta_credits": 187,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.SPDF.controller.api.SettingsController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14281,
              "scalar_headers": 14281,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14281,
              "edge_delta_credits": 87,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "virtual (spring: __spring_dispatcher__)#__dispatch__stirling.software.SPDF.controller.web.MetricsController_Opentaint_EntryPoint() [{}]",
              "step_credits": 14221,
              "scalar_headers": 14221,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 14221,
              "edge_delta_credits": 139,
              "neutral_scalar_store_fallback_credits": 0
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 43.262338608
      },
      "raw_comparison": {
        "TAINT_memberships": {
          "before": 24774,
          "after": 24479,
          "change": -295
        },
        "protected_memberships": {
          "before": 2249,
          "after": 2273,
          "change": 24
        },
        "FLOW_memberships": {
          "before": 4876,
          "after": 4876,
          "change": 0
        }
      }
    },
    "OWASP": {
      "before": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "baseline-shape-probe-results",
          "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
          "core": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
          "checker": "baseline-any-alias-guard-v1",
          "policy": "Old runtime ANY-only normalizer, canonical run-1 FULL/Empty-E initial cell, original alias-effect identity guard; old primary-reason order."
        },
        "input": {
          "path": "baseline-shape-probe-results/OWASP/bidi/shapes/run1-shapes.json",
          "sha256": "974de76841eb86c316c3370aa6b25b7da273facdd0fd83f50108b7d663334d2c"
        },
        "manifest": {
          "path": "baseline-shape-probe-results/OWASP/bidi/manifest.json",
          "sha256": "62f0e4fb74d259b0e04ecfb4786a8b43bbb74ddf44fc1a83470225dfeb108878"
        },
        "summary": {
          "path": "baseline-shape-probe-results/OWASP/bidi/summary.json",
          "sha256": "36d8ccf2c66fca71d33c4ce024f4ca0d173411f5fe389f97db2db086829c2985"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "00:08:14.719 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=15m 14.582513567s markMode=FULL",
          "end_line": "00:11:30.129 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=3m 15.410768161s",
          "barrier_line": "00:11:35.048 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=4.895126709s iterationTime=3m 20.329546721s"
        },
        "accepted_forward_frontier": "00:11:34.935 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 4413, demand edges 133966 in 12083 method keys, left 0, record crossings 0, DEMAND 9709, CONFIRMED 0, seeds 11077, zero only 7670 (308677 edges)",
        "explicit_handoff_demand_patterns": 133966,
        "demand_method_keys": 12083,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "583 runtime normalizer unchanged: ANY-only, same-base identity arms retained by alias-effect guard",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
          "memory": "8g",
          "timeout": 1000,
          "outer_timeout": 1200
        },
        "model_sha256": "e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
        "owners": {
          "raw": {
            "FLOW_memberships": 11235,
            "TAINT_memberships": 111133,
            "protected_memberships": 413,
            "protected_share": 0.0037162678952246406,
            "coverage": {
              "removable_now": 0,
              "protection_only": 0,
              "other": 111133
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0,
              "other": 1.0
            },
            "removal_events": {
              "covered_offer_rejections": 44,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 93439,
              "UNSUPPORTED_INITIAL": 16919,
              "ALIAS_EFFECT_CLASS": 371,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 28,
              "NO_ANNOTATED_ANY_PREFIX": 52,
              "UNSUPPORTED_OUTPUT_TAIL": 95,
              "OUTPUT_TAIL_MISMATCH": 143
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 93439,
              "UNSUPPORTED_INITIAL": 16919,
              "ALIAS_EFFECT_CLASS": 371,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 115,
              "OUTPUT_BASE_MISMATCH": 223,
              "OUTPUT_TAIL_MISMATCH": 223,
              "NO_ANNOTATED_ANY_PREFIX": 59,
              "UNSUPPORTED_OUTPUT_TAIL": 95
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 91565,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 107,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 13036,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2424,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 479,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 34,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 115,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 538,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 217,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 15,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 622,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 1114,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 97,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 114,
              "EXACT->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 34,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 37,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 12,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 18,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=true|depth=2": 5,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 8,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 406,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 58,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 36,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 16
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 9721,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 385,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 275,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 506,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 304,
              "STAR->ANY|NS->S|DEMAND|depth=2": 38,
              "STAR->STAR|NS->S|DEMAND|depth=2": 6
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1700,
                "EXACT->ANY_TAINT": 107,
                "EXACT->EXACT": 108551,
                "STAR->ANY": 608,
                "STAR->EXACT": 167
              },
              "base_pairs": {
                "NS->NS": 17398,
                "NS->S": 296,
                "Z->NS": 91673,
                "Z->S": 1766
              },
              "layers": {
                "DEMAND": 111133
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 96021,
                "diagonal": 15112
              },
              "flags": {
                "false": 110720,
                "true": 413
              },
              "output_depth": {
                "0": 108464,
                "1": 607,
                "2": 2062
              },
              "output_bases": {
                "NS": 109071,
                "S": 2062
              },
              "protected_output_bases": {
                "NS": 369,
                "S": 44
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 819,
                "STAR->STAR": 10416
              },
              "base_pairs": {
                "NS->NS": 11191,
                "NS->S": 44
              },
              "layers": {
                "DEMAND": 1129,
                "NORMAL": 10106
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 10300,
                "1": 891,
                "2": 44
              },
              "output_bases": {
                "NS": 11191,
                "S": 44
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=2)": 5661,
              "GroupId(value=3)": 5673,
              "GroupId(value=4)": 6444,
              "GroupId(value=5)": 13080,
              "GroupId(value=6)": 5700,
              "GroupId(value=7)": 5998,
              "GroupId(value=8)": 5890,
              "GroupId(value=9)": 26032,
              "GroupId(value=10)": 5622,
              "GroupId(value=11)": 5619,
              "GroupId(value=12)": 5702,
              "GroupId(value=13)": 5619,
              "GroupId(value=14)": 5643,
              "GroupId(value=1)": 8442,
              "GroupId(value=19)": 8
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 223,
              "diagonal_mark_rows": 594,
              "scalar_concrete_rows": 26776
            },
            "protection_tree_counts": {
              "none": 26976,
              "full_identity": 343,
              "partial": 25,
              "full_structural_only": 26
            },
            "protection_tree_memberships": {
              "none": 110443,
              "full_identity": 343,
              "partial": 306,
              "full_structural_only": 41
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.owasp.benchmark.helpers.DataBaseServer#createOrder2(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.helpers.DataBaseServer#getOtherOrder(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02304#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                64
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00222#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00529#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01118#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01405#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01406#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01407#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01987#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02303#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00457#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01331#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02110#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02111#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00132#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00135#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00136#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00362#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00363#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ]
            ],
            "top_fields": [
              [
                "NS:",
                108464
              ],
              [
                "S:<static>(org.owasp.benchmark.helpers.Utils)/Utils#TESTFILES_DIR",
                2062
              ],
              [
                "NS:CharSequence#<rule-storage>",
                210
              ],
              [
                "NS:String#<string-bytes>",
                203
              ],
              [
                "NS:String#bytes",
                194
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 11235,
            "TAINT_memberships": 111133,
            "protected_memberships": 413,
            "protected_share": 0.0037162678952246406,
            "coverage": {
              "removable_now": 0,
              "protection_only": 0,
              "other": 111133
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 0.0,
              "other": 1.0
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 93439,
              "UNSUPPORTED_INITIAL": 16919,
              "ALIAS_EFFECT_CLASS": 371,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 28,
              "NO_ANNOTATED_ANY_PREFIX": 52,
              "UNSUPPORTED_OUTPUT_TAIL": 95,
              "OUTPUT_TAIL_MISMATCH": 143
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 93439,
              "UNSUPPORTED_INITIAL": 16919,
              "ALIAS_EFFECT_CLASS": 371,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 115,
              "OUTPUT_BASE_MISMATCH": 223,
              "OUTPUT_TAIL_MISMATCH": 223,
              "NO_ANNOTATED_ANY_PREFIX": 59,
              "UNSUPPORTED_OUTPUT_TAIL": 95
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 91565,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 107,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 13036,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2424,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 479,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 34,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 115,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 538,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 217,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 15,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 622,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 1114,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 97,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 114,
              "EXACT->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 34,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 37,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 12,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 18,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=true|depth=2": 5,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 8,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 406,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 2,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 58,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 36,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 16
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 9721,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 385,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 275,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 506,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 304,
              "STAR->ANY|NS->S|DEMAND|depth=2": 38,
              "STAR->STAR|NS->S|DEMAND|depth=2": 6
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1700,
                "EXACT->ANY_TAINT": 107,
                "EXACT->EXACT": 108551,
                "STAR->ANY": 608,
                "STAR->EXACT": 167
              },
              "base_pairs": {
                "NS->NS": 17398,
                "NS->S": 296,
                "Z->NS": 91673,
                "Z->S": 1766
              },
              "layers": {
                "DEMAND": 111133
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 96021,
                "diagonal": 15112
              },
              "flags": {
                "false": 110720,
                "true": 413
              },
              "output_depth": {
                "0": 108464,
                "1": 607,
                "2": 2062
              },
              "output_bases": {
                "NS": 109071,
                "S": 2062
              },
              "protected_output_bases": {
                "NS": 369,
                "S": 44
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 819,
                "STAR->STAR": 10416
              },
              "base_pairs": {
                "NS->NS": 11191,
                "NS->S": 44
              },
              "layers": {
                "DEMAND": 1129,
                "NORMAL": 10106
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 10300,
                "1": 891,
                "2": 44
              },
              "output_bases": {
                "NS": 11191,
                "S": 44
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=2)": 5661,
              "GroupId(value=3)": 5673,
              "GroupId(value=4)": 6444,
              "GroupId(value=5)": 13080,
              "GroupId(value=6)": 5700,
              "GroupId(value=7)": 5998,
              "GroupId(value=8)": 5890,
              "GroupId(value=9)": 26032,
              "GroupId(value=10)": 5622,
              "GroupId(value=11)": 5619,
              "GroupId(value=12)": 5702,
              "GroupId(value=13)": 5619,
              "GroupId(value=14)": 5643,
              "GroupId(value=1)": 8442,
              "GroupId(value=19)": 8
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 223,
              "diagonal_mark_rows": 594,
              "scalar_concrete_rows": 26776
            },
            "protection_tree_counts": {
              "none": 26976,
              "full_identity": 343,
              "partial": 25,
              "full_structural_only": 26
            },
            "protection_tree_memberships": {
              "none": 110443,
              "full_identity": 343,
              "partial": 306,
              "full_structural_only": 41
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.owasp.benchmark.helpers.DataBaseServer#createOrder2(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.helpers.DataBaseServer#getOtherOrder(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02304#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                64
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00222#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00529#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01118#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01405#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01406#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01407#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01987#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02303#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00457#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01331#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02110#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02111#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00132#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00135#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00136#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00362#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00363#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ]
            ],
            "top_fields": [
              [
                "NS:",
                108464
              ],
              [
                "S:<static>(org.owasp.benchmark.helpers.Utils)/Utils#TESTFILES_DIR",
                2062
              ],
              [
                "NS:CharSequence#<rule-storage>",
                210
              ],
              [
                "NS:String#<string-bytes>",
                203
              ],
              [
                "NS:String#bytes",
                194
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 44,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-cold-actors-v1",
          "totals": {
            "scalar_headers": 63013546,
            "packed_invocations": 3539,
            "packed_mark_credits": 3840,
            "physical_method_edge_invocations": 63017085
          },
          "actor_totals": {
            "actors": 12083,
            "steps": 63017386,
            "neutralBatchApplications": 3539,
            "neutralBatchMemberships": 3840
          },
          "top_methods": [
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01447#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 138819,
              "scalar_headers": 138819,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 138819
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00524#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 136914,
              "scalar_headers": 136914,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 136914
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00578#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 136438,
              "scalar_headers": 136438,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 136438
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00561#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 135290,
              "scalar_headers": 135290,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 135290
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02346#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 134365,
              "scalar_headers": 134365,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 134365
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00579#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 133654,
              "scalar_headers": 133654,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 133654
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01450#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 132178,
              "scalar_headers": 132178,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 132178
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00583#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 131236,
              "scalar_headers": 131236,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 131236
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00577#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 131032,
              "scalar_headers": 131032,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 131032
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02345#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 129481,
              "scalar_headers": 129481,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 129481
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00748#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 129238,
              "scalar_headers": 129238,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 129238
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00580#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 128354,
              "scalar_headers": 128354,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 128354
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00584#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 126891,
              "scalar_headers": 126891,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 126891
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00532#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 126596,
              "scalar_headers": 126596,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 126596
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00316#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 124560,
              "scalar_headers": 124560,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 124560
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00585#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 122189,
              "scalar_headers": 122189,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 122189
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00506#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 122019,
              "scalar_headers": 122019,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 122019
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00817#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 121789,
              "scalar_headers": 121789,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 121789
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00538#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 118675,
              "scalar_headers": 118675,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 118675
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01452#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 117672,
              "scalar_headers": 117672,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 117672
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00562#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 117133,
              "scalar_headers": 117133,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 117133
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01449#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116895,
              "scalar_headers": 116895,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116895
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00523#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116193,
              "scalar_headers": 116193,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116193
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00560#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116146,
              "scalar_headers": 116146,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116146
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00245#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 115211,
              "scalar_headers": 115211,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 115211
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00318#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 115019,
              "scalar_headers": 115019,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 115019
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00522#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 114053,
              "scalar_headers": 114053,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 114053
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01448#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112788,
              "scalar_headers": 112788,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112788
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01451#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112788,
              "scalar_headers": 112788,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112788
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00564#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112256,
              "scalar_headers": 112256,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112256
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02347#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111723,
              "scalar_headers": 111723,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111723
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00582#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111412,
              "scalar_headers": 111412,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111412
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02348#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111245,
              "scalar_headers": 111245,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111245
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02349#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111135,
              "scalar_headers": 111135,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111135
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02351#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111135,
              "scalar_headers": 111135,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111135
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00239#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111131,
              "scalar_headers": 111131,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111131
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02350#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111084,
              "scalar_headers": 111084,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111084
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01453#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111048,
              "scalar_headers": 111048,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111048
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00581#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 110579,
              "scalar_headers": 110579,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 110579
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00521#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 108183,
              "scalar_headers": 108183,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 108183
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 195.410768161
      },
      "after": {
        "state": "VALID_JOINED_RUN1_CENSUS",
        "source": {
          "directory": "shape-probe-results",
          "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
          "core": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
          "checker": "correlated-star-any-v1",
          "policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order."
        },
        "input": {
          "path": "shape-probe-results/OWASP/bidi/shapes/run1-shapes.json",
          "sha256": "d8613c0317a27ec1a07bcd53d48b21f1f99a85bcfd69a83a4cdf4a4d616e78d5"
        },
        "manifest": {
          "path": "shape-probe-results/OWASP/bidi/manifest.json",
          "sha256": "4727e8f9a704b543dfd3ac843a09c6c35c4846576f35d43e6437258ba07f3ba7"
        },
        "summary": {
          "path": "shape-probe-results/OWASP/bidi/summary.json",
          "sha256": "bab6f492e038887e93e63a1962c59a556beffe57e4c97e9fb807b1c15d616686"
        },
        "command_status": "OK",
        "SARIF_available": true,
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "completion_markers": {
          "start_line": "22:07:28.038 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=15m 22.309060798s markMode=FULL",
          "end_line": "22:10:40.296 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=3m 12.258801982s",
          "barrier_line": "22:10:45.799 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=5.458963877s iterationTime=3m 17.761878950s"
        },
        "accepted_forward_frontier": "22:10:45.595 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 4413, demand edges 133858 in 12083 method keys, left 0, record crossings 0, DEMAND 9709, CONFIRMED 0, seeds 11077, zero only 7670 (308659 edges)",
        "explicit_handoff_demand_patterns": 133858,
        "demand_method_keys": 12083,
        "captured_at": "joined_engine_barrier; written after report and handoff",
        "coverage_policy": "Selected runtime STAR equal-path/E-subset and ANY annotated-prefix coverage; current atoms/legal initial E; alias-effect exception removed; current primary-reason order.",
        "config": {
          "model": "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
          "memory": "8g",
          "timeout": 1000,
          "outer_timeout": 1200
        },
        "model_sha256": "e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873",
        "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
        "diagnostic_patch_sha256_from_runtime_manifest": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
        "owners": {
          "raw": {
            "FLOW_memberships": 11235,
            "TAINT_memberships": 111025,
            "protected_memberships": 460,
            "protected_share": 0.0041432109885161,
            "coverage": {
              "removable_now": 0,
              "protection_only": 8,
              "other": 111017
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 7.205584327854087e-05,
              "other": 0.9999279441567215
            },
            "removal_events": {
              "covered_offer_rejections": 786,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 93441,
              "UNSUPPORTED_INITIAL": 17241,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 154,
              "UNSUPPORTED_OUTPUT": 95
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 93441,
              "UNSUPPORTED_INITIAL": 17241,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 154,
              "OUTPUT_BASE_MISMATCH": 154,
              "OUTPUT_TAIL_MISMATCH": 95,
              "NO_ANNOTATED_ANY_PREFIX": 19,
              "STAR_PATH_INEQUALITY": 32,
              "UNSUPPORTED_OUTPUT": 95
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 91565,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 107,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 13360,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2424,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 34,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 28,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 700,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 35,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 87,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 12,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 15,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 217,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 624,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 1114,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 99,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 114,
              "EXACT->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 34,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 37,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 12,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 18,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=true|depth=2": 5,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 8,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 164,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 78,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 58,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 36,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 16
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 9721,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 385,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 275,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 506,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 304,
              "STAR->ANY|NS->S|DEMAND|depth=2": 38,
              "STAR->STAR|NS->S|DEMAND|depth=2": 6
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1534,
                "EXACT->ANY_TAINT": 107,
                "EXACT->EXACT": 109041,
                "STAR->ANY": 77,
                "STAR->EXACT": 167,
                "STAR->STAR": 99
              },
              "base_pairs": {
                "NS->NS": 17286,
                "NS->S": 298,
                "Z->NS": 91673,
                "Z->S": 1768
              },
              "layers": {
                "DEMAND": 111025
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 96023,
                "diagonal": 15002
              },
              "flags": {
                "false": 110565,
                "true": 460
              },
              "output_depth": {
                "0": 107981,
                "1": 978,
                "2": 2066
              },
              "output_bases": {
                "NS": 108959,
                "S": 2066
              },
              "protected_output_bases": {
                "NS": 416,
                "S": 44
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 819,
                "STAR->STAR": 10416
              },
              "base_pairs": {
                "NS->NS": 11191,
                "NS->S": 44
              },
              "layers": {
                "DEMAND": 1129,
                "NORMAL": 10106
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 10300,
                "1": 891,
                "2": 44
              },
              "output_bases": {
                "NS": 11191,
                "S": 44
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=12)": 5661,
              "GroupId(value=9)": 5673,
              "GroupId(value=3)": 6427,
              "GroupId(value=13)": 5700,
              "GroupId(value=1)": 5998,
              "GroupId(value=6)": 5890,
              "GroupId(value=4)": 26029,
              "GroupId(value=14)": 5622,
              "GroupId(value=2)": 13077,
              "GroupId(value=7)": 5619,
              "GroupId(value=11)": 5702,
              "GroupId(value=10)": 5619,
              "GroupId(value=8)": 5643,
              "GroupId(value=5)": 8357,
              "GroupId(value=19)": 8
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 118,
              "diagonal_mark_rows": 143,
              "scalar_concrete_rows": 26938
            },
            "protection_tree_counts": {
              "none": 26659,
              "full_identity": 322,
              "full_structural_only": 75,
              "partial": 25
            },
            "protection_tree_memberships": {
              "none": 110288,
              "full_identity": 322,
              "full_structural_only": 109,
              "partial": 306
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.owasp.benchmark.helpers.DataBaseServer#createOrder2(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.helpers.DataBaseServer#getOtherOrder(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02304#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                64
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00222#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00529#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01118#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01405#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01406#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01407#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01987#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02303#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00457#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01331#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02110#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02111#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00132#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00135#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00136#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00362#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00363#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ]
            ],
            "top_fields": [
              [
                "NS:",
                107981
              ],
              [
                "S:<static>(org.owasp.benchmark.helpers.Utils)/Utils#TESTFILES_DIR",
                2066
              ],
              [
                "NS:String#<string-bytes>",
                393
              ],
              [
                "NS:CharSequence#<rule-storage>",
                391
              ],
              [
                "NS:String#bytes",
                194
              ]
            ]
          },
          "selected": {
            "FLOW_memberships": 11235,
            "TAINT_memberships": 111025,
            "protected_memberships": 460,
            "protected_share": 0.0041432109885161,
            "coverage": {
              "removable_now": 0,
              "protection_only": 8,
              "other": 111017
            },
            "coverage_shares": {
              "removable_now": 0.0,
              "protection_only": 7.205584327854087e-05,
              "other": 0.9999279441567215
            },
            "removal_events": {
              "covered_offer_rejections": 0,
              "stored_compaction_memberships": 0
            },
            "primary_other_reasons": {
              "ZERO_INITIAL": 93441,
              "UNSUPPORTED_INITIAL": 17241,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 154,
              "UNSUPPORTED_OUTPUT": 95
            },
            "secondary_failures_nonadditive": {
              "ZERO_INITIAL": 93441,
              "UNSUPPORTED_INITIAL": 17241,
              "CROSS_ATOM": 86,
              "MARK_EXCLUDED": 154,
              "OUTPUT_BASE_MISMATCH": 154,
              "OUTPUT_TAIL_MISMATCH": 95,
              "NO_ANNOTATED_ANY_PREFIX": 19,
              "STAR_PATH_INEQUALITY": 32,
              "UNSUPPORTED_OUTPUT": 95
            },
            "TAINT_full_shape_histogram": {
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 91565,
              "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 107,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 13360,
              "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 2424,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0": 34,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0": 28,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 700,
              "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1": 35,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0": 87,
              "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=1": 12,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 15,
              "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 217,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0": 1,
              "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 1,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 624,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 1114,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=false|depth=2": 99,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2": 114,
              "EXACT->EXACT|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 34,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2": 37,
              "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 12,
              "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 18,
              "EXACT->EXACT|NS->S|DEMAND|diagonal|flag=true|depth=2": 5,
              "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2": 8,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1": 164,
              "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0": 78,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0": 7,
              "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1": 7,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0": 58,
              "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=1": 36,
              "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2": 1,
              "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1": 16
            },
            "FLOW_full_shape_histogram": {
              "STAR->STAR|NS->NS|NORMAL|depth=0": 9721,
              "STAR->STAR|NS->NS|NORMAL|depth=1": 385,
              "STAR->ANY|NS->NS|DEMAND|depth=0": 275,
              "STAR->ANY|NS->NS|DEMAND|depth=1": 506,
              "STAR->STAR|NS->NS|DEMAND|depth=0": 304,
              "STAR->ANY|NS->S|DEMAND|depth=2": 38,
              "STAR->STAR|NS->S|DEMAND|depth=2": 6
            },
            "TAINT_dimensions": {
              "tail_pairs": {
                "EXACT->ANY": 1534,
                "EXACT->ANY_TAINT": 107,
                "EXACT->EXACT": 109041,
                "STAR->ANY": 77,
                "STAR->EXACT": 167,
                "STAR->STAR": 99
              },
              "base_pairs": {
                "NS->NS": 17286,
                "NS->S": 298,
                "Z->NS": 91673,
                "Z->S": 1768
              },
              "layers": {
                "DEMAND": 111025
              },
              "relation_kind": {
                "cross_or_zero_or_nd": 96023,
                "diagonal": 15002
              },
              "flags": {
                "false": 110565,
                "true": 460
              },
              "output_depth": {
                "0": 107981,
                "1": 978,
                "2": 2066
              },
              "output_bases": {
                "NS": 108959,
                "S": 2066
              },
              "protected_output_bases": {
                "NS": 416,
                "S": 44
              }
            },
            "FLOW_dimensions": {
              "tail_pairs": {
                "STAR->ANY": 819,
                "STAR->STAR": 10416
              },
              "base_pairs": {
                "NS->NS": 11191,
                "NS->S": 44
              },
              "layers": {
                "DEMAND": 1129,
                "NORMAL": 10106
              },
              "relation_kind": {},
              "flags": {},
              "output_depth": {
                "0": 10300,
                "1": 891,
                "2": 44
              },
              "output_bases": {
                "NS": 11191,
                "S": 44
              },
              "protected_output_bases": {}
            },
            "mark_group_memberships": {
              "GroupId(value=12)": 5661,
              "GroupId(value=9)": 5673,
              "GroupId(value=3)": 6427,
              "GroupId(value=13)": 5700,
              "GroupId(value=1)": 5998,
              "GroupId(value=6)": 5890,
              "GroupId(value=4)": 26029,
              "GroupId(value=14)": 5622,
              "GroupId(value=2)": 13077,
              "GroupId(value=7)": 5619,
              "GroupId(value=11)": 5702,
              "GroupId(value=10)": 5619,
              "GroupId(value=8)": 5643,
              "GroupId(value=5)": 8357,
              "GroupId(value=19)": 8
            },
            "physical_rows_not_logical_memberships": {
              "diagonal_geometry_rows": 118,
              "diagonal_mark_rows": 143,
              "scalar_concrete_rows": 26938
            },
            "protection_tree_counts": {
              "none": 26659,
              "full_identity": 322,
              "full_structural_only": 75,
              "partial": 25
            },
            "protection_tree_memberships": {
              "none": 110288,
              "full_identity": 322,
              "full_structural_only": 109,
              "partial": 306
            },
            "recorded_invariant_violations": {},
            "top_methods": [
              [
                "org.owasp.benchmark.helpers.DataBaseServer#createOrder2(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.helpers.DataBaseServer#getOtherOrder(org.owasp.benchmark.service.pojo.Person, javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                80
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02304#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                64
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00222#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00529#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01118#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01405#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01406#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01407#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01987#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02303#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                61
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00457#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest01331#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02110#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest02111#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                60
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00132#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00135#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00136#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00362#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ],
              [
                "org.owasp.benchmark.testcode.BenchmarkTest00363#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
                57
              ]
            ],
            "top_fields": [
              [
                "NS:",
                107981
              ],
              [
                "S:<static>(org.owasp.benchmark.helpers.Utils)/Utils#TESTFILES_DIR",
                2066
              ],
              [
                "NS:String#<string-bytes>",
                393
              ],
              [
                "NS:CharSequence#<rule-storage>",
                391
              ],
              [
                "NS:String#bytes",
                194
              ]
            ]
          }
        },
        "raw_selected_differences": {
          "event.covered_offer_rejections": {
            "raw": 786,
            "selected": 0
          }
        },
        "work": {
          "version": "run1-work-v2",
          "totals": {
            "scalar_headers": 62969407,
            "packed_invocations": 4019,
            "packed_mark_credits": 4318,
            "resume_events": 10662,
            "physical_method_edge_invocations": 62973426,
            "statement_untouched_from_process": 31628594,
            "statement_pure_untouched_from_process": 28618850,
            "statement_untouched_from_resume": 0,
            "statement_pure_untouched_from_resume": 0,
            "packed_untouched_callbacks": 3098,
            "packed_untouched_mark_credits": 3363,
            "scalar_taint_headers": 58213674,
            "scalar_fully_protected_identity_headers": 722155,
            "packed_fully_protected_identity_invocations": 1464,
            "packed_fully_protected_identity_mark_credits": 1467,
            "resume_taint_headers": 8529,
            "resume_fully_protected_identity_headers": 0
          },
          "actor_totals": {
            "actors": 12083,
            "steps": 62973725,
            "neutralBatchApplications": 4019,
            "neutralBatchMemberships": 4318
          },
          "top_methods": [
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01447#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 138819,
              "scalar_headers": 138819,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 138819,
              "edge_delta_credits": 3222,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00524#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 136914,
              "scalar_headers": 136914,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 136914,
              "edge_delta_credits": 2829,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00578#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 135382,
              "scalar_headers": 135382,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 135382,
              "edge_delta_credits": 3002,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00561#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 135290,
              "scalar_headers": 135290,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 135290,
              "edge_delta_credits": 3874,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02346#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 134365,
              "scalar_headers": 134365,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 134365,
              "edge_delta_credits": 3020,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00579#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 133654,
              "scalar_headers": 133654,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 133654,
              "edge_delta_credits": 3039,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01450#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 132178,
              "scalar_headers": 132178,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 132178,
              "edge_delta_credits": 3072,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00583#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 131236,
              "scalar_headers": 131236,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 131236,
              "edge_delta_credits": 3050,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00577#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 131032,
              "scalar_headers": 131032,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 131032,
              "edge_delta_credits": 3015,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02345#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 129481,
              "scalar_headers": 129481,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 129481,
              "edge_delta_credits": 2983,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00748#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 129238,
              "scalar_headers": 129238,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 129238,
              "edge_delta_credits": 3223,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00580#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 128354,
              "scalar_headers": 128354,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 128354,
              "edge_delta_credits": 3023,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00584#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 126891,
              "scalar_headers": 126891,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 126891,
              "edge_delta_credits": 3197,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00532#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 126596,
              "scalar_headers": 126596,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 126596,
              "edge_delta_credits": 2858,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00316#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 124560,
              "scalar_headers": 124560,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 124560,
              "edge_delta_credits": 3311,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00585#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 122189,
              "scalar_headers": 122189,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 122189,
              "edge_delta_credits": 3015,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00506#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 122019,
              "scalar_headers": 122019,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 122019,
              "edge_delta_credits": 3190,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00817#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 121789,
              "scalar_headers": 121789,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 121789,
              "edge_delta_credits": 4016,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00538#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 118675,
              "scalar_headers": 118675,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 118675,
              "edge_delta_credits": 2828,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00562#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 117133,
              "scalar_headers": 117133,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 117133,
              "edge_delta_credits": 3582,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01449#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116895,
              "scalar_headers": 116895,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116895,
              "edge_delta_credits": 2991,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01452#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116784,
              "scalar_headers": 116784,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116784,
              "edge_delta_credits": 2990,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00523#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116193,
              "scalar_headers": 116193,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116193,
              "edge_delta_credits": 2446,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00560#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 116146,
              "scalar_headers": 116146,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 116146,
              "edge_delta_credits": 3585,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00245#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 115211,
              "scalar_headers": 115211,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 115211,
              "edge_delta_credits": 3013,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00318#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 115019,
              "scalar_headers": 115019,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 115019,
              "edge_delta_credits": 3138,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00522#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 114053,
              "scalar_headers": 114053,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 114053,
              "edge_delta_credits": 1897,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01448#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112788,
              "scalar_headers": 112788,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112788,
              "edge_delta_credits": 2954,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01451#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112788,
              "scalar_headers": 112788,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112788,
              "edge_delta_credits": 2954,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00564#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 112256,
              "scalar_headers": 112256,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 112256,
              "edge_delta_credits": 3096,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02347#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111723,
              "scalar_headers": 111723,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111723,
              "edge_delta_credits": 2953,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00582#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111412,
              "scalar_headers": 111412,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111412,
              "edge_delta_credits": 2862,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02348#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111245,
              "scalar_headers": 111245,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111245,
              "edge_delta_credits": 2953,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02349#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111135,
              "scalar_headers": 111135,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111135,
              "edge_delta_credits": 2952,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02351#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111135,
              "scalar_headers": 111135,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111135,
              "edge_delta_credits": 2952,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00239#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111131,
              "scalar_headers": 111131,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111131,
              "edge_delta_credits": 3126,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest02350#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111084,
              "scalar_headers": 111084,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111084,
              "edge_delta_credits": 2875,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest01453#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 111048,
              "scalar_headers": 111048,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 111048,
              "edge_delta_credits": 2866,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00581#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 110579,
              "scalar_headers": 110579,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 110579,
              "edge_delta_credits": 2844,
              "neutral_scalar_store_fallback_credits": 0
            },
            {
              "method": "org.owasp.benchmark.testcode.BenchmarkTest00521#doPost(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse) [{}]",
              "step_credits": 108183,
              "scalar_headers": 108183,
              "packed_invocations": 0,
              "packed_mark_credits": 0,
              "physical_method_edge_invocations": 108183,
              "edge_delta_credits": 1863,
              "neutral_scalar_store_fallback_credits": 0
            }
          ]
        },
        "engine_seconds_diagnostic_not_performance_comparison": 192.258801982
      },
      "raw_comparison": {
        "TAINT_memberships": {
          "before": 111133,
          "after": 111025,
          "change": -108
        },
        "protected_memberships": {
          "before": 413,
          "after": 460,
          "change": 47
        },
        "FLOW_memberships": {
          "before": 11235,
          "after": 11235,
          "change": 0
        }
      }
    }
  },
  "checks": {
    "thingsboard/before/revision": true,
    "thingsboard/before/core_tree": true,
    "thingsboard/before/checker_version": true,
    "thingsboard/before/census_completed_run1": true,
    "thingsboard/before/summary_completed_run1": true,
    "thingsboard/before/engine_complete_marker": true,
    "thingsboard/before/normal_report_accepted_marker": true,
    "thingsboard/before/barrier_marker": true,
    "thingsboard/before/forward_limit1": true,
    "thingsboard/before/joined_capture_binding": true,
    "thingsboard/before/manifest_binding": true,
    "thingsboard/before/direct_Gradle_task": true,
    "thingsboard/before/Java17": true,
    "thingsboard/before/FULL_mode": true,
    "thingsboard/before/statics_enabled": true,
    "thingsboard/before/default_aliases": true,
    "thingsboard/before/raw/sum_TAINT.shape.": true,
    "thingsboard/before/raw/sum_FLOW.shape.": true,
    "thingsboard/before/raw/sum_reason.": true,
    "thingsboard/before/raw/sum_method.": true,
    "thingsboard/before/raw/sum_FLOW.method.": true,
    "thingsboard/before/raw/sum_field.": true,
    "thingsboard/before/raw/sum_FLOW.field.": true,
    "thingsboard/before/raw/sum_group.": true,
    "thingsboard/before/raw/coverage_partition": true,
    "thingsboard/before/raw/normalized_boundary": true,
    "thingsboard/before/raw/flag_bounds": true,
    "thingsboard/before/raw/decoded_tree_partition": true,
    "thingsboard/before/raw/protection_class_membership_partition": true,
    "thingsboard/before/raw/decoded_backend_tree_partition": true,
    "thingsboard/before/raw/EmptyE_no_recorded_retained_violation": true,
    "thingsboard/before/raw/no_static_static_retained_violation": true,
    "thingsboard/before/raw/no_unexplained_normalizer_mismatch": true,
    "thingsboard/before/raw/all_retained_taint_DEMAND": true,
    "thingsboard/before/raw/no_static_static_shape": true,
    "thingsboard/before/raw/shape_flag_count": true,
    "thingsboard/before/raw/output_base_partition": true,
    "thingsboard/before/raw/protected_output_base_partition": true,
    "thingsboard/before/selected/sum_TAINT.shape.": true,
    "thingsboard/before/selected/sum_FLOW.shape.": true,
    "thingsboard/before/selected/sum_reason.": true,
    "thingsboard/before/selected/sum_method.": true,
    "thingsboard/before/selected/sum_FLOW.method.": true,
    "thingsboard/before/selected/sum_field.": true,
    "thingsboard/before/selected/sum_FLOW.field.": true,
    "thingsboard/before/selected/sum_group.": true,
    "thingsboard/before/selected/coverage_partition": true,
    "thingsboard/before/selected/normalized_boundary": true,
    "thingsboard/before/selected/flag_bounds": true,
    "thingsboard/before/selected/decoded_tree_partition": true,
    "thingsboard/before/selected/protection_class_membership_partition": true,
    "thingsboard/before/selected/decoded_backend_tree_partition": true,
    "thingsboard/before/selected/EmptyE_no_recorded_retained_violation": true,
    "thingsboard/before/selected/no_static_static_retained_violation": true,
    "thingsboard/before/selected/no_unexplained_normalizer_mismatch": true,
    "thingsboard/before/selected/all_retained_taint_DEMAND": true,
    "thingsboard/before/selected/no_static_static_shape": true,
    "thingsboard/before/selected/shape_flag_count": true,
    "thingsboard/before/selected/output_base_partition": true,
    "thingsboard/before/selected/protected_output_base_partition": true,
    "thingsboard/before/work_credit_reconciliation": true,
    "thingsboard/before/physical_work_reconciliation": true,
    "thingsboard/before/work_packed_reconciliation": true,
    "thingsboard/after/revision": true,
    "thingsboard/after/core_tree": true,
    "thingsboard/after/checker_version": true,
    "thingsboard/after/census_completed_run1": true,
    "thingsboard/after/summary_completed_run1": true,
    "thingsboard/after/engine_complete_marker": true,
    "thingsboard/after/normal_report_accepted_marker": true,
    "thingsboard/after/barrier_marker": true,
    "thingsboard/after/forward_limit1": true,
    "thingsboard/after/joined_capture_binding": true,
    "thingsboard/after/manifest_binding": true,
    "thingsboard/after/direct_Gradle_task": true,
    "thingsboard/after/Java17": true,
    "thingsboard/after/FULL_mode": true,
    "thingsboard/after/statics_enabled": true,
    "thingsboard/after/default_aliases": true,
    "thingsboard/after/raw/sum_TAINT.shape.": true,
    "thingsboard/after/raw/sum_FLOW.shape.": true,
    "thingsboard/after/raw/sum_reason.": true,
    "thingsboard/after/raw/sum_method.": true,
    "thingsboard/after/raw/sum_FLOW.method.": true,
    "thingsboard/after/raw/sum_field.": true,
    "thingsboard/after/raw/sum_FLOW.field.": true,
    "thingsboard/after/raw/sum_group.": true,
    "thingsboard/after/raw/coverage_partition": true,
    "thingsboard/after/raw/normalized_boundary": true,
    "thingsboard/after/raw/flag_bounds": true,
    "thingsboard/after/raw/decoded_tree_partition": true,
    "thingsboard/after/raw/protection_class_membership_partition": true,
    "thingsboard/after/raw/decoded_backend_tree_partition": true,
    "thingsboard/after/raw/EmptyE_no_recorded_retained_violation": true,
    "thingsboard/after/raw/no_static_static_retained_violation": true,
    "thingsboard/after/raw/no_unexplained_normalizer_mismatch": true,
    "thingsboard/after/raw/all_retained_taint_DEMAND": true,
    "thingsboard/after/raw/no_static_static_shape": true,
    "thingsboard/after/raw/shape_flag_count": true,
    "thingsboard/after/raw/output_base_partition": true,
    "thingsboard/after/raw/protected_output_base_partition": true,
    "thingsboard/after/selected/sum_TAINT.shape.": true,
    "thingsboard/after/selected/sum_FLOW.shape.": true,
    "thingsboard/after/selected/sum_reason.": true,
    "thingsboard/after/selected/sum_method.": true,
    "thingsboard/after/selected/sum_FLOW.method.": true,
    "thingsboard/after/selected/sum_field.": true,
    "thingsboard/after/selected/sum_FLOW.field.": true,
    "thingsboard/after/selected/sum_group.": true,
    "thingsboard/after/selected/coverage_partition": true,
    "thingsboard/after/selected/normalized_boundary": true,
    "thingsboard/after/selected/flag_bounds": true,
    "thingsboard/after/selected/decoded_tree_partition": true,
    "thingsboard/after/selected/protection_class_membership_partition": true,
    "thingsboard/after/selected/decoded_backend_tree_partition": true,
    "thingsboard/after/selected/EmptyE_no_recorded_retained_violation": true,
    "thingsboard/after/selected/no_static_static_retained_violation": true,
    "thingsboard/after/selected/no_unexplained_normalizer_mismatch": true,
    "thingsboard/after/selected/all_retained_taint_DEMAND": true,
    "thingsboard/after/selected/no_static_static_shape": true,
    "thingsboard/after/selected/shape_flag_count": true,
    "thingsboard/after/selected/output_base_partition": true,
    "thingsboard/after/selected/protected_output_base_partition": true,
    "thingsboard/after/work_credit_reconciliation": true,
    "thingsboard/after/physical_work_reconciliation": true,
    "thingsboard/after/work_packed_reconciliation": true,
    "thingsboard/fixed_config": true,
    "thingsboard/same_project_model": true,
    "thingsboard/same_test_revision": true,
    "conductor/before/revision": true,
    "conductor/before/core_tree": true,
    "conductor/before/checker_version": true,
    "conductor/before/census_completed_run1": true,
    "conductor/before/summary_completed_run1": true,
    "conductor/before/engine_complete_marker": true,
    "conductor/before/normal_report_accepted_marker": true,
    "conductor/before/barrier_marker": true,
    "conductor/before/forward_limit1": true,
    "conductor/before/joined_capture_binding": true,
    "conductor/before/manifest_binding": true,
    "conductor/before/direct_Gradle_task": true,
    "conductor/before/Java17": true,
    "conductor/before/FULL_mode": true,
    "conductor/before/statics_enabled": true,
    "conductor/before/default_aliases": true,
    "conductor/before/raw/sum_TAINT.shape.": true,
    "conductor/before/raw/sum_FLOW.shape.": true,
    "conductor/before/raw/sum_reason.": true,
    "conductor/before/raw/sum_method.": true,
    "conductor/before/raw/sum_FLOW.method.": true,
    "conductor/before/raw/sum_field.": true,
    "conductor/before/raw/sum_FLOW.field.": true,
    "conductor/before/raw/sum_group.": true,
    "conductor/before/raw/coverage_partition": true,
    "conductor/before/raw/normalized_boundary": true,
    "conductor/before/raw/flag_bounds": true,
    "conductor/before/raw/decoded_tree_partition": true,
    "conductor/before/raw/protection_class_membership_partition": true,
    "conductor/before/raw/decoded_backend_tree_partition": true,
    "conductor/before/raw/EmptyE_no_recorded_retained_violation": true,
    "conductor/before/raw/no_static_static_retained_violation": true,
    "conductor/before/raw/no_unexplained_normalizer_mismatch": true,
    "conductor/before/raw/all_retained_taint_DEMAND": true,
    "conductor/before/raw/no_static_static_shape": true,
    "conductor/before/raw/shape_flag_count": true,
    "conductor/before/raw/output_base_partition": true,
    "conductor/before/raw/protected_output_base_partition": true,
    "conductor/before/selected/sum_TAINT.shape.": true,
    "conductor/before/selected/sum_FLOW.shape.": true,
    "conductor/before/selected/sum_reason.": true,
    "conductor/before/selected/sum_method.": true,
    "conductor/before/selected/sum_FLOW.method.": true,
    "conductor/before/selected/sum_field.": true,
    "conductor/before/selected/sum_FLOW.field.": true,
    "conductor/before/selected/sum_group.": true,
    "conductor/before/selected/coverage_partition": true,
    "conductor/before/selected/normalized_boundary": true,
    "conductor/before/selected/flag_bounds": true,
    "conductor/before/selected/decoded_tree_partition": true,
    "conductor/before/selected/protection_class_membership_partition": true,
    "conductor/before/selected/decoded_backend_tree_partition": true,
    "conductor/before/selected/EmptyE_no_recorded_retained_violation": true,
    "conductor/before/selected/no_static_static_retained_violation": true,
    "conductor/before/selected/no_unexplained_normalizer_mismatch": true,
    "conductor/before/selected/all_retained_taint_DEMAND": true,
    "conductor/before/selected/no_static_static_shape": true,
    "conductor/before/selected/shape_flag_count": true,
    "conductor/before/selected/output_base_partition": true,
    "conductor/before/selected/protected_output_base_partition": true,
    "conductor/before/work_credit_reconciliation": true,
    "conductor/before/physical_work_reconciliation": true,
    "conductor/before/work_packed_reconciliation": true,
    "conductor/after/revision": true,
    "conductor/after/core_tree": true,
    "conductor/after/checker_version": true,
    "conductor/after/census_completed_run1": true,
    "conductor/after/summary_completed_run1": true,
    "conductor/after/engine_complete_marker": true,
    "conductor/after/normal_report_accepted_marker": true,
    "conductor/after/barrier_marker": true,
    "conductor/after/forward_limit1": true,
    "conductor/after/joined_capture_binding": true,
    "conductor/after/manifest_binding": true,
    "conductor/after/direct_Gradle_task": true,
    "conductor/after/Java17": true,
    "conductor/after/FULL_mode": true,
    "conductor/after/statics_enabled": true,
    "conductor/after/default_aliases": true,
    "conductor/after/raw/sum_TAINT.shape.": true,
    "conductor/after/raw/sum_FLOW.shape.": true,
    "conductor/after/raw/sum_reason.": true,
    "conductor/after/raw/sum_method.": true,
    "conductor/after/raw/sum_FLOW.method.": true,
    "conductor/after/raw/sum_field.": true,
    "conductor/after/raw/sum_FLOW.field.": true,
    "conductor/after/raw/sum_group.": true,
    "conductor/after/raw/coverage_partition": true,
    "conductor/after/raw/normalized_boundary": true,
    "conductor/after/raw/flag_bounds": true,
    "conductor/after/raw/decoded_tree_partition": true,
    "conductor/after/raw/protection_class_membership_partition": true,
    "conductor/after/raw/decoded_backend_tree_partition": true,
    "conductor/after/raw/EmptyE_no_recorded_retained_violation": true,
    "conductor/after/raw/no_static_static_retained_violation": true,
    "conductor/after/raw/no_unexplained_normalizer_mismatch": true,
    "conductor/after/raw/all_retained_taint_DEMAND": true,
    "conductor/after/raw/no_static_static_shape": true,
    "conductor/after/raw/shape_flag_count": true,
    "conductor/after/raw/output_base_partition": true,
    "conductor/after/raw/protected_output_base_partition": true,
    "conductor/after/selected/sum_TAINT.shape.": true,
    "conductor/after/selected/sum_FLOW.shape.": true,
    "conductor/after/selected/sum_reason.": true,
    "conductor/after/selected/sum_method.": true,
    "conductor/after/selected/sum_FLOW.method.": true,
    "conductor/after/selected/sum_field.": true,
    "conductor/after/selected/sum_FLOW.field.": true,
    "conductor/after/selected/sum_group.": true,
    "conductor/after/selected/coverage_partition": true,
    "conductor/after/selected/normalized_boundary": true,
    "conductor/after/selected/flag_bounds": true,
    "conductor/after/selected/decoded_tree_partition": true,
    "conductor/after/selected/protection_class_membership_partition": true,
    "conductor/after/selected/decoded_backend_tree_partition": true,
    "conductor/after/selected/EmptyE_no_recorded_retained_violation": true,
    "conductor/after/selected/no_static_static_retained_violation": true,
    "conductor/after/selected/no_unexplained_normalizer_mismatch": true,
    "conductor/after/selected/all_retained_taint_DEMAND": true,
    "conductor/after/selected/no_static_static_shape": true,
    "conductor/after/selected/shape_flag_count": true,
    "conductor/after/selected/output_base_partition": true,
    "conductor/after/selected/protected_output_base_partition": true,
    "conductor/after/work_credit_reconciliation": true,
    "conductor/after/physical_work_reconciliation": true,
    "conductor/after/work_packed_reconciliation": true,
    "conductor/fixed_config": true,
    "conductor/same_project_model": true,
    "conductor/same_test_revision": true,
    "Stirling-PDF/before/revision": true,
    "Stirling-PDF/before/core_tree": true,
    "Stirling-PDF/before/checker_version": true,
    "Stirling-PDF/before/census_completed_run1": true,
    "Stirling-PDF/before/summary_completed_run1": true,
    "Stirling-PDF/before/engine_complete_marker": true,
    "Stirling-PDF/before/normal_report_accepted_marker": true,
    "Stirling-PDF/before/barrier_marker": true,
    "Stirling-PDF/before/forward_limit1": true,
    "Stirling-PDF/before/joined_capture_binding": true,
    "Stirling-PDF/before/manifest_binding": true,
    "Stirling-PDF/before/direct_Gradle_task": true,
    "Stirling-PDF/before/Java17": true,
    "Stirling-PDF/before/FULL_mode": true,
    "Stirling-PDF/before/statics_enabled": true,
    "Stirling-PDF/before/default_aliases": true,
    "Stirling-PDF/before/raw/sum_TAINT.shape.": true,
    "Stirling-PDF/before/raw/sum_FLOW.shape.": true,
    "Stirling-PDF/before/raw/sum_reason.": true,
    "Stirling-PDF/before/raw/sum_method.": true,
    "Stirling-PDF/before/raw/sum_FLOW.method.": true,
    "Stirling-PDF/before/raw/sum_field.": true,
    "Stirling-PDF/before/raw/sum_FLOW.field.": true,
    "Stirling-PDF/before/raw/sum_group.": true,
    "Stirling-PDF/before/raw/coverage_partition": true,
    "Stirling-PDF/before/raw/normalized_boundary": true,
    "Stirling-PDF/before/raw/flag_bounds": true,
    "Stirling-PDF/before/raw/decoded_tree_partition": true,
    "Stirling-PDF/before/raw/protection_class_membership_partition": true,
    "Stirling-PDF/before/raw/decoded_backend_tree_partition": true,
    "Stirling-PDF/before/raw/EmptyE_no_recorded_retained_violation": true,
    "Stirling-PDF/before/raw/no_static_static_retained_violation": true,
    "Stirling-PDF/before/raw/no_unexplained_normalizer_mismatch": true,
    "Stirling-PDF/before/raw/all_retained_taint_DEMAND": true,
    "Stirling-PDF/before/raw/no_static_static_shape": true,
    "Stirling-PDF/before/raw/shape_flag_count": true,
    "Stirling-PDF/before/raw/output_base_partition": true,
    "Stirling-PDF/before/raw/protected_output_base_partition": true,
    "Stirling-PDF/before/selected/sum_TAINT.shape.": true,
    "Stirling-PDF/before/selected/sum_FLOW.shape.": true,
    "Stirling-PDF/before/selected/sum_reason.": true,
    "Stirling-PDF/before/selected/sum_method.": true,
    "Stirling-PDF/before/selected/sum_FLOW.method.": true,
    "Stirling-PDF/before/selected/sum_field.": true,
    "Stirling-PDF/before/selected/sum_FLOW.field.": true,
    "Stirling-PDF/before/selected/sum_group.": true,
    "Stirling-PDF/before/selected/coverage_partition": true,
    "Stirling-PDF/before/selected/normalized_boundary": true,
    "Stirling-PDF/before/selected/flag_bounds": true,
    "Stirling-PDF/before/selected/decoded_tree_partition": true,
    "Stirling-PDF/before/selected/protection_class_membership_partition": true,
    "Stirling-PDF/before/selected/decoded_backend_tree_partition": true,
    "Stirling-PDF/before/selected/EmptyE_no_recorded_retained_violation": true,
    "Stirling-PDF/before/selected/no_static_static_retained_violation": true,
    "Stirling-PDF/before/selected/no_unexplained_normalizer_mismatch": true,
    "Stirling-PDF/before/selected/all_retained_taint_DEMAND": true,
    "Stirling-PDF/before/selected/no_static_static_shape": true,
    "Stirling-PDF/before/selected/shape_flag_count": true,
    "Stirling-PDF/before/selected/output_base_partition": true,
    "Stirling-PDF/before/selected/protected_output_base_partition": true,
    "Stirling-PDF/before/work_credit_reconciliation": true,
    "Stirling-PDF/before/physical_work_reconciliation": true,
    "Stirling-PDF/before/work_packed_reconciliation": true,
    "Stirling-PDF/after/revision": true,
    "Stirling-PDF/after/core_tree": true,
    "Stirling-PDF/after/checker_version": true,
    "Stirling-PDF/after/census_completed_run1": true,
    "Stirling-PDF/after/summary_completed_run1": true,
    "Stirling-PDF/after/engine_complete_marker": true,
    "Stirling-PDF/after/normal_report_accepted_marker": true,
    "Stirling-PDF/after/barrier_marker": true,
    "Stirling-PDF/after/forward_limit1": true,
    "Stirling-PDF/after/joined_capture_binding": true,
    "Stirling-PDF/after/manifest_binding": true,
    "Stirling-PDF/after/direct_Gradle_task": true,
    "Stirling-PDF/after/Java17": true,
    "Stirling-PDF/after/FULL_mode": true,
    "Stirling-PDF/after/statics_enabled": true,
    "Stirling-PDF/after/default_aliases": true,
    "Stirling-PDF/after/raw/sum_TAINT.shape.": true,
    "Stirling-PDF/after/raw/sum_FLOW.shape.": true,
    "Stirling-PDF/after/raw/sum_reason.": true,
    "Stirling-PDF/after/raw/sum_method.": true,
    "Stirling-PDF/after/raw/sum_FLOW.method.": true,
    "Stirling-PDF/after/raw/sum_field.": true,
    "Stirling-PDF/after/raw/sum_FLOW.field.": true,
    "Stirling-PDF/after/raw/sum_group.": true,
    "Stirling-PDF/after/raw/coverage_partition": true,
    "Stirling-PDF/after/raw/normalized_boundary": true,
    "Stirling-PDF/after/raw/flag_bounds": true,
    "Stirling-PDF/after/raw/decoded_tree_partition": true,
    "Stirling-PDF/after/raw/protection_class_membership_partition": true,
    "Stirling-PDF/after/raw/decoded_backend_tree_partition": true,
    "Stirling-PDF/after/raw/EmptyE_no_recorded_retained_violation": true,
    "Stirling-PDF/after/raw/no_static_static_retained_violation": true,
    "Stirling-PDF/after/raw/no_unexplained_normalizer_mismatch": true,
    "Stirling-PDF/after/raw/all_retained_taint_DEMAND": true,
    "Stirling-PDF/after/raw/no_static_static_shape": true,
    "Stirling-PDF/after/raw/shape_flag_count": true,
    "Stirling-PDF/after/raw/output_base_partition": true,
    "Stirling-PDF/after/raw/protected_output_base_partition": true,
    "Stirling-PDF/after/selected/sum_TAINT.shape.": true,
    "Stirling-PDF/after/selected/sum_FLOW.shape.": true,
    "Stirling-PDF/after/selected/sum_reason.": true,
    "Stirling-PDF/after/selected/sum_method.": true,
    "Stirling-PDF/after/selected/sum_FLOW.method.": true,
    "Stirling-PDF/after/selected/sum_field.": true,
    "Stirling-PDF/after/selected/sum_FLOW.field.": true,
    "Stirling-PDF/after/selected/sum_group.": true,
    "Stirling-PDF/after/selected/coverage_partition": true,
    "Stirling-PDF/after/selected/normalized_boundary": true,
    "Stirling-PDF/after/selected/flag_bounds": true,
    "Stirling-PDF/after/selected/decoded_tree_partition": true,
    "Stirling-PDF/after/selected/protection_class_membership_partition": true,
    "Stirling-PDF/after/selected/decoded_backend_tree_partition": true,
    "Stirling-PDF/after/selected/EmptyE_no_recorded_retained_violation": true,
    "Stirling-PDF/after/selected/no_static_static_retained_violation": true,
    "Stirling-PDF/after/selected/no_unexplained_normalizer_mismatch": true,
    "Stirling-PDF/after/selected/all_retained_taint_DEMAND": true,
    "Stirling-PDF/after/selected/no_static_static_shape": true,
    "Stirling-PDF/after/selected/shape_flag_count": true,
    "Stirling-PDF/after/selected/output_base_partition": true,
    "Stirling-PDF/after/selected/protected_output_base_partition": true,
    "Stirling-PDF/after/work_credit_reconciliation": true,
    "Stirling-PDF/after/physical_work_reconciliation": true,
    "Stirling-PDF/after/work_packed_reconciliation": true,
    "Stirling-PDF/fixed_config": true,
    "Stirling-PDF/same_project_model": true,
    "Stirling-PDF/same_test_revision": true,
    "OWASP/before/revision": true,
    "OWASP/before/core_tree": true,
    "OWASP/before/checker_version": true,
    "OWASP/before/census_completed_run1": true,
    "OWASP/before/summary_completed_run1": true,
    "OWASP/before/engine_complete_marker": true,
    "OWASP/before/normal_report_accepted_marker": true,
    "OWASP/before/barrier_marker": true,
    "OWASP/before/forward_limit1": true,
    "OWASP/before/joined_capture_binding": true,
    "OWASP/before/manifest_binding": true,
    "OWASP/before/direct_Gradle_task": true,
    "OWASP/before/Java17": true,
    "OWASP/before/FULL_mode": true,
    "OWASP/before/statics_enabled": true,
    "OWASP/before/default_aliases": true,
    "OWASP/before/raw/sum_TAINT.shape.": true,
    "OWASP/before/raw/sum_FLOW.shape.": true,
    "OWASP/before/raw/sum_reason.": true,
    "OWASP/before/raw/sum_method.": true,
    "OWASP/before/raw/sum_FLOW.method.": true,
    "OWASP/before/raw/sum_field.": true,
    "OWASP/before/raw/sum_FLOW.field.": true,
    "OWASP/before/raw/sum_group.": true,
    "OWASP/before/raw/coverage_partition": true,
    "OWASP/before/raw/normalized_boundary": true,
    "OWASP/before/raw/flag_bounds": true,
    "OWASP/before/raw/decoded_tree_partition": true,
    "OWASP/before/raw/protection_class_membership_partition": true,
    "OWASP/before/raw/decoded_backend_tree_partition": true,
    "OWASP/before/raw/EmptyE_no_recorded_retained_violation": true,
    "OWASP/before/raw/no_static_static_retained_violation": true,
    "OWASP/before/raw/no_unexplained_normalizer_mismatch": true,
    "OWASP/before/raw/all_retained_taint_DEMAND": true,
    "OWASP/before/raw/no_static_static_shape": true,
    "OWASP/before/raw/shape_flag_count": true,
    "OWASP/before/raw/output_base_partition": true,
    "OWASP/before/raw/protected_output_base_partition": true,
    "OWASP/before/selected/sum_TAINT.shape.": true,
    "OWASP/before/selected/sum_FLOW.shape.": true,
    "OWASP/before/selected/sum_reason.": true,
    "OWASP/before/selected/sum_method.": true,
    "OWASP/before/selected/sum_FLOW.method.": true,
    "OWASP/before/selected/sum_field.": true,
    "OWASP/before/selected/sum_FLOW.field.": true,
    "OWASP/before/selected/sum_group.": true,
    "OWASP/before/selected/coverage_partition": true,
    "OWASP/before/selected/normalized_boundary": true,
    "OWASP/before/selected/flag_bounds": true,
    "OWASP/before/selected/decoded_tree_partition": true,
    "OWASP/before/selected/protection_class_membership_partition": true,
    "OWASP/before/selected/decoded_backend_tree_partition": true,
    "OWASP/before/selected/EmptyE_no_recorded_retained_violation": true,
    "OWASP/before/selected/no_static_static_retained_violation": true,
    "OWASP/before/selected/no_unexplained_normalizer_mismatch": true,
    "OWASP/before/selected/all_retained_taint_DEMAND": true,
    "OWASP/before/selected/no_static_static_shape": true,
    "OWASP/before/selected/shape_flag_count": true,
    "OWASP/before/selected/output_base_partition": true,
    "OWASP/before/selected/protected_output_base_partition": true,
    "OWASP/before/work_credit_reconciliation": true,
    "OWASP/before/physical_work_reconciliation": true,
    "OWASP/before/work_packed_reconciliation": true,
    "OWASP/after/revision": true,
    "OWASP/after/core_tree": true,
    "OWASP/after/checker_version": true,
    "OWASP/after/census_completed_run1": true,
    "OWASP/after/summary_completed_run1": true,
    "OWASP/after/engine_complete_marker": true,
    "OWASP/after/normal_report_accepted_marker": true,
    "OWASP/after/barrier_marker": true,
    "OWASP/after/forward_limit1": true,
    "OWASP/after/joined_capture_binding": true,
    "OWASP/after/manifest_binding": true,
    "OWASP/after/direct_Gradle_task": true,
    "OWASP/after/Java17": true,
    "OWASP/after/FULL_mode": true,
    "OWASP/after/statics_enabled": true,
    "OWASP/after/default_aliases": true,
    "OWASP/after/raw/sum_TAINT.shape.": true,
    "OWASP/after/raw/sum_FLOW.shape.": true,
    "OWASP/after/raw/sum_reason.": true,
    "OWASP/after/raw/sum_method.": true,
    "OWASP/after/raw/sum_FLOW.method.": true,
    "OWASP/after/raw/sum_field.": true,
    "OWASP/after/raw/sum_FLOW.field.": true,
    "OWASP/after/raw/sum_group.": true,
    "OWASP/after/raw/coverage_partition": true,
    "OWASP/after/raw/normalized_boundary": true,
    "OWASP/after/raw/flag_bounds": true,
    "OWASP/after/raw/decoded_tree_partition": true,
    "OWASP/after/raw/protection_class_membership_partition": true,
    "OWASP/after/raw/decoded_backend_tree_partition": true,
    "OWASP/after/raw/EmptyE_no_recorded_retained_violation": true,
    "OWASP/after/raw/no_static_static_retained_violation": true,
    "OWASP/after/raw/no_unexplained_normalizer_mismatch": true,
    "OWASP/after/raw/all_retained_taint_DEMAND": true,
    "OWASP/after/raw/no_static_static_shape": true,
    "OWASP/after/raw/shape_flag_count": true,
    "OWASP/after/raw/output_base_partition": true,
    "OWASP/after/raw/protected_output_base_partition": true,
    "OWASP/after/selected/sum_TAINT.shape.": true,
    "OWASP/after/selected/sum_FLOW.shape.": true,
    "OWASP/after/selected/sum_reason.": true,
    "OWASP/after/selected/sum_method.": true,
    "OWASP/after/selected/sum_FLOW.method.": true,
    "OWASP/after/selected/sum_field.": true,
    "OWASP/after/selected/sum_FLOW.field.": true,
    "OWASP/after/selected/sum_group.": true,
    "OWASP/after/selected/coverage_partition": true,
    "OWASP/after/selected/normalized_boundary": true,
    "OWASP/after/selected/flag_bounds": true,
    "OWASP/after/selected/decoded_tree_partition": true,
    "OWASP/after/selected/protection_class_membership_partition": true,
    "OWASP/after/selected/decoded_backend_tree_partition": true,
    "OWASP/after/selected/EmptyE_no_recorded_retained_violation": true,
    "OWASP/after/selected/no_static_static_retained_violation": true,
    "OWASP/after/selected/no_unexplained_normalizer_mismatch": true,
    "OWASP/after/selected/all_retained_taint_DEMAND": true,
    "OWASP/after/selected/no_static_static_shape": true,
    "OWASP/after/selected/shape_flag_count": true,
    "OWASP/after/selected/output_base_partition": true,
    "OWASP/after/selected/protected_output_base_partition": true,
    "OWASP/after/work_credit_reconciliation": true,
    "OWASP/after/physical_work_reconciliation": true,
    "OWASP/after/work_packed_reconciliation": true,
    "OWASP/fixed_config": true,
    "OWASP/same_project_model": true,
    "OWASP/same_test_revision": true,
    "control/baseline_five_controls": true,
    "control/baseline_source_unchanged": true,
    "control/current_seven_controls": true,
    "control/current_source_unchanged": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/FlowBackedSummaries.kt": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DiagonalRelations.kt": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/RunSummaries.kt": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineRun1ShapeCensus.kt": true,
    "baseline_installed_file/core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineRun1ShapeCensusTest.kt": true,
    "old_policy_unchanged/ap/FlowBackedCoverage.kt": true,
    "old_policy_unchanged/ap/Run1SummaryAliases.kt": true,
    "old_policy_unchanged/normalize_body": true,
    "catalog/before/clean_tracked_rule_tree": true,
    "catalog/before/no_untracked_rule_files": true,
    "catalog/after/clean_tracked_rule_tree": true,
    "catalog/after/no_untracked_rule_files": true,
    "catalog/identical_branch_catalog_tree": true,
    "regex/actual_four_AP_controls_pass": true,
    "regex/source_unchanged": true,
    "regex/no_historical_first_producer_claim": true,
    "current_example/example-raw_PROTECTION_ONLY-0.json": true,
    "current_example/example-raw_PROTECTION_ONLY-1.json": true,
    "current_example/example-raw_UNSUPPORTED_INITIAL-0.json": true,
    "current_example/example-raw_UNSUPPORTED_INITIAL-1.json": true,
    "current_example/example-raw_CROSS_ATOM-0.json": true,
    "current_example/example-raw_CROSS_ATOM-1.json": true,
    "current_example/example-raw_NO_FLOW_COUNTERPART-0.json": true,
    "current_example/example-raw_NO_FLOW_COUNTERPART-1.json": true,
    "current_example/example-raw_MARK_EXCLUDED-0.json": true,
    "current_example/example-raw_MARK_EXCLUDED-1.json": true,
    "current_example/example-raw_OUTPUT_BASE_MISMATCH-0.json": true,
    "current_example/example-raw_OUTPUT_BASE_MISMATCH-1.json": true,
    "current_example/example-raw_ZERO_INITIAL-0.json": true,
    "current_example/example-raw_ZERO_INITIAL-1.json": true,
    "current_example/example-raw_UNSUPPORTED_OUTPUT-0.json": true,
    "current_example/example-raw_UNSUPPORTED_OUTPUT-1.json": true,
    "current_example/example-raw_OUTPUT_TAIL_MISMATCH-0.json": true,
    "current_examples_17": true,
    "baseline_campaign/closed_four": true,
    "baseline_campaign/thingsboard/census_hash": true,
    "baseline_campaign/thingsboard/summary_hash": true,
    "baseline_campaign/conductor/census_hash": true,
    "baseline_campaign/conductor/summary_hash": true,
    "baseline_campaign/Stirling-PDF/census_hash": true,
    "baseline_campaign/Stirling-PDF/summary_hash": true,
    "baseline_campaign/OWASP/census_hash": true,
    "baseline_campaign/OWASP/summary_hash": true
  },
  "all_available_checks_pass": true,
  "check_count": 564,
  "control_receipts": {
    "baseline-shape-probe/terminal.json": {
      "path": "validation/baseline-shape-probe/terminal.json",
      "sha256": "8bd44f2d77134eaf3ea65091d6ea28f0568f9d95b88730e1fc67fdf2e181cac1"
    },
    "baseline-shape-probe/prepared.json": {
      "path": "validation/baseline-shape-probe/prepared.json",
      "sha256": "226b05d94ec192c77fc0b7335dc08907433c1b166a1723a580eeae4626bfa724"
    },
    "shape-probe/terminal.json": {
      "path": "validation/shape-probe/terminal.json",
      "sha256": "89c0f92102dd112c2ca796daef937fa43d6201d756ab2c6dd0102439b59de4ff"
    },
    "cassandra-regex-ap-replay/report.json": {
      "path": "validation/cassandra-regex-ap-replay/report.json",
      "sha256": "c9f7b77439232be5989752beb978efd650030856b40d6e069a2457ba8c342774"
    },
    "cassandra-regex-ap-replay/terminal.json": {
      "path": "validation/cassandra-regex-ap-replay/terminal.json",
      "sha256": "f3325b49958d0d972daceedd75aa7f11969d6466e79d8158a9bcffd4ac63377b"
    },
    "final-run1-shapes/evidence.json": {
      "path": "validation/final-run1-shapes/evidence.json",
      "sha256": "ab48f076c84f62b78cb5396037493d3c128f309736acec8a9afe78839ee648d4"
    },
    "baseline_installed_manifest": {
      "path": "baseline-diagnostic-source/baseline-shape-probe-manifest.json",
      "sha256": "1146fcf1254badf3f01adb774926d53b4ff718c2e4310153a0a1668b81d7d9fa"
    }
  },
  "current_examples": [
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_PROTECTION_ONLY-0.json",
      "sha256": "b14055e692d16ac31be19f0643213189938644b73bf8ef80ea8100b92abf3fce",
      "reason": "PROTECTION_ONLY",
      "method": "org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_PROTECTION_ONLY-1.json",
      "sha256": "c3ed4acd5a27f3d8dcabdeb7edd0cb99fb2a25f9d496113ff3fc5ebfe3e27953",
      "reason": "PROTECTION_ONLY",
      "method": "org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_INITIAL-0.json",
      "sha256": "f241cc39268bb43dbf754bc4cd13230fb1bee3c9cf87b4fd27c66e7550d4b057",
      "reason": "UNSUPPORTED_INITIAL",
      "method": "org.thingsboard.server.controller.AuthController#checkActivateToken(java.lang.String) [{}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_INITIAL-1.json",
      "sha256": "d715e5dce4d4400b6d287b8fabcc6d88d75de5b63d424905c880c4761802c420",
      "reason": "UNSUPPORTED_INITIAL",
      "method": "org.thingsboard.server.controller.AuthController#checkResetToken(java.lang.String) [{}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_CROSS_ATOM-0.json",
      "sha256": "b8b8b1c2e259af1229098e91d3e3e6d0515da0fb243e5dc34b0f600ef2512270",
      "reason": "CROSS_ATOM",
      "method": "org.thingsboard.server.controller.QrCodeSettingsController#getAppleAppSiteAssociation() [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_CROSS_ATOM-1.json",
      "sha256": "26af7470cc7b615404bec5a31a48e7fb84b408ce56205e1ceccfb6537d5d48f5",
      "reason": "CROSS_ATOM",
      "method": "org.thingsboard.server.controller.QrCodeSettingsController#getAssetLinks() [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_NO_FLOW_COUNTERPART-0.json",
      "sha256": "101aebd367de20e3c82d9ab25a2212bfbb059a0689ae39def447129b07655921",
      "reason": "NO_FLOW_COUNTERPART",
      "method": "org.thingsboard.rule.engine.ai.Langchain4jJsonSchemaAdapter#parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_NO_FLOW_COUNTERPART-1.json",
      "sha256": "1d7be6c582fb565e7d102e9cf52272197f2430254bc520c08688058e42dc9666",
      "reason": "NO_FLOW_COUNTERPART",
      "method": "org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx#evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_MARK_EXCLUDED-0.json",
      "sha256": "7ec7ac3dca89b238acbd929b5f8e491a22655a5d69e5cf04876b94a814511a8e",
      "reason": "MARK_EXCLUDED",
      "method": "org.thingsboard.server.transport.mqtt.HashMapObserver#getActiveSessions(java.lang.String) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_MARK_EXCLUDED-1.json",
      "sha256": "1a8df83296403089d5362c79be9aa0fc6f6c942fc4bfc99e157bc0498b8327cc",
      "reason": "MARK_EXCLUDED",
      "method": "org.thingsboard.server.transport.mqtt.HashMapObserver#getAllSessions(java.lang.String) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_BASE_MISMATCH-0.json",
      "sha256": "e5177caa44b5da34fe649ab94e028296bb58d768933346ee2977d713d861208e",
      "reason": "OUTPUT_BASE_MISMATCH",
      "method": "org.thingsboard.server.common.adaptor.JsonConverter#parseValues(com.google.gson.JsonObject) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_BASE_MISMATCH-1.json",
      "sha256": "a3dd1ccf9e6789b68cc75bd24d1628dfc9b1f2b543c91612802268fd26367aed",
      "reason": "OUTPUT_BASE_MISMATCH",
      "method": "org.thingsboard.server.common.adaptor.JsonConverter#parseProtoValues(com.google.gson.JsonObject) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_ZERO_INITIAL-0.json",
      "sha256": "61fc1123726d5cc0d871fc4ed190a396d7137cf3892409dd9df025db02d051c9",
      "reason": "ZERO_INITIAL",
      "method": "org.thingsboard.server.config.WebConfig#redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_ZERO_INITIAL-1.json",
      "sha256": "d6f8b159c72b31f82e59da00473ed14614e2060cb9ca959d3e3569c06cc4294c",
      "reason": "ZERO_INITIAL",
      "method": "org.thingsboard.server.controller.AdminController#checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]",
      "flow_candidates": 0
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_OUTPUT-0.json",
      "sha256": "354e09abe9299353a4840b9ec077ee3a9761870f90825d288bf154166328356d",
      "reason": "UNSUPPORTED_OUTPUT",
      "method": "org.thingsboard.server.controller.AuthController#logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_UNSUPPORTED_OUTPUT-1.json",
      "sha256": "c0feb59b4c399c7c55164fa619b7dfa5118debc2820c9d0e7ddb7a711a579a4b",
      "reason": "UNSUPPORTED_OUTPUT",
      "method": "org.thingsboard.server.controller.DashboardController#saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]",
      "flow_candidates": 1
    },
    {
      "path": "shape-probe-results/thingsboard/bidi/shapes/example-raw_OUTPUT_TAIL_MISMATCH-0.json",
      "sha256": "17d6d68706655294df192af2518a3b4f4723e1ced401cf6280a7659d1002fcc9",
      "reason": "OUTPUT_TAIL_MISMATCH",
      "method": "org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]",
      "flow_candidates": 2
    }
  ],
  "baseline_campaign": {
    "state": "CLOSED",
    "input": {
      "path": "preparation/baseline-shape-probe-campaign.json",
      "sha256": "ca8570b115de6208c68b77ca18b96171abb548949f693bddd884b4bf3b6b0247"
    },
    "completed": [
      {
        "project": "thingsboard",
        "status": "HARD_TIMEOUT",
        "summary": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/summary.json",
        "summary_sha256": "9d4429ca5f5589218a60898eef2841d9a1846f818b39f32117bf806bac48d118",
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "shape_census_present": true,
        "ended_utc": "2026-10-27T00:00:12.438420+00:00",
        "shape_census": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/shapes/run1-shapes.json",
        "shape_census_sha256": "f2d5d5d96fc8d76c7305d4f5e79e77a82ef7c0286b3d303a25b8c25c9fb835b0"
      },
      {
        "project": "conductor",
        "status": "OK",
        "summary": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/summary.json",
        "summary_sha256": "df3eabd153e7f8455d3c1b1eabf58747e3068fe7e89496492af700dafbea41d2",
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "shape_census_present": true,
        "ended_utc": "2026-10-27T00:03:25.034014+00:00",
        "shape_census": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/shapes/run1-shapes.json",
        "shape_census_sha256": "e8480ce429204ae4c8e2a808a15793b51a6dcaacdbbc679d694dfd06a7f9b57f"
      },
      {
        "project": "Stirling-PDF",
        "status": "OK",
        "summary": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/summary.json",
        "summary_sha256": "d61023d04372bf96c6d4da94375d5216cad94b1ea44ce16248bae8744d39c916",
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "shape_census_present": true,
        "ended_utc": "2026-10-27T00:05:56.491417+00:00",
        "shape_census": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/shapes/run1-shapes.json",
        "shape_census_sha256": "468ca78501bbfb08ca7a5900fc98a2424bd91d571e7d36940e03a70cc10e647a"
      },
      {
        "project": "OWASP",
        "status": "OK",
        "summary": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/summary.json",
        "summary_sha256": "36d8ccf2c66fca71d33c4ce024f4ca0d173411f5fe389f97db2db086829c2985",
        "latest_reached": "run-1",
        "latest_completed": "run-1",
        "latest_accepted_forward": "run-1",
        "shape_census_present": true,
        "ended_utc": "2026-10-27T00:12:17.123768+00:00",
        "shape_census": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/shapes/run1-shapes.json",
        "shape_census_sha256": "974de76841eb86c316c3370aa6b25b7da273facdd0fd83f50108b7d663334d2c"
      }
    ]
  },
  "baseline_queue": {
    "state": "FAILED",
    "input": {
      "path": "preparation/baseline-shape-queue.json",
      "sha256": "4ca7ea88e1faef716e5d49c2ab36f28ab235f10dc0deda8524bf4b6ba613c981"
    },
    "interpretation": "Strict all-OK outer queue status is preserved; it is not the accepted/completed joined-census validity gate."
  },
  "rule_catalog_source_check": {
    "before": {
      "committed_tree": "95cc67c171d6cd3d1e94cca1f1caf795754ee31c",
      "tracked_diff_empty": true,
      "untracked_rule_files": []
    },
    "after": {
      "committed_tree": "95cc67c171d6cd3d1e94cca1f1caf795754ee31c",
      "tracked_diff_empty": true,
      "untracked_rule_files": []
    }
  },
  "regex_replay": {
    "input": {
      "path": "validation/cassandra-regex-ap-replay/report.json",
      "sha256": "c9f7b77439232be5989752beb978efd650030856b40d6e069a2457ba8c342774"
    },
    "tests": {
      "tests": 4,
      "failures": 0,
      "errors": 0,
      "skipped": 0
    },
    "scope": [
      "ApOps.applyEdge for the copied source-valid regex model positions",
      "ApOps.limit(fieldLimit=1)",
      "FlowBackedSummaries.add/normalize using actual corrected fcfe owner"
    ],
    "controls": {
      "order-and-layer-controls.json": {
        "reverse_order": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "demand_any_then_normal_star": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "NORMAL",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "weak_flow_normal_taint": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@492691d7",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "NORMAL",
                "protected": false
              }
            ]
          }
        ]
      },
      "any-first-same-layer.json": {
        "flow_any_admitted": true,
        "later_flow_star_admitted": false,
        "marked_any_admitted": false,
        "marked_star_admitted": true,
        "t_handle": 3,
        "stored": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6af9fcb2",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@ca30bc1",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "later_star_scope": "A legal DEMAND STAR header is offered as an admission control; its producer is not claimed.",
        "historical_offer_order_claimed": false
      },
      "protected-field-cut.json": {
        "steps": [
          [
            {
              "base": "arg(0)",
              "path": [],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group",
                "String#content"
              ],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group"
              ],
              "tail": "ANY",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ]
        ],
        "stored": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6fa34d52",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@4671115f",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": true
              }
            ]
          }
        ],
        "protected_memberships": 1
      },
      "regex-field-cut.json": {
        "checker": "actual-fcfe-AP",
        "mark_names_in_handle_order": [
          "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
          "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
          "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3"
        ],
        "input_scope": "The observed excluded marks1/2 are supplied on the operand to isolate geometry; their producer is not replayed.",
        "steps": [
          [
            {
              "base": "arg(0)",
              "path": [],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group",
                "String#content"
              ],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group"
              ],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ],
          [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        ],
        "historical_first_producer_claimed": false
      }
    },
    "origin_limit": "Actual AP field-cut mechanism and owner/order controls, not the historical first producer of the sampled summary."
  },
  "analysis_script": {
    "path": "validation/final_before_after_shapes.py",
    "sha256": "2c4ab529e1fdd6d711e49079c872ced7306290ee5d414b304c3609d43e966f3a"
  },
  "limits": [
    "Separate diagnostic executions. Do not use their elapsed times as the fixed timed engine comparison.",
    "Own-policy before/after classification, not one unified predicate and not matched edge histories. Old alias primary reason precedes FLOW candidate geometry checks.",
    "Raw and selected are separate owners; do not add counts. A selected-only flag difference is preserved explicitly.",
    "Removal counts are logical output-membership event weights, may include repeated offers; no distinct removed-edge archive is inferred.",
    "No nonzero recorded retained-E/static-static violations is a census result, not a whole-engine invariant proof.",
    "Full per-key shape histograms are logical output memberships. Physical diagonal/scalar rows cannot replace those counts.",
    "Outer HARD_TIMEOUT does not invalidate an already completed, joined, report-accepted run1 census; SARIF absence remains unavailable.",
    "No runtime, campaign helper, queue, source, project or JVM was changed or started by this analysis."
  ],
  "evidence_root": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026",
  "path_rule": "Artifact paths without an absolute prefix are relative to evidence_root."
}
```

</details>

<a id="inline-current-support-data"></a>
### Complete current support counts, work partitions and checks

<details>
<summary>Full record; SHA-256 ab48f076c84f62b78cb5396037493d3c128f309736acec8a9afe78839ee648d4</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/evidence.json`.

```json
{
  "state": "SOURCE_BOUND_JOINED_RUN1_RECONCILIATION",
  "latest_reached": "run-1",
  "latest_completed": "run-1",
  "latest_accepted_forward": "run-1",
  "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
  "captured_at": "joined_engine_barrier; written after report and handoff",
  "scope": "Separate Thingsboard joined diagnostic. Raw and selected are equal for retained data and are not additive. Not a timed campaign or byte measurement.",
  "checks": {
    "actor_steps": true,
    "physical_calls": true,
    "actor_packed_calls": true,
    "actor_packed_credits": true,
    "work_partition.scalar_headers": true,
    "work_partition.packed_invocations": true,
    "work_partition.packed_mark_credits": true,
    "work_partition.resume_events": true,
    "work_partition.statement_untouched_from_process": true,
    "work_partition.statement_pure_untouched_from_process": true,
    "work_partition.statement_untouched_from_resume": true,
    "work_partition.statement_pure_untouched_from_resume": true,
    "work_partition.packed_untouched_callbacks": true,
    "work_partition.packed_untouched_mark_credits": true,
    "work_partition.scalar_taint_headers": true,
    "work_partition.scalar_fully_protected_identity_headers": true,
    "work_partition.packed_fully_protected_identity_invocations": true,
    "work_partition.packed_fully_protected_identity_mark_credits": true,
    "work_partition.resume_taint_headers": true,
    "work_partition.resume_fully_protected_identity_headers": true,
    "stored_partition.TAINT.shape.": true,
    "stored_partition.FLOW.shape.": true,
    "stored_partition.method.": true,
    "stored_partition.FLOW.method.": true,
    "stored_partition.field.": true,
    "stored_partition.FLOW.field.": true,
    "stored_partition.group.": true,
    "stored_partition.reason.": true,
    "coverage_partition": true,
    "decoded_trees": true,
    "protection_tree_partition": true,
    "protection_tree_membership_partition": true,
    "only_expected_raw_selected_event_difference": true,
    "template.relation_rows": true,
    "template.distinct_templates": true,
    "template.distinct_origin_pairs": true,
    "template.repeated_origin_pairs": true,
    "template.same_origin_duplicate_rows": true,
    "template.repeated_templates": true,
    "template.relation_memberships": true,
    "template.distinct_pair_memberships": true,
    "template.template_memberships": true,
    "template.repeated_pair_memberships": true,
    "template.max_origin_width": true,
    "untruncated.example-raw_PROTECTION_ONLY-0.json": true,
    "complete_flow_list.example-raw_PROTECTION_ONLY-0.json": true,
    "untruncated.example-raw_PROTECTION_ONLY-1.json": true,
    "complete_flow_list.example-raw_PROTECTION_ONLY-1.json": true,
    "untruncated.example-raw_UNSUPPORTED_INITIAL-0.json": true,
    "complete_flow_list.example-raw_UNSUPPORTED_INITIAL-0.json": true,
    "untruncated.example-raw_UNSUPPORTED_INITIAL-1.json": true,
    "complete_flow_list.example-raw_UNSUPPORTED_INITIAL-1.json": true,
    "untruncated.example-raw_CROSS_ATOM-0.json": true,
    "complete_flow_list.example-raw_CROSS_ATOM-0.json": true,
    "untruncated.example-raw_CROSS_ATOM-1.json": true,
    "complete_flow_list.example-raw_CROSS_ATOM-1.json": true,
    "untruncated.example-raw_NO_FLOW_COUNTERPART-0.json": true,
    "complete_flow_list.example-raw_NO_FLOW_COUNTERPART-0.json": true,
    "untruncated.example-raw_NO_FLOW_COUNTERPART-1.json": true,
    "complete_flow_list.example-raw_NO_FLOW_COUNTERPART-1.json": true,
    "untruncated.example-raw_MARK_EXCLUDED-0.json": true,
    "complete_flow_list.example-raw_MARK_EXCLUDED-0.json": true,
    "untruncated.example-raw_MARK_EXCLUDED-1.json": true,
    "complete_flow_list.example-raw_MARK_EXCLUDED-1.json": true,
    "untruncated.example-raw_OUTPUT_BASE_MISMATCH-0.json": true,
    "complete_flow_list.example-raw_OUTPUT_BASE_MISMATCH-0.json": true,
    "untruncated.example-raw_OUTPUT_BASE_MISMATCH-1.json": true,
    "complete_flow_list.example-raw_OUTPUT_BASE_MISMATCH-1.json": true,
    "untruncated.example-raw_ZERO_INITIAL-0.json": true,
    "complete_flow_list.example-raw_ZERO_INITIAL-0.json": true,
    "untruncated.example-raw_ZERO_INITIAL-1.json": true,
    "complete_flow_list.example-raw_ZERO_INITIAL-1.json": true,
    "untruncated.example-raw_UNSUPPORTED_OUTPUT-0.json": true,
    "complete_flow_list.example-raw_UNSUPPORTED_OUTPUT-0.json": true,
    "untruncated.example-raw_UNSUPPORTED_OUTPUT-1.json": true,
    "complete_flow_list.example-raw_UNSUPPORTED_OUTPUT-1.json": true,
    "untruncated.example-raw_OUTPUT_TAIL_MISMATCH-0.json": true,
    "complete_flow_list.example-raw_OUTPUT_TAIL_MISMATCH-0.json": true,
    "top_method.org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#processUplinkMsg(org.thingsboard.server.gen.edge.v1.UplinkMsg) [{}]": true,
    "top_method.org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.common.util.JacksonUtil$replaceAllByMapping_27c33466$jIR_lambda$0/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]": true,
    "top_method.org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.server.dao.resource.BaseResourceService$processResources_fc592dee$jIR_lambda$18/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]": true,
    "top_method.org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#lambda$scheduleDownlinkMsgsPackSend$5(int) [{}]": true,
    "top_method.org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{}]": true,
    "top_method.org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{arg(0) is org.thingsboard.server.actors.ruleChain.DefaultTbContext}]": true,
    "top_method.org.thingsboard.server.gen.edge.v1.DownlinkMsg#getSerializedSize() [{}]": true,
    "top_method.org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{}]": true,
    "top_method.org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{arg(2) == (lambda: org.thingsboard.server.service.sync.ie.importing.impl.RuleChainImportService$saveOrUpdate_3af00c54$jIR_lambda$15/java.util.function.Function#apply(java.lang.Object))}]": true,
    "top_method.org.thingsboard.common.util.JacksonUtil#replaceAll(com.fasterxml.jackson.databind.JsonNode, java.lang.String, java.util.function.BiFunction) [{arg(2) == (lambda: org.thingsboard.server.dao.resource.BaseImageService$convertToImageUrls_69156998$jIR_lambda$2/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]": true,
    "top_method.org.thingsboard.server.service.entitiy.queue.DefaultTbQueueService#updateQueuesByTenants(java.util.List, org.thingsboard.server.common.data.TenantProfile, org.thingsboard.server.common.data.TenantProfile) [{}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.transport.coap.client.DefaultCoapClientContext$CoapSessionListener#onToDeviceRpcRequest(java.util.UUID, org.thingsboard.server.gen.transport.TransportProtos$ToDeviceRpcRequestMsg) [{}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo}]": true,
    "top_method.org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(1) is org.thingsboard.server.common.data.TbResourceInfo}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true,
    "top_method.org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]": true
  },
  "all_checks_pass": true,
  "raw_selected_differences": {
    "event.covered_offer_rejections": {
      "raw": 7327506,
      "selected": 0
    }
  },
  "work_totals": {
    "scalar_headers": 140288224,
    "packed_invocations": 3618887,
    "packed_mark_credits": 6789565,
    "resume_events": 1011222,
    "physical_method_edge_invocations": 143907111,
    "statement_untouched_from_process": 86690000,
    "statement_pure_untouched_from_process": 71897409,
    "statement_untouched_from_resume": 0,
    "statement_pure_untouched_from_resume": 0,
    "packed_untouched_callbacks": 3164550,
    "packed_untouched_mark_credits": 5954705,
    "scalar_taint_headers": 128093674,
    "scalar_fully_protected_identity_headers": 275612,
    "packed_fully_protected_identity_invocations": 2787,
    "packed_fully_protected_identity_mark_credits": 7233,
    "resume_taint_headers": 1006505,
    "resume_fully_protected_identity_headers": 0
  },
  "actor_totals": {
    "actors": 73669,
    "steps": 147077789,
    "neutralBatchApplications": 3618887,
    "neutralBatchMemberships": 6789565
  },
  "work_partitions": {
    "scalar_headers": {
      "ZERO|ZERO|REACH|NORMAL": 1037448,
      "ZERO|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 491430,
      "ZERO|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 131028,
      "ZERO|NONSTATIC|TAINT_MUST_NONEXACT|DEMAND": 404181,
      "FLOW|NONSTATIC|FLOW_STAR|NORMAL": 2262662,
      "FLOW|NONSTATIC|FLOW_STAR|DEMAND": 294004,
      "FLOW|NONSTATIC|FLOW_ANY|DEMAND": 8600436,
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 787004,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 37772585,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 88507446
    },
    "packed_invocations": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 1467,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 1102981,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 2514439
    },
    "packed_mark_credits": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 2903,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 2477854,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 4308808
    },
    "resume_events": {
      "StatementInput|FLOW|STATIC|FLOW_STAR|DEMAND": 418,
      "StatementInput|FLOW|STATIC|FLOW_ANY|DEMAND": 4299,
      "BoundaryInput/END|CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 46747,
      "CallStageInput|CONCRETE|STATIC|TAINT_EXACT_ONLY|DEMAND": 2250,
      "CallStageInput|CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 114,
      "CallStageInput|CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 955325,
      "CleanerInput/CLEAN|CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 2069
    },
    "statement_untouched_from_process": {
      "ZERO|ZERO|REACH|NORMAL": 736876,
      "ZERO|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 314447,
      "ZERO|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 76834,
      "ZERO|NONSTATIC|TAINT_MUST_NONEXACT|DEMAND": 249634,
      "FLOW|NONSTATIC|FLOW_STAR|NORMAL": 1407487,
      "FLOW|NONSTATIC|FLOW_STAR|DEMAND": 207510,
      "FLOW|NONSTATIC|FLOW_ANY|DEMAND": 6276082,
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 514026,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 22466980,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 54440124
    },
    "statement_pure_untouched_from_process": {
      "ZERO|ZERO|REACH|NORMAL": 593302,
      "ZERO|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 267465,
      "ZERO|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 64049,
      "ZERO|NONSTATIC|TAINT_MUST_NONEXACT|DEMAND": 204358,
      "FLOW|NONSTATIC|FLOW_STAR|NORMAL": 1185345,
      "FLOW|NONSTATIC|FLOW_STAR|DEMAND": 95193,
      "FLOW|NONSTATIC|FLOW_ANY|DEMAND": 3232957,
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 453254,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 18950285,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 46851201
    },
    "statement_untouched_from_resume": {},
    "statement_pure_untouched_from_resume": {},
    "packed_untouched_callbacks": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 1429,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 996529,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 2166592
    },
    "packed_untouched_mark_credits": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 2848,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 2296653,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 3655204
    },
    "scalar_taint_headers": {
      "ZERO|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 491430,
      "ZERO|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 131028,
      "ZERO|NONSTATIC|TAINT_MUST_NONEXACT|DEMAND": 404181,
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 787004,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 37772585,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 88507446
    },
    "scalar_fully_protected_identity_headers": {
      "ZERO|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 61,
      "ZERO|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 332,
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 863,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 770,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 273586
    },
    "packed_fully_protected_identity_invocations": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 37,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 72,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 2678
    },
    "packed_fully_protected_identity_mark_credits": {
      "CONCRETE|NONSTATIC|TAINT_EXACT_ONLY|DEMAND": 37,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 72,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 7124
    },
    "resume_taint_headers": {
      "CONCRETE|STATIC|TAINT_EXACT_ONLY|DEMAND": 2250,
      "CONCRETE|NONSTATIC|TAINT_STAR_NONEXACT|DEMAND": 114,
      "CONCRETE|NONSTATIC|TAINT_ANY_NONEXACT|DEMAND": 1004141
    },
    "resume_fully_protected_identity_headers": {}
  },
  "pure_untouched": {
    "scalar_calls": 71897409,
    "share_of_all_physical_method_edge_calls": 0.4996098420737527,
    "nonzero_nonstatic_scalar_calls": 70768235,
    "nonzero_nonstatic_share_of_all_physical_method_edge_calls": 0.4917632944490144,
    "not_an_engine_speedup_bound": true
  },
  "stored_counts": {
    "event.covered_offer_rejections": 7327506,
    "event.stored_compaction_memberships": 102,
    "physical.diagonal_geometry_rows": 25820,
    "physical.diagonal_mark_rows": 176807,
    "physical.scalar_concrete_rows": 18239,
    "FLOW.memberships": 226209,
    "TAINT.memberships": 1800397,
    "TAINT.decoded_trees": 195046,
    "TAINT.protection_trees.full_structural_only": 182426,
    "TAINT.protection_tree_memberships.full_structural_only": 1720875,
    "TAINT.flag_annotations": 1737136,
    "partition.removable_now": 0,
    "partition.protection_only": 901285,
    "partition.other": 899112,
    "TAINT.protection_trees.none": 12199,
    "TAINT.protection_tree_memberships.none": 47295,
    "TAINT.protection_trees.full_identity": 61,
    "TAINT.protection_tree_memberships.full_identity": 61,
    "TAINT.protection_trees.partial": 360,
    "TAINT.protection_tree_memberships.partial": 32166
  },
  "primary_other_reasons": [
    {
      "key": "CROSS_ATOM",
      "memberships": 817618
    },
    {
      "key": "ZERO_INITIAL",
      "memberships": 43089
    },
    {
      "key": "UNSUPPORTED_INITIAL",
      "memberships": 33195
    },
    {
      "key": "MARK_EXCLUDED",
      "memberships": 3934
    },
    {
      "key": "UNSUPPORTED_OUTPUT",
      "memberships": 1096
    },
    {
      "key": "OUTPUT_BASE_MISMATCH",
      "memberships": 108
    },
    {
      "key": "NO_FLOW_COUNTERPART",
      "memberships": 54
    },
    {
      "key": "OUTPUT_TAIL_MISMATCH",
      "memberships": 18
    }
  ],
  "taint_shapes": [
    {
      "key": "STAR->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2",
      "memberships": 857848
    },
    {
      "key": "STAR->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2",
      "memberships": 778176
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=1",
      "memberships": 42518
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1",
      "memberships": 25002
    },
    {
      "key": "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1",
      "memberships": 13932
    },
    {
      "key": "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2",
      "memberships": 11217
    },
    {
      "key": "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 10916
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 10674
    },
    {
      "key": "EXACT->ANY_TAINT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 10641
    },
    {
      "key": "EXACT->ANY|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 9828
    },
    {
      "key": "EXACT->ANY|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2",
      "memberships": 7676
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1",
      "memberships": 4814
    },
    {
      "key": "EXACT->ANY|NS->S|DEMAND|diagonal|flag=false|depth=2",
      "memberships": 2465
    },
    {
      "key": "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=1",
      "memberships": 2232
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 1872
    },
    {
      "key": "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 1868
    },
    {
      "key": "EXACT->ANY|NS->S|DEMAND|cross_or_zero_or_nd|flag=true|depth=2",
      "memberships": 1764
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1",
      "memberships": 1530
    },
    {
      "key": "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 1026
    },
    {
      "key": "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 967
    },
    {
      "key": "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 756
    },
    {
      "key": "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 416
    },
    {
      "key": "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 387
    },
    {
      "key": "EXACT->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 360
    },
    {
      "key": "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 235
    },
    {
      "key": "EXACT->ANY|NS->S|DEMAND|diagonal|flag=true|depth=2",
      "memberships": 201
    },
    {
      "key": "EXACT->ANY_TAINT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2",
      "memberships": 198
    },
    {
      "key": "EXACT->EXACT|Z->S|DEMAND|cross_or_zero_or_nd|flag=false|depth=2",
      "memberships": 198
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 162
    },
    {
      "key": "STAR->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 109
    },
    {
      "key": "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 87
    },
    {
      "key": "EXACT->EXACT|NS->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 72
    },
    {
      "key": "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=1",
      "memberships": 67
    },
    {
      "key": "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 60
    },
    {
      "key": "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=0",
      "memberships": 19
    },
    {
      "key": "STAR->STAR|NS->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 18
    },
    {
      "key": "EXACT->ANY|NS->NS|DEMAND|diagonal|flag=false|depth=0",
      "memberships": 16
    },
    {
      "key": "EXACT->ANY|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=1",
      "memberships": 16
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 14
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 13
    },
    {
      "key": "STAR->STAR|NS->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 12
    },
    {
      "key": "STAR->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 6
    },
    {
      "key": "EXACT->EXACT|NS->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 3
    },
    {
      "key": "STAR->EXACT|S->NS|DEMAND|diagonal|flag=false|depth=1",
      "memberships": 2
    },
    {
      "key": "STAR->EXACT|S->NS|DEMAND|diagonal|flag=true|depth=0",
      "memberships": 2
    },
    {
      "key": "EXACT->EXACT|Z->NS|DEMAND|cross_or_zero_or_nd|flag=true|depth=0",
      "memberships": 1
    },
    {
      "key": "STAR->EXACT|S->NS|DEMAND|cross_or_zero_or_nd|flag=false|depth=1",
      "memberships": 1
    }
  ],
  "flow_shapes": [
    {
      "key": "STAR->STAR|NS->NS|NORMAL|depth=0",
      "memberships": 66464
    },
    {
      "key": "STAR->ANY|NS->S|DEMAND|depth=2",
      "memberships": 65843
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|depth=1",
      "memberships": 36744
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|depth=1",
      "memberships": 29413
    },
    {
      "key": "STAR->STAR|NS->NS|NORMAL|depth=1",
      "memberships": 11489
    },
    {
      "key": "STAR->ANY|NS->NS|DEMAND|depth=0",
      "memberships": 7755
    },
    {
      "key": "STAR->STAR|NS->NS|DEMAND|depth=0",
      "memberships": 5631
    },
    {
      "key": "STAR->ANY|S->NS|DEMAND|depth=0",
      "memberships": 2527
    },
    {
      "key": "STAR->STAR|NS->NS|DEMAND|depth=1",
      "memberships": 342
    },
    {
      "key": "STAR->STAR|NS->S|DEMAND|depth=2",
      "memberships": 1
    }
  ],
  "top_static_output_fields": [
    {
      "key": "<static>(org.thingsboard.server.common.data.id.TenantId)/TenantId#tenants",
      "memberships": 121135
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.cluster.TbClusterService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.edge.EdgeService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.event.EventService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.nosql.CassandraBufferedRateWriteExecutor",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.dao.timeseries.TimeseriesService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.apiusage.TbApiUsageStateService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.rpc.TbCoreDeviceRpcService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.ruleengine.RuleEngineCallService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.session.DeviceSessionCacheService",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.transport.TbCoreToTransportService",
      "memberships": 118211
    },
    {
      "key": "<static>(org.thingsboard.rule.engine.math.TbMathNode)/TbMathNode#locks",
      "memberships": 118211
    },
    {
      "key": "<static>(org.thingsboard.server.common.msg.queue.TbCallback)/TbCallback#EMPTY",
      "memberships": 118211
    },
    {
      "key": "<static>(org.thingsboard.server.common.msg.queue.TbMsgCallback)/TbMsgCallback#EMPTY",
      "memberships": 118211
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.springframework.util.MultiValueMap",
      "memberships": 242
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.springframework.web.multipart.MultipartFile",
      "memberships": 154
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.entitiy.device.TbDeviceService",
      "memberships": 121
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.resource.TbImageService",
      "memberships": 110
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.resource.TbResourceService",
      "memberships": 110
    },
    {
      "key": "<static>(__spring_registry__)/__spring_registry__#org.thingsboard.server.service.sync.vc.EntitiesVersionControlService",
      "memberships": 108
    }
  ],
  "source_derived_backend_split": {
    "packed": {
      "memberships": 905399,
      "protected": 905219,
      "by_output_base": {
        "NS": 47551,
        "S": 857848
      }
    },
    "scalar_fallback": {
      "memberships": 894998,
      "protected": 831917,
      "by_output_base": {
        "NS": 92347,
        "S": 802651
      }
    },
    "physical_rows": {
      "physical.diagonal_geometry_rows": 25820,
      "physical.diagonal_mark_rows": 176807,
      "physical.scalar_concrete_rows": 18239
    },
    "coverage_partition": {
      "partition.removable_now": 0,
      "partition.protection_only": 901285,
      "partition.other": 899112
    }
  },
  "top_processed_methods": [
    {
      "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#processUplinkMsg(org.thingsboard.server.gen.edge.v1.UplinkMsg) [{}]",
      "step_credits": 14688616,
      "scalar_headers": 14623519,
      "packed_invocations": 52858,
      "packed_mark_credits": 65097,
      "physical_method_edge_invocations": 14676377,
      "edge_delta_credits": 106552,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 1068,
      "retained_flow_memberships": 49,
      "physical_work_share": 0.10198507146738565
    },
    {
      "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.common.util.JacksonUtil$replaceAllByMapping_27c33466$jIR_lambda$0/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
      "step_credits": 1910552,
      "scalar_headers": 1896198,
      "packed_invocations": 10977,
      "packed_mark_credits": 14354,
      "physical_method_edge_invocations": 1907175,
      "edge_delta_credits": 20910,
      "neutral_scalar_store_fallback_credits": 116,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 3,
      "physical_work_share": 0.01325281973036065
    },
    {
      "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{arg(3) == (lambda: org.thingsboard.server.dao.resource.BaseResourceService$processResources_fc592dee$jIR_lambda$18/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
      "step_credits": 991079,
      "scalar_headers": 983465,
      "packed_invocations": 5865,
      "packed_mark_credits": 7614,
      "physical_method_edge_invocations": 989330,
      "edge_delta_credits": 10923,
      "neutral_scalar_store_fallback_credits": 36,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 1,
      "physical_work_share": 0.006874781886212697
    },
    {
      "method": "org.thingsboard.server.service.edge.rpc.EdgeGrpcSession#lambda$scheduleDownlinkMsgsPackSend$5(int) [{}]",
      "step_credits": 823616,
      "scalar_headers": 815532,
      "packed_invocations": 7186,
      "packed_mark_credits": 8084,
      "physical_method_edge_invocations": 822718,
      "edge_delta_credits": 19965,
      "neutral_scalar_store_fallback_credits": 109,
      "retained_taint_memberships": 535,
      "retained_flow_memberships": 41,
      "physical_work_share": 0.005717007271447482
    },
    {
      "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{}]",
      "step_credits": 750609,
      "scalar_headers": 744753,
      "packed_invocations": 5483,
      "packed_mark_credits": 5856,
      "physical_method_edge_invocations": 750236,
      "edge_delta_credits": 11309,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 1064,
      "retained_flow_memberships": 41,
      "physical_work_share": 0.00521333514922692
    },
    {
      "method": "org.thingsboard.rule.engine.deduplication.TbMsgDeduplicationNode#processDeduplication(org.thingsboard.rule.engine.api.TbContext, org.thingsboard.server.common.data.id.EntityId) [{arg(0) is org.thingsboard.server.actors.ruleChain.DefaultTbContext}]",
      "step_credits": 750037,
      "scalar_headers": 744181,
      "packed_invocations": 5483,
      "packed_mark_credits": 5856,
      "physical_method_edge_invocations": 749664,
      "edge_delta_credits": 11329,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 1064,
      "retained_flow_memberships": 44,
      "physical_work_share": 0.00520936036301917
    },
    {
      "method": "org.thingsboard.server.gen.edge.v1.DownlinkMsg#getSerializedSize() [{}]",
      "step_credits": 739513,
      "scalar_headers": 737659,
      "packed_invocations": 1836,
      "packed_mark_credits": 1854,
      "physical_method_edge_invocations": 739495,
      "edge_delta_credits": 6638,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 4,
      "physical_work_share": 0.005138696725000615
    },
    {
      "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{}]",
      "step_credits": 738854,
      "scalar_headers": 733010,
      "packed_invocations": 3907,
      "packed_mark_credits": 5844,
      "physical_method_edge_invocations": 736917,
      "edge_delta_credits": 11977,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 1064,
      "retained_flow_memberships": 43,
      "physical_work_share": 0.005120782391357992
    },
    {
      "method": "org.thingsboard.server.dao.rule.BaseRuleChainService#saveRuleChainMetaData(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.rule.RuleChainMetaData, java.util.function.Function, boolean) [{arg(2) == (lambda: org.thingsboard.server.service.sync.ie.importing.impl.RuleChainImportService$saveOrUpdate_3af00c54$jIR_lambda$15/java.util.function.Function#apply(java.lang.Object))}]",
      "step_credits": 713692,
      "scalar_headers": 708352,
      "packed_invocations": 3824,
      "packed_mark_credits": 5340,
      "physical_method_edge_invocations": 712176,
      "edge_delta_credits": 11052,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 532,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.004948858990018915
    },
    {
      "method": "org.thingsboard.common.util.JacksonUtil#replaceAll(com.fasterxml.jackson.databind.JsonNode, java.lang.String, java.util.function.BiFunction) [{arg(2) == (lambda: org.thingsboard.server.dao.resource.BaseImageService$convertToImageUrls_69156998$jIR_lambda$2/java.util.function.BiFunction#apply(java.lang.Object, java.lang.Object))}]",
      "step_credits": 679878,
      "scalar_headers": 670491,
      "packed_invocations": 8504,
      "packed_mark_credits": 9387,
      "physical_method_edge_invocations": 678995,
      "edge_delta_credits": 13305,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.004718286645334711
    },
    {
      "method": "org.thingsboard.server.service.entitiy.queue.DefaultTbQueueService#updateQueuesByTenants(java.util.List, org.thingsboard.server.common.data.TenantProfile, org.thingsboard.server.common.data.TenantProfile) [{}]",
      "step_credits": 662738,
      "scalar_headers": 651683,
      "packed_invocations": 7312,
      "packed_mark_credits": 11055,
      "physical_method_edge_invocations": 658995,
      "edge_delta_credits": 13754,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.004579308106602182
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 661821,
      "scalar_headers": 650672,
      "packed_invocations": 4200,
      "packed_mark_credits": 11149,
      "physical_method_edge_invocations": 654872,
      "edge_delta_credits": 15658,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 33,
      "retained_flow_memberships": 27,
      "physical_work_share": 0.0045506576808424706
    },
    {
      "method": "org.thingsboard.server.transport.coap.client.DefaultCoapClientContext$CoapSessionListener#onToDeviceRpcRequest(java.util.UUID, org.thingsboard.server.gen.transport.TransportProtos$ToDeviceRpcRequestMsg) [{}]",
      "step_credits": 638960,
      "scalar_headers": 631979,
      "packed_invocations": 6202,
      "packed_mark_credits": 6981,
      "physical_method_edge_invocations": 638181,
      "edge_delta_credits": 12786,
      "neutral_scalar_store_fallback_credits": 319,
      "retained_taint_memberships": 532,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.0044346731413432375
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 641744,
      "scalar_headers": 630048,
      "packed_invocations": 3930,
      "packed_mark_credits": 11696,
      "physical_method_edge_invocations": 633978,
      "edge_delta_credits": 15399,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.0044054668014285965
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.RuleChainId} & {arg(1) is org.thingsboard.server.common.data.rule.RuleChain}]",
      "step_credits": 638013,
      "scalar_headers": 626893,
      "packed_invocations": 4172,
      "packed_mark_credits": 11120,
      "physical_method_edge_invocations": 631065,
      "edge_delta_credits": 14822,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.004385224577262203
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile}]",
      "step_credits": 638013,
      "scalar_headers": 626893,
      "packed_invocations": 4165,
      "packed_mark_credits": 11120,
      "physical_method_edge_invocations": 631058,
      "edge_delta_credits": 14822,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.004385175934773647
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile}]",
      "step_credits": 638013,
      "scalar_headers": 626893,
      "packed_invocations": 4159,
      "packed_mark_credits": 11120,
      "physical_method_edge_invocations": 631052,
      "edge_delta_credits": 14822,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.0043851342412120275
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard}]",
      "step_credits": 637987,
      "scalar_headers": 626867,
      "packed_invocations": 3919,
      "packed_mark_credits": 11120,
      "physical_method_edge_invocations": 630786,
      "edge_delta_credits": 14822,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 27,
      "physical_work_share": 0.004383285826646884
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DashboardId} & {arg(1) is org.thingsboard.server.common.data.Dashboard} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 637974,
      "scalar_headers": 626854,
      "packed_invocations": 3909,
      "packed_mark_credits": 11120,
      "physical_method_edge_invocations": 630763,
      "edge_delta_credits": 14819,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 26,
      "physical_work_share": 0.004383126001327342
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{}]",
      "step_credits": 591877,
      "scalar_headers": 581975,
      "packed_invocations": 3512,
      "packed_mark_credits": 9902,
      "physical_method_edge_invocations": 585487,
      "edge_delta_credits": 13200,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 24,
      "physical_work_share": 0.004068506385344641
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId}]",
      "step_credits": 590607,
      "scalar_headers": 580158,
      "packed_invocations": 3252,
      "packed_mark_credits": 10449,
      "physical_method_edge_invocations": 583410,
      "edge_delta_credits": 13625,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 23,
      "physical_work_share": 0.004054073464097268
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 588152,
      "scalar_headers": 577703,
      "packed_invocations": 3243,
      "packed_mark_credits": 10449,
      "physical_method_edge_invocations": 580946,
      "edge_delta_credits": 13618,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 23,
      "physical_work_share": 0.00403695130812542
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm}]",
      "step_credits": 581782,
      "scalar_headers": 570561,
      "packed_invocations": 3807,
      "packed_mark_credits": 11221,
      "physical_method_edge_invocations": 574368,
      "edge_delta_credits": 15406,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 33,
      "retained_flow_memberships": 25,
      "physical_work_share": 0.003991241266736291
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo}]",
      "step_credits": 561991,
      "scalar_headers": 551346,
      "packed_invocations": 4059,
      "packed_mark_credits": 10645,
      "physical_method_edge_invocations": 555405,
      "edge_delta_credits": 14147,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 25,
      "physical_work_share": 0.0038594687652370426
    },
    {
      "method": "org.thingsboard.common.util.JacksonUtil#replaceByMapping(com.fasterxml.jackson.databind.JsonNode, java.util.Map, java.util.Map, java.util.function.BiFunction) [{}]",
      "step_credits": 553290,
      "scalar_headers": 548718,
      "packed_invocations": 2889,
      "packed_mark_credits": 4572,
      "physical_method_edge_invocations": 551607,
      "edge_delta_credits": 6313,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 0,
      "physical_work_share": 0.003833076740731735
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device}]",
      "step_credits": 556990,
      "scalar_headers": 546374,
      "packed_invocations": 4056,
      "packed_mark_credits": 10616,
      "physical_method_edge_invocations": 550430,
      "edge_delta_credits": 14004,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 25,
      "physical_work_share": 0.0038248978537273257
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView}]",
      "step_credits": 556990,
      "scalar_headers": 546374,
      "packed_invocations": 4036,
      "packed_mark_credits": 10616,
      "physical_method_edge_invocations": 550410,
      "edge_delta_credits": 14003,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 25,
      "physical_work_share": 0.003824758875188593
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.Alarm} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 548347,
      "scalar_headers": 538170,
      "packed_invocations": 3732,
      "packed_mark_credits": 10177,
      "physical_method_edge_invocations": 541902,
      "edge_delta_credits": 14325,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 33,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.003765637404811775
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge}]",
      "step_credits": 536632,
      "scalar_headers": 526664,
      "packed_invocations": 4104,
      "packed_mark_credits": 9968,
      "physical_method_edge_invocations": 530768,
      "edge_delta_credits": 13355,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 25,
      "physical_work_share": 0.003688268052299375
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(1) is org.thingsboard.server.common.data.alarm.AlarmInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 531805,
      "scalar_headers": 521628,
      "packed_invocations": 3736,
      "packed_mark_credits": 10177,
      "physical_method_edge_invocations": 525364,
      "edge_delta_credits": 13640,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.0036507160511338455
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EntityViewId} & {arg(1) is org.thingsboard.server.common.data.EntityView} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 526817,
      "scalar_headers": 516669,
      "packed_invocations": 3709,
      "packed_mark_credits": 10148,
      "physical_method_edge_invocations": 520378,
      "edge_delta_credits": 13495,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.003616068701427826
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceId} & {arg(1) is org.thingsboard.server.common.data.Device} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 526804,
      "scalar_headers": 516656,
      "packed_invocations": 3701,
      "packed_mark_credits": 10148,
      "physical_method_edge_invocations": 520357,
      "edge_delta_credits": 13496,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.0036159227739621567
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.EdgeId} & {arg(1) is org.thingsboard.server.common.data.edge.Edge} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 523047,
      "scalar_headers": 513475,
      "packed_invocations": 3705,
      "packed_mark_credits": 9572,
      "physical_method_edge_invocations": 517180,
      "edge_delta_credits": 12918,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.0035938460330844943
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo}]",
      "step_credits": 503044,
      "scalar_headers": 492780,
      "packed_invocations": 3450,
      "packed_mark_credits": 10264,
      "physical_method_edge_invocations": 496230,
      "edge_delta_credits": 13286,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.003448266013762169
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.TbResourceId} & {arg(1) is org.thingsboard.server.common.data.TbResourceInfo}]",
      "step_credits": 500948,
      "scalar_headers": 490684,
      "packed_invocations": 3456,
      "packed_mark_credits": 10264,
      "physical_method_edge_invocations": 494140,
      "edge_delta_credits": 13279,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 22,
      "physical_work_share": 0.0034337427564646197
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 485708,
      "scalar_headers": 476488,
      "packed_invocations": 3466,
      "packed_mark_credits": 9220,
      "physical_method_edge_invocations": 479954,
      "edge_delta_credits": 12886,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 33,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.003335165278941636
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AiModelId} & {arg(1) is org.thingsboard.server.common.data.ai.AiModel}]",
      "step_credits": 485695,
      "scalar_headers": 476475,
      "packed_invocations": 3433,
      "packed_mark_credits": 9220,
      "physical_method_edge_invocations": 479908,
      "edge_delta_credits": 12884,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 33,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.0033348456283025514
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.AssetProfileId} & {arg(1) is org.thingsboard.server.common.data.asset.AssetProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 469127,
      "scalar_headers": 459907,
      "packed_invocations": 3375,
      "packed_mark_credits": 9220,
      "physical_method_edge_invocations": 463282,
      "edge_delta_credits": 12205,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.003219312769054199
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.DeviceProfileId} & {arg(1) is org.thingsboard.server.common.data.DeviceProfile} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 469127,
      "scalar_headers": 459907,
      "packed_invocations": 3375,
      "packed_mark_credits": 9220,
      "physical_method_edge_invocations": 463282,
      "edge_delta_credits": 12205,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.003219312769054199
    },
    {
      "method": "org.thingsboard.server.service.action.EntityActionService#pushEntityActionToRuleEngine(org.thingsboard.server.common.data.id.EntityId, org.thingsboard.server.common.data.HasName, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.CustomerId, org.thingsboard.server.common.data.audit.ActionType, org.thingsboard.server.common.data.User, java.lang.Object[]) [{arg(0) is org.thingsboard.server.common.data.id.OtaPackageId} & {arg(1) is org.thingsboard.server.common.data.OtaPackageInfo} & {arg(5) is org.thingsboard.server.service.security.model.SecurityUser}]",
      "step_credits": 469114,
      "scalar_headers": 459894,
      "packed_invocations": 3385,
      "packed_mark_credits": 9220,
      "physical_method_edge_invocations": 463279,
      "edge_delta_credits": 12203,
      "neutral_scalar_store_fallback_credits": 0,
      "retained_taint_memberships": 0,
      "retained_flow_memberships": 19,
      "physical_work_share": 0.003219291922273389
    }
  ],
  "template_reuse": {
    "owners": {
      "raw": 73669,
      "selected": 73669
    },
    "raw_totals": {
      "relation_rows": 193732,
      "distinct_templates": 115108,
      "distinct_origin_pairs": 193732,
      "repeated_origin_pairs": 78624,
      "same_origin_duplicate_rows": 0,
      "repeated_templates": 55680,
      "relation_memberships": 1757308,
      "distinct_pair_memberships": 1757308,
      "template_memberships": 1032432,
      "repeated_pair_memberships": 724876,
      "max_origin_width": 6
    },
    "top_methods": [
      {
        "method": "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.ArrayList} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.actors.calculatedField.CalculatedFieldEntityMessageProcessor#processStateIfReady(org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState, java.util.Map, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx, java.util.List, java.util.UUID, java.lang.String, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(3) == java.util.HashSet} & {arg(6) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.controller.TelemetryController#lambda$saveTelemetry$8(long, org.thingsboard.server.service.security.model.SecurityUser, java.util.List, org.springframework.web.context.request.async.DeferredResult, org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId) [{}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processResult(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#pushMsgToRuleEngine(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      },
      {
        "method": "org.thingsboard.server.service.cf.DefaultCalculatedFieldProcessingService#processImmediately(org.thingsboard.server.common.data.id.TenantId, org.thingsboard.server.common.data.id.EntityId, java.lang.String, org.thingsboard.server.service.cf.CalculatedFieldResult, java.util.List, org.thingsboard.server.common.msg.queue.TbCallback) [{arg(4) == java.util.ArrayList} & {arg(5) == org.thingsboard.server.actors.calculatedField.MultipleTbCallback}]",
        "owner": "raw",
        "counts": {
          "relation_rows": 264,
          "distinct_templates": 44,
          "distinct_origin_pairs": 264,
          "repeated_origin_pairs": 220,
          "same_origin_duplicate_rows": 0,
          "repeated_templates": 44,
          "relation_memberships": 3192,
          "distinct_pair_memberships": 3192,
          "template_memberships": 532,
          "repeated_pair_memberships": 2660
        },
        "max_origin_width": 6,
        "scope": "Exact complete TAINT Facts plus complete mask; distinct unary non-ZERO premises in one current method/owner; scalar/diagonal physical split unavailable from all()"
      }
    ]
  },
  "examples": [
    {
      "file": "examples/example-raw_PROTECTION_ONLY-0.json",
      "sha256": "b14055e692d16ac31be19f0643213189938644b73bf8ef80ea8100b92abf3fce",
      "reason": "PROTECTION_ONLY",
      "method": "org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]",
      "flow_candidates": 1,
      "flag": true
    },
    {
      "file": "examples/example-raw_PROTECTION_ONLY-1.json",
      "sha256": "c3ed4acd5a27f3d8dcabdeb7edd0cb99fb2a25f9d496113ff3fc5ebfe3e27953",
      "reason": "PROTECTION_ONLY",
      "method": "org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]",
      "flow_candidates": 1,
      "flag": true
    },
    {
      "file": "examples/example-raw_UNSUPPORTED_INITIAL-0.json",
      "sha256": "f241cc39268bb43dbf754bc4cd13230fb1bee3c9cf87b4fd27c66e7550d4b057",
      "reason": "UNSUPPORTED_INITIAL",
      "method": "org.thingsboard.server.controller.AuthController#checkActivateToken(java.lang.String) [{}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_UNSUPPORTED_INITIAL-1.json",
      "sha256": "d715e5dce4d4400b6d287b8fabcc6d88d75de5b63d424905c880c4761802c420",
      "reason": "UNSUPPORTED_INITIAL",
      "method": "org.thingsboard.server.controller.AuthController#checkResetToken(java.lang.String) [{}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_CROSS_ATOM-0.json",
      "sha256": "b8b8b1c2e259af1229098e91d3e3e6d0515da0fb243e5dc34b0f600ef2512270",
      "reason": "CROSS_ATOM",
      "method": "org.thingsboard.server.controller.QrCodeSettingsController#getAppleAppSiteAssociation() [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_CROSS_ATOM-1.json",
      "sha256": "26af7470cc7b615404bec5a31a48e7fb84b408ce56205e1ceccfb6537d5d48f5",
      "reason": "CROSS_ATOM",
      "method": "org.thingsboard.server.controller.QrCodeSettingsController#getAssetLinks() [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_NO_FLOW_COUNTERPART-0.json",
      "sha256": "101aebd367de20e3c82d9ab25a2212bfbb059a0689ae39def447129b07655921",
      "reason": "NO_FLOW_COUNTERPART",
      "method": "org.thingsboard.rule.engine.ai.Langchain4jJsonSchemaAdapter#parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_NO_FLOW_COUNTERPART-1.json",
      "sha256": "1d7be6c582fb565e7d102e9cf52272197f2430254bc520c08688058e42dc9666",
      "reason": "NO_FLOW_COUNTERPART",
      "method": "org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx#evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_MARK_EXCLUDED-0.json",
      "sha256": "7ec7ac3dca89b238acbd929b5f8e491a22655a5d69e5cf04876b94a814511a8e",
      "reason": "MARK_EXCLUDED",
      "method": "org.thingsboard.server.transport.mqtt.HashMapObserver#getActiveSessions(java.lang.String) [{}]",
      "flow_candidates": 1,
      "flag": true
    },
    {
      "file": "examples/example-raw_MARK_EXCLUDED-1.json",
      "sha256": "1a8df83296403089d5362c79be9aa0fc6f6c942fc4bfc99e157bc0498b8327cc",
      "reason": "MARK_EXCLUDED",
      "method": "org.thingsboard.server.transport.mqtt.HashMapObserver#getAllSessions(java.lang.String) [{}]",
      "flow_candidates": 1,
      "flag": true
    },
    {
      "file": "examples/example-raw_OUTPUT_BASE_MISMATCH-0.json",
      "sha256": "e5177caa44b5da34fe649ab94e028296bb58d768933346ee2977d713d861208e",
      "reason": "OUTPUT_BASE_MISMATCH",
      "method": "org.thingsboard.server.common.adaptor.JsonConverter#parseValues(com.google.gson.JsonObject) [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_OUTPUT_BASE_MISMATCH-1.json",
      "sha256": "a3dd1ccf9e6789b68cc75bd24d1628dfc9b1f2b543c91612802268fd26367aed",
      "reason": "OUTPUT_BASE_MISMATCH",
      "method": "org.thingsboard.server.common.adaptor.JsonConverter#parseProtoValues(com.google.gson.JsonObject) [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_ZERO_INITIAL-0.json",
      "sha256": "61fc1123726d5cc0d871fc4ed190a396d7137cf3892409dd9df025db02d051c9",
      "reason": "ZERO_INITIAL",
      "method": "org.thingsboard.server.config.WebConfig#redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_ZERO_INITIAL-1.json",
      "sha256": "d6f8b159c72b31f82e59da00473ed14614e2060cb9ca959d3e3569c06cc4294c",
      "reason": "ZERO_INITIAL",
      "method": "org.thingsboard.server.controller.AdminController#checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]",
      "flow_candidates": 0,
      "flag": false
    },
    {
      "file": "examples/example-raw_UNSUPPORTED_OUTPUT-0.json",
      "sha256": "354e09abe9299353a4840b9ec077ee3a9761870f90825d288bf154166328356d",
      "reason": "UNSUPPORTED_OUTPUT",
      "method": "org.thingsboard.server.controller.AuthController#logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_UNSUPPORTED_OUTPUT-1.json",
      "sha256": "c0feb59b4c399c7c55164fa619b7dfa5118debc2820c9d0e7ddb7a711a579a4b",
      "reason": "UNSUPPORTED_OUTPUT",
      "method": "org.thingsboard.server.controller.DashboardController#saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]",
      "flow_candidates": 1,
      "flag": false
    },
    {
      "file": "examples/example-raw_OUTPUT_TAIL_MISMATCH-0.json",
      "sha256": "17d6d68706655294df192af2518a3b4f4723e1ced401cf6280a7659d1002fcc9",
      "reason": "OUTPUT_TAIL_MISMATCH",
      "method": "org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]",
      "flow_candidates": 2,
      "flag": false
    }
  ],
  "source_hashes": {
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/run1-shapes.json": "806e5bba1c968f9c6861d94a608e1688c42829fc020ca44f81e9b74cd818d0c9",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/run1-template-reuse.jsonl": "563f34f265bab4fc146d1e07c86d4aa37f3655bc9b6d2a18ddd1b329c1613fbd",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/Run1ShapeCensus.kt": "1f6b9f5bd4bb11891000138f8daefd2b671d545ab4df54f4987ed7d7d6b27d8a",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/Run1ProcessedWorkCounters.kt": "b0a9b39ccaacd051cfc37c6e546d0c7d674d1e792e347498f79928f5b8bcb598",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/run1-backend-split-fcfe.json": "b7837048fd10c7de0513ad82d6161f4e3cf4ad004264ddfc849e8e0fcbc442f8",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt": "d21608744a5ab2ff58fcab1ba97d1fd9bba4693866cfaf7a970dd505550859ed",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/DeltaWorklist.kt": "3f31f4bde824687f37f75a51dbe47e6691f5ca829054c8b87f7ff0fcc3f7b19b",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/EngineAlgebra.kt": "765cf7ecc4f18973d42fa925bf2a7b593c6d177409193be211940a75ee5ebed9",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/Run1PointResume.kt": "6ee6a1aed930f097881d326c3876cc314b358be9a3a2fda765720d48127a3689",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/NeutralRelationBatch.kt": "6873d3074eefee86c8fbd6410bc19103362bd255f0de9be3c25b929de86c6dac",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/MethodContextCache.kt": "cba977e9ed0b902af44039fce53b166f1092384a92cdaaa1e03d2f84b40c5de5",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/FormApplier.kt": "06bca49113a3aced10ecdf858ee323ccf9354c471902189d11425a9678109b6a",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/StatementSummary.kt": "f3a00e5cfbb8003d97d5d773b3f318a7c86ba7cf188521a4381a4f0a006bcadb",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/FlowBackedSummaries.kt": "d1b3d398ef084cc37acab1cca14d65e2958d5af347451fbda7e7f1b1f2b58ed0",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DiagonalRelations.kt": "82d17677972889a9f08e530225c31a9faab3bae56777a03649c067f0ab8c0a2e",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Groups.kt": "18a7cb13e2a90bec933c22ae5658af499d5d0844a3f702439ae5193c258ce050",
    "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Summary.kt": "decefd8631355ca5e95456ae1130d346aa3d31a608801a04bb233a5d556e69cc"
  },
  "artifact_sha256": {
    "analyze.py": "2c8846804e396f8dac25ff173fe2d8a77f2d360ff953ba054f131dc1a505d051",
    "report.md": "e1a2b722f15966414558113e15aafc93c64c6b2e12edc191495903141c320f9d",
    "sparse-routing-candidate.md": "7172622fe68c00d6c52684a40bd1a9b6499344c933123c54f7fff88ba639b3ff",
    "code-under-analysis.md": "55d27eeb9a007ea39e7efcb4f5c8ef7726ae540817bc810261b641ebaa116900",
    "code-under-analysis.json": "b331044ca399ab456a0716de07269f31f57be99ff528c4fcd3f0992ffd6949f5"
  },
  "limits": [
    "No per-point Thingsboard targets were captured in existing target dump files (methods=0); do not invent a measured dominant NS-to-static relation.",
    "17 raw examples and 17 matching selected copies exist, not 18 distinct raw examples. All full FLOW candidate lists and masks are untruncated.",
    "Physical diagonal mark rows do not count output paths. Logical backend split is source-derived from exact extraction, not physical-row subtraction.",
    "Processing headers, packed credits, retained memberships, rejection events and template rows are different units.",
    "A barrier census cannot attribute individual baseline-to-final flag changes or transient processing flags. Scalar full-protection process counters use identity only.",
    "No runtime, decoder, analyzer configuration or tracked proposal was changed."
  ]
}
```

</details>

<a id="inline-examples"></a>
## All 17 full example records

Each JSON block is equal to its original raw example file. Selected copies are duplicate diagnostic evidence, not 17 more samples. Each matching-initial FLOW list and mask is complete. An empty list is recorded empty data, not an omission.

Notation below: `S.tenants` abbreviates the full `TenantId` + `tenants` static path. `Tn` is the exact atom id in the complete JSON, not a group id. All sampled field exclusions are Empty. Each listed FLOW has the matching FLOW original obtained from that complete TAINT initial, unless no legal counterpart exists. `D`/`N` mean DEMAND/NORMAL.

| Example and actual method | TAINT relation | All relevant FLOW conclusions | Why retained |
|---|---|---|---|
| [Protection only](#example-01), `DeviceConnectivityServiceImpl.getCoapPublishCommand` | `S.tenants.*/T201 → ret.[any]/T201 D`, protected | `ret.[any]/FLOW\{T1,T2} D` | All shape/layer/mark gates pass; protection alone retains it |
| [Cross atom](#example-05), `QrCodeSettingsController.getAppleAppSiteAssociation` | `S.tenants.*/T146 → ret.EXACT/T65 D` | `ret.HttpEntity.Body.[any]/FLOW\{1,2,65,68,70,78,80,89,94,105,117,146} D` | Different full atom; same group does not make a FLOW transport relation; tail/path/exclusion also fail |
| [Unsupported initial](#example-03), `AuthController.checkActivateToken` | `S.syntheticClassMarker.EXACT/T400 → ret.EXACT/T233 D` | None | Legal EXACT class marker has no STAR/ANY FLOW initial counterpart; it is not an invalid ordinary static field input |
| [Tail mismatch](#example-17), `CassandraToSqlColumn.getColumnValue` | `arg0.*/T3 → ret.*/T3 D` | `arg0.*/FLOW N`; `ret.[any]/FLOW\{1,2} D` | First has wrong output base; second has wrong tail. FLOW ANY does not cover correlated TAINT STAR under the selected same-tail replacement law |
| [Mark excluded](#example-09), `HashMapObserver.getActiveSessions` | `S.tenants.*/T201 → ret.[any]/T201 D`, protected | `ret.[any]/FLOW\{1,2,201} D` | FLOW explicitly excludes T201, so removing protection would still not cover it |
| [No FLOW](#example-07), `Langchain4jJsonSchemaAdapter.parseEnum` | `S.tenants.*/T3 → exception.[any]/T3 D` | None | No retained FLOW under that complete initial |
| [Wrong output base](#example-11), `JsonConverter.parseValues` | `S.tenants.*/T3 → exception.[any]/T3 D` | `ret.Iterable.Element.[any]/FLOW\{1,2} D` | Return FLOW does not cover exception output |
| [ZERO](#example-13), `WebConfig.redirectSwagger` | `ZERO → arg0.EXACT/T123 D` | None | A generated concrete result cannot be replaced by a FLOW with a non-ZERO premise |
| [Unsupported output](#example-15), `AuthController.logLogoutAction` | `arg0.*/T203 → arg0.EXACT/T203 D` | `arg0.*/FLOW N` | Selected replacement supports matching STAR/ANY concrete outputs, not EXACT |


The complete records below add the eight second examples to this short explanation table. All 17 matching FLOW lists and masks remain untruncated.

<a id="example-01"></a>
### Example 01: PROTECTION_ONLY

Method: `org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]`. Owner: `raw`.

<a id="example-01-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 b14055e692d16ac31be19f0643213189938644b73bf8ef80ea8100b92abf3fce</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_PROTECTION_ONLY-0.json`.

```json
{"owner":"raw","reason":"PROTECTION_ONLY","method":"org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND","flag_present":true,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":[]}],"current_protection_mask":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND"}],"protection_mask_truncated":false}
```

</details>

<a id="example-02"></a>
### Example 02: PROTECTION_ONLY

Method: `org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]`. Owner: `raw`.

<a id="example-02-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 c3ed4acd5a27f3d8dcabdeb7edd0cb99fb2a25f9d496113ff3fc5ebfe3e27953</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_PROTECTION_ONLY-1.json`.

```json
{"owner":"raw","reason":"PROTECTION_ONLY","method":"org.thingsboard.server.dao.device.DeviceConnectivityServiceImpl#getDockerCoapPublishCommand(java.lang.String, java.lang.String, org.thingsboard.server.common.data.security.DeviceCredentials) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND","flag_present":true,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":[]}],"current_protection_mask":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND"}],"protection_mask_truncated":false}
```

</details>

<a id="example-03"></a>
### Example 03: UNSUPPORTED_INITIAL

Method: `org.thingsboard.server.controller.AuthController#checkActivateToken(java.lang.String) [{}]`. Owner: `raw`.

<a id="example-03-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 f241cc39268bb43dbf754bc4cd13230fb1bee3c9cf87b4fd27c66e7550d4b057</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_UNSUPPORTED_INITIAL-0.json`.

```json
{"owner":"raw","reason":"UNSUPPORTED_INITIAL","method":"org.thingsboard.server.controller.AuthController#checkActivateToken(java.lang.String) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[433],"path":["java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos"],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":400,"name":"java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=399)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":233,"name":"java/security/xss.yaml:xss#sink#1;sink_15;$X;4","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=232)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-04"></a>
### Example 04: UNSUPPORTED_INITIAL

Method: `org.thingsboard.server.controller.AuthController#checkResetToken(java.lang.String) [{}]`. Owner: `raw`.

<a id="example-04-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 d715e5dce4d4400b6d287b8fabcc6d88d75de5b63d424905c880c4761802c420</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_UNSUPPORTED_INITIAL-1.json`.

```json
{"owner":"raw","reason":"UNSUPPORTED_INITIAL","method":"org.thingsboard.server.controller.AuthController#checkResetToken(java.lang.String) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[433],"path":["java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;pos"],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":400,"name":"java/security/xss.yaml:xss#sink#1;sink_15;_<S>_;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=399)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":233,"name":"java/security/xss.yaml:xss#sink#1;sink_15;$X;4","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=232)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-05"></a>
### Example 05: CROSS_ATOM

Method: `org.thingsboard.server.controller.QrCodeSettingsController#getAppleAppSiteAssociation() [{}]`. Owner: `raw`.

<a id="example-05-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 b8b8b1c2e259af1229098e91d3e3e6d0515da0fb243e5dc34b0f600ef2512270</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_CROSS_ATOM-0.json`.

```json
{"owner":"raw","reason":"CROSS_ATOM","method":"org.thingsboard.server.controller.QrCodeSettingsController#getAppleAppSiteAssociation() [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":146,"name":"java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=145)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":65,"name":"java/security/xss.yaml:xss#sink#1;sink_96;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=64)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[5616],"path":["org.springframework.http.HttpEntity.Body"],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"},{"id":65,"name":"java/security/xss.yaml:xss#sink#1;sink_96;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=64)))"},{"id":68,"name":"java/security/xss.yaml:xss#sink#1;sink_36;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=67)))"},{"id":70,"name":"java/security/xss.yaml:xss#sink#1;sink_0;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=69)))"},{"id":78,"name":"java/security/xss.yaml:xss#sink#1;sink_60;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=77)))"},{"id":80,"name":"java/security/xss.yaml:xss#sink#1;sink_48;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=79)))"},{"id":89,"name":"java/security/xss.yaml:xss#sink#1;sink_84;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=88)))"},{"id":94,"name":"java/security/xss.yaml:xss#sink#1;sink_12;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=93)))"},{"id":105,"name":"java/security/xss.yaml:xss#sink#1;sink_72;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=104)))"},{"id":117,"name":"java/security/xss.yaml:xss#sink#1;sink_24;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=116)))"},{"id":146,"name":"java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=145)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_TAIL_MISMATCH","NO_ANNOTATED_ANY_PREFIX","MARK_EXCLUDED"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-06"></a>
### Example 06: CROSS_ATOM

Method: `org.thingsboard.server.controller.QrCodeSettingsController#getAssetLinks() [{}]`. Owner: `raw`.

<a id="example-06-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 26af7470cc7b615404bec5a31a48e7fb84b408ce56205e1ceccfb6537d5d48f5</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_CROSS_ATOM-1.json`.

```json
{"owner":"raw","reason":"CROSS_ATOM","method":"org.thingsboard.server.controller.QrCodeSettingsController#getAssetLinks() [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":146,"name":"java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=145)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":65,"name":"java/security/xss.yaml:xss#sink#1;sink_96;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=64)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[5616],"path":["org.springframework.http.HttpEntity.Body"],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"},{"id":65,"name":"java/security/xss.yaml:xss#sink#1;sink_96;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=64)))"},{"id":68,"name":"java/security/xss.yaml:xss#sink#1;sink_36;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=67)))"},{"id":70,"name":"java/security/xss.yaml:xss#sink#1;sink_0;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=69)))"},{"id":78,"name":"java/security/xss.yaml:xss#sink#1;sink_60;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=77)))"},{"id":80,"name":"java/security/xss.yaml:xss#sink#1;sink_48;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=79)))"},{"id":89,"name":"java/security/xss.yaml:xss#sink#1;sink_84;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=88)))"},{"id":94,"name":"java/security/xss.yaml:xss#sink#1;sink_12;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=93)))"},{"id":105,"name":"java/security/xss.yaml:xss#sink#1;sink_72;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=104)))"},{"id":117,"name":"java/security/xss.yaml:xss#sink#1;sink_24;$<ARTIFICIAL>_2;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=116)))"},{"id":146,"name":"java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=145)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_TAIL_MISMATCH","NO_ANNOTATED_ANY_PREFIX","MARK_EXCLUDED"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-07"></a>
### Example 07: NO_FLOW_COUNTERPART

Method: `org.thingsboard.rule.engine.ai.Langchain4jJsonSchemaAdapter#parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]`. Owner: `raw`.

<a id="example-07-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 101aebd367de20e3c82d9ab25a2212bfbb059a0689ae39def447129b07655921</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_NO_FLOW_COUNTERPART-0.json`.

```json
{"owner":"raw","reason":"NO_FLOW_COUNTERPART","method":"org.thingsboard.rule.engine.ai.Langchain4jJsonSchemaAdapter#parseEnum(com.fasterxml.jackson.databind.JsonNode) [{arg(0) is com.fasterxml.jackson.databind.node.ObjectNode}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}}],"output":{"base":"exception","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-08"></a>
### Example 08: NO_FLOW_COUNTERPART

Method: `org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx#evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]`. Owner: `raw`.

<a id="example-08-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 1d7be6c582fb565e7d102e9cf52272197f2430254bc520c08688058e42dc9666</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_NO_FLOW_COUNTERPART-1.json`.

```json
{"owner":"raw","reason":"NO_FLOW_COUNTERPART","method":"org.thingsboard.server.service.cf.ctx.state.CalculatedFieldCtx#evaluateSimpleExpression(net.objecthunter.exp4j.Expression, org.thingsboard.server.service.cf.ctx.state.CalculatedFieldState) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}}],"output":{"base":"exception","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-09"></a>
### Example 09: MARK_EXCLUDED

Method: `org.thingsboard.server.transport.mqtt.HashMapObserver#getActiveSessions(java.lang.String) [{}]`. Owner: `raw`.

<a id="example-09-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 7ec7ac3dca89b238acbd929b5f8e491a22655a5d69e5cf04876b94a814511a8e</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_MARK_EXCLUDED-0.json`.

```json
{"owner":"raw","reason":"MARK_EXCLUDED","method":"org.thingsboard.server.transport.mqtt.HashMapObserver#getActiveSessions(java.lang.String) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND","flag_present":true,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"},{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["MARK_EXCLUDED"]}],"current_protection_mask":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND"}],"protection_mask_truncated":false}
```

</details>

<a id="example-10"></a>
### Example 10: MARK_EXCLUDED

Method: `org.thingsboard.server.transport.mqtt.HashMapObserver#getAllSessions(java.lang.String) [{}]`. Owner: `raw`.

<a id="example-10-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 1a8df83296403089d5362c79be9aa0fc6f6c942fc4bfc99e157bc0498b8327cc</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_MARK_EXCLUDED-1.json`.

```json
{"owner":"raw","reason":"MARK_EXCLUDED","method":"org.thingsboard.server.transport.mqtt.HashMapObserver#getAllSessions(java.lang.String) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND","flag_present":true,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"},{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["MARK_EXCLUDED"]}],"current_protection_mask":[{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND"}],"protection_mask_truncated":false}
```

</details>

<a id="example-11"></a>
### Example 11: OUTPUT_BASE_MISMATCH

Method: `org.thingsboard.server.common.adaptor.JsonConverter#parseValues(com.google.gson.JsonObject) [{}]`. Owner: `raw`.

<a id="example-11-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 e5177caa44b5da34fe649ab94e028296bb58d768933346ee2977d713d861208e</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_OUTPUT_BASE_MISMATCH-0.json`.

```json
{"owner":"raw","reason":"OUTPUT_BASE_MISMATCH","method":"org.thingsboard.server.common.adaptor.JsonConverter#parseValues(com.google.gson.JsonObject) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}}],"output":{"base":"exception","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[644],"path":["java.lang.Iterable.Element"],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_BASE_MISMATCH","NO_ANNOTATED_ANY_PREFIX"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-12"></a>
### Example 12: OUTPUT_BASE_MISMATCH

Method: `org.thingsboard.server.common.adaptor.JsonConverter#parseProtoValues(com.google.gson.JsonObject) [{}]`. Owner: `raw`.

<a id="example-12-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 a3dd1ccf9e6789b68cc75bd24d1628dfc9b1f2b543c91612802268fd26367aed</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_OUTPUT_BASE_MISMATCH-1.json`.

```json
{"owner":"raw","reason":"OUTPUT_BASE_MISMATCH","method":"org.thingsboard.server.common.adaptor.JsonConverter#parseProtoValues(com.google.gson.JsonObject) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}}],"output":{"base":"exception","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"ret","base_family":"NS","path_ids":[644],"path":["java.lang.Iterable.Element"],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"},{"id":4,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;8","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=3)))"},{"id":5,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;45","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=4)))"},{"id":6,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;8","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=5)))"},{"id":7,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=6)))"},{"id":8,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;88","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=7)))"},{"id":9,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;0;$<ARTIFICIAL>_25;4","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=8)))"},{"id":10,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;103","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=9)))"},{"id":11,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;63","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=10)))"},{"id":12,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;63","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=11)))"},{"id":13,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;80","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=12)))"},{"id":14,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;3;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=13)))"},{"id":15,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;63","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=14)))"},{"id":16,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;0;$<ARTIFICIAL>_25;22","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=15)))"},{"id":17,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;45","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=16)))"},{"id":18,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=17)))"},{"id":19,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;95","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=18)))"},{"id":20,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;7;$<ARTIFICIAL>_25;23","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=19)))"},{"id":21,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;45","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=20)))"},{"id":22,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;8","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=21)))"},{"id":23,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=22)))"},{"id":24,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;95","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=23)))"},{"id":25,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;80","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=24)))"},{"id":26,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=25)))"},{"id":27,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;7;$<ARTIFICIAL>_25;16","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=26)))"},{"id":28,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;103","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=27)))"},{"id":29,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;95","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=28)))"},{"id":30,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;7;$<ARTIFICIAL>_25;7","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=29)))"},{"id":31,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;37","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=30)))"},{"id":32,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;55","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=31)))"},{"id":33,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;8","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=32)))"},{"id":34,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;0;$<ARTIFICIAL>_25;12","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=33)))"},{"id":35,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;4;$<ARTIFICIAL>_25;12","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=34)))"},{"id":36,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;37","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=35)))"},{"id":37,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;55","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=36)))"},{"id":38,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;37","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=37)))"},{"id":39,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;26","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=38)))"},{"id":40,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;88","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=39)))"},{"id":41,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;55","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=40)))"},{"id":42,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;88","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=41)))"},{"id":43,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;55","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=42)))"},{"id":44,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;3;$<ARTIFICIAL>_25;23","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=43)))"},{"id":45,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;95","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=44)))"},{"id":46,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;5;$<ARTIFICIAL>_25;80","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=45)))"},{"id":47,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;45","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=46)))"},{"id":48,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;26","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=47)))"},{"id":49,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;3;$<ARTIFICIAL>_25;7","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=48)))"},{"id":50,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;103","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=49)))"},{"id":51,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;26","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=50)))"},{"id":52,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;63","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=51)))"},{"id":53,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;26","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=52)))"},{"id":54,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;4;$<ARTIFICIAL>_25;22","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=53)))"},{"id":55,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;6;$<ARTIFICIAL>_25;37","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=54)))"},{"id":56,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;103","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=55)))"},{"id":57,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;4;$<ARTIFICIAL>_25;4","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=56)))"},{"id":58,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;1;$<ARTIFICIAL>_25;80","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=57)))"},{"id":59,"name":"java/security/unsafe-deserialization.yaml:unsafe-jackson-deserialization;2;$<ARTIFICIAL>_25;88","key":"Full(mark=ExactMark(group=GroupId(value=3), full=FullMarkId(value=58)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_BASE_MISMATCH","NO_ANNOTATED_ANY_PREFIX"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-13"></a>
### Example 13: ZERO_INITIAL

Method: `org.thingsboard.server.config.WebConfig#redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]`. Owner: `raw`.

<a id="example-13-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 61fc1123726d5cc0d871fc4ed190a396d7137cf3892409dd9df025db02d051c9</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_ZERO_INITIAL-0.json`.

```json
{"owner":"raw","reason":"ZERO_INITIAL","method":"org.thingsboard.server.config.WebConfig#redirectSwagger(jakarta.servlet.http.HttpServletRequest, jakarta.servlet.http.HttpServletResponse) [{}]","initial":[{"base":"<zero>","base_family":"Z","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":0,"name":"<zero>","key":"ControlZero"}}],"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":123,"name":"java/security/path-traversal.yaml:path-traversal#spring-path-source;1;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=5), full=FullMarkId(value=122)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-14"></a>
### Example 14: ZERO_INITIAL

Method: `org.thingsboard.server.controller.AdminController#checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]`. Owner: `raw`.

<a id="example-14-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 d6f8b159c72b31f82e59da00473ed14614e2060cb9ca959d3e3569c06cc4294c</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_ZERO_INITIAL-1.json`.

```json
{"owner":"raw","reason":"ZERO_INITIAL","method":"org.thingsboard.server.controller.AdminController#checkRepositoryAccess(org.thingsboard.server.common.data.sync.vc.RepositorySettings) [{}]","initial":[{"base":"<zero>","base_family":"Z","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":0,"name":"<zero>","key":"ControlZero"}}],"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":123,"name":"java/security/path-traversal.yaml:path-traversal#spring-path-source;1;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=5), full=FullMarkId(value=122)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":0,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-15"></a>
### Example 15: UNSUPPORTED_OUTPUT

Method: `org.thingsboard.server.controller.AuthController#logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]`. Owner: `raw`.

<a id="example-15-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 354e09abe9299353a4840b9ec077ee3a9761870f90825d288bf154166328356d</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_UNSUPPORTED_OUTPUT-0.json`.

```json
{"owner":"raw","reason":"UNSUPPORTED_OUTPUT","method":"org.thingsboard.server.controller.AuthController#logLogoutAction(jakarta.servlet.http.HttpServletRequest) [{}]","initial":[{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"STAR","field_exclusion":"Empty","mark":{"id":203,"name":"java/security/xxe.yaml:xxe#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=10), full=FullMarkId(value=202)))"}}],"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":203,"name":"java/security/xxe.yaml:xxe#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=10), full=FullMarkId(value=202)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"STAR","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[]}},"layer":"NORMAL","failed_scalar_flow_gates":["OUTPUT_TAIL_MISMATCH","NO_ANNOTATED_ANY_PREFIX"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-16"></a>
### Example 16: UNSUPPORTED_OUTPUT

Method: `org.thingsboard.server.controller.DashboardController#saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]`. Owner: `raw`.

<a id="example-16-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 c0feb59b4c399c7c55164fa619b7dfa5118debc2820c9d0e7ddb7a711a579a4b</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_UNSUPPORTED_OUTPUT-1.json`.

```json
{"owner":"raw","reason":"UNSUPPORTED_OUTPUT","method":"org.thingsboard.server.controller.DashboardController#saveDashboard(org.thingsboard.server.common.data.Dashboard, java.lang.String, jakarta.servlet.http.HttpServletResponse) [{}]","initial":[{"base":"<static>","base_family":"S","path_ids":[305,5860],"path":["org.thingsboard.server.common.data.id.TenantId","org.thingsboard.server.common.data.id.TenantId.tenants"],"tail":"STAR","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}}],"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"EXACT","field_exclusion":"Empty","mark":{"id":201,"name":"java/security/crlf-injection.yaml:http-response-splitting#source#1;0;$UNTRUSTED;2","key":"Full(mark=ExactMark(group=GroupId(value=8), full=FullMarkId(value=200)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":1,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"arg(0)","base_family":"NS","path_ids":[21176],"path":["org.thingsboard.server.common.data.Dashboard.resources"],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_TAIL_MISMATCH","NO_ANNOTATED_ANY_PREFIX"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="example-17"></a>
### Example 17: OUTPUT_TAIL_MISMATCH

Method: `org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]`. Owner: `raw`.

<a id="example-17-record"></a>
### Full initial, concrete output, FLOW candidates and mask

<details>
<summary>Full record; SHA-256 17d6d68706655294df192af2518a3b4f4723e1ced401cf6280a7659d1002fcc9</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/examples/example-raw_OUTPUT_TAIL_MISMATCH-0.json`.

```json
{"owner":"raw","reason":"OUTPUT_TAIL_MISMATCH","method":"org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]","initial":[{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}}],"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"STAR","field_exclusion":"Empty","mark":{"id":3,"name":"java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3","key":"Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"}},"layer":"DEMAND","flag_present":false,"matching_flow_leaf_count":2,"flow_candidates_truncated":false,"matching_initial_flow_candidates":[{"output":{"base":"arg(0)","base_family":"NS","path_ids":[],"path":[],"tail":"STAR","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[]}},"layer":"NORMAL","failed_scalar_flow_gates":["OUTPUT_BASE_MISMATCH"]},{"output":{"base":"ret","base_family":"NS","path_ids":[],"path":[],"tail":"ANY","field_exclusion":"Empty","mark":{"kind":"FLOW","excluded":[{"id":1,"name":"java/security/crypto.yaml:jjwt-hs256;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=0)))"},{"id":2,"name":"java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;","key":"Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"}]}},"layer":"DEMAND","failed_scalar_flow_gates":["OUTPUT_TAIL_MISMATCH"]}],"current_protection_mask":[],"protection_mask_truncated":false}
```

</details>

<a id="inline-example-source"></a>
## Actual code for all 17 example methods

These complete Java method declarations and bodies come from the fixed model sources. Adjacent annotations are included when they are in the same declaration block; class annotations can be outside the shown range. File and snippet hashes identify the text. Snippet hashes exclude the display-only final newline. This code identifies real calls, branches and returns; it is not an operation-level producer history.

<a id="example-01-source"></a>
### Example 01 source: `getCoapPublishCommand`

Source label: `sources/dao/src/main/java/org/thingsboard/server/dao/device/DeviceConnectivityServiceImpl.java`, lines 341–346. File SHA-256: `a7eeb022ca47447f16be9c77778ec62ceaa7cff2c07b939868e40af188205739`. Snippet SHA-256: `0112f5d512bff54b4a24e44b49fb8d21a0eb7bbaff8b8106c09dd792b2546d93`.

```java
    private String getCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {
        DeviceConnectivityInfo properties = getConnectivity(protocol);
        String hostName = getHost(baseUrl, properties, protocol);
        String port = StringUtils.isBlank(properties.getPort()) ? "" : ":" + properties.getPort();
        return DeviceConnectivityUtil.getCoapPublishCommand(protocol, hostName, port, deviceCredentials);
    }
```

<a id="example-02-source"></a>
### Example 02 source: `getDockerCoapPublishCommand`

Source label: `sources/dao/src/main/java/org/thingsboard/server/dao/device/DeviceConnectivityServiceImpl.java`, lines 348–353. File SHA-256: `a7eeb022ca47447f16be9c77778ec62ceaa7cff2c07b939868e40af188205739`. Snippet SHA-256: `8d2cefd1db3e4bb9e6e1cd3e2edbc231f90716b788637e9b44dd9014817edb4e`.

```java
    private String getDockerCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {
        DeviceConnectivityInfo properties = getConnectivity(protocol);
        String host = getHost(baseUrl, properties, protocol);
        String port = StringUtils.isBlank(properties.getPort()) ? "" : ":" + properties.getPort();
        return DeviceConnectivityUtil.getDockerCoapPublishCommand(protocol, baseUrl, host, port, deviceCredentials);
    }
```

<a id="example-03-source"></a>
### Example 03 source: `checkActivateToken`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/AuthController.java`, lines 134–150. File SHA-256: `dd46a45322143141790d0d0ba925303abb5a0bbbb0390401f42aa7340151b6f3`. Snippet SHA-256: `c23ff6b740c2dce1ceabc7ba25c2470ce7973e70dc2c426e06fd501f13a85570`.

```java
    @ApiOperation(value = "Check Activate User Token (checkActivateToken)",
            notes = "Checks the activation token and forwards user to 'Create Password' page. " +
                    "If token is valid, returns '303 See Other' (redirect) response code with the correct address of 'Create Password' page and same 'activateToken' specified in the URL parameters. " +
                    "If token is not valid, returns '409 Conflict'. " +
                    "If token is expired, redirects to error page.")
    @GetMapping(value = "/noauth/activate", params = {"activateToken"})
    public ResponseEntity<?> checkActivateToken(
            @Parameter(description = "The activate token string.")
            @RequestParam(value = "activateToken") String activateToken) {
        UserCredentials userCredentials = userService.findUserCredentialsByActivateToken(TenantId.SYS_TENANT_ID, activateToken);
        if (userCredentials == null) {
            return response(HttpStatus.CONFLICT);
        } else if (userCredentials.isActivationTokenExpired()) {
            return redirectTo("/activationLinkExpired");
        }
        return redirectTo("/login/createPassword?activateToken=" + activateToken);
    }
```

<a id="example-04-source"></a>
### Example 04 source: `checkResetToken`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/AuthController.java`, lines 174–193. File SHA-256: `dd46a45322143141790d0d0ba925303abb5a0bbbb0390401f42aa7340151b6f3`. Snippet SHA-256: `115fddcc52c88b5eaf2e993a0b22129d1c6973a7830883bc9aaec0f761aed7d2`.

```java
    @ApiOperation(value = "Check password reset token (checkResetToken)",
            notes = "Checks the password reset token and forwards user to 'Reset Password' page. " +
                    "If token is valid, returns '303 See Other' (redirect) response code with the correct address of 'Reset Password' page and same 'resetToken' specified in the URL parameters. " +
                    "If token is not valid, returns '409 Conflict'. " +
                    "If token is expired, redirects to error page.")
    @GetMapping(value = "/noauth/resetPassword", params = {"resetToken"})
    public ResponseEntity<?> checkResetToken(
            @Parameter(description = "The reset token string.")
            @RequestParam(value = "resetToken") String resetToken) {
        UserCredentials userCredentials = userService.findUserCredentialsByResetToken(TenantId.SYS_TENANT_ID, resetToken);
        if (userCredentials == null) {
            return response(HttpStatus.CONFLICT);
        } else if (userCredentials.isResetTokenExpired()) {
            return redirectTo("/passwordResetLinkExpired");
        }
        if (!rateLimitService.checkRateLimit(LimitedApi.PASSWORD_RESET, userCredentials.getUserId(), defaultLimitsConfiguration)) {
            return response(HttpStatus.TOO_MANY_REQUESTS);
        }
        return redirectTo("/login/resetPassword?resetToken=" + resetToken);
    }
```

<a id="example-05-source"></a>
### Example 05 source: `getAppleAppSiteAssociation`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/QrCodeSettingsController.java`, lines 108–118. File SHA-256: `adfcd8615f5cc8ecfc44369054f4aafcbddd89c67decfe5797e563b39ce3f6ae`. Snippet SHA-256: `be0a88fdf0ada855df207c8bee772be00d4e105526b70df38c8fa12ecbc507f5`.

```java
    @ApiOperation(value = "Get associated ios applications (getAppleAppSiteAssociation)")
    @GetMapping(value = "/.well-known/apple-app-site-association")
    public ResponseEntity<JsonNode> getAppleAppSiteAssociation() {
        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, IOS);
        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;
        if (storeInfo != null && storeInfo.getAppId() != null) {
            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(APPLE_APP_SITE_ASSOCIATION_PATTERN, storeInfo.getAppId())));
        } else {
            return ResponseEntity.notFound().build();
        }
    }
```

<a id="example-06-source"></a>
### Example 06 source: `getAssetLinks`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/QrCodeSettingsController.java`, lines 96–106. File SHA-256: `adfcd8615f5cc8ecfc44369054f4aafcbddd89c67decfe5797e563b39ce3f6ae`. Snippet SHA-256: `9f789014b7dbdf8c1e38302d1e00d8d66ac9fa11d395d68d7f1410539918ecbb`.

```java
    @ApiOperation(value = "Get associated android applications (getAssetLinks)")
    @GetMapping(value = "/.well-known/assetlinks.json")
    public ResponseEntity<JsonNode> getAssetLinks() {
        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, ANDROID);
        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;
        if (storeInfo != null && storeInfo.getSha256CertFingerprints() != null) {
            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(ASSET_LINKS_PATTERN, mobileApp.getPkgName(), storeInfo.getSha256CertFingerprints())));
        } else {
            return ResponseEntity.notFound().build();
        }
    }
```

<a id="example-07-source"></a>
### Example 07 source: `parseEnum`

Source label: `sources/rule-engine/rule-engine-components/src/main/java/org/thingsboard/rule/engine/ai/Langchain4jJsonSchemaAdapter.java`, lines 77–90. File SHA-256: `69f670c9a49c0bad4c4768d00f1ea67c6c015639f78972a473fa092b33ea26f6`. Snippet SHA-256: `30553445548e39fc52ae1837086b51232bffda51009eb5de60d3106a6cae3511`.

```java
    private static JsonEnumSchema.Builder parseEnum(JsonNode enumSchema) {
        var builder = new JsonEnumSchema.Builder();

        List<String> enumValues = new ArrayList<>();
        for (JsonNode element : enumSchema.get("enum")) {
            if (!element.isTextual()) {
                throw new IllegalArgumentException("Expected each 'enum' element to be a string, but found: " + element.getNodeType());
            }
            enumValues.add(element.textValue());
        }
        builder.enumValues(enumValues);

        return builder;
    }
```

<a id="example-08-source"></a>
### Example 08 source: `evaluateSimpleExpression`

Source label: `sources/application/src/main/java/org/thingsboard/server/service/cf/ctx/state/CalculatedFieldCtx.java`, lines 313–329. File SHA-256: `1e42dc694bc408b56efc92fe8b53a3f560d8ec75a61d9ca6f0af7e9247ded23e`. Snippet SHA-256: `a3663682898f5f277466636f4f658f84a1a4f1d37843c6c69fcaa0eb186b866c`.

```java
    public double evaluateSimpleExpression(Expression expression, CalculatedFieldState state) {
        for (Map.Entry<String, ArgumentEntry> entry : state.getArguments().entrySet()) {
            try {
                BasicKvEntry kvEntry = ((SingleValueArgumentEntry) entry.getValue()).getKvEntryValue();
                double value = switch (kvEntry.getDataType()) {
                    case LONG -> kvEntry.getLongValue().map(Long::doubleValue).orElseThrow();
                    case DOUBLE -> kvEntry.getDoubleValue().orElseThrow();
                    case BOOLEAN -> kvEntry.getBooleanValue().map(b -> b ? 1.0 : 0.0).orElseThrow();
                    case STRING, JSON -> Double.parseDouble(kvEntry.getValueAsString());
                };
                expression.setVariable(entry.getKey(), value);
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Argument '" + entry.getKey() + "' is not a number.");
            }
        }
        return expression.evaluate();
    }
```

<a id="example-09-source"></a>
### Example 09 source: `getActiveSessions`

Source label: `sources/common/transport/mqtt/src/main/java/org/thingsboard/server/transport/mqtt/HashMapObserver.java`, lines 115–138. File SHA-256: `11be0e212f6a7fb9d3253719856ad57819953979bdb35c7dd0453bfa53420ebb`. Snippet SHA-256: `b6ca80a125f482d23e633978f122f4c59a56cdae5f30d57abf250d831f38cd9c`.

```java
    @Override
    public String getActiveSessions(String unused) {
        log.info("getActiveSessions()");
        StringBuilder content = new StringBuilder();
        try {
            int count = 0;
            for (Map.Entry<UUID, SessionMetaData> entry : map.entrySet()) {
                SessionMetaData sessionMetaData = entry.getValue();
                if (sessionMetaData.getListener() instanceof MqttTransportHandler) {
                    MqttTransportHandler listener = (MqttTransportHandler) sessionMetaData.getListener();
                    if (listener.deviceSessionCtx.getChannel().channel().isActive()) {
                        addContent(entry, ++count, content);
                    }
                } else {
                    addContent(sessionMetaData.getListener().getClass(), ++count, content);
                }
            }
            return content.toString();
        } catch (Exception e) {
            log.error(e.getMessage(), e);

            throw e;
        }
    }
```

<a id="example-10-source"></a>
### Example 10 source: `getAllSessions`

Source label: `sources/common/transport/mqtt/src/main/java/org/thingsboard/server/transport/mqtt/HashMapObserver.java`, lines 58–72. File SHA-256: `11be0e212f6a7fb9d3253719856ad57819953979bdb35c7dd0453bfa53420ebb`. Snippet SHA-256: `630175c718dbe9a7ed445628434b962bec559f486f449b365976c5b42ca18a8a`.

```java
    @Override
    public String getAllSessions(String unused) {
        log.info("getAllSessions()");
        StringBuilder content = new StringBuilder();
        try {
            int count = 0;
            for (Map.Entry<UUID, SessionMetaData> entry : map.entrySet()) {
                addContent(entry, ++count, content);
            }
            return content.toString();
        } catch (Exception e) {
            log.error(e.getMessage(), e);
            throw e;
        }
    }
```

<a id="example-11-source"></a>
### Example 11 source: `parseValues`

Source label: `sources/common/proto/src/main/java/org/thingsboard/server/common/adaptor/JsonConverter.java`, lines 548–582. File SHA-256: `29a62dd9f4c994ca760a123274188b39ab73d131548f3b27f3777e9626a1f249`. Snippet SHA-256: `ae8156f2d8d78cddcde401f8a010c3dcdc9969febec72f0d1abc2e7c8abd6d8a`.

```java
    private static List<KvEntry> parseValues(JsonObject valuesObject) {
        List<KvEntry> result = new ArrayList<>();
        for (Entry<String, JsonElement> valueEntry : valuesObject.entrySet()) {
            JsonElement element = valueEntry.getValue();
            if (element.isJsonPrimitive()) {
                JsonPrimitive value = element.getAsJsonPrimitive();
                if (value.isString()) {
                    if (maxStringValueLength > 0 && value.getAsString().length() > maxStringValueLength) {
                        String message = String.format("String value length [%d] for key [%s] is greater than maximum allowed [%d]", value.getAsString().length(), valueEntry.getKey(), maxStringValueLength);
                        throw new JsonSyntaxException(message);
                    }
                    if (isTypeCastEnabled && NumberUtils.isParsable(value.getAsString())) {
                        try {
                            parseNumericValue(result, valueEntry, value);
                        } catch (RuntimeException th) {
                            result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));
                        }
                    } else {
                        result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));
                    }
                } else if (value.isBoolean()) {
                    result.add(new BooleanDataEntry(valueEntry.getKey(), value.getAsBoolean()));
                } else if (value.isNumber()) {
                    parseNumericValue(result, valueEntry, value);
                } else {
                    throw new JsonSyntaxException(CAN_T_PARSE_VALUE + value);
                }
            } else if (element.isJsonObject() || element.isJsonArray()) {
                result.add(new JsonDataEntry(valueEntry.getKey(), element.toString()));
            } else {
                throw new JsonSyntaxException(CAN_T_PARSE_VALUE + element);
            }
        }
        return result;
    }
```

<a id="example-12-source"></a>
### Example 12 source: `parseProtoValues`

Source label: `sources/common/proto/src/main/java/org/thingsboard/server/common/adaptor/JsonConverter.java`, lines 230–267. File SHA-256: `29a62dd9f4c994ca760a123274188b39ab73d131548f3b27f3777e9626a1f249`. Snippet SHA-256: `2357e227b921b7cb8d07273d752a17fc97c68996b14a5151c5dd08cfd7f1056c`.

```java
    private static List<KeyValueProto> parseProtoValues(JsonObject valuesObject) {
        List<KeyValueProto> result = new ArrayList<>();
        for (Entry<String, JsonElement> valueEntry : valuesObject.entrySet()) {
            JsonElement element = valueEntry.getValue();
            if (element.isJsonPrimitive()) {
                JsonPrimitive value = element.getAsJsonPrimitive();
                if (value.isString()) {
                    if (maxStringValueLength > 0 && value.getAsString().length() > maxStringValueLength) {
                        String message = String.format("String value length [%d] for key [%s] is greater than maximum allowed [%d]", value.getAsString().length(), valueEntry.getKey(), maxStringValueLength);
                        throw new JsonSyntaxException(message);
                    }
                    if (isTypeCastEnabled && NumberUtils.isParsable(value.getAsString())) {
                        try {
                            result.add(buildNumericKeyValueProto(value, valueEntry.getKey()));
                        } catch (RuntimeException th) {
                            result.add(KeyValueProto.newBuilder().setKey(valueEntry.getKey()).setType(KeyValueType.STRING_V)
                                    .setStringV(value.getAsString()).build());
                        }
                    } else {
                        result.add(KeyValueProto.newBuilder().setKey(valueEntry.getKey()).setType(KeyValueType.STRING_V)
                                .setStringV(value.getAsString()).build());
                    }
                } else if (value.isBoolean()) {
                    result.add(KeyValueProto.newBuilder().setKey(valueEntry.getKey()).setType(KeyValueType.BOOLEAN_V)
                            .setBoolV(value.getAsBoolean()).build());
                } else if (value.isNumber()) {
                    result.add(buildNumericKeyValueProto(value, valueEntry.getKey()));
                } else if (!value.isJsonNull()) {
                    throw new JsonSyntaxException(CAN_T_PARSE_VALUE + value);
                }
            } else if (element.isJsonObject() || element.isJsonArray()) {
                result.add(KeyValueProto.newBuilder().setKey(valueEntry.getKey()).setType(KeyValueType.JSON_V).setJsonV(element.toString()).build());
            } else if (!element.isJsonNull()) {
                throw new JsonSyntaxException(CAN_T_PARSE_VALUE + element);
            }
        }
        return result;
    }
```

<a id="example-13-source"></a>
### Example 13 source: `redirectSwagger`

Source label: `sources/application/src/main/java/org/thingsboard/server/config/WebConfig.java`, lines 34–38. File SHA-256: `676a498d30cebb88b253ea76972cc3eb9b977ec1acdb841898eb53e4831b2763`. Snippet SHA-256: `ba351f2ad003239b080b7836baab275c34eedfd66e61715404bcf697cc6ffdb4`.

```java
    @RequestMapping("/swagger-ui.html")
    public void redirectSwagger(HttpServletRequest request, HttpServletResponse response) throws IOException {
        String baseUrl = MiscUtils.constructBaseUrl(request);
        response.sendRedirect(baseUrl + "/swagger-ui/");
    }
```

<a id="example-14-source"></a>
### Example 14 source: `checkRepositoryAccess`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/AdminController.java`, lines 328–338. File SHA-256: `6f3842b16b4bbe4e7f262b070410b44d1cd100654fbfc5fd5b3a66be433bca3a`. Snippet SHA-256: `ce23961ab658e3c37c0f86aec418d81a036e273f2d641b9779b9ab59c68b8a49`.

```java
    @ApiOperation(value = "Check repository access (checkRepositoryAccess)",
            notes = "Attempts to check repository access. " + TENANT_AUTHORITY_PARAGRAPH)
    @PreAuthorize("hasAuthority('TENANT_ADMIN')")
    @PostMapping(value = "/repositorySettings/checkAccess")
    public DeferredResult<Void> checkRepositoryAccess(
            @Parameter(description = "A JSON value representing the Repository Settings.")
            @RequestBody RepositorySettings settings) throws Exception {
        accessControlService.checkPermission(getCurrentUser(), Resource.VERSION_CONTROL, Operation.READ);
        settings.setLocalOnly(false); // only to be used in tests
        return wrapFuture(versionControlService.checkVersionControlAccess(getTenantId(), settings), vcRequestTimeout);
    }
```

<a id="example-15-source"></a>
### Example 15 source: `logLogoutAction`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/AuthController.java`, lines 280–284. File SHA-256: `dd46a45322143141790d0d0ba925303abb5a0bbbb0390401f42aa7340151b6f3`. Snippet SHA-256: `ff9da3c29971afc286b84af0c4e4dfaa694f8b59fa33508a1e39932105ac3b11`.

```java
    private void logLogoutAction(HttpServletRequest request) throws ThingsboardException {
        var user = getCurrentUser();
        systemSecurityService.logLoginAction(user, new RestAuthenticationDetails(request), ActionType.LOGOUT, null);
        eventPublisher.publishEvent(new UserSessionInvalidationEvent(user.getSessionId()));
    }
```

<a id="example-16-source"></a>
### Example 16 source: `saveDashboard`

Source label: `sources/application/src/main/java/org/thingsboard/server/controller/DashboardController.java`, lines 172–190. File SHA-256: `4cf8fef9708a7e324df2346629e361c705cb4f4b7204ea77719398000761ba19`. Snippet SHA-256: `c9c3e070547ff277dbcfd14e851e26bdd5d9e091b7f586dc2677426f3000aeef`.

```java
    @ApiOperation(value = "Create Or Update Dashboard (saveDashboard)",
            notes = "Create or update the Dashboard. When creating dashboard, platform generates Dashboard Id as " + UUID_WIKI_LINK +
                    "The newly created Dashboard id will be present in the response. " +
                    "Specify existing Dashboard id to update the dashboard. " +
                    "Referencing non-existing dashboard Id will cause 'Not Found' error. " +
                    "Remove 'id', 'tenantId' and optionally 'customerId' from the request body example (below) to create new Dashboard entity. " +
                    TENANT_AUTHORITY_PARAGRAPH)
    @PreAuthorize("hasAuthority('TENANT_ADMIN')")
    @PostMapping(value = "/dashboard")
    public void saveDashboard(@io.swagger.v3.oas.annotations.parameters.RequestBody(description = "A JSON value representing the dashboard.")
                              @RequestBody Dashboard dashboard,
                              @RequestHeader(name = HttpHeaders.ACCEPT_ENCODING, required = false) String acceptEncodingHeader,
                              HttpServletResponse response) throws Exception {
        dashboard.setTenantId(getTenantId());
        checkEntity(dashboard.getId(), dashboard, Resource.DASHBOARD);
        var savedDashboard = tbDashboardService.save(dashboard, getCurrentUser());
        response.setContentType(APPLICATION_JSON_VALUE);
        compressResponseWithGzipIFAccepted(acceptEncodingHeader, response, JacksonUtil.writeValueAsBytes(savedDashboard));
    }
```

<a id="example-17-source"></a>
### Example 17 source: `getColumnValue`

Source label: `sources/application/src/main/java/org/thingsboard/server/service/install/migrate/CassandraToSqlColumn.java`, lines 103–132. File SHA-256: `a6ad1253084294ae89a5f5aed1f65ee2815172ccffb7afd9244972e9856e8652`. Snippet SHA-256: `8de12dd47213b55bdd2b81832278db15168d871613e53612655a992a9e18f204`.

```java
    public String getColumnValue(Row row) {
        if (row.isNull(index)) {
            if (this.type == CassandraToSqlColumnType.BOOLEAN && !this.allowNullBoolean) {
                return Boolean.toString(false);
            } else {
                return null;
            }
        } else {
            switch (this.type) {
                case ID:
                    return UUIDConverter.fromTimeUUID(row.getUuid(index));
                case DOUBLE:
                    return Double.toString(row.getDouble(index));
                case INTEGER:
                    return Integer.toString(row.getInt(index));
                case FLOAT:
                    return Float.toString(row.getFloat(index));
                case BIGINT:
                    return Long.toString(row.getLong(index));
                case BOOLEAN:
                    return Boolean.toString(row.getBoolean(index));
                case STRING:
                case JSON:
                case ENUM_TO_INT:
                default:
                    String value = row.getString(index);
                    return this.replaceNullChars(value);
            }
        }
    }
```

<a id="inline-recorded-source-excerpts"></a>
## Additional recorded source excerpts

These original excerpts cover hot methods, six-origin template reuse and static fields. Their line ranges mark each excerpt boundary. They do not claim an exact producer history.

Project source revision: `b31176433e8065ae4cb2a285bcd5e03fce9014f5`. These snippets identify the actual methods; the census has no operation-level producer trace, so they do not establish which statement produced a sampled relation.

### processUplinkMsg

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/edge/rpc/EdgeGrpcSession.java:823`.

```java
    protected ListenableFuture<List<Void>> processUplinkMsg(UplinkMsg uplinkMsg) {
        List<ListenableFuture<Void>> result = new ArrayList<>();
        try {
            if (uplinkMsg.getDeviceProfileUpdateMsgCount() > 0) {
                for (DeviceProfileUpdateMsg deviceProfileUpdateMsg : uplinkMsg.getDeviceProfileUpdateMsgList()) {
                    result.add(ctx.getDeviceProfileProcessor().processDeviceProfileMsgFromEdge(edge.getTenantId(), edge, deviceProfileUpdateMsg));
                }
            }
            if (uplinkMsg.getDeviceUpdateMsgCount() > 0) {
                for (DeviceUpdateMsg deviceUpdateMsg : uplinkMsg.getDeviceUpdateMsgList()) {
                    result.add(ctx.getDeviceProcessor().processDeviceMsgFromEdge(edge.getTenantId(), edge, deviceUpdateMsg));
                }
            }
            if (uplinkMsg.getDeviceCredentialsUpdateMsgCount() > 0) {
                for (DeviceCredentialsUpdateMsg deviceCredentialsUpdateMsg : uplinkMsg.getDeviceCredentialsUpdateMsgList()) {
                    result.add(ctx.getDeviceProcessor().processDeviceCredentialsMsgFromEdge(edge.getTenantId(), edge.getId(), deviceCredentialsUpdateMsg));
                }
            }
            if (uplinkMsg.getAssetProfileUpdateMsgCount() > 0) {
                for (AssetProfileUpdateMsg assetProfileUpdateMsg : uplinkMsg.getAssetProfileUpdateMsgList()) {
                    result.add(ctx.getAssetProfileProcessor().processAssetProfileMsgFromEdge(edge.getTenantId(), edge, assetProfileUpdateMsg));
                }
            }
            if (uplinkMsg.getAssetUpdateMsgCount() > 0) {
                for (AssetUpdateMsg assetUpdateMsg : uplinkMsg.getAssetUpdateMsgList()) {
                    result.add(ctx.getAssetProcessor().processAssetMsgFromEdge(edge.getTenantId(), edge, assetUpdateMsg));
                }
            }
            if (uplinkMsg.getRuleChainUpdateMsgCount() > 0) {
                for (RuleChainUpdateMsg ruleChainUpdateMsg : uplinkMsg.getRuleChainUpdateMsgList()) {
                    result.add(ctx.getRuleChainProcessor().processRuleChainMsgFromEdge(edge.getTenantId(), edge, ruleChainUpdateMsg));
                }
            }
            if (uplinkMsg.getRuleChainMetadataUpdateMsgCount() > 0) {
                for (RuleChainMetadataUpdateMsg ruleChainMetadataUpdateMsg : uplinkMsg.getRuleChainMetadataUpdateMsgList()) {
                    result.add(ctx.getRuleChainProcessor().processRuleChainMetadataMsgFromEdge(edge.getTenantId(), edge, ruleChainMetadataUpdateMsg));
                }
            }
            if (uplinkMsg.getEntityViewUpdateMsgCount() > 0) {
                for (EntityViewUpdateMsg entityViewUpdateMsg : uplinkMsg.getEntityViewUpdateMsgList()) {
                    result.add(ctx.getEntityViewProcessor().processEntityViewMsgFromEdge(edge.getTenantId(), edge, entityViewUpdateMsg));
                }
            }
```

### replaceByMapping

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/util/src/main/java/org/thingsboard/common/util/JacksonUtil.java:523`.

```java
    public static void replaceByMapping(JsonNode jsonNode, Map<String, String> mapping, Map<String, String> templateParams, BiFunction<String, JsonNode, JsonNode> processor) {
        for (var entry : mapping.entrySet()) {
            String expression = entry.getValue();
            Queue<JsonPathProcessingTask> tasks = new LinkedList<>();
            tasks.add(new JsonPathProcessingTask(entry.getKey().split("\\."), templateParams, jsonNode));
            while (!tasks.isEmpty()) {
                JsonPathProcessingTask task = tasks.poll();
                String token = task.currentToken();
                JsonNode node = task.getNode();
                if (node == null) {
                    continue;
                }
                if (token.equals("*") || token.startsWith("$")) {
                    String variableName = token.startsWith("$") ? token.substring(1) : null;
                    if (node.isArray()) {
                        ArrayNode childArray = (ArrayNode) node;
                        for (JsonNode element : childArray) {
                            tasks.add(task.next(element));
                        }
                    } else if (node.isObject()) {
                        ObjectNode on = (ObjectNode) node;
                        for (Iterator<Map.Entry<String, JsonNode>> it = on.fields(); it.hasNext(); ) {
                            var kv = it.next();
                            if (variableName != null) {
                                tasks.add(task.next(kv.getValue(), variableName, kv.getKey()));
                            } else {
                                tasks.add(task.next(kv.getValue()));
                            }
                        }
                    }
                } else {
                    String variableName = null;
                    String variableValue = null;
                    if (token.contains("[$")) {
                        variableName = StringUtils.substringBetween(token, "[$", "]");
                        token = StringUtils.substringBefore(token, "[$");
                    }
                    if (node.has(token)) {
                        JsonNode value = node.get(token);
                        if (variableName != null && value.has(variableName) && value.get(variableName).isTextual()) {
                            variableValue = value.get(variableName).asText();
                        }
                        if (task.isLast()) {
                            String name = expression;
                            for (var replacement : task.getVariables().entrySet()) {
                                name = name.replace("$" + replacement.getKey(), Strings.nullToEmpty(replacement.getValue()));
                            }
                            ((ObjectNode) node).set(token, processor.apply(name, value));
                        } else {
                            if (StringUtils.isNotEmpty(variableName)) {
                                tasks.add(task.next(value, variableName, variableValue));
                            } else {
                                tasks.add(task.next(value));
                            }
                        }
                    }
                }
            }
```

### template_reuse_six_origins

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/cf/DefaultCalculatedFieldProcessingService.java:145`.

```java
    public void processResult(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {
        if (result instanceof AlarmCalculatedFieldResult) {
            sendMsgToRuleEngine(tenantId, entityId, callback, result.toTbMsg(entityId, cfName, cfIds));
            return;
        }
        TelemetryCalculatedFieldResult telemetryResult = result instanceof TelemetryCalculatedFieldResult telemetryRes
                ? telemetryRes : ((PropagationCalculatedFieldResult) result).getResult();
        switch (telemetryResult.getOutputStrategy().getType()) {
            case IMMEDIATE -> processImmediately(tenantId, entityId, cfName, result, cfIds, callback);
            case RULE_CHAIN -> pushMsgToRuleEngine(tenantId, entityId, cfName, result, cfIds, callback);
        }
    }

    private void processImmediately(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {
        if (result instanceof TelemetryCalculatedFieldResult telemetryResult) {
            saveTelemetryResult(tenantId, entityId, cfName, telemetryResult, cfIds, callback);
            return;
        }
        if (result instanceof PropagationCalculatedFieldResult propagationResult) {
            handlePropagationResults(propagationResult, callback,
                    (entity, res, cb) -> saveTelemetryResult(tenantId, entity, cfName, res, cfIds, cb));
            return;
        }
        callback.onSuccess();
    }

    private void pushMsgToRuleEngine(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {
        if (result instanceof PropagationCalculatedFieldResult propagationResult) {
            handlePropagationResults(propagationResult, callback,
                    (entity, res, cb) -> sendMsgToRuleEngine(tenantId, entity, cb, res.toTbMsg(entity, cfName, cfIds)));
            return;
        }

        sendMsgToRuleEngine(tenantId, entityId, callback, result.toTbMsg(entityId, cfName, cfIds));
    }

    @Override
    public void pushMsgToLinks(CalculatedFieldTelemetryMsg msg, List<CalculatedFieldEntityCtxId> linkedCalculatedFields, TbCallback callback) {
        Map<TopicPartitionInfo, List<CalculatedFieldEntityCtxId>> unicasts = new HashMap<>();
        List<CalculatedFieldEntityCtxId> broadcasts = new ArrayList<>();
        for (CalculatedFieldEntityCtxId link : linkedCalculatedFields) {
```

### PROTECTION_ONLY

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/dao/src/main/java/org/thingsboard/server/dao/device/DeviceConnectivityServiceImpl.java:341`.

```java
    private String getCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {
        DeviceConnectivityInfo properties = getConnectivity(protocol);
        String hostName = getHost(baseUrl, properties, protocol);
        String port = StringUtils.isBlank(properties.getPort()) ? "" : ":" + properties.getPort();
        return DeviceConnectivityUtil.getCoapPublishCommand(protocol, hostName, port, deviceCredentials);
    }

    private String getDockerCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {
        DeviceConnectivityInfo properties = getConnectivity(protocol);
        String host = getHost(baseUrl, properties, protocol);
        String port = StringUtils.isBlank(properties.getPort()) ? "" : ":" + properties.getPort();
        return DeviceConnectivityUtil.getDockerCoapPublishCommand(protocol, baseUrl, host, port, deviceCredentials);
    }
```

### CROSS_ATOM

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/QrCodeSettingsController.java:98`.

```java
    public ResponseEntity<JsonNode> getAssetLinks() {
        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, ANDROID);
        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;
        if (storeInfo != null && storeInfo.getSha256CertFingerprints() != null) {
            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(ASSET_LINKS_PATTERN, mobileApp.getPkgName(), storeInfo.getSha256CertFingerprints())));
        } else {
            return ResponseEntity.notFound().build();
        }
    }

    @ApiOperation(value = "Get associated ios applications (getAppleAppSiteAssociation)")
    @GetMapping(value = "/.well-known/apple-app-site-association")
    public ResponseEntity<JsonNode> getAppleAppSiteAssociation() {
        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, IOS);
        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;
        if (storeInfo != null && storeInfo.getAppId() != null) {
            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(APPLE_APP_SITE_ASSOCIATION_PATTERN, storeInfo.getAppId())));
        } else {
            return ResponseEntity.notFound().build();
        }
```

### UNSUPPORTED_INITIAL

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/AuthController.java:137`.

```java
                    "If token is not valid, returns '409 Conflict'. " +
                    "If token is expired, redirects to error page.")
    @GetMapping(value = "/noauth/activate", params = {"activateToken"})
    public ResponseEntity<?> checkActivateToken(
            @Parameter(description = "The activate token string.")
            @RequestParam(value = "activateToken") String activateToken) {
        UserCredentials userCredentials = userService.findUserCredentialsByActivateToken(TenantId.SYS_TENANT_ID, activateToken);
        if (userCredentials == null) {
            return response(HttpStatus.CONFLICT);
        } else if (userCredentials.isActivationTokenExpired()) {
            return redirectTo("/activationLinkExpired");
        }
        return redirectTo("/login/createPassword?activateToken=" + activateToken);
    }

    @ApiOperation(value = "Request reset password email (requestResetPasswordByEmail)",
            notes = "Request to send the reset password email if the user with specified email address is present in the database. " +
                    "Always return '200 OK' status for security purposes.")
    @PostMapping(value = "/noauth/resetPasswordByEmail")
```

### OUTPUT_TAIL_MISMATCH

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/install/migrate/CassandraToSqlColumn.java:103`.

```java
    public String getColumnValue(Row row) {
        if (row.isNull(index)) {
            if (this.type == CassandraToSqlColumnType.BOOLEAN && !this.allowNullBoolean) {
                return Boolean.toString(false);
            } else {
                return null;
            }
        } else {
            switch (this.type) {
                case ID:
                    return UUIDConverter.fromTimeUUID(row.getUuid(index));
                case DOUBLE:
                    return Double.toString(row.getDouble(index));
                case INTEGER:
                    return Integer.toString(row.getInt(index));
                case FLOAT:
                    return Float.toString(row.getFloat(index));
                case BIGINT:
                    return Long.toString(row.getLong(index));
                case BOOLEAN:
                    return Boolean.toString(row.getBoolean(index));
                case STRING:
                case JSON:
                case ENUM_TO_INT:
                default:
                    String value = row.getString(index);
                    return this.replaceNullChars(value);
            }
        }
    }

    public void setColumnValue(PreparedStatement sqlInsertStatement, String value) throws SQLException {
        if (value == null) {
            sqlInsertStatement.setNull(this.sqlIndex, this.sqlType);
        } else {
            switch (this.type) {
                case DOUBLE:
                    sqlInsertStatement.setDouble(this.sqlIndex, Double.parseDouble(value));
```

### MARK_EXCLUDED

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/transport/mqtt/src/main/java/org/thingsboard/server/transport/mqtt/HashMapObserver.java:116`.

```java
    public String getActiveSessions(String unused) {
        log.info("getActiveSessions()");
        StringBuilder content = new StringBuilder();
        try {
            int count = 0;
            for (Map.Entry<UUID, SessionMetaData> entry : map.entrySet()) {
                SessionMetaData sessionMetaData = entry.getValue();
                if (sessionMetaData.getListener() instanceof MqttTransportHandler) {
                    MqttTransportHandler listener = (MqttTransportHandler) sessionMetaData.getListener();
                    if (listener.deviceSessionCtx.getChannel().channel().isActive()) {
                        addContent(entry, ++count, content);
                    }
                } else {
                    addContent(sessionMetaData.getListener().getClass(), ++count, content);
                }
            }
            return content.toString();
        } catch (Exception e) {
            log.error(e.getMessage(), e);

            throw e;
        }
    }

    @Override
    public String getGatewayDeviceSessionContextConnectedSessions(String unused) {
```

### NO_FLOW_COUNTERPART

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/rule-engine/rule-engine-components/src/main/java/org/thingsboard/rule/engine/ai/Langchain4jJsonSchemaAdapter.java:77`.

```java
    private static JsonEnumSchema.Builder parseEnum(JsonNode enumSchema) {
        var builder = new JsonEnumSchema.Builder();

        List<String> enumValues = new ArrayList<>();
        for (JsonNode element : enumSchema.get("enum")) {
            if (!element.isTextual()) {
                throw new IllegalArgumentException("Expected each 'enum' element to be a string, but found: " + element.getNodeType());
            }
            enumValues.add(element.textValue());
        }
        builder.enumValues(enumValues);

        return builder;
    }

    private static JsonObjectSchema.Builder parseObject(JsonNode objectSchema) {
        var builder = new JsonObjectSchema.Builder();

        JsonNode propertiesNode = objectSchema.get("properties");
```

### OUTPUT_BASE_MISMATCH

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/proto/src/main/java/org/thingsboard/server/common/adaptor/JsonConverter.java:548`.

```java
    private static List<KvEntry> parseValues(JsonObject valuesObject) {
        List<KvEntry> result = new ArrayList<>();
        for (Entry<String, JsonElement> valueEntry : valuesObject.entrySet()) {
            JsonElement element = valueEntry.getValue();
            if (element.isJsonPrimitive()) {
                JsonPrimitive value = element.getAsJsonPrimitive();
                if (value.isString()) {
                    if (maxStringValueLength > 0 && value.getAsString().length() > maxStringValueLength) {
                        String message = String.format("String value length [%d] for key [%s] is greater than maximum allowed [%d]", value.getAsString().length(), valueEntry.getKey(), maxStringValueLength);
                        throw new JsonSyntaxException(message);
                    }
                    if (isTypeCastEnabled && NumberUtils.isParsable(value.getAsString())) {
                        try {
                            parseNumericValue(result, valueEntry, value);
                        } catch (RuntimeException th) {
                            result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));
                        }
                    } else {
                        result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));
                    }
                } else if (value.isBoolean()) {
                    result.add(new BooleanDataEntry(valueEntry.getKey(), value.getAsBoolean()));
                } else if (value.isNumber()) {
                    parseNumericValue(result, valueEntry, value);
                } else {
                    throw new JsonSyntaxException(CAN_T_PARSE_VALUE + value);
                }
            } else if (element.isJsonObject() || element.isJsonArray()) {
                result.add(new JsonDataEntry(valueEntry.getKey(), element.toString()));
            } else {
                throw new JsonSyntaxException(CAN_T_PARSE_VALUE + element);
            }
        }
```

### ZERO_INITIAL

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/config/WebConfig.java:30`.

```java
    public String redirect() {
        return "forward:/index.html";
    }

    @RequestMapping("/swagger-ui.html")
    public void redirectSwagger(HttpServletRequest request, HttpServletResponse response) throws IOException {
        String baseUrl = MiscUtils.constructBaseUrl(request);
        response.sendRedirect(baseUrl + "/swagger-ui/");
    }

    @RequestMapping("/swagger-ui/")
    public String redirectSwaggerIndex() throws IOException {
        return "forward:/swagger-ui/index.html";
    }

```

### UNSUPPORTED_OUTPUT

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/AuthController.java:280`.

```java
    private void logLogoutAction(HttpServletRequest request) throws ThingsboardException {
        var user = getCurrentUser();
        systemSecurityService.logLoginAction(user, new RestAuthenticationDetails(request), ActionType.LOGOUT, null);
        eventPublisher.publishEvent(new UserSessionInvalidationEvent(user.getSessionId()));
    }

}
```

### static_tenants

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/data/src/main/java/org/thingsboard/server/common/data/id/TenantId.java:27`.

```java
import java.util.UUID;

public final class TenantId extends UUIDBased implements EntityId {

    @JsonIgnore
    static final ConcurrentReferenceHashMap<UUID, TenantId> tenants = new ConcurrentReferenceHashMap<>(16, ReferenceType.SOFT);

    @JsonIgnore
    public static final TenantId SYS_TENANT_ID = TenantId.fromUUID(EntityId.NULL_UUID);

    @Serial
    private static final long serialVersionUID = 1L;

    @JsonCreator
    public static TenantId fromUUID(@JsonProperty("id") UUID id) {
        return tenants.computeIfAbsent(id, TenantId::new);
    }

    // Please, use TenantId.fromUUID instead
    // Default constructor is still available due to possible usage in extensions
    @Deprecated
    public TenantId(UUID id) {
```

### static_EMPTY

Source label: `/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/message/src/main/java/org/thingsboard/server/common/msg/queue/TbMsgCallback.java:20`.

```java
/**
 * Should be renamed to TbMsgPackContext, but this can't be changed due to backward-compatibility.
 */
public interface TbMsgCallback {

    TbMsgCallback EMPTY = new TbMsgCallback() {

        @Override
        public void onSuccess() {

        }

        @Override
        public void onFailure(RuleEngineException e) {

        }
    };

    void onSuccess();

    void onFailure(RuleEngineException e);

    default void onRateLimit(RuleEngineException e) {
        onFailure(e);
    };

    /**
```

<a id="inline-source-excerpt-metadata"></a>
### Complete original source metadata and excerpts

<details>
<summary>Full record; SHA-256 b331044ca399ab456a0716de07269f31f57be99ff528c4fcd3f0992ffd6949f5</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/final-run1-shapes/code-under-analysis.json`.

```json
[
  {
    "label": "processUplinkMsg",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/edge/rpc/EdgeGrpcSession.java",
    "first_line": 823,
    "last_line": 865,
    "sha256": "167f3175e1566d0a3a4dbcc40597803409306a11d234b7d0b511301e43e10910",
    "snippet": "    protected ListenableFuture<List<Void>> processUplinkMsg(UplinkMsg uplinkMsg) {\n        List<ListenableFuture<Void>> result = new ArrayList<>();\n        try {\n            if (uplinkMsg.getDeviceProfileUpdateMsgCount() > 0) {\n                for (DeviceProfileUpdateMsg deviceProfileUpdateMsg : uplinkMsg.getDeviceProfileUpdateMsgList()) {\n                    result.add(ctx.getDeviceProfileProcessor().processDeviceProfileMsgFromEdge(edge.getTenantId(), edge, deviceProfileUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getDeviceUpdateMsgCount() > 0) {\n                for (DeviceUpdateMsg deviceUpdateMsg : uplinkMsg.getDeviceUpdateMsgList()) {\n                    result.add(ctx.getDeviceProcessor().processDeviceMsgFromEdge(edge.getTenantId(), edge, deviceUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getDeviceCredentialsUpdateMsgCount() > 0) {\n                for (DeviceCredentialsUpdateMsg deviceCredentialsUpdateMsg : uplinkMsg.getDeviceCredentialsUpdateMsgList()) {\n                    result.add(ctx.getDeviceProcessor().processDeviceCredentialsMsgFromEdge(edge.getTenantId(), edge.getId(), deviceCredentialsUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getAssetProfileUpdateMsgCount() > 0) {\n                for (AssetProfileUpdateMsg assetProfileUpdateMsg : uplinkMsg.getAssetProfileUpdateMsgList()) {\n                    result.add(ctx.getAssetProfileProcessor().processAssetProfileMsgFromEdge(edge.getTenantId(), edge, assetProfileUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getAssetUpdateMsgCount() > 0) {\n                for (AssetUpdateMsg assetUpdateMsg : uplinkMsg.getAssetUpdateMsgList()) {\n                    result.add(ctx.getAssetProcessor().processAssetMsgFromEdge(edge.getTenantId(), edge, assetUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getRuleChainUpdateMsgCount() > 0) {\n                for (RuleChainUpdateMsg ruleChainUpdateMsg : uplinkMsg.getRuleChainUpdateMsgList()) {\n                    result.add(ctx.getRuleChainProcessor().processRuleChainMsgFromEdge(edge.getTenantId(), edge, ruleChainUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getRuleChainMetadataUpdateMsgCount() > 0) {\n                for (RuleChainMetadataUpdateMsg ruleChainMetadataUpdateMsg : uplinkMsg.getRuleChainMetadataUpdateMsgList()) {\n                    result.add(ctx.getRuleChainProcessor().processRuleChainMetadataMsgFromEdge(edge.getTenantId(), edge, ruleChainMetadataUpdateMsg));\n                }\n            }\n            if (uplinkMsg.getEntityViewUpdateMsgCount() > 0) {\n                for (EntityViewUpdateMsg entityViewUpdateMsg : uplinkMsg.getEntityViewUpdateMsgList()) {\n                    result.add(ctx.getEntityViewProcessor().processEntityViewMsgFromEdge(edge.getTenantId(), edge, entityViewUpdateMsg));\n                }\n            }"
  },
  {
    "label": "replaceByMapping",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/util/src/main/java/org/thingsboard/common/util/JacksonUtil.java",
    "first_line": 523,
    "last_line": 580,
    "sha256": "ca56fd2a1c1a0b39c8955899445f87960fe333afe2b5415e6717454537dc5421",
    "snippet": "    public static void replaceByMapping(JsonNode jsonNode, Map<String, String> mapping, Map<String, String> templateParams, BiFunction<String, JsonNode, JsonNode> processor) {\n        for (var entry : mapping.entrySet()) {\n            String expression = entry.getValue();\n            Queue<JsonPathProcessingTask> tasks = new LinkedList<>();\n            tasks.add(new JsonPathProcessingTask(entry.getKey().split(\"\\\\.\"), templateParams, jsonNode));\n            while (!tasks.isEmpty()) {\n                JsonPathProcessingTask task = tasks.poll();\n                String token = task.currentToken();\n                JsonNode node = task.getNode();\n                if (node == null) {\n                    continue;\n                }\n                if (token.equals(\"*\") || token.startsWith(\"$\")) {\n                    String variableName = token.startsWith(\"$\") ? token.substring(1) : null;\n                    if (node.isArray()) {\n                        ArrayNode childArray = (ArrayNode) node;\n                        for (JsonNode element : childArray) {\n                            tasks.add(task.next(element));\n                        }\n                    } else if (node.isObject()) {\n                        ObjectNode on = (ObjectNode) node;\n                        for (Iterator<Map.Entry<String, JsonNode>> it = on.fields(); it.hasNext(); ) {\n                            var kv = it.next();\n                            if (variableName != null) {\n                                tasks.add(task.next(kv.getValue(), variableName, kv.getKey()));\n                            } else {\n                                tasks.add(task.next(kv.getValue()));\n                            }\n                        }\n                    }\n                } else {\n                    String variableName = null;\n                    String variableValue = null;\n                    if (token.contains(\"[$\")) {\n                        variableName = StringUtils.substringBetween(token, \"[$\", \"]\");\n                        token = StringUtils.substringBefore(token, \"[$\");\n                    }\n                    if (node.has(token)) {\n                        JsonNode value = node.get(token);\n                        if (variableName != null && value.has(variableName) && value.get(variableName).isTextual()) {\n                            variableValue = value.get(variableName).asText();\n                        }\n                        if (task.isLast()) {\n                            String name = expression;\n                            for (var replacement : task.getVariables().entrySet()) {\n                                name = name.replace(\"$\" + replacement.getKey(), Strings.nullToEmpty(replacement.getValue()));\n                            }\n                            ((ObjectNode) node).set(token, processor.apply(name, value));\n                        } else {\n                            if (StringUtils.isNotEmpty(variableName)) {\n                                tasks.add(task.next(value, variableName, variableValue));\n                            } else {\n                                tasks.add(task.next(value));\n                            }\n                        }\n                    }\n                }\n            }"
  },
  {
    "label": "template_reuse_six_origins",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/cf/DefaultCalculatedFieldProcessingService.java",
    "first_line": 145,
    "last_line": 185,
    "sha256": "a48773296213dbb90b214cea279a3b5954b02988a9855476d67773a11234bc7b",
    "snippet": "    public void processResult(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {\n        if (result instanceof AlarmCalculatedFieldResult) {\n            sendMsgToRuleEngine(tenantId, entityId, callback, result.toTbMsg(entityId, cfName, cfIds));\n            return;\n        }\n        TelemetryCalculatedFieldResult telemetryResult = result instanceof TelemetryCalculatedFieldResult telemetryRes\n                ? telemetryRes : ((PropagationCalculatedFieldResult) result).getResult();\n        switch (telemetryResult.getOutputStrategy().getType()) {\n            case IMMEDIATE -> processImmediately(tenantId, entityId, cfName, result, cfIds, callback);\n            case RULE_CHAIN -> pushMsgToRuleEngine(tenantId, entityId, cfName, result, cfIds, callback);\n        }\n    }\n\n    private void processImmediately(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {\n        if (result instanceof TelemetryCalculatedFieldResult telemetryResult) {\n            saveTelemetryResult(tenantId, entityId, cfName, telemetryResult, cfIds, callback);\n            return;\n        }\n        if (result instanceof PropagationCalculatedFieldResult propagationResult) {\n            handlePropagationResults(propagationResult, callback,\n                    (entity, res, cb) -> saveTelemetryResult(tenantId, entity, cfName, res, cfIds, cb));\n            return;\n        }\n        callback.onSuccess();\n    }\n\n    private void pushMsgToRuleEngine(TenantId tenantId, EntityId entityId, String cfName, CalculatedFieldResult result, List<CalculatedFieldId> cfIds, TbCallback callback) {\n        if (result instanceof PropagationCalculatedFieldResult propagationResult) {\n            handlePropagationResults(propagationResult, callback,\n                    (entity, res, cb) -> sendMsgToRuleEngine(tenantId, entity, cb, res.toTbMsg(entity, cfName, cfIds)));\n            return;\n        }\n\n        sendMsgToRuleEngine(tenantId, entityId, callback, result.toTbMsg(entityId, cfName, cfIds));\n    }\n\n    @Override\n    public void pushMsgToLinks(CalculatedFieldTelemetryMsg msg, List<CalculatedFieldEntityCtxId> linkedCalculatedFields, TbCallback callback) {\n        Map<TopicPartitionInfo, List<CalculatedFieldEntityCtxId>> unicasts = new HashMap<>();\n        List<CalculatedFieldEntityCtxId> broadcasts = new ArrayList<>();\n        for (CalculatedFieldEntityCtxId link : linkedCalculatedFields) {"
  },
  {
    "label": "PROTECTION_ONLY",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/dao/src/main/java/org/thingsboard/server/dao/device/DeviceConnectivityServiceImpl.java",
    "first_line": 341,
    "last_line": 353,
    "sha256": "a7eeb022ca47447f16be9c77778ec62ceaa7cff2c07b939868e40af188205739",
    "snippet": "    private String getCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {\n        DeviceConnectivityInfo properties = getConnectivity(protocol);\n        String hostName = getHost(baseUrl, properties, protocol);\n        String port = StringUtils.isBlank(properties.getPort()) ? \"\" : \":\" + properties.getPort();\n        return DeviceConnectivityUtil.getCoapPublishCommand(protocol, hostName, port, deviceCredentials);\n    }\n\n    private String getDockerCoapPublishCommand(String protocol, String baseUrl, DeviceCredentials deviceCredentials) throws URISyntaxException {\n        DeviceConnectivityInfo properties = getConnectivity(protocol);\n        String host = getHost(baseUrl, properties, protocol);\n        String port = StringUtils.isBlank(properties.getPort()) ? \"\" : \":\" + properties.getPort();\n        return DeviceConnectivityUtil.getDockerCoapPublishCommand(protocol, baseUrl, host, port, deviceCredentials);\n    }"
  },
  {
    "label": "CROSS_ATOM",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/QrCodeSettingsController.java",
    "first_line": 98,
    "last_line": 117,
    "sha256": "adfcd8615f5cc8ecfc44369054f4aafcbddd89c67decfe5797e563b39ce3f6ae",
    "snippet": "    public ResponseEntity<JsonNode> getAssetLinks() {\n        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, ANDROID);\n        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;\n        if (storeInfo != null && storeInfo.getSha256CertFingerprints() != null) {\n            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(ASSET_LINKS_PATTERN, mobileApp.getPkgName(), storeInfo.getSha256CertFingerprints())));\n        } else {\n            return ResponseEntity.notFound().build();\n        }\n    }\n\n    @ApiOperation(value = \"Get associated ios applications (getAppleAppSiteAssociation)\")\n    @GetMapping(value = \"/.well-known/apple-app-site-association\")\n    public ResponseEntity<JsonNode> getAppleAppSiteAssociation() {\n        MobileApp mobileApp = qrCodeSettingService.findAppFromQrCodeSettings(TenantId.SYS_TENANT_ID, IOS);\n        StoreInfo storeInfo = mobileApp != null ? mobileApp.getStoreInfo() : null;\n        if (storeInfo != null && storeInfo.getAppId() != null) {\n            return ResponseEntity.ok(JacksonUtil.toJsonNode(String.format(APPLE_APP_SITE_ASSOCIATION_PATTERN, storeInfo.getAppId())));\n        } else {\n            return ResponseEntity.notFound().build();\n        }"
  },
  {
    "label": "UNSUPPORTED_INITIAL",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/AuthController.java",
    "first_line": 137,
    "last_line": 155,
    "sha256": "dd46a45322143141790d0d0ba925303abb5a0bbbb0390401f42aa7340151b6f3",
    "snippet": "                    \"If token is not valid, returns '409 Conflict'. \" +\n                    \"If token is expired, redirects to error page.\")\n    @GetMapping(value = \"/noauth/activate\", params = {\"activateToken\"})\n    public ResponseEntity<?> checkActivateToken(\n            @Parameter(description = \"The activate token string.\")\n            @RequestParam(value = \"activateToken\") String activateToken) {\n        UserCredentials userCredentials = userService.findUserCredentialsByActivateToken(TenantId.SYS_TENANT_ID, activateToken);\n        if (userCredentials == null) {\n            return response(HttpStatus.CONFLICT);\n        } else if (userCredentials.isActivationTokenExpired()) {\n            return redirectTo(\"/activationLinkExpired\");\n        }\n        return redirectTo(\"/login/createPassword?activateToken=\" + activateToken);\n    }\n\n    @ApiOperation(value = \"Request reset password email (requestResetPasswordByEmail)\",\n            notes = \"Request to send the reset password email if the user with specified email address is present in the database. \" +\n                    \"Always return '200 OK' status for security purposes.\")\n    @PostMapping(value = \"/noauth/resetPasswordByEmail\")"
  },
  {
    "label": "OUTPUT_TAIL_MISMATCH",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/service/install/migrate/CassandraToSqlColumn.java",
    "first_line": 103,
    "last_line": 140,
    "sha256": "a6ad1253084294ae89a5f5aed1f65ee2815172ccffb7afd9244972e9856e8652",
    "snippet": "    public String getColumnValue(Row row) {\n        if (row.isNull(index)) {\n            if (this.type == CassandraToSqlColumnType.BOOLEAN && !this.allowNullBoolean) {\n                return Boolean.toString(false);\n            } else {\n                return null;\n            }\n        } else {\n            switch (this.type) {\n                case ID:\n                    return UUIDConverter.fromTimeUUID(row.getUuid(index));\n                case DOUBLE:\n                    return Double.toString(row.getDouble(index));\n                case INTEGER:\n                    return Integer.toString(row.getInt(index));\n                case FLOAT:\n                    return Float.toString(row.getFloat(index));\n                case BIGINT:\n                    return Long.toString(row.getLong(index));\n                case BOOLEAN:\n                    return Boolean.toString(row.getBoolean(index));\n                case STRING:\n                case JSON:\n                case ENUM_TO_INT:\n                default:\n                    String value = row.getString(index);\n                    return this.replaceNullChars(value);\n            }\n        }\n    }\n\n    public void setColumnValue(PreparedStatement sqlInsertStatement, String value) throws SQLException {\n        if (value == null) {\n            sqlInsertStatement.setNull(this.sqlIndex, this.sqlType);\n        } else {\n            switch (this.type) {\n                case DOUBLE:\n                    sqlInsertStatement.setDouble(this.sqlIndex, Double.parseDouble(value));"
  },
  {
    "label": "MARK_EXCLUDED",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/transport/mqtt/src/main/java/org/thingsboard/server/transport/mqtt/HashMapObserver.java",
    "first_line": 116,
    "last_line": 141,
    "sha256": "11be0e212f6a7fb9d3253719856ad57819953979bdb35c7dd0453bfa53420ebb",
    "snippet": "    public String getActiveSessions(String unused) {\n        log.info(\"getActiveSessions()\");\n        StringBuilder content = new StringBuilder();\n        try {\n            int count = 0;\n            for (Map.Entry<UUID, SessionMetaData> entry : map.entrySet()) {\n                SessionMetaData sessionMetaData = entry.getValue();\n                if (sessionMetaData.getListener() instanceof MqttTransportHandler) {\n                    MqttTransportHandler listener = (MqttTransportHandler) sessionMetaData.getListener();\n                    if (listener.deviceSessionCtx.getChannel().channel().isActive()) {\n                        addContent(entry, ++count, content);\n                    }\n                } else {\n                    addContent(sessionMetaData.getListener().getClass(), ++count, content);\n                }\n            }\n            return content.toString();\n        } catch (Exception e) {\n            log.error(e.getMessage(), e);\n\n            throw e;\n        }\n    }\n\n    @Override\n    public String getGatewayDeviceSessionContextConnectedSessions(String unused) {"
  },
  {
    "label": "NO_FLOW_COUNTERPART",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/rule-engine/rule-engine-components/src/main/java/org/thingsboard/rule/engine/ai/Langchain4jJsonSchemaAdapter.java",
    "first_line": 77,
    "last_line": 95,
    "sha256": "69f670c9a49c0bad4c4768d00f1ea67c6c015639f78972a473fa092b33ea26f6",
    "snippet": "    private static JsonEnumSchema.Builder parseEnum(JsonNode enumSchema) {\n        var builder = new JsonEnumSchema.Builder();\n\n        List<String> enumValues = new ArrayList<>();\n        for (JsonNode element : enumSchema.get(\"enum\")) {\n            if (!element.isTextual()) {\n                throw new IllegalArgumentException(\"Expected each 'enum' element to be a string, but found: \" + element.getNodeType());\n            }\n            enumValues.add(element.textValue());\n        }\n        builder.enumValues(enumValues);\n\n        return builder;\n    }\n\n    private static JsonObjectSchema.Builder parseObject(JsonNode objectSchema) {\n        var builder = new JsonObjectSchema.Builder();\n\n        JsonNode propertiesNode = objectSchema.get(\"properties\");"
  },
  {
    "label": "OUTPUT_BASE_MISMATCH",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/proto/src/main/java/org/thingsboard/server/common/adaptor/JsonConverter.java",
    "first_line": 548,
    "last_line": 580,
    "sha256": "29a62dd9f4c994ca760a123274188b39ab73d131548f3b27f3777e9626a1f249",
    "snippet": "    private static List<KvEntry> parseValues(JsonObject valuesObject) {\n        List<KvEntry> result = new ArrayList<>();\n        for (Entry<String, JsonElement> valueEntry : valuesObject.entrySet()) {\n            JsonElement element = valueEntry.getValue();\n            if (element.isJsonPrimitive()) {\n                JsonPrimitive value = element.getAsJsonPrimitive();\n                if (value.isString()) {\n                    if (maxStringValueLength > 0 && value.getAsString().length() > maxStringValueLength) {\n                        String message = String.format(\"String value length [%d] for key [%s] is greater than maximum allowed [%d]\", value.getAsString().length(), valueEntry.getKey(), maxStringValueLength);\n                        throw new JsonSyntaxException(message);\n                    }\n                    if (isTypeCastEnabled && NumberUtils.isParsable(value.getAsString())) {\n                        try {\n                            parseNumericValue(result, valueEntry, value);\n                        } catch (RuntimeException th) {\n                            result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));\n                        }\n                    } else {\n                        result.add(new StringDataEntry(valueEntry.getKey(), value.getAsString()));\n                    }\n                } else if (value.isBoolean()) {\n                    result.add(new BooleanDataEntry(valueEntry.getKey(), value.getAsBoolean()));\n                } else if (value.isNumber()) {\n                    parseNumericValue(result, valueEntry, value);\n                } else {\n                    throw new JsonSyntaxException(CAN_T_PARSE_VALUE + value);\n                }\n            } else if (element.isJsonObject() || element.isJsonArray()) {\n                result.add(new JsonDataEntry(valueEntry.getKey(), element.toString()));\n            } else {\n                throw new JsonSyntaxException(CAN_T_PARSE_VALUE + element);\n            }\n        }"
  },
  {
    "label": "ZERO_INITIAL",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/config/WebConfig.java",
    "first_line": 30,
    "last_line": 44,
    "sha256": "676a498d30cebb88b253ea76972cc3eb9b977ec1acdb841898eb53e4831b2763",
    "snippet": "    public String redirect() {\n        return \"forward:/index.html\";\n    }\n\n    @RequestMapping(\"/swagger-ui.html\")\n    public void redirectSwagger(HttpServletRequest request, HttpServletResponse response) throws IOException {\n        String baseUrl = MiscUtils.constructBaseUrl(request);\n        response.sendRedirect(baseUrl + \"/swagger-ui/\");\n    }\n\n    @RequestMapping(\"/swagger-ui/\")\n    public String redirectSwaggerIndex() throws IOException {\n        return \"forward:/swagger-ui/index.html\";\n    }\n"
  },
  {
    "label": "UNSUPPORTED_OUTPUT",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/application/src/main/java/org/thingsboard/server/controller/AuthController.java",
    "first_line": 280,
    "last_line": 286,
    "sha256": "dd46a45322143141790d0d0ba925303abb5a0bbbb0390401f42aa7340151b6f3",
    "snippet": "    private void logLogoutAction(HttpServletRequest request) throws ThingsboardException {\n        var user = getCurrentUser();\n        systemSecurityService.logLoginAction(user, new RestAuthenticationDetails(request), ActionType.LOGOUT, null);\n        eventPublisher.publishEvent(new UserSessionInvalidationEvent(user.getSessionId()));\n    }\n\n}"
  },
  {
    "label": "static_tenants",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/data/src/main/java/org/thingsboard/server/common/data/id/TenantId.java",
    "first_line": 27,
    "last_line": 48,
    "sha256": "2a97e1af2989da3fcc1fc8ab8537e72bda8a315f198d11aa4800824e9d42ab5e",
    "snippet": "import java.util.UUID;\n\npublic final class TenantId extends UUIDBased implements EntityId {\n\n    @JsonIgnore\n    static final ConcurrentReferenceHashMap<UUID, TenantId> tenants = new ConcurrentReferenceHashMap<>(16, ReferenceType.SOFT);\n\n    @JsonIgnore\n    public static final TenantId SYS_TENANT_ID = TenantId.fromUUID(EntityId.NULL_UUID);\n\n    @Serial\n    private static final long serialVersionUID = 1L;\n\n    @JsonCreator\n    public static TenantId fromUUID(@JsonProperty(\"id\") UUID id) {\n        return tenants.computeIfAbsent(id, TenantId::new);\n    }\n\n    // Please, use TenantId.fromUUID instead\n    // Default constructor is still available due to possible usage in extensions\n    @Deprecated\n    public TenantId(UUID id) {"
  },
  {
    "label": "static_EMPTY",
    "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/repo/common/message/src/main/java/org/thingsboard/server/common/msg/queue/TbMsgCallback.java",
    "first_line": 20,
    "last_line": 46,
    "sha256": "4fd7cedb319b9f271171b93b8ac2b96bef7da8a3baa4f4497d36b80a355f15a7",
    "snippet": "/**\n * Should be renamed to TbMsgPackContext, but this can't be changed due to backward-compatibility.\n */\npublic interface TbMsgCallback {\n\n    TbMsgCallback EMPTY = new TbMsgCallback() {\n\n        @Override\n        public void onSuccess() {\n\n        }\n\n        @Override\n        public void onFailure(RuleEngineException e) {\n\n        }\n    };\n\n    void onSuccess();\n\n    void onFailure(RuleEngineException e);\n\n    default void onRateLimit(RuleEngineException e) {\n        onFailure(e);\n    };\n\n    /**"
  }
]
```

</details>

<a id="inline-source-trace"></a>
## Source/model ANY trace and limits

The source-valid regex route and four actual AP controls establish a possible field-cut derivation of root ANY. They do not identify the first producer for the sampled row or the dominant protected static matrix.

The driver has `DefaultRow.data : List<ByteBuffer>` and reads it through `List.get`. String/UUID getters decode this buffer. Primitive getters have a fast decoder and a generic fallback. Ordinary library bodies are outside this campaign's unit boundary. External getter fallback is STAR-to-STAR. The bytecode below is therefore not claimed as the analyzer's actual ANY producer.

<a id="inline-source-trace-record"></a>
### Complete source trace, source hashes and origin limit

<details>
<summary>Full record; SHA-256 0c17cc4574b9b005f9a0cbe78e1d80c429cd3eeafbb64e9729cd27026dff8fd4</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/report.json`.

```json
{
  "state": "SOURCE_TRACE_COMPLETE_WITH_ORIGIN_LIMIT",
  "created_utc": "2026-10-26T23:02:25.035490+00:00",
  "latest_reached": "run-1",
  "latest_completed": "run-1",
  "latest_accepted_forward": "run-1",
  "source": {
    "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
    "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
    "core_rules_patch_empty": true,
    "source_file_sha256": {
      "core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/JIRTaintAnalyzer.kt": "393cb3f9d7c81434613bfaf0d0eb348425178e56aaabba19899a4e06a6c85099",
      "core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisContext.kt": "4906e43d69640521cb7a51aa355802f542ab30a2e7cc987dba19bda354d8319e",
      "core/opentaint-jvm-sast-project/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectClasses.kt": "5724d6d3a881efa8b18f5a2ceb8fd0259ef13fbdbd5df45644c15241a0aeb5dd",
      "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRCallResolver.kt": "e5da7c93e7ceb921d52c07c554e0e75569b423d1d47bae603997bf803f695328",
      "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/analysis/JIRMethodGetDefault.kt": "b101082d1f278b1e72363ed42a58436b8c05161e6fff81f4443970c692279486",
      "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRCallPlanBuilder.kt": "d40274e6f306c1eab9e55e80a6ebab05e4ed6f0416df4659584a845573f6c1f7",
      "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRRuleForms.kt": "7370b426ba4edb241f6b0c39bf27854214a91f4a5ee81f254dde5862d7faf285",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/EdgeApplication.kt": "7c3bbdb0ea444fe50c971213907661da1280a18682f16a1db0dd23ee29bcf792",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Limit.kt": "4a03eed47d6c2f1362219fbdb0e8d40895194dd2a7f090ed93c822054f6de45d",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Groups.kt": "18a7cb13e2a90bec933c22ae5658af499d5d0844a3f702439ae5193c258ce050",
      "core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt": "fc75981b3378c781f67d130327174e8888adc40f64a0a69592a99da93e1f722a",
      "core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/DataFlowApproximationLoader.kt": "acbd8d1d21b46d862652eb421fdbb83856d4ca3f3210cd30b588287f76ffc0b8",
      "core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/MethodTaintConfigurationResolver.kt": "1836fd487f33cfbe4508b49470e4a7c928d226159b063d44dec97f00c0aa63e5",
      "core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/Provider.kt": "a7bf5766f0915108a986d91ccd34ef8d1e6f26ac8fb05b7d029dd6fca168d71a",
      "model/java/config/stdlib/java-util.yaml": "1ed925590e148a36acf11affcd281838f3cb4ce8358556d1ce08b21254e119c6",
      "model/java/config/stdlib/java-util-regex.yaml": "78b484e42661f44b933dfbfc9477b8b24a4445a374f6e0ac9d30d9a84b825139",
      "model/java/accumulated-fields.yaml": "06ae5b32e1648a6ac7f0827acf1a6fb21f4dd36387a535fb025e3b0b3e95a433",
      "core/src/main/kotlin/org/opentaint/jvm/sast/project/JirProjectAnalyzer.kt": "7efb88796543d4a3b9102ab716b113d8a695a6e6023f350d13e1d3b37cdf8ae6",
      "core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/TaintConfiguration.kt": "b69f46372081c9f2e79f5edeab1bee4ea0207bb128428f2f2bdcbac75be7105f",
      "core/opentaint-jvm-sast-dataflow/build.gradle.kts": "71ff8fc67054da65d46a7f8d5ef55da2b38f369797a5b426327717f722c75bca"
    },
    "project_file_sha256": {
      "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/sources/application/src/main/java/org/thingsboard/server/service/install/migrate/CassandraToSqlColumn.java": "a6ad1253084294ae89a5f5aed1f65ee2815172ccffb7afd9244972e9856e8652",
      "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/sources/common/data/src/main/java/org/thingsboard/server/common/data/UUIDConverter.java": "83b5712f26a6e97a706dec3f695cba3bbf70dec77cede8a5edb1922e86c4f6e3",
      "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/dependencies/java-driver-core-4.17.0.jar": "445e1c91e3f7512c1c0686700ec1e3d77d89131a2711ce66062909a7d88e8cd3",
      "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
      "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/classes/c8_classes_8/org/thingsboard/server/service/install/migrate/CassandraToSqlColumn.class": "53aee6aab7826709887bce31a9e1ea08b148f46a93e08d51883bf36d3e4c049b"
    },
    "timed_manifest": {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/candidate-final-results/thingsboard/bidi/manifest.json",
      "sha256": "6f88605a3acfa3f07ba6a6691588af253cb15b14eef6fb60fab963855d0514bc",
      "default_get_disable_option_absent": true,
      "custom_approximation_option_absent": true
    }
  },
  "artifacts": {
    "validation/baseline-shape-probe/cassandra-producer-trace/DoubleCodec.javap.txt": "8bd104e4571aca4c990713acc4771e461cf385f396b69e724d029926f86d83b2",
    "validation/baseline-shape-probe/cassandra-producer-trace/GettableByIndex.javap.txt": "165fca1aa0ebeee48f001dfc9f4c426dd3e55de4e6b3f777b24bbe8456d5e51c",
    "validation/baseline-shape-probe/cassandra-producer-trace/AccessibleByIndex.javap.txt": "943d198030a9717f049b429ffd5648ea6d41c790c9a6cc59802dc71f3231dc7b",
    "validation/baseline-shape-probe/cassandra-producer-trace/StringCodec.javap.txt": "c293a18f5202896d2a1965956c18a18f46925075edf049e98c963ff57fefa0a2",
    "validation/baseline-shape-probe/cassandra-producer-trace/Row.javap.txt": "1754495db17ddc4f2cfa8a1739afbb190db848a6bb8f9c61686737e69745c272",
    "validation/baseline-shape-probe/cassandra-producer-trace/UuidCodec.javap.txt": "69df215b72ebd1b98a4cc99dd579b4a540f337c187f994175bc0a47700f902f7",
    "validation/baseline-shape-probe/cassandra-producer-trace/DefaultRow.javap.txt": "1dce4062221711205685a5347d25b1f8ed5bf38d10f897d1b2e5c26d72b6beb2",
    "validation/baseline-shape-probe/cassandra-producer-trace/IntCodec.javap.txt": "be60a06de3d136c9a6881fe69f9a870496374b7cea7f91b605a94b4f0357cd22",
    "validation/baseline-shape-probe/cassandra-producer-trace/CassandraToSqlColumn.javap.txt": "d0b0ae99cc92fe5e5f3bcd1c8931a2d968350e0b08af8acb75b5792fac715391"
  },
  "model_candidates": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/model-candidates.json",
  "model_candidates_sha256": "7699d60eb8c70a04689b8f435c386372b859d00680e34803b5c78ce7e9f6bf95",
  "current_run1_census": {
    "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes/run1-shapes.json",
    "sha256": "806e5bba1c968f9c6861d94a608e1688c42829fc020ca44f81e9b74cd818d0c9",
    "source_revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
    "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
    "matching_method_counts": {
      "raw": {
        "target_summary_memberships": {
          "FLOW.method.org.thingsboard.server.common.data.UUIDConverter#fromTimeUUID(java.util.UUID) [{}]": 3,
          "FLOW.method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]": 3,
          "method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]": 18,
          "FLOW.method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#replaceNullChars(java.lang.String) [{}]": 5
        },
        "driver_declaring_method_counters": {}
      },
      "selected": {
        "target_summary_memberships": {
          "FLOW.method.org.thingsboard.server.common.data.UUIDConverter#fromTimeUUID(java.util.UUID) [{}]": 3,
          "FLOW.method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]": 3,
          "method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#getColumnValue(com.datastax.oss.driver.api.core.cql.Row) [{}]": 18,
          "FLOW.method.org.thingsboard.server.service.install.migrate.CassandraToSqlColumn#replaceNullChars(java.lang.String) [{}]": 5
        },
        "driver_declaring_method_counters": {}
      }
    }
  },
  "compiled_default_approximation_classes": {
    "jar": "/drive-testcomp/opentaint-go-rules/opentaint-w3/core/opentaint-jvm-sast-dataflow/build/libs/opentaint-jvm-sast-dataflow.jar",
    "jar_sha256": "d16908b8c02c073c8026151978ccdde4f3329083ea0fbd5554ea7656b2ac8edd",
    "members": {
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/kotlin/BuildersBuildersCommon.class": "5133598321df1dbeeb7c55b051fb3419309d90b77413362ad5c1f8763e3e73bd",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/kotlin/BuildersBuilders.class": "8b18a163ee9f5add9fa0369b065cee0eb26070a38279ae4b5a41460943f99b6d",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/kotlin/Builders.class": "3caeea73b29d474e402f778fda5ff1d5f3e48833a4932de4c52948e31886dde7",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/Thread.class": "f72056b8432c8caa828c0bcb372140006a2d581cdc64f65c74600748e539c222",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/Optional.class": "54cab6327a2b38409831c1b105a0cf6189d09c42079d679029e38c802f5ff243",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/CompletableFuture.class": "b8784229934947411d0f9ce402943d145bf68bc6032b1988ef416b6cea70d991",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/Stream.class": "e0481f0a9f5c1a8b78cad4065ab5d07ca86b0f3b5f7991f0efcba7739a39408d",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/CompletionStage.class": "2e40d587c601cd13f41e81dd5347a3d4fce7114a36dc708ed1e47b7f2f552f01",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/ExecutorService.class": "73ab1290e5af64964bf2e846eb7f8ceb8860d8f479fc4bc335cb1269dec82781",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/stdlib/Executor.class": "9104ce6b7e4879c8b5d34db5f0463b69e8fee66768ef6933ae1c19b83b676c15",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/OpentaintNdUtil.class": "51ee1330826551eb2ae614468032c4be54da23bf8440cd4b6f453040e14f0ec9",
      "opentaint-dataflow-approximations/org/opentaint/jvm/dataflow/approximations/ArgumentTypeContext.class": "ed9be695299b4426862b219e970138b3286566d2f89d2a19a05c0d38b7840904"
    },
    "driver_refs_absent": true,
    "scope": "Current built application artifact; jar not separately pinned by historical runner manifest. Source/default setup is primary correspondence."
  },
  "physical_driver_facts": [
    "DefaultRow implements Row; private final java.util.List<java.nio.ByteBuffer> data.",
    "DefaultRow.getBytesUnsafe(int) executes getfield data, List.get(index), ByteBuffer cast, return.",
    "String/UUID getter bodies use get(index,Class), codec selection, then get(index,TypeCodec); the latter calls TypeCodec.decode(getBytesUnsafe(index),protocolVersion()).",
    "Double/int/float/long/boolean getter bodies each have a Primitive*Codec.decodePrimitive(getBytesUnsafe(index),protocolVersion()) fast branch and generic get(index,TypeCodec) fallback.",
    "isNull(index) also reads getBytesUnsafe, but null/default/error returns do not represent decoded payload flow."
  ],
  "analyzer_facts": [
    "Fixed model lists java-driver-core-4.17.0.jar as dependency, not a module class location. ProjectAnalysisContext loads dependencies as LIB; ProjectClasses recognizes configured module locations only.",
    "PackageUnitResolver maps nonproject library methods to UnknownUnit unless the method is a bytecode approximation or lambda. JIRCallResolver excludes unknown library bodies; JIRCallPlanBuilder uses unresolved stages for them.",
    "The fixed runner has default-get model enabled (disable flag defaults false and was absent in the recorded invocation). Unknown nonstatic get* calls receive synthetic CopyAllMarks(This,Result), plus an element result for Object/array returns. JIRRuleForms lowers ordinary This/Result CopyAllMarks to STAR -> STAR.",
    "No Datastax/Cassandra-named function model or pattern-valued package matcher was found in serialized model/java/config. No built-in dataflow approximation source targets Row/DefaultRow/GettableByIndex or TypeCodec. No project source declaring an implements Row / extends DefaultRow type was found; this source scan is not a replacement for the recorded dispatch list.",
    "The current joined census has no summary counter whose declaring method starts com.datastax.; it does contain getColumnValue, replaceNullChars and UUIDConverter summaries. Counter absence is supporting evidence, not an execution history."
  ],
  "confirmed_semantic_opportunities": [
    "A field read from an abstract FLOW ancestor produces DEMAND ANY in EdgeApplication.flow (prefix callback). Thus IF DefaultRow were analyzed, its data read could create ANY before the second List/Element step. That is a counterfactual under the current library boundary.",
    "Existing Pattern.matcher model copies its CharSequence argument to Matcher.group.String.content (two counted fields). Limit1 cuts this to Matcher.group/[any] DEMAND. A separate Matcher.replaceAll model with signature return:String reads this.Matcher.group and copies to result, which admits String overload and produces result/[any] DEMAND at the root. This is a valid source/model route in the analyzed replaceNullChars helper. It establishes an available root-ANY derivation, not the historical first output/offer order for the saved sample.",
    "FlowGroup.subtractSubsumed admits per-layer ordinary FLOW ANY as covering a later same-output-path FLOW STAR when mark exclusions permit. Concrete replacement requires matching tail kinds. Thus an early ANY route can discard a later STAR FLOW route while a STAR marked relation remains. The saved final owner is compatible with that sequence, but no offer-order history was captured."
  ],
  "origin_limit": "The exact switch branch, first actual ANY output and offer order that produced this particular retained summary are NOT proved by the source/exit sample. The shared DefaultRow storage path is verified; it must not be presented as the actual analyzer origin because library bodies are outside the current unit boundary. A replay of saved AP values proves only application/coverage behavior. A positive bound call-form/summary trace or a scoped isolated actual call-model fixture would be needed to close origin attribution. No current Thingsboard rerun, new analyzer or tracked source change was performed.",
  "model_scan_control": {
    "parsed_files": 164,
    "parsed_function_items": 7626,
    "candidate_count": 12,
    "direct_driver_model_count": 0,
    "pattern_package_count": 0
  },
  "frozen_baseline_lane_unchanged": {
    "tools/run_baseline_shape_campaign.py": "ee62a87debdde99b665ef9ce5d126b77d6714d3c7d55e7ad5138a217225901f9",
    "tools/test_baseline_shape_probe.py": "6eedc2d5cece014a1459ea586c8f37762f414f2342da5514716eaf1f87d5c14a",
    "validation/baseline-shape-probe/prepared.json": "069e38697f903c7353177dacca23045f5641461941b39745bdfc5ef6dd20dc81"
  }
}
```

</details>

<a id="inline-model-rules"></a>
### Complete relevant serialized model rules and scan controls

<details>
<summary>Full record; SHA-256 7699d60eb8c70a04689b8f435c386372b859d00680e34803b5c78ce7e9f6bf95</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/model-candidates.json`.

```json
{
  "scope": "Serialized candidate models. Signature/override predicates and runtime method resolution still apply.",
  "parsed_files": 164,
  "parsed_function_items": 7626,
  "candidates": [
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-lang.yaml",
      "item_path": [
        "passThrough",
        31
      ],
      "model": {
        "function": "java.lang.String#substring",
        "signature": "(int) java.lang.String",
        "copy": [
          {
            "from": "this",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-lang.yaml",
      "item_path": [
        "passThrough",
        84
      ],
      "model": {
        "function": "java.lang.String#substring",
        "signature": "(int, int) java.lang.String",
        "copy": [
          {
            "from": "this",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-lang.yaml",
      "item_path": [
        "passThrough",
        184
      ],
      "model": {
        "function": "java.lang.Object#toString",
        "signature": "() java.lang.String",
        "copy": [
          {
            "from": "this",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        13
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": "(*) java.lang.String",
        "copy": [
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#input#java.lang.CharSequence"
            ],
            "to": [
              "result",
              ".java.lang.String#content#java.lang.CharSequence"
            ]
          },
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#group#java.lang.String",
              ".java.lang.String#content#java.lang.CharSequence"
            ],
            "to": [
              "result",
              ".java.lang.String#content#java.lang.CharSequence"
            ]
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        18
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": "(java.util.function.Function) java.lang.String",
        "taintCopyOnly": true,
        "copy": [
          {
            "from": "arg(0)",
            "to": "result"
          },
          {
            "from": "this",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        21
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": {
          "return": "java.lang.String"
        },
        "copy": [
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#group#java.lang.String"
            ],
            "to": "result"
          },
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#pattern#java.util.regex.Pattern",
              ".java.util.regex.Pattern#regex#java.lang.String"
            ],
            "to": "result"
          },
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#group#java.lang.String"
            ],
            "to": "result"
          },
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#pattern#java.util.regex.Pattern",
              ".java.util.regex.Pattern#regex#java.lang.String"
            ],
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        35
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": "(java.util.function.Function) java.lang.String",
        "copy": [
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#<rule-storage>#java.lang.Object"
            ],
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        39
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": "(java.lang.String) java.lang.String",
        "copy": [
          {
            "from": "arg(0)",
            "to": "result"
          },
          {
            "from": [
              "this",
              ".java.util.regex.Matcher#<rule-storage>#java.lang.Object"
            ],
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        42
      ],
      "model": {
        "function": "java.util.regex.Pattern#matcher",
        "signature": "(java.lang.CharSequence) java.util.regex.Matcher",
        "taintCopyOnly": true,
        "copy": [
          {
            "from": "arg(0)",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        54
      ],
      "model": {
        "function": "java.util.regex.Pattern#matcher",
        "signature": {
          "params": [
            {
              "index": 0,
              "type": "java.lang.CharSequence"
            }
          ],
          "return": "java.util.regex.Matcher"
        },
        "copy": [
          {
            "from": "arg(0)",
            "to": [
              "result",
              ".java.util.regex.Matcher#input#java.lang.CharSequence"
            ]
          },
          {
            "from": "arg(0)",
            "to": [
              "result",
              ".java.util.regex.Matcher#group#java.lang.String",
              ".java.lang.String#content#java.lang.CharSequence"
            ]
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util-regex.yaml",
      "item_path": [
        "passThrough",
        67
      ],
      "model": {
        "function": "java.util.regex.Matcher#replaceAll",
        "signature": "(java.lang.String) java.lang.String",
        "taintCopyOnly": true,
        "copy": [
          {
            "from": "this",
            "to": "result"
          }
        ]
      }
    },
    {
      "file": "/drive-testcomp/opentaint-go-rules/opentaint-w3/model/java/config/stdlib/java-util.yaml",
      "item_path": [
        "passThrough",
        294
      ],
      "model": {
        "function": "java.util.List#get",
        "signature": "(int) java.lang.Object",
        "copy": [
          {
            "from": [
              "this",
              ".java.lang.Iterable#Element#java.lang.Object"
            ],
            "to": "result"
          }
        ]
      }
    }
  ],
  "direct_driver_models": [],
  "pattern_package_models": [],
  "model_inventory_sha256": "63fea35e2eb1c104769aad83a4658e173445a3ad6500e0cd328db7d08ab2367f"
}
```

</details>

<a id="inline-bytecode-gettablebyindex"></a>
### Recorded GettableByIndex bytecode

<details>
<summary>Full record; SHA-256 165fca1aa0ebeee48f001dfc9f4c426dd3e55de4e6b3f777b24bbe8456d5e51c</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/GettableByIndex.javap.txt`.

```text
Compiled from "GettableByIndex.java"
public interface com.datastax.oss.driver.api.core.data.GettableByIndex extends com.datastax.oss.driver.api.core.data.AccessibleByIndex {
  public abstract java.nio.ByteBuffer getBytesUnsafe(int);

  public default boolean isNull(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
       7: ifnonnull     14
      10: iconst_1
      11: goto          15
      14: iconst_0
      15: ireturn

  public default <ValueT> ValueT get(int, com.datastax.oss.driver.api.core.type.codec.TypeCodec<ValueT>);
    Code:
       0: aload_2
       1: aload_0
       2: iload_1
       3: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
       8: aload_0
       9: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      14: invokeinterface #3,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/TypeCodec.decode:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)Ljava/lang/Object;
      19: areturn

  public default <ValueT> ValueT get(int, com.datastax.oss.driver.api.core.type.reflect.GenericType<ValueT>);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_3
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_3
      15: aload_2
      16: invokeinterface #6,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Lcom/datastax/oss/driver/api/core/type/reflect/GenericType;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      21: astore        4
      23: aload_0
      24: iload_1
      25: aload         4
      27: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      32: areturn

  public default <ValueT> ValueT get(int, java.lang.Class<ValueT>);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_3
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_3
      15: aload_2
      16: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      21: astore        4
      23: aload_0
      24: iload_1
      25: aload         4
      27: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      32: areturn

  public default java.lang.Object getObject(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: invokeinterface #9,  2            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      20: astore_3
      21: aload_3
      22: aload_0
      23: iload_1
      24: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      29: aload_0
      30: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      35: invokeinterface #3,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/TypeCodec.decode:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)Ljava/lang/Object;
      40: areturn

  public default boolean getBoolean(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #10                 // class java/lang/Boolean
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #11                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveBooleanCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #11                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveBooleanCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #12,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveBooleanCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)Z
      52: ireturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #10                 // class java/lang/Boolean
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: iconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #13                 // Method java/lang/Boolean.booleanValue:()Z
      80: ireturn

  public default boolean getBool(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #14,  2           // InterfaceMethod getBoolean:(I)Z
       7: ireturn

  public default byte getByte(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #15                 // class java/lang/Byte
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #16                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveByteCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #16                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveByteCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #17,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveByteCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)B
      52: ireturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #15                 // class java/lang/Byte
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: iconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #18                 // Method java/lang/Byte.byteValue:()B
      80: ireturn

  public default double getDouble(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #19                 // class java/lang/Double
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #20                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveDoubleCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #20                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveDoubleCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #21,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveDoubleCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)D
      52: dreturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #19                 // class java/lang/Double
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: dconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #22                 // Method java/lang/Double.doubleValue:()D
      80: dreturn

  public default float getFloat(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #23                 // class java/lang/Float
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #24                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveFloatCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #24                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveFloatCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #25,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveFloatCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)F
      52: freturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #23                 // class java/lang/Float
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: fconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #26                 // Method java/lang/Float.floatValue:()F
      80: freturn

  public default int getInt(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #27                 // class java/lang/Integer
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #28                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveIntCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #28                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveIntCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #29,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveIntCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)I
      52: ireturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #27                 // class java/lang/Integer
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: iconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #30                 // Method java/lang/Integer.intValue:()I
      80: ireturn

  public default long getLong(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #31                 // class java/lang/Long
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #32                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveLongCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #32                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveLongCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #33,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveLongCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)J
      52: lreturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #31                 // class java/lang/Long
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: lconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #34                 // Method java/lang/Long.longValue:()J
      80: lreturn

  public default short getShort(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_0
       9: invokeinterface #5,  1            // InterfaceMethod codecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
      14: aload_2
      15: ldc           #35                 // class java/lang/Short
      17: invokeinterface #8,  3            // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry.codecFor:(Lcom/datastax/oss/driver/api/core/type/DataType;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/codec/TypeCodec;
      22: astore_3
      23: aload_3
      24: instanceof    #36                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveShortCodec
      27: ifeq          53
      30: aload_3
      31: checkcast     #36                 // class com/datastax/oss/driver/api/core/type/codec/PrimitiveShortCodec
      34: aload_0
      35: iload_1
      36: invokeinterface #1,  2            // InterfaceMethod getBytesUnsafe:(I)Ljava/nio/ByteBuffer;
      41: aload_0
      42: invokeinterface #2,  1            // InterfaceMethod protocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
      47: invokeinterface #37,  3           // InterfaceMethod com/datastax/oss/driver/api/core/type/codec/PrimitiveShortCodec.decodePrimitive:(Ljava/nio/ByteBuffer;Lcom/datastax/oss/driver/api/core/ProtocolVersion;)S
      52: ireturn
      53: aload_0
      54: iload_1
      55: aload_3
      56: invokeinterface #7,  3            // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/codec/TypeCodec;)Ljava/lang/Object;
      61: checkcast     #35                 // class java/lang/Short
      64: astore        4
      66: aload         4
      68: ifnonnull     75
      71: iconst_0
      72: goto          80
      75: aload         4
      77: invokevirtual #38                 // Method java/lang/Short.shortValue:()S
      80: ireturn

  public default java.time.Instant getInstant(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #39                 // class java/time/Instant
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #39                 // class java/time/Instant
      12: areturn

  public default java.time.LocalDate getLocalDate(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #41                 // class java/time/LocalDate
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #41                 // class java/time/LocalDate
      12: areturn

  public default java.time.LocalTime getLocalTime(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #42                 // class java/time/LocalTime
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #42                 // class java/time/LocalTime
      12: areturn

  public default java.nio.ByteBuffer getByteBuffer(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #43                 // class java/nio/ByteBuffer
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #43                 // class java/nio/ByteBuffer
      12: areturn

  public default java.lang.String getString(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #44                 // class java/lang/String
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #44                 // class java/lang/String
      12: areturn

  public default java.math.BigInteger getBigInteger(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #45                 // class java/math/BigInteger
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #45                 // class java/math/BigInteger
      12: areturn

  public default java.math.BigDecimal getBigDecimal(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #46                 // class java/math/BigDecimal
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #46                 // class java/math/BigDecimal
      12: areturn

  public default java.util.UUID getUuid(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #47                 // class java/util/UUID
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #47                 // class java/util/UUID
      12: areturn

  public default java.net.InetAddress getInetAddress(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #48                 // class java/net/InetAddress
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #48                 // class java/net/InetAddress
      12: areturn

  public default com.datastax.oss.driver.api.core.data.CqlDuration getCqlDuration(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #49                 // class com/datastax/oss/driver/api/core/data/CqlDuration
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #49                 // class com/datastax/oss/driver/api/core/data/CqlDuration
      12: areturn

  public default <ElementT extends java.lang.Number> com.datastax.oss.driver.api.core.data.CqlVector<ElementT> getVector(int, java.lang.Class<ElementT>);
    Code:
       0: aload_0
       1: iload_1
       2: aload_2
       3: invokestatic  #50                 // Method com/datastax/oss/driver/api/core/type/reflect/GenericType.vectorOf:(Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/reflect/GenericType;
       6: invokeinterface #51,  3           // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/reflect/GenericType;)Ljava/lang/Object;
      11: checkcast     #52                 // class com/datastax/oss/driver/api/core/data/CqlVector
      14: areturn

  public default com.datastax.oss.driver.api.core.metadata.token.Token getToken(int);
    Code:
       0: aload_0
       1: iload_1
       2: invokeinterface #4,  2            // InterfaceMethod getType:(I)Lcom/datastax/oss/driver/api/core/type/DataType;
       7: astore_2
       8: aload_2
       9: getstatic     #53                 // Field com/datastax/oss/driver/api/core/type/DataTypes.BIGINT:Lcom/datastax/oss/driver/api/core/type/DataType;
      12: invokevirtual #54                 // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
      15: ifeq          47
      18: aload_0
      19: iload_1
      20: invokeinterface #55,  2           // InterfaceMethod isNull:(I)Z
      25: ifeq          32
      28: aconst_null
      29: goto          46
      32: new           #56                 // class com/datastax/oss/driver/internal/core/metadata/token/Murmur3Token
      35: dup
      36: aload_0
      37: iload_1
      38: invokeinterface #57,  2           // InterfaceMethod getLong:(I)J
      43: invokespecial #58                 // Method com/datastax/oss/driver/internal/core/metadata/token/Murmur3Token."<init>":(J)V
      46: areturn
      47: aload_2
      48: getstatic     #59                 // Field com/datastax/oss/driver/api/core/type/DataTypes.BLOB:Lcom/datastax/oss/driver/api/core/type/DataType;
      51: invokevirtual #54                 // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
      54: ifeq          86
      57: aload_0
      58: iload_1
      59: invokeinterface #55,  2           // InterfaceMethod isNull:(I)Z
      64: ifeq          71
      67: aconst_null
      68: goto          85
      71: new           #60                 // class com/datastax/oss/driver/internal/core/metadata/token/ByteOrderedToken
      74: dup
      75: aload_0
      76: iload_1
      77: invokeinterface #61,  2           // InterfaceMethod getByteBuffer:(I)Ljava/nio/ByteBuffer;
      82: invokespecial #62                 // Method com/datastax/oss/driver/internal/core/metadata/token/ByteOrderedToken."<init>":(Ljava/nio/ByteBuffer;)V
      85: areturn
      86: aload_2
      87: getstatic     #63                 // Field com/datastax/oss/driver/api/core/type/DataTypes.VARINT:Lcom/datastax/oss/driver/api/core/type/DataType;
      90: invokevirtual #54                 // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
      93: ifeq          125
      96: aload_0
      97: iload_1
      98: invokeinterface #55,  2           // InterfaceMethod isNull:(I)Z
     103: ifeq          110
     106: aconst_null
     107: goto          124
     110: new           #64                 // class com/datastax/oss/driver/internal/core/metadata/token/RandomToken
     113: dup
     114: aload_0
     115: iload_1
     116: invokeinterface #65,  2           // InterfaceMethod getBigInteger:(I)Ljava/math/BigInteger;
     121: invokespecial #66                 // Method com/datastax/oss/driver/internal/core/metadata/token/RandomToken."<init>":(Ljava/math/BigInteger;)V
     124: areturn
     125: new           #67                 // class java/lang/IllegalArgumentException
     128: dup
     129: new           #68                 // class java/lang/StringBuilder
     132: dup
     133: invokespecial #69                 // Method java/lang/StringBuilder."<init>":()V
     136: ldc           #70                 // String Can\'t convert CQL type
     138: invokevirtual #71                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
     141: aload_2
     142: invokevirtual #72                 // Method java/lang/StringBuilder.append:(Ljava/lang/Object;)Ljava/lang/StringBuilder;
     145: ldc           #73                 // String  into a token
     147: invokevirtual #71                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
     150: invokevirtual #74                 // Method java/lang/StringBuilder.toString:()Ljava/lang/String;
     153: invokespecial #75                 // Method java/lang/IllegalArgumentException."<init>":(Ljava/lang/String;)V
     156: athrow

  public default <ElementT> java.util.List<ElementT> getList(int, java.lang.Class<ElementT>);
    Code:
       0: aload_0
       1: iload_1
       2: aload_2
       3: invokestatic  #76                 // Method com/datastax/oss/driver/api/core/type/reflect/GenericType.listOf:(Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/reflect/GenericType;
       6: invokeinterface #51,  3           // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/reflect/GenericType;)Ljava/lang/Object;
      11: checkcast     #77                 // class java/util/List
      14: areturn

  public default <ElementT> java.util.Set<ElementT> getSet(int, java.lang.Class<ElementT>);
    Code:
       0: aload_0
       1: iload_1
       2: aload_2
       3: invokestatic  #78                 // Method com/datastax/oss/driver/api/core/type/reflect/GenericType.setOf:(Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/reflect/GenericType;
       6: invokeinterface #51,  3           // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/reflect/GenericType;)Ljava/lang/Object;
      11: checkcast     #79                 // class java/util/Set
      14: areturn

  public default <KeyT, ValueT> java.util.Map<KeyT, ValueT> getMap(int, java.lang.Class<KeyT>, java.lang.Class<ValueT>);
    Code:
       0: aload_0
       1: iload_1
       2: aload_2
       3: aload_3
       4: invokestatic  #80                 // Method com/datastax/oss/driver/api/core/type/reflect/GenericType.mapOf:(Ljava/lang/Class;Ljava/lang/Class;)Lcom/datastax/oss/driver/api/core/type/reflect/GenericType;
       7: invokeinterface #51,  3           // InterfaceMethod get:(ILcom/datastax/oss/driver/api/core/type/reflect/GenericType;)Ljava/lang/Object;
      12: checkcast     #81                 // class java/util/Map
      15: areturn

  public default com.datastax.oss.driver.api.core.data.UdtValue getUdtValue(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #82                 // class com/datastax/oss/driver/api/core/data/UdtValue
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #82                 // class com/datastax/oss/driver/api/core/data/UdtValue
      12: areturn

  public default com.datastax.oss.driver.api.core.data.TupleValue getTupleValue(int);
    Code:
       0: aload_0
       1: iload_1
       2: ldc           #83                 // class com/datastax/oss/driver/api/core/data/TupleValue
       4: invokeinterface #40,  3           // InterfaceMethod get:(ILjava/lang/Class;)Ljava/lang/Object;
       9: checkcast     #83                 // class com/datastax/oss/driver/api/core/data/TupleValue
      12: areturn
}
```

</details>

<a id="inline-bytecode-defaultrow"></a>
### Recorded DefaultRow bytecode

<details>
<summary>Full record; SHA-256 1dce4062221711205685a5347d25b1f8ed5bf38d10f897d1b2e5c26d72b6beb2</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/DefaultRow.javap.txt`.

```text
Compiled from "DefaultRow.java"
public class com.datastax.oss.driver.internal.core.cql.DefaultRow implements com.datastax.oss.driver.api.core.cql.Row,java.io.Serializable {
  private final com.datastax.oss.driver.api.core.cql.ColumnDefinitions definitions;

  private final java.util.List<java.nio.ByteBuffer> data;

  private volatile transient com.datastax.oss.driver.api.core.detach.AttachmentPoint attachmentPoint;

  public com.datastax.oss.driver.internal.core.cql.DefaultRow(com.datastax.oss.driver.api.core.cql.ColumnDefinitions, java.util.List<java.nio.ByteBuffer>, com.datastax.oss.driver.api.core.detach.AttachmentPoint);
    Code:
       0: aload_0
       1: invokespecial #3                  // Method java/lang/Object."<init>":()V
       4: aload_0
       5: aload_1
       6: putfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       9: aload_0
      10: aload_2
      11: putfield      #1                  // Field data:Ljava/util/List;
      14: aload_0
      15: aload_3
      16: putfield      #4                  // Field attachmentPoint:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
      19: return

  public com.datastax.oss.driver.internal.core.cql.DefaultRow(com.datastax.oss.driver.api.core.cql.ColumnDefinitions, java.util.List<java.nio.ByteBuffer>);
    Code:
       0: aload_0
       1: aload_1
       2: aload_2
       3: getstatic     #5                  // Field com/datastax/oss/driver/api/core/detach/AttachmentPoint.NONE:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       6: invokespecial #6                  // Method "<init>":(Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;Ljava/util/List;Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;)V
       9: return

  public com.datastax.oss.driver.api.core.cql.ColumnDefinitions getColumnDefinitions();
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: areturn

  public int size();
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: invokeinterface #7,  1            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.size:()I
       9: ireturn

  public com.datastax.oss.driver.api.core.type.DataType getType(int);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: iload_1
       5: invokeinterface #8,  2            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.get:(I)Lcom/datastax/oss/driver/api/core/cql/ColumnDefinition;
      10: invokeinterface #9,  1            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinition.getType:()Lcom/datastax/oss/driver/api/core/type/DataType;
      15: areturn

  public java.util.List<java.lang.Integer> allIndicesOf(com.datastax.oss.driver.api.core.CqlIdentifier);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_1
       5: invokeinterface #10,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.allIndicesOf:(Lcom/datastax/oss/driver/api/core/CqlIdentifier;)Ljava/util/List;
      10: astore_2
      11: aload_2
      12: invokeinterface #11,  1           // InterfaceMethod java/util/List.isEmpty:()Z
      17: ifeq          47
      20: new           #12                 // class java/lang/IllegalArgumentException
      23: dup
      24: new           #13                 // class java/lang/StringBuilder
      27: dup
      28: invokespecial #14                 // Method java/lang/StringBuilder."<init>":()V
      31: aload_1
      32: invokevirtual #15                 // Method java/lang/StringBuilder.append:(Ljava/lang/Object;)Ljava/lang/StringBuilder;
      35: ldc           #16                 // String  is not a column in this row
      37: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      40: invokevirtual #18                 // Method java/lang/StringBuilder.toString:()Ljava/lang/String;
      43: invokespecial #19                 // Method java/lang/IllegalArgumentException."<init>":(Ljava/lang/String;)V
      46: athrow
      47: aload_2
      48: areturn

  public int firstIndexOf(com.datastax.oss.driver.api.core.CqlIdentifier);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_1
       5: invokeinterface #20,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.firstIndexOf:(Lcom/datastax/oss/driver/api/core/CqlIdentifier;)I
      10: istore_2
      11: iload_2
      12: iconst_m1
      13: if_icmpne     43
      16: new           #12                 // class java/lang/IllegalArgumentException
      19: dup
      20: new           #13                 // class java/lang/StringBuilder
      23: dup
      24: invokespecial #14                 // Method java/lang/StringBuilder."<init>":()V
      27: aload_1
      28: invokevirtual #15                 // Method java/lang/StringBuilder.append:(Ljava/lang/Object;)Ljava/lang/StringBuilder;
      31: ldc           #16                 // String  is not a column in this row
      33: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      36: invokevirtual #18                 // Method java/lang/StringBuilder.toString:()Ljava/lang/String;
      39: invokespecial #19                 // Method java/lang/IllegalArgumentException."<init>":(Ljava/lang/String;)V
      42: athrow
      43: iload_2
      44: ireturn

  public com.datastax.oss.driver.api.core.type.DataType getType(com.datastax.oss.driver.api.core.CqlIdentifier);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_0
       5: aload_1
       6: invokevirtual #21                 // Method firstIndexOf:(Lcom/datastax/oss/driver/api/core/CqlIdentifier;)I
       9: invokeinterface #8,  2            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.get:(I)Lcom/datastax/oss/driver/api/core/cql/ColumnDefinition;
      14: invokeinterface #9,  1            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinition.getType:()Lcom/datastax/oss/driver/api/core/type/DataType;
      19: areturn

  public java.util.List<java.lang.Integer> allIndicesOf(java.lang.String);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_1
       5: invokeinterface #22,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.allIndicesOf:(Ljava/lang/String;)Ljava/util/List;
      10: astore_2
      11: aload_2
      12: invokeinterface #11,  1           // InterfaceMethod java/util/List.isEmpty:()Z
      17: ifeq          47
      20: new           #12                 // class java/lang/IllegalArgumentException
      23: dup
      24: new           #13                 // class java/lang/StringBuilder
      27: dup
      28: invokespecial #14                 // Method java/lang/StringBuilder."<init>":()V
      31: aload_1
      32: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      35: ldc           #16                 // String  is not a column in this row
      37: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      40: invokevirtual #18                 // Method java/lang/StringBuilder.toString:()Ljava/lang/String;
      43: invokespecial #19                 // Method java/lang/IllegalArgumentException."<init>":(Ljava/lang/String;)V
      46: athrow
      47: aload_2
      48: areturn

  public int firstIndexOf(java.lang.String);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_1
       5: invokeinterface #23,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.firstIndexOf:(Ljava/lang/String;)I
      10: istore_2
      11: iload_2
      12: iconst_m1
      13: if_icmpne     43
      16: new           #12                 // class java/lang/IllegalArgumentException
      19: dup
      20: new           #13                 // class java/lang/StringBuilder
      23: dup
      24: invokespecial #14                 // Method java/lang/StringBuilder."<init>":()V
      27: aload_1
      28: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      31: ldc           #16                 // String  is not a column in this row
      33: invokevirtual #17                 // Method java/lang/StringBuilder.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;
      36: invokevirtual #18                 // Method java/lang/StringBuilder.toString:()Ljava/lang/String;
      39: invokespecial #19                 // Method java/lang/IllegalArgumentException."<init>":(Ljava/lang/String;)V
      42: athrow
      43: iload_2
      44: ireturn

  public com.datastax.oss.driver.api.core.type.DataType getType(java.lang.String);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: aload_0
       5: aload_1
       6: invokevirtual #24                 // Method firstIndexOf:(Ljava/lang/String;)I
       9: invokeinterface #8,  2            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.get:(I)Lcom/datastax/oss/driver/api/core/cql/ColumnDefinition;
      14: invokeinterface #9,  1            // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinition.getType:()Lcom/datastax/oss/driver/api/core/type/DataType;
      19: areturn

  public com.datastax.oss.driver.api.core.type.codec.registry.CodecRegistry codecRegistry();
    Code:
       0: aload_0
       1: getfield      #4                  // Field attachmentPoint:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       4: invokeinterface #25,  1           // InterfaceMethod com/datastax/oss/driver/api/core/detach/AttachmentPoint.getCodecRegistry:()Lcom/datastax/oss/driver/api/core/type/codec/registry/CodecRegistry;
       9: areturn

  public com.datastax.oss.driver.api.core.ProtocolVersion protocolVersion();
    Code:
       0: aload_0
       1: getfield      #4                  // Field attachmentPoint:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       4: invokeinterface #26,  1           // InterfaceMethod com/datastax/oss/driver/api/core/detach/AttachmentPoint.getProtocolVersion:()Lcom/datastax/oss/driver/api/core/ProtocolVersion;
       9: areturn

  public boolean isDetached();
    Code:
       0: aload_0
       1: getfield      #4                  // Field attachmentPoint:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       4: getstatic     #5                  // Field com/datastax/oss/driver/api/core/detach/AttachmentPoint.NONE:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       7: if_acmpne     14
      10: iconst_1
      11: goto          15
      14: iconst_0
      15: ireturn

  public void attach(com.datastax.oss.driver.api.core.detach.AttachmentPoint);
    Code:
       0: aload_0
       1: aload_1
       2: putfield      #4                  // Field attachmentPoint:Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;
       5: aload_0
       6: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       9: aload_1
      10: invokeinterface #27,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/ColumnDefinitions.attach:(Lcom/datastax/oss/driver/api/core/detach/AttachmentPoint;)V
      15: return

  public java.nio.ByteBuffer getBytesUnsafe(int);
    Code:
       0: aload_0
       1: getfield      #1                  // Field data:Ljava/util/List;
       4: iload_1
       5: invokeinterface #28,  2           // InterfaceMethod java/util/List.get:(I)Ljava/lang/Object;
      10: checkcast     #29                 // class java/nio/ByteBuffer
      13: areturn

  private java.lang.Object writeReplace();
    Code:
       0: new           #30                 // class com/datastax/oss/driver/internal/core/cql/DefaultRow$SerializationProxy
       3: dup
       4: aload_0
       5: invokespecial #31                 // Method com/datastax/oss/driver/internal/core/cql/DefaultRow$SerializationProxy."<init>":(Lcom/datastax/oss/driver/internal/core/cql/DefaultRow;)V
       8: areturn

  private void readObject(java.io.ObjectInputStream) throws java.io.InvalidObjectException;
    Code:
       0: new           #32                 // class java/io/InvalidObjectException
       3: dup
       4: ldc           #33                 // String Proxy required
       6: invokespecial #34                 // Method java/io/InvalidObjectException."<init>":(Ljava/lang/String;)V
       9: athrow

  static com.datastax.oss.driver.api.core.cql.ColumnDefinitions access$000(com.datastax.oss.driver.internal.core.cql.DefaultRow);
    Code:
       0: aload_0
       1: getfield      #2                  // Field definitions:Lcom/datastax/oss/driver/api/core/cql/ColumnDefinitions;
       4: areturn

  static java.util.List access$100(com.datastax.oss.driver.internal.core.cql.DefaultRow);
    Code:
       0: aload_0
       1: getfield      #1                  // Field data:Ljava/util/List;
       4: areturn
}
```

</details>

<a id="inline-bytecode-cassandratosqlcolumn"></a>
### Recorded CassandraToSqlColumn bytecode

<details>
<summary>Full record; SHA-256 d0b0ae99cc92fe5e5f3bcd1c8931a2d968350e0b08af8acb75b5792fac715391</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/CassandraToSqlColumn.javap.txt`.

```text
Compiled from "CassandraToSqlColumn.java"
public class org.thingsboard.server.service.install.migrate.CassandraToSqlColumn {
  private static final java.lang.ThreadLocal<java.util.regex.Pattern> PATTERN_THREAD_LOCAL;

  private static final java.lang.String EMPTY_STR;

  private int index;

  private int sqlIndex;

  private java.lang.String cassandraColumnName;

  private java.lang.String sqlColumnName;

  private org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType type;

  private int sqlType;

  private int size;

  private java.lang.Class<? extends java.lang.Enum> enumClass;

  private boolean allowNullBoolean;

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn idColumn(java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #3                  // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.ID:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: invokespecial #9                  // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;)V
      11: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn stringColumn(java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #13                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.STRING:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: invokespecial #9                  // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;)V
      11: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn stringColumn(java.lang.String, java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: aload_1
       6: invokespecial #16                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;)V
       9: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn bigintColumn(java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #19                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.BIGINT:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: invokespecial #9                  // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;)V
      11: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn doubleColumn(java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #22                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.DOUBLE:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: invokespecial #9                  // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;)V
      11: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn booleanColumn(java.lang.String);
    Code:
       0: aload_0
       1: iconst_0
       2: invokestatic  #25                 // Method booleanColumn:(Ljava/lang/String;Z)Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumn;
       5: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn booleanColumn(java.lang.String, boolean);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: aload_0
       6: getstatic     #29                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.BOOLEAN:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       9: aconst_null
      10: iload_1
      11: invokespecial #32                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;Z)V
      14: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn jsonColumn(java.lang.String);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #35                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.JSON:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: invokespecial #9                  // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;)V
      11: areturn

  public static org.thingsboard.server.service.install.migrate.CassandraToSqlColumn enumToIntColumn(java.lang.String, java.lang.Class<? extends java.lang.Enum>);
    Code:
       0: new           #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       3: dup
       4: aload_0
       5: getstatic     #38                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.ENUM_TO_INT:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       8: aload_1
       9: invokespecial #41                 // Method "<init>":(Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;)V
      12: areturn

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumn(java.lang.String);
    Code:
       0: aload_0
       1: aload_1
       2: aload_1
       3: getstatic     #13                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.STRING:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       6: aconst_null
       7: iconst_0
       8: invokespecial #32                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;Z)V
      11: return

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumn(java.lang.String, org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType);
    Code:
       0: aload_0
       1: aload_1
       2: aload_1
       3: aload_2
       4: aconst_null
       5: iconst_0
       6: invokespecial #32                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;Z)V
       9: return

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumn(java.lang.String, org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType, java.lang.Class<? extends java.lang.Enum>);
    Code:
       0: aload_0
       1: aload_1
       2: aload_1
       3: aload_2
       4: aload_3
       5: iconst_0
       6: invokespecial #32                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;Z)V
       9: return

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumn(java.lang.String, java.lang.String);
    Code:
       0: aload_0
       1: aload_1
       2: aload_2
       3: getstatic     #13                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.STRING:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       6: aconst_null
       7: iconst_0
       8: invokespecial #32                 // Method "<init>":(Ljava/lang/String;Ljava/lang/String;Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;Ljava/lang/Class;Z)V
      11: return

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumn(java.lang.String, java.lang.String, org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType, java.lang.Class<? extends java.lang.Enum>, boolean);
    Code:
       0: aload_0
       1: invokespecial #44                 // Method java/lang/Object."<init>":()V
       4: aload_0
       5: iconst_0
       6: putfield      #49                 // Field allowNullBoolean:Z
       9: aload_0
      10: aload_1
      11: putfield      #53                 // Field cassandraColumnName:Ljava/lang/String;
      14: aload_0
      15: aload_2
      16: putfield      #57                 // Field sqlColumnName:Ljava/lang/String;
      19: aload_0
      20: aload_3
      21: putfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      24: aload_0
      25: aload         4
      27: putfield      #63                 // Field enumClass:Ljava/lang/Class;
      30: aload_0
      31: iload         5
      33: putfield      #49                 // Field allowNullBoolean:Z
      36: return

  public java.lang.String getColumnValue(com.datastax.oss.driver.api.core.cql.Row);
    Code:
       0: aload_1
       1: aload_0
       2: getfield      #67                 // Field index:I
       5: invokeinterface #71,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.isNull:(I)Z
      10: ifeq          37
      13: aload_0
      14: getfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      17: getstatic     #29                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.BOOLEAN:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      20: if_acmpne     35
      23: aload_0
      24: getfield      #49                 // Field allowNullBoolean:Z
      27: ifne          35
      30: iconst_0
      31: invokestatic  #77                 // Method java/lang/Boolean.toString:(Z)Ljava/lang/String;
      34: areturn
      35: aconst_null
      36: areturn
      37: getstatic     #83                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumn$1.$SwitchMap$org$thingsboard$server$service$install$migrate$CassandraToSqlColumnType:[I
      40: aload_0
      41: getfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      44: invokevirtual #89                 // Method org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.ordinal:()I
      47: iaload
      48: tableswitch   { // 1 to 9
                     1: 100
                     2: 114
                     3: 128
                     4: 142
                     5: 156
                     6: 170
                     7: 184
                     8: 184
                     9: 184
               default: 184
          }
     100: aload_1
     101: aload_0
     102: getfield      #67                 // Field index:I
     105: invokeinterface #93,  2           // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getUuid:(I)Ljava/util/UUID;
     110: invokestatic  #97                 // Method org/thingsboard/server/common/data/UUIDConverter.fromTimeUUID:(Ljava/util/UUID;)Ljava/lang/String;
     113: areturn
     114: aload_1
     115: aload_0
     116: getfield      #67                 // Field index:I
     119: invokeinterface #103,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getDouble:(I)D
     124: invokestatic  #107                // Method java/lang/Double.toString:(D)Ljava/lang/String;
     127: areturn
     128: aload_1
     129: aload_0
     130: getfield      #67                 // Field index:I
     133: invokeinterface #112,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getInt:(I)I
     138: invokestatic  #116                // Method java/lang/Integer.toString:(I)Ljava/lang/String;
     141: areturn
     142: aload_1
     143: aload_0
     144: getfield      #67                 // Field index:I
     147: invokeinterface #121,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getFloat:(I)F
     152: invokestatic  #125                // Method java/lang/Float.toString:(F)Ljava/lang/String;
     155: areturn
     156: aload_1
     157: aload_0
     158: getfield      #67                 // Field index:I
     161: invokeinterface #130,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getLong:(I)J
     166: invokestatic  #134                // Method java/lang/Long.toString:(J)Ljava/lang/String;
     169: areturn
     170: aload_1
     171: aload_0
     172: getfield      #67                 // Field index:I
     175: invokeinterface #139,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getBoolean:(I)Z
     180: invokestatic  #77                 // Method java/lang/Boolean.toString:(Z)Ljava/lang/String;
     183: areturn
     184: aload_1
     185: aload_0
     186: getfield      #67                 // Field index:I
     189: invokeinterface #142,  2          // InterfaceMethod com/datastax/oss/driver/api/core/cql/Row.getString:(I)Ljava/lang/String;
     194: astore_2
     195: aload_0
     196: aload_2
     197: invokevirtual #145                // Method replaceNullChars:(Ljava/lang/String;)Ljava/lang/String;
     200: areturn

  public void setColumnValue(java.sql.PreparedStatement, java.lang.String) throws java.sql.SQLException;
    Code:
       0: aload_2
       1: ifnonnull     21
       4: aload_1
       5: aload_0
       6: getfield      #149                // Field sqlIndex:I
       9: aload_0
      10: getfield      #152                // Field sqlType:I
      13: invokeinterface #155,  3          // InterfaceMethod java/sql/PreparedStatement.setNull:(II)V
      18: goto          210
      21: getstatic     #83                 // Field org/thingsboard/server/service/install/migrate/CassandraToSqlColumn$1.$SwitchMap$org$thingsboard$server$service$install$migrate$CassandraToSqlColumnType:[I
      24: aload_0
      25: getfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      28: invokevirtual #89                 // Method org/thingsboard/server/service/install/migrate/CassandraToSqlColumnType.ordinal:()I
      31: iaload
      32: tableswitch   { // 1 to 9
                     1: 199
                     2: 84
                     3: 101
                     4: 118
                     5: 135
                     6: 152
                     7: 199
                     8: 199
                     9: 169
               default: 199
          }
      84: aload_1
      85: aload_0
      86: getfield      #149                // Field sqlIndex:I
      89: aload_2
      90: invokestatic  #161                // Method java/lang/Double.parseDouble:(Ljava/lang/String;)D
      93: invokeinterface #165,  4          // InterfaceMethod java/sql/PreparedStatement.setDouble:(ID)V
      98: goto          210
     101: aload_1
     102: aload_0
     103: getfield      #149                // Field sqlIndex:I
     106: aload_2
     107: invokestatic  #169                // Method java/lang/Integer.parseInt:(Ljava/lang/String;)I
     110: invokeinterface #173,  3          // InterfaceMethod java/sql/PreparedStatement.setInt:(II)V
     115: goto          210
     118: aload_1
     119: aload_0
     120: getfield      #149                // Field sqlIndex:I
     123: aload_2
     124: invokestatic  #176                // Method java/lang/Float.parseFloat:(Ljava/lang/String;)F
     127: invokeinterface #180,  3          // InterfaceMethod java/sql/PreparedStatement.setFloat:(IF)V
     132: goto          210
     135: aload_1
     136: aload_0
     137: getfield      #149                // Field sqlIndex:I
     140: aload_2
     141: invokestatic  #184                // Method java/lang/Long.parseLong:(Ljava/lang/String;)J
     144: invokeinterface #188,  4          // InterfaceMethod java/sql/PreparedStatement.setLong:(IJ)V
     149: goto          210
     152: aload_1
     153: aload_0
     154: getfield      #149                // Field sqlIndex:I
     157: aload_2
     158: invokestatic  #192                // Method java/lang/Boolean.parseBoolean:(Ljava/lang/String;)Z
     161: invokeinterface #196,  3          // InterfaceMethod java/sql/PreparedStatement.setBoolean:(IZ)V
     166: goto          210
     169: aload_0
     170: getfield      #63                 // Field enumClass:Ljava/lang/Class;
     173: aload_2
     174: invokestatic  #200                // Method java/lang/Enum.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;
     177: astore_3
     178: aload_3
     179: invokevirtual #206                // Method java/lang/Enum.ordinal:()I
     182: istore        4
     184: aload_1
     185: aload_0
     186: getfield      #149                // Field sqlIndex:I
     189: iload         4
     191: invokeinterface #173,  3          // InterfaceMethod java/sql/PreparedStatement.setInt:(II)V
     196: goto          210
     199: aload_1
     200: aload_0
     201: getfield      #149                // Field sqlIndex:I
     204: aload_2
     205: invokeinterface #207,  3          // InterfaceMethod java/sql/PreparedStatement.setString:(ILjava/lang/String;)V
     210: return

  private java.lang.String replaceNullChars(java.lang.String);
    Code:
       0: aload_1
       1: ifnull        23
       4: getstatic     #211                // Field PATTERN_THREAD_LOCAL:Ljava/lang/ThreadLocal;
       7: invokevirtual #215                // Method java/lang/ThreadLocal.get:()Ljava/lang/Object;
      10: checkcast     #221                // class java/util/regex/Pattern
      13: aload_1
      14: invokevirtual #223                // Method java/util/regex/Pattern.matcher:(Ljava/lang/CharSequence;)Ljava/util/regex/Matcher;
      17: ldc           #227                // String
      19: invokevirtual #229                // Method java/util/regex/Matcher.replaceAll:(Ljava/lang/String;)Ljava/lang/String;
      22: areturn
      23: aload_1
      24: areturn

  public int getIndex();
    Code:
       0: aload_0
       1: getfield      #67                 // Field index:I
       4: ireturn

  public int getSqlIndex();
    Code:
       0: aload_0
       1: getfield      #149                // Field sqlIndex:I
       4: ireturn

  public java.lang.String getCassandraColumnName();
    Code:
       0: aload_0
       1: getfield      #53                 // Field cassandraColumnName:Ljava/lang/String;
       4: areturn

  public java.lang.String getSqlColumnName();
    Code:
       0: aload_0
       1: getfield      #57                 // Field sqlColumnName:Ljava/lang/String;
       4: areturn

  public org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType getType();
    Code:
       0: aload_0
       1: getfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       4: areturn

  public int getSqlType();
    Code:
       0: aload_0
       1: getfield      #152                // Field sqlType:I
       4: ireturn

  public int getSize();
    Code:
       0: aload_0
       1: getfield      #234                // Field size:I
       4: ireturn

  public java.lang.Class<? extends java.lang.Enum> getEnumClass();
    Code:
       0: aload_0
       1: getfield      #63                 // Field enumClass:Ljava/lang/Class;
       4: areturn

  public boolean isAllowNullBoolean();
    Code:
       0: aload_0
       1: getfield      #49                 // Field allowNullBoolean:Z
       4: ireturn

  public void setIndex(int);
    Code:
       0: aload_0
       1: iload_1
       2: putfield      #67                 // Field index:I
       5: return

  public void setSqlIndex(int);
    Code:
       0: aload_0
       1: iload_1
       2: putfield      #149                // Field sqlIndex:I
       5: return

  public void setCassandraColumnName(java.lang.String);
    Code:
       0: aload_0
       1: aload_1
       2: putfield      #53                 // Field cassandraColumnName:Ljava/lang/String;
       5: return

  public void setSqlColumnName(java.lang.String);
    Code:
       0: aload_0
       1: aload_1
       2: putfield      #57                 // Field sqlColumnName:Ljava/lang/String;
       5: return

  public void setType(org.thingsboard.server.service.install.migrate.CassandraToSqlColumnType);
    Code:
       0: aload_0
       1: aload_1
       2: putfield      #60                 // Field type:Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
       5: return

  public void setSqlType(int);
    Code:
       0: aload_0
       1: iload_1
       2: putfield      #152                // Field sqlType:I
       5: return

  public void setSize(int);
    Code:
       0: aload_0
       1: iload_1
       2: putfield      #234                // Field size:I
       5: return

  public void setEnumClass(java.lang.Class<? extends java.lang.Enum>);
    Code:
       0: aload_0
       1: aload_1
       2: putfield      #63                 // Field enumClass:Ljava/lang/Class;
       5: return

  public void setAllowNullBoolean(boolean);
    Code:
       0: aload_0
       1: iload_1
       2: putfield      #49                 // Field allowNullBoolean:Z
       5: return

  public boolean equals(java.lang.Object);
    Code:
       0: aload_1
       1: aload_0
       2: if_acmpne     7
       5: iconst_1
       6: ireturn
       7: aload_1
       8: instanceof    #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
      11: ifne          16
      14: iconst_0
      15: ireturn
      16: aload_1
      17: checkcast     #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
      20: astore_2
      21: aload_2
      22: aload_0
      23: invokevirtual #237                // Method canEqual:(Ljava/lang/Object;)Z
      26: ifne          31
      29: iconst_0
      30: ireturn
      31: aload_0
      32: invokevirtual #241                // Method getIndex:()I
      35: aload_2
      36: invokevirtual #241                // Method getIndex:()I
      39: if_icmpeq     44
      42: iconst_0
      43: ireturn
      44: aload_0
      45: invokevirtual #244                // Method getSqlIndex:()I
      48: aload_2
      49: invokevirtual #244                // Method getSqlIndex:()I
      52: if_icmpeq     57
      55: iconst_0
      56: ireturn
      57: aload_0
      58: invokevirtual #247                // Method getSqlType:()I
      61: aload_2
      62: invokevirtual #247                // Method getSqlType:()I
      65: if_icmpeq     70
      68: iconst_0
      69: ireturn
      70: aload_0
      71: invokevirtual #250                // Method getSize:()I
      74: aload_2
      75: invokevirtual #250                // Method getSize:()I
      78: if_icmpeq     83
      81: iconst_0
      82: ireturn
      83: aload_0
      84: invokevirtual #253                // Method isAllowNullBoolean:()Z
      87: aload_2
      88: invokevirtual #253                // Method isAllowNullBoolean:()Z
      91: if_icmpeq     96
      94: iconst_0
      95: ireturn
      96: aload_0
      97: invokevirtual #257                // Method getCassandraColumnName:()Ljava/lang/String;
     100: astore_3
     101: aload_2
     102: invokevirtual #257                // Method getCassandraColumnName:()Ljava/lang/String;
     105: astore        4
     107: aload_3
     108: ifnonnull     119
     111: aload         4
     113: ifnull        130
     116: goto          128
     119: aload_3
     120: aload         4
     122: invokevirtual #261                // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
     125: ifne          130
     128: iconst_0
     129: ireturn
     130: aload_0
     131: invokevirtual #264                // Method getSqlColumnName:()Ljava/lang/String;
     134: astore        5
     136: aload_2
     137: invokevirtual #264                // Method getSqlColumnName:()Ljava/lang/String;
     140: astore        6
     142: aload         5
     144: ifnonnull     155
     147: aload         6
     149: ifnull        167
     152: goto          165
     155: aload         5
     157: aload         6
     159: invokevirtual #261                // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
     162: ifne          167
     165: iconst_0
     166: ireturn
     167: aload_0
     168: invokevirtual #267                // Method getType:()Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
     171: astore        7
     173: aload_2
     174: invokevirtual #267                // Method getType:()Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
     177: astore        8
     179: aload         7
     181: ifnonnull     192
     184: aload         8
     186: ifnull        204
     189: goto          202
     192: aload         7
     194: aload         8
     196: invokevirtual #261                // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
     199: ifne          204
     202: iconst_0
     203: ireturn
     204: aload_0
     205: invokevirtual #271                // Method getEnumClass:()Ljava/lang/Class;
     208: astore        9
     210: aload_2
     211: invokevirtual #271                // Method getEnumClass:()Ljava/lang/Class;
     214: astore        10
     216: aload         9
     218: ifnonnull     229
     221: aload         10
     223: ifnull        241
     226: goto          239
     229: aload         9
     231: aload         10
     233: invokevirtual #261                // Method java/lang/Object.equals:(Ljava/lang/Object;)Z
     236: ifne          241
     239: iconst_0
     240: ireturn
     241: iconst_1
     242: ireturn

  protected boolean canEqual(java.lang.Object);
    Code:
       0: aload_1
       1: instanceof    #1                  // class org/thingsboard/server/service/install/migrate/CassandraToSqlColumn
       4: ireturn

  public int hashCode();
    Code:
       0: bipush        59
       2: istore_1
       3: iconst_1
       4: istore_2
       5: iload_2
       6: bipush        59
       8: imul
       9: aload_0
      10: invokevirtual #241                // Method getIndex:()I
      13: iadd
      14: istore_2
      15: iload_2
      16: bipush        59
      18: imul
      19: aload_0
      20: invokevirtual #244                // Method getSqlIndex:()I
      23: iadd
      24: istore_2
      25: iload_2
      26: bipush        59
      28: imul
      29: aload_0
      30: invokevirtual #247                // Method getSqlType:()I
      33: iadd
      34: istore_2
      35: iload_2
      36: bipush        59
      38: imul
      39: aload_0
      40: invokevirtual #250                // Method getSize:()I
      43: iadd
      44: istore_2
      45: iload_2
      46: bipush        59
      48: imul
      49: aload_0
      50: invokevirtual #253                // Method isAllowNullBoolean:()Z
      53: ifeq          61
      56: bipush        79
      58: goto          63
      61: bipush        97
      63: iadd
      64: istore_2
      65: aload_0
      66: invokevirtual #257                // Method getCassandraColumnName:()Ljava/lang/String;
      69: astore_3
      70: iload_2
      71: bipush        59
      73: imul
      74: aload_3
      75: ifnonnull     83
      78: bipush        43
      80: goto          87
      83: aload_3
      84: invokevirtual #275                // Method java/lang/Object.hashCode:()I
      87: iadd
      88: istore_2
      89: aload_0
      90: invokevirtual #264                // Method getSqlColumnName:()Ljava/lang/String;
      93: astore        4
      95: iload_2
      96: bipush        59
      98: imul
      99: aload         4
     101: ifnonnull     109
     104: bipush        43
     106: goto          114
     109: aload         4
     111: invokevirtual #275                // Method java/lang/Object.hashCode:()I
     114: iadd
     115: istore_2
     116: aload_0
     117: invokevirtual #267                // Method getType:()Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
     120: astore        5
     122: iload_2
     123: bipush        59
     125: imul
     126: aload         5
     128: ifnonnull     136
     131: bipush        43
     133: goto          141
     136: aload         5
     138: invokevirtual #275                // Method java/lang/Object.hashCode:()I
     141: iadd
     142: istore_2
     143: aload_0
     144: invokevirtual #271                // Method getEnumClass:()Ljava/lang/Class;
     147: astore        6
     149: iload_2
     150: bipush        59
     152: imul
     153: aload         6
     155: ifnonnull     163
     158: bipush        43
     160: goto          168
     163: aload         6
     165: invokevirtual #275                // Method java/lang/Object.hashCode:()I
     168: iadd
     169: istore_2
     170: iload_2
     171: ireturn

  public java.lang.String toString();
    Code:
       0: aload_0
       1: invokevirtual #241                // Method getIndex:()I
       4: aload_0
       5: invokevirtual #244                // Method getSqlIndex:()I
       8: aload_0
       9: invokevirtual #257                // Method getCassandraColumnName:()Ljava/lang/String;
      12: aload_0
      13: invokevirtual #264                // Method getSqlColumnName:()Ljava/lang/String;
      16: aload_0
      17: invokevirtual #267                // Method getType:()Lorg/thingsboard/server/service/install/migrate/CassandraToSqlColumnType;
      20: invokestatic  #278                // Method java/lang/String.valueOf:(Ljava/lang/Object;)Ljava/lang/String;
      23: aload_0
      24: invokevirtual #247                // Method getSqlType:()I
      27: aload_0
      28: invokevirtual #250                // Method getSize:()I
      31: aload_0
      32: invokevirtual #271                // Method getEnumClass:()Ljava/lang/Class;
      35: invokestatic  #278                // Method java/lang/String.valueOf:(Ljava/lang/Object;)Ljava/lang/String;
      38: aload_0
      39: invokevirtual #253                // Method isAllowNullBoolean:()Z
      42: invokedynamic #283,  0            // InvokeDynamic #0:makeConcatWithConstants:(IILjava/lang/String;Ljava/lang/String;Ljava/lang/String;IILjava/lang/String;Z)Ljava/lang/String;
      47: areturn

  private static java.util.regex.Pattern lambda$static$0();
    Code:
       0: iconst_0
       1: invokestatic  #289                // Method java/lang/String.valueOf:(C)Ljava/lang/String;
       4: invokestatic  #292                // Method java/util/regex/Pattern.compile:(Ljava/lang/String;)Ljava/util/regex/Pattern;
       7: areturn

  static {};
    Code:
       0: invokedynamic #296,  0            // InvokeDynamic #1:get:()Ljava/util/function/Supplier;
       5: invokestatic  #299                // Method java/lang/ThreadLocal.withInitial:(Ljava/util/function/Supplier;)Ljava/lang/ThreadLocal;
       8: putstatic     #211                // Field PATTERN_THREAD_LOCAL:Ljava/lang/ThreadLocal;
      11: return
}
```

</details>

<a id="inline-ap-replay"></a>
## Actual AP replay: source and controls

This replay uses actual `fcfe2e905` AP operators and its corrected owner. It executes the source-valid copy, field cut and read. It then tests owner order, layers and full-mask transport. It does not run the JVM rule binder or a project analyzer.

The observed two excluded marks are supplied on the operand; their producer is not replayed. A later DEMAND STAR FLOW is a legal admission control, not a claim about its real producer. The arg0 self-output FLOW is omitted because it has the wrong output base for ret. The NORMAL marked layer near-miss tests the general owner API; it does not claim that run-1 emits NORMAL marked results.

<a id="inline-ap-replay-results"></a>
### Complete replay report and four control records

<details>
<summary>Full record; SHA-256 c9f7b77439232be5989752beb978efd650030856b40d6e069a2457ba8c342774</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/report.json`.

```json
{
  "state": "PASS",
  "created_utc": "2026-10-26T23:31:51.641585+00:00",
  "modeled_iteration": "run-1",
  "field_limit": 1,
  "mark_mode": "FULL",
  "project_analyzer_runs": 0,
  "source_revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
  "terminal": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/terminal.json",
  "terminal_sha256": "f3325b49958d0d972daceedd75aa7f11969d6466e79d8158a9bcffd4ac63377b",
  "tests": {
    "tests": 4,
    "failures": 0,
    "errors": 0,
    "skipped": 0
  },
  "test_heap": "1g",
  "compiler_heap": "2g",
  "all_four_source_snapshots_unchanged": true,
  "frozen_baseline_artifacts_unchanged": true,
  "compiled_main_classes_unchanged": true,
  "controls": {
    "order-and-layer-controls.json": {
      "reverse_order": [
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        },
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        }
      ],
      "demand_any_then_normal_star": [
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ]
        },
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        }
      ],
      "weak_flow_normal_taint": [
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        },
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@492691d7",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ]
        }
      ]
    },
    "any-first-same-layer.json": {
      "flow_any_admitted": true,
      "later_flow_star_admitted": false,
      "marked_any_admitted": false,
      "marked_star_admitted": true,
      "t_handle": 3,
      "stored": [
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6af9fcb2",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        },
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@ca30bc1",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        }
      ],
      "later_star_scope": "A legal DEMAND STAR header is offered as an admission control; its producer is not claimed.",
      "historical_offer_order_claimed": false
    },
    "protected-field-cut.json": {
      "steps": [
        [
          {
            "base": "arg(0)",
            "path": [],
            "tail": "STAR",
            "mark": "Concrete(mark=TaintMark(id=3))",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": true
          }
        ],
        [
          {
            "base": "var(17)",
            "path": [
              "Matcher#group",
              "String#content"
            ],
            "tail": "STAR",
            "mark": "Concrete(mark=TaintMark(id=3))",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": true
          }
        ],
        [
          {
            "base": "var(17)",
            "path": [
              "Matcher#group"
            ],
            "tail": "ANY",
            "mark": "Concrete(mark=TaintMark(id=3))",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": true
          }
        ],
        [
          {
            "base": "ret",
            "path": [],
            "tail": "ANY",
            "mark": "Concrete(mark=TaintMark(id=3))",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "stored": [
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6fa34d52",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        },
        {
          "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@4671115f",
          "facts": [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ]
        }
      ],
      "protected_memberships": 1
    },
    "regex-field-cut.json": {
      "checker": "actual-fcfe-AP",
      "mark_names_in_handle_order": [
        "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
        "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
        "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3"
      ],
      "input_scope": "The observed excluded marks1/2 are supplied on the operand to isolate geometry; their producer is not replayed.",
      "steps": [
        [
          {
            "base": "arg(0)",
            "path": [],
            "tail": "STAR",
            "mark": "Star(excluded={1, 2})",
            "field_exclusion": "Empty",
            "layer": "NORMAL",
            "protected": false
          }
        ],
        [
          {
            "base": "var(17)",
            "path": [
              "Matcher#group",
              "String#content"
            ],
            "tail": "STAR",
            "mark": "Star(excluded={1, 2})",
            "field_exclusion": "Empty",
            "layer": "NORMAL",
            "protected": false
          }
        ],
        [
          {
            "base": "var(17)",
            "path": [
              "Matcher#group"
            ],
            "tail": "ANY",
            "mark": "Star(excluded={1, 2})",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": false
          }
        ],
        [
          {
            "base": "ret",
            "path": [],
            "tail": "ANY",
            "mark": "Star(excluded={1, 2})",
            "field_exclusion": "Empty",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "historical_first_producer_claimed": false
    }
  },
  "actual_operator_scope": [
    "ApOps.applyEdge for the copied source-valid regex model positions",
    "ApOps.limit(fieldLimit=1)",
    "FlowBackedSummaries.add/normalize using actual corrected fcfe owner"
  ],
  "source_correspondence": {
    "report": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/report.json",
    "sha256": "0c17cc4574b9b005f9a0cbe78e1d80c429cd3eeafbb64e9729cd27026dff8fd4",
    "models": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/cassandra-producer-trace/model-candidates.json",
    "models_sha256": "7699d60eb8c70a04689b8f435c386372b859d00680e34803b5c78ce7e9f6bf95"
  },
  "limits": [
    "This is an actual AP/store replay of source-valid lowered positions, not execution of the JVM rule binder or Thingsboard project.",
    "Excluded full marks1/2 are seeded on the operand from the observed final header; the source of those exclusions is not replayed.",
    "The later same-DEMAND FLOW STAR offer is a legal admission control; its real producer is not claimed.",
    "The observed arg0 NORMAL self-output FLOW is omitted from the owner control because its output base cannot cover ret.",
    "The NORMAL TAINT layer near-miss checks the general owner API; it is not claimed to be emitted by the run-1 engine, which forces marked results to DEMAND.",
    "The historical switch branch, first actual producer and offer order in Thingsboard remain unproved. No runtime behavior, proof contract or tracked source was patched."
  ],
  "setup_attempts": [
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232506/terminal.json",
      "classification": "EXTERNAL_INIT_SETUP_FAILURE"
    },
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232602/terminal.json",
      "classification": "EXTERNAL_INIT_SETUP_FAILURE"
    },
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232806/terminal.json",
      "classification": "EXTERNAL_FIXTURE_COMPILE_FAILURE"
    },
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/terminal.json",
      "classification": "PASS"
    }
  ]
}
```

</details>

<a id="inline-ap-replay-receipt"></a>
### Complete replay command, source hashes and control results

<details>
<summary>Full record; SHA-256 f3325b49958d0d972daceedd75aa7f11969d6466e79d8158a9bcffd4ac63377b</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/terminal.json`.

```json
{
  "state": "PASS",
  "started_utc": "2026-10-26T23:29:33.478910+00:00",
  "command": [
    "./gradlew",
    ":opentaint-dataflow-core:opentaint-dataflow:test",
    "--tests",
    "org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest",
    "--console=plain",
    "--no-daemon",
    "--max-workers=2",
    "-Pkotlin.compiler.execution.strategy=in-process",
    "-Dorg.gradle.jvmargs=-Xmx2g",
    "-Dopentaint.replay.attempt=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/preparation/test-protoc.init.gradle",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/replay.init.gradle"
  ],
  "cwd": "/drive-testcomp/opentaint-go-rules/opentaint-w3/core",
  "mem_available_bytes": 45411086336,
  "test_heap": "1g",
  "compiler_heap": "2g",
  "source": {
    "current": {
      "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
      "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
      "tracked_patch_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
      "added_sources": {}
    },
    "reference": {
      "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
      "core_tree": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
      "tracked_patch_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
      "added_sources": {}
    },
    "diagnostic": {
      "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
      "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
      "tracked_patch_sha256": "425b82dda902da61b63cf05a5aa0aeed17bc356a79f3c743565cd10417bb2a06",
      "added_sources": {
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/Run1ProcessedWorkCounters.kt": "b0a9b39ccaacd051cfc37c6e546d0c7d674d1e792e347498f79928f5b8bcb598",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1ShapeCensus.kt": "aaf5d26850604bf87e1993c7d526acaffe4965c69ebb7ced4875465dbf9a83f4",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1TargetMethodDump.kt": "3b06173bc20b6eb123987e02178f996085af042b68a2cc29339d0b190061b93c",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/Run1ShapeCensusTest.kt": "c6083507f726afeef3232360fa5d40902181fe3a1ffe12204b4525482f83bf2c"
      }
    },
    "baseline_diagnostic": {
      "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
      "core_tree": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
      "tracked_patch_sha256": "a4ad2f865e7ffae6f023b4ed756435e88c3d48c35fc94fb4fca54e9b48064af0",
      "added_sources": {
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineRun1ShapeCensus.kt": "248de77d94e78778b85a20ba412098cef7e7e95a9cd5bb9d7d734d23c8537933",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c"
      }
    }
  },
  "external_files": {
    "run.py": "e9387102da778f86fb45e02f294e9919d8da4faa916396058af83c796f3cadac",
    "replay.init.gradle": "71f500c3e88d99a9f1d83a2fe317104390ae40476a1ec00678a7ec9bd3b02b2b",
    "source/CassandraRegexTailReplayTest.kt": "08867037a0cd8320ed54f4da93f3558837035bf2cf6d7efbcd2560b3d6edfe3f",
    "fixture-cache-manifest.json": "b891fc6bf73cb9766f2fb81cb76245d6cd7cebecd392d74422ec384195a7c8c4"
  },
  "compiled_main_classes": {
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/ap/ApOps.class": "64cbc5aea1db8ec5c521c6652147232efd16098a18b04364b98f572a7b0c7af4",
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/ap/EdgeApplication.class": "2cd37f9acd09dd709f56f61e1ae0357f39bc2d60d4ca180c37add83be95d051a",
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/ap/LimitKt.class": "340587d3aa9b2db608726c43dcb68a258e1adaa81adff64d52561c02a9298ac7",
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/ap/FlowGroup.class": "e520f3efcc1a05eceeda621315d9f472144af4bb15678267b0ce35152a4a1694",
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/store/FlowBackedSummaries.class": "bce503406c98ac28e5b394c936c40306459f7bfba67f5598c9b6dc0726623acb",
    "core/opentaint-dataflow-core/opentaint-dataflow/build/classes/kotlin/main/org/opentaint/dataflow/bidi/store/DiagonalRelations.class": "e5dbb4d30d41c05dd46667471a4054c4db0ba684e98c7284c1977c9482a2f16c"
  },
  "frozen_baseline_files": {
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/run_baseline_shape_campaign.py": "ee62a87debdde99b665ef9ce5d126b77d6714d3c7d55e7ad5138a217225901f9",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/test_baseline_shape_probe.py": "6eedc2d5cece014a1459ea586c8f37762f414f2342da5514716eaf1f87d5c14a",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/terminal.json": "8bd44f2d77134eaf3ea65091d6ea28f0568f9d95b88730e1fc67fdf2e181cac1",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/prepared.json": "226b05d94ec192c77fc0b7335dc08907433c1b166a1723a580eeae4626bfa724"
  },
  "scope": "Actual fcfe AP operators and normalized owner; source-valid metadata paths reconstructed externally. No project analyzer, JIR binding or historical processing order is replayed.",
  "ended_utc": "2026-10-26T23:30:11.206248+00:00",
  "returncode": 0,
  "source_unchanged": true,
  "frozen_baseline_files_unchanged": true,
  "external_files_unchanged": true,
  "totals": {
    "tests": 4,
    "failures": 0,
    "errors": 0,
    "skipped": 0
  },
  "fresh_xml": [
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/xml/TEST-org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest.xml",
      "sha256": "6742208f6f891530e9e9127b4ad45cbb45bd704ecb22f72cf0bd378a3998145b"
    }
  ],
  "controls": {
    "order-and-layer-controls.json": {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/controls/order-and-layer-controls.json",
      "sha256": "596b73131f2faa1ea0c1e52adfa413ecbe3ad0c2bd02daff4361fec44fa15f59",
      "data": {
        "reverse_order": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "demand_any_then_normal_star": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "NORMAL",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "weak_flow_normal_taint": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@63f259c3",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@492691d7",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "NORMAL",
                "protected": false
              }
            ]
          }
        ]
      }
    },
    "any-first-same-layer.json": {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/controls/any-first-same-layer.json",
      "sha256": "db3c6d834ed4b4543a27971f8c10bf7d6cb7c6c61c5293a5c24f7ac4a1e8fd56",
      "data": {
        "flow_any_admitted": true,
        "later_flow_star_admitted": false,
        "marked_any_admitted": false,
        "marked_star_admitted": true,
        "t_handle": 3,
        "stored": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6af9fcb2",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@ca30bc1",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "STAR",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          }
        ],
        "later_star_scope": "A legal DEMAND STAR header is offered as an admission control; its producer is not claimed.",
        "historical_offer_order_claimed": false
      }
    },
    "protected-field-cut.json": {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/controls/protected-field-cut.json",
      "sha256": "6b26d73f9989400e3ee4a8de50af3564086462189796410dcf99c9eee4fd39b4",
      "data": {
        "steps": [
          [
            {
              "base": "arg(0)",
              "path": [],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group",
                "String#content"
              ],
              "tail": "STAR",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group"
              ],
              "tail": "ANY",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ],
          [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Concrete(mark=TaintMark(id=3))",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": true
            }
          ]
        ],
        "stored": [
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@6fa34d52",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Star(excluded={1, 2})",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": false
              }
            ]
          },
          {
            "initial": "org.opentaint.dataflow.bidi.ap.InitialAp@4671115f",
            "facts": [
              {
                "base": "ret",
                "path": [],
                "tail": "ANY",
                "mark": "Concrete(mark=TaintMark(id=3))",
                "field_exclusion": "Empty",
                "layer": "DEMAND",
                "protected": true
              }
            ]
          }
        ],
        "protected_memberships": 1
      }
    },
    "regex-field-cut.json": {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/controls/regex-field-cut.json",
      "sha256": "94abe2e2c812a882b308a8d0792dae4b4eb014fa3cabb5857182c6e61c6015bf",
      "data": {
        "checker": "actual-fcfe-AP",
        "mark_names_in_handle_order": [
          "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
          "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
          "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3"
        ],
        "input_scope": "The observed excluded marks1/2 are supplied on the operand to isolate geometry; their producer is not replayed.",
        "steps": [
          [
            {
              "base": "arg(0)",
              "path": [],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group",
                "String#content"
              ],
              "tail": "STAR",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "NORMAL",
              "protected": false
            }
          ],
          [
            {
              "base": "var(17)",
              "path": [
                "Matcher#group"
              ],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ],
          [
            {
              "base": "ret",
              "path": [],
              "tail": "ANY",
              "mark": "Star(excluded={1, 2})",
              "field_exclusion": "Empty",
              "layer": "DEMAND",
              "protected": false
            }
          ]
        ],
        "historical_first_producer_claimed": false
      }
    }
  },
  "log_sha256": "7a1b102728e128fc6bea5282088e2250c96630cfb160229c48285e62dac40919",
  "attempt": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933"
}
```

</details>

<a id="inline-ap-replay-source"></a>
### Complete external Kotlin fixture

<details>
<summary>Full record; SHA-256 08867037a0cd8320ed54f4da93f3558837035bf2cf6d7efbcd2560b3d6edfe3f</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/source/CassandraRegexTailReplayTest.kt`.

```kotlin
package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.fixtures.fixtureMarkDeclarations
import org.opentaint.dataflow.bidi.store.FlowBackedSummaries
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption
import kotlin.test.*

/** External source-only replay against actual fcfe AP/store code, never a project analysis. */
class CassandraRegexTailReplayTest {
    private val names=listOf("java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
        "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
        "java/security/xss.yaml:xss#sink#1;sink_50;$"+"<ARTIFICIAL>_4;3")
    private val fixture=StoreFixtures(markDeclarations=fixtureMarkDeclarations(names))
    private val m=fixture.manager
    private val ops=fixture.ops
    private val marks=names.map(fixture::mark)
    private val t=marks[2]
    private val arg=AccessPathBase.Argument(0)
    private val matcher=AccessPathBase.LocalVar(17)
    private val ret=AccessPathBase.Return
    private val group=m.accessors.index(FieldAccessor("java.util.regex.Matcher","group","java.lang.String"))
    private val content=m.accessors.index(FieldAccessor("java.lang.String","content","java.lang.CharSequence"))
    private val mx=m.markSetOf(marks[0]) + m.markSetOf(marks[1])
    private val flowInitial=m.initial(arg,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR)
    private val taintInitial=m.initial(arg,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.Concrete(t))
    private val mode=ApMode(true,Direction.FORWARD,1,markMode=MarkMode.FULL)

    private fun flow(tail:Tail,layer:Layer=Layer.DEMAND)=m.flowTree(ret,layer,ExclusionSet.Empty,mx,FlowAlgebra.LEAF_NODE,tail)
    private fun taint(tail:Tail,layer:Layer=Layer.DEMAND)=m.taintTree(ret,layer,
        m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,m.markSetOf(t))),anyTail=tail)
    private fun transfer(value:Facts,initial:InitialAp,from:AccessPathBase,fromPath:List<Int>,to:AccessPathBase,toPath:List<Int>):Facts {
        val out=CollectingOut()
        ops.applyEdge(value,initial,PathEdge(PathFact(from,fromPath,Tail.STAR,MarkSlot.STAR),
            PathFact(to,toPath,Tail.STAR,MarkSlot.STAR),ExclusionSet.Empty),false,mode,out)
        assertEquals(1,out.results.size);assertTrue(out.markRequests.isEmpty())
        return out.results.single()
    }
    private fun regex(value:Facts,initial:InitialAp):List<Facts> {
        val copied=transfer(value,initial,arg,emptyList(),matcher,listOf(group,content))
        val cut=CollectingOut();ops.limit(copied,1,cut)
        assertEquals(1,cut.results.size)
        val limited=cut.results.single()
        val returned=transfer(limited,initial,matcher,listOf(group),ret,emptyList())
        return listOf(value,copied,limited,returned)
    }
    private fun flagged(f:Facts)=(f as? TaintTree)?.nonSubsumable!=null
    private fun rows(f:Facts):List<Map<String,Any?>> = ops.leaves(f).map { p -> linkedMapOf<String,Any?>(
        "base" to  p.fact.base.toString(),"path" to  p.fact.path.map { m.accessors.accessor(it).toString() },
        "tail" to  p.fact.tail.name,"mark" to  p.fact.mark.toString(),"field_exclusion" to  p.exclusion.toString(),
        "layer" to  f.layer.name,"protected" to  flagged(f)) }.toList()
    private fun stored(owner:FlowBackedSummaries)=owner.all().map { (i,f)->mapOf("initial" to  i.toString(),"facts" to  rows(f)) }.toList()
    private fun record(name:String,data:Map<String,Any?>) {
        val dir=Path.of(checkNotNull(System.getProperty("opentaint.replay.output")));Files.createDirectories(dir)
        Files.writeString(dir.resolve("$name.json"),json(data)+"\n",StandardOpenOption.CREATE_NEW)
    }
    private fun json(value:Any?):String=when(value) {
        null->"null";is Number,is Boolean->value.toString()
        is Map<*,*>->value.entries.joinToString(",","{","}") { json(it.key.toString())+":"+json(it.value) }
        is Iterable<*>->value.joinToString(",","[","]") { json(it) }
        else->"\""+value.toString().replace("\\","\\\\").replace("\"","\\\"").replace("\n","\\n").replace("\r","\\r").replace("\t","\\t")+"\""
    }

    @Test fun `actual regex model field cut produces root ANY DEMAND`() {
        assertEquals(3,t.id)
        val input=m.flowTree(arg,Layer.NORMAL,ExclusionSet.Empty,mx,FlowAlgebra.LEAF_NODE,Tail.STAR)
        val trace=regex(input,flowInitial)
        val copied=trace[1] as FlowTree;val cut=trace[2] as FlowTree;val output=trace[3] as FlowTree
        assertEquals(Tail.STAR,copied.tail);assertEquals(Layer.NORMAL,copied.layer)
        assertEquals(listOf(group,content),ops.leaves(copied).single().fact.path)
        assertEquals(Tail.ANY,cut.tail);assertEquals(Layer.DEMAND,cut.layer)
        assertEquals(listOf(group),ops.leaves(cut).single().fact.path)
        assertEquals(ret,output.base);assertEquals(Tail.ANY,output.tail);assertEquals(Layer.DEMAND,output.layer)
        assertEquals(emptyList(),ops.leaves(output).single().fact.path);assertEquals(mx.ids.toList(),output.markExclusion.ids.toList())
        record("regex-field-cut",mapOf("checker" to "actual-fcfe-AP","mark_names_in_handle_order" to  names,
            "input_scope" to "The observed excluded marks1/2 are supplied on the operand to isolate geometry; their producer is not replayed.",
            "steps" to  trace.map(::rows),"historical_first_producer_claimed" to  false))
    }

    @Test fun `ANY first suppresses same-layer FLOW STAR but marked STAR survives`() {
        val input=m.flowTree(arg,Layer.NORMAL,ExclusionSet.Empty,mx,FlowAlgebra.LEAF_NODE,Tail.STAR)
        val any=regex(input,flowInitial).last() as FlowTree
        val owner=FlowBackedSummaries(m)
        assertNotNull(owner.add(flowInitial,any))
        val laterStar=flow(Tail.STAR)
        assertNull(owner.add(flowInitial,laterStar),"Existing ordinary FLOW ANY suppresses the later STAR offer in the same layer")
        assertNull(owner.add(taintInitial,taint(Tail.ANY)),"Unprotected diagonal ANY is covered")
        val marked=taint(Tail.STAR)
        assertNotNull(owner.add(taintInitial,marked),"Tail mismatch prevents concrete STAR replacement")
        assertEquals(setOf(Tail.ANY),owner.all().mapNotNull { (it.second as? FlowTree)?.tail }.toSet())
        val kept=owner.all().mapNotNull { it.second as? TaintTree }.single()
        assertEquals(Tail.STAR,kept.anyTail);assertNull(kept.nonSubsumable)
        assertEquals(1L,owner.census().concreteOutputMemberships)
        record("any-first-same-layer",mapOf("flow_any_admitted" to  true,"later_flow_star_admitted" to  false,
            "marked_any_admitted" to  false,"marked_star_admitted" to  true,"t_handle" to  t.id,"stored" to  stored(owner),
            "later_star_scope" to "A legal DEMAND STAR header is offered as an admission control; its producer is not claimed.",
            "historical_offer_order_claimed" to  false))
    }

    @Test fun `reverse order and different FLOW layer keep a usable STAR counterpart`() {
        val reverse=FlowBackedSummaries(m)
        assertNotNull(reverse.add(flowInitial,flow(Tail.STAR)))
        assertNotNull(reverse.add(flowInitial,flow(Tail.ANY)))
        assertEquals(setOf(Tail.STAR,Tail.ANY),reverse.all().mapNotNull { (it.second as? FlowTree)?.tail }.toSet())
        assertNull(reverse.add(taintInitial,taint(Tail.STAR)))
        assertNull(reverse.add(taintInitial,taint(Tail.ANY)))
        val crossLayer=FlowBackedSummaries(m)
        assertNotNull(crossLayer.add(flowInitial,flow(Tail.ANY,Layer.DEMAND)))
        assertNotNull(crossLayer.add(flowInitial,flow(Tail.STAR,Layer.NORMAL)))
        assertNull(crossLayer.add(taintInitial,taint(Tail.STAR)))
        val weak=FlowBackedSummaries(m)
        assertNotNull(weak.add(flowInitial,flow(Tail.STAR,Layer.DEMAND)))
        assertNotNull(weak.add(taintInitial,taint(Tail.STAR,Layer.NORMAL)),"DEMAND FLOW cannot cover a NORMAL marked relation")
        record("order-and-layer-controls",mapOf("reverse_order" to  stored(reverse),"demand_any_then_normal_star" to  stored(crossLayer),
            "weak_flow_normal_taint" to  stored(weak)))
    }

    @Test fun `actual cut and getter retain full protection and owner cannot erase or downgrade it`() {
        val input=m.taintTree(arg,Layer.DEMAND,m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,m.markSetOf(t))),anyTail=Tail.STAR)
        val trace=regex(input.withProtection(input.root),taintInitial)
        for(value in trace) {
            val tree=value as TaintTree
            assertEquals(tree.root,tree.nonSubsumable,"The complete protected payload must follow the real AP operation")
        }
        val output=trace.last() as TaintTree
        assertEquals(Tail.ANY,output.anyTail);assertEquals(ret,output.base)
        val owner=FlowBackedSummaries(m);owner.add(flowInitial,flow(Tail.ANY))
        assertNotNull(owner.add(taintInitial,output))
        assertNull(owner.add(taintInitial,output.withoutProtection()))
        val retained=owner.all().mapNotNull { it.second as? TaintTree }.single()
        assertEquals(retained.root,retained.nonSubsumable)
        assertEquals(1L,owner.census().protectedOutputMemberships)
        record("protected-field-cut",mapOf("steps" to  trace.map(::rows),"stored" to  stored(owner),
            "protected_memberships" to  owner.census().protectedOutputMemberships))
    }
}
```

</details>

<a id="inline-ap-replay-init"></a>
### Complete external Gradle init script

<details>
<summary>Full record; SHA-256 71f500c3e88d99a9f1d83a2fe317104390ae40476a1ec00678a7ec9bd3b02b2b</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/replay.init.gradle`.

```groovy
// External-only AP fixture. Source and compiled outputs remain outside the worktree.
def replayRoot = new File('/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay')
def outputDir = System.getProperty('opentaint.replay.attempt')
assert outputDir != null
gradle.projectsEvaluated {
    def p = rootProject.findProject(':opentaint-dataflow-core:opentaint-dataflow')
    if (p == null && rootProject.name == 'opentaint-dataflow-core') p = rootProject.findProject(':opentaint-dataflow')
    if (p == null) return
    println('AP_REPLAY_ATTACH root=' + rootProject.name + ' project=' + p.path + ' output=' + outputDir)
    def existingFixtures = new File(replayRoot, 'fixture-cache')
    assert new File(existingFixtures, 'org/opentaint/dataflow/bidi/fixtures/StoreFixtures.class').isFile()
    p.kotlin.sourceSets.getByName('test').kotlin.setSrcDirs([new File(replayRoot, 'source')])
    p.sourceSets.getByName('test').java.setSrcDirs([])
    p.tasks.named('compileTestKotlin').configure {
        destinationDirectory.set(new File(outputDir, 'classes'))
        libraries.from(p.files(existingFixtures))
    }
    p.tasks.named('test').configure {
        maxHeapSize = '1g'
        outputs.upToDateWhen { false }
        testClassesDirs = p.files(new File(outputDir, 'classes'))
        classpath = p.files(new File(outputDir, 'classes'), existingFixtures) + classpath
        systemProperty 'opentaint.replay.output', new File(outputDir, 'controls').absolutePath
        reports.junitXml.outputLocation.set(new File(outputDir, 'xml'))
        reports.html.outputLocation.set(new File(outputDir, 'html'))
        binaryResultsDirectory.set(new File(outputDir, 'binary'))
        doFirst {
            def activeProject = new File('/proc').listFiles().findAll { it.name ==~ /[0-9]+/ }.findAll { entry ->
                try {
                    if (java.nio.file.Files.readSymbolicLink(entry.toPath().resolve('exe')).fileName.toString() != 'java') return false
                    return new String(new File(entry, 'cmdline').bytes).contains('org.opentaint.jvm.sast.runner.ProjectAnalyzerRunner')
                }
                catch (IOException ignored) { return false }
            }
            assert activeProject.isEmpty(): 'Do not overlap a project analyzer; preserve this setup failure before retrying.'
        }
    }
}
```

</details>

<a id="inline-ap-xml-1"></a>
### Complete replay JUnit XML

<details>
<summary>Full record; SHA-256 6742208f6f891530e9e9127b4ad45cbb45bd704ecb22f72cf0bd378a3998145b</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/cassandra-regex-ap-replay/attempt-232933/xml/TEST-org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest.xml`.

```xml
<?xml version="1.0" encoding="UTF-8"?>
<testsuite name="org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest" tests="4" skipped="0" failures="0" errors="0" timestamp="2026-10-26T23:30:09" hostname="dev-1" time="0.254">
  <properties/>
  <testcase name="actual cut and getter retain full protection and owner cannot erase or downgrade it()" classname="org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest" time="0.214"/>
  <testcase name="reverse order and different FLOW layer keep a usable STAR counterpart()" classname="org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest" time="0.01"/>
  <testcase name="actual regex model field cut produces root ANY DEMAND()" classname="org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest" time="0.013"/>
  <testcase name="ANY first suppresses same-layer FLOW STAR but marked STAR survives()" classname="org.opentaint.dataflow.bidi.CassandraRegexTailReplayTest" time="0.007"/>
  <system-out><![CDATA[]]></system-out>
  <system-err><![CDATA[]]></system-err>
</testsuite>
```

</details>

<a id="inline-capture-controls"></a>
## Recorded commands and census controls

The next records give the exact project commands and JVM options for both fixed four-project diagnostic cohorts. These times are not the timed performance results. The inline data can repeat all table arithmetic without a campaign directory. To rerun a capture or replay, use the pinned source/model bindings and map recorded absolute work paths to local paths. No heap or timeout change is implied.

<a id="inline-command-before-thingsboard"></a>
### Complete before thingsboard invocation manifest

<details>
<summary>Full record; SHA-256 44d6e6de74b0e73607df8db7c049e329f3114fa2a5d1cc66b54a9f52f333ecec</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/manifest.json`.

```json
{
  "project": "thingsboard",
  "side": "bidi",
  "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
  "patch_sha256": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
    "memory": "12g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx12g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/thingsboard/bidi/manifest.json"
  ],
  "started_utc": "2026-10-26T23:39:54Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "8987ba4b0975ce1d089f706e9e07e2ed46e4c498ba7752e3f5e92f2144719882",
  "analyzer_started_elapsed": 16.46367257833481
}
```

</details>

<a id="inline-command-before-conductor"></a>
### Complete before conductor invocation manifest

<details>
<summary>Full record; SHA-256 3951f18782122720dabb5f583bb44eda249ddb67720eacf659180e605caf2f62</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/manifest.json`.

```json
{
  "project": "conductor",
  "side": "bidi",
  "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
  "patch_sha256": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
    "memory": "8g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/projects/extensions/conductor/rules",
    "--passthrough-approximations",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/projects/extensions/conductor/passthrough",
    "--java-dataflow-approximations",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/dataflow-compiled",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/conductor/bidi/manifest.json"
  ],
  "started_utc": "2026-10-27T00:00:13Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "f1c067a682af5cc4b9379171d9ee4e2d2347c197d0a2e6ac05063964f080c889",
  "analyzer_started_elapsed": 5.101739808917046
}
```

</details>

<a id="inline-command-before-stirling-pdf"></a>
### Complete before Stirling-PDF invocation manifest

<details>
<summary>Full record; SHA-256 a458128c467492f4cc07f35d90bde2ef5f7e7b4026258f2bca47423a47b592d9</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/manifest.json`.

```json
{
  "project": "Stirling-PDF",
  "side": "bidi",
  "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
  "patch_sha256": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
    "memory": "8g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/Stirling-PDF/bidi/manifest.json"
  ],
  "started_utc": "2026-10-27T00:03:25Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "ff389b7364b2612ac3aba4ae94c4594869ca309cb5303c02adb4a41b79dc4ce4",
  "analyzer_started_elapsed": 4.089144170284271
}
```

</details>

<a id="inline-command-before-owasp"></a>
### Complete before OWASP invocation manifest

<details>
<summary>Full record; SHA-256 62f0e4fb74d259b0e04ecfb4786a8b43bbb74ddf44fc1a83470225dfeb108878</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/manifest.json`.

```json
{
  "project": "OWASP",
  "side": "bidi",
  "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
  "patch_sha256": "34d51b27c40f4e32ce5e9cf2c315d79e548b83993caa8f558a008b9e4f0887a7",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
    "memory": "8g",
    "timeout": 1000,
    "outer_timeout": 1200
  },
  "model_sha256": "e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/reports",
    "--ifds-analysis-timeout",
    "1000",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-shape-probe-results/OWASP/bidi/manifest.json"
  ],
  "started_utc": "2026-10-27T00:05:57Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "3035eef4b38022dad302539584d47b88bab8ded95548051f8aab9b946fe8f44f",
  "analyzer_started_elapsed": 4.0740179270505905
}
```

</details>

<a id="inline-command-after-thingsboard"></a>
### Complete after thingsboard invocation manifest

<details>
<summary>Full record; SHA-256 6229ecfb67891c062c2395ae31fe77a98f66e59577aed7a056414f162e774648</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/manifest.json`.

```json
{
  "project": "thingsboard",
  "side": "bidi",
  "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "patch_sha256": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
    "memory": "12g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx12g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/thingsboard/bidi/manifest.json"
  ],
  "started_utc": "2026-10-26T21:41:47Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "a74f5a4927f567a9f1d34381fbf8846199420ff7599cb6805b424fca58558ee5",
  "analyzer_started_elapsed": 3.029678598046303
}
```

</details>

<a id="inline-command-after-conductor"></a>
### Complete after conductor invocation manifest

<details>
<summary>Full record; SHA-256 c7db5b79b5b829fb89f839cde8c68ba80404466857f0582ed72c8f1a06616f02</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/manifest.json`.

```json
{
  "project": "conductor",
  "side": "bidi",
  "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "patch_sha256": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
    "memory": "8g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/opentaint-project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/projects/extensions/conductor/rules",
    "--passthrough-approximations",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/projects/extensions/conductor/passthrough",
    "--java-dataflow-approximations",
    "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-conductor/dataflow-compiled",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/conductor/bidi/manifest.json"
  ],
  "started_utc": "2026-10-26T21:59:53Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "9333cce649944c662ac47b0caefa59c4493e7525175877ab1bc885e706e90a20",
  "analyzer_started_elapsed": 3.071905791759491
}
```

</details>

<a id="inline-command-after-stirling-pdf"></a>
### Complete after Stirling-PDF invocation manifest

<details>
<summary>Full record; SHA-256 9ea54005c6a11d55bdcb91c4a359a2e6b22c467391e46dac7a950cc8a2a0ea07</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/manifest.json`.

```json
{
  "project": "Stirling-PDF",
  "side": "bidi",
  "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "patch_sha256": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
    "memory": "8g",
    "timeout": 1080,
    "outer_timeout": 1200
  },
  "model_sha256": "b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/e2e-root/model-Stirling-PDF/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/reports",
    "--ifds-analysis-timeout",
    "1080",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--sarif-semgrep-style-id",
    "--semgrep-rule-severity",
    "warning",
    "--semgrep-rule-severity",
    "error",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/Stirling-PDF/bidi/manifest.json"
  ],
  "started_utc": "2026-10-26T22:02:50Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "a703b500f31a9e8317f2fadd1bda879217d6cccd21bdb39abf0238b0069ad407",
  "analyzer_started_elapsed": 4.078438624739647
}
```

</details>

<a id="inline-command-after-owasp"></a>
### Complete after OWASP invocation manifest

<details>
<summary>Full record; SHA-256 4727e8f9a704b543dfd3ac843a09c6c35c4846576f35d43e6437258ba07f3ba7</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/manifest.json`.

```json
{
  "project": "OWASP",
  "side": "bidi",
  "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "patch_sha256": "756213f1151b87e801a71cf636d366293829992b1cc0c2bd239462f7c31fec6e",
  "config": {
    "model": "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
    "memory": "8g",
    "timeout": 1000,
    "outer_timeout": 1200
  },
  "model_sha256": "e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873",
  "command": [
    "./gradlew",
    ":runProjectAnalyzer",
    "--console=plain",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/benchmark.init.gradle",
    "-x",
    ":opentaint-ir:go:buildGoServer"
  ],
  "runner_args": [
    "--project",
    "/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/project/project.yaml",
    "--output-dir",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/reports",
    "--ifds-analysis-timeout",
    "1000",
    "--logs-file",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/analyzer.log",
    "--verbosity",
    "debug",
    "--semgrep-rule-set",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/diagnostic-source/rules/ruleset",
    "--sarif-generate-fingerprint",
    "--ifds-bidirectional"
  ],
  "test_revision": "bbdbcc5fd35d976d93348760ea60561e4670f68c",
  "guard_heap_snapshot": true,
  "form_statistics": true,
  "optimization_statistics": true,
  "run1_mark_mode": "FULL",
  "analyzer_jvm_args": [
    "-Xmx8g",
    "-Dorg.opentaint.ir.impl.storage.defaultBatchSize=2000",
    "-Djdk.util.jar.enableMultiRelease=false",
    "-XX:FlightRecorderOptions=stackdepth=256",
    "-XX:StartFlightRecording=filename=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/continuous.jfr,settings=profile,dumponexit=true,maxsize=256m",
    "-Xlog:gc*:file=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/gc.log:time,uptime,level,tags:filecount=0",
    "-Dopentaint.memorySnapshotDir=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi",
    "-XX:+HeapDumpOnOutOfMemoryError",
    "-XX:HeapDumpPath=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/jvm-oom.hprof",
    "-Dopentaint.bidi.run1MarkMode=FULL",
    "-Dopentaint.bidi.disableRun1Statics=false",
    "-Dorg.opentaint.bidi.formStatistics=true",
    "-Dorg.opentaint.bidi.optimizationStatistics=true",
    "-Dopentaint.diagnostic.run1Shapes=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/shapes",
    "-Dopentaint.diagnostic.configManifest=/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/shape-probe-results/OWASP/bidi/manifest.json"
  ],
  "started_utc": "2026-10-26T22:05:19Z",
  "analyzer_executable": "/usr/lib/jvm/java-17-openjdk-amd64/bin/java",
  "analyzer_command_sha256": "877d918c0773d652151750c9cae850bc1c55e0bf106a9f23ac2905e78be7d577",
  "analyzer_started_elapsed": 4.093544825911522
}
```

</details>

<a id="inline-census-control-before"></a>
### Complete before census-control receipt

<details>
<summary>Full record; SHA-256 8bd44f2d77134eaf3ea65091d6ea28f0568f9d95b88730e1fc67fdf2e181cac1</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/terminal.json`.

```json
{
  "state": "PASS",
  "started_utc": "2026-10-26T23:19:33.348918+00:00",
  "command": [
    "./gradlew",
    ":opentaint-dataflow-core:opentaint-dataflow:test",
    "--tests",
    "org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest",
    "--console=plain",
    "--no-daemon",
    "--max-workers=2",
    "-Pkotlin.compiler.execution.strategy=in-process",
    "-Dorg.gradle.jvmargs=-Xmx2g",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/preparation/test-protoc.init.gradle",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/preparation/fresh-tests.init.gradle"
  ],
  "cwd": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/baseline-diagnostic-source/core",
  "mem_available_bytes": 46951464960,
  "source": {
    "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
    "core_tree": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
    "tracked_patch_sha256": "a4ad2f865e7ffae6f023b4ed756435e88c3d48c35fc94fb4fca54e9b48064af0",
    "added_sources": {
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineRun1ShapeCensus.kt": "248de77d94e78778b85a20ba412098cef7e7e95a9cd5bb9d7d734d23c8537933",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c"
    }
  },
  "full_patch_sha256": "4023b60c65f5d8223b082a5d2d92fe47c61eb47030595b1ea7a567d67ecde20c",
  "full_patch": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/attempt-231933/source.patch",
  "unchanged_old_coverage_policy": {
    "ap/FlowBackedCoverage.kt": "c5d6a2f4f90260ebb58c1eb12a0171d39cfdca8aa7f11f60d9340745d9c3aa92",
    "ap/Run1SummaryAliases.kt": "0ded987b2384ea6cd48d89fb1ebca98c4ac3b724afedfc8b88c860ba92528d6c",
    "store/FlowBackedSummaries.kt::normalize": "c6b25a3dd928ad3833ec064afad8cb6f9f97e5093df2070338de0b5c55b7ff76"
  },
  "installed_manifest_sha256": "1146fcf1254badf3f01adb774926d53b4ff718c2e4310153a0a1668b81d7d9fa",
  "helper_sha256": {
    "tools/test_baseline_shape_probe.py": "6eedc2d5cece014a1459ea586c8f37762f414f2342da5514716eaf1f87d5c14a",
    "tools/BaselineRun1ShapeCensus.kt": "fc8385381998132a562bcdde8881df0b1ce3cef411fcadcea8c9e0e5a9ecb184",
    "tools/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c",
    "tools/install_baseline_shape_probe.py": "82dbfc43be2da33fd90a57829b912729ee2dd4b4fbf893cd955008291ef56c41",
    "tools/run_baseline_shape_campaign.py": "ee62a87debdde99b665ef9ce5d126b77d6714d3c7d55e7ad5138a217225901f9"
  },
  "ended_utc": "2026-10-26T23:23:13.079302+00:00",
  "returncode": 0,
  "source_unchanged": true,
  "totals": {
    "tests": 5,
    "failures": 0,
    "errors": 0,
    "skipped": 0
  },
  "fresh_xml": [
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/attempt-231933/fresh-xml/TEST-org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest.xml",
      "sha256": "0dbe9fd58cca3194af8c9fbaac0c1da72fbc076435fb997d722733024115be64"
    }
  ],
  "log_sha256": "8745a47d792829e64fc9b59788db966925ff8e72118d133c2d34d26f6cd53e3a",
  "attempt": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/attempt-231933"
}
```

</details>

<a id="inline-census-xml-before-1"></a>
### Complete before census JUnit XML

<details>
<summary>Full record; SHA-256 0dbe9fd58cca3194af8c9fbaac0c1da72fbc076435fb997d722733024115be64</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/attempt-231933/fresh-xml/TEST-org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest.xml`.

```xml
<?xml version="1.0" encoding="UTF-8"?>
<testsuite name="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" tests="5" skipped="0" failures="0" errors="0" timestamp="2026-10-26T23:23:11" hostname="dev-1" time="0.595">
  <properties/>
  <testcase name="old ANY policy partitions protected other and removal events without mutating the relation()" classname="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" time="0.249"/>
  <testcase name="actual joined manager freezes actors then driver scans and completes report and handoff before stopping()" classname="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" time="0.324"/>
  <testcase name="different complete FLOW headers cannot synthesize one coverage witness()" classname="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" time="0.006"/>
  <testcase name="old alias identity guard remains authoritative even with spatial ANY coverage()" classname="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" time="0.006"/>
  <testcase name="baseline ANY-only coverage does not acquire STAR or EXACT coverage()" classname="org.opentaint.dataflow.bidi.BaselineRun1ShapeCensusTest" time="0.004"/>
  <system-out><![CDATA[]]></system-out>
  <system-err><![CDATA[SLF4J: No SLF4J providers were found.
SLF4J: Defaulting to no-operation (NOP) logger implementation
SLF4J: See https://www.slf4j.org/codes.html#noProviders for further details.
]]></system-err>
</testsuite>
```

</details>

<a id="inline-census-control-after"></a>
### Complete after census-control receipt

<details>
<summary>Full record; SHA-256 89c0f92102dd112c2ca796daef937fa43d6201d756ab2c6dd0102439b59de4ff</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/shape-probe/terminal.json`.

```json
{
  "state": "PASS",
  "ended_utc": "2026-10-26T20:28:01.106081+00:00",
  "command": [
    "./gradlew",
    ":opentaint-dataflow-core:opentaint-dataflow:test",
    "--tests",
    "org.opentaint.dataflow.bidi.Run1ShapeCensusTest",
    "--console=plain",
    "--no-daemon",
    "--max-workers=2",
    "-Pkotlin.compiler.execution.strategy=in-process",
    "-Dorg.gradle.jvmargs=-Xmx2g",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/preparation/test-protoc.init.gradle",
    "-I",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/preparation/fresh-tests.init.gradle"
  ],
  "returncode": 0,
  "source": {
    "revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
    "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
    "tracked_patch_sha256": "425b82dda902da61b63cf05a5aa0aeed17bc356a79f3c743565cd10417bb2a06",
    "added_sources": {
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/Run1ProcessedWorkCounters.kt": "b0a9b39ccaacd051cfc37c6e546d0c7d674d1e792e347498f79928f5b8bcb598",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1ShapeCensus.kt": "aaf5d26850604bf87e1993c7d526acaffe4965c69ebb7ced4875465dbf9a83f4",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1TargetMethodDump.kt": "3b06173bc20b6eb123987e02178f996085af042b68a2cc29339d0b190061b93c",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/Run1ShapeCensusTest.kt": "c6083507f726afeef3232360fa5d40902181fe3a1ffe12204b4525482f83bf2c"
    }
  },
  "source_unchanged": true,
  "full_patch_sha256": "f24ef62919ed1864d7d05042d2abe73f700950ac5687f667e17495805359963f",
  "log_sha256": "8005f7a1383d6440ab88e4227698c01e1e81089f6394388cfba6b2983aaf2e1a",
  "fresh_xml": [
    {
      "path": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/shape-probe/attempt-202507/xml/TEST-org.opentaint.dataflow.bidi.Run1ShapeCensusTest.xml",
      "sha256": "4ecb251357b9f14055ad340fe7b23c6703537c08806e97bc8bbcc6c6836639a5"
    }
  ],
  "totals": {
    "tests": 7,
    "failures": 0,
    "errors": 0,
    "skipped": 0
  },
  "attempt": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/shape-probe/attempt-202507"
}
```

</details>

<a id="inline-census-xml-after-1"></a>
### Complete after census JUnit XML

<details>
<summary>Full record; SHA-256 4ecb251357b9f14055ad340fe7b23c6703537c08806e97bc8bbcc6c6836639a5</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/shape-probe/attempt-202507/xml/TEST-org.opentaint.dataflow.bidi.Run1ShapeCensusTest.xml`.

```xml
<?xml version="1.0" encoding="UTF-8"?>
<testsuite name="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" tests="7" skipped="0" failures="0" errors="0" timestamp="2026-10-26T20:28:00" hostname="dev-1" time="0.288">
  <properties/>
  <testcase name="untouched counters distinguish packed decode from scalar and pure callbacks()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.121"/>
  <testcase name="distinct FLOW leaves and headers cannot form a synthetic coverage witness()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.031"/>
  <testcase name="full identity structural and partial protection are distinct read-only partitions()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.011"/>
  <testcase name="processed work counters partition origins without expanding masks or trees()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.004"/>
  <testcase name="read-only repeated census gives equal partitions and exact nonhistorical events()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.014"/>
  <testcase name="an unflagged ANY parent sample includes its protected exact descendant witness()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.005"/>
  <testcase name="actual process packed and resume hooks reconcile without observer fallback()" classname="org.opentaint.dataflow.bidi.Run1ShapeCensusTest" time="0.095"/>
  <system-out><![CDATA[]]></system-out>
  <system-err><![CDATA[SLF4J: No SLF4J providers were found.
SLF4J: Defaulting to no-operation (NOP) logger implementation
SLF4J: See https://www.slf4j.org/codes.html#noProviders for further details.
]]></system-err>
</testsuite>
```

</details>

<a id="inline-baseline-seal"></a>
### Complete baseline source/control seal

<details>
<summary>Full record; SHA-256 226b05d94ec192c77fc0b7335dc08907433c1b166a1723a580eeae4626bfa724</summary>

Original source label: `/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/prepared.json`.

```json
{
  "state": "PREPARED_TESTED_NOT_LAUNCHED",
  "created_utc": "2026-10-26T23:24:10.833065+00:00",
  "source": {
    "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
    "core_tree": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
    "tracked_patch_sha256": "a4ad2f865e7ffae6f023b4ed756435e88c3d48c35fc94fb4fca54e9b48064af0",
    "added_sources": {
      "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineRun1ShapeCensus.kt": "248de77d94e78778b85a20ba412098cef7e7e95a9cd5bb9d7d734d23c8537933",
      "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c"
    }
  },
  "full_patch_sha256": "4023b60c65f5d8223b082a5d2d92fe47c61eb47030595b1ea7a567d67ecde20c",
  "full_patch": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/attempt-231933/source.patch",
  "test_receipt": "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/validation/baseline-shape-probe/terminal.json",
  "test_receipt_sha256": "8bd44f2d77134eaf3ea65091d6ea28f0568f9d95b88730e1fc67fdf2e181cac1",
  "tests": {
    "tests": 5,
    "failures": 0,
    "errors": 0,
    "skipped": 0
  },
  "policy_checker": "baseline-any-alias-guard-v1",
  "old_policy_byte_checks": {
    "ap/FlowBackedCoverage.kt": "c5d6a2f4f90260ebb58c1eb12a0171d39cfdca8aa7f11f60d9340745d9c3aa92",
    "ap/Run1SummaryAliases.kt": "0ded987b2384ea6cd48d89fb1ebca98c4ac3b724afedfc8b88c860ba92528d6c",
    "store/FlowBackedSummaries.kt::normalize": "c6b25a3dd928ad3833ec064afad8cb6f9f97e5093df2070338de0b5c55b7ff76"
  },
  "artifacts": {
    "tools/install_baseline_shape_probe.py": "82dbfc43be2da33fd90a57829b912729ee2dd4b4fbf893cd955008291ef56c41",
    "tools/BaselineRun1ShapeCensus.kt": "fc8385381998132a562bcdde8881df0b1ce3cef411fcadcea8c9e0e5a9ecb184",
    "tools/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c",
    "tools/test_baseline_shape_probe.py": "6eedc2d5cece014a1459ea586c8f37762f414f2342da5514716eaf1f87d5c14a",
    "tools/run_baseline_shape_campaign.py": "ee62a87debdde99b665ef9ce5d126b77d6714d3c7d55e7ad5138a217225901f9",
    "preparation/baseline-shape-probe-campaign-plan.json": "0946aae747a36712a7cdb40409178f8dc683529d7f67cbed56b2dbb135be6ac9",
    "validation/baseline-shape-probe/cassandra-replay-plan.json": "95b9acbf086aeea50d5350c7de2beffe4742c85008bece9347efff60663f4475",
    "validation/baseline-shape-probe/cassandra-GettableByIndex.javap.txt": "165fca1aa0ebeee48f001dfc9f4c426dd3e55de4e6b3f777b24bbe8456d5e51c"
  },
  "production_revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "production_core_rules_patch_empty": true,
  "post_test_tool_change": "No post-test source change. Authorized cold actor census, driver call and existing test extensions were compiled and passed; old coverage/normalize/alias code remains byte-identical. Earlier sealed gate/manifest preserved in before-cold-actor-extension.",
  "launch_command": [
    "python3",
    "/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026/tools/run_baseline_shape_campaign.py"
  ],
  "launch_authority": "Parent only, after final-heap-campaign CLOSED; no project analyzers were launched by this task.",
  "cold_actor_work": {
    "version": "run1-work-cold-actors-v1",
    "fields": [
      "actors",
      "steps",
      "neutralBatchApplications",
      "neutralBatchMemberships"
    ],
    "physical_formula": "steps - neutralBatchMemberships + neutralBatchApplications",
    "top_method_rows": 40,
    "scope": "Joined/frozen actor numeric reads only; no hot observer, counter, event archive, context/form/point read.",
    "tests": "Existing five-control gate checks positive arithmetic/top40 bound and the actual joined/frozen actor sums in the complete driver lifecycle."
  }
}
```

</details>

## Verify the inline arithmetic

Run this local check from the report directory. It reads this Markdown file only. It checks all 16 before/after owner partitions and all 17 complete examples. It starts no analyzer and needs no original capture directory.

```python
from pathlib import Path
import json

text = Path("bidirectional-correlated-concrete-run1-shapes-20261026.md").read_text()
def inline_json(anchor):
    section = text.split(f'<a id="{anchor}"></a>', 1)[1]
    return json.loads(section.split("```json\n", 1)[1].split("\n```", 1)[0])

comparison = inline_json("inline-comparison-data")
assert comparison["projects_with_both_valid_censuses"] == 4
for project in comparison["projects"].values():
    for side in ("before", "after"):
        capture = project[side]
        assert capture["latest_reached"] == "run-1"
        assert capture["latest_completed"] == "run-1"
        assert capture["latest_accepted_forward"] == "run-1"
        for owner in capture["owners"].values():
            assert sum(owner["coverage"].values()) == owner["TAINT_memberships"]
            assert owner["coverage"]["removable_now"] == 0
            assert sum(owner["primary_other_reasons"].values()) == owner["coverage"]["other"]
            assert sum(owner["TAINT_full_shape_histogram"].values()) == owner["TAINT_memberships"]
            assert sum(owner["FLOW_full_shape_histogram"].values()) == owner["FLOW_memberships"]
for number in range(1, 18):
    record = inline_json(f"example-{number:02d}-record")
    assert record["flow_candidates_truncated"] is False
    assert record["protection_mask_truncated"] is False
print("16 owner partitions and all 17 complete examples verified")
```

The data preserve source and invocation identity. An outer timeout is not a successful export. An ordinary FLOW tail is not a correlated concrete tail. The dominant protected-matrix producer is still unknown. No runtime code, configuration or experiment changed when this report was assembled.
