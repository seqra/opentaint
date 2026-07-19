# BaseOnly E2E correctness and performance investigation

Date: 2026-07-17

Compared analyzers:

- Tree/base: `41d13abadcf7f4a4e2494a468ddf51f9a3985d3e`
- BaseOnlyField/new: `2100fe3b090667149cfd924fd098e5c336700830`
- project revisions: `seqra/opentaint-test:projects/repos.yaml` at the time of the run

## Executive result

The report has 65 removed SARIF results in five projects after excluding the two autobuilder-only rows (`CordysCRM` and `shopizer`). They do **not** represent 65 independently proven access-path regressions.

| project | removed | forward/trace classification | evidence/root |
|---|---:|---|---|
| Stirling-PDF | 1 | exact-project diagnostic: forward-present, then trace-filtered | reproduced `BaseOnlyAccessOps.splitDelta`/`suffixExcluded` bug; July 17 aggregate log does not name filtered candidates |
| spring-petclinic | 2 | absent from forward storage | one shared `Integer getId()` flow, intentionally rejected by the primitive/boxed-primitive policy |
| conductor | 3 | absent from the partial forward candidate set | F2F-summary-storage crash stopped forward analysis; semantic cause of removals unproven |
| thingsboard | 1 | indeterminate | forward IFDS timed out; two unnamed trace jobs remained unfinished when trace resolution timed out |
| tms | 58 | 33 pattern-only absent; 25 dataflow items indeterminate individually | run invalidated by the same BaseOnly F2F-summary-storage crash; four unnamed candidates were trace-filtered |

The confirmed semantic access-path regression is the Stirling trace transition reproduced on the exact project revision. The Petclinic difference is expected under the explicit primitive policy. The other 62 removals are evidence that incomplete scans must not be compared as semantic result sets. Four status-regression projects (`apollo`, `conductor`, `klaw`, `tms`) expose the same fastutil iterator-corruption symptom in two BaseOnly summary-storage implementations; ThingsBoard instead times out.

## How the stage boundary was established

`TaintAnalyzer - Total vulnerabilities: N` is emitted after the forward runner terminates (normally, by timeout, or exceptionally) and vulnerability confirmation, but before trace generation. `Filter out N vulnerabilities without traces` is emitted after trace resolution/path generation. The final SARIF omits filtered candidates and does not retain their identities. Consequently:

- a result named by an instrumented pre-trace diagnostic is forward-present;
- `Total vulnerabilities: 0` proves there was no trace candidate;
- aggregate `Filter out N` alone cannot identify which sinks were filtered;
- any comparison whose new status is `incomplete` is not a complete result-set comparison.

## 1. Stirling-PDF: confirmed trace-resolution operation bug

### Removed vulnerability

- rule: `java.security.xss-in-spring-app`
- sink: `app/core/src/main/java/stirling/software/SPDF/controller/api/security/GetInfoOnPDF.java:992-995`
- base source/sink fingerprint: `PSwjpS6bPFOko+dQgotUB8dh7Rz9FqJnLlpqig0C2RI=`

The Tree trace is:

```text
getPdfInfo(PDFFile request) entry: request[$UNTRUSTED]       GetInfoOnPDF.java:472
  -> request.getFileInput()                                  :473
  -> PDFFile.getFileInput(): this.fileInput                  PDFFile.java:24
  -> local inputFile / %830
  -> bytesToWebResponse(%830, "response.json", mediaType)     GetInfoOnPDF.java:992
  -> bytesToWebResponse arg(0) bytes                         WebResponseUtils.java:45
  -> ResponseEntity Body carries bytes                       :58
  -> getPdfInfo return / Spring sink_35
```

The new run has 88 pre-trace candidates, filters 48 and writes 40. A diagnostic on the exact Stirling project revision reproduces this removed sink and names it as a candidate rejected in `MethodTraceResolver`, strongly attributing the difference to trace reconstruction. The temporary diagnostic did not persist its analyzer hash, so the aggregate July 17 log alone does not identify this specific one of the 48 filtered candidates.

### Exact failing statement, facts and operation

Statement:

```text
GetInfoOnPDF#getPdfInfo:992
%832 = WebResponseUtils.bytesToWebResponse(%830, "response.json", %831)
```

Facts at the call boundary (unrelated exclusions abbreviated as `E`):

```text
backward/caller fact:
  var(832)![java/security/xss.yaml:xss-in-spring-app;sink_35;$<ARTIFICIAL>_6;5].$

stored pass-summary final mapped to caller:
  var(832).Body.*/E

stored pass-summary initial:
  arg(0).*/E

important exclusion:
  sink_35 is a member of E
```

Call chain:

```text
MethodTraceResolver.resolveCallPassSummary
  -> callerFact.splitDelta(mappedSummaryFinal)
  -> BaseOnlyFinalFactAp.delta
  -> BaseOnlyAccessOps.splitDelta
  -> BaseOnlyApManager.suffixExcluded
```

Current behavior in `BaseOnlyAccessOps.splitDelta`:

1. `splitConcreteInitial(var832.Body.*, var832![sink_35].$)` accepts the field-compatible open summary.
2. It projects `![sink_35].$` as the concrete delta.
3. `suffixExcluded(delta, E)` sees `sink_35` in the summary exclusions.
4. `splitDelta` returns `[]`.
5. Trace resolution cannot map the result fact on `%832` back to input `%830`; the candidate is filtered.

This is internally inconsistent: the open `.Body.*` summary has already accepted the concrete caller fact, but a pass-summary structural exclusion is then applied to the semantic sink label required only to reconstruct the trace.

Expected result:

```text
splitDelta(...) = [
  matched = var(832).Body.*,
  delta   = BaseOnlyNodeInitialDelta(![sink_35].$)
]
```

Mapping `arg(0).*` back to `%830` and concatenating this delta preserves `sink_35`, after which the resolver can follow `%830` through `getFileInput` to the method-entry source. The fix must distinguish trace-carried semantic marks from structural suffixes excluded by the forward summary.

Diagnostic evidence: `/tmp/stirling-diag2.log:891` and `/tmp/stirling-target-ops.txt` in the investigation environment. Persistent inputs are `run-debug/result-Stirling-PDF-{base,new}` and `run-debug/regression-diff/diff/Stirling-PDF.json`.

### Minimal regression test

`BaseOnlyApDeltaConcatTest` now pins both representations at the exact failing call boundary, without depending on Spring classes. The Tree case retains the union that was present in the production Tree summary:

```text
summary = Body.* | ![sink_35].$
caller  = ![sink_35].$
result  = one matching split with an empty delta
```

The corresponding BaseOnly normalization is:

```text
fact       = ![sink_35].$
pattern    = Body.*
exclusions = { sink_35 }
expected   = [(Body.*, delta=![sink_35].$)]
actual     = []
```

The Tree test passes. The BaseOnly test asserts semantic equivalence and fails because `splitDelta` returns `[]`, proving that the lossy normalized representation rejects the trace-only semantic branch. The earlier Spring-free end-to-end sample was removed: it generated an additional concrete `arg(untrusted) -> result(sink_35)` summary and therefore did not reproduce the production rejection.

Narrow command:

```bash
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests '*BaseOnlyApDeltaConcatTest.Tree resolves*' \
  --no-daemon --max-workers=1

./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests '*BaseOnlyApDeltaConcatTest.BaseOnly resolves*' \
  --no-daemon --max-workers=1
```

## 2. spring-petclinic: two results, one intentional primitive flow

Removed results:

- `java.security.xss-in-spring-app`, `OwnerController.java:86`, fingerprint `onTQDIQvHLpmcSNIaK1DQ3vfrIa3xYNcZYVuakvcexw=`
- `java.security.unvalidated-redirect-in-spring-app`, `OwnerController.java:86`, fingerprint `wZQJdS0kYXhgX3Ck3v76OEl1Xlz7GpfA90pkBpI68dc=`

They are two rule joins over the same Tree flow:

```text
OwnerController.processCreationForm(owner) entry: owner[$UNTRUSTED]   line 78
  -> owner.getId()                                                    line 86
  -> BaseEntity.getId(): return this.id                               lines 40-41
  -> return "redirect:/owners/" + id                                  line 86
```

`BaseEntity.id` and `getId()` have type `java.lang.Integer`. Tree reports two candidates. BaseOnly reports `Total vulnerabilities: 0`; no candidate reaches trace generation. Method statistics agree: Tree records six pass-summary applications for `getId`, BaseOnly records zero.

At the summary boundary, the whole receiver fact is compared with the getter relation for `this.id`. `BaseOnlyAccessOps.covers`/`matchPrefix` does not create a delta when the concrete receiver has no value in the committed field slot. Independently, `JIRFactTypeChecker.AccessorFilter` rejects a `TaintMarkAccessor` when `actualType.unboxIfNeeded()` is primitive unless the rule explicitly enables `%%primitive%%` tracking. Neither security join enables it.

Current and expected behavior under the stated policy are therefore the same:

```text
input:    owner![UNTRUSTED].$
getter:   this.id -> Integer return
actual:   no marked Integer fact
expected: no marked Integer fact (primitive/boxed-primitive facts are forbidden)
```

These are not BaseOnly correctness regressions. They should be excluded from the overapproximation oracle or the primitive policy must be changed for both representations.

## 3. BaseOnly summary-storage iterator crashes

### Affected runs

The same exception makes four new scans incomplete:

| project | new status | comparison effect |
|---|---|---|
| apollo | `incomplete` | side-effect-summary (`SEStorage`) crash; no removed final results, but not a valid completion |
| conductor | `high_memory,incomplete` | F2F-summary crash; three Tree findings absent from partial forward candidates |
| klaw | `incomplete` | side-effect-summary (`SEStorage`) crash; 73 partial candidates fail trace resolution |
| tms | `incomplete` | F2F-summary crash; 58 Tree results absent from partial SARIF |

Conductor and TMS fail on the F2F-summary path:

```text
Long2ObjectOpenHashMap$MapIterator.nextEntry
Long2ObjectOpenHashMap$ValueIterator.next
MethodInitialToFinalBaseOnlyApSummariesStorage$F2FStorage.collectSummariesTo
CommonF2FSummary$MethodTaintedSummariesGroupedByFact.collectTo
CommonF2FSummary$MethodTaintedSummariesGroupedByFact.filterEdgesTo
SummaryEdgeSubscriptionManager.subscribeOnMethodSummary
```

Apollo and Klaw fail with the same fastutil exception on a different BaseOnly storage path:

```text
Long2ObjectOpenHashMap$MapIterator.nextEntry
Long2ObjectOpenHashMap$ValueIterator.next
FactSESummariesBaseOnlyStorage$SEStorage.collectSummariesTo
CommonFactSideEffectSummary$MethodTaintedSideEffectSummaries.collectTo
CommonFactSideEffectSummary$MethodTaintedSideEffectSummaries.filterSummariesTo
CommonFactSideEffectSummary.filterTaintedTo
SummaryEdgeSubscriptionManager.subscribeOnMethodSummary
```

Exception:

```text
java.lang.NullPointerException:
Cannot invoke "it.unimi.dsi.fastutil.longs.LongArrayList.getLong(int)"
because "this.wrapped" is null
```

Both BaseOnly implementations own mutable fastutil `Long2ObjectOpenHashMap` state and iterate its values during summary subscription while analysis runners can add summaries. A fastutil iterator's internal wrapped-key list being null at `nextEntry` is direct evidence of invalid map iteration state. The stacks do not name a racing writer, so “concurrent mutation” is the supported mechanism, not a proven thread interleaving.

Current behavior is to catch the exception, log `Ifds engine failed`, confirm whatever partial candidates exist, generate partial SARIF and exit 252. In Conductor, the crash occurs with 2,225 work items pending; the later `Finish IFDS analysis` message is an outer phase marker emitted after trace generation, not evidence that forward IFDS reached quiescence. Expected behavior is a stable snapshot or otherwise synchronized/concurrent-safe iteration, followed by analysis quiescence and exit 0. Result comparison must be gated on `complete`.

### Conductor's three partial-forward absences

The partial new candidate set has 15 results: 12 added and three unchanged. All 15 reach SARIF (`TraceGenerationStats(total=15, simple=2, generatedSuccess=13, generationFailed=0)`), so the three removed Tree findings are absent from the **partial forward set**, not trace-filtered:

1. `graaljs-polyglot-code-injection`, `ScriptEvaluator.java:253`, fingerprint `XwZ5Hp7oRb/d9Epw+EWzlpXu/eCaHJ6y1HnTzrXrLNM=`: REST/workflow input reaches `TaskModel.inputPayload`, `Lambda.execute.taskInput`, `scriptExpression`, `ScriptEvaluator.eval/getSource`, then `Source.newBuilder(...).buildLiteral()`.
2. `graaljs-polyglot-code-injection`, `PythonEvaluator.java:63`, fingerprint `5Z0paTcbpFWw375Xtahij/4976Syl9AHL06SimS7cHU=`: the same workflow sources reach `Inline.execute.expression`, `PythonEvaluator.evaluate`, concatenated `line`, then `Context.eval`.
3. `path-traversal`, `DummyPayloadStorage.java:95`, fingerprint `RRtrIyruCjCM1+l1oyB0JT8prjWBRiO1Nr7eaZfmEuo=`: `WorkflowModel.externalInputPayloadStoragePath` reaches `ExternalPayloadStorageUtils.downloadPayload`, virtual `download(path)`, then `new File(payloadDir, path)`.

Expected sink facts are respectively `$UNTRUSTED` on `getSource` argument 1, on `PythonEvaluator.expression/line`, and on `DummyPayloadStorage.download` argument 1. The production logs do not contain BaseOnly per-statement facts, and the IFDS runner crashed before quiescence with pending work. Therefore the first bad AP transfer for these three cannot be selected from this run; the exact evidenced BaseOnly operation is the storage failure above. Claiming `read`, `write`, dispatch or `matchPrefix` for these flows would be speculation.

## 4. ThingsBoard: one result is inconclusive

Removed result:

- `java.security.unvalidated-redirect-in-spring-app`
- `application/src/main/java/org/thingsboard/server/controller/AdminController.java:483`
- source/sink fingerprint: `igG4z/W/Og667GbZipjYjRtCsxi1Tp85r9581EoozGM=`

Tree trace:

```text
AdminController request[$UNTRUSTED]                        line 445
  -> DefaultSystemSecurityService.getBaseUrl(request)     line 451
  -> MiscUtils.constructBaseUrl/getDomainName(request)
  -> baseUrl -> prevUri                                   line 452
  -> response.sendRedirect(prevUri)                       line 483
```

The new run is not diagnostic:

- IFDS times out after `14m 24.728s` and reports 16 partial candidates.
- trace resolution reaches `14/16` and remains there for about 87 seconds.
- trace processing times out and cancels the channel.
- exactly two unnamed candidates are filtered, leaving 14 SARIF results.

The removed Admin redirect may be one of the two forward-present trace jobs that did not finish, or it may be absent from the timed-out forward set while two different candidates were filtered. The artifacts do not contain the filtered candidates' identities. Current evidence is timeout/cancellation, not an AP operation. Expected behavior is a complete IFDS run and trace-job logging that includes rule id, fingerprint and sink location.

## 5. tms: classification of every removed result

`run-debug/regression-diff/diff/tms.json` enumerates all 58 removals in its `removed` array. The report numbering below regroups that exact set by finding class; full fingerprints and traces remain in `run-debug/result-tms-base/results.sarif`.

### Removed items 1-25: dataflow findings

| items | rules | sinks |
|---|---|---|
| 1-2 | HTTP response splitting | `BlogController.java:1755`, `:1936` |
| 3-4 | OS command injection | `BlogController.java:1704`, `:1887` |
| 5-18 | path traversal | `BlogController.java:1637`, `1642`, `1654`, `1674`, `1686`, `1694`, `1758`, `1820`, `1825`, `1837`, `1857`, `1869`, `1877`, `1939` |
| 19-20 | path traversal | `FileController.java:551`, `:557` |
| 21-22 | path traversal | `ExcelUtil.java:130`, `:157` |
| 23-25 | path traversal | `LuckySheetUtil.java:102`, `:103`, `:106` |

The BaseOnly runner crashes while 97 work items remain. It then reports 103 partial forward candidates and filters four unnamed candidates, producing 99 results. At most four of items 1-25 could be those filtered candidates, and they could instead be BaseOnly-only candidates absent from Tree. The saved logs do not allow an honest per-item forward-versus-trace split. Every item is therefore classified as “absent from incomplete final SARIF; semantic AP cause unproven.”

### Removed items 26-58: direct pattern findings

All 33 are `stacktrace-printing-in-error-message` results with zero code flows:

- `BlogController`: lines 566, 1245, 1336, 1602, 1611, 1644, 1659, 1688, 1766, 1795, 1827, 1842, 1871, 1947
- `ChatChannelController`: 250, 450, 1069, 1092, 1303, 1352, 1515, 1610
- `ChatController`: 317
- `ChatDirectController`: 477, 487, 511, 740, 777
- `ImportController`: 135, 379
- `TranslateController`: 216, 308, 518

They are direct `Throwable.printStackTrace()` pattern matches, not source-to-sink AP findings. Tree has 106 simple results and partial BaseOnly has 73; the difference is exactly these 33. This is consistent with interruption before their accumulation, but the aggregate log does not identify each missing simple candidate. In either case they provide no evidence about forward fact propagation or trace resolution.

### Complete per-result tms inventory

ID is the Tree SARIF `vulnerabilitySourceSinkHash/v1`; flows are the Tree code-flow count. Paths are under `src/main/java/com/lhjz/portal/`.

| # | rule | ID | location | method | flows |
|---:|---|---|---|---|---:|
| 1 | http-response-splitting | `mDrb8b1F+Udd6y5WDdi1CSQ5zNw/ARARxOGXa0RmsoU=` | `BlogController.java:1755:9` | `BlogController#download` | 4 |
| 2 | http-response-splitting | `W48bU53MJKuddRqrMPrlUwlUvUbfConAEnIZkuGLANc=` | `BlogController.java:1936:9` | `BlogController#downloadComment` | 3 |
| 3 | os-command-injection | `z4r6/OkkMSUnXIcSTLK6jWpLH4vE6bvy0QwLh6WNZMc=` | `BlogController.java:1704:21` | `BlogController#download` | 2 |
| 4 | os-command-injection | `5ZOiUNRneKuBB5UX/4oo0DZUELz9jZfJ4uKEDmfH7ro=` | `BlogController.java:1887:21` | `BlogController#downloadComment` | 1 |
| 5 | path-traversal | `u3gKQo3lzEwsHk2AbttVohzZHQgcciUhge85dtn7QKM=` | `BlogController.java:1637:18` | `BlogController#download` | 2 |
| 6 | path-traversal | `JxCyzRPLGZ21YX/qmvrd+5y38YSFhC5ZkDCinhP7P6o=` | `BlogController.java:1642:21` | `BlogController#download` | 2 |
| 7 | path-traversal | `K5Iv71Xw4mz1Bfowceo7tdTO7h0A5g8CDQlujCFriF4=` | `BlogController.java:1654:18` | `BlogController#download` | 2 |
| 8 | path-traversal | `D13qD+9CLzvkUGi6T3RewrrAfHN5+PuOb5JmQP4jtXI=` | `BlogController.java:1674:18` | `BlogController#download` | 2 |
| 9 | path-traversal | `qQzmU9HOEgyprZumiruJZTZ9k1O/Yv5/AJHpJ3SQftg=` | `BlogController.java:1686:21` | `BlogController#download` | 2 |
| 10 | path-traversal | `PRE8xYbiAvxH+sce6NYg0JM3thmfYiY5duixPI535mM=` | `BlogController.java:1694:18` | `BlogController#download` | 2 |
| 11 | path-traversal | `RixOflcWgdpVqtxZ8PxOp3DQ0Ex7eeHoGIy2chmVToI=` | `BlogController.java:1758:64` | `BlogController#download` | 2 |
| 12 | path-traversal | `VSNt4NM3HMyx91oAgQJsdnuhwIjQ66BxVAz+EIwVcF8=` | `BlogController.java:1820:18` | `BlogController#downloadComment` | 1 |
| 13 | path-traversal | `DTBjWp0974FDuO8ff/TxzM44BNQUzK2mLZ8hYGtg7tg=` | `BlogController.java:1825:21` | `BlogController#downloadComment` | 1 |
| 14 | path-traversal | `tL18KmMDy6UTIiGlQhR6Wzt9rOQLDlOlAdTr35bOrj4=` | `BlogController.java:1837:18` | `BlogController#downloadComment` | 1 |
| 15 | path-traversal | `a3TinEUNpQIuKotppMXhdH+CryykPTKYeBfKGfBhwAA=` | `BlogController.java:1857:18` | `BlogController#downloadComment` | 1 |
| 16 | path-traversal | `h2jRTQhMCbTw+pQEJMLiNmI63Lly6DKa7NXZwRDp/vA=` | `BlogController.java:1869:21` | `BlogController#downloadComment` | 1 |
| 17 | path-traversal | `nCGeNp94ezLj3CiO98YVdTVPN8xnYzduom9KUVD6gUg=` | `BlogController.java:1877:18` | `BlogController#downloadComment` | 1 |
| 18 | path-traversal | `haKHG33DJ9LSdM1hn5EsUnsbtPvdGl9o5BfuobGYi+4=` | `BlogController.java:1939:64` | `BlogController#downloadComment` | 1 |
| 19 | path-traversal | `xPqPBpvxSdAsI8BZBnYrzuqCzFlnAGYF3psQcDRwohs=` | `FileController.java:551:14` | `FileController#csv2md2` | 1 |
| 20 | path-traversal | `WVIue0SjhPOkHW3im86e95IebbaLNr2Q+wo1O3qklqQ=` | `FileController.java:557:22` | `FileController#csv2md2` | 1 |
| 21 | path-traversal | `JeLVq6a8tfZI1hAoJfmNFQdZYFSQrdmMuAYbfTcrl2A=` | `ExcelUtil.java:130:49` | `ExcelUtil#readXls` | 1 |
| 22 | path-traversal | `Rqsv8XVS/ginpCrGGSjl+ieqmktGYIBaQjpxeh7GUss=` | `ExcelUtil.java:157:49` | `ExcelUtil#readXlsx` | 1 |
| 23 | path-traversal | `DDsnUnXKnxhgyq7tqBsduT8kXd70IvTvv7ZQE/o79Po=` | `LuckySheetUtil.java:102:18` | `LuckySheetUtil#exportLuckySheetXlsxByPOI` | 2 |
| 24 | path-traversal | `K/5HAXDcpamEnNvY2QK5Q/mC9Pi9rGf5viwKtt5Bu6E=` | `LuckySheetUtil.java:103:17` | `LuckySheetUtil#exportLuckySheetXlsxByPOI` | 2 |
| 25 | path-traversal | `LFOGW4FfHKuu68rylzJPvbSak8m7nFYD2zoHAzNuDJI=` | `LuckySheetUtil.java:106:18` | `LuckySheetUtil#exportLuckySheetXlsxByPOI` | 2 |
| 26 | stacktrace | `eCuu5ZKzXGcZKwfImqhIsh0qJgjS7bzUA6C6V9cXKdc=` | `BlogController.java:566:21` | `BlogController#update` | 0 |
| 27 | stacktrace | `1QTZJpNj2dOdBWycUHpeoty9p+g+iVhQwxfZ8XgG1yk=` | `BlogController.java:1245:13` | `BlogController#createComment` | 0 |
| 28 | stacktrace | `QPR6ON8G7Ued/WmIi776gxFBl0SI9bTAs4MYOuHK/Gs=` | `BlogController.java:1336:13` | `BlogController#updateComment` | 0 |
| 29 | stacktrace | `r6hOTnMRnj1t2PmqcsSnPp8aC6UEZgCOed3acdH+jPQ=` | `BlogController.java:1602:17` | `BlogController#download` | 0 |
| 30 | stacktrace | `WFW4BoNIL9BWUkBVCtLtCEe9R4FLhPr4prkv679ciG0=` | `BlogController.java:1611:17` | `BlogController#download` | 0 |
| 31 | stacktrace | `qAPTjg/WdqpV2rCULBYpVj2VBdWfXUSXvBzcRKZj/NE=` | `BlogController.java:1644:21` | `BlogController#download` | 0 |
| 32 | stacktrace | `49Y1Q+rWO902bA6Ztmy66i/J+4okQwhRg6VfZBAXUaE=` | `BlogController.java:1659:21` | `BlogController#download` | 0 |
| 33 | stacktrace | `abS65tfZmgtFDHpxtdD0eOXWswqghfEKzWwu7KaOxnQ=` | `BlogController.java:1688:21` | `BlogController#download` | 0 |
| 34 | stacktrace | `NkRk/47wjNrE6oinq3DF/PSWXirvNFolJv6SoaNWLEE=` | `BlogController.java:1766:13` | `BlogController#download` | 0 |
| 35 | stacktrace | `f+5jOn1bHPIX2XoaLjcu/AUX7L6rHWT2nsOZo+tm2LA=` | `BlogController.java:1795:17` | `BlogController#downloadComment` | 0 |
| 36 | stacktrace | `2ZFUp8rcGVVG/DkJss4e0+2+/ynpSaHC4n9z4aDpS7A=` | `BlogController.java:1827:21` | `BlogController#downloadComment` | 0 |
| 37 | stacktrace | `vypF2aA7OC8Q7JTfuqOWSBOo1FWTsep61N8lxzBITd4=` | `BlogController.java:1842:21` | `BlogController#downloadComment` | 0 |
| 38 | stacktrace | `ONcErEyEcrTcH7iaSZQQvgm0WwzIJqDmLvpHJ1Nzafw=` | `BlogController.java:1871:21` | `BlogController#downloadComment` | 0 |
| 39 | stacktrace | `pIBq7H5TnsuU/LsdFi4X6S9fdzzNX2ebIurfRzhhNK4=` | `BlogController.java:1947:13` | `BlogController#downloadComment` | 0 |
| 40 | stacktrace | `aqvvJlOc8dSJrStQWIECX4OXAW/HkRRG4WbIdE9gDJo=` | `ChatChannelController.java:250:13` | `ChatChannelController#create` | 0 |
| 41 | stacktrace | `255IggtufRLp0f6m8ExnW4xP0OJxZhDZxiuKWYhlBUM=` | `ChatChannelController.java:450:13` | `ChatChannelController#update` | 0 |
| 42 | stacktrace | `pPqBuh7MMeeEMA03DjrNjL1Q0EivJ8bfBiWKMsMAGpY=` | `ChatChannelController.java:1069:17` | `ChatChannelController#download` | 0 |
| 43 | stacktrace | `YZN1ClhvWy+TmuFARbXp1MbyNjoLel/6HYnNBj/vuYM=` | `ChatChannelController.java:1092:17` | `ChatChannelController#download` | 0 |
| 44 | stacktrace | `czMbI6Woq9KctMKBhugLwLekMfVTGCsZ2MxyCpgtGTI=` | `ChatChannelController.java:1303:17` | `ChatChannelController#toggleLabel` | 0 |
| 45 | stacktrace | `rXW8CwrJJsTLqOOl0xijgWOtG12FGM+ylWWEqhavqTI=` | `ChatChannelController.java:1352:21` | `ChatChannelController#toggleLabel` | 0 |
| 46 | stacktrace | `sDgmXEYcQGTtfVSEVYpKZqzAKrWW3855suhEahvR8As=` | `ChatChannelController.java:1515:13` | `ChatChannelController#addReply` | 0 |
| 47 | stacktrace | `NQH5b18IwcDVMb05w9JGd1t1cC30y9fgsl/zXZT+cgY=` | `ChatChannelController.java:1610:13` | `ChatChannelController#updateReply` | 0 |
| 48 | stacktrace | `7R8ShFz5i0FlMvEyVhzyZUi45pc5exhCm4wIr7AObqE=` | `ChatController.java:317:17` | `ChatController#update` | 0 |
| 49 | stacktrace | `xLivmJP8O7DE+m6z5g2niTkD4s8ni66gNLk4lF35KfA=` | `ChatDirectController.java:477:17` | `ChatDirectController#download` | 0 |
| 50 | stacktrace | `weKNgH5AYCN3IzeTC4xTFzM/tYjHKmquhtjOBT7sWJ0=` | `ChatDirectController.java:487:17` | `ChatDirectController#download` | 0 |
| 51 | stacktrace | `n4nBExzNMTb062CmnuChPS/bt1aFTSeFC/4tyJkSaTI=` | `ChatDirectController.java:511:17` | `ChatDirectController#download` | 0 |
| 52 | stacktrace | `PyR7niylHrWDSlmeLbSFcaUJZbhLyLnhQpBY7Ngo4Ts=` | `ChatDirectController.java:740:17` | `ChatDirectController#toggleLabel` | 0 |
| 53 | stacktrace | `e+IbveP9/WkP6jgogoGR0Ry+aZ4PiqPekJYGHxCsZyU=` | `ChatDirectController.java:777:21` | `ChatDirectController#toggleLabel` | 0 |
| 54 | stacktrace | `JLb2tGE4d9U+Cl8tPFm0aGCtfbhrazv0fEWvAZcv/ao=` | `ImportController.java:135:5` | `ImportController#save` | 0 |
| 55 | stacktrace | `Sz3m0ShUSnjkT0zkuc54km/yvvrVaUZOebDmdK8QPWc=` | `ImportController.java:379:4` | `ImportController#save` | 0 |
| 56 | stacktrace | `nprTZD+x8d+OMU1n79GdIckX4VrB37PirWIh/HxAXa8=` | `TranslateController.java:216:13` | `TranslateController#save` | 0 |
| 57 | stacktrace | `M0jfMZf+A056HQXBsXASmfFh7OoXYbAwqdVbG37YC4A=` | `TranslateController.java:308:17` | `TranslateController#update` | 0 |
| 58 | stacktrace | `VGouVjaccjseQsL3X1XwKn9ZijOoQwsT9kfTVwXJKB8=` | `TranslateController.java:518:17` | `TranslateController#update2` | 0 |

### Exact tms run failure and workload

```text
Tree:     complete, 333,428 processed / 0 pending
BaseOnly: incomplete, 534,830 processed / 97 pending, exit 252
```

The crash stack is the F2F storage operation in section 3. IFDS wall time is nearly equal (49.616s vs 49.720s), but BaseOnly performs 60.4% more steps before crashing. Trace time doubles (about 5.55s to 11.26s) and code flows increase from 75 to 468 despite the partial result set. Path-traversal traces alone increase from 60 flows across 40 findings to 406 across 19 findings. This is trace multiplicity/work amplification, not evidence of 25 distinct forward algebra failures.

## 6. Performance investigation

### Aggregate complete-run result

For the 20 projects where both statuses are exactly `complete`:

| aggregate | Tree | BaseOnly | change |
|---|---:|---:|---:|
| summed scan time | 1,338.6s | 1,685.1s | +346.5s, +25.9% |
| mean peak memory | 6.21GiB | 6.53GiB | +0.32GiB |
| projects faster/slower | 8 faster | 12 slower | — |

The aggregate is highly concentrated. Removing Stirling-PDF, OpenMRS and HertzBeat leaves 17 projects at 1,070.0s Tree versus 1,085.6s BaseOnly (+1.46%).

### Dominant complete-run regressions

| project | scan Tree -> BaseOnly | IFDS Tree -> BaseOnly | trace Tree -> BaseOnly | candidate/trace evidence |
|---|---:|---:|---:|---|
| Stirling-PDF | 96.1s -> 200.0s (2.08x) | 44.51s -> 68.44s (1.54x) | 1.62s -> 79.55s (~49x) | candidates 24 -> 88; filtered 4 -> 48; flows 51 -> 308 |
| openmrs-core | 84.9s -> 274.6s (3.23x) | 36.25s -> 77.79s (2.15x) | 0.19s -> 144.36s (~764x) | candidates 13 -> 82; filtered 0 -> 10; flows 11 -> 140 |
| hertzbeat | 87.6s -> 124.9s (1.43x) | 38.82s -> 53.75s (1.38x) | 0.44s -> 9.83s (~22x) | candidates 27 -> 41; flows 28 -> 505 |

This shows that trace workload is a major observed contributor: BaseOnly creates more candidates and many more code flows, and trace resolution takes much longer. The available logs do not show whether packed representation or summary algebra creates that multiplicity. Across this three-project set, and especially Stirling/OpenMRS, trace time dominates the additional runtime; HertzBeat also has a larger IFDS increase than trace increase.

Secondary complete-run changes:

- `kkFileView`: 54.5s -> 66.5s; IFDS 8.02s -> 11.98s; trace 1.77s -> 5.75s; memory +1.36GiB; findings 39 -> 50.
- `continew-admin`: 52.0s -> 69.8s; IFDS 14.75s -> 19.28s; findings unchanged at two. This needs a repeated benchmark before operation-level attribution.
- `DWSurvey`: 87.5s -> 96.1s; trace 9.27s -> 15.16s; peak memory +2.70GiB; findings 297 -> 299.
- `jeesite5`: 74.3s -> 78.1s; IFDS 21.97s -> 27.14s; peak memory +1.38GiB; two candidates filtered.
- `snowy`: runtime improves slightly while peak memory rises 1.67GiB. A single peak-RSS sample without a work increase is insufficient to assign an AP cause.

### Status-regression performance failures

| project | evidence | classification |
|---|---|---|
| apollo | IFDS 26.82s -> 135.03s and crashes; tracing the partial candidates then takes 363.24s versus 0.06s | severe trace pathology plus invalid partial completion |
| conductor | IFDS 62.33s -> 107.71s before crash; trace 1.20s -> 76.37s; memory reaches 93.5% | forward fact/summary expansion, storage crash, then expensive tracing of 15 partial candidates |
| klaw | IFDS 30.85s -> 89.19s before crash; candidates 36 -> 190; 73 filtered; trace 0.55s -> 65.94s | fact/summary explosion, trace failures, storage crash |
| thingsboard | IFDS 390.49s -> 864.73s unfinished; trace phase lasts 96.73s and stalls about 86.71s at 14/16 | larger unfinished work is associated with exhausted forward and trace budgets; exact state-expansion cause unproven |
| tms | IFDS time flat but 60.4% more steps before crash; trace 2.0x; flows 75 -> 468 | work/trace multiplicity plus storage crash |

### Performance root evidence and missing instrumentation

The logs prove two actionable roots:

1. **Trace graph explosion.** More forward candidates, many more code flows, long trace phases and large filtered sets move cost from compact fact storage into combinatorial trace resolution.
2. **Unsafe BaseOnly summary storage.** Conductor/TMS crash in F2F collection and Apollo/Klaw crash in side-effect-summary collection with the same invalid fastutil iterator symptom, making both correctness and performance results invalid.

The logs do not provide distinct-fact and summary-edge cardinalities per analysis unit, so a single algebra operation cannot yet be blamed for all state expansion. The next performance run should record, per unit and phase: unique final facts, unique F2F/Z2F/ND edges, exclusion-set cardinality, subscriber count, trace candidates explored, and trace rejection operation. Candidate identity must be logged before filtering.

## Artifact map and reproduction

- summary/diffs: `run-debug/regression-diff/report.md`, `run-debug/regression-diff/diff/*.json`
- statuses: `run-debug/result-<project>-{base,new}/status.json`
- phase/crash evidence: `run-debug/result-<project>-{base,new}/analyzer.log`
- successful Tree traces and fingerprints: `run-debug/result-<project>-base/results.sarif`
- partial/final BaseOnly results: `run-debug/result-<project>-new/results.sarif`
- previous run investigation: `docs/baseonly-e2e-missed-findings-report.md`

Useful checks:

```bash
rg -n 'Total vulnerabilities|Filter out|Ifds engine failed|Ifds analysis timeout|processing timeout' \
  run-debug/result-*-new/analyzer.log

for p in Stirling-PDF spring-petclinic conductor thingsboard tms; do
  jq -r '.removed[] | [.ruleId,.path,.startLine,.startColumn,.codeFlows] | @tsv' \
    "run-debug/regression-diff/diff/$p.json"
done
```

## Required gates

1. Pin the Stirling `%832![sink_35].$` versus `%832.Body.*` trace split and make semantic trace marks survive structural summary exclusions.
2. Keep Petclinic excluded from the BaseOnly no-FN oracle while primitive and boxed-primitive facts are intentionally forbidden.
3. Make both BaseOnly F2F and side-effect summary collection safe under concurrent add/subscribe, then rerun `apollo`, `conductor`, `klaw` and `tms`; do not compare partial SARIF.
4. Rerun ThingsBoard with enough IFDS/trace budget and candidate-identity logging.
5. Add performance gates for phase time, unique summary edges and trace multiplicity; total scan time alone hides the dominant trace explosion.
