# BaseOnly e2e missed-findings investigation

Date: 2026-07-15

Compared analyzers:

- Tree/base: `ff1e4f5707920385ed06316362ce1c0191a589c4`
- BaseOnlyField/new: `e8dca670479eb319dbad011582b65d6a93ac5db7`

## Scope and result

The report contains every `-finding` whose new side had an analyzer result. Rows whose missing side failed in the autobuilder are excluded as requested. There are 39 such result differences: 36 findings from complete runs and three conductor results from an incomplete run.

| Project | Removed | Classification | Proven cause |
|---|---:|---|---|
| kkFileView | 31 | forward/confirmation loss | `matchPrefix` rejects an exact whole-value fact against an abstract identity summary with a committed field slot |
| spring-petclinic | 2 | forward/confirmation loss | kind-strict `covers`/`matchPrefix` rejects the whole-receiver getter relation |
| Stirling-PDF | 2 | trace-resolution filtering | `splitDelta` creates a sink-mark suffix which `suffixExcluded` rejects |
| jeesite5 | 1 | trace-resolution filtering | nested `ActionEnter.invoke` summary widens the requested exact fact and has no matching intra trace |
| conductor | 3 | invalid comparison: new analysis is incomplete | concurrent mutation/iteration of a fastutil map crashes BaseOnly analysis |

`Total vulnerabilities` is logged after forward IFDS and vulnerability confirmation but before trace generation. `Filter out N vulnerabilities without traces` is logged only after trace resolution/path generation. Those two points are the stage boundary used below.

## 1. kkFileView: 31 forward losses

All 31 removed results are `java.security.path-traversal`. Their common source is the untrusted `url` parameter at `OnlinePreviewController.java:67:12`. Tree reports 39 pre-trace vulnerabilities. BaseOnly reports nine and performs no trace filtering. The final-set equation is exact: 39 Tree results minus 31 removed plus one BaseOnly-only result equals nine. Therefore every removed kkFileView result is absent before trace generation.

An exact-commit rerun (`92ca92bee6d4682f2eb6f388174d39afd2263874`) with fact-reachability output reproduces the loss: Tree has 38 path-traversal candidates and BaseOnly has seven for the isolated rule. At `ConvertPicUtil.java:43`, Tree carries the source mark into `arg(0)` and the sink local; BaseOnly has only static facts at that method entry. At `TiffFilePreviewImpl.java:37`, Tree carries the mark through `FileAttribute.outFilePath`; BaseOnly retains an exact marked `FileAttribute.url` but does not produce the marked `outFilePath` fact. The relevant object is populated in `FileHandlerService.getFileAttribute` through setters for URL-derived name, suffix, and output path.

Fact-level instrumentation locates the first kill at an unrelated sequential setter call in `FileHandlerService.getFileAttribute`. Immediately before `attribute.setName(...)`, the untrusted output path is present as an exact whole-value fact. Call mapping rebases it to an exact `arg(0)` fact with taint exclusions. The call identity summary is `arg(0).*/{}`, but `BaseOnlyFinalFactAp.delta` returns no effects. The exact observed state is:

```text
current  = var(6)![UNTRUSTED].$ / {taint exclusions}
rebased  = arg(0)![UNTRUSTED].$ / {taint exclusions}
summary initial = arg(0).<field#0>.* / {}
effects  = []
```

The packed accesses are `final=(-1,-1,31)` (exact terminal semantic mark) and `initial=(-1,0,-2)` (abstract identity summary with a committed field slot). In the current `covers` implementation, `BaseOnlyAccessOps.matchPrefix` rejects the pair because the exact whole-value final has no matching field in the fixed prefix; the equivalent older matcher reports that the zero-length final core cannot start with the summary's one-slot core. It returns `NO_MATCH` and summary application yields no identity successor. This is incorrect for an identity summary—the exact marked value itself must survive an unrelated call. It drops the local at the first setter and therefore removes every downstream field/getter and filesystem flow represented by the 31 sinks.

Five alternative hypotheses were isolated and ruled out as sufficient causes: reverting specialized `IdEdgeStorage`, restoring a previous broad matcher variant, restoring the mixed concrete-to-abstract terminal seed, persisting collapsed edges, and changing non-identity exclusion merge from union to intersection each leave the isolated result at seven. The direct rejected-pair instrumentation, rather than those broad A/B attempts, identifies the operation that kills the fact.

The 31 affected sinks are:

| # | Sink |
|---:|---|
| 1 | `utils/ConvertPicUtil.java:111:28` |
| 2 | `utils/ConvertPicUtil.java:68:42` |
| 3 | `utils/OfficeUtils.java:71:13` |
| 4 | `utils/ConvertPicUtil.java:43:14` |
| 5 | `utils/ConvertPicUtil.java:60:43` |
| 6 | `utils/ConvertPicUtil.java:106:13` |
| 7 | `utils/KkFileUtils.java:137:31` |
| 8 | `utils/EncodingDetects.java:30:14` |
| 9 | `utils/OfficeUtils.java:35:26` |
| 10 | `utils/KkFileUtils.java:137:13` |
| 11 | `utils/ConvertPicUtil.java:60:18` |
| 12 | `service/CompressFileReader.java:55:14` |
| 13 | `service/FileHandlerService.java:168:14` |
| 14 | `service/FileHandlerService.java:345:17` |
| 15 | `service/FileHandlerService.java:344:18` |
| 16 | `service/OfficeToPdfService.java:79:21` |
| 17 | `service/FileHandlerService.java:253:14` |
| 18 | `service/FileHandlerService.java:387:26` |
| 19 | `service/OfficeToPdfService.java:84:21` |
| 20 | `service/OfficeToPdfService.java:33:54` |
| 21 | `service/FileHandlerService.java:259:14` |
| 22 | `service/FileHandlerService.java:259:32` |
| 23 | `service/FileHandlerService.java:184:14` |
| 24 | `service/OfficeToPdfService.java:33:14` |
| 25 | `service/impl/JsonFilePreviewImpl.java:92:9` |
| 26 | `service/impl/MediaFilePreviewImpl.java:123:21` |
| 27 | `service/impl/JsonFilePreviewImpl.java:87:14` |
| 28 | `service/impl/SimTextFilePreviewImpl.java:79:14` |
| 29 | `service/impl/SimTextFilePreviewImpl.java:86:74` |
| 30 | `service/impl/MediaFilePreviewImpl.java:114:17` |
| 31 | `service/impl/MediaFilePreviewImpl.java:122:22` |

Paths in this table are relative to `server/src/main/java/cn/keking/`. Every base trace begins at the controller's untrusted `url` and ends at a filesystem/path API.

## 2. spring-petclinic: two forward losses

Both results have the same physical source-to-sink flow and differ only by rule:

- `java.security.xss-in-spring-app`, `OwnerController.java:86`
- `java.security.unvalidated-redirect-in-spring-app`, `OwnerController.java:86`

The source is the untrusted `Owner owner` argument of `processCreationForm` at line 78. The value flows through `owner.getId()` (`BaseEntity.getId`, lines 40-41) into `"redirect:/owners/" + owner.getId()`.

The supplied logs prove forward loss: Tree reports two pre-trace vulnerabilities; BaseOnly reports zero, so trace generation receives no candidate. A local exact-commit portable-model rerun in `BaseOnlyField` mode also reports zero.

The method statistics isolate the failed summary relation:

- Tree: `BaseEntity#getId()` has `pass: 6`.
- BaseOnly: the same method has `pass: 0`.

The concrete failed relation is the whole receiver taint `owner![UNTRUSTED].$` against the getter's field/AP summary for `this.id`. `BaseOnlyAccessOps.covers` requires the abstraction-slot kind to be present (`slotVal(x, k) != NO_ACCESSOR`); `matchPrefix` converts its rejection to `NO_MATCH`. In a field-insensitive overapproximation the whole-object taint must satisfy the getter relation. Instead `FinalFactAp.delta` is empty, summary application has no effect, and the value never reaches `Return` or `TaintAnalysisUnitStorage.addVulnerability`.

This is direct evidence of an under-approximating BaseOnly operation: Tree applies six getter/pass summaries, BaseOnly applies none, and both vulnerabilities disappear before trace resolution.

## 3. Stirling-PDF: two trace-filtered findings

Both removed XSS findings are present in the BaseOnly pre-trace vulnerability list in an instrumented exact-commit rerun, and both receive `TracePathGenerationResult.Failure` after interprocedural trace resolution:

1. `java.security.xss-in-spring-app`, `GetInfoOnPDF.java:992:13`
   - Request-controlled input begins in `getPdfInfo` around line 472.
   - It flows through `PDFFile.getFileInput`, JSON/byte construction, and `WebResponseUtils.bytesToWebResponse` to the Spring response.
2. `java.security.xss-in-spring-app`, `PipelineController.java:90:17`
   - Request-controlled `HandleDataRequest` input flows through `generateInputFiles`, pipeline execution/output collection and file reading, then into `WebResponseUtils.bytesToWebResponse`.

The exact rejected trace operation is `MethodTraceResolver.resolveCallPassSummary` at the call to `callerFact.splitDelta(mappedSummaryFact)`:

- GetInfo: caller `var(832)![xss sink_35].$`; mapped `WebResponseUtils` summary final `var(832).Body.*`.
- Pipeline: caller `var(104)![xss sink_35].$`; mapped summary final `var(104).Body.*`.

`BaseOnlyAccessOps.splitConcreteInitial` accepts the field-lenient shape and projects the caller remainder to the bare semantic sink mark. `splitDelta` then calls `BaseOnlyApManager.suffixExcluded`; the summary exclusion set contains that mark, so it returns an empty delta list. The backward walk cannot cross the call summary and the already-discovered vulnerability is filtered.

The incorrect behavior is observable as `deltas=0` for both concrete pairs. The caller fact is a valid concrete instance of the open `.Body.*` summary; treating the trace-only sink mark as an excluded structural suffix prevents reconstruction even though forward IFDS reached the sink.

## 4. jeesite5: one removed XSS

The removed result is `java.security.xss-in-spring-app` at `modules/core/src/main/java/com/jeesite/modules/file/web/UeditorController.java:40`.

The base trace has two source paths. The direct one is:

`HttpServletRequest request` at line 38 -> `ActionEnter(request, rootPath, action)` -> `this.request` -> `ActionEnter.exec()` -> `request.getParameter("callback")` -> concatenated callback response -> Spring return at line 40.

An exact-commit full-model rerun reproduces 319 pre-trace candidates, exactly one `Trace has no resolved paths`, and 318 final findings. Per-vulnerability diagnostics identify line 40 definitively as `trace=Failure`; line 33 has a successful path. Thus line 40 was added to forward storage and was removed solely during trace resolution.

The interprocedural trace graph for the two `upload` overloads is connected and yields four method-trace candidates, but all four fail while resolving the inner method. At `ActionEnter.exec`, lines 43-45 (`this.invoke()`), trace resolution requests the exact tainted fact `<this>.request![UNTRUSTED].$/{}`. The recorded `CallSummary` instead has:

```text
edge start:       <this>.request![UNTRUSTED].$ / {}
summary initial:  <this>.request.* / {unrelated MongoDB, JWT, JSON marks}
summary final:    ret.* / {the same unrelated marks}
inner traces in ActionEnter.invoke: 0
```

BaseOnly therefore reconstructs a widened `.*` summary with unrelated negative marks instead of the requested exact `.request![UNTRUSTED].$` fact. `resolveIntraProceduralFullStart2FinalTrace(ActionEnter.invoke)` finds no matching inner trace; recursive `resolveEntry` returns null for every candidate, and path generation filters the already-discovered XSS. This is a trace-only BaseOnly summary/AP reconstruction error, not a forward miss.

## 5. conductor: three differences from an invalid partial run

The three base findings are plausible vulnerabilities:

1. GraalJS code injection, `ScriptEvaluator.java:253`: workflow-controlled script reaches `Source.newBuilder(...).buildLiteral()`.
2. Python code injection, `PythonEvaluator.java:63`: workflow-controlled expression is appended into `wrappedExpression` and reaches `context.eval("python", ...)`.
3. Path traversal, `DummyPayloadStorage.java:95`: REST-controlled external payload path reaches `new FileInputStream(new File(payloadDir, path))`.

They cannot honestly be classified individually as forward loss versus trace filtering from this run. The new run is `high_memory,incomplete`, and the engine stops analysis of `PackageUnit(com.netflix.conductor.rest.controllers)` before producing a partial SARIF. Its one filtered trace candidate is not named and need not be one of these three.

The BaseOnly failure itself is exact and actionable. `BaseOnlySideEffectRequirementApStorage` protects only its outer `based` map with `ConcurrentHashMap`. Each per-base `RequirementStorage.requirements` is a non-thread-safe fastutil `Long2ObjectOpenHashMap`. `filterTo` iterates `requirements.values` while `mergeAdd` mutates the same map. The observed fastutil iterator corruption throws:

```text
NullPointerException: ... LongArrayList.getLong(int) because "this.wrapped" is null
at Long2ObjectOpenHashMap$MapIterator.nextEntry
at BaseOnlySideEffectRequirementApStorage.filterTo(...:29)
```

The analyzer then logs `Ifds engine failed` and writes partial output. These three rows must be rerun after the storage is made thread-safe; they are not evidence about BaseOnly AP algebra.

## Verification evidence

### Supplied artifacts

```bash
rg -n 'Total vulnerabilities|Filter out|Trace has no resolved paths|Ifds engine failed' \
  run-debug/result-{kkFileView,spring-petclinic,Stirling-PDF,jeesite5,conductor}-new/analyzer.log
```

```bash
for p in Stirling-PDF conductor jeesite5 kkFileView spring-petclinic; do
  jq -r '.removed[] | [.ruleId,.path,.startLine,.startColumn,.codeFlows] | @tsv' \
    run-debug/regression-diff/diff/$p.json
done
```

### Local exact-commit diagnostics

- spring-petclinic portable model: exact repo commit `3e1ce239f4488f20abda24441388a515ea55a815`; local BaseOnlyField rerun reproduced `Total vulnerabilities: 0`.
- kkFileView portable model: exact repo commit `92ca92bee6d4682f2eb6f388174d39afd2263874`; isolated path rule reproduced Tree 38 versus BaseOnly seven before traces.
- Stirling-PDF portable model: exact repo commit `d80e627899daf804f1390a0b75a1da3fd093aa84`; instrumented trace rerun named both removed sinks and logged the failing fact pairs above.
- jeesite5 full portable model: exact repo commit `7be0a1c5bd5349933e7e75c97e4f6bd1d529725e`; diagnostic rerun reproduced 319 -> filter one -> 318, named `UeditorController#upload:40`, and isolated the zero-inner-trace `ActionEnter.invoke` summary above.

Temporary diagnostics were not retained in production source.

## Recommended fixes and gates

1. Make `matchPrefix` preserve an exact whole value across an abstract identity call summary carrying a committed field; pin a local surviving two unrelated setter calls and rerun kkFileView.
2. Make `covers`/`matchPrefix` preserve the field-insensitive whole-receiver-to-getter relation without broadly reintroducing unwanted cross-kind matches; pin the petclinic `owner.getId()` flow. These are two manifestations of the same wildcard-slot rejection but require separate call-identity and getter tests.
3. In trace splitting, distinguish summary structural exclusions from trace-only semantic marks. Pin both Stirling `.Body.*` fact pairs.
4. Preserve the exact requested AP and relevant exclusions when reconstructing nested call summaries; pin the JeeSite `ActionEnter.exec -> invoke` trace.
5. Make every per-base collection in `BaseOnlySideEffectRequirementApStorage` safe for concurrent iteration/mutation, then require a complete conductor rerun before comparing findings.
6. Log the vulnerability identity and failing fact pair whenever trace generation filters a result. Aggregate `Filter out N` logs are insufficient for regression attribution.
