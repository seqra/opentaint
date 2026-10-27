# Why the callback edges are protected — 2026-10-27

The traced `TbDeviceStateNode$1.onSuccess()` edges inherit protection from a
selected-mark return cleaner. The callback does not set the flag. The cleaner
can preserve a concrete field fact and still block its FLOW replay. Therefore,
**spatially disjoint from the cleaner does not imply safe to leave unprotected**.

There is a narrower opportunity: `RemoveAllMarks` currently adds new protection
to its survivors too. It has no selected-mark exclusion barrier. The controls
below distinguish this conservative case from the selected-mark case. They do
not establish that it accounts for the large Thingsboard population.

Latest reached/completed/accepted project iteration in the reused diagnostics:
**run-1 / run-1 / run-1**. No new project analysis was run for this report. The
small controls exercise forward and backward AP operations; they are not a
completed run-2. The original timed campaign reached run-2 and completed run-1.
The analyzer implementation remains unchanged.

## 1. Meaning of protection

The flag belongs to an output path and mark under a particular initial premise.
It prevents replacement of that marked relation by FLOW. It preserves a marked
DEMAND for the next iteration. It does not change CM evaluation or indicate that
the fact is a confirmed source-to-sink path.

Use `T` for this full mark in the captured cases:

```text
java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3
```

`ANY` below means the `[any]` field tail. `FLOW` is the abstract mark slot.
`mx` is its set of excluded marks. All three local birth cases have empty field
exclusions, layer DEMAND, and the initial `arg(0).*/T`. That initial is a
conditional input hypothesis, not proof of an actual T source.

The current cleaner adapter has this effective policy:

```kotlin
// Ordinary scalar cleanup, including RemoveAllMarks.
val protect = input.base == cleaner.base
val result = cleanFacts(input, cleaner)
if (protect) {
    // null means all surviving marks, not an empty set.
    result.addProtection(cleaner.mark?.let(::setOf))
}

// Batched FULL cleanup has the same policy for the selected mask.
if (input.base == cleaner.base) result.addProtection(selectedMarks)
```

This policy tests the base and selected mark. It does not test whether the
surviving concrete path overlaps the cleaner. Other bases and unselected marks
do not gain protection. Existing protection is transported separately and is
merged by OR.

## 2. `TbDeviceStateNode$1.onSuccess()`: inherited protection

The actual callback body is:

```java
public void onSuccess() {
    ctx.tellSuccess(msg);
}
```

Its protected static result comes from applying a `tellSuccess` summary. The
captured chain goes through the actor mailbox, calculated-field processing,
queue send, and callback wrappers. The important operations are:

```text
ResponseEntity return cleanup:
  this.Body.Iterable.Element / ANY / T, plain
    -> same concrete fact, protected

callback composition and aliases:
  this.val$response / ANY / T, protected
    -> this.val$originalCallback / ANY / T, protected
    -> this.callback / ANY / T, protected

actual FLOW summary application in broadcastToCalculatedFields:
  incoming: arg(2).MultipleTbQueueCallbackWrapper.callback / ANY / T, protected
  callee:   arg(2).*/FLOW -> STATIC {TbMathNode.locks, ...} / ANY / FLOW
  result:   STATIC {TbMathNode.locks, ...} / ANY / T, protected

summary composition back to onSuccess:
  this.*/T -> STATIC TbMathNode.locks / ANY / T, protected
```

The static FLOW application has eleven static paths in its captured part. Its
FLOW excludes two JWT crypto marks, not T. It transports the incoming flag;
it does not create a new flag. The final callback has fourteen static fields
across all captured summary parts. These two counts describe different scopes.

The [matched trace report](bidirectional-correlated-concrete-run1-shapes-20261026.md#why-protected-static-summaries-increased)
contains the full chain and old/current owner comparison. This follow-up checks
whether the flag at its producer is necessary. A flag must not be cleared at
`onSuccess()` just because this small body has no cleaner.

## 3. Three actual local births

All three events show an empty selected protection mask on input and a nonempty
mask on output. They are local gains, not only inherited flags.

| Trace line | Method | Constructor call | Surviving fact, before → after |
|---:|---|---|---|
| 74 | `TelemetryController$6.onSuccess(List)` | `new ResponseEntity<>(keys, HttpStatus.OK)` | `this.Body.Iterable.Element/ANY/T`, plain → protected |
| 1 | `DeviceApiController$DeviceAuthCallback.onError(Throwable)` | `new ResponseEntity<>(body, HttpStatus.INTERNAL_SERVER_ERROR)` | `this.Body/ANY/T`, plain → protected |
| 78 | `DeviceController$1.onSuccess(ClaimResult)` | `new ResponseEntity<>(result, status)` | `this.Body/STAR/T`, plain → protected |

Here `Body` is `org.springframework.http.HttpEntity.Body`, and `Element` is
`java.lang.Iterable.Element`. The before/after path, tail, mark, layer and field
exclusions agree. The flag is the change. The STAR case shows that the producer
is not limited to ANY facts.

### Telemetry: the cleaner and FLOW counterpart

The class-file enclosing-method attribute identifies this `$6` as
`getAttributeKeysToResponseCallback`. Its actual source includes:

```java
public void onSuccess(List<AttributeKvEntry> attributes) {
    List<String> keys = attributes.stream()
        .map(KvEntry::getKey).collect(Collectors.toList());
    response.setResult(new ResponseEntity<>(keys, HttpStatus.OK));
}
```

The selected T cleaner is a generated **return rewriter**, not
`RemoveAllMarks`. Its geometry is `base=this, path=[], reach=EXACT`. The matched
cold call form and unchanged builder reconstruct bulk block `[90,100)`: ten
raw steps, seven distinct selected marks, with T at raw step 94. The live event
reports step 90 because it records the block start. It does not serialize the
cleaner descriptor itself. Other T steps occur in other blocks. The wider
cleanup schedule must not be described as one block.

`this.Body.Iterable.Element/ANY/T` is disjoint from an exact-root cleaner. Its
survival is correct. Nevertheless, current selected **nonstatic FLOW** cleanup
has no spatial test:

```kotlin
out.markRequest(T)
out.result(flow.copy(markExclusion = flow.markExclusion + T))
```

The matched completed Telemetry FLOW snapshot confirms the effect. Before the
constructor, `var(6).Iterable.Element/ANY/FLOW` excludes only the two JWT marks.
After the constructor, `var(8).Body/ANY/FLOW` excludes 48 marks, including T.
The complete candidate rows and mark names are embedded below. These are old
matched point-store facts, after the field-limit cut; they are not claimed to
be the unlogged current transient bound input. The source policy is unchanged.

Thus this local FLOW candidate **cannot cover T**, with or without the flag.
Farther along, another FLOW derivation can cover the output geometry. The flag
keeps that other derivation from erasing the cleaner-sensitive marked path.

### Device authentication error

```java
String body = null;
if (e instanceof HttpMessageNotReadableException || e instanceof JsonParseException) {
    body = e.getMessage();
}
responseWriter.setResult(new ResponseEntity<>(body, HttpStatus.INTERNAL_SERVER_ERROR));
```

The live event proves a selected FULL cleaner adds protection to `this.Body/ANY/T`.
The same constructor overload suggests the same reset geometry. This method's
live descriptor and matching FLOW snapshot were not captured, so that geometry
is an inference. It is not a second exact geometry proof or a distinct partial
cleaning case.

### Device claim result

```java
if (result.getResponse().equals(ClaimResponse.SUCCESS)) {
    status = HttpStatus.OK;
    deferredResult.setResult(new ResponseEntity<>(result, status));
}
```

This live event proves the same type of local flag gain on `this.Body/STAR/T`.
The descriptor and matching FLOW snapshot have the same evidence limit as the
authentication case. A different field tail does not stop the same-base wrapper
from adding the flag.

The bounded selected-T trace contains fourteen primitive cleanup gains among
2,000 recorded `new_flag` events. All fourteen use the ResponseEntity return
cleanup path. Other events can relay protection. The category also skipped
14,549 offers at its cap. These are not a census of all marks or a claim that
every protected summary has this origin.

## 4. Why dropping the disjoint survivor flag is unsafe as a general rule

The AP controls use this branch pattern. `spread` denotes the explicitly tested
micro-edge to an ANY return; it is not an assumed Java library model.

```java
if (b) {
    x.value = p.left;
    removeTAtExactRoot(x);     // preserves the marked x.value descendant
    return spread(x.value);
} else {
    return spread(p.right);
}
```

Facts under the same `p.*/T` initial are:

```text
left branch, selected cleanup:
  x.value/ANY/T -> x.value/ANY/T, protected
  then ret/ANY/T, protected

right branch, FLOW:
  p.*/FLOW -> ret/ANY/FLOW, T not excluded

summary normalization:
  keep flag:       retain the marked left relation
  omit new flag:  remove the marked left relation under the right FLOW

original backward abstract processing of the left branch:
  selected cleanup adds T to FLOW.mx
  result: p.left/ANY/FLOW excluding T
  apply to an actual return/T: no p.left/T answer
```

The covering right branch cannot recover the left source. The controls use the
actual cleaner, summary normalizer, reverse micro-edge application and summary
application. They do not use StrongQueries. The same distinction also appears
with a BELOW-root selected cleaner.

There is a second reason not to remove requests based only on forward spatial
disjointness. The existing constructive regression
`ReviewBaseCleaner.Repaired.disjoint_requests` has this shape:

```java
p.n = arg;
removeTAtExactRoot(p);
ret.f = p;
```

Forward run-1 has `p.n/STAR/FLOW`, disjoint from the cleaner. A later backward
abstraction can reach `p/STAR/FLOW`, which overlaps the root. The concrete T
request supplies the marked demand needed to cross that boundary. Therefore,
even adding a DISJOINT bypass in both cleaner directions is not by itself a
proof: the two traversals need not have the same field prefix.

These witnesses reject a general no-flag/no-request rule. They do not prove
that each captured Thingsboard flag is individually indispensable in the full
fixed point; the trace does not record all alternative derivations for each
membership.

## 5. A narrower candidate: do not create protection for `RemoveAllMarks`

The ordinary adapter also protects every same-base survivor when `mark=null`.
For example:

```text
input:        x.value/ANY/T, plain
cleaner:      RemoveAllMarks at x, EXACT
current:      x.value/ANY/T, protected
candidate:    x.value/ANY/T, plain

FLOW in both cases:
  x.value/ANY/FLOW, mx unchanged, no mark request
```

In the same branch control, omitting this new flag lets FLOW remove the marked
summary. Backward FLOW still returns `p.left/T`. The selected-mark version
returns no such answer. The all-mark cleaner does not introduce a selected T
barrier in either direction.

A possible next-iteration change is:

```kotlin
// Keep ordinary cleaning, spatial residuals and incoming annotations.
manager.transportProtection(input, out) { part, target ->
    val sink = if (sameBase && cleaner.mark != null)
        protectSelectedSurvivors(target, cleaner.mark)
    else target
    cleanFacts(part, cleaner, sink)
}
```

This changes only the creation of a **new** flag for `RemoveAllMarks`.
It must not clear an existing flag. Full kills still emit nothing. Partial
residuals, field exclusions, layers, selected cleanup, rule assignment and cycle
protection stay unchanged. It is a proposed change to demand retention, not an
implemented optimization.

The controls include disjoint, BELOW-root, partial-child, full-kill, inherited
flag, unselected-mark, other-base and later MUST/exclusion cases. A constructive
local certificate proves that an all-mark cleaner needs no selected request or
abstract-mode exclusion: each already-related concrete pair which survives has
an executable abstract output witness. The certificate does not prove a new
whole-engine normalization algorithm or authorize removal of inherited flags.

This is a justified narrow candidate, but **the captured high-fanout primitive
births use selected cleaners**. There is no measured Thingsboard saving for the
all-mark change in these captures. It must not be presented as the fix for the
901,285 protection-only memberships.

## 6. What the investigation establishes

The apparent redundancy at the concrete cleaner is real: the marked field fact
can pass unchanged. The extra protection compensates for information which
selected FLOW cleanup removes, and that dependency can matter after backward
abstraction. Clearing the flag based on the current path alone is insufficient.

For the traced callback family, a larger reduction needs a design that preserves
the selected-cleaner dependency through refinement without retaining every
protected marked relation. Such a design must pass the disjoint-root and
backward-prefix-loss regressions. Changing cleaner semantics, request emission
or handoff matching is a major change and must be specified separately.

For now, the positive narrowing is the mark-neutral all-mark adapter. No
evidence here justifies stripping selected protection at its birth, during
static FLOW application, or at `onSuccess()`.

## 7. Embedded evidence

The following sections include all three extracted cases, their source bodies,
full facts, matched FLOW candidates, the reconstructed block directory, AP
control inputs/outputs and the local Lean certificate. External paths in the
receipts are provenance labels; the data needed for this report is inline.

### 7.1 Full case data

<details>
<summary>Three real cases, complete matched FLOW rows, all 324 scalar cleaners, block directory and source receipts</summary>

```json
{
  "state": "BOUNDED_REAL_CASE_EXTRACTION_WITH_EXPLICIT_GEOMETRY_SCOPE",
  "latest_reached": "run-1",
  "latest_completed": "run-1",
  "trace": {
    "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/trace-protected-results/thingsboard/bidi/protected-trace.jsonl",
    "bytes": 257087463,
    "sha256": "097da65f85a23ddd24938f59d0230c5467f23a4fa60c426bd9f6b2ae6034862e"
  },
  "cold_form_capture": {
    "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/results/thingsboard/bidi/shapes/baseline-scoped-prefreeze.jsonl",
    "bytes": 1740260,
    "sha256": "f18ca5559346ce86e74342c938ccf95ace6fb048fe5377285c2a5ae985c967d6"
  },
  "cold_summary_capture": {
    "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/results/thingsboard/bidi/shapes/baseline-scoped-summaries.jsonl",
    "bytes": 99967803,
    "sha256": "af214ecedae525927d5d3a6238822b3299093d805d9b7a364a4c37b5f8d17ff3"
  },
  "current_diagnostic": {
    "state": "CLOSED",
    "utc": "2026-10-27T07:37:04.887571+00:00",
    "source": {
      "revision": "889f7c91e75e9343b2f95c0f13f4204872bd8731",
      "core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
      "tracked_patch_sha256": "44563e0055635a34fe02c796b4360bc9dfe1bf2b55b5975ddea94197a4fda2f9",
      "new_sources": {
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/ProtectedStaticTrace.kt": "7ff4c23650c556c314750138f170eecfa3aac9b910b38da74e438381e4ef34a7",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/Run1ProcessedWorkCounters.kt": "b0a9b39ccaacd051cfc37c6e546d0c7d674d1e792e347498f79928f5b8bcb598",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1ShapeCensus.kt": "a3cb17ab1327148c66c5ca8376e75c60e0e972a3da9a48e4d1292456eb016bc1",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/Run1TargetMethodDump.kt": "2571dec97bb8bb027e21fc3635725f4bca05c3e5bd505f949b08d511163111da",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/Run1ShapeCensusTest.kt": "c6083507f726afeef3232360fa5d40902181fe3a1ffe12204b4525482f83bf2c"
      }
    },
    "diagnostic_tests": {
      "xml": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/build/test-results/test/TEST-org.opentaint.dataflow.bidi.Run1ShapeCensusTest.xml",
      "sha256": "5004ede590fdd642cf6b78aec7b36ec8dada5184010d590dbc50fd832566f55e",
      "tests": 7,
      "failures": 0,
      "errors": 0
    },
    "config": {
      "model": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/project.yaml",
      "memory": "12g",
      "timeout": 1080,
      "outer_timeout": 1200
    },
    "rules_sha256": {
      "go/security/xss.yaml": "7598386eb5811a411a62edde1d8350838c97410cc95ad6a2d5b2e8668b0107b5",
      "go/security/trust-boundary.yaml": "f129579635d7b108c2f870dfe981541f7366b29922500832c75a10462be16ac6",
      "go/security/weak-random.yaml": "9fcfc5e4d57ff2d020f433ef2205e7016bbc6b270514d4a75c4fd9b75811966d",
      "go/security/ssti.yaml": "592cefb4c585e3b820750b8123c9cfcf8cf4fb0bfd1a0716d65624842381477f",
      "go/security/path-traversal.yaml": "8caf0137ede8fa50ed5c2eef816e0a26d691eda13460bcb86b2cd5cdf18a29d5",
      "go/security/ssrf.yaml": "9f27da42b04e175bb421f81f58768c44bf0473307fadc324e28d8b27ad16af44",
      "go/security/weak-hash.yaml": "022cd6ebf641632af284a3f1afb6acbcf22ae88ba4043d590bdbed89f6aa52d9",
      "go/security/weak-crypto.yaml": "7a9b0ec4b43b254319b24ce8192a1543b50e431e90615c4d773fc7f8a7f99f38",
      "go/security/cmdinj.yaml": "67e569171866a5e1a08350e1b48facab3c56f860dcccbed62f78431642522cc1",
      "go/security/sql-injection.yaml": "8acb09af826ad43ba6ccdbfb5e336d3bf564fb89110e713a02be662e8b1317f1",
      "go/lib/http-sources.yaml": "7e62c7007a730d11137752c95ec0210d0e2461b4a652620e387e354247457ce9",
      "go/lib/xss-sinks.yaml": "c26cb84ba8b5bc3611903b03856bf4a5d2da452bb00abd976f0cab571d867d57",
      "go/lib/sql-sinks.yaml": "931b2ab86f59c1a78d789d5eee10fa43f0a7c2d28b41ab9b0a53c4932aaf4974",
      "go/lib/http-sources-requesturi.yaml": "d43ccd94c9568e5b1f3d624286e792e688329081bfcb24ec1297c8b490591ab7",
      "go/lib/cmdi-sinks.yaml": "ca7249462753cd42b9fbd84a02f62860c351080c0b15decee4ec8fa5a92920aa",
      "go/lib/http-sources-header-index.yaml": "6b103aa8b154d193e91bd15c7e34574b59e0d9c9ca42a87755232c6f755caf2a",
      "go/lib/path-sinks.yaml": "ebccf806678a169e29bd77897ba7d0d441ec7e2ae88729692df2f7838730de30",
      "go/lib/ssrf-sinks.yaml": "92484446a8b0871f51fcb67bb2cbc5f909be2a365a7ce3ff56c3af14ac80dbd3",
      "go/lib/ssti-sinks.yaml": "dea210bdd21ddbabd1324c6c6799009bf15a772bd56da210fa8c78c473dc34b1",
      "java/security/external-configuration-control.yaml": "4f79551089f91c61c4f25470aead611bcecd913dd3bcf88971f69edba614a0a1",
      "java/security/strings.yaml": "7eaaa210550068f15522bfcb60755237d0dafa81365ec1fb61528a5714256e5e",
      "java/security/unvalidated-redirect.yaml": "744210834142e43b78d26481c28c3c3c25c3cf1c93b257ebf7f00ac7f9671e0d",
      "java/security/xss.yaml": "59abf24316a0c280cfeb15fad0e6a89973846118e0c6a163b1074f60b4ebaaa7",
      "java/security/permissions.yaml": "4578204fe67bfa7fcdbb96058109acc3e8b9025d15fb7fc14c03138545f36afd",
      "java/security/ldap.yaml": "9995c353ab5997e710167dfe5886fdddd83287d93d42934ee79b1e2ea51a15c4",
      "java/security/csrf.yaml": "4a8cb0db5cb44f84a4f8d5a0e01aa913eee96f0309658a3b8ec7c2b9b23f3c03",
      "java/security/command-injection.yaml": "471f72c537fff18678323ea78fc4cfb4528529ded93a66e705143708e3b4e243",
      "java/security/hardcoded-credentials.yaml": "ff8a876daf7e08c3842b09278e68be7cb4dac7aff26c550e6c6f011823a28110",
      "java/security/xxe.yaml": "4cc0efba1e3b769ed764e40244c4afe8f5da5eda7f27ee9819936b62a8c2a7ef",
      "java/security/data-query-injection.yaml": "d7fe4ecc2dadd55a4ff7d0f32305d49338f2eba0526cf15f74ed34e1b2125362",
      "java/security/code-injection.yaml": "674a66c99a7f572b0e43894c720412354af42771a10db81ba9aff36585968c08",
      "java/security/weak-authentication.yaml": "a639264fe629eb8712d69864d70987eea5825c832d1ee227b74354f1b166b345",
      "java/security/log-injection.yaml": "076e2a99cf9f7099f79721689f4a63705023dc06c3cbbcf48ef5354701479c7c",
      "java/security/path-traversal.yaml": "d160e3d09ddd56d3fd6f508b0be7f33f8c8c91d721a833a0309e0d349242a9ad",
      "java/security/ssrf.yaml": "17b8b8baa4ce771e9f8f14c989963142c79f721819ec10f8ea509bd1035763cf",
      "java/security/unsafe-deserialization.yaml": "e416638ac8a6b612317a059d610645712087210781b5d2c7e7f85b2215514cd4",
      "java/security/sensitive-data-exposure.yaml": "e803245e749765cba0694cd4e9bef4683e336875c8aa6feea47e792b3c6aebca",
      "java/security/insecure-design.yaml": "ce7c8fb6e32bfa085351db4bb3ddff3f8995035c40ce61587bf4a6bcc0ccdf3b",
      "java/security/crypto.yaml": "79648c02b3d67d8c972707f8550c9b48018260ff42b457f7d7250006e1f1d19f",
      "java/security/crlf-injection.yaml": "9ba98705e53a0883577ad3a4ab4ae2f807ada7c1f986dd61322359c230303e0c",
      "java/security/sqli.yaml": "c2c6193aa471e640b872f25e1f9f33a8620ce620faaa48a476d0234f5f20234e",
      "java/lib/spring/untrusted-path-source.yaml": "b8554f58f17dab28e7e8135372257d12a62b2a9931b347de27b1bd506345eb07",
      "java/lib/spring/spel-injection-sinks.yaml": "af14a60b8d08db2eeb561d4565eaca0a764bda01f1049d5c36f2eee0429e747f",
      "java/lib/spring/unvalidated-redirect-sinks.yaml": "336f2a59d57920ce13e096b5332948da577b1453082db377fee94d6393f73437",
      "java/lib/spring/spring-xss-html-response-sinks.yaml": "33c108d181018a4acbadaaa7f0eccd5eeb91b26e90645b5575ce850f9ac41c01",
      "java/lib/spring/spring-response-injection-sinks.yaml": "b8e98bd060a96ed2d567473e7521632536e1c9893fee1ef5d5690f2c96757213",
      "java/lib/spring/jdbc-sqli-sinks.yaml": "aacd5f40f39fd013ab54d45f5ee8ab2419c8c253c93f9b91efe4c7ffa19d4428",
      "java/lib/spring/untrusted-data-source.yaml": "2064e06e7c5d2be491dd360a761317606c0c299a44d246221ef447ac56ddc2a5",
      "java/lib/generic/servlet-xss-html-response-sinks.yaml": "35f32e0a3351148401f77f0b16674da2d6c184cfc746a0494715b15b895af86b",
      "java/lib/generic/unsafe-deserialization-sinks.yaml": "12693762cce1e9905f5bef1b95d808165f7e9fd9bd401c559896f229515104d2",
      "java/lib/generic/data-query-injection-sinks.yaml": "f215196e7f3b1965444dffec1e6d0112c5440241201becb711397da9359f0a52",
      "java/lib/generic/command-injection-sinks.yaml": "b1104c17dad012c3d73ffa0602fa66790b11efc18417652b3119e3b43bc4379c",
      "java/lib/generic/unsafe-reflection.yaml": "c745378c5cd944fc4c924f8e06a58da49e0a5cdda91c07c02125d974d78561e2",
      "java/lib/generic/path-traversal-sinks.yaml": "75a9d91621590e75276bf9732fac31af27711964ce00cf8d44637b245ea5b7ab",
      "java/lib/generic/smtp-injection-sinks.yaml": "e694e2a6981d2e48d57b54016edcb53883fd860f746e0ab1dec71412e0a024e6",
      "java/lib/generic/ldap-injection-sinks.yaml": "fce498992a7e12a0d7787ae077241bdcef4aea85f6d8da3fb5dda57abf968a0e",
      "java/lib/generic/code-injection-sinks.yaml": "aa91aa30a4eb5cfff2aface852c7eb4ca3b2a809d743ed286cfb93309871d41c",
      "java/lib/generic/logging-sinks.yaml": "92ac8024aad92b8dd3508c3c0f6c756c37f5302e5539d993ee3ad8d9e1f1789e",
      "java/lib/generic/template-injection-sinks.yaml": "a68af1682c2894035b7725dade0d227996a85cc34dccc13cde402e7146f7d3db",
      "java/lib/generic/seam-untrusted-data-source.yaml": "7496c7e40c0b6e65f825d68a585e80523a057ada57e9627062d430a129b265b8",
      "java/lib/generic/xxe-sinks.yaml": "cd5545038cde3dfae636a749f80afe6a60f52a1550e4c0760301a4cea9fbddac",
      "java/lib/generic/servlet-unvalidated-redirect-sinks.yaml": "a9fab487056aaa98332cef6734c636ae690b5fd322e183142d5df61b3a139f46",
      "java/lib/generic/ssrf-sinks.yaml": "cb8f90f79330c87936febeff68b68e84c90517279bf30fdd1b223f480dc41d09",
      "java/lib/generic/http-response-splitting-sinks.yaml": "76dd49a15d0b0ac6c58ee056384bec4e629574b983f74dc2bd62e02b03110772",
      "java/lib/generic/servlet-response-injection-sinks.yaml": "e051b43c7d3e45164acd8bd5ae31756f512a1e49d9f87e5f1c6cd6aa8ac89b78",
      "java/lib/generic/servlet-untrusted-data-source.yaml": "ffddc9b1ee8785c9d7bb80d49cc2e02b9e830a2f0e552d12326c1d3bb0b61c23"
    },
    "model_sha256": "1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3",
    "script_sha256": "2c38df809196aa790d30e247d444e8ba409e0a88a90a7e45ed71ad08fb1f191b",
    "scope": "Second diagnostic fixedThingsboard run; read-only bounded selected-mark PROTECTED alias/protection observations, per-category capacity. First plain-prefix capture remains preserved. Not timing or new semantics. Stop after completed run1 joined/persisted diagnosticbarrier.",
    "tracked_patch_file": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/source-review/trace-full.patch",
    "ended_utc": "2026-10-27T07:47:25.544806+00:00",
    "summary": {
      "status": "OK",
      "gradle_exit": 0,
      "analyzer_exit": 0,
      "command_wall_seconds": 620.5699297487736,
      "wall_seconds": 620.6054872274399,
      "peak_rss_bytes": 14946619392,
      "analysis_started_elapsed": 35.108167976140976,
      "full_started_elapsed": 194.36474952101707,
      "profiles": {
        "normal": {
          "start_elapsed": 254.4442914277315,
          "duration_requested": 30,
          "requested_delay_seconds": 60,
          "anchor": "run-1-engine",
          "latest_run": 1,
          "engine_active": true,
          "end_observed_elapsed": 285.5033019632101,
          "end_latest_run": 1,
          "end_engine_active": true,
          "return_code": 0
        }
      },
      "continuous_jfr": true,
      "run1_recording": {
        "returncode": 0,
        "output": "1291272:\nDumped recording, 176.6 MB written to:\n\n/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/trace-protected-results/thingsboard/bidi/run1.jfr\n",
        "elapsed": 540.8585750758648,
        "latest_run": 1
      },
      "sarif": true,
      "latest_bidi_iteration": "run-1",
      "latest_complete_bidi_iteration": "run-1",
      "latest_accepted_forward_report": "run-1",
      "bidi_iteration_progress": {
        "state": "AVAILABLE",
        "latest_reached": {
          "state": "AVAILABLE",
          "label": "run-1",
          "source": "BIDI_RUN_START",
          "engine_end_seen": true,
          "engine_status": "COMPLETE",
          "run": 1,
          "direction": "FORWARD",
          "limit": 1,
          "timeout": "15m 19.899629358s markMode=FULL",
          "timeout_seconds": 919.899629358,
          "start_line": "07:40:19.266 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=15m 19.899629358s markMode=FULL",
          "status": "COMPLETE",
          "engine_time": "5m 46.440959757s",
          "engine_seconds": 346.440959757,
          "end_line": "07:46:05.707 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=5m 46.440959757s",
          "barrier_time": "26.158746678s",
          "barrier_seconds": 26.158746678,
          "iteration_time": "6m 12.623055007s",
          "iteration_seconds": 372.623055007,
          "barrier_line": "07:46:31.889 |I| IterationDriver - BIDI_BARRIER_END run=1 barrierTime=26.158746678s iterationTime=6m 12.623055007s"
        },
        "latest_complete_engine": {
          "state": "AVAILABLE",
          "label": "run-1",
          "source": "BIDI_RUN_END status=COMPLETE",
          "engine_end_seen": true,
          "engine_status": "COMPLETE",
          "run": 1,
          "direction": "FORWARD",
          "limit": 1,
          "timeout": "15m 19.899629358s markMode=FULL",
          "timeout_seconds": 919.899629358,
          "start_line": "07:40:19.266 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=15m 19.899629358s markMode=FULL",
          "status": "COMPLETE",
          "engine_time": "5m 46.440959757s",
          "engine_seconds": 346.440959757,
          "end_line": "07:46:05.707 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=5m 46.440959757s"
        },
        "latest_accepted_forward_report": {
          "state": "AVAILABLE",
          "label": "run-1",
          "source": "Run N (FORWARD) frontier after report.add",
          "engine_end_seen": true,
          "engine_status": "COMPLETE",
          "run": 1,
          "direction": "FORWARD",
          "limit": 1,
          "timeout": "15m 19.899629358s markMode=FULL",
          "timeout_seconds": 919.899629358,
          "start_line": "07:40:19.266 |I| IterationDriver - BIDI_RUN_START run=1 direction=FORWARD limit=1 timeout=15m 19.899629358s markMode=FULL",
          "status": "COMPLETE",
          "engine_time": "5m 46.440959757s",
          "engine_seconds": 346.440959757,
          "end_line": "07:46:05.707 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=5m 46.440959757s",
          "forward_frontier_line": "07:46:31.317 |I| FrontierKt$frontierLogger$1 - Run 1 (FORWARD) frontier: analysed 37378, demand edges 2078055 in 73599 method keys, left 34, record crossings 0, DEMAND 95058, CONFIRMED 0, seeds 141974, zero only 36291 (184238 edges)"
        },
        "invalid_run_start_lines": [],
        "limits": "Latest reached follows actual start-marker order, including failed or unfinished engines. Report updates are proven by compact forward frontiers; a report may update before a later barrier failure, so missing forward-frontier evidence is unavailable, not proof of an empty report."
      }
    },
    "source_unchanged": true
  },
  "old_diagnostic": {
    "file": {
      "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/campaign.json",
      "bytes": 16407,
      "sha256": "05f88ee882bf01f4c533f2ce3755da4b1d3c6d045edb95d9892ad5b8697209dd"
    },
    "source": {
      "revision": "583a58063ab67ad18b8664d45badee065e68fd85",
      "core_tree": "e3ede1a36d3b04d79a23cc93285f385ecd968dbf",
      "tracked_patch_sha256": "a7387c08abcc7718f720fd1542aa179fcd88767bd2af744c364c8113f1160649",
      "added_sources": {
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineRun1ShapeCensus.kt": "364b33728b195cb818d745fe34f98420f77d683f12ee2015e8b12402f1167103",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineScopedPointDump.kt": "cc3dc4fb63c1c7d001dcedfe54b48fff58c2c4389492565f2337f4205f52c76a",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/BaselineScopedSummaryDump.kt": "9d3188bba9407f1f35c3fc384b7aa956f46b5586190096df6320d13145e1f4cf",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineRun1ShapeCensusTest.kt": "24b4fff6f6dbe0fbc303d01b61fa4792305ef540d4984e494063e0abacc9f93c",
        "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/BaselineScopedSummaryDumpTest.kt": "dd8e1f03aeabf0f06f4c0eb9b249c9dd74eb01c09133af0938936a6f739be062"
      }
    }
  },
  "case_count": 3,
  "cases": [
    {
      "case": "device-auth-error",
      "latest_reached": "run-1",
      "latest_completed": "run-1",
      "current_flag_birth": {
        "line": 1,
        "row_sha256": "2979bced7bff53e91d0e86f0757d22c08783080fbb676cb8a9a52412f632dd91",
        "record": {
          "event": "new_flag",
          "method": "org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable) [{}]",
          "initial": [
            {
              "base": "arg(0)",
              "path_ids": [],
              "path": [],
              "path_full": [],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@175628ea, method=org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable), context=org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable) [{}], statement=%7.<init>(body, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
          "input": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": []
          },
          "result": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ]
          },
          "extra": null,
          "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
          "stack": [
            "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
            "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
            "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
            "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
            "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
            "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
            "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
            "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
          ]
        }
      },
      "origin_classification": "Local selected-FULL cleanup survivor flag birth. Not all-mark cleanup, source assignment, summary cycle, or merely inherited selected-T flag. Input selected-T mask is empty.",
      "cleaner": {
        "exact_current_geometry": null,
        "position_relation": "UNDETERMINED_FROM_CAPTURE",
        "kind": "selected FULL return cleanup; actual geometry not serialized",
        "evidence_status": "SAME_API_DESCRIPTOR_ONLY",
        "matched_Telemetry_candidate": {
          "base": "<this>",
          "path": [],
          "reach": "EXACT",
          "selected_marks_include_T": true,
          "T": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
          "kind": "selected FULL return rewriter, not RemoveAllMarks",
          "evidence_status": "SHARED_API_DESCRIPTOR_INFERENCE_ONLY",
          "current_live_descriptor_serialized": false,
          "classification_if_matched_geometry": "DISJOINT: a nonempty Body/Body.Element path cannot denote the exact receiver root. No spatial part of the fact is cleaned.",
          "not_inferred": "No PART/INSIDE case is asserted for an unobserved current descriptor."
        },
        "warning": "The matched API descriptor is not proof of this call-site block geometry. No DISJOINT, PART or INSIDE label is asserted for this case."
      },
      "source_body": {
        "label": "DeviceAuthCallback",
        "path": "common/transport/http/src/main/java/org/thingsboard/server/transport/http/DeviceApiController.java",
        "file_sha256": "63ca855c165bc79f4f5734d378d941fe23f4591fc0092ad86da27eab9abd7a5f",
        "start_line": 451,
        "end_line": 476,
        "snippet_sha256": "fd02afb7c47cf77793bd2ed41bf0744c629da3212b3778a249e132057f271c0e",
        "body": "    static class DeviceAuthCallback implements TransportServiceCallback<ValidateDeviceCredentialsResponse> {\n        private final TransportContext transportContext;\n        private final DeferredResult<ResponseEntity> responseWriter;\n        private final Consumer<SessionInfoProto> onSuccess;\n\n        @Override\n        public void onSuccess(ValidateDeviceCredentialsResponse msg) {\n            if (msg.hasDeviceInfo()) {\n                onSuccess.accept(SessionInfoCreator.create(msg, transportContext, UUID.randomUUID()));\n            } else {\n                responseWriter.setResult(new ResponseEntity<>(HttpStatus.UNAUTHORIZED));\n            }\n        }\n\n        @Override\n        public void onError(Throwable e) {\n            String body = null;\n            if (e instanceof HttpMessageNotReadableException || e instanceof JsonParseException) {\n                body = e.getMessage();\n                log.debug(\"Failed to process request in DeviceAuthCallback: {}\", body);\n            } else {\n                log.warn(\"Failed to process request in DeviceAuthCallback\", e);\n            }\n            responseWriter.setResult(new ResponseEntity<>(body, HttpStatus.INTERNAL_SERVER_ERROR));\n        }\n    }"
      },
      "class_constructor_binding": {
        "class_file": {
          "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/classes/c36_classes_36/org/thingsboard/server/transport/http/DeviceApiController$DeviceAuthCallback.class",
          "bytes": 4382,
          "sha256": "3d4e20c1f74ac5c62b0b51d7944fbf046d498c09dfde33792f8a1f249c1ab79c"
        },
        "ResponseEntity_constructor_references": [
          {
            "constant_pool_index": 47,
            "class": "org/springframework/http/ResponseEntity",
            "method": "<init>",
            "descriptor": "(Lorg/springframework/http/HttpStatusCode;)V"
          },
          {
            "constant_pool_index": 90,
            "class": "org/springframework/http/ResponseEntity",
            "method": "<init>",
            "descriptor": "(Ljava/lang/Object;Lorg/springframework/http/HttpStatusCode;)V"
          }
        ],
        "limit": "Constant-pool references and matching Java call source identify available overloads; this is not an instruction-offset history."
      },
      "FLOW_counterparts": {
        "status": "UNAVAILABLE_NOT_EMPTY",
        "point_records": null,
        "raw_summary_records_with_all_matching_initial_FLOW": null,
        "limitations": "Old point facts include the limit1 cut; they are not the unlogged current bound transient FLOW input. No current DeviceAuth/DeviceController FLOW snapshot exists in these artifacts."
      },
      "local_flag_need": "For the reconstructed root-EXACT geometry, spatial disjointness proves only that concrete cleanup is an identity on this region. It does NOT prove that a NEW protection flag can be omitted for handoff. Base-wide FLOW exclusions and later backward prefix loss can require the marked dependency even for this identity transfer. No flag-removal conclusion is justified by this local observation alone.",
      "subsumption_limit": "In the matched Telemetry snapshot, FLOW already excludes T after cleanup, so removing the flag alone does not make that local FLOW candidate cover T."
    },
    {
      "case": "telemetry-attribute-keys",
      "latest_reached": "run-1",
      "latest_completed": "run-1",
      "current_flag_birth": {
        "line": 74,
        "row_sha256": "951c4645f40d51bbbb84700ac092defba7ce6382fa94d4286ef9a4776d5f3b55",
        "record": {
          "event": "new_flag",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "initial": [
            {
              "base": "arg(0)",
              "path_ids": [],
              "path": [],
              "path_full": [],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@7dc5753, method=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List), context=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}], statement=%8.<init>(keys, %9)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
          "input": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596,
                  640
                ],
                "path": [
                  "HttpEntity#Body",
                  "Iterable#Element"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body",
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": []
          },
          "result": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596,
                  640
                ],
                "path": [
                  "HttpEntity#Body",
                  "Iterable#Element"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body",
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": [
              {
                "base": "<this>",
                "path_ids": [
                  5596,
                  640
                ],
                "path": [
                  "HttpEntity#Body",
                  "Iterable#Element"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body",
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ]
          },
          "extra": null,
          "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
          "stack": [
            "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
            "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
            "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
            "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
            "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
            "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
            "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
            "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
          ]
        }
      },
      "origin_classification": "Local selected-FULL cleanup survivor flag birth. Not all-mark cleanup, source assignment, summary cycle, or merely inherited selected-T flag. Input selected-T mask is empty.",
      "cleaner": {
        "base": "<this>",
        "path": [],
        "reach": "EXACT",
        "selected_marks_include_T": true,
        "T": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
        "kind": "selected FULL return rewriter, not RemoveAllMarks",
        "evidence_status": "COLD_MATCHED_CALL_PLUS_SOURCE_RECONSTRUCTED_BULK_BLOCK",
        "current_live_descriptor_serialized": false,
        "classification_if_matched_geometry": "DISJOINT: a nonempty Body/Body.Element path cannot denote the exact receiver root. No spatial part of the fact is cleaned.",
        "not_inferred": "No PART/INSIDE case is asserted for an unobserved current descriptor."
      },
      "source_body": {
        "label": "getAttributeKeysToResponseCallback",
        "path": "application/src/main/java/org/thingsboard/server/controller/TelemetryController.java",
        "file_sha256": "a1702db14e899c4ef8280915908cf28c7aa021882e47df44b0aefd4ae90b95d6",
        "start_line": 779,
        "end_line": 794,
        "snippet_sha256": "15b449dfcdaa3d61de1c830d550d261f3b2230765b160a1888d32114c45492d7",
        "body": "    private FutureCallback<List<AttributeKvEntry>> getAttributeKeysToResponseCallback(final DeferredResult<ResponseEntity> response) {\n        return new FutureCallback<List<AttributeKvEntry>>() {\n\n            @Override\n            public void onSuccess(List<AttributeKvEntry> attributes) {\n                List<String> keys = attributes.stream().map(KvEntry::getKey).collect(Collectors.toList());\n                response.setResult(new ResponseEntity<>(keys, HttpStatus.OK));\n            }\n\n            @Override\n            public void onFailure(Throwable e) {\n                log.error(\"Failed to fetch attributes\", e);\n                AccessValidator.handleError(e, response, HttpStatus.INTERNAL_SERVER_ERROR);\n            }\n        };\n    }"
      },
      "class_constructor_binding": {
        "class_file": {
          "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/classes/c8_classes_8/org/thingsboard/server/controller/TelemetryController$6.class",
          "bytes": 3738,
          "sha256": "a056eec50fcd72df705b717ab6224d77e36390ca3ed97d5019330fb099a7204c"
        },
        "ResponseEntity_constructor_references": [
          {
            "constant_pool_index": 51,
            "class": "org/springframework/http/ResponseEntity",
            "method": "<init>",
            "descriptor": "(Ljava/lang/Object;Lorg/springframework/http/HttpStatusCode;)V"
          }
        ],
        "limit": "Constant-pool references and matching Java call source identify available overloads; this is not an instruction-offset history."
      },
      "FLOW_counterparts": {
        "status": "OLD_MATCHED_METHOD_COMPLETE_RETAINED_CANDIDATES",
        "point_records": [
          {
            "line": 51,
            "row_sha256": "78baf458864cf760109e8599ec8b707bbb83203f25abbac099d0b3fb51da1e0a",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "arg(0)",
                "path_ids": [],
                "path": [],
                "tail": "STAR",
                "mark": {
                  "kind": "FLOW",
                  "excluded": []
                },
                "field_exclusion": "Empty"
              },
              "layer": "NORMAL",
              "protected": null,
              "index": 1,
              "statement": "goto JIRInstRef(index=12)",
              "successors": [
                12
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 52,
            "row_sha256": "b77fb426968970d84707872968ae124022542cbeefec31912f10682018625b40",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(0)",
                "path_ids": [
                  1000
                ],
                "path": [
                  "java.util.stream.BaseStream.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 1,
              "statement": "goto JIRInstRef(index=12)",
              "successors": [
                12
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 67,
            "row_sha256": "d017cd072453b336fc04ddac97d6182ec06201f3ef2ba3eac787a921207fb228",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(0)",
                "path_ids": [
                  1000
                ],
                "path": [
                  "java.util.stream.BaseStream.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 3,
              "statement": "%3 = java.util.stream.Collectors.toList()",
              "successors": [
                4
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 68,
            "row_sha256": "51914f8c65474c00ca5ff6f5deaf1ea99e4c7b338d24cf443f5c1a6043d8ebcb",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(2)",
                "path_ids": [
                  1000
                ],
                "path": [
                  "java.util.stream.BaseStream.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 3,
              "statement": "%3 = java.util.stream.Collectors.toList()",
              "successors": [
                4
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 96,
            "row_sha256": "4e52906fdd8376cd72ab57b38aae7feecc4097280b358641f1a61bf01b220312",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(4)",
                "path_ids": [
                  640
                ],
                "path": [
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 5,
              "statement": "keys = (java.util.List<E>) %4",
              "successors": [
                6
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 97,
            "row_sha256": "8f7d9696d2a67a7f414e12a00d61ef5ac8874e238119f5791cb458c5d4bdfad7",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(4)",
                "path_ids": [
                  1000
                ],
                "path": [
                  "java.util.stream.BaseStream.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 5,
              "statement": "keys = (java.util.List<E>) %4",
              "successors": [
                6
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 98,
            "row_sha256": "52490e178c51f6e1f0c20c924ceb214466bf478d4826163beaebe2d1b161cc27",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(2)",
                "path_ids": [
                  1000
                ],
                "path": [
                  "java.util.stream.BaseStream.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 5,
              "statement": "keys = (java.util.List<E>) %4",
              "successors": [
                6
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 108,
            "row_sha256": "ee01f9969a9fac51d0b3892ef0cf24ade01f4a800a0611b2f25ef2a5688c2119",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(4)",
                "path_ids": [
                  640
                ],
                "path": [
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 6,
              "statement": "%7 = this.val$response",
              "successors": [
                7
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 109,
            "row_sha256": "d484fbf6bcdb5c40180007a8b8d81acc5db4abd99e8d96dd476198942479092e",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(6)",
                "path_ids": [
                  640
                ],
                "path": [
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 6,
              "statement": "%7 = this.val$response",
              "successors": [
                7
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 456,
            "row_sha256": "58bae5eb45d95ec08ba6e126da71e57752f7af28a6c92071395602de4367ce91",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(8)",
                "path_ids": [
                  5620
                ],
                "path": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    },
                    {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    },
                    {
                      "id": 7,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                    },
                    {
                      "id": 8,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                    },
                    {
                      "id": 10,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                    },
                    {
                      "id": 12,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                    },
                    {
                      "id": 15,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                    },
                    {
                      "id": 16,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                    },
                    {
                      "id": 17,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                    },
                    {
                      "id": 29,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                    },
                    {
                      "id": 31,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                    },
                    {
                      "id": 37,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                    },
                    {
                      "id": 48,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                    },
                    {
                      "id": 58,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                    },
                    {
                      "id": 74,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                    },
                    {
                      "id": 80,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                    },
                    {
                      "id": 90,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                    },
                    {
                      "id": 95,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                    },
                    {
                      "id": 100,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                    },
                    {
                      "id": 103,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                    },
                    {
                      "id": 106,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                    },
                    {
                      "id": 108,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                    },
                    {
                      "id": 113,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                    },
                    {
                      "id": 115,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                    },
                    {
                      "id": 116,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                    },
                    {
                      "id": 117,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                    },
                    {
                      "id": 119,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                    },
                    {
                      "id": 120,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                    },
                    {
                      "id": 146,
                      "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                    },
                    {
                      "id": 166,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                    },
                    {
                      "id": 167,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                    },
                    {
                      "id": 170,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                    },
                    {
                      "id": 171,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                    },
                    {
                      "id": 173,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                    },
                    {
                      "id": 174,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                    },
                    {
                      "id": 178,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                    },
                    {
                      "id": 179,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                    },
                    {
                      "id": 181,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                    },
                    {
                      "id": 182,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                    },
                    {
                      "id": 185,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                    },
                    {
                      "id": 186,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                    },
                    {
                      "id": 192,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                    },
                    {
                      "id": 193,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                    },
                    {
                      "id": 194,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                    },
                    {
                      "id": 195,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                    },
                    {
                      "id": 199,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                    },
                    {
                      "id": 200,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 10,
              "statement": "%10 = %7.setResult(%8)",
              "successors": [
                11
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 457,
            "row_sha256": "a7083597fc89aa050058cd02a292e2f86e3945402ea3183d395b8044c4c3830e",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(6)",
                "path_ids": [
                  640
                ],
                "path": [
                  "java.lang.Iterable.Element"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 10,
              "statement": "%10 = %7.setResult(%8)",
              "successors": [
                11
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 479,
            "row_sha256": "254aa737fdfd254d0d60e81c8559b81947f75eec00c9218d1c4b02aa75de48c8",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(8)",
                "path_ids": [
                  5620
                ],
                "path": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    },
                    {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    },
                    {
                      "id": 7,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                    },
                    {
                      "id": 8,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                    },
                    {
                      "id": 10,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                    },
                    {
                      "id": 12,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                    },
                    {
                      "id": 15,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                    },
                    {
                      "id": 16,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                    },
                    {
                      "id": 17,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                    },
                    {
                      "id": 29,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                    },
                    {
                      "id": 31,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                    },
                    {
                      "id": 37,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                    },
                    {
                      "id": 48,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                    },
                    {
                      "id": 58,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                    },
                    {
                      "id": 74,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                    },
                    {
                      "id": 80,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                    },
                    {
                      "id": 90,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                    },
                    {
                      "id": 95,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                    },
                    {
                      "id": 100,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                    },
                    {
                      "id": 103,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                    },
                    {
                      "id": 106,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                    },
                    {
                      "id": 108,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                    },
                    {
                      "id": 113,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                    },
                    {
                      "id": 115,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                    },
                    {
                      "id": 116,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                    },
                    {
                      "id": 117,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                    },
                    {
                      "id": 119,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                    },
                    {
                      "id": 120,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                    },
                    {
                      "id": 146,
                      "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                    },
                    {
                      "id": 166,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                    },
                    {
                      "id": 167,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                    },
                    {
                      "id": 170,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                    },
                    {
                      "id": 171,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                    },
                    {
                      "id": 173,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                    },
                    {
                      "id": 174,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                    },
                    {
                      "id": 178,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                    },
                    {
                      "id": 179,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                    },
                    {
                      "id": 181,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                    },
                    {
                      "id": 182,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                    },
                    {
                      "id": 185,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                    },
                    {
                      "id": 186,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                    },
                    {
                      "id": 192,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                    },
                    {
                      "id": 193,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                    },
                    {
                      "id": 194,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                    },
                    {
                      "id": 195,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                    },
                    {
                      "id": 199,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                    },
                    {
                      "id": 200,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 11,
              "statement": "return",
              "successors": [
                17
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 480,
            "row_sha256": "237536b05713422904df121f89a33804f19c9ad9a718f9e59b451a8838dfe67d",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "var(7)",
                "path_ids": [
                  6432
                ],
                "path": [
                  "org.springframework.web.context.request.async.DeferredResult.Result"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    },
                    {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    },
                    {
                      "id": 7,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                    },
                    {
                      "id": 8,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                    },
                    {
                      "id": 10,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                    },
                    {
                      "id": 12,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                    },
                    {
                      "id": 15,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                    },
                    {
                      "id": 16,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                    },
                    {
                      "id": 17,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                    },
                    {
                      "id": 29,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                    },
                    {
                      "id": 31,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                    },
                    {
                      "id": 37,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                    },
                    {
                      "id": 48,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                    },
                    {
                      "id": 58,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                    },
                    {
                      "id": 74,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                    },
                    {
                      "id": 80,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                    },
                    {
                      "id": 90,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                    },
                    {
                      "id": 95,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                    },
                    {
                      "id": 100,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                    },
                    {
                      "id": 103,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                    },
                    {
                      "id": 106,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                    },
                    {
                      "id": 108,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                    },
                    {
                      "id": 113,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                    },
                    {
                      "id": 115,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                    },
                    {
                      "id": 116,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                    },
                    {
                      "id": 117,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                    },
                    {
                      "id": 119,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                    },
                    {
                      "id": 120,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                    },
                    {
                      "id": 146,
                      "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                    },
                    {
                      "id": 166,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                    },
                    {
                      "id": 167,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                    },
                    {
                      "id": 170,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                    },
                    {
                      "id": 171,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                    },
                    {
                      "id": 173,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                    },
                    {
                      "id": 174,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                    },
                    {
                      "id": 178,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                    },
                    {
                      "id": 179,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                    },
                    {
                      "id": 181,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                    },
                    {
                      "id": 182,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                    },
                    {
                      "id": 185,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                    },
                    {
                      "id": 186,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                    },
                    {
                      "id": 192,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                    },
                    {
                      "id": 193,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                    },
                    {
                      "id": 194,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                    },
                    {
                      "id": 195,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                    },
                    {
                      "id": 199,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                    },
                    {
                      "id": 200,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 11,
              "statement": "return",
              "successors": [
                17
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 481,
            "row_sha256": "7f23a0d1e8223d9768c63dd9e6c94d44aa242b68e5265e43f625cd66cd7f5fe6",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "<this>",
                "path_ids": [
                  81236
                ],
                "path": [
                  "org.thingsboard.server.controller.TelemetryController$6.val$response"
                ],
                "tail": "ANY",
                "mark": {
                  "kind": "FLOW",
                  "excluded": [
                    {
                      "id": 2,
                      "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                    },
                    {
                      "id": 3,
                      "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                      "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                    },
                    {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    },
                    {
                      "id": 7,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                    },
                    {
                      "id": 8,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                    },
                    {
                      "id": 10,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                    },
                    {
                      "id": 12,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                    },
                    {
                      "id": 15,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                    },
                    {
                      "id": 16,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                    },
                    {
                      "id": 17,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                    },
                    {
                      "id": 29,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                    },
                    {
                      "id": 31,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                    },
                    {
                      "id": 37,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                    },
                    {
                      "id": 48,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                    },
                    {
                      "id": 58,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                    },
                    {
                      "id": 74,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                    },
                    {
                      "id": 80,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                    },
                    {
                      "id": 90,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                    },
                    {
                      "id": 95,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                    },
                    {
                      "id": 100,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                    },
                    {
                      "id": 103,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                    },
                    {
                      "id": 106,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                    },
                    {
                      "id": 108,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                    },
                    {
                      "id": 113,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                    },
                    {
                      "id": 115,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                    },
                    {
                      "id": 116,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                    },
                    {
                      "id": 117,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                    },
                    {
                      "id": 119,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                    },
                    {
                      "id": 120,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                    },
                    {
                      "id": 146,
                      "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                    },
                    {
                      "id": 166,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                    },
                    {
                      "id": 167,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                    },
                    {
                      "id": 170,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                    },
                    {
                      "id": 171,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                    },
                    {
                      "id": 173,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                    },
                    {
                      "id": 174,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                    },
                    {
                      "id": 178,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                    },
                    {
                      "id": 179,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                    },
                    {
                      "id": 181,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                    },
                    {
                      "id": 182,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                    },
                    {
                      "id": 185,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                    },
                    {
                      "id": 186,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                    },
                    {
                      "id": 192,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                    },
                    {
                      "id": 193,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                    },
                    {
                      "id": 194,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                    },
                    {
                      "id": 195,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                    },
                    {
                      "id": 199,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                    },
                    {
                      "id": 200,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                    }
                  ]
                },
                "field_exclusion": "Empty"
              },
              "layer": "DEMAND",
              "protected": null,
              "index": 11,
              "statement": "return",
              "successors": [
                17
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          },
          {
            "line": 507,
            "row_sha256": "8933d71ecc21afa68da2d9374352469f71e0b45cbd72f249f1b9dc05459d68b5",
            "record": {
              "record": "point",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "mark": {
                    "kind": "FLOW",
                    "excluded": []
                  },
                  "field_exclusion": "Empty"
                }
              ],
              "output": {
                "base": "arg(0)",
                "path_ids": [],
                "path": [],
                "tail": "STAR",
                "mark": {
                  "kind": "FLOW",
                  "excluded": []
                },
                "field_exclusion": "Empty"
              },
              "layer": "NORMAL",
              "protected": null,
              "index": 16,
              "statement": "method enter",
              "successors": [
                0
              ],
              "normal_end": false,
              "exceptional_end": false
            }
          }
        ],
        "raw_summary_records_with_all_matching_initial_FLOW": [
          {
            "line": 449,
            "row_sha256": "d41ea4e9c2538f35ca6fceb418ea0c6b4b80e0dbb592d1e6d6cc51fac82d9168",
            "record": {
              "record": "summary",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "owner": "raw",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "field_exclusion": "Empty",
                  "mark": {
                    "id": 6,
                    "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                    "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                  }
                }
              ],
              "output": {
                "base": "<this>",
                "layer": "DEMAND",
                "kind": "TaintTree",
                "leaves": [
                  {
                    "base": "<this>",
                    "path_ids": [
                      81236
                    ],
                    "path": [
                      "org.thingsboard.server.controller.TelemetryController$6.val$response"
                    ],
                    "tail": "ANY",
                    "field_exclusion": "Empty",
                    "mark": {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    }
                  }
                ],
                "full_protection_mask": [
                  {
                    "base": "<this>",
                    "path_ids": [
                      81236
                    ],
                    "path": [
                      "org.thingsboard.server.controller.TelemetryController$6.val$response"
                    ],
                    "tail": "ANY",
                    "field_exclusion": "Empty",
                    "mark": {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    }
                  }
                ]
              },
              "flow_initial": {
                "base": "arg(0)",
                "path_ids": [],
                "path": [],
                "tail": "STAR",
                "field_exclusion": "Empty",
                "mark": {
                  "kind": "FLOW",
                  "excluded": []
                }
              },
              "matching_initial_FLOW": [
                {
                  "base": "arg(0)",
                  "layer": "NORMAL",
                  "kind": "FlowTree",
                  "leaves": [
                    {
                      "base": "arg(0)",
                      "path_ids": [],
                      "path": [],
                      "tail": "STAR",
                      "field_exclusion": "Empty",
                      "mark": {
                        "kind": "FLOW",
                        "excluded": []
                      }
                    }
                  ],
                  "full_protection_mask": []
                },
                {
                  "base": "<this>",
                  "layer": "DEMAND",
                  "kind": "FlowTree",
                  "leaves": [
                    {
                      "base": "<this>",
                      "path_ids": [
                        81236
                      ],
                      "path": [
                        "org.thingsboard.server.controller.TelemetryController$6.val$response"
                      ],
                      "tail": "ANY",
                      "field_exclusion": "Empty",
                      "mark": {
                        "kind": "FLOW",
                        "excluded": [
                          {
                            "id": 2,
                            "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                            "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                          },
                          {
                            "id": 3,
                            "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                            "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                          },
                          {
                            "id": 6,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                          },
                          {
                            "id": 7,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                          },
                          {
                            "id": 8,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                          },
                          {
                            "id": 10,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                          },
                          {
                            "id": 12,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                          },
                          {
                            "id": 15,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                          },
                          {
                            "id": 16,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                          },
                          {
                            "id": 17,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                          },
                          {
                            "id": 29,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                          },
                          {
                            "id": 31,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                          },
                          {
                            "id": 37,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                          },
                          {
                            "id": 48,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                          },
                          {
                            "id": 58,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                          },
                          {
                            "id": 74,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                          },
                          {
                            "id": 80,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                          },
                          {
                            "id": 90,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                          },
                          {
                            "id": 95,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                          },
                          {
                            "id": 100,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                          },
                          {
                            "id": 103,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                          },
                          {
                            "id": 106,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                          },
                          {
                            "id": 108,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                          },
                          {
                            "id": 113,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                          },
                          {
                            "id": 115,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                          },
                          {
                            "id": 116,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                          },
                          {
                            "id": 117,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                          },
                          {
                            "id": 119,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                          },
                          {
                            "id": 120,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                          },
                          {
                            "id": 146,
                            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                          },
                          {
                            "id": 166,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                          },
                          {
                            "id": 167,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                          },
                          {
                            "id": 170,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                          },
                          {
                            "id": 171,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                          },
                          {
                            "id": 173,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                          },
                          {
                            "id": 174,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                          },
                          {
                            "id": 178,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                          },
                          {
                            "id": 179,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                          },
                          {
                            "id": 181,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                          },
                          {
                            "id": 182,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                          },
                          {
                            "id": 185,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                          },
                          {
                            "id": 186,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                          },
                          {
                            "id": 192,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                          },
                          {
                            "id": 193,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                          },
                          {
                            "id": 194,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                          },
                          {
                            "id": 195,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                          },
                          {
                            "id": 199,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                          },
                          {
                            "id": 200,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                          }
                        ]
                      }
                    }
                  ],
                  "full_protection_mask": []
                }
              ]
            }
          },
          {
            "line": 468,
            "row_sha256": "8b96068eecdfa9836e1ac59333b368d1bc39337c4f9c1ab48772dab813902dc7",
            "record": {
              "record": "summary",
              "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
              "owner": "raw",
              "initial": [
                {
                  "base": "arg(0)",
                  "path_ids": [],
                  "path": [],
                  "tail": "STAR",
                  "field_exclusion": "Empty",
                  "mark": {
                    "id": 6,
                    "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                    "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                  }
                }
              ],
              "output": {
                "base": "arg(0)",
                "layer": "DEMAND",
                "kind": "TaintTree",
                "leaves": [
                  {
                    "base": "arg(0)",
                    "path_ids": [],
                    "path": [],
                    "tail": "ANY",
                    "field_exclusion": "Empty",
                    "mark": {
                      "id": 6,
                      "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                      "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                    }
                  }
                ],
                "full_protection_mask": []
              },
              "flow_initial": {
                "base": "arg(0)",
                "path_ids": [],
                "path": [],
                "tail": "STAR",
                "field_exclusion": "Empty",
                "mark": {
                  "kind": "FLOW",
                  "excluded": []
                }
              },
              "matching_initial_FLOW": [
                {
                  "base": "arg(0)",
                  "layer": "NORMAL",
                  "kind": "FlowTree",
                  "leaves": [
                    {
                      "base": "arg(0)",
                      "path_ids": [],
                      "path": [],
                      "tail": "STAR",
                      "field_exclusion": "Empty",
                      "mark": {
                        "kind": "FLOW",
                        "excluded": []
                      }
                    }
                  ],
                  "full_protection_mask": []
                },
                {
                  "base": "<this>",
                  "layer": "DEMAND",
                  "kind": "FlowTree",
                  "leaves": [
                    {
                      "base": "<this>",
                      "path_ids": [
                        81236
                      ],
                      "path": [
                        "org.thingsboard.server.controller.TelemetryController$6.val$response"
                      ],
                      "tail": "ANY",
                      "field_exclusion": "Empty",
                      "mark": {
                        "kind": "FLOW",
                        "excluded": [
                          {
                            "id": 2,
                            "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
                            "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
                          },
                          {
                            "id": 3,
                            "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
                            "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
                          },
                          {
                            "id": 6,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
                          },
                          {
                            "id": 7,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
                          },
                          {
                            "id": 8,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
                          },
                          {
                            "id": 10,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
                          },
                          {
                            "id": 12,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
                          },
                          {
                            "id": 15,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
                          },
                          {
                            "id": 16,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
                          },
                          {
                            "id": 17,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
                          },
                          {
                            "id": 29,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
                          },
                          {
                            "id": 31,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
                          },
                          {
                            "id": 37,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
                          },
                          {
                            "id": 48,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
                          },
                          {
                            "id": 58,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
                          },
                          {
                            "id": 74,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
                          },
                          {
                            "id": 80,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
                          },
                          {
                            "id": 90,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
                          },
                          {
                            "id": 95,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
                          },
                          {
                            "id": 100,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
                          },
                          {
                            "id": 103,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
                          },
                          {
                            "id": 106,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
                          },
                          {
                            "id": 108,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
                          },
                          {
                            "id": 113,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
                          },
                          {
                            "id": 115,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
                          },
                          {
                            "id": 116,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
                          },
                          {
                            "id": 117,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
                          },
                          {
                            "id": 119,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
                          },
                          {
                            "id": 120,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
                          },
                          {
                            "id": 146,
                            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
                          },
                          {
                            "id": 166,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
                          },
                          {
                            "id": 167,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
                          },
                          {
                            "id": 170,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
                          },
                          {
                            "id": 171,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
                          },
                          {
                            "id": 173,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
                          },
                          {
                            "id": 174,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
                          },
                          {
                            "id": 178,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
                          },
                          {
                            "id": 179,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
                          },
                          {
                            "id": 181,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
                          },
                          {
                            "id": 182,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
                          },
                          {
                            "id": 185,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
                          },
                          {
                            "id": 186,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
                          },
                          {
                            "id": 192,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
                          },
                          {
                            "id": 193,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
                          },
                          {
                            "id": 194,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
                          },
                          {
                            "id": 195,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
                          },
                          {
                            "id": 199,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
                          },
                          {
                            "id": 200,
                            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
                            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
                          }
                        ]
                      }
                    }
                  ],
                  "full_protection_mask": []
                }
              ]
            }
          }
        ],
        "limitations": "Old point facts include the limit1 cut; they are not the unlogged current bound transient FLOW input. No current DeviceAuth/DeviceController FLOW snapshot exists in these artifacts."
      },
      "local_flag_need": "For the reconstructed root-EXACT geometry, spatial disjointness proves only that concrete cleanup is an identity on this region. It does NOT prove that a NEW protection flag can be omitted for handoff. Base-wide FLOW exclusions and later backward prefix loss can require the marked dependency even for this identity transfer. No flag-removal conclusion is justified by this local observation alone.",
      "subsumption_limit": "In the matched Telemetry snapshot, FLOW already excludes T after cleanup, so removing the flag alone does not make that local FLOW candidate cover T."
    },
    {
      "case": "device-claim-star-body",
      "latest_reached": "run-1",
      "latest_completed": "run-1",
      "current_flag_birth": {
        "line": 78,
        "row_sha256": "2cf2cdca9a9f029323c412d9f144cd4c2dad81642e49f6b64f9c1d5b57d8c158",
        "record": {
          "event": "new_flag",
          "method": "org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}]",
          "initial": [
            {
              "base": "arg(0)",
              "path_ids": [],
              "path": [],
              "path_full": [],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@ff74793, method=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult), context=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}], statement=%16.<init>(result, status)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
          "input": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "STAR",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": []
          },
          "result": {
            "base": "<this>",
            "layer": "DEMAND",
            "selected_leaves": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "STAR",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ],
            "selected_protection": [
              {
                "base": "<this>",
                "path_ids": [
                  5596
                ],
                "path": [
                  "HttpEntity#Body"
                ],
                "path_full": [
                  "org.springframework.http.HttpEntity.Body"
                ],
                "tail": "STAR",
                "E": "Empty",
                "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
              }
            ]
          },
          "extra": null,
          "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
          "stack": [
            "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
            "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
            "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
            "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
            "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
            "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
            "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
            "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
            "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
            "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
            "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
            "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
          ]
        }
      },
      "origin_classification": "Local selected-FULL cleanup survivor flag birth. Not all-mark cleanup, source assignment, summary cycle, or merely inherited selected-T flag. Input selected-T mask is empty.",
      "cleaner": {
        "exact_current_geometry": null,
        "position_relation": "UNDETERMINED_FROM_CAPTURE",
        "kind": "selected FULL return cleanup; actual geometry not serialized",
        "evidence_status": "SAME_API_DESCRIPTOR_ONLY",
        "matched_Telemetry_candidate": {
          "base": "<this>",
          "path": [],
          "reach": "EXACT",
          "selected_marks_include_T": true,
          "T": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
          "kind": "selected FULL return rewriter, not RemoveAllMarks",
          "evidence_status": "SHARED_API_DESCRIPTOR_INFERENCE_ONLY",
          "current_live_descriptor_serialized": false,
          "classification_if_matched_geometry": "DISJOINT: a nonempty Body/Body.Element path cannot denote the exact receiver root. No spatial part of the fact is cleaned.",
          "not_inferred": "No PART/INSIDE case is asserted for an unobserved current descriptor."
        },
        "warning": "The matched API descriptor is not proof of this call-site block geometry. No DISJOINT, PART or INSIDE label is asserted for this case."
      },
      "source_body": {
        "label": "claimDevice",
        "path": "application/src/main/java/org/thingsboard/server/controller/DeviceController.java",
        "file_sha256": "ab3ad71f1fc8d026ba6879d631fc99bf42121af71fb116acf3cd1343fe7feea3",
        "start_line": 576,
        "end_line": 617,
        "snippet_sha256": "4ae7d63619f9e743b93090fa9bdcbdc713873111a37104e428f1d5b1bf5db08b",
        "body": "    public DeferredResult<ResponseEntity> claimDevice(@Parameter(description = \"Unique name of the device which is going to be claimed\")\n                                                      @PathVariable(DEVICE_NAME) String deviceName,\n                                                      @Parameter(description = \"Claiming request which can optionally contain secret key\")\n                                                      @RequestBody(required = false) ClaimRequest claimRequest) throws ThingsboardException {\n        checkParameter(DEVICE_NAME, deviceName);\n        final DeferredResult<ResponseEntity> deferredResult = new DeferredResult<>();\n\n        SecurityUser user = getCurrentUser();\n        TenantId tenantId = user.getTenantId();\n        CustomerId customerId = user.getCustomerId();\n\n        Device device = checkNotNull(deviceService.findDeviceByTenantIdAndName(tenantId, deviceName));\n        accessControlService.checkPermission(user, Resource.DEVICE, Operation.CLAIM_DEVICES,\n                device.getId(), device);\n        String secretKey = getSecretKey(claimRequest);\n\n        ListenableFuture<ClaimResult> future = tbDeviceService.claimDevice(tenantId, device, customerId, secretKey, user);\n\n        Futures.addCallback(future, new FutureCallback<>() {\n            @Override\n            public void onSuccess(@Nullable ClaimResult result) {\n                HttpStatus status;\n                if (result != null) {\n                    if (result.getResponse().equals(ClaimResponse.SUCCESS)) {\n                        status = HttpStatus.OK;\n                        deferredResult.setResult(new ResponseEntity<>(result, status));\n                    } else {\n                        status = HttpStatus.BAD_REQUEST;\n                        deferredResult.setResult(new ResponseEntity<>(result.getResponse(), status));\n                    }\n                } else {\n                    deferredResult.setResult(new ResponseEntity<>(HttpStatus.BAD_REQUEST));\n                }\n            }\n\n            @Override\n            public void onFailure(Throwable t) {\n                deferredResult.setErrorResult(t);\n            }\n        }, MoreExecutors.directExecutor());\n        return deferredResult;\n    }"
      },
      "class_constructor_binding": {
        "class_file": {
          "path": "/drive-testcomp/opentaint-go-rules/opentaint-test/opentaint-test-thingsboard/opentaint-project/classes/c8_classes_8/org/thingsboard/server/controller/DeviceController$1.class",
          "bytes": 2674,
          "sha256": "accdd3950b95efc1eefb7af299dacdb828b8514832a0a8e289aa4b42cba7de52"
        },
        "ResponseEntity_constructor_references": [
          {
            "constant_pool_index": 41,
            "class": "org/springframework/http/ResponseEntity",
            "method": "<init>",
            "descriptor": "(Ljava/lang/Object;Lorg/springframework/http/HttpStatusCode;)V"
          },
          {
            "constant_pool_index": 52,
            "class": "org/springframework/http/ResponseEntity",
            "method": "<init>",
            "descriptor": "(Lorg/springframework/http/HttpStatusCode;)V"
          }
        ],
        "limit": "Constant-pool references and matching Java call source identify available overloads; this is not an instruction-offset history."
      },
      "FLOW_counterparts": {
        "status": "UNAVAILABLE_NOT_EMPTY",
        "point_records": null,
        "raw_summary_records_with_all_matching_initial_FLOW": null,
        "limitations": "Old point facts include the limit1 cut; they are not the unlogged current bound transient FLOW input. No current DeviceAuth/DeviceController FLOW snapshot exists in these artifacts."
      },
      "local_flag_need": "For the reconstructed root-EXACT geometry, spatial disjointness proves only that concrete cleanup is an identity on this region. It does NOT prove that a NEW protection flag can be omitted for handoff. Base-wide FLOW exclusions and later backward prefix loss can require the marked dependency even for this identity transfer. No flag-removal conclusion is justified by this local observation alone.",
      "subsumption_limit": "In the matched Telemetry snapshot, FLOW already excludes T after cleanup, so removing the flag alone does not make that local FLOW candidate cover T."
    }
  ],
  "primitive_inventory": [
    {
      "line": 1,
      "row_sha256": "2979bced7bff53e91d0e86f0757d22c08783080fbb676cb8a9a52412f632dd91",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@175628ea, method=org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable), context=org.thingsboard.server.transport.http.DeviceApiController$DeviceAuthCallback#onError(java.lang.Throwable) [{}], statement=%7.<init>(body, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 13,
      "row_sha256": "17da2900764169b7f46c868a1554db23149b0cdda1f5bd15386f93a3667fbda4",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.transport.http.DeviceApiController$GetOtaPackageCallback#onError(java.lang.Throwable) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@3b73074b, method=org.thingsboard.server.transport.http.DeviceApiController$GetOtaPackageCallback#onError(java.lang.Throwable), context=org.thingsboard.server.transport.http.DeviceApiController$GetOtaPackageCallback#onError(java.lang.Throwable) [{}], statement=%7.<init>(body, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 34,
      "row_sha256": "ffe14b60430f85e34dcf025251a225e5e887d39d06c54f8cecd455403cac2369",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.transport.http.DeviceApiController$DeviceProvisionCallback#onError(java.lang.Throwable) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@2d8fe61b, method=org.thingsboard.server.transport.http.DeviceApiController$DeviceProvisionCallback#onError(java.lang.Throwable), context=org.thingsboard.server.transport.http.DeviceApiController$DeviceProvisionCallback#onError(java.lang.Throwable) [{}], statement=%7.<init>(body, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 74,
      "row_sha256": "951c4645f40d51bbbb84700ac092defba7ce6382fa94d4286ef9a4776d5f3b55",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@7dc5753, method=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List), context=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}], statement=%8.<init>(keys, %9)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 76,
      "row_sha256": "711e6e7a9ab4eafc13fd129070f357ce638a5d101971028ead4d513ecc8f8d1a",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.controller.TelemetryController$5#onSuccess(java.util.List) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@7f6e9bd6, method=org.thingsboard.server.controller.TelemetryController$5#onSuccess(java.util.List), context=org.thingsboard.server.controller.TelemetryController$5#onSuccess(java.util.List) [{}], statement=%8.<init>(keys, %9)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596,
                640
              ],
              "path": [
                "HttpEntity#Body",
                "Iterable#Element"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body",
                "java.lang.Iterable.Element"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 78,
      "row_sha256": "2cf2cdca9a9f029323c412d9f144cd4c2dad81642e49f6b64f9c1d5b57d8c158",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@ff74793, method=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult), context=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}], statement=%16.<init>(result, status)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "STAR",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 80,
      "row_sha256": "dc8d511070aa3769df1fe44d9f7a7464f0a703ae9b1872df459d56032ad4a0ac",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@ff74793, method=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult), context=org.thingsboard.server.controller.DeviceController$1#onSuccess(org.thingsboard.server.dao.device.claim.ClaimResult) [{}], statement=%10.<init>(%11, status)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 83,
      "row_sha256": "b648c12629c956f67e021cc47171b634e9a833789b74dd94f1dcfbc9b834f4ac",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus) [{}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@2afa392, method=org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus), context=org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus) [{}], statement=responseEntity.<init>(%7, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 85,
      "row_sha256": "68aa37d7efac3ce16e369103e5a78730fda0cf1ba6fc27f26a51b5548fcab4e5",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.exception.AccessDeniedException#toErrorResponseEntity() [{}]",
        "initial": [
          {
            "base": "<this>",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@5f7e028b, method=org.thingsboard.server.exception.AccessDeniedException#toErrorResponseEntity(), context=org.thingsboard.server.exception.AccessDeniedException#toErrorResponseEntity() [{}], statement=%0.<init>(%1, %2)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 90,
      "row_sha256": "04d937044a68a1b76ba462187c7eae3de108f953ff6cddce11d194ce0f5f2781",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.exception.UnauthorizedException#toErrorResponseEntity() [{}]",
        "initial": [
          {
            "base": "<this>",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@1689a93, method=org.thingsboard.server.exception.UnauthorizedException#toErrorResponseEntity(), context=org.thingsboard.server.exception.UnauthorizedException#toErrorResponseEntity() [{}], statement=%0.<init>(%1, %2)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 97,
      "row_sha256": "56f4d85e02f9caf4baeb4a3bed6137d3ae840b5d0d982c9a96787a68523cef85",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.exception.InvalidParametersException#toErrorResponseEntity() [{}]",
        "initial": [
          {
            "base": "<this>",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@5b5bd7d7, method=org.thingsboard.server.exception.InvalidParametersException#toErrorResponseEntity(), context=org.thingsboard.server.exception.InvalidParametersException#toErrorResponseEntity() [{}], statement=%0.<init>(%1, %2)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 101,
      "row_sha256": "b28a1d7fc9bb483198ebb370f56b1246f1fd15158a57f7f011ae58bed551a188",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.exception.EntityNotFoundException#toErrorResponseEntity() [{}]",
        "initial": [
          {
            "base": "<this>",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@1d1e4d49, method=org.thingsboard.server.exception.EntityNotFoundException#toErrorResponseEntity(), context=org.thingsboard.server.exception.EntityNotFoundException#toErrorResponseEntity() [{}], statement=%0.<init>(%1, %2)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 104,
      "row_sha256": "7d2e9aeeecf8b0d0eda4cac3c4c398f8fe80d50e8ec58ed30da8b303a3ff55b1",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.exception.InternalErrorException#toErrorResponseEntity() [{}]",
        "initial": [
          {
            "base": "<this>",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@72562b84, method=org.thingsboard.server.exception.InternalErrorException#toErrorResponseEntity(), context=org.thingsboard.server.exception.InternalErrorException#toErrorResponseEntity() [{}], statement=%0.<init>(%1, %2)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    },
    {
      "line": 317,
      "row_sha256": "a4019e771a4f6f5b41c3d6d86624ce6144f7a03cf51411dd8e6ca232bb4af240",
      "record": {
        "event": "new_flag",
        "method": "org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus) [{arg(0) is java.lang.Exception}]",
        "initial": [
          {
            "base": "arg(0)",
            "path_ids": [],
            "path": [],
            "path_full": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@481ee72b, method=org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus), context=org.thingsboard.server.service.security.AccessValidator#handleError(java.lang.Throwable, org.springframework.web.context.request.async.DeferredResult, org.springframework.http.HttpStatus) [{arg(0) is java.lang.Exception}], statement=responseEntity.<init>(%7, %8)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
        "input": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": []
        },
        "result": {
          "base": "<this>",
          "layer": "DEMAND",
          "selected_leaves": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ],
          "selected_protection": [
            {
              "base": "<this>",
              "path_ids": [
                5596
              ],
              "path": [
                "HttpEntity#Body"
              ],
              "path_full": [
                "org.springframework.http.HttpEntity.Body"
              ],
              "tail": "ANY",
              "E": "Empty",
              "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
            }
          ]
        },
        "extra": null,
        "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
        "stack": [
          "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
          "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
          "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
          "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
          "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
          "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
          "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
          "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
          "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
          "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
          "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
          "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
        ]
      }
    }
  ],
  "primitive_inventory_count": 14,
  "bulk_reconciliation": {
    "start": 90,
    "end_exclusive": 100,
    "raw_step_count": 10,
    "unique_selected_marks": 7,
    "mark_names": [
      "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
      "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_95;$H;5"
    ],
    "selected_T_raw_ordinals": [
      94
    ],
    "preceding_raw_step": {
      "line": 215,
      "row_sha256": "283f2222bcac998428a900aee808f76849047118473005a6b5c3835ef6e08f14",
      "record": {
        "record": "cleaner",
        "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
        "ordinal": 89,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "mark": {
          "id": 146,
          "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
        },
        "index": 9,
        "statement": "%8.<init>(keys, %9)",
        "successors": [
          10
        ],
        "normal_end": false,
        "exceptional_end": false,
        "from": "RETURNED",
        "to": "REWRITTEN"
      }
    },
    "following_raw_step": {
      "line": 226,
      "row_sha256": "819d4228863e6697bb6a0a20472c152274d3da261fa0dd80cab94fc0f26797d3",
      "record": {
        "record": "cleaner",
        "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
        "ordinal": 100,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "mark": {
          "id": 199,
          "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
        },
        "index": 9,
        "statement": "%8.<init>(keys, %9)",
        "successors": [
          10
        ],
        "normal_end": false,
        "exceptional_end": false,
        "from": "RETURNED",
        "to": "REWRITTEN"
      }
    },
    "all_10_complete_block_raw_steps": [
      {
        "line": 216,
        "row_sha256": "4aef6399b19bfc523be1f0c77f95aefa9649be4010654efb7579d2d7582617d6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 90,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 217,
        "row_sha256": "69395f6727441a8378c2c1224e7f784ce96bce604b90af9372cb498b79a250c6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 91,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 218,
        "row_sha256": "a2b64bbbfb630b5cc55f1ff71b4357e7f4584be099894ce2175507daeaee8db7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 92,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 219,
        "row_sha256": "f8f6d118c2f7035076d101d652a0ea303cea93130b43c878bcef8943478cbf75",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 93,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 220,
        "row_sha256": "01fbebff7840fb30134cbf2edb7ed1cbfb3e30841a6e06f9ab747d45760efc84",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 94,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 6,
            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 221,
        "row_sha256": "e5d18dac5abf02a1ab12d64e3254f9728d5bec40c1221e3aaa1b844ea210cefa",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 95,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 222,
        "row_sha256": "574373279deeec13b340c510cbc81f55103ff7dfd53b8d7a7f9bb1fc533848f9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 96,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 106,
            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 223,
        "row_sha256": "17463f263082656f0f5b4e767cd76c8b4f6c0c3857a893b5e85d5b2cf3e8102e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 97,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 224,
        "row_sha256": "dbf2128fee7b3adcb6dba866be7845288a915e31dd9cd923a5b0b558e6e9fcc3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 98,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 103,
            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 225,
        "row_sha256": "8c26e6c8dab6debbdbd52ca97e180885a5e4af17e99da0c8f2f11e3969bc61a3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 99,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      }
    ],
    "all_55_blocks": [
      {
        "first": 0,
        "end_exclusive": 2,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 2,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 2,
        "end_exclusive": 6,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 6,
        "end_exclusive": 14,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 8,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 14,
        "end_exclusive": 18,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 18,
        "end_exclusive": 24,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 6,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 24,
        "end_exclusive": 28,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 28,
        "end_exclusive": 38,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 10,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 38,
        "end_exclusive": 42,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 42,
        "end_exclusive": 48,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 6,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 48,
        "end_exclusive": 52,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 52,
        "end_exclusive": 60,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 8,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 60,
        "end_exclusive": 64,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 64,
        "end_exclusive": 78,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 14,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 78,
        "end_exclusive": 82,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 82,
        "end_exclusive": 86,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 86,
        "end_exclusive": 90,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 90,
        "end_exclusive": 100,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 10,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5"
        ],
        "T_raw_ordinals": [
          94
        ]
      },
      {
        "first": 100,
        "end_exclusive": 104,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 104,
        "end_exclusive": 108,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 108,
        "end_exclusive": 112,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 112,
        "end_exclusive": 116,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 116,
        "end_exclusive": 120,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 120,
        "end_exclusive": 124,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 124,
        "end_exclusive": 128,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 128,
        "end_exclusive": 146,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 18,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": [
          142
        ]
      },
      {
        "first": 146,
        "end_exclusive": 150,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 150,
        "end_exclusive": 158,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 8,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 158,
        "end_exclusive": 162,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 162,
        "end_exclusive": 166,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 166,
        "end_exclusive": 170,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 170,
        "end_exclusive": 180,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 10,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 180,
        "end_exclusive": 184,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 184,
        "end_exclusive": 198,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 14,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 198,
        "end_exclusive": 202,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 202,
        "end_exclusive": 208,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 6,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 208,
        "end_exclusive": 212,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 212,
        "end_exclusive": 216,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 216,
        "end_exclusive": 220,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 220,
        "end_exclusive": 224,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_71;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 224,
        "end_exclusive": 228,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 228,
        "end_exclusive": 232,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_107;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 232,
        "end_exclusive": 236,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 236,
        "end_exclusive": 248,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 12,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 248,
        "end_exclusive": 252,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 252,
        "end_exclusive": 258,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 6,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_83;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 258,
        "end_exclusive": 262,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 262,
        "end_exclusive": 270,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 8,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 270,
        "end_exclusive": 274,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 274,
        "end_exclusive": 280,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 6,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 280,
        "end_exclusive": 284,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 284,
        "end_exclusive": 296,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 12,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": [
          292
        ]
      },
      {
        "first": 296,
        "end_exclusive": 300,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 300,
        "end_exclusive": 304,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_23;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 304,
        "end_exclusive": 308,
        "base": "arg(1)",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 4,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5"
        ],
        "T_raw_ordinals": []
      },
      {
        "first": 308,
        "end_exclusive": 324,
        "base": "<this>",
        "path": null,
        "reach": "EXACT",
        "raw_steps": 16,
        "unique_mark_names": [
          "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
          "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
          "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
          "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
          "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
          "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3"
        ],
        "T_raw_ordinals": []
      }
    ],
    "all_receiver_cleanup_union_46_marks": [
      "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
      "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
      "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
      "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
      "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
      "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
      "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3"
    ],
    "complete_raw_constructor_cleaners": [
      {
        "line": 126,
        "row_sha256": "77dcf0ae2336c3da0ca20495b045e10d36b66642b6fc408496778739ecbc0943",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 0,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 117,
            "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 127,
        "row_sha256": "9c3730a71a4d690c21cfc9b187981d9a874d3739895ff69e7774694b935aa897",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 1,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 128,
        "row_sha256": "3d818bdbf49cf06516c4c1497aa5d1e5673336e9d6ed7b9e31d0f95aa7c94ec7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 2,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 129,
        "row_sha256": "a16d1b98423a27d9cd32fb24ff326ff315cb5cddd4e413f32edc2e2db77fe05e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 3,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 130,
        "row_sha256": "47cff93d3126729805853ea10f7d70c7575321ebe43ac7696829f59eda8a27d6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 4,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 131,
        "row_sha256": "cf02a599f365668b2694c6a607e85bb1d36eb247158eceefc54521c6a7d98cb9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 5,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 132,
        "row_sha256": "f7de24b21e1978389ca29b5b7b8a08d9f07e7258fdb1bda0cf305d647bcdea11",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 6,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 133,
        "row_sha256": "bcd83cc375f9aa8912d9d9d08d38a4a0a59a27cc04d47818770c49bd4cb7d4d9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 7,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 134,
        "row_sha256": "30a9a7432325190a9919e911efd253bef48e0767bdec4c6b20bc207a6d87e017",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 8,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 135,
        "row_sha256": "7d638bc57ba24aba58f0c256c178bbe4355a62a0a886c004fa4fa6c9053531a7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 9,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 136,
        "row_sha256": "975394f188b62a403379e7084472cba492f99b315c19a4c8883c4cd1b3c2ee82",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 10,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 48,
            "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 137,
        "row_sha256": "2756b88cd6a44eb6c933c43f23d13f0b1383c23bef191d4e9b81e0a356a23e82",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 11,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 138,
        "row_sha256": "5fd9aea73ac364c6cd11c391150e5f0d25aca355545c9eba94a4a80bbca75a4b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 12,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 15,
            "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 139,
        "row_sha256": "49081bd7d25efe8a80a6bade63f27c0c7d7502144e09bc706a1caecd57b42fff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 13,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 140,
        "row_sha256": "ad4a7fded18bfeea452f5670a3cd1b4ca193a02315189f6e5c09079ee5249e8f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 14,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 141,
        "row_sha256": "85a7b1b72e946feb922d99c08234a80c329bd119592767b57aae4bdaf7129ddc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 15,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 142,
        "row_sha256": "229c9be8f346d8ea42a8c50785f93984fcb4b7a540f5c422a5d10fe1040629a7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 16,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 143,
        "row_sha256": "4e3f12bde2f4f34b4a64ba461a7069334152d77580e75cbc6e12526ffcc21042",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 17,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 144,
        "row_sha256": "efe119045afe2f24c91b7426518e6f534f62a6ffe11b689cb9ca85d6ce9cfc05",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 18,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 145,
        "row_sha256": "b7029251ecfff28853793dff33ca3a66088db034c21c06fd01a548e7d2db4b21",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 19,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 146,
        "row_sha256": "48626277fc9026af4bd38c03bf21124d5778a1d30104a267738c5ceddfbc5f80",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 20,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 147,
        "row_sha256": "98cd11c32847d18350f392fc033b6f5f91cab5434c8d0ff7cf2c7c1fc4bc9a85",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 21,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 148,
        "row_sha256": "a0c33f3d034972f5e44f692e882d486f411904dada4aefabc1982101bab28559",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 22,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 100,
            "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 149,
        "row_sha256": "2081a088406d30d6e5e2afe8685c059a3ab2e8b2edadff59ac7873fc6a77f319",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 23,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 150,
        "row_sha256": "b5c92536229ea534729cf57a3ad7f1fc734db324d17e650f8b45e1ac3bb2ea47",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 24,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 151,
        "row_sha256": "f467da6fd5fe057f9f1f353d72d89786368ef5db813e364c0531c9d1d35082ed",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 25,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 152,
        "row_sha256": "cabb6ed7d3596d6c99002b0c85bc99fabdc4b6f0e503001f723404f1dc8e7406",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 26,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 153,
        "row_sha256": "a0ad93b49386a20f44832ffafb5aad2b47480c717c3d443e1452552fb3ce9f53",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 27,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 154,
        "row_sha256": "89ed5ded12ca5b73ad0ae40d0307dc53bc7eca5e987becd025afd5c59e059f51",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 28,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 155,
        "row_sha256": "f7c53baeaf1062c83de41876ea51e85a33c3f0496d5478e0d4c784056d03378d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 29,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 156,
        "row_sha256": "645a5ef22bbc366280809fedb5f607d62cced8be937d98ebc2d96779bd98477e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 30,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 157,
        "row_sha256": "8c1c4bf80360d68562dbd7bcef03129aaba961ecc800c8027f5090a6847b3230",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 31,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 158,
        "row_sha256": "a7dd44a1026a21e086bec3f6671a75b78fe4e607753a969239294b76db4f77f6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 32,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 159,
        "row_sha256": "b73e17cd24c3686c1930f97ddea2b0333e1d313f9a6ff2fed2cdbeb9685b3520",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 33,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 120,
            "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 160,
        "row_sha256": "e4e7b772258133763444c91bd657afacc42850e127eb88440215254fc8511e5b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 34,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 116,
            "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 161,
        "row_sha256": "1a523a78cad53a3d7df0baa46c5b00a640853e2c7a96e44c9510603e229ab21c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 35,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 162,
        "row_sha256": "51f2d7f9f36f1987d10ddf0b6fa7c349bcee18bf37598ad0a0f4864eaa716b32",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 36,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 74,
            "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 163,
        "row_sha256": "e931da61e852d5446acb250c5bbbd2f6167cf3ebb34074cbe0e6a43d9fb941a1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 37,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 164,
        "row_sha256": "16747a9d2dbfd9d6d3779d6ed228dc50116beb77b1b6082d69348d978dab3c8b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 38,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 165,
        "row_sha256": "e54c08fcd99d0defeec48ca8671bfd79a38b7161f400816578672579976c94de",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 39,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 166,
        "row_sha256": "93e00c596ed1bf16f70c8b9bb55e1dd9f90b5dc02dccfa14d32073377663792b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 40,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 167,
        "row_sha256": "4642c83b0afc810d05c39ecc70bf4660b4cf6673254b8be0a503c02b64bcd8b6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 41,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 168,
        "row_sha256": "88802ce4588e2ce951212b520141478b1a1088c5ae7276825722a464243c66bc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 42,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 169,
        "row_sha256": "f65141325c3df8c740ded765beb0fec47a4147dac35bf5e61228e2a8868f7815",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 43,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 170,
        "row_sha256": "2637838f58ebca0335f268480016cfb381602be229c030cb88be6ff424ed1f74",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 44,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 171,
        "row_sha256": "b57cfc3e4ec75d1b38c5f7be3adcfa313a1dea7a27867f60b847969d177ac9c6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 45,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 172,
        "row_sha256": "2b2ad9af333a2b0ea0e77ca66087f9aebe7db11efebee3eeb4bc539056577896",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 46,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 8,
            "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 173,
        "row_sha256": "7b5224e43bdf2601c629404c74875c277cf4470f3186131a4b9299410dfc8d16",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 47,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 174,
        "row_sha256": "f444bec4ea2c22895c5eff00351ff9d365acb96deb5378e9d2a45e04923cee34",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 48,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 175,
        "row_sha256": "1cf92ef87850027e0286f127bcdab3e1f31627fcfb8a809d86ed7d7e81075f0e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 49,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 176,
        "row_sha256": "e853d554aba9bd3e028930d107e30b6405fde9a925807ed8b8b4a6f4de87e7ad",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 50,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 177,
        "row_sha256": "d13100dfdea0f093ba8ccc51e28c9fb9135147d6396f7791c7505dc2c403043e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 51,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 178,
        "row_sha256": "8beb06d4dedd67d8d42dc62097f58d5018ae0f13641aea2ff201cf2480d94066",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 52,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 179,
        "row_sha256": "5deafaf8573e8ea6e6bc5d9ae6504e7c7d39227df7ac583ddefa5cf8418a51ef",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 53,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 180,
        "row_sha256": "274131f4d780abcd82a5ea284058216aced7421fab3e83c67bc2e0209acb5a44",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 54,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 181,
        "row_sha256": "dd3dba4f70f5aaa8cf3ef1542c5e91715a99cc82a3601de562dae93cc4d1b05a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 55,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 182,
        "row_sha256": "666b5bb4777ea1b48517e8a3cdf17009196259ee473138731a16efd40ac4de52",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 56,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 95,
            "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 183,
        "row_sha256": "e5b717f76048240f45df5de13ef991d09e0f8a27f2dc30e0c6abc8d3b3329441",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 57,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 184,
        "row_sha256": "f6289cc0e45123ef63c2daa112a0aba5e3d5d27ca89007c8a65987b22c25371c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 58,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 37,
            "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 185,
        "row_sha256": "c2e8718390b4e517ca1287c2b195d3b8f0f6e5ea10de13ba2feef0dac56b2d00",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 59,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 186,
        "row_sha256": "05dd7165058347cdf29a26055936dc29b931284834adce03de892f0f36a86cb5",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 60,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 187,
        "row_sha256": "4b4562decc4edb657fa067fdce50f0e222d7dd6415db9cf5240d2fae91b07b5f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 61,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 188,
        "row_sha256": "b7627da20178d6e32daa26601e6b11854bb2c195afba6e1b36ea3e04d339e79e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 62,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 189,
        "row_sha256": "88f319fb8196850a44c137b75e6cfa1e5f036cd88fb18a8b7e869054ada0aa20",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 63,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 190,
        "row_sha256": "3c7610ab4e8e81257cb7638b839f4f2ee02ed8834884b5433c5113573863ecac",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 64,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 191,
        "row_sha256": "5ab190ed5f90f1ada4c3c3ac82b6dafb6b4f7d4c7cfc787d54da6e0d363962ad",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 65,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 192,
        "row_sha256": "6de3a0c00dfc5e17b19a88a57c74fc7b2af96392bfb3b5a399f405120a9d3e34",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 66,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 193,
        "row_sha256": "0c16e7db79616675f586ef43610e26ec99d5291746f50d0f710394eb069804f1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 67,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 194,
        "row_sha256": "2a29c90df6bc8d638412eac85766bd5fcf4427138b57eac9fd0d86b71a641a87",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 68,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 31,
            "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 195,
        "row_sha256": "8b0859ec1acd4dee284c05eab143e094abc2165102831173d0f41ea7cb539e00",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 69,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 196,
        "row_sha256": "86b76abf42d82ade9d9f0560db326cdd85b334a682173c3f80abd713e32e9661",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 70,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 29,
            "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 197,
        "row_sha256": "56339919ae456b24de519d83c6bfb96de289757191caa10ed81818cd20d5ee1e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 71,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 198,
        "row_sha256": "6aea6a1feb0a5172e532d53555d1bd8e862bdbd5c504e3dd38727e2fc80b782a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 72,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 90,
            "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 199,
        "row_sha256": "3a62d883f43a6ab23f5c9792fecfd8e662e5890d220135355795ec4c406ebb69",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 73,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 200,
        "row_sha256": "2bb7e79a1bdfe62af34529a3574fc45699a30e7932482380a63bda26e8ddfcca",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 74,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 113,
            "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 201,
        "row_sha256": "2809dbfa2c9539dc0d3035e5648254d4b9e9d1244b514d5ec60aaa20fd4a00fc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 75,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 202,
        "row_sha256": "5784e52413756355128b6d221e26d8f3946147886b2b0aba1aa7b862c5041f35",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 76,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 203,
        "row_sha256": "b1c7a5354feef858a00ddd87a13ce4e77a15503ec1d4d7e741a85878f0906582",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 77,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 16,
            "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 204,
        "row_sha256": "83859549dbce77394391d2cb051ef95452aae5335cb525932a2c26abe873ac68",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 78,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 205,
        "row_sha256": "0c090d89633ecbf02ca73a9947f2294729d6590ee0fac7eeb9607a0591b26cbe",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 79,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 206,
        "row_sha256": "7a2b8a762fcca793fe68325d22ef91bfad4ee33856375862e61629d9ee73ab00",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 80,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 207,
        "row_sha256": "315f11284fe18b2cf3f46d79a7f9d88c71f675ab8de53ec937a099d110b8ce3d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 81,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 208,
        "row_sha256": "bb166677b4e56ffed4697e78dcc474685c10c24f1fd4e05ba26034416d5487bb",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 82,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 209,
        "row_sha256": "bd355570246aa9ffaaa65bbfe9f6c73a7ec84bc885466839ddb50ced38322b0f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 83,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 210,
        "row_sha256": "714d87273d1745903e9997e5edf41f80603c2b1af1e5cb2daadc3c6325c9efff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 84,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 211,
        "row_sha256": "5bcb751bcb7d5be8f59e4d80ecc07b6c488fea01f00863c5fc0a04d15faf5688",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 85,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 212,
        "row_sha256": "77155361e1317bccf0298f191ca6dc4e483edd624b9a6b86d3561a5f16174683",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 86,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 213,
        "row_sha256": "c84672c14b77ead458c8753d591f052c53d10e36842132a4cea588e3556074a7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 87,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 214,
        "row_sha256": "05413f641fa9b0c96ad9db3e849d80b01b2c8ddd9c2d5b4edfd451ebacd8abce",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 88,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 215,
        "row_sha256": "283f2222bcac998428a900aee808f76849047118473005a6b5c3835ef6e08f14",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 89,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 216,
        "row_sha256": "4aef6399b19bfc523be1f0c77f95aefa9649be4010654efb7579d2d7582617d6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 90,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 217,
        "row_sha256": "69395f6727441a8378c2c1224e7f784ce96bce604b90af9372cb498b79a250c6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 91,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 218,
        "row_sha256": "a2b64bbbfb630b5cc55f1ff71b4357e7f4584be099894ce2175507daeaee8db7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 92,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 219,
        "row_sha256": "f8f6d118c2f7035076d101d652a0ea303cea93130b43c878bcef8943478cbf75",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 93,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 220,
        "row_sha256": "01fbebff7840fb30134cbf2edb7ed1cbfb3e30841a6e06f9ab747d45760efc84",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 94,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 6,
            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 221,
        "row_sha256": "e5d18dac5abf02a1ab12d64e3254f9728d5bec40c1221e3aaa1b844ea210cefa",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 95,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 222,
        "row_sha256": "574373279deeec13b340c510cbc81f55103ff7dfd53b8d7a7f9bb1fc533848f9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 96,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 106,
            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 223,
        "row_sha256": "17463f263082656f0f5b4e767cd76c8b4f6c0c3857a893b5e85d5b2cf3e8102e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 97,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 224,
        "row_sha256": "dbf2128fee7b3adcb6dba866be7845288a915e31dd9cd923a5b0b558e6e9fcc3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 98,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 103,
            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 225,
        "row_sha256": "8c26e6c8dab6debbdbd52ca97e180885a5e4af17e99da0c8f2f11e3969bc61a3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 99,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 226,
        "row_sha256": "819d4228863e6697bb6a0a20472c152274d3da261fa0dd80cab94fc0f26797d3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 100,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 227,
        "row_sha256": "bf0a63ce22725ca69431e1c2366f3dac2575064026b6ffc1d1849eb923e720d7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 101,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 228,
        "row_sha256": "72d548758e656701652f8bb228072ad2389e433fa92425c1e65e940004f96eae",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 102,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 229,
        "row_sha256": "709eba98bdfe42a845651a4f8337a119b2c48c9bea84dd5afee7525d0deb03c7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 103,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 230,
        "row_sha256": "f2569eedc82b220cbfeb0b9136ce64012787eb0ae8068ab828375aaac2bf7383",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 104,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 231,
        "row_sha256": "a85e4e3067f8e882c77ff19adfc52e7511cd7ea6e421848437bf5d5d63239629",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 105,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 232,
        "row_sha256": "23862081d01dcc7ace7f4856b9298163b540e3fb1bde4cd6b7756241457d754d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 106,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 233,
        "row_sha256": "aa1e201abedc5490e67880a9e0f45400f8f559c40be55fe713c92448559ef785",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 107,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 234,
        "row_sha256": "96461a459c80264b5673c0dd4c8dfdc8a8ce67f1316b43446d0c0675a4ec9ab1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 108,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 235,
        "row_sha256": "64db27bccb983a77b9a33881a6601ce952a4479c1a0583366bb6167df0da025d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 109,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 236,
        "row_sha256": "5d634aac3e60e0b2f593ddd5f4a6bb89e88f968e6c77e872cc059db76c88868e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 110,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 237,
        "row_sha256": "b0d9bc27c143060f56ed31ffdcda3f2ac604f579104b80b74e356f03187ddf36",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 111,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 238,
        "row_sha256": "ef90c85c55d0e106a4b49f2ba2f8fd842328d5660e528486f32e03d984faed6d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 112,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 239,
        "row_sha256": "b9153e3c5f2468c299875e5fee2b7705f10f41c567b54ff55c96e65740e67d76",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 113,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 240,
        "row_sha256": "8a74fd66b7724302c438ffbe3a8c0c89d51412be01d3910a40f07e649c9b6cff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 114,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 241,
        "row_sha256": "fa4b30d72f70b78bd43fbfc485ce3a48bd1899de7f3271c99d2e141abb77032d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 115,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 242,
        "row_sha256": "3c95abfec2f926f3af12d4154f84174cf9671400285261d3ca3519080ed59861",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 116,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 243,
        "row_sha256": "601552399279afc9875e07a28fadd8742d2dab1e0517bae84b78e480c6371695",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 117,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 244,
        "row_sha256": "ecd3634fe9ac7bd7637189642bee07f1ce732c537ea4ec9c22b268e31159be30",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 118,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 245,
        "row_sha256": "c62196d44741b0d125a5e9c97e897fe277269d297b33bd47089f7a0fb5906ca2",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 119,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 246,
        "row_sha256": "f9ca42ab7d77eaad2c2698a50edad8753004a2250c21878721b95219909b2f0c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 120,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 247,
        "row_sha256": "afc5ed2bc841e708da857e8d8f2268d0d68a301f80c8f1a499147a47c2cf90f1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 121,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 248,
        "row_sha256": "1ab2dfe915a1d70de52fab96460fed45b726822cb0924caa462842e6a8396e3b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 122,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 249,
        "row_sha256": "8f485bc867696fde836e26893d951db1db9bba1e5577be3184f3b5b414954d8e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 123,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 250,
        "row_sha256": "70d07d8032a66efaf1acb7d9b061d3b3a87d1e4e44f167743754c0d78fb30c78",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 124,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 251,
        "row_sha256": "66f863c77f76f15daba8274ecbadc856e33f97d086c04248d18539bb1bd297cc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 125,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 252,
        "row_sha256": "96c95ee2d53b643efa39730af3340abc948aba7cb9635f39eb369a49201489b2",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 126,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 253,
        "row_sha256": "43f182ae3efe79c279393811b67e0ce5ed4fbab6f0fc797ffad3bd87f3cad96f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 127,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 254,
        "row_sha256": "89dddb30f6141628485223c73c445fb9e12da447d5de18c2e526f2e2c1157021",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 128,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 255,
        "row_sha256": "38139ced25e437eb77512fabae57ee9fa3dad9c6fd40423f0cc509b38a0c0f08",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 129,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 256,
        "row_sha256": "4415782935cada011afa6b750178fd71ad60a6aae513773be3b85ab31207913b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 130,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 257,
        "row_sha256": "38d3d4281c1b61c372e4d86719ef6ea11ccc65e500dff64810240d78752abf61",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 131,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 258,
        "row_sha256": "c7ac9aa2557e69127af2c54a3a55df88fb3c486cee730cc63e477b5e07552284",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 132,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 95,
            "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 259,
        "row_sha256": "5a9bd53d8424b374e77c394e4a9ba82dd3f960226add4cf9f1568baf5f297f2d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 133,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 260,
        "row_sha256": "cc0e56ae3ec5cbf03381ae2e85d22337927795b61a8caa6aefa30558f8aea3d1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 134,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 90,
            "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 261,
        "row_sha256": "b3ceab736b1f2462c218a857ad7900772b82ac17e7751356987e12a680bc5941",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 135,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 262,
        "row_sha256": "265c7c9d9397df38e8aea2be3bfd692858f5b0fea1ff3043212792851764515e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 136,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 116,
            "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 263,
        "row_sha256": "58545a0cf797626746e1c38378e3453f8405d2b9c890b115568796040a8cd047",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 137,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 264,
        "row_sha256": "6deb6df7cbccaf141bd0ea617f785be4538670a8a23dd56f5335bb267a82f79e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 138,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 8,
            "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 265,
        "row_sha256": "4c812baeda2c60c5f1a10f8d7d2b2be540dfdfbd33c62d6a8fa6a8ede5daf043",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 139,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 266,
        "row_sha256": "97cb992c5f57f944e3affeb8be01465b47ce9bf934fc47088822258b0b84f644",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 140,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 113,
            "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 267,
        "row_sha256": "7353c72b168fc26e8e27acb85b2883053389461408b1292dbb74d38d705af15d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 141,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 268,
        "row_sha256": "d9f02df95e3436c4f43fc8fb11fd27b0683a8613b68ed20c4d22972458610eb7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 142,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 6,
            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 269,
        "row_sha256": "1e8e8b1cfc6cfe57a8414e49b018ef2861162421c5e01b847895c6fe4dd72f14",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 143,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 270,
        "row_sha256": "8d63372851ead5f8b6d555a267ea8c55e9f9090aa0bcb98cfa4f5999a86acd28",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 144,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 271,
        "row_sha256": "710761482c57cdb1e79b748679aa6f8518b2cd2c7caabe6a415a882211a62946",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 145,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 16,
            "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 272,
        "row_sha256": "2917aca2fc201580b68d92c51b749aef9bcc962dfd8f7b86fbd7874cb8814bf4",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 146,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 273,
        "row_sha256": "832eab881a23071e1f5164840e50d98226278f41d8a5573de40ae3164c22019f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 147,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 274,
        "row_sha256": "ef52cbc6cae2632ac38c8a3fbc45252e957b62c216454e0d281667e34ddc74dc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 148,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 275,
        "row_sha256": "92cb74fe0eeb412010f1f35e1720b9d0b78ea4a31b273684e78383dbb1eb1c2f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 149,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 276,
        "row_sha256": "15408d91367feffc347c00bec9449b5e9b86b84ad22e3c1569ec144f89526f12",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 150,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 277,
        "row_sha256": "6c319b58df0fcc5189e74a18b034ad98e41dd5dc04f95ccc47323c481a00e700",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 151,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 278,
        "row_sha256": "ca4059898bceb81c81aae6a9cc968d72cc28d98f7a6a24a0dc2cedfba6935bb1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 152,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 279,
        "row_sha256": "6ce4ca652b651da2cd98390f051c910f922eb8bd65040504f1bb4c741df348c6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 153,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 280,
        "row_sha256": "c0cc01875846d41479352c2e0d9fb8bb242035501fbdf3216b7dc49407d7302a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 154,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 15,
            "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 281,
        "row_sha256": "e237a8a556612b7eac183173caf2161efad4ce13c5e2ee44c85909a191291c21",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 155,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 282,
        "row_sha256": "fb8c154824061c8daea472ae5d6b12cdca3257f86383fcfaaf57b96c0f497ec9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 156,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 29,
            "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 283,
        "row_sha256": "da55e552f116a9484579986bfda416249e7a3ccc3db236fe7cd9ec966cec46be",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 157,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 284,
        "row_sha256": "9f3d29345b455caad313d01f8aa988faec7d6607fb14b9aa81aa66cfc456fc7b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 158,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 285,
        "row_sha256": "9c7db744bc8685f4a37c78222a9307b36d5d4ec04dcc73765e2202933ae17c73",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 159,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 286,
        "row_sha256": "50b6d9ecd374bb702cec3f534ea269a2a0c6a028f7d05a8c4aa1b7849a8f477a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 160,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 287,
        "row_sha256": "c6c18e1710bb70a59ff3af3daa4b9a264cdcbf6b72009bb821aced79030661c9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 161,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 288,
        "row_sha256": "b2688f1f24a99f78b1945f90397542dfacc07dba416792eab6e9306ce8356585",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 162,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 289,
        "row_sha256": "33875b9f2da0087f46a20083999c75f58409e55add9ac8b7cc57f59059618605",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 163,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 290,
        "row_sha256": "1a9849cf88525a7e648026563686c0320c908cb9649de7979fe98f53db130e28",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 164,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 291,
        "row_sha256": "48f0e0ca755ae8e62eff7bee791cf965dbada2c9614e1564efb3407f69316688",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 165,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 292,
        "row_sha256": "67e2400f36d8b6bf8460e75d4c5f1465f9c86ee6e6238dbe291fb84c60fec96b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 166,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 293,
        "row_sha256": "b429fcf4e1e176b6fb5478d532d5973778f3d606a1c04d0aaae7128c93100213",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 167,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 294,
        "row_sha256": "6a534d24f293bd54d193232466b75182e2d67dceef02d73cf4fe1e94ba4c0410",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 168,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 295,
        "row_sha256": "f9c4ae668c10987d524f6d804debbc3cad0d8c6e3deeffb342263b422ba9ecc3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 169,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 296,
        "row_sha256": "8a8af78d0ff3c81be961a4b2aaac771cf87cb5bc434080280e8490ae08f6daff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 170,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 297,
        "row_sha256": "2c8861374b422a09388ebe5306e132148877c6d1783725d5d60131918bf8fc8b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 171,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 298,
        "row_sha256": "75fe52128312f8f67ee5c3ed7d67dc7a7fcfccc45f4f26511589810af1a2ac3b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 172,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 299,
        "row_sha256": "d8204bdb0274acd580094426c9ed386588d22bdf69df16ba79f8b46f5d309293",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 173,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 300,
        "row_sha256": "6e91736e02e324ea5a2077b3105947d21dcc44db097e11b7d91354714878d143",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 174,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 301,
        "row_sha256": "3617ce7dc1a1ff65021a81e5987c814cc38e56a38b8512c5c1b59e6244f4a062",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 175,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 120,
            "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 302,
        "row_sha256": "75846006ba2454ca6ece598763f951c4a3cca09134501229cf4ad603f9951d6f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 176,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 117,
            "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 303,
        "row_sha256": "cbbf7a8faf410af876a6f4ec12270531385ac6fefe5ae5f070e4f7f588b1d3a9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 177,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 304,
        "row_sha256": "20c142d4c8fba1bc2f1fb5a30d3ad265a19e44273d2bd2a20e3a6fac7c003fc1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 178,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 48,
            "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 305,
        "row_sha256": "9304ae70d9c94843a2bce3cd87797bae0085f5c75a42e566afbb0207b5a01297",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 179,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 306,
        "row_sha256": "2b19c738ea3cf30dce499c079d7b8ccba08cc51ed9b291b441ee9732bbc765e2",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 180,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 307,
        "row_sha256": "7107ef7e3c82912d2d1832f8dbf96e5fce61c61dcea9c62d2b24dc26867aa4d3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 181,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 308,
        "row_sha256": "22f9dcca6efbf101b6a5508d9978585cf403218190fe80bfe903ae70cbeeb3ee",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 182,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 309,
        "row_sha256": "4a0ff36e52b439582c203a0d9704258e2e1fbfc3d988b282b5493959c1d24019",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 183,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 310,
        "row_sha256": "4378d741dc7bb9791cdc993a0568f4cf646c54c5eb58ae252453d8ebc87839ba",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 184,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 311,
        "row_sha256": "ed08d34b866babbeea1fcf2cda49d91b96203cb80099ab52fa00311483b8db80",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 185,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 312,
        "row_sha256": "48c55c32062754d9bafa674c71364074c7abe806b3e763bdea0142fea0d0b483",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 186,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 313,
        "row_sha256": "2a781f5aa37fa3cd76f211b357d04bf24e91fe220635cb29ebd6eb3a14051d1c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 187,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 314,
        "row_sha256": "85760cf78edb4c6af1968767a21532ca36b64ea4fd8337c61484db9b4962054e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 188,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 31,
            "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 315,
        "row_sha256": "9e4a5af839b788e18fe0d52abd15c65ae84fb5f0ff976d7bb4fd5b71e214cd14",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 189,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 316,
        "row_sha256": "fa696f16910520bda3b67cb4072a351633c16833b4eb6a5525cb3d2542c57b0b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 190,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 100,
            "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 317,
        "row_sha256": "997df605a106795f9047958d54e340d9575e4370e7f525bae8d63b14d01c8018",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 191,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 318,
        "row_sha256": "606f3292fb41b3923381e3cfa1722a113837e17a51c3453b6f15543baf84e8bd",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 192,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 103,
            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 319,
        "row_sha256": "535aef5600414c44622c130870b8ceef5f2cc96eb5c7df3da9153be516891d09",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 193,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 320,
        "row_sha256": "8859601e110d504e06f6cabb0d0733bb13f141e2d3449b26dae109097bbf1388",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 194,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 74,
            "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 321,
        "row_sha256": "6d78d2649c1a140b30063a3be595780ca952d61a7e65b8b60552387bee1538dd",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 195,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 322,
        "row_sha256": "c984369fc6041780e9acd855c2bb04179954049dc226a8ff65a93a63277796b1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 196,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 106,
            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 323,
        "row_sha256": "2613cf1f5b86fe93acbd93e21d70c9dfb30688cd07f4ed89f2b24b0c701bdcb0",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 197,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 324,
        "row_sha256": "e96227e7700d4b9044acd3a64dd0d636297a166354d1d63d596c683c1dd193c6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 198,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 325,
        "row_sha256": "0e9487c429eb52e9b7d2a0284afb14b3cee9f0203a3edb16ee16ff8306d72a30",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 199,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 326,
        "row_sha256": "24e8848e9205a2237eb4755d9789d694afd4703b4dd96a903aa7d333e26b5c43",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 200,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 327,
        "row_sha256": "7f6d7fe7d12fb5fa451ba0b5af6a2753de64819a6cbb69eb4af34e3eaf7bd56f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 201,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 328,
        "row_sha256": "5988672c4895906074f04edded292291134390e6f42d56e393f6b4887c22f2a7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 202,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 329,
        "row_sha256": "e7255be0e65663b1e8b2f24d76d1f50db2ea7b530aa50b4672069e7348aed6e7",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 203,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 330,
        "row_sha256": "17b954beed41a0c1f4402330c44e28d481d3903fa7f203f3f390c03700bb365e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 204,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 331,
        "row_sha256": "19bb2861ed823cbc26fba0f6434cf74188d0ee6e6e38146cfdd9b0d49adf54bd",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 205,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 332,
        "row_sha256": "678e11f3673395cbeebf709f27e9fac3b42d82fdc18dd1dcc0b8c1895e856fd9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 206,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 37,
            "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 333,
        "row_sha256": "08427fc71ab297e1209a06c51d905da6dce74bbac7bbe5b2cd0121b867375307",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 207,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 334,
        "row_sha256": "a81f889687a65e8ec8f646b08657ab1fd5042e284158e4d1d0d43a11d63d6be1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 208,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 335,
        "row_sha256": "1d251aea6d5af8bbcc4c21c6492af5c804f75aee01857222b2eff32cf5636b17",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 209,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 336,
        "row_sha256": "9523b20224ecc2e40a1c3c5d96d23ea9b1ba710582e0dc4a5cc26554b062ad83",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 210,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 337,
        "row_sha256": "4c5e8acc8bc464c9ecf295211a6b04f81663ae064333ad10723a49f48f407004",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 211,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 338,
        "row_sha256": "ba276c15629000d96828eb7c58b8c1b17f29d3222bfd4767d0c6348cb2758826",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 212,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 339,
        "row_sha256": "eb7996ed3a68ceeca09efe258f9d37dc6683126d44f7a36b815982ff62052112",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 213,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 340,
        "row_sha256": "ef85506869d24d14af1b6d981eb55502de810b8b4e247965a98433c03bf432d5",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 214,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 341,
        "row_sha256": "c88ab48a96eb68556750faaa82c3ab3ce4118e0360287f6278e1c41a9162a3a0",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 215,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 342,
        "row_sha256": "2115b3abdd01fbf47ebe8b1c2e90a15ebca889a14716a9aeb7eeb58fa5c5eba0",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 216,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 343,
        "row_sha256": "d3002b7f2137a86bb9cbbb6e6b753705317cc71f6bb37ead9ea5e353285c11f9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 217,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 344,
        "row_sha256": "a3a9acae4f770f46777b9605ba7b0bc6afe3de42cec6422412b35d848cf6ab43",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 218,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 345,
        "row_sha256": "7e00d1697e111d51c63cb4f382d4a9b3789478d23ead929373af698ac7afae77",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 219,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 346,
        "row_sha256": "f93bd72d04db4d986177917323a0df4b8c3abb05b8bd1ac048505adc9563bdff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 220,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 199,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 347,
        "row_sha256": "6d249fb0d45df2edb4d23d5b4f3c81767869ddf336ea58ff1108e59266f6ff74",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 221,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 200,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 348,
        "row_sha256": "dc942d3e5a4d0d219e2cabd2cd26824d71c158d86794de5fdc4dc62526a2860e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 222,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 7,
            "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 349,
        "row_sha256": "aa0610edc7efc117472f6f4846fe203cc6142368d94311aaf6544f322cfee58a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 223,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 350,
        "row_sha256": "8e180f42832acb76bbe2e57bb1626faf1ee19a23d3ff3e6af25b6afa34a6491f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 224,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 351,
        "row_sha256": "f31173cee7fd41502488e9fc16818ea32f04a8213c97bfe776afb4fcd2cba7a5",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 225,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 352,
        "row_sha256": "92fced7bbf41569b98d22c367f7ea746af77de194683bd2bfc39023177c73726",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 226,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 353,
        "row_sha256": "9f781fc30b73af3268432b77d20ceb0605d27ea3965dc7ef5a46393815b3abfe",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 227,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 354,
        "row_sha256": "cdb2bc7c3bed45ed34e5f041f1a285fc31ac5338ba261879686773d0765b31ff",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 228,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 115,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 355,
        "row_sha256": "bf08f8ee5cea2fdd4bd9d1afc94d321abbaa2861b196d7ae8bbca654883c6a24",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 229,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 185,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 356,
        "row_sha256": "696e17ecf7349dfb584c9dd7393b53226699404b44bf4d68fe5b6df8b05dcf25",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 230,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 186,
            "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 357,
        "row_sha256": "7bf6e8e27f01fb6786a57e80bb4e9b4256ac1fcf7bcd9a3cb9b299d365d562af",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 231,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 358,
        "row_sha256": "cdea8dc95ad2bcfa303f3d3208e10fbd75249b71629c838d8b0f705e54bfe870",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 232,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 359,
        "row_sha256": "28d575fac6bcca49550d690cbc02bc4c8c08239d4cdd1fc946cd1f5a7dc402b6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 233,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 360,
        "row_sha256": "e5f66b0514efc10b938d859746f7eb72f6601ac374d6a2daf868ff67928ebaeb",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 234,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 361,
        "row_sha256": "f5119acfb27a1c0e46f8d33ac38e881f1684175c070d0b59e95807aadd36163c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 235,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 362,
        "row_sha256": "53e3dbd7568debc2f5d1ed7b73c072373a387e16dd8e88981dfd8902216b0411",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 236,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 194,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 363,
        "row_sha256": "6b34da3241912f7a6161443115346e0f0c38adff29085178a0681c2acb3a4e8c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 237,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 195,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 364,
        "row_sha256": "904e693f5147a3175578c79a10bafb4e2660d603f92caaeabe66c430d1cb64e9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 238,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 108,
            "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 365,
        "row_sha256": "d5cc51c8afb4186518915d0a47a4053d4ff3077f7c8179506bb76a3fe9df250f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 239,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 366,
        "row_sha256": "810a4a6a6d5832878d45331383e101e36f17be16e3c4b0452c0cd14f05413439",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 240,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 95,
            "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 367,
        "row_sha256": "e3795ffa38f3e1dfac575996ca799de6340572a95ee8474ec621d316dc683d73",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 241,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 368,
        "row_sha256": "cf4bef00cd866d5a88381ed51c639ac386d7086c9dd27e6c46c7bd6edfc1be77",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 242,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 116,
            "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 369,
        "row_sha256": "77e4ca701e1e4aefaae25cd32c1b42f06c7955ab09f085ea3738c62691c7c41f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 243,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 370,
        "row_sha256": "25dc79c97f25841c37454dc46a877766ac101743898c4aed6b27fead9a65b1ec",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 244,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 113,
            "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 371,
        "row_sha256": "16ed324e58ae56daa7a2e728ead8f38f6161c8287dc1367df16b5bd70be20feb",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 245,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 372,
        "row_sha256": "ef9a045c233622982ab87020edcbd73edcb30d8595717daa4845d500057ffa24",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 246,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 373,
        "row_sha256": "7243081301a0686c7c5dd0a33590fbf4ea7138e68f383383c930c051729328b6",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 247,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 16,
            "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 374,
        "row_sha256": "35d8e67d07be6f3145a17acfe734bec6e7391b9dc28fe57d2d5ffc5ee84f8907",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 248,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 375,
        "row_sha256": "1f18d3890282725eacae4c69cab5c2a65498e1bac218d45dc4b8a50363b129c3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 249,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 376,
        "row_sha256": "6ac96645aa1c4cfd534cece31aa5c392b6b621a0b6c7b4a513bef97514fb2009",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 250,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 377,
        "row_sha256": "3754cb26f5f42c024b3fa613745f48fc4014d1c1fec30657d04e28af102ba914",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 251,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 378,
        "row_sha256": "f8dadd22a218979437dccbd9538e4756cd71b21f449d63166f6227cf7a9a1541",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 252,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 167,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 379,
        "row_sha256": "dafdc0d7b1c3363fd7cb524b43a743ba5b8b50ec823d4d979d658e82679c0e2b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 253,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 166,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 380,
        "row_sha256": "0d3150ee547730d3c91b14a82cae474821d63aa1e23916cd619db2a991f2d068",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 254,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 17,
            "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 381,
        "row_sha256": "dcaf7117bdb854dc9ebddb65ef7e805fada7b9372e6097ef5fcfd68e0644ccae",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 255,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 382,
        "row_sha256": "6bb29f35bdb8c59f53bfbb380a80d3c8929e5100ca641dddbcc4d78d657f1b9e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 256,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 15,
            "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 383,
        "row_sha256": "4750e5985e2d619753d93822dde323245f25cf1ffe2f765ef3c2de35af1f357b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 257,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 384,
        "row_sha256": "83453b4b2bf9522d1f52bf0a90e9c8a754929f701cbacdc8d859a88ecea14a76",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 258,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 385,
        "row_sha256": "e5b6d4fc5d55c7217169c647099f92fecf8156c1d76afe42359e3a6a2849dc0e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 259,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 386,
        "row_sha256": "bd9cb7bc4071efd23edfe5766dc0103fde638bf2218e34da72283febeda2fb3c",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 260,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 387,
        "row_sha256": "fd8b5fbed1694c4f7751a96caaf0bf59ac8da3cc2af0bef6bf91b19648d12310",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 261,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 388,
        "row_sha256": "9643e47fdd9b46ef42c5af2cb5595ccff310fdd06252f87ce803d827f3d5dc07",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 262,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 12,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 389,
        "row_sha256": "3f45a98cb96630eae6e5c93014f6fc657f83ed22238a65256ebcd42822ff1636",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 263,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 171,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 390,
        "row_sha256": "20ddff643d44aee68a45c1a99eff5d6fc79b6a42cb0120f53c84a7007b6196a2",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 264,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 170,
            "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 391,
        "row_sha256": "e969e61a9a92e081a6428ce3b10f6a1ad0661418cf278487d3ffbfb4c8b50a57",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 265,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 392,
        "row_sha256": "7eb176c1ecd0c44633e955230920ecbcfbfc3cff7c1edb5d1f57aeab4fd3d0c9",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 266,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 100,
            "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 393,
        "row_sha256": "9a4712ca80bea799e05c51fb60a34544dd3e67c992b5837fc698deee71b10558",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 267,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 394,
        "row_sha256": "1b6abff6314b3055bb415c98198fa7d7ffbeeb6f127717df93b85c8e1d6abddf",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 268,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 103,
            "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 395,
        "row_sha256": "d6ba456e1b197ded2091d840a203ac301b8110ce8c53a0cc05d56eeef35aa691",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 269,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 396,
        "row_sha256": "9a814f0087e64257a14a174bea959f7ed002a960781e352dcf5eac7ec0c00728",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 270,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 397,
        "row_sha256": "0f9b4293f417f5f41ec4dbea23f8ebbf5229af1252f4ea38469effbe03c5cc61",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 271,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 398,
        "row_sha256": "0fd9bcc7de064d804df77fdd734df1a007e45f7681c9a3ac0eb9d47b68ea50b5",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 272,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 399,
        "row_sha256": "db1163f4a42663b8ce2c5ba7d46432137432787125eef00ba52d0c1ccb62b33d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 273,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 400,
        "row_sha256": "a6330d00d58d648f149c12b6d688c6088921ecc58e1f7f5369b4c8a5e9c8bd02",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 274,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 174,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 401,
        "row_sha256": "1fca95c512c45588aa2b67aab194d02a8cfb7d9988264823d53cc43bc213d867",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 275,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 119,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 402,
        "row_sha256": "cdd7d8dfce5a4e6a69feba1bce17178ca481b4c3aa1cd4c08c83a18fc41d9d92",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 276,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 173,
            "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 403,
        "row_sha256": "b6355f8c193658af673c86f2345e22fb6ab565f6e6b8342d51639f773e90bbf3",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 277,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 404,
        "row_sha256": "281e4c15ef77c4d383d901d43b8d261592d9a9daa43e0d7ffe8edc3493261406",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 278,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 37,
            "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 405,
        "row_sha256": "7fe9691002703fc3fb2de020ec491ace556b51f296190574b9820ac2651ec802",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 279,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 406,
        "row_sha256": "6f975b094af5c4b3af6f3b2611989e07120a4eb9339371870695b76915930d64",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 280,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 407,
        "row_sha256": "22e35479665baf46232e5e989feb45cb1ec380ed868bdf5c50cac69831660bd0",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 281,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 408,
        "row_sha256": "7d280ee33e239defa6e36a5e3f79b1a444986ca1d6499f2a190af2370b7ccda1",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 282,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 409,
        "row_sha256": "5009bd6e0880dfac2efdc1d685135aae30568d82e473d8f8915ce6981c4f6e90",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 283,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 410,
        "row_sha256": "da77617baaa778a1ed65bbe223b7a31e7533766561f036ab1760131d6c737e60",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 284,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 80,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 411,
        "row_sha256": "4ab120d8ad7006319f34c423676427dfcd5fdd9d70f67f0827aaba3a11631b1d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 285,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 181,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 412,
        "row_sha256": "3568b16fad540f36590190700c3d01cae8dede6bc0ed693eb534ff05872c75be",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 286,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 413,
        "row_sha256": "a099df6b8ac94df95d15cc9e0b723d104c5b59dc21494c29d563143d7033ea9e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 287,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 182,
            "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 414,
        "row_sha256": "580513fcbbee43ba998a24b7a04d8be5fc5514ccc4bc9f92eb27a6549c336e31",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 288,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 90,
            "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 415,
        "row_sha256": "73e5fbabdf3f057b26f99a4c4a0e249de56edcfa7bf844274ce84aba2e7a8434",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 289,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 416,
        "row_sha256": "aed1eac7b27a46b8919d7b6cb54b21669470afa90c64137e8f00d6a9d31e1345",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 290,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 8,
            "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 417,
        "row_sha256": "92b44d5eb1763440e39f84dc57928fdbcb8f2f972f6217c0598db4040107627e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 291,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 418,
        "row_sha256": "05bb84bc597db01549817127a5363a75d6ef7c86314d985661d47eca3a1f799d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 292,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 6,
            "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 419,
        "row_sha256": "8893c72373566a436ce7167d7cc3638f2edd6911b31b52e90e09a149bcf97229",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 293,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 420,
        "row_sha256": "c1d26bd9b03a69fdf016df1304ac89ff79c18e7203f36d8c9cf952dd39c9239f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 294,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 29,
            "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 421,
        "row_sha256": "b505c74cfdf3666a4e87d69efed03ca8988f7ededd23275660ee84f9c015311a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 295,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 422,
        "row_sha256": "042905c97240f3fc0efa7e982237f19bf09e1efdbfe468e9779b8959a388109b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 296,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 423,
        "row_sha256": "38e780cc43d6e7f11e460a4fb3eb3d128d478db928d4ac18940b78b69d081933",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 297,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 424,
        "row_sha256": "53879af2a1f8467792e442ec8e3fcd96f5bc80166b8a019311febe2c8427a16d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 298,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 425,
        "row_sha256": "8f34b03374cc7610590b20bb2b8eb2766a4f0004b4e5d286538b160ce5b6cc70",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 299,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 426,
        "row_sha256": "0d570219b6951d2615375f2d8e6578b78ab2e77212a77578a508b4b6aba27f1e",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 300,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 193,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 427,
        "row_sha256": "40fb27c08607826993e54e5da48f84fb2c52932c2422d9cd12d9e22b0a7e347b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 301,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 10,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 428,
        "row_sha256": "7a036b1c0e36c22bb922dcd1ef27abcfda58e17e7313a8818aaf11f8f6e78109",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 302,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 429,
        "row_sha256": "99db30f03357b1c335ce8d8388f20713ea0fa3a08a5587eff643b52f20ae1846",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 303,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 192,
            "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 430,
        "row_sha256": "be391dba8ee0bfa7bd38d1320ff578c4a7b0d5d3d88efe417059e47b7645afcc",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 304,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 431,
        "row_sha256": "f00d0587ad042a8243d8f2f332b4a4b23cc3dd51ed4bf27187b6f9550c57a990",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 305,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 432,
        "row_sha256": "b24d33c2d8817c35af9135a7353aeaa4e08454b81114da3ea7a9075abdddcb32",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 306,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 433,
        "row_sha256": "b612ab06d5010a96953fe84bf73d7f92149661fdfe865ca3927650eb50331fee",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 307,
          "base": "arg(1)",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 434,
        "row_sha256": "579543b92cc5f022b5c684c055e0e2d87be86482133a288e0a95b9010d9efcd8",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 308,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 58,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 435,
        "row_sha256": "7b571e0e81c24fcd87e7e3d501220278c5e2d0799420a75c3a734b812ac731fb",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 309,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 436,
        "row_sha256": "c0c31bf15134ca8309a2a4ce62b27b603b4ee3ff4194b6907885c8abaf6fd46d",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 310,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 179,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 437,
        "row_sha256": "2ab86fcdb01fc3cfa2846d5f7b2691ff741722100408a80b2b7de83f66f52290",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 311,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 178,
            "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 438,
        "row_sha256": "d9ff2ac3109e34f92b06e94643ce76e9aa53ad39220d6a38af3af1e6742bc9ab",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 312,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 439,
        "row_sha256": "8a603c0a75dee033bf867be21a8a9f06693905afa74e78340f16cd2010ec3826",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 313,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 120,
            "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 440,
        "row_sha256": "c019d9e90d8c3e9bb3b11d95f038acceeaa0bec3fa6e62a647659f1591d6343f",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 314,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 117,
            "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 441,
        "row_sha256": "91e8c04cab0f4959c87d483462b43bf81d051aad8f1af2c4284a560bafffcfaa",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 315,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 442,
        "row_sha256": "cbf4922c76a100f52bf4ebff116efb381fa84d1f0be79d077cc137f6d11c6c77",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 316,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 48,
            "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 443,
        "row_sha256": "aeddbf661e138bd2ed984c0ce07c74729b41bf1c835590cb49ae34f9e67e1dce",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 317,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 444,
        "row_sha256": "b8613c08bfe2d1420db66cc5a0b032fe813d737b2574e743fb9e25c4bb9b8d8a",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 318,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 31,
            "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 445,
        "row_sha256": "44e2bfed3eb1bead6b4413b17eb8acfb1232fbde7126b63333372d8bcc0d8029",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 319,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 446,
        "row_sha256": "b9720a0295639ff20159d58b730d973ca73a83907ed1d29ce590a152986ba6a4",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 320,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 74,
            "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 447,
        "row_sha256": "c6df54956fe81d37b0edd8db92139b7b0df7d6df5d4c580d3f97fd7dc4dbbd79",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 321,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 448,
        "row_sha256": "bfa5b075ecba8ec44924e4eec9bb8a691005668c892c8339569d4eb77bb84e46",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 322,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 106,
            "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      },
      {
        "line": 449,
        "row_sha256": "c499f60ed001aa8456c1ed7d8650e34883855e967feb56c5f7f469732586f71b",
        "record": {
          "record": "cleaner",
          "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
          "ordinal": 323,
          "base": "<this>",
          "path": null,
          "reach": "EXACT",
          "mark": {
            "id": 146,
            "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
            "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
          },
          "index": 9,
          "statement": "%8.<init>(keys, %9)",
          "successors": [
            10
          ],
          "normal_end": false,
          "exceptional_end": false,
          "from": "RETURNED",
          "to": "REWRITTEN"
        }
      }
    ],
    "preexisting_FLOW_exclusions": [
      {
        "id": 2,
        "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
        "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
      },
      {
        "id": 3,
        "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
        "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
      }
    ],
    "post_cleanup_FLOW_exclusions": [
      {
        "id": 2,
        "name": "java/security/crypto.yaml:jjwt-hs256;0;_<T>_;",
        "key": "Full(mark=ExactMark(group=GroupId(value=1), full=FullMarkId(value=1)))"
      },
      {
        "id": 3,
        "name": "java/security/crypto.yaml:jjwt-none-alg;0;_<T>_;",
        "key": "Full(mark=ExactMark(group=GroupId(value=2), full=FullMarkId(value=2)))"
      },
      {
        "id": 6,
        "name": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=5)))"
      },
      {
        "id": 7,
        "name": "java/security/xss.yaml:xss#sink#1;sink_71;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=6)))"
      },
      {
        "id": 8,
        "name": "java/security/xss.yaml:xss#sink#1;sink_2;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=7)))"
      },
      {
        "id": 10,
        "name": "java/security/xss.yaml:xss#sink#1;sink_23;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=9)))"
      },
      {
        "id": 12,
        "name": "java/security/xss.yaml:xss#sink#1;sink_59;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=11)))"
      },
      {
        "id": 15,
        "name": "java/security/xss.yaml:xss#sink#1;sink_38;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=14)))"
      },
      {
        "id": 16,
        "name": "java/security/xss.yaml:xss#sink#1;sink_25;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=15)))"
      },
      {
        "id": 17,
        "name": "java/security/xss.yaml:xss#sink#1;sink_83;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=16)))"
      },
      {
        "id": 29,
        "name": "java/security/xss.yaml:xss#sink#1;sink_50;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=28)))"
      },
      {
        "id": 31,
        "name": "java/security/xss.yaml:xss#sink#1;sink_1;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=30)))"
      },
      {
        "id": 37,
        "name": "java/security/xss.yaml:xss#sink#1;sink_37;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=36)))"
      },
      {
        "id": 48,
        "name": "java/security/xss.yaml:xss#sink#1;sink_26;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=47)))"
      },
      {
        "id": 58,
        "name": "java/security/xss.yaml:xss#sink#1;sink_35;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=57)))"
      },
      {
        "id": 74,
        "name": "java/security/xss.yaml:xss#sink#1;sink_85;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=73)))"
      },
      {
        "id": 80,
        "name": "java/security/xss.yaml:xss#sink#1;sink_47;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=79)))"
      },
      {
        "id": 90,
        "name": "java/security/xss.yaml:xss#sink#1;sink_49;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=89)))"
      },
      {
        "id": 95,
        "name": "java/security/xss.yaml:xss#sink#1;sink_97;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=94)))"
      },
      {
        "id": 100,
        "name": "java/security/xss.yaml:xss#sink#1;sink_62;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=99)))"
      },
      {
        "id": 103,
        "name": "java/security/xss.yaml:xss#sink#1;sink_14;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=102)))"
      },
      {
        "id": 106,
        "name": "java/security/xss.yaml:xss#sink#1;sink_74;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=105)))"
      },
      {
        "id": 108,
        "name": "java/security/xss.yaml:xss#sink#1;sink_95;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=107)))"
      },
      {
        "id": 113,
        "name": "java/security/xss.yaml:xss#sink#1;sink_61;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=112)))"
      },
      {
        "id": 115,
        "name": "java/security/xss.yaml:xss#sink#1;sink_107;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=114)))"
      },
      {
        "id": 116,
        "name": "java/security/xss.yaml:xss#sink#1;sink_98;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=115)))"
      },
      {
        "id": 117,
        "name": "java/security/xss.yaml:xss#sink#1;sink_73;$<ARTIFICIAL>_3;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=116)))"
      },
      {
        "id": 119,
        "name": "java/security/xss.yaml:xss#sink#1;sink_11;$<ARTIFICIAL>_6;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=118)))"
      },
      {
        "id": 120,
        "name": "java/security/xss.yaml:xss#sink#1;sink_86;$<ARTIFICIAL>_4;3",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=119)))"
      },
      {
        "id": 146,
        "name": "java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=145)))"
      },
      {
        "id": 166,
        "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=165)))"
      },
      {
        "id": 167,
        "name": "java/security/xss.yaml:xss#sink#1;sink_83;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=166)))"
      },
      {
        "id": 170,
        "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=169)))"
      },
      {
        "id": 171,
        "name": "java/security/xss.yaml:xss#sink#1;sink_59;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=170)))"
      },
      {
        "id": 173,
        "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=172)))"
      },
      {
        "id": 174,
        "name": "java/security/xss.yaml:xss#sink#1;sink_11;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=173)))"
      },
      {
        "id": 178,
        "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=177)))"
      },
      {
        "id": 179,
        "name": "java/security/xss.yaml:xss#sink#1;sink_35;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=178)))"
      },
      {
        "id": 181,
        "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=180)))"
      },
      {
        "id": 182,
        "name": "java/security/xss.yaml:xss#sink#1;sink_47;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=181)))"
      },
      {
        "id": 185,
        "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=184)))"
      },
      {
        "id": 186,
        "name": "java/security/xss.yaml:xss#sink#1;sink_107;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=185)))"
      },
      {
        "id": 192,
        "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=191)))"
      },
      {
        "id": 193,
        "name": "java/security/xss.yaml:xss#sink#1;sink_23;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=192)))"
      },
      {
        "id": 194,
        "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=193)))"
      },
      {
        "id": 195,
        "name": "java/security/xss.yaml:xss#sink#1;sink_95;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=194)))"
      },
      {
        "id": 199,
        "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;4",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=198)))"
      },
      {
        "id": 200,
        "name": "java/security/xss.yaml:xss#sink#1;sink_71;$H;5",
        "key": "Full(mark=ExactMark(group=GroupId(value=0), full=FullMarkId(value=199)))"
      }
    ],
    "post_exclusions_equal_previous_union_all_receiver_masks": true
  },
  "source_guards": [
    {
      "old": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/source/core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRCallPlanBuilder.kt",
        "bytes": 19039,
        "sha256": "d40274e6f306c1eab9e55e80a6ebab05e4ed6f0416df4659584a845573f6c1f7"
      },
      "current": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRCallPlanBuilder.kt",
        "bytes": 19039,
        "sha256": "d40274e6f306c1eab9e55e80a6ebab05e4ed6f0416df4659584a845573f6c1f7"
      },
      "byte_identical": true
    },
    {
      "old": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/source/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/CallPlan.kt",
        "bytes": 14739,
        "sha256": "01b9869c73f6e496af414a3200d18abc010b18c8347b3440f0dd498ca07f47fa"
      },
      "current": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/CallPlan.kt",
        "bytes": 14739,
        "sha256": "01b9869c73f6e496af414a3200d18abc010b18c8347b3440f0dd498ca07f47fa"
      },
      "byte_identical": true
    }
  ],
  "kernel_source": [
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/ApOps.kt",
        "bytes": 11211,
        "sha256": "5a3a59d641738705fd4d63391a5759e5b6d8738024fbdb3c8d0a5c851261372a"
      },
      "start_line": 132,
      "end_line": 152,
      "text": "        }\n    }\n\n    /** Selected FULL mask; null Cleaner.mark retains its all-mark meaning on the scalar API. */\n    fun cleanSelectedFullMask(c: Facts, premise: PremiseKey, geometry: Cleaner, selected: MarkSet,\n                              mode: ApMode, request: (MarkSet) -> Unit, out: ApOut) {\n        check(geometry.mark != null) { \"A FULL cleanup block must have selected-mark geometry\" }\n        val sink = if (c.base != geometry.base) out else object : ApOut {\n            override fun result(f: Facts) = out.result(manager.selectedProtection(f, selected))\n            override fun markRequest(mark: TaintMark) = out.markRequest(mark)\n        }\n        val protected = (c as? TaintTree)?.protectedPart()\n        val masks = protected?.let { part -> ProtectionOutputs(manager).also {\n            cleanSelectedFullMask(manager, part, geometry, selected, mode, {}, it.run1Policy(manager, mode))\n        } }\n        val target = if (masks == null) sink else object : ApOut {\n            override fun result(f: Facts) = sink.result(masks.attach(f))\n            override fun markRequest(mark: TaintMark) = sink.markRequest(mark)\n        }\n        cleanSelectedFullMask(manager, c, geometry, selected, mode, request, target.run1Policy(manager, mode))\n    }"
    },
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Clean.kt",
        "bytes": 9473,
        "sha256": "c0c18f13d44e186876d2443f8156ee0669b13e4c6edc0c7f1508a3e77cc7da71"
      },
      "start_line": 1,
      "end_line": 50,
      "text": "package org.opentaint.dataflow.bidi.ap\n\nimport org.opentaint.dataflow.util.Cancellation\nimport java.util.ArrayDeque\n\n/** A leaf on the cleaner spine is above or at its position. */\ninternal fun cleanPosAt(cl: Cleaner, tail: Tail, d: Int, admitsRest: Boolean): Pos =\n    if (d < cl.pathArray.size) when (tail) {\n        Tail.EXACT -> Pos.DISJOINT\n        Tail.STAR, Tail.ANY, Tail.ANY_TAINT -> if (admitsRest) Pos.PART else Pos.DISJOINT\n    } else when (tail) {\n        Tail.EXACT -> if (cl.reach == CleanReach.BELOW) Pos.DISJOINT else Pos.INSIDE\n        else -> if (cl.reach == CleanReach.AT_AND_BELOW) Pos.INSIDE else Pos.PART\n    }\n\nprivate class CleanFrame<P : TrieLeaf>(val node: TrieNode<P>, val kept: P, val accessor: Int)\n\n/** Keep the original positional callback interface. */\ninternal fun <P : TrieLeaf> LeafAlgebra<P>.cleanSpine(\n    n: TrieNode<P>, p: IntArray, reach: CleanReach, d: Int,\n    atNode: (Int, P) -> P, inside: (TrieNode<P>) -> TrieNode<P>?,\n): TrieNode<P>? = cleanSpine(n, p, reach, d, null, atNode, inside)\n\n/** Visit and rebuild one spine. Only children below its end go through inside. */\ninternal fun <P : TrieLeaf> LeafAlgebra<P>.cleanSpine(\n    n: TrieNode<P>, p: IntArray, reach: CleanReach, d: Int, cancellation: Cancellation?,\n    atNode: (Int, P) -> P, inside: (TrieNode<P>) -> TrieNode<P>?,\n): TrieNode<P>? {\n    val parents = ArrayDeque<CleanFrame<P>>()\n    var current = n\n    var depth = d\n    var result: TrieNode<P>?\n    while (true) {\n        cancellation?.checkpoint()\n        val kept = atNode(depth, current.leaf)\n        if (depth >= p.size) {\n            result = if (reach == CleanReach.EXACT) withLeaf(current, kept) else {\n                val kids = retainChildren(current, cancellation) { true }\n                withLeaf(kids?.let(inside), kept)\n            }\n            break\n        }\n        val accessor = p[depth]\n        val child = current.child(accessor)\n        if (child == null) {\n            result = replaceChild(current, kept, accessor, null)\n            break\n        }\n        parents.addLast(CleanFrame(current, kept, accessor))\n        current = child"
    },
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Clean.kt",
        "bytes": 9473,
        "sha256": "c0c18f13d44e186876d2443f8156ee0669b13e4c6edc0c7f1508a3e77cc7da71"
      },
      "start_line": 73,
      "end_line": 114,
      "text": "\n/** Exact FULL-mask form of the selected nonstatic kernel. Geometry stays in the existing spatial walker. */\ninternal fun cleanSelectedFullMask(m: ApManager, c: Facts, cl: Cleaner, selected: MarkSet,\n                                   mode: ApMode, request: (MarkSet) -> Unit, out: ApOut) {\n    require(mode.run1 && mode.direction == Direction.FORWARD && mode.markMode == MarkMode.FULL)\n    require(cl.base != STATIC && cl.base != org.opentaint.dataflow.ap.ifds.AccessPathBase.Zero)\n    m.cancellation.checkpoint()\n    if (c.base != cl.base) { out.result(c); return }\n    when (c) {\n        is Reach -> out.result(c)\n        is FlowTree -> {\n            // Selected nonstatic FLOW cleaning intentionally has no spatial test.\n            val mx = m.intern(c.markExclusion + selected)\n            request(selected) // incoming mx does not remove requested memberships\n            out.result(m.flowTree(c.base, c.layer, c.exclusion, mx, c.root, c.tail))\n        }\n        is TaintTree -> TaintClean(m, c, cl, mode, out, selected).run()\n    }\n}\n\n/** The selected-mark branch changes the header and shares every path. */\nprivate class FlowClean(private val m: ApManager, private val c: FlowTree, private val cl: Cleaner,\n                        private val mode: ApMode, private val out: ApOut) {\n    private val results = Results(m, c.base)\n    private val tail = c.tail\n\n    fun run() {\n        val selected = cl.mark?.let { m.marks.runtimeAtom(it, mode.markMode) }\n        if (selected != null) {\n            if (mode.run1 && c.base == STATIC) { selectedStatic(selected); return }\n            results.flow(c.layer, c.exclusion, m.intern(c.markExclusion + selected), c.root, c.tail)\n            if (mode.run1) out.markRequest(selected)\n            results.flush(out)\n            return\n        }\n        FlowAlgebra.cleanSpine(c.root, cl.pathArray, cl.reach, 0, m.cancellation, ::row) { null }\n            ?.let { results.flow(c.layer, c.exclusion, c.markExclusion, it, c.tail) }\n        results.flush(out)\n    }\n\n    /** A disjoint static field is not a mark-interest producer. Split selected\n     * leaves before changing mx so an unrelated sibling keeps its own header. */"
    },
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Clean.kt",
        "bytes": 9473,
        "sha256": "c0c18f13d44e186876d2443f8156ee0669b13e4c6edc0c7f1508a3e77cc7da71"
      },
      "start_line": 150,
      "end_line": 207,
      "text": "    }\n}\n\n/** Concrete and all-mark cleaners retain the spatial and partial-cleaning rows. */\nprivate class TaintClean(private val m: ApManager, private val c: TaintTree, private val cl: Cleaner,\n                         private val mode: ApMode, private val out: ApOut, private val selected: MarkSet? = null) {\n    private val results = Results(m, c.base)\n    private val anyTail = c.anyTail\n\n    private fun gone(marks: MarkSet): MarkSet = when {\n        selected != null -> marks intersect selected\n        cl.mark == null || marks.isEmpty -> marks\n        mode.markMode == MarkMode.GROUP -> MarkSet.EMPTY // selected full mark cannot kill wildcard group\n        else -> marks.intersect(m.markSetOf(cl.mark))\n    }\n\n    fun run() {\n        m.taintAlg.cleanSpine(c.root, cl.pathArray, cl.reach, 0, m.cancellation, ::row) { kids ->\n            m.taintAlg.mapLeaves(kids, m.cancellation) {\n                m.taintLeaves(it.exact - gone(it.exact), it.any - gone(it.any))\n            }\n        }?.let { results.taint(c.layer, it, c.exclusion, c.anyTail) }\n        results.flush(out)\n    }\n\n    private fun row(d: Int, leaf: TaintLeaves): TaintLeaves =\n        m.taintLeaves(cut(d, Tail.EXACT, leaf.exact), cut(d, anyTail, leaf.any))\n\n    private fun cut(d: Int, tail: Tail, marks: MarkSet): MarkSet {\n        val removed = gone(marks)\n        if (removed.isEmpty) return marks\n        val path = cl.pathArray\n        when (cleanPosAt(cl, tail, d, d >= path.size || c.exclusion.admits(path[d]))) {\n            Pos.DISJOINT -> return marks\n            Pos.INSIDE -> Unit\n            Pos.PART -> {\n                val at = m.path(path.copyOf(d))\n                when {\n                    tail == Tail.ANY_TAINT && d == path.size - 1 && cl.reach != CleanReach.EXACT -> {\n                        if (mode.run1) put(Layer.DEMAND, at, Tail.ANY_TAINT, removed)\n                        else put(c.layer, at, Tail.ANY_TAINT, removed, c.exclusion.union(ExclusionSet.of(path[d])))\n                        if (cl.reach == CleanReach.BELOW) put(c.layer, cl.path, Tail.EXACT, removed)\n                    }\n                    (tail.isAny || tail == Tail.STAR) && cl.reach == CleanReach.BELOW && d == path.size ->\n                        put(c.layer, at, Tail.EXACT, removed)\n                    else -> put(Layer.DEMAND, at, tail, removed, c.exclusion)\n                }\n            }\n        }\n        return marks - removed\n    }\n\n    private fun put(layer: Layer, at: PathNode?, tail: Tail, marks: MarkSet,\n                    exclusion: ExclusionSet = ExclusionSet.Empty) {\n        val leaf = if (tail == Tail.EXACT) m.taintLeaves(marks, MarkSet.EMPTY) else m.taintLeaves(MarkSet.EMPTY, marks)\n        val root = m.taintAlg.prepend(m, at, m.taintAlg.leafNode(leaf))\n        results.taint(layer, root, exclusion, if (tail == Tail.EXACT) Tail.ANY_TAINT else tail)\n    }"
    },
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/CallPlan.kt",
        "bytes": 14739,
        "sha256": "01b9869c73f6e496af414a3200d18abc010b18c8347b3440f0dd498ca07f47fa"
      },
      "start_line": 84,
      "end_line": 150,
      "text": "internal class FullCleanupBlock(\n    val first: Int,\n    val end: Int,\n    val geometry: Cleaner,\n    val marks: MarkSet,\n    private val raw: List<CleanStep>,\n) {\n    fun marksFrom(firstStep: Int, cancellation: Cancellation? = null): MarkSet {\n        require(firstStep in first until end)\n        if (firstStep == first) return marks\n        val selected = IntArray(end - firstStep)\n        for (index in firstStep until end) {\n            cancellation?.checkpoint()\n            selected[index - firstStep] = checkNotNull((raw[index] as CleanStep.Clean).cleaner.mark).id\n        }\n        return MarkSet(selected)\n    }\n}\n\n/** Linear raw-index directory. Rebuilding a form does not change resume addresses. */\ninternal class ReturnFullCleanupSchedule private constructor(\n    private val blocks: List<FullCleanupBlock>,\n    private val byStep: IntArray,\n) {\n    fun blockContaining(step: Int): FullCleanupBlock? =\n        byStep.getOrNull(step)?.takeIf { it >= 0 }?.let { blocks[it] }\n\n    fun storage(counts: FormStorageCounts) {\n        counts.index(byStep)\n        counts.include(blocks)\n        for (block in blocks) counts.index(block.marks.data)\n    }\n\n    companion object {\n        fun compile(raw: List<CleanStep>, marks: MarkTable): ReturnFullCleanupSchedule? {\n            fun eligible(step: CleanStep): Cleaner? {\n                val cleaner = (step as? CleanStep.Clean)?.cleaner ?: return null\n                if (cleaner.base == AccessPathBase.Zero || cleaner.base == AccessPathBase.ClassStatic ||\n                    cleaner.base is AccessPathBase.CleanerTemporary) return null\n                val mark = cleaner.mark ?: return null\n                return cleaner.takeIf { marks.isFull(mark) }\n            }\n            fun same(a: Cleaner, b: Cleaner) = a.base == b.base && a.reach == b.reach &&\n                a.pathArray.contentEquals(b.pathArray)\n            val blocks = ArrayList<FullCleanupBlock>()\n            val byStep = IntArray(raw.size) { -1 }\n            var start = 0\n            while (start < raw.size) {\n                val geometry = eligible(raw[start])\n                if (geometry == null) { start++; continue }\n                var end = start + 1\n                while (end < raw.size) {\n                    val next = eligible(raw[end]) ?: break\n                    if (!same(geometry, next)) break\n                    end++\n                }\n                if (end - start >= 2) {\n                    val mask = MarkSet(IntArray(end - start) { index ->\n                        checkNotNull((raw[start + index] as CleanStep.Clean).cleaner.mark).id\n                    })\n                    for (index in start until end) byStep[index] = blocks.size\n                    blocks += FullCleanupBlock(start, end, geometry, mask, raw)\n                }\n                start = end\n            }\n            return if (blocks.isEmpty()) null else ReturnFullCleanupSchedule(ownedList(blocks), byStep)\n        }"
    },
    {
      "file": {
        "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/current/core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodCallServices.kt",
        "bytes": 35176,
        "sha256": "b886633752695394c5f5998579e2dc1aa0ae303079b28d978f40325d1a2fe339"
      },
      "start_line": 208,
      "end_line": 231,
      "text": "            if (schedule != null && !schedule.execute(stepIndex, firstStep)) { stepIndex++; continue }\n            val block = fullSchedule?.blockContaining(stepIndex)\n            if (block != null) {\n                val statistics = core.context.shared.n2Statistics\n                if (current.all { fullCleanupCollectorFixed(it.premise, it.facts) }) {\n                    val mask = block.marksFrom(stepIndex, core.ap.cancellation)\n                    statistics?.fullCleanupBlock(stepIndex > block.first, block.end - stepIndex, current.size)\n                    val next = PlanFacts(core.ap)\n                    for (input in current) {\n                        core.ap.cancellation.checkpoint()\n                        val address = at(input, stepIndex, CleanerPhase.CLEAN)\n                        core.ops.cleanSelectedFullMask(input.facts, input.premise, block.geometry, mask, core.mode,\n                            request = { requested ->\n                                statistics?.fullCleanupRequested(requested.size)\n                                core.needGroups(address, requested)\n                            }, out = core.collect(address) { premise, result ->\n                                if (result.base == STATIC) core.promoteStaticSummary(premise, result)\n                                else next += planFact(premise, result, input.identityCandidate)\n                            })\n                        if (statistics != null && current.size == 1 && input.facts is FlowTree &&\n                            input.facts.base == block.geometry.base) {\n                            statistics.fullCleanupSingletonFlow(block.end - stepIndex)\n                        }\n                    }"
    }
  ],
  "limitations": [
    "All14 captured primitive selected-T cleaner births use ResponseEntity constructor return cleanup; the 2000-new_flag category cap excludes later offers. This is not an inventory of all cleaners or all marks.",
    "Three fact geometries are Body/ANY, Body.Element/ANY, Body/STAR. A distinct overlapping cleaner geometry was not captured; no real PART or INSIDE example is invented.",
    "Telemetry block geometry is reconstructed exactly from all cold raw steps and byte-identical compiler/kernel source. DeviceAuth and DeviceController reuse the same two-argument API descriptor but their complete live forms were not captured; their geometry is explicitly inferred.",
    "No project run, JVM, Gradle build, code edit or semantic callback is invoked by this extractor."
  ],
  "optional_bounded_closure": "If direct current descriptors are needed, reconstruct only these three actual call forms with fixed class/rule/model inputs; serialize RETURNED→REWRITTEN blockContaining(90).geometry, marksFrom(90), scalar T cleaners and bound copy edges. Do not create RunManager, prescan, work queues, body propagation, or execute aliases. If alias form construction is coupled, stop after rewriterSteps or use existing frozen forms. No full project analyzer run is needed."
}
```

</details>

### 7.2 AP controls and checks

All 61 checks pass across 15 evaluated cases. Source hashes match this checkout.
The tested runtime core is `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`,
the same `core` tree as runtime revision `fcfe2e90558665d813bd74207832d4ae3fc83aec`.
No production classes were edited by the controls.

<details>
<summary>Complete inputs, outputs, 61 check results, source/class hashes and evidence limits</summary>

```json
{
  "state": "PASS_SOURCE_ONLY_NECESSITY_ANALYSIS",
  "utc": "2026-10-27T09:25:54.045429+00:00",
  "runtime_revision": "fcfe2e90558665d813bd74207832d4ae3fc83aec",
  "runtime_core_tree": "57ca8d4940e8fb52e7eed6151928d4025c7d7ad9",
  "actual_project_latest_reached": "run-1",
  "actual_project_latest_completed": "run-1",
  "actual_project_latest_accepted": "run-1",
  "controls": 15,
  "checks": {
    "compile_exit0": true,
    "runtime_exit0": true,
    "fifteen_cases": true,
    "selected_disjoint_exact_root/ordinary_spatial_geometry_layer_E_identical": true,
    "selected_disjoint_exact_root/selected_scalar_bulk_parity": true,
    "all_disjoint_exact_root/ordinary_spatial_geometry_layer_E_identical": true,
    "all_disjoint_exact_root/no_FLOW_mark_exclusion": true,
    "selected_below_root/ordinary_spatial_geometry_layer_E_identical": true,
    "selected_below_root/selected_scalar_bulk_parity": true,
    "all_below_root/ordinary_spatial_geometry_layer_E_identical": true,
    "all_below_root/no_FLOW_mark_exclusion": true,
    "all_partial_child/ordinary_spatial_geometry_layer_E_identical": true,
    "all_partial_child/no_FLOW_mark_exclusion": true,
    "all_full_kill/ordinary_spatial_geometry_layer_E_identical": true,
    "all_full_kill/no_FLOW_mark_exclusion": true,
    "all_existing_flag_disjoint/ordinary_spatial_geometry_layer_E_identical": true,
    "all_existing_flag_disjoint/no_FLOW_mark_exclusion": true,
    "all_later_must_partial/ordinary_spatial_geometry_layer_E_identical": true,
    "all_later_must_partial/no_FLOW_mark_exclusion": true,
    "selected_other_mark/ordinary_spatial_geometry_layer_E_identical": true,
    "selected_other_mark/selected_scalar_bulk_parity": true,
    "selected_other_base/ordinary_spatial_geometry_layer_E_identical": true,
    "all_disjoint_omits_only_new_flag": true,
    "selected_disjoint_has_same_problematic_mx": true,
    "all_existing_flag_survives": true,
    "all_full_kill_no_flag_or_result": true,
    "all_BELOW_exact_survivor_unchanged": true,
    "all_later_MUST_E_preserved": true,
    "unselected_mark_already_plain": true,
    "other_base_already_plain": true,
    "BELOW/selected/same_marked_geometry_without_new_flag": true,
    "BELOW/selected/current_flag_blocks_removal": true,
    "BELOW/selected/stripped_flag_allows_removal": true,
    "BELOW/selected/original_backward_T_answer": true,
    "BELOW/selected/mx_matches_selected_policy": true,
    "BELOW/selected/StrongQueries_not_used": true,
    "BELOW/all/same_marked_geometry_without_new_flag": true,
    "BELOW/all/current_flag_blocks_removal": true,
    "BELOW/all/stripped_flag_allows_removal": true,
    "BELOW/all/original_backward_T_answer": true,
    "BELOW/all/mx_matches_selected_policy": true,
    "BELOW/all/StrongQueries_not_used": true,
    "disjoint_EXACT/selected/same_marked_geometry_without_new_flag": true,
    "disjoint_EXACT/selected/current_flag_blocks_removal": true,
    "disjoint_EXACT/selected/stripped_flag_allows_removal": true,
    "disjoint_EXACT/selected/original_backward_T_answer": true,
    "disjoint_EXACT/selected/mx_matches_selected_policy": true,
    "disjoint_EXACT/selected/StrongQueries_not_used": true,
    "disjoint_EXACT/all/same_marked_geometry_without_new_flag": true,
    "disjoint_EXACT/all/current_flag_blocks_removal": true,
    "disjoint_EXACT/all/stripped_flag_allows_removal": true,
    "disjoint_EXACT/all/original_backward_T_answer": true,
    "disjoint_EXACT/all/mx_matches_selected_policy": true,
    "disjoint_EXACT/all/StrongQueries_not_used": true,
    "static_run1_disjoint_unchanged_mx": true,
    "static_backward_disjoint_excludes_T": true,
    "Lean_exit0": true,
    "Lean_eight_declarations_audited": true,
    "Lean_constructive_only": true,
    "actual_gain_selected_bulk_cleaner": true,
    "actual_gain_geometry_unchanged": true
  },
  "check_count": 61,
  "all_pass": true,
  "proof": {
    "theorems": 7,
    "executable_witness_definitions": 1,
    "audited_declarations": 8,
    "observed_axioms": [
      "Quot.sound",
      "propext"
    ],
    "scope": "Local original AP all-mark cleaner replay given an abstract pair and surviving concrete pair. Not a complete Kotlin/typed-store/engine or paired-spatial-cleaner proof."
  },
  "findings": {
    "selected_disjoint": "Dropping NEW flag alone is unsafe with current global mx; actual operator disjoint branch loses marked guide and backward FLOW rejects T.",
    "RemoveAllMarks": "No NEW selected-mark barrier is needed for this mark-independent cleaner if inherited masks and all existing spatial/layer/E transfer stay unchanged. Existing original-AP mode and executable local witness support the exception; typed/global integration obligations remain.",
    "static_disjoint": "Local run1 no-mx does not justify flag omission: same backward cleaner changes mx. No safe exception asserted.",
    "paired_spatial_change": "Semantic change requiring forward/backward replay proof; forward disjointness is not stable under backward coarsening. Existing root-cleaner regression is a mandatory test, not automatically solved by run1 spatial split."
  },
  "actual_local_gain": {
    "line": 74,
    "row_sha256": "951c4645f40d51bbbb84700ac092defba7ce6382fa94d4286ef9a4776d5f3b55",
    "record": {
      "event": "new_flag",
      "method": "org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}]",
      "initial": [
        {
          "base": "arg(0)",
          "path_ids": [],
          "path": [],
          "path_full": [],
          "tail": "STAR",
          "E": "Empty",
          "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
        }
      ],
      "place": "CleanerInput(operation=OperationId(form=FormKey(owner=org.opentaint.dataflow.bidi.interp.FormOwner@7dc5753, method=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List), context=org.thingsboard.server.controller.TelemetryController$6#onSuccess(java.util.List) [{}], statement=%8.<init>(keys, %9)), stageOrdinal=6, action=null, substep=0), step=90, phase=CLEAN)",
      "input": {
        "base": "<this>",
        "layer": "DEMAND",
        "selected_leaves": [
          {
            "base": "<this>",
            "path_ids": [
              5596,
              640
            ],
            "path": [
              "HttpEntity#Body",
              "Iterable#Element"
            ],
            "path_full": [
              "org.springframework.http.HttpEntity.Body",
              "java.lang.Iterable.Element"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "selected_protection": []
      },
      "result": {
        "base": "<this>",
        "layer": "DEMAND",
        "selected_leaves": [
          {
            "base": "<this>",
            "path_ids": [
              5596,
              640
            ],
            "path": [
              "HttpEntity#Body",
              "Iterable#Element"
            ],
            "path_full": [
              "org.springframework.http.HttpEntity.Body",
              "java.lang.Iterable.Element"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ],
        "selected_protection": [
          {
            "base": "<this>",
            "path_ids": [
              5596,
              640
            ],
            "path": [
              "HttpEntity#Body",
              "Iterable#Element"
            ],
            "path_full": [
              "org.springframework.http.HttpEntity.Body",
              "java.lang.Iterable.Element"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "java/security/xss.yaml:xss#sink#1;sink_13;$<ARTIFICIAL>_3;3"
          }
        ]
      },
      "extra": null,
      "new_flag_scope": "local input lacked selected mask; output has selected mask; not global first producer",
      "stack": [
        "java.base/java.lang.Thread.getStackTrace(Thread.java:1619)",
        "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe(ProtectedStaticTrace.kt:110)",
        "org.opentaint.dataflow.bidi.engine.ProtectedStaticTrace.observe$default(ProtectedStaticTrace.kt:81)",
        "org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer$collect$2.result(RunMethodAnalyzer.kt:239)",
        "org.opentaint.dataflow.bidi.ap.ApOps$cleanSelectedFullMask$sink$1.result(ApOps.kt:140)",
        "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result$lambda$0(ApOut.kt:12)",
        "org.opentaint.dataflow.bidi.ap.ConclusionsKt.run1CoverFacts(Conclusions.kt:108)",
        "org.opentaint.dataflow.bidi.ap.ApOutKt$run1Policy$1.result(ApOut.kt:12)",
        "org.opentaint.dataflow.bidi.ap.Results.flush(ApOut.kt:56)",
        "org.opentaint.dataflow.bidi.ap.TaintClean.run(Clean.kt:172)",
        "org.opentaint.dataflow.bidi.ap.CleanKt.cleanSelectedFullMask(Clean.kt:89)",
        "org.opentaint.dataflow.bidi.ap.ApOps.cleanSelectedFullMask(ApOps.kt:151)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain(RunMethodCallServices.kt:219)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.cleanChain$default(RunMethodCallServices.kt:163)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.applyStage(RunMethodCallServices.kt:152)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow(RunMethodCallServices.kt:101)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.flow$default(RunMethodCallServices.kt:68)",
        "org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process$lambda$4(RunMethodCallServices.kt:62)",
        "org.opentaint.dataflow.bidi.interp.FormsCache.withForm(FormsCache.kt:100)",
        "org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms.withCall(JIRMethodForms.kt:58)"
      ]
    }
  },
  "source_sha256": {
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/ApOps.kt": "5a3a59d641738705fd4d63391a5759e5b6d8738024fbdb3c8d0a5c851261372a",
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Clean.kt": "c0c18f13d44e186876d2443f8156ee0669b13e4c6edc0c7f1508a3e77cc7da71",
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/FlowBackedProtection.kt": "babe4411354ceeaa06c169602c8bae726ae29b83ad979fb8febaa95a70f37d62",
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/FlowBackedCoverage.kt": "1526c8b423685530bce07026a87a363c71eb6cf20dc08f30885535737453ea40",
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Summary.kt": "decefd8631355ca5e95456ae1130d346aa3d31a608801a04bb233a5d556e69cc",
    "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt": "c872b6325718e4e76db926c6e416a77d69572be0ff5ba8f390ebc80fbcdc6f6a",
    "spec/run1-flow-backed-concrete-relations.md": "0d2381e1153dd69c4b43114208f10d9ffd27991b6a30df74388fdcd4f816572f",
    "spec/lean/ApSpec/BaseCleaner.lean": "bae707f5332119765b5369035538e0213d3a8b7752dc3adba54f5d50b8f9ad98",
    "spec/lean/ApSpec/FlowBackedRelationsCounterexamples.lean": "7fa1480fc6529819f8250d1bb49f7ad02749e78bc81e9da0c2742f80468503eb",
    "spec/lean/ApSpec/ReviewBaseCleaner.lean": "42121cf891adac7830d4225a12e010bad189794ba56870325aa5dec276d33e7e",
    "spec/lean/ApSpec/ReviewRootCleaner.lean": "9838de572eb6594ec3012efc68c97c87b5b37190123673dc6d4506ac14c2c273"
  },
  "actual_source_receipts": {
    "current_witness": {
      "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/trace-analysis/v2/causal-witness.json",
      "sha256": "56efccffb482eaa8bb0e68cbc53a4b7e99e7c275e6b158412752605986934fc8"
    },
    "old_cold_geometry": {
      "path": "/drive-testcomp/opentaint-go-rules/protected-statics-root-cause-20261027/baseline/analysis/selected-old-point-and-form-proof-rows.json",
      "sha256": "581c742406cf94d8546281df890a8342eedebcb7c3d5bc65eeff28deb8025e86"
    }
  },
  "artifacts": {
    "ProtectionNecessity.kt": "f998c47541e2d561085bf01a444e3dc6dca8ebc3fdc2f9667edf1ac6bf160c76",
    "run.py": "2a7aa675d125f765fd0e3cd8b7e71c8a4179babc51338ff0b8cad3a75cdf74a6",
    "terminal.json": "2b7ebce9a84cc101cef222ebd25e7c9319e253c8e4fd85202aa88aa4243d13c6",
    "compile.log": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "current.jsonl": "cdf1eeb515a1661801f2fd22edc1e752fe9cf9123b47087eb29ebc3fe1505c76",
    "NeutralCleaner.lean": "5a4031082b16c915277c708230b434e0c99175653f82314d81dc805a3d12eec4",
    "NeutralCleaner.log": "70b156e51620d442ea0ef3a5ac245eac80c9e921d3e79ad9f4c214050473b7ac",
    "lean-terminal.json": "98788dc96bd079f6b092defb77315e8fb7c41f83ea613b9a30c660dcf3cb1f44"
  },
  "rows": [
    {
      "kind": "local",
      "case": "selected_disjoint_exact_root",
      "selected": true,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [
            "Box#f"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [
        "T"
      ],
      "bulk": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ]
    },
    {
      "kind": "local",
      "case": "all_disjoint_exact_root",
      "selected": false,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [
            "Box#f"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "selected_below_root",
      "selected": true,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [
        "T"
      ],
      "bulk": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ]
    },
    {
      "kind": "local",
      "case": "all_below_root",
      "selected": false,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "all_partial_child",
      "selected": false,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "all_full_kill",
      "selected": false,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [],
      "omit_new_only": [],
      "FLOW": [],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "all_existing_flag_disjoint",
      "selected": false,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [
            "Box#f"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": true
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "all_later_must_partial",
      "selected": false,
      "run1": false,
      "input": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY_TAINT",
          "E": "Empty",
          "mark": "T",
          "layer": "NORMAL",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY_TAINT",
            "E": "{0}",
            "mark": "T",
            "layer": "NORMAL",
            "protected": true
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY_TAINT",
            "E": "{0}",
            "mark": "T",
            "layer": "NORMAL",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "STAR",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "local",
      "case": "selected_other_mark",
      "selected": true,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [
            "Box#f"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "U",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "U",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "U",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [
        "T"
      ],
      "bulk": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "U",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ]
    },
    {
      "kind": "local",
      "case": "selected_other_base",
      "selected": true,
      "run1": true,
      "input": [
        {
          "base": "var(1)",
          "path": [
            "Box#f"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "omit_new_only": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#f"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW_requests": [],
      "bulk": null
    },
    {
      "kind": "original_AP_handoff_branch",
      "disjoint_root_EXACT": false,
      "selected": true,
      "marked_read": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "cleaned": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "marked_return_current": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": true
        }
      ],
      "marked_return_omit_new": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "covering_right_FLOW": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current_retained_marked": 1,
      "omit_new_retained_marked": 0,
      "backward_abstract_after_clean": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "backward_left_summary": [
        {
          "base": "arg(0)",
          "path": [
            "Box#left"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": [
              "T"
            ]
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "backward_left_summary_T_answer": [],
      "no_StrongQueries": true
    },
    {
      "kind": "original_AP_handoff_branch",
      "disjoint_root_EXACT": false,
      "selected": false,
      "marked_read": [
        {
          "base": "var(1)",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "cleaned": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "EXACT",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "marked_return_current": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": true
        }
      ],
      "marked_return_omit_new": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "covering_right_FLOW": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current_retained_marked": 1,
      "omit_new_retained_marked": 0,
      "backward_abstract_after_clean": [
        [
          {
            "base": "var(1)",
            "path": [],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "backward_left_summary": [
        {
          "base": "arg(0)",
          "path": [
            "Box#left"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "backward_left_summary_T_answer": [
        [
          {
            "base": "arg(0)",
            "path": [
              "Box#left"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "no_StrongQueries": true
    },
    {
      "kind": "original_AP_handoff_branch",
      "disjoint_root_EXACT": true,
      "selected": true,
      "marked_read": [
        {
          "base": "var(1)",
          "path": [
            "Box#value"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "cleaned": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#value"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "marked_return_current": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": true
        }
      ],
      "marked_return_omit_new": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "covering_right_FLOW": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current_retained_marked": 1,
      "omit_new_retained_marked": 0,
      "backward_abstract_after_clean": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#value"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "backward_left_summary": [
        {
          "base": "arg(0)",
          "path": [
            "Box#left"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": [
              "T"
            ]
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "backward_left_summary_T_answer": [],
      "no_StrongQueries": true
    },
    {
      "kind": "original_AP_handoff_branch",
      "disjoint_root_EXACT": true,
      "selected": false,
      "marked_read": [
        {
          "base": "var(1)",
          "path": [
            "Box#value"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "cleaned": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#value"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "marked_return_current": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": true
        }
      ],
      "marked_return_omit_new": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": "T",
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "covering_right_FLOW": [
        {
          "base": "ret",
          "path": [],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "current_retained_marked": 1,
      "omit_new_retained_marked": 0,
      "backward_abstract_after_clean": [
        [
          {
            "base": "var(1)",
            "path": [
              "Box#value"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "backward_left_summary": [
        {
          "base": "arg(0)",
          "path": [
            "Box#left"
          ],
          "tail": "ANY",
          "E": "Empty",
          "mark": {
            "FLOW_excludes": []
          },
          "layer": "DEMAND",
          "protected": false
        }
      ],
      "backward_left_summary_T_answer": [
        [
          {
            "base": "arg(0)",
            "path": [
              "Box#left"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "no_StrongQueries": true
    },
    {
      "backward_same_disjoint_FLOW": [
        [
          {
            "base": "<static>",
            "path": [
              "<static>(C)",
              "Box#a"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": [
                "T"
              ]
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "kind": "static_disjoint_run1",
      "current": [
        [
          {
            "base": "<static>",
            "path": [
              "<static>(C)",
              "Box#a"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": true
          }
        ]
      ],
      "omit_new": [
        [
          {
            "base": "<static>",
            "path": [
              "<static>(C)",
              "Box#a"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": "T",
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "FLOW": [
        [
          {
            "base": "<static>",
            "path": [
              "<static>(C)",
              "Box#a"
            ],
            "tail": "ANY",
            "E": "Empty",
            "mark": {
              "FLOW_excludes": []
            },
            "layer": "DEMAND",
            "protected": false
          }
        ]
      ],
      "requests": []
    }
  ],
  "first_class_resource_hashes": {
    "current": {
      "org/opentaint/dataflow/bidi/ap/ApOps.class": "64cbc5aea1db8ec5c521c6652147232efd16098a18b04364b98f572a7b0c7af4",
      "org/opentaint/dataflow/bidi/ap/DemandKt.class": "4472ef0e29740708afe78f15a92d80046803095d0e4a90a5ced733a311e42a3a",
      "org/opentaint/dataflow/bidi/ap/Run1SummaryAliasesKt.class": "3eaed337e29b29eaf6d8e96d3901c914775f7bcc8661dd0a04fe87796f4f2fa4",
      "org/opentaint/dataflow/bidi/store/FlowBackedSummaries.class": "bce503406c98ac28e5b394c936c40306459f7bfba67f5598c9b6dc0726623acb",
      "org/opentaint/dataflow/bidi/store/DiagonalRelations.class": "e5dbb4d30d41c05dd46667471a4054c4db0ba684e98c7284c1977c9482a2f16c"
    }
  },
  "project_runs": 0,
  "Gradle_runs": 0,
  "production_edits": 0,
  "limits": [
    "No throughput or flag-population impact is measured. Actual row74 is selected-T, not RemoveAllMarks, so the all-mark exception does not eliminate this captured origin.",
    "Local operator controls exercise run1 FULL and one later MUST/E row. Lean certificate uses original scalar AP, no StrongQueries, and assumes a related abstract input; full typed/all-run adapter induction remains for implementation.",
    "The earlier guarded0→11 AP fixture is a counterfactual alias-delivery isolation. Production BIND_IN/CALLEES/FLOW502 application is not MemoryEffect-guarded; direct literal FLOW replay was11/11.",
    "All inherited masks remain sticky; the candidate is never clearing existing output flags or records."
  ]
}
```

</details>

### 7.3 Executable local proof

Seven theorems and one executable output witness pass the Lean kernel and axiom
audit. Only `propext` and `Quot.sound` occur; there is no classical choice or
unproved placeholder. The witness assumes an already-related abstract input
and a surviving concrete pair. It does not prove all-run engine integration.
The imported original AP model is in `spec/lean/ApSpec`.

<details>
<summary>Complete Lean source and kernel output</summary>

```lean
/- Source-only local proposal certificate; no runtime or tracked model change.
   The caller supplies the already-established abstract pair. No whole engine
   completeness, source adapter, or universal removal of protection is claimed. -/
import ApSpec.BaseCleaner
namespace ProtectionNecessity
open ApSpec

theorem allMarksNoRequests (cl : Cleaner) (c : AFact) (ht : cl.mark = none) :
    (BaseCleaner.cleanRes cl c).reqs = [] := by
  rw [BaseCleaner.all_marks_unchanged ht]
  unfold ApSpec.cleanRes
  cases hp : cleanPos cl c.fact <;> cases hm : c.fact.mark <;>
    simp [hp, hm, ht, Res.none, Cleaner.markB]

theorem allMarksNeutralMode (cl : Cleaner) (c : AFact) (l : Loc) (ht : cl.mark = none) :
    BaseCleaner.cleanMABBase cl c l = true :=
  BaseCleaner.abstract_mode_all_marks ht

/-- An executable surviving output on the same already-related concrete pair.
    No concrete-mark request can be needed for an all-mark cleaner. -/
def allMarksReplayWitness {cl : Cleaner} {i : PFact} {c : AFact} {l0 l : Loc}
    (ht : cl.mark = none) (hd : den i c.fact l0 l) (hc : cl.cleansB l = false) :
    {r : AFact // r ∈ (BaseCleaner.cleanRes cl c).facts ∧ den i r.fact l0 l} :=
  match BaseCleaner.cleanRes_sound_witness hd hc with
  | .output r member pair => ⟨r,member,pair⟩
  | .request t _ _ member => False.elim (by
      rw [allMarksNoRequests cl c ht] at member
      cases member)

def selectedRoot : Cleaner := ⟨2, [], .exact, some 7⟩
def allRoot : Cleaner := ⟨2, [], .exact, none⟩
def childT : AFact := ⟨⟨2, [10], .any, .conc 7⟩,true⟩
def childFlow : AFact := ⟨⟨2, [10], .any, .star⟩,true⟩
def childLoc : Loc := ⟨2,[10],7⟩

theorem selectedDisjointConcrete :
    cleanPos selectedRoot childT.fact = .disjoint ∧
    BaseCleaner.cleanRes selectedRoot childT = ⟨[childT],[]⟩ := by constructor <;> rfl

theorem selectedDisjointAbstractExcludes :
    BaseCleaner.cleanRes selectedRoot childFlow =
      ⟨[⟨⟨2,[10],.any,.starEx [7]⟩,true⟩],[7]⟩ := by rfl

theorem selectedDisjointNotNeutral :
    BaseCleaner.cleanMABBase selectedRoot childFlow childLoc = false := by rfl

theorem allDisjointPasses :
    BaseCleaner.cleanRes allRoot childT = ⟨[childT],[]⟩ ∧
    BaseCleaner.cleanRes allRoot childFlow = ⟨[childFlow],[]⟩ := by constructor <;> rfl

theorem allDisjointNeutral :
    BaseCleaner.cleanMABBase allRoot childFlow childLoc = true := by rfl

#print axioms allMarksNoRequests
#print axioms allMarksNeutralMode
#print axioms allMarksReplayWitness
#print axioms selectedDisjointConcrete
#print axioms selectedDisjointAbstractExcludes
#print axioms selectedDisjointNotNeutral
#print axioms allDisjointPasses
#print axioms allDisjointNeutral
end ProtectionNecessity
```

```text
/drive-testcomp/opentaint-go-rules/protection-necessity-20261027/ap/NeutralCleaner.lean:13:10: warning: This simp argument is unused:
  hp

Hint: Omit it from the simp argument list.
  [apply] simp [hm, ht, Res.none, Cleaner.markB]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/drive-testcomp/opentaint-go-rules/protection-necessity-20261027/ap/NeutralCleaner.lean:13:14: warning: This simp argument is unused:
  hm

Hint: Omit it from the simp argument list.
  [apply] simp [hp, ht, Res.none, Cleaner.markB]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'ProtectionNecessity.allMarksNoRequests' depends on axioms: [propext]
'ProtectionNecessity.allMarksNeutralMode' does not depend on any axioms
'ProtectionNecessity.allMarksReplayWitness' depends on axioms: [propext, Quot.sound]
'ProtectionNecessity.selectedDisjointConcrete' depends on axioms: [propext]
'ProtectionNecessity.selectedDisjointAbstractExcludes' depends on axioms: [propext]
'ProtectionNecessity.selectedDisjointNotNeutral' does not depend on any axioms
'ProtectionNecessity.allDisjointPasses' depends on axioms: [propext]
'ProtectionNecessity.allDisjointNeutral' does not depend on any axioms
```

</details>

### 7.4 Control worker

This worker changes the fresh protection adapter only on temporary values.
It calls the actual AP and summary store. It does not patch an analyzer class.

<details>
<summary>Complete Kotlin microcontrol source</summary>

```kotlin
package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.FlowBackedSummaries

/** Read-only operator controls. Candidate changes only fresh annotation, not cleanup. */
object ProtectionNecessity {
 @JvmStatic fun main(args:Array<String>) {
  val scenarios=listOf(
   Case("selected_disjoint_exact_root",Tail.ANY,listOf("f"),emptyList(),CleanReach.EXACT,true),
   Case("all_disjoint_exact_root",Tail.ANY,listOf("f"),emptyList(),CleanReach.EXACT,false),
   Case("selected_below_root",Tail.ANY,emptyList(),emptyList(),CleanReach.BELOW,true),
   Case("all_below_root",Tail.ANY,emptyList(),emptyList(),CleanReach.BELOW,false),
   Case("all_partial_child",Tail.ANY,emptyList(),listOf("f"),CleanReach.AT_AND_BELOW,false),
   Case("all_full_kill",Tail.ANY,emptyList(),emptyList(),CleanReach.AT_AND_BELOW,false),
   Case("all_existing_flag_disjoint",Tail.ANY,listOf("f"),emptyList(),CleanReach.EXACT,false,oldFlag=true),
   Case("all_later_must_partial",Tail.ANY_TAINT,emptyList(),listOf("f"),CleanReach.AT_AND_BELOW,false,later=true),
   Case("selected_other_mark",Tail.ANY,listOf("f"),emptyList(),CleanReach.EXACT,true,otherMark=true),
   Case("selected_other_base",Tail.ANY,listOf("f"),emptyList(),CleanReach.EXACT,true,otherBase=true)
  )
  for(c in scenarios)println(json(local(c)))
  println(json(branch(true)));println(json(branch(false)))
  println(json(branch(true,true)));println(json(branch(false,true)))
  println(json(staticDisjoint()))
 }
 private data class Case(val name:String,val tail:Tail,val factPath:List<String>,val cleanPath:List<String>,val reach:CleanReach,val selected:Boolean,
  val oldFlag:Boolean=false,val later:Boolean=false,val otherMark:Boolean=false,val otherBase:Boolean=false)
 private fun neutral(m:ApManager,c:Facts,p:PremiseKey,cl:Cleaner,mode:ApMode):List<Facts>{
  val out=CollectingOut()
  m.transportProtection(c,out){part,sink->cleanFacts(m,part,p,cl,mode,sink.run1Policy(m,mode))}
  return out.results
 }
 private fun local(c:Case):Map<String,Any?>{
  val f=StoreFixtures();val m=f.manager;val ops=f.ops;val t=f.mark("T");val u=f.mark("U")
  val base=AccessPathBase.LocalVar(1);val paths=(c.factPath+c.cleanPath).distinct().associateWith{f.field(it)}
  val layer=if(c.tail==Tail.ANY_TAINT)Layer.NORMAL else Layer.DEMAND
  val mark=if(c.otherMark)u else t
  val plain=m.factsOf(PathFact(base,c.factPath.map{paths.getValue(it)},c.tail,MarkSlot.Concrete(mark)),ExclusionSet.Empty,layer)as TaintTree
  val input=if(c.oldFlag)plain.withProtection(plain.root)else plain
  val flowTail=if(c.tail==Tail.ANY_TAINT)Tail.STAR else c.tail
  val flow=m.factsOf(PathFact(base,c.factPath.map{paths.getValue(it)},flowTail,MarkSlot.STAR),ExclusionSet.Empty,layer)
  val cl=Cleaner(if(c.otherBase)AccessPathBase.LocalVar(2)else base,m.path(c.cleanPath.map{paths.getValue(it)}),c.reach,if(c.selected)t else null)
  val i=m.initial(AccessPathBase.Argument(0),null,Tail.STAR,ExclusionSet.Empty,MarkSlot.Concrete(mark))
  val mode=ApMode(!c.later,Direction.FORWARD,if(c.later)2 else 1,markMode=MarkMode.FULL)
  val cur=CollectingOut();ops.clean(input,i,cl,mode,cur)
  val raw=neutral(m,input,i,cl,mode)
  val fc=CollectingOut();ops.clean(flow,m.initial(i.base,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR),cl,mode,fc)
  val bulk=if(c.selected&&!c.otherBase&&!c.later)CollectingOut().also{ops.cleanSelectedFullMask(input,i,cl,m.markSetOf(t),mode,{},it)}else null
  return mapOf("kind" to "local","case" to  c.name,"selected" to  c.selected,"run1" to  !c.later,"input" to  facts(ops,input),"current" to  cur.results.map{facts(ops,it)},
   "omit_new_only" to  raw.map{facts(ops,it)},"FLOW" to  fc.results.map{facts(ops,it)},"FLOW_requests" to  fc.markRequests.map{m.marks.name(it)},"bulk" to  bulk?.results?.map{facts(ops,it)})
 }
 private fun branch(selected:Boolean,disjointRoot:Boolean=false):Map<String,Any?>{
  val f=StoreFixtures();val m=f.manager;val ops=f.ops;val t=f.mark("T")
  val p=AccessPathBase.Argument(0);val x=AccessPathBase.LocalVar(1);val r=AccessPathBase.Return
  val left=f.field("left");val right=f.field("right");val value=f.field("value");val localPath=if(disjointRoot)listOf(value)else emptyList()
  val mode=ApMode(true,Direction.FORWARD,1,markMode=MarkMode.FULL);val backward=ApMode(false,Direction.BACKWARD,1,markMode=MarkMode.FULL)
  fun read(at:Int)=PathEdge(PathFact(p,listOf(at),Tail.STAR,MarkSlot.STAR),PathFact(x,localPath,Tail.STAR,MarkSlot.STAR),ExclusionSet.Empty)
  val spread=PathEdge(PathFact(x,localPath,Tail.STAR,MarkSlot.STAR),PathFact(r,emptyList(),Tail.ANY,MarkSlot.STAR),ExclusionSet.Empty)
  fun apply(c:Facts,i:PremiseKey,e:PathEdge,md:ApMode):List<Facts> = CollectingOut().also{ops.applyEdge(c,i,e,true,md,it)}.results
  val ti=m.initial(p,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.Concrete(t));val fi=m.initial(p,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR)
  val cl=Cleaner(x,null,if(disjointRoot)CleanReach.EXACT else CleanReach.BELOW,if(selected)t else null)
  val taintRead=apply(ops.startFact(ti,mode),ti,read(left),mode).single()
  val tc=CollectingOut();ops.clean(taintRead,ti,cl,mode,tc)
  val currentReturn=tc.results.flatMap{apply(it,ti,spread,mode)}.single()as TaintTree
  val noNewReturn=neutral(m,taintRead,ti,cl,mode).flatMap{apply(it,ti,spread,mode)}.single()as TaintTree
  val rightFlow=apply(ops.startFact(fi,mode),fi,read(right),mode).flatMap{apply(it,fi,spread,mode)}.single()
  fun retained(value:Facts):Long{val s=FlowBackedSummaries(m);s.add(ti,value);s.add(fi,rightFlow);return s.census().concreteOutputMemberships}
  // Original AP backward abstract start and primitive cleanup; no StrongQueries.
  val ri=m.initial(r,null,Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR)
  val b1=apply(ops.startFact(ri,backward),ri,checkNotNull(ops.reverse(spread)),backward).single()
  val b2=CollectingOut();ops.clean(b1,ri,cl,backward,b2)
  val backSummary=b2.results.flatMap{apply(it,ri,checkNotNull(ops.reverse(read(left))),backward)}.single()
  val actualReturn=m.factsOf(PathFact(r,emptyList(),Tail.EXACT,MarkSlot.Concrete(t)),ExclusionSet.Empty,Layer.NORMAL)
  val answer=CollectingOut();ops.applySummary(actualReturn,ri,backSummary,backward,answer)
  return mapOf("kind" to "original_AP_handoff_branch","disjoint_root_EXACT" to disjointRoot,"selected" to  selected,"marked_read" to  facts(ops,taintRead),"cleaned" to  tc.results.map{facts(ops,it)},
   "marked_return_current" to  facts(ops,currentReturn),"marked_return_omit_new" to  facts(ops,noNewReturn),"covering_right_FLOW" to  facts(ops,rightFlow),
   "current_retained_marked" to  retained(currentReturn),"omit_new_retained_marked" to  retained(noNewReturn),
   "backward_abstract_after_clean" to  b2.results.map{facts(ops,it)},"backward_left_summary" to  facts(ops,backSummary),
   "backward_left_summary_T_answer" to  answer.results.map{facts(ops,it)},"no_StrongQueries" to  true)
 }
 private fun staticDisjoint():Map<String,Any?>{
  val f=StoreFixtures();val m=f.manager;val ops=f.ops;val t=f.mark("T")
  val cls=m.accessors.index(org.opentaint.dataflow.ap.ifds.ClassStaticAccessor("C"));val a=f.field("a");val b=f.field("b")
  val i=m.initial(STATIC,m.path(listOf(cls,a)),Tail.STAR,ExclusionSet.Empty,MarkSlot.Concrete(t))
  val input=m.factsOf(PathFact(STATIC,listOf(cls,a),Tail.ANY,MarkSlot.Concrete(t)),ExclusionSet.Empty,Layer.DEMAND)
  val flow=m.factsOf(PathFact(STATIC,listOf(cls,a),Tail.ANY,MarkSlot.STAR),ExclusionSet.Empty,Layer.DEMAND)
  val cl=Cleaner(STATIC,m.path(listOf(cls,b)),CleanReach.AT_AND_BELOW,t);val mode=ApMode(true,Direction.FORWARD,1)
  val tc=CollectingOut();ops.clean(input,i,cl,mode,tc)
  val fc=CollectingOut();ops.clean(flow,m.initial(STATIC,m.path(listOf(cls,a)),Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR),cl,mode,fc)
  val backward=ApMode(false,Direction.BACKWARD,1)
  val bc=CollectingOut();ops.clean(flow,m.initial(STATIC,m.path(listOf(cls,a)),Tail.STAR,ExclusionSet.Empty,MarkSlot.STAR),cl,backward,bc)
  return mapOf("backward_same_disjoint_FLOW" to bc.results.map{facts(ops,it)},"kind" to "static_disjoint_run1","current" to  tc.results.map{facts(ops,it)},"omit_new" to  neutral(m,input,i,cl,mode).map{facts(ops,it)},"FLOW" to  fc.results.map{facts(ops,it)},"requests" to  fc.markRequests.map{m.marks.name(it)})
 }
 private fun facts(ops:ApOps,f:Facts):List<Map<String,Any?>> = ops.leaves(f).map{p->mapOf("base" to  p.fact.base.toString(),"path" to  p.fact.path.map{ops.manager.accessors.accessor(it).toString()},"tail" to  p.fact.tail.name,"E" to  p.exclusion.toString(),"mark" to  when(val a=p.fact.mark){is MarkSlot.Concrete->ops.manager.marks.name(a.mark);is MarkSlot.Star->mapOf("FLOW_excludes" to  a.excluded.ids.map{ops.manager.marks.name(TaintMark(it))})},"layer" to  f.layer.name,"protected" to ((f as? TaintTree)?.nonSubsumable!=null))}.toList()
 private fun json(v:Any?):String=when(v){null->"null";is Number,is Boolean->v.toString();is Map<*,*>->v.entries.joinToString(",","{","}"){json(it.key.toString())+":"+json(it.value)};is Iterable<*>->v.joinToString(",","[","]"){json(it)};else->"\""+v.toString().replace("\\","\\\\").replace("\"","\\\"").replace("\n","\\n")+"\""}
}
```

</details>
