# BaseOnly OWASP new-findings investigation

Date: 2026-07-25

## Verdict

The current analyzer reports 5,686 OWASP Benchmark findings, versus 4,112 on
the exact base revision. The 1,574 additions are all false positives:

| Rule | New findings | TP | FP | Reason |
|---|---:|---:|---:|---|
| `cookie-missing-httponly` | 776 | 0 | 776 | The exact cookie passed to `addCookie` has `setHttpOnly(true)` before the sink. |
| `cookie-issecure-false` | 740 | 0 | 740 | The exact cookie passed to `addCookie` has `setSecure(true)` before the sink. |
| `xss-in-servlet-app` | 29 | 0 | 29 | The value is HTML-escaped before the response sink. |
| `response-injection-in-servlet-app` | 29 | 0 | 29 | The same 29 escaped values are reported by the sibling response rule. |
| **Total** | **1,574** | **0** | **1,574** | |

All additions have the same root cause: a cleaning action reaches
`BaseOnlyAccessOps#clear`, but clearing a root semantic mark is deliberately a
no-op in BaseOnly. Tree removes the mark. BaseOnly consequently carries the
sanitized mark forward and reports it at the sink.

This is a forward-analysis precision regression, not a trace-resolution
regression.

## Controlled comparison

The workflow checks out OWASP Benchmark revision
`79b9bd6177e07991a9c11dc19e457c840e229931`.

Three scans used the same portable project and rules:

| Analyzer | AP mode | Findings |
|---|---|---:|
| Exact PR base `049c3cb61c8623f43edd5f65b3db025b392ead9a` | workflow default | 4,112 |
| Current `38f97a2b94995f95cb1b2d7fb07503625d501ee6` | `Tree` | 4,112 |
| Current `38f97a2b94995f95cb1b2d7fb07503625d501ee6` | workflow default, `BaseOnlyField` | 5,686 |

Result identity was compared using rule ID, artifact URI, start line, start
column, and decorated logical name:

- current Tree and base have identical identity sets;
- current BaseOnly has all 4,112 baseline results plus exactly 1,574 additions;
- there are no missing results;
- current Tree and base have the same sorted-identity SHA-256:
  `d3246ea4225b61953f436cf373e5c8f62b0a2a25fa992931b4627fbe38d41f26`.

The current CLI default is `BaseOnlyField` in
`AbstractAnalyzerRunner#apMode`. Therefore the AP mode alone explains the
workflow difference; current rule generation and the other analyzer changes
do not.

The current CI trace statistics are
`total=5686, simple=493, generatedSuccess=5193, generationFailed=0`. The
additional findings are present in forward-analysis storage and resolve
successfully. Trace resolution neither introduces nor filters them.

Local evidence:

- base SARIF:
  `/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/reports-main/report-ifds.sarif`;
- current BaseOnly SARIF:
  `/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/reports-current/report-ifds.sarif`;
- current Tree SARIF:
  `/drive-testcomp/opentaint-go-rules/owasp-ci-investigation/reports-current-tree/report-ifds.sarif`.

## Per-finding classification

### Cookie findings

Each of the 1,516 new cookie results was checked at its exact SARIF sink.
For every result, the variable passed to `HttpServletResponse.addCookie` was
resolved and its preceding statements in the same method were inspected:

- all 776 `cookie-missing-httponly` results have
  `<reportedCookie>.setHttpOnly(true)` before the reported `addCookie`;
- all 740 `cookie-issecure-false` results have
  `<reportedCookie>.setSecure(true)` before the reported `addCookie`.

There are no unproved cookie results.

The OWASP expected category cannot safely classify these individual reports.
A benchmark class may intentionally contain an insecure cookie at one sink and
a separate, correctly configured cookie at another sink. For example,
`BenchmarkTest00087` is an insecure-cookie benchmark overall, but its newly
reported `doGet` cookie calls `setSecure(true)` before its own sink, and its
newly reported `doPost` cookie calls `setHttpOnly(true)` before its own sink.
Both added results are false positives even though another flag at another sink
is intentionally insecure.

Representative complete case: `BenchmarkTest00001#doGet` constructs
`userCookie`, executes:

```java
userCookie.setSecure(true);
userCookie.setHttpOnly(true);
response.addCookie(userCookie);
```

Tree reports neither cookie rule. BaseOnly reports both at `addCookie`. Its
HttpOnly trace contains only:

1. `Cookie` initializer puts `$C` on `userCookie`;
2. `cookie-missing-httponly` sink.

The `setHttpOnly(true)` cleaning step has not changed the fact and consequently
does not appear as a trace transition. The Secure trace behaves identically
with `$COOKIE`.

### XSS and response-injection findings

The two rules report the same 29 benchmark sinks, for 58 false positives. Each
reported value is escaped before reaching the response writer, either directly
or through a local helper:

`00278`, `00286`, `00389`, `00471`, `00474`, `00713`, `00718`, `00726`,
`01048`, `01054`, `01255`, `01339`, `01342`, `01348`, `01351`, `01352`,
`01585`, `01586`, `01595`, `01659`, `01661`, `01924`, `02049`, `02318`,
`02398`, `02401`, `02488`, `02581`, and `02601`.

Representative complete case: `BenchmarkTest00278#doPost` executes:

```java
String bar = org.springframework.web.util.HtmlUtils.htmlEscape(param);
response.getWriter().print(bar);
```

`HtmlUtils.htmlEscape` is explicitly a `pattern-sanitizer` in both
`servlet-xss-html-response-sinks.yaml` and
`servlet-response-injection-sinks.yaml`. Tree reports neither rule. BaseOnly
reports both. The BaseOnly trace says:

> Method "htmlEscape" propagates $UNTRUSTED data from "param" to "bar"

That transition is the direct observable evidence of the error: the configured
sanitizer's `RemoveMark` action failed to remove `$UNTRUSTED`, after which the
ordinary return-value propagation carried the surviving mark to `bar`.

The other 28 cases use the same configured sanitizer family, including
`HtmlUtils.htmlEscape`, Apache `StringEscapeUtils.escapeHtml`, and helper
methods returning their escaped result. Formatting, character-array, and
helper variants do not alter the verdict: the exact value sent to the sink is
the escaped value.

## Exact operation-level root cause

The action pipeline is:

1. Pattern-automata conversion creates a clean action in
   `TaintRuleGenerationCtx#stateCleanMark`, through
   `JavaTaintRuleStrategy#createCleanAction`.
2. `MethodTaintConfigurationResolver#resolve` resolves the serialized clean to
   `RemoveMark`.
3. `JIRTaintCleanActionEvaluator#evaluate(RemoveMark)` calls
   `TaintCleanActionEvaluator#removeFinalFact`.
4. `TaintCleanActionEvaluator#clearPosition` calls
   `FinalFactAp#clearAccessor(mark)`.
5. The manager dispatches that call to either Tree or BaseOnly.

At each failing sanitizer, the relevant state is:

| Item | Value |
|---|---|
| Statement | `cookie.setHttpOnly(true)`, `cookie.setSecure(true)`, or an HTML escape call |
| Fact before | A direct semantic terminal on the sanitized value: `$C`, `$COOKIE`, or `$UNTRUSTED` |
| Operation | `clearAccessor(TaintMarkAccessor(mark))` |
| Tree result | `null` for the bare marked fact: the semantic mark is removed |
| BaseOnly result | The original marked fact, unchanged |
| Expected analysis effect | The sanitized direct mark must not reach the corresponding sink |
| Observed effect | The direct mark survives and produces a false positive |

Tree implements the expected subtraction in `AccessTree#clearAccessor`:
`access.clearChild(accessor.idx)` returns an empty tree and the wrapper returns
`null`.

BaseOnly implements a special case in `BaseOnlyAccessOps#clear`:

```kotlin
if (access.staticIdx == NO_ACCESSOR &&
    access.fieldIdx == NO_ACCESSOR &&
    access.hasSemanticMark
) {
    return access
}
```

The differential unit test
`BaseOnlyTreeDifferentialOperationsTest#explicit Any projects to the implicit structural branch`
pins this exact difference:

```kotlin
assertNull(treeBare.clearAccessor(mark))
assertEquals(baseOnlyBare, baseOnlyBare.clearAccessor(mark))
```

It is therefore not an incidental bug in rule matching, summary application,
or tracing. It is the implemented and tested BaseOnly semantics.

## Why the current BaseOnly rule causes the regression

A compact BaseOnly root semantic fact implicitly combines two languages:

- the zero-length direct terminal, which the sanitizer must remove;
- the same terminal after one or more implicit `Any` structural steps, which a
  conservative field-insensitive representation wants to retain.

After subtracting only the direct terminal, BaseOnly cannot represent the
remaining `Any+ → mark` language. `BaseOnlyAccessOps#clear` returns the least
representable overapproximation, namely the original fact. That cover includes
the path that was explicitly cleaned.

This behavior is consistent with the current BaseOnly specification:
`baseonly-access-domain-spec.md` explicitly permits retaining a cleared path
when exact subtraction is unrepresentable. It is nevertheless incompatible
with the precision required by destructive sanitizer actions. In these OWASP
cases the theoretically surviving implicit-field paths are irrelevant, while
retaining the direct path defeats the sanitizer completely.

The previously proposed alternative—returning `null` for the entire compact
fact—would fix these direct sanitizer cases, but it may underapproximate real
taint below implicit structural fields. The refactoring review records 39
mutation traces that disappeared under that behavior. A correct general fix
therefore needs either:

- a representation for the residual “implicit Any descendants, but no direct
  terminal” state; or
- a cleaning operation that can return a set/split residual instead of forcing
  the result back into one BaseOnly fact.

Until that residual is representable, using BaseOnly as the full-scan domain
necessarily trades sanitizer precision for conservative structural coverage.
A staged strategy—BaseOnly for candidate discovery and Tree for the full
scan—avoids this particular false-positive regression; the controlled
current-Tree run proves that it reproduces the 4,112-result baseline exactly.
