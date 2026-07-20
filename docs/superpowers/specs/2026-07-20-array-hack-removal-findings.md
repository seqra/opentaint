# Result-array hack removal — findings & recommendation

**Date:** 2026-07-20 · Branch `misonijnik/star-operator` · BenchmarkJava/OWASP

## TL;DR

The "result array hack" is **not a single removable hack**. Only one of its three parts is
removable-ish; the other is the **varargs / element-taint-to-sink mechanism** and is load-bearing.
**No removal variant is finding-neutral** against the true baseline (3737 traces). Recommend
**not** removing `arrayElementConditionReaders`; the `resolveArrayPosition` removal costs 10 OWASP
true positives; the converter `$X[...]`→star routing is a genuine, keepable improvement on its own.

## Baseline note

CI pins `EXPECTED_TRACES=3619`, but the current branch actually produces **3737**
(`TraceGenerationStats(total=3737, simple=503, generatedSuccess=3234)`). The 3619 is stale
pre-existing drift unrelated to this work. All deltas below are vs. the real 3737 baseline.

## The three pieces

1. **`MethodTaintConfigurationResolver.resolveArrayPosition`** (config side) — duplicates a
   source-action / `ContainsMark[OnAnyField]` position whose declared type `isArray` or
   `== java.lang.Object` into `{pos, pos[*]}`. This *is* the removable "hackResultArray" the
   `PatternToActionListConverter.kt:188` comment references.
2. **`JIRMethodCallTaintUtil.arrayElementConditionReaders`** (JVM runtime) + its Go twin
   **`GoMethodCallTaintUtil.patchSinkConditionFactReader`** — wrap a sink condition reader so
   element taint `arg[*]` satisfies a whole-arg sink condition. **This is the VARARGS mechanism,**
   not a hack: Go `log.Printf($FMT,$X)`, `fmt.Fprint(w,$A)`, `exec.Command(name,...)`,
   `filepath.Join(...string)`, and Java `String.format(String,Object[])` all bind the metavar to a
   variadic slice whose tainted value is a slice *element* (`arg[*]`); this reader is what lets it
   reach the whole-param sink.
3. **`PatternToActionListConverter.kt:180-193`** — drops `$X[...]` array-index in patterns.
   Changed to **force the metavar starred** (`obj.copy(star = true)`), routing `$X[...]` through
   the any-field machinery. This *works* and recovers rule-side array access — `issue84`
   (`$VALUES[...]`) passes. It **cannot** recover cases where only the *code* has the element
   access and the *rule* matches the whole param (there is no `[...]` in the rule to star).

## Measured results

| Config | OWASP total | Δ | Go querylang | Java querylang |
|---|---|---|---|---|
| Baseline | **3737** | — | pass | pass |
| Split: remove #1 only, keep #2, apply #3 | **3727** | −10 | **all pass** | `ExampleTest.test array example` fails |
| Full: remove #1 + #2 + #3 (star routing) | **3574** | −163 | **10 fail** (variadic) | `ExampleTest` fails |

Per-rule losses (full removal): `xss-in-servlet-app` −63, `response-injection-in-servlet-app` −63,
`sql-injection` −27, `trust-boundary-violation` −10. The split loses only the `trust-boundary-violation`
−10 (the config-side source `[*]` twin, e.g. a `String[]`/`Object[]` source whose element is read).

Go tests broken by removing #2 (all variadic/element flows): `loginj01-04/07/08`, `path02QueryJoinOpenfile`,
`cmdStringShellSink`, `shellExecArgConstraint`, `typedArgSink`.

Java case broken by removing #1: `ArrayExample.PositiveEpElementGuessed` / `PositiveSrcElementGuessed`
— code passes `data[0]` to a whole-array sink `otherElementSink($PARAM)`; needed the source-side
`[*]` twin. (`issue84` still passes via the star routing.)

## Why the star operator does not subsume this

`$*VAR` gives whole-object → any-field taint, which *does* subsume `[*]` when the **rule** names the
array access (`$X[...]` → forced star). It does **nothing** for the two dominant real-world cases:
- **varargs sinks** — the rule matches the whole variadic param `$X`; the element access is implicit
  in the callee's `...`/`Object[]` ABI, never written in the rule.
- **code-side element reads to whole-array sinks** — `sink(data[0])` where the rule is `sink($PARAM)`.

Both require element↔whole flattening at analysis time, which is exactly what `arrayElementConditionReaders`
provides.

## Root-cause investigation (every lost trace inspected)

**The −10 (resolveArrayPosition) are array-SOURCE → element-read TPs.** All 10 lost
`trust-boundary-violation` traces (BenchmarkTest 00754/00755/00756/00757/00758/01619/02523/02524/02526/02527)
are the identical shape:
```java
String[] values = request.getParameterValues("...");   // String[] SOURCE
String param;
if (values != null && values.length > 0) param = values[0];   // concrete element read
... request.getSession().putValue("userid", param);   // trust-boundary sink
```
`getParameterValues()` returns a tainted `String[]`; `resolveArrayPosition` taints `Result[*]` so the
concrete `values[0]` read inherits it. Remove it → `values[0]` is clean → FN. These are **genuine
true positives** and the `getParameterValues()[0]` idiom is ubiquitous.

**The −153 (arrayElementConditionReaders) are vararg-SINK TPs.** Spot-checked:
- `sql-injection` BenchmarkTest00104 (`getCookies()` array → element → `JDBCtemplate.batchUpdate(sql)`),
  BenchmarkTest00434 (`getParameter()` scalar → `batchUpdate(sql)`). `JdbcTemplate.batchUpdate(String... sql)`
  is a **vararg**; `sql` is passed as element `arg[*]`.
- `xss-in-servlet-app` BenchmarkTest00147 (`getHeader("Referer")` → List → `response.getWriter().format(
  "%1$s %2$s", obj)` with `Object[] obj = {"a", bar}`). `PrintWriter.format(String, Object...)` is a
  **vararg**; the taint is `obj[1]`.
The split (readers kept) lost **zero** sqli/xss/response-injection — proving those 153 are entirely the
vararg-sink readers, not `resolveArrayPosition`. Genuine true positives (real SQLi / XSS).

**Conclusion of the investigation:** neither piece is dead or redundant. Both implement the
array/vararg element-taint machinery for extremely common real code. The `hackResultArray` comment is a
misnomer — it is load-bearing, not a hack. The star operator cannot subsume either, because both are
*code-side* element/vararg mechanics with no `$X[...]` in the rule to star.

## RESOLUTION (2026-07-20): star-model replacement, finding-neutral

The runtime element-reader — the varargs/element-taint mechanism (#2) — **can** be deleted and
replaced by the star operator's any-field sink CONDITION, finding-neutral on OWASP (exactly 3737,
zero per-rule delta) and all Java + Go tests green.

**Mechanism facts that made it work:**
- Production unroll (`TaintAnalyzer.kt:67`) unrolls `ElementAccessor→true` AND `FieldAccessor→true`
  (except `<rule-storage>`).
- `ContainsMarkOnAnyField` → `evalContainsMarkOnAnyField` → `readAnyPosition` is a **recursive,
  any-depth, search-based** match over the fact's existing accessor tree (field + element edges). It
  matches a concrete `arg[*]` element fact **directly**, and — being search-based — does **not** need
  the unroll strategy, so it is harness-safe under `AnyAccessorDisabled`.
- The source-side any-field *assign* (`pos.AnyFieldAccessor`) DOES need the unroll to reach a concrete
  element read, so it breaks the `AnyAccessorDisabled` querylang harness (Step B: 13 FNs). Kept the
  source-side as concrete `[*]` instead.

**Change landed:**
- `MethodTaintConfigurationResolver`: `SerializedCondition.ContainsMark` on array/`Object`-typed
  positions also emits `ContainsMarkOnAnyField(pos)` (drops the redundant `[*]` condition twin);
  source **actions** keep concrete `[*]`.
- Deleted JVM `arrayElementConditionReaders` + `patchSinkConditionFactReader` override +
  `callArgumentMayBeArray`/`mayBeArray`.
- Go: `GoConditionResolver.ContainsMark` also emits `GoRuleCondition.ContainsMarkOnAnyAccessor`;
  deleted the Go `patchSinkConditionFactReader` reader.
- Kept the converter `$X[...]`→star routing (recovers `issue84`).
- Kept `resolveArrayPosition` for source actions (the array-source element model; removing it loses
  10 `trust-boundary` TPs — the `getParameterValues()[0]` pattern).

**Measured (BenchmarkJava):** Step A (any-field sink cond + JVM reader removed) = 3737. Step B (also
any-field source assign) = 3737 on OWASP but breaks 13 querylang tests (harness AnyAccessorDisabled).
Step A.5 (final: any-field sink cond, concrete `[*]` source, no reader) = **3737, zero delta, all
querylang green**. Go full suite green (10 variadic tests recovered, no new FPs).

## Recommendation (superseded by the resolution above)

1. **Keep** `arrayElementConditionReaders` (JVM), its Go twin, and `callArgumentMayBeArray` — they are
   the varargs mechanism (−153 traces, 10 Go tests if removed).
2. **Keep** the converter `$X[...]`→star routing (#3) as a standalone improvement — it makes rule-side
   array access explicit via the star operator and is independent of #1/#2.
3. **`resolveArrayPosition` (#1)** removal is *not* finding-neutral (−10 OWASP trust-boundary true
   positives + 2 querylang cases). Remove only if those 10 are judged acceptable / false positives;
   otherwise keep. No "poorly designed fix" was attempted to recover them (would need real engine work
   to taint code-side element reads from array-typed sources).

**Status:** Sub-project A (star tests) committed & green. Sub-project B code changes are **uncommitted**,
pending the user's decision on the above.
