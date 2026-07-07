# Next session: Python OWASP benchmarking — delegated rounds

You are continuing the **Python OWASP benchmark**. The harness, the seed set, and one engine fix are
already committed (see "Current status"). Your job now is to grow coverage across the remaining
categories **without saturating your own context with debugging transcripts** — so you run as a lean
**orchestrator/reviewer** and delegate each batch's author→run→debug work to a sub-agent via the
`python-owasp-benchmark-round` skill.

## Goal

Grow `OwaspBenchmarkTest` to cover the OWASP Benchmark for Python (1230 entries in
`core/samples/src/main/python/owasp-benchmark/testcode/`), one hand-written semgrep rule per entry,
ground truth hardcoded per `@Test`, raising recall/precision by (1) correct per-entry
source/sink/cleaner rules and (2) pass-through approximations for library methods that drop taint.

## The delegated round loop (how you operate)

You stay lean. **Do not author/debug entries directly in this context.** Instead, per batch:

1. **Pick a batch** — a category (see the table) or an ID range. Start with small taint-flow
   categories (`cmdi` 22, `sqli` remaining, `ldapi` 24, `xxe` 20, `redirect` 24, `codeinj` 35).
2. **Invoke `python-owasp-benchmark-round`** with the batch. It dispatches one sub-agent that does the
   *entire* round in its own context (author rules + `@Test`s → run the batched gradle → triage FN/FP
   → apply simple fixes → document unfixable FP/FN) and returns a **compact report**.
3. **Review the report** — sanity-check pass/fail vs. `expectedresults-0.1.csv`, confirm the suite is
   green-or-documented, skim the fixes (rules / pass-throughs / small engine changes) and the
   escalated hard issues (each ships with a minimized failing reproducer — see below).
4. **Integrate** — commit the round; append any newly-discovered invariant to the list below.
5. **Repeat** for the next batch. Escalated hard engine issues (like the wrapper bug that shaped this
   list) you tackle centrally, with the user, using the minimized reproducers left behind.

Sequential by design: each round sees the previous round's committed fixes, so shared config/engine
fixes accumulate cleanly.

## Current status

- **Seed set committed** — 16 SQLi entries: 14 active (all pass), 2 `@Disabled` (`00192`, `00287` —
  `match`/`case` unsupported, see invariant 4).
- **Engine fix committed** — `PIRMethodQFNameReconstructor` resolves `x.attr` on a known base class
  via the MRO (fixed the `request_wrapper` FN; invariant 7).
- **Pass-throughs committed** — base64 (`b64encode`/`b64decode`) + `builtins.bytes.decode` in
  `config.yaml` (fixed `00454`).
- Running notes: `python-owasp-benchmark-insights.md` (per-entry FP/FN, pass-throughs, deep
  root-cause writeups). Read it before a hard debug.

## Invariants (append-only — future sessions MUST add what they learn here)

Hard-won facts that make debugging fast. This list is a living reference: when a round discovers a new
one, add it.

> ⚠️ **Capability invariants go stale.** Any invariant claiming the engine "can't do X / is unsupported /
> unmodeled / broken / escalated" may have been FIXED on a later commit. Before `@Disabling` an entry on
> such grounds, VERIFY against the current engine: `git log --oneline | grep -i <feature>` and grep the
> relevant handler (e.g. `handleNextIter` in `PIRMethodSequentFlowFunction.kt`). match/case (inv 4),
> `list.append` (inv 14), and for-loop NextIter (inv 15) were all marked unsupported here yet already
> fixed — author the correct rule instead of disabling, then rewrite the invariant.

1. **Sink positional precision.** For a sink where only one arg is dangerous (`$DB.execute($Q, ...)`),
   restrict with `focus-metavariable: $Q`; otherwise taint anywhere in the call (e.g. a parameterized
   query's bound-params tuple) false-positives. This is what keeps the parameterized-safe SQLi cases
   negative.
2. **Source resolution asymmetry.** Module globals resolve by *import name*
   (`from flask import request` → `flask.request`); instance attributes resolve by *declared type*,
   which erases to `Any` for third-party imports under `--ignore-missing-imports` → the callee then
   falls back to **simple-name (last-segment) matching**.
3. **Pass/sink rules match by last segment** for simple/unknown callees
   (`MethodTaintConfigurationResolver.matchesName`) — a config rule `flask.wrappers.Request.form.get`
   fires on a call resolving only to `get`. Powerful, but broad — mind false positives.
4. **`match`/`case` is now SUPPORTED.** (Historic: it used to drop `MatchStmt`.) `ast_serializer`
   serializes `MatchStmt` (ast_serializer.py:456); such functions build and analyze. NOTE the flow is
   **path-insensitive across arms** — see invariant 18. Do NOT `@Disable` for match/case anymore.
5. **Field/alias flow works.** Taint stored in `self.field` in one method is readable in another —
   don't suspect this first when a wrapper/getter drops taint.
6. **Unmodeled library calls drop taint** → they surface in
   `core/build/py-owasp-report/external-methods-without-rules.txt` (sorted by call sites) → add a
   `passThrough` to `config.yaml`. Iterative: fixing one hop reveals the next (e.g. the base64 chain).
7. **QF-name reconstruction** (`PIRMethodQFNameReconstructor`) resolves `x.attr` on a *known* base
   class via the MRO (field/property → its type QN; method → its own QN); an `Any`-typed field yields
   no binding → simple-name fallback. When a call resolves to an unexpected name, trace here.
8. **Entry function name** — `testcode.BenchmarkTest<id>.init$BenchmarkTest<id>_post`.
9. **Classpath cost** — built once per test class in `@BeforeAll` (~15s for 1230 files); adding a new
   `.py` to the owasp-benchmark samples rebuilds the JAR (~45s). Batch entries into one run.
10. **Reading engine traces** — gradle captures the test JVM's stderr into
    `core/build/test-results/test/TEST-*.xml` `<system-err>` (NOT the console) — parse the XML. Add
    targeted `System.err.println` in `PIRMethodSequentFlowFunction` (attr-load path) /
    `PIRMethodCallFlowFunction.applyPassRules` (call path); minimized reproducers localize the drop.
11. **`config.yaml` is pass-through-only** — never add source/sink/cleaner there; those come
    exclusively from the per-entry semgrep rules.
12. **Source facts are `base.![mark]`** (concrete, taint mark directly on base — edges-knowledge §2).
    Intraprocedurally reading an *element* (`x[i]`) or attribute of such a whole-object-tainted value
    used to drop the taint (the outermost accessor is the mark, not `ElementAccessor`). Fixed for
    subscripts in `handleAccessorRead` (`PIRMethodSequentFlowFunction`): if a fact's start accessors
    are all `TaintMarkAccessor` and its base is the container, any element read now propagates the mark
    (`rebase(assignTo)`). This is why the wrapper case (01191) already worked — interprocedural call
    *abstraction* turns the fact abstract, and the abstract branch handled it; the intraprocedural
    concrete path did not.
13. **cmdi sink shape.** `subprocess.run($CMD, ...)` focus `$CMD`. Command is built as
    `argList.append(f"echo {bar}"); subprocess.run(argList)` — the sink matches `argList` at its base.
    Sinks match by base-prefix (tolerate junk tails); intraprocedural element reads do NOT.
14. **`list.append` now propagates (was broken; fixed by "Fix list append rule").** `lst.append(param)`
    now taints the list so `bar = lst[0]`/`lst[1]` reads tainted. Consequence: lists are
    **index/flow-insensitive** (see invariant 19) — a safe `append`+`pop`+`lst[1]` pattern false-positives.
    Previously-`@Disabled` list cases (00165/00511) are candidates to re-enable — verify.
15. **for-loop iteration is now SUPPORTED (was escalated as unmodeled — STALE).** `handleNextIter` in
    `PIRMethodSequentFlowFunction.kt` (commit `de73130ad "Add next iter handling"`) taints the loop var
    from a tainted iterable, so `for name in request.form.keys():` correctly taints `name`. The proven
    working source shape for keys()-iteration is `flask.request.form.keys(...)[...]` (active passing
    cmdi entries 00431/00432; ldapi 00427/00429/00430/01193). **Do NOT `@Disable` for for-loop
    iteration anymore** — this was the same stale-invariant trap that bit match/case (inv 4) and
    list.append (inv 14). Note the getlist shape is wrong for these entries: `getlist(name)` only
    appears in the `if` guard and never reaches the sink; the value that flows is the loop KEY `name`.
16. **dict / `configparser` are key-insensitive** (single `ElementAccessor` / `.Element`): a value
    stored under one key taints reads of *every* key. So the safe "store keyB(param), read keyA(const)"
    variant false-positives (00350/00736 dict; 00512/00900 configparser). The configparser passthrough
    is required by the true seed 00099, so this can't be tightened — mark such FALSE entries `@Disabled`.
17. **`request.path` is not a taint source** (server-controlled route). Model the FALSE path-based
    entries (01097/01098) by giving the rule a source pattern that simply doesn't match `request.path`
    (e.g. `flask.request.form.get(...)`), so nothing is tainted — "never-tainted", not "cleaned".
18. **Branching is path-insensitive (ternary + match arms) → safe-arm FP.** `bar = SAFE if <const-true>
    else param` and `match const: case X: bar=SAFE; case _: bar=param` both taint `bar` because the
    engine explores *all* arms and can't constant-fold the discriminator. So a FALSE entry whose safe
    value is selected by a constant guard, but which also has a tainted arm, false-positives. Unfixable
    without path-sensitivity/const-folding → `@Disabled` (ldapi 00077 match, 00732/00897 ternary).
    Note the mirror: TRUE match/ternary entries with a tainted arm correctly reach (00266/00604/etc.).
19. **Lists are index/flow-insensitive** (single `ElementAccessor`, like dict inv 16). `lst.append(param)`
    taints the whole list; `bar = lst[i]` (any index, even after `pop`) reads tainted. So the safe
    "append param, pop, read a constant slot" pattern false-positives → `@Disabled` (ldapi 00348).
20. **Dynamic `getattr` construction erases the receiver type → user-method call unresolved (FN).**
    `obj = getattr(mod, name)(); obj.doSomething(param)` — `obj` is `Any`, so `doSomething` resolves to no
    concrete class and its arg→return pass-through is lost; taint drops. Interprocedural resolution does
    NOT fall back to simple-name matching the way config pass/sink rules do (inv 3). Escalated
    (ldapi 00896, `ThingFactory`); reproducer = the `@Disabled` OWASP entry itself.

## Category → sink / CWE reference

| category | CWE | typical sink pattern |
|---|---|---|
| sqli | 89 | `$DB.execute($Q, ...)` (focus `$Q`) |
| cmdi | 78 | `os.system($C)`, `subprocess.$F(...)` |
| pathtraver | 22 | `open($P, ...)`, `os.path.join(...)` into open |
| xss | 79 | `render_template_string($S)`, response write |
| xpathi | 643 | `$T.xpath($Q)`, `etree...find($Q)` |
| ldapi | 90 | ldap `search*($FILTER, ...)` |
| xxe | 611 | `etree.parse(...)` / resolve-entities on |
| codeinj | 94 | `eval($X)`, `exec($X)` |
| deserialization | 502 | `pickle.loads($X)`, `yaml.load($X)` |
| trustbound | 501 | session write |
| securecookie | 614 | `set_cookie(...)` without secure |
| weakrand | 330 | `random.*` used for security |
| hash | 328 | `hashlib.md5/sha1(...)` |
| redirect | 601 | `redirect($URL)` |

`weakrand` / `hash` / `securecookie` are **structural** (no taint flow) — model with semgrep
*structural* rules (see `core/opentaint-python-querylang/samples-py/` examples), not taint flow.
Defer to a later round; discuss before investing.

## Key files

- Harness: `core/src/test/kotlin/org/opentaint/python/sast/dataflow/OwaspBenchmarkTest.kt`,
  base `AnalysisTest.kt`.
- Rules: `core/src/test/resources/owasp-benchmark-rules/BenchmarkTest<id>.yaml`
  (example `BenchmarkTest00099.yaml`; known-good semgrep forms in
  `core/opentaint-python-querylang/src/test/resources/python-rules/` and `samples-py/`).
- Pass-through config (pass-only): `core/opentaint-config/python-config/config/python-config/config.yaml`.
- Reproducers for escalated issues: `core/opentaint-python-querylang/samples-py/<Name>/` +
  `PythonSampleBasedTest`.
- Insights log: `python-owasp-benchmark-insights.md`. Tracker: `core/build/py-owasp-report/`.
- Ground truth: OWASP `expectedresults-0.1.csv`
  (`https://github.com/OWASP-Benchmark/BenchmarkPython/blob/main/expectedresults-0.1.csv`;
  columns `test name, category, real vulnerability, cwe`).

## Run command

```bash
./core/gradlew -p core :test --tests "org.opentaint.python.sast.dataflow.OwaspBenchmarkTest"
```

## Open considerations

- **Speed:** rounds are sequential by design (clean context + no shared-state conflicts). Only if
  wall-clock becomes the bottleneck, consider running non-conflicting categories as parallel
  sub-agents — but that reintroduces config/engine merge conflicts, so revisit only if needed.
- **Deferred design question:** whether request-accessor `.form`/`.get` entries belong as
  `config.yaml` pass-throughs or as source rules.
