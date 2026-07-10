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
    **Confirmed still failing** in the xxe round (00462/00541, same `ThingFactory`) despite the
    `7aba04fa6` simple-name resolver fallback — that fallback resolves to a synthetic *unknown*
    function with no arg→return modeling, so taint still drops. Not stale.
21. **Config-gated sink (parser hardening) via `pattern-inside` sibling-statement match.** When a sink
    is dangerous only if a *sibling* config call enabled it, gate it with a statement-sequence
    `pattern-inside`. XXE (CWE-611): the parse is dangerous only when the parser has external entities
    on. Model with the parser var `$P` unified across a preceding `setFeature(_, True)` and the parse:
    ```yaml
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              $P.setFeature($F, True)
              ...
          - pattern: "xml.dom.minidom.parseString($DOC, $P)"
          - focus-metavariable: $DOC
    ```
    Hardened FALSE variants omit `setFeature(_, True)` (all features off by default) → the sink never
    fires **regardless of whether tainted data reaches the parse** — this is how 13 safe-parser xxe
    FALSE entries pass, incl. 01211 (byte-identical dataflow to TRUE 01212, differing *only* in that
    line). `pattern-inside` in taint `pattern-sinks` works (see sample `RuleWithInside`;
    statement-sequence form in `RuleWithRealInsideSequence`).
22. **Structural (search-mode) rules are supported — PREFER them for OWASP entries.** A rule can be a
    pure *structural* semgrep match instead of a taint rule: top-level `patterns:` holding
    `pattern` / `pattern-not` / `pattern-inside` / `pattern-not-inside` blocks (NO `pattern-sources` /
    `pattern-sinks`, NO `mode: taint`). Metavariables (`$A`, `$SOURCE`, `$SINK`) **unify across
    blocks**, `...` matches intervening statements (statement-sequence), `pattern-inside` /
    `pattern-not-inside` scope to the enclosing context, and `focus-metavariable` narrows the reported
    node. Because each OWASP entry is one self-contained function with a **fixed syntactic shape**, a
    structural rule that matches the source→sink shape (threading unification through every
    intermediate assignment) and **excludes the safe/validated variant** with `pattern-not` /
    `pattern-not-inside` is usually MORE reliable than a taint rule: it sidesteps the engine's
    path-insensitivity and index/flow-insensitivity (inv 16/18/19) that otherwise force `@Disabled` on
    many FALSE entries. E.g. redirect FALSE 00069 is "safe" only because of a `urllib.parse.urlparse` +
    netloc/scheme guard the taint engine can't model as a sanitizer — but a structural
    `pattern-not-inside` that matches the guard excludes it cleanly.
    **ALWAYS use structural rules — every OWASP entry can be expressed as one.** Do NOT fall back to
    taint-mode (`pattern-sources`/`pattern-sinks`) syntax. **Why it's not a fallback:** a structural
    rule is *itself lowered to a taint rule* by `PythonPatternToActionListConverter` (the first
    binding becomes the source, the sink call the sink; `...`/`EllipsisStmt` spans intervening
    statements) — so the resulting taint dataflow **tracks flow through intermediate calls AND field
    reads/writes just like a hand-written taint rule**. Intermediate calls/field ops on the source→sink
    path are therefore NOT a reason to switch modes: put a `...` between the source binding and the
    sink and the lowered rule follows the flow across them (interprocedurally too). This was the trap
    the first structural round fell into — the sub-agent saw intermediate calls and reverted to taint
    mode; that is always unnecessary. Reference forms in
    `core/opentaint-python-querylang/samples-py/`: `RuleWithPatternsSimple` (source→sink),
    `RuleWithMultiplePatternsUnification` (unification + `pattern-inside return`),
    `RuleWithMultiplePatterns` (source→sink through two intermediate `mk_type*` calls — the exact
    "intermediate calls" shape), `TrickyPatternNot` / `ObjectMapperPatternNotFull` (`pattern-not`
    excludes the cleaned variant), `RuleWithPatternInside` (`pattern-inside` source scope). Caveat:
    metavariable unification must thread through the binding chain — either name each intermediate
    binding and unify it (`$V2 = f($A); ... g($V2)`) or elide the chain with `...` between the source
    binding and the sink; a broken chain (metavar that never re-appears) just won't match.
    **CORRECTION (redirect round):** the claim above that a `pattern-not-inside` matching a validator
    "excludes 00069 cleanly" was NEVER empirically true as written — see invariant 23 for the exact
    working form. A `pattern-not` / `pattern-not-inside` only excludes if it clears **the same taint
    mark the sink checks**, which requires the guard metavar to be unified with the source+sink metavar.
23. **A validator/sanitizer exclusion (`pattern-not` / `pattern-not-inside`) works ONLY when source,
    sink, AND the excluded guard call are unified on ONE metavar** — the ObjectMapperPatternNotEllipsis
    shape. Discovered debugging redirect FALSE guard entries (urlparse+netloc/scheme validators).
    - **Why the naive forms silently fail (all verified by dumping emitted rules via `PythonRuleEmitTest`):**
      - *Sink-only + cleaner* (`pattern: sink($X)` + `pattern-not-inside: clean($X) ...`, i.e. no source):
        emits **just a bare `NumberOfArgs` sink, NO cleaner** — the cleaner's automata edges have "no
        positive predicate" (no taint mark exists without a source) and are dropped. `RuleWithNotInsidePrefix`
        (the canonical sample for this shape) only *appears* to pass because its Negative is decorated
        `@TaintRuleFalsePositive` (a **tolerated** FP), not because the cleaner fires. Do not trust it.
      - *Split source/sink metavars* (`$A = src() ... sink($URL)` + `pattern-not: ... clean($URL) ... sink($URL)`):
        the source taints a canonical mark `_<S>_` and the sink checks `_<S>_`, but the cleaner cleans a
        **different** mark `$URL` → the cleaner removes a mark nobody checks → FP persists.
    - **The working form (unify everything on `$M`):**
      ```yaml
      patterns:
        - pattern: |
            $M = <request-source>(...)
            ...
            sink($M)
        - pattern-not: |
            ...
            validator($M)
            ...
            sink($M)
      ```
      Emits: Source taints mark `$M`; Sink checks `ContainsMark($M, arg0)`; Cleaner (validator) checks
      `ContainsMark($M, arg0)` and cleans it — **all the same mark id `$M`**, so the cleaner removes
      exactly what the sink checks. Crucially, sink/cleaner are **dataflow `ContainsMark` checks on
      arg0, NOT syntactic metavar matches** — so even when the request value is **rebound** before the
      sink (`param → configparser/list/match/base64/dict → bar; validator(bar); sink(bar)`), the `$M`
      mark propagates by dataflow to `bar`, the validator cleans it there, and the sink sees it clean.
      This made all 9 urlparse-guarded redirect FALSE entries pass — direct (01209) and rebinding
      (00069/00151/00419/00420/00598/00815/00816/00983) alike.
    - **Cleaners are NOT a general no-op** (retires the stale `reference_cleaner_mark_abstraction` claim
      for this engine): `ObjectMapperPatternNotFull`, `ObjectMapperPatternNotEllipsis`, and the unified-`$M`
      OWASP rules all clean correctly on the real engine (post commit `95ad3f916` "Fix pattern-not handling").
    - **When there is NO distinguishing validator CALL** (safety comes purely from a key/index/branch the
      engine can't fold — configparser/dict key-insensitivity inv 16, list index-insensitivity inv 19,
      const ternary/match arm inv 18), there is nothing to unify a cleaner against → still `@Disabled`.
    - **Debugging tool:** to see what a structural rule *actually* lowers to, add a throwaway test to
      `PythonRuleEmitTest` calling the loader and printing `rule.taintRules.flatMap { it.rules }`
      (Source `taint`, Sink `condition`, Cleaner `cleans`+`condition`). The `SemgrepLoadTrace` also
      surfaces `AUTOMATA_TO_TAINT_RULE` warnings like "N automata edges have no positive predicate and
      were removed" — that message means your cleaner got dropped for lack of a source mark. Fast
      (querylang module only, no PIR build). Remove the throwaway test before finishing.
24. **The source metavar MUST thread into the sink — this is what models the data flow. (THE #1
    structural-rule rule.)** A shape like
    ```yaml
    - pattern: |
        $A = flask.request.form.get(...)
        ...
        flask.redirect($URL)          # ← WRONG: $URL is a different, unbound metavar
    ```
    does **NOT** model taint flow. `$A` (source result) and `$URL` (sink arg) are distinct metavars, so
    this lowers to a pure **syntactic co-occurrence**: "a source call is assigned somewhere AND a
    `redirect(anything)` call occurs somewhere" — the source's value need not reach the sink at all.
    Consequences: a TRUE entry passes for the WRONG reason (masks any taint-drop on the real path — the
    rule fires regardless), and a FALSE entry that calls the source but redirects a *constant/other*
    value FALSE-POSITIVES. Correct form unifies the metavar end-to-end:
    ```yaml
    - pattern: |
        $A = flask.request.form.get(...)
        ...
        flask.redirect($A)            # ← same $A: lowers to ContainsMark($A) dataflow check on the sink arg
    ```
    Because the sink becomes a **dataflow** `ContainsMark($A)` check (not a syntactic match, inv 23), it
    correctly follows rebinding (`param=source(); ...; bar=f(param); redirect(bar)` still fires) — you do
    NOT need to name every intermediate binding, just bind the source to `$A` and use `$A` at the sink
    with `...` between. Same principle for a `focus`/multi-arg sink: the tainted metavar in the sink
    pattern must be the one the source bound. (The first redirect round shipped the split-metavar shape
    for all plain rules — passing by co-occurrence, not flow — and was corrected in a follow-up.)
25. **A collection-element source MUST carry the `[...]` subscript so it taints the ELEMENT, not the
    whole collection — AND the structural `$A = expr[...]` assignment now preserves that element
    modifier (engine fix this round).** Two coupled facts, discovered fixing the 6 redirect TRUE
    entries that FN'd after the inv-24 metavar unification (00258/00418/00596/00654/00655/00814):
    - **inv 12 is STALE for concrete facts.** A concrete whole-object source fact `values.![mark]`
      does NOT propagate through an intraprocedural element read (`param = values[0]`) or a for-loop
      `NextIter` (`for name in request.form.keys()`). `mayReadAccessor(values, ElementAccessor)`
      (`PIRFlowFunctionUtils`) is **false** — the fact starts with a `TaintMarkAccessor`, not
      `ElementAccessor`, and a concrete source fact is not `isAbstract()`. Inv 12's whole→element
      propagation only exists on the **abstract** branch (interprocedural call-abstraction, the `.*`
      tail), NOT the concrete intraprocedural path. So a source that taints the *whole* collection
      drops at the very first `x[i]` / loop-iteration read on that path.
    - **The fix: taint the element directly.** A source pattern `flask.request.form.getlist(...)[...]`
      (bare, taint-mode) taints `Result[*]` (the element), and reading `values[0]` extracts it cleanly
      via `startsWithAccessor(ElementAccessor)`. This is why the cmdi/ldapi taint-mode keys/getlist
      entries always used the `[...]` shape (insights "add the subscript for collection accessors").
    - **The structural trap that caused the FNs:** in a STRUCTURAL rule the source is bound by an
      assignment `$A = flask.request.form.getlist(...)[...]`, and `transformAssignmentValue`'s
      `setResultCondition(mkAnd(conditions))` **overwrote** the subscript's element modifier with just
      `$A` → the source tainted the *whole* `Result`, identical to the no-`[...]` form (verified by
      dumping emitted rules: both `getlist(...)` and `getlist(...)[...]` → `taint=[BaseOnly(Result)]`).
      Then the concrete whole-object taint dropped at the element read/NextIter per the bullet above.
      **Fix landed in `PythonPatternToActionListConverter.transformAssignmentValue`:** merge the value's
      existing result modifier into the metavar condition (`conditions + last.result`) so
      `$A = getlist(...)[...]` now emits `taint=[WithModifiers(Result,[ArrayElement])]` = `Result[*]`,
      matching the bare taint-mode subscript source. Regression-locked by
      `PythonRuleEmitTest.subscript-assignment source binds the metavar to the result element`
      (+ resource `python-rules/subscript-assign-source.yaml`).
    - **Consequence for authoring:** for any collection-accessor source in a STRUCTURAL rule
      (`getlist`/`keys`/`values`/`getlist`-view), write `$A = <source>(...)[...]` (with `[...]`). The
      `[...]` is now load-bearing (was a silent no-op before this fix). Plain scalar sources
      (`.get(...)`) need no `[...]`. This also made the two keys-source FALSE entries 00419/00420 pass
      for the RIGHT reason: previously their taint dropped at NextIter (masking); now it flows and the
      unified-`$M` urlparse cleaner (inv 23) removes it.

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
