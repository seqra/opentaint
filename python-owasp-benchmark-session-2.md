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

- **Rounds committed (all suite green-or-documented):** sqli (16), cmdi (20), ldapi (29), xxe (28),
  redirect (34), codeinj (53), trustbound (37, **all `@Disabled` — blocked by the store-sink gap inv 28**),
  deserialization (54). Each entry has a hand-written rule + hardcoded ground-truth `@Test`;
  unfixable-by-design FALSE entries are `@Disabled` with a one-line reason. OWASP suite currently
  271 tests: 171 pass / 0 fail / 100 skipped. codeinj: 26 pass + 27 `@Disabled` (inv 27/16/18/19/20);
  trustbound: 0 pass + 37 `@Disabled` (all inv 28); deserialization: 45 pass + 9 `@Disabled` (inv 20/16/18/19/29).
- **Next batch: `pathtraver`** (CWE-22, 168, `open()`/`os.path.join` call sink) — cleaner next step. `xss`
  (89) is entangled with the inv-25/29 char-rebuild gap + `html.escape`/`escape_for_html` sanitizer modeling,
  so prefer pathtraver first. Then xpathi (186). trustbound stays blocked (inv 28). Structural-only
  categories (weakrand/hash/securecookie) deferred.
- **Open engine gaps (escalated, deferred to a later engine phase):**
  - **inv 27** — receiver-position (`This`) `pattern-not` cleaners clean only the `$PIR_SELF` may-alias,
    not the base variable → ~14 codeinj FALSE `@Disabled`. Fix: propagate receiver-cleans to may-aliases.
  - **inv 28** — subscript-STORE (assignment-target) sinks unsupported → all 37 trustbound `@Disabled`.
    Fix: emit + fire a store-sink for subscript/attr assignment targets. Tripwire:
    `PythonRuleEmitTest.subscript-assignment sink emits no sink` (flips when fixed).
  - **inv 25/29** — concrete whole-object taint drops through element/NextIter reads, incl. interprocedural
    char-rebuild helpers (`escape_for_html`) → deser 00605 `@Disabled`; will bite xss. Fix: propagate the
    mark through NextIter.
  - **inv 20** — dynamic `getattr` dispatch FN (ThingFactory). Full traces in the insights log.
- **Author rules STRUCTURALLY — always** (see CARDINAL RULES). Never taint-mode. Thread the source
  metavar into the sink; use `[...]` on collection-accessor sources; unify the guard metavar for
  validator exclusions.
- **Engine/converter fixes committed:** `PIRMethodQFNameReconstructor` MRO attr resolution (inv 7);
  `pattern-not` cleaner handling (`95ad3f916`, retires the "cleaners no-op" claim, inv 23);
  `PythonPatternToActionListConverter.transformAssignmentValue` preserves the subscript element modifier
  so `$A = src(...)[...]` taints `Result[*]` (inv 25).
- **Pass-throughs committed** — base64 (`b64encode`/`b64decode`/`urlsafe_b64decode`) +
  `builtins.bytes.decode` in `config.yaml`.
- **Known unrelated red test:** `PythonSampleBasedTest.allowedSpecificConstant` fails on this branch
  independently of the benchmark work (a `Positive_iter_proc` sample; converter-independent). The OWASP
  suite is unaffected — don't mistake it for a regression.
- Running notes: `python-owasp-benchmark-insights.md` (per-entry FP/FN, pass-throughs, deep
  root-cause writeups). Read it before a hard debug.

## Invariants

### CARDINAL RULES — read these; everything below is symptom-reference

1. 🚫 **NEVER taint-mode. EVERY rule is STRUCTURAL.** No `mode: taint` / `pattern-sources:` /
   `pattern-sinks:` in any `owasp-benchmark-rules/*.yaml`. A structural rule is **not** semgrep syntactic
   matching: the loader (`PythonPatternToActionListConverter`) **lowers it into generated taint
   source+sink rules** run by the full interprocedural engine. So source and sink need **not** share a
   function — the source fires wherever its expression is read (incl. `self.request.form.get` inside a
   wrapper, via declared-type resolution, inv 26) and taint flows interprocedurally (inv 5). Structural is
   strictly as powerful as taint-mode; no case ever needs it. (Historic error: taint-mode was once
   instructed for wrappers citing `01191` — wrong; they pass as structural. Any legacy `mode: taint` file
   is debt to convert, never a template.)
2. **Thread the source metavar into the sink** (inv 24): `$A = <src>(...)` … `<sink>($A)` — the SAME `$A`.
   Different metavars = mere syntactic co-occurrence (masks FNs; FPs safe variants). The sink lowers to a
   `ContainsMark($A)` dataflow check → follows rebinding: put `...` between source and sink, no need to
   name intermediates.
3. **Collection-element sources carry `[...]`** (inv 25): `$A = <src>(...)[...]` for `getlist`/`keys`/
   `values` (taints the element `Result[*]`). Plain scalar `.get(...)` needs none.
4. **Exclude a validated FALSE variant only by unifying source+sink+guard on one `$M`** (inv 23): add
   `pattern-not: … validator($M) … sink($M)`. If safety is a key/index/branch with NO distinguishing
   validator CALL → nothing to unify → `@Disabled`.
5. **VERIFY before you conclude** — never assert "doesn't lower / isn't supported / doesn't fire" from a
   hunch. Dump emitted rules (`PythonRuleEmitTest`, print `rule.taintRules.flatMap { it.rules }`) AND trace
   facts (`System.err.println` in the flow functions → test XML `<system-err>`, inv 10). Hypothesis-as-fact
   is a defect.

### Reference appendix — consult by symptom, don't read cover-to-cover

⚠️ **Capability claims go stale.** Any "engine can't do X / unsupported / broken" may have been FIXED
since — verify (`git log --oneline | grep -i <feature>`, grep the handler) before `@Disabling`. match/case
(4), list.append (14), for-loop NextIter (15) were all wrongly disabled while already working. Numbers are
stable — the `@Disabled` reasons in `OwaspBenchmarkTest.kt` cite them.

1. **Sink precision** — one dangerous arg → `focus-metavariable: $Q` (`$DB.execute($Q,...)`); else taint
   elsewhere in the call (a parameterized query's bound-params tuple) FPs.
2. **Source resolution asymmetry** — module globals resolve by *import name* (`from flask import request`
   → `flask.request`); instance attrs by *declared type*, which erases to `Any` for third-party imports
   under `--ignore-missing-imports` → simple-name (last-segment) fallback.
3. **Last-segment matching** — pass/sink rules match by last segment for simple/unknown callees
   (`MethodTaintConfigurationResolver.matchesName`): config `flask.wrappers.Request.form.get` fires on a
   call resolving only to `get`. Powerful but broad (FP risk).
4. **`match`/`case` SUPPORTED** (was: dropped `MatchStmt`; `ast_serializer.py:456`). Path-insensitive
   across arms (inv 18). Don't `@Disable` for match/case.
5. **Field/alias flow works** — taint set in `self.field` in one method is readable in another.
6. **Unmodeled lib calls drop taint** → surface in `external-methods-without-rules.txt` (by call sites) →
   add a `passThrough` to `config.yaml`. Iterative: fixing one hop reveals the next (base64 chain).
7. **QF-name reconstruction** (`PIRMethodQFNameReconstructor`) resolves `x.attr` on a *known* base via the
   MRO (field/prop → type QN, method → own QN); `Any`-typed field → simple-name fallback. Trace here when a
   call resolves to an unexpected name.
8. **Entry fn name** — `testcode.BenchmarkTest<id>.init$BenchmarkTest<id>_post`.
9. **Classpath cost** — built once/class in `@BeforeAll` (~15s/1230 files); a new `.py` sample rebuilds the
   JAR (~45s). Batch entries into one run.
10. **Engine traces** — gradle captures the test-JVM stderr into `test-results/test/TEST-*.xml`
    `<system-err>` (NOT console) → parse the XML. Add `System.err.println` in `PIRMethodSequentFlowFunction`
    (attr-load) / `PIRMethodCallFlowFunction.applyPassRules` (call).
11. **`config.yaml` is pass-through-only** — never source/sink/cleaner there.
12. **Source facts are `base.![mark]`** — whole-object taint propagates to element reads ONLY on the
    abstract (interprocedural) branch; concrete intraproc `x[i]` used to drop it (`handleAccessorRead` fix
    propagates for subscripts when start accessors are all `TaintMarkAccessor`). **STALE for concrete facts —
    see inv 25.**
13. **cmdi sink** — `subprocess.run($CMD,...)` focus `$CMD`. Command built as
    `argList.append(f"…{bar}"); run(argList)` → sink matches `argList` at its base. Sinks match by
    base-prefix (tolerate tails); intraproc element reads do NOT.
14. **`list.append` propagates** (fixed). Consequence: lists index/flow-insensitive (inv 19) → safe
    `append`+`pop`+`[1]` FPs. Old `@Disabled` list cases (00165/00511) were re-enable candidates.
15. **for-loop NextIter SUPPORTED** (`handleNextIter`, `de73130ad`) — taints the loop var from a tainted
    iterable. Working keys shape `flask.request.form.keys(...)[...]`. Don't `@Disable` for for-loops. (The
    getlist shape is wrong for these — the value that flows is the loop KEY, not `getlist(name)`.)
16. **dict / `configparser` key-insensitive** (single `ElementAccessor`) — a value under one key taints
    reads of every key → safe store-keyB/read-keyA FPs (00350/00736 dict; 00512/00900 configparser). The
    configparser passthrough is required by true seed 00099 → can't tighten → `@Disable` those FALSE.
17. **`request.path` is not a source** (server-controlled route). Model FALSE path entries (01097/01098)
    with a source pattern that simply doesn't match `request.path` → "never-tainted", not "cleaned".
18. **Branching path-insensitive** (ternary + match arms) — engine explores all arms, can't const-fold the
    guard → a FALSE entry whose safe value is const-selected but which also has a tainted arm FPs.
    Unfixable → `@Disabled` (00077 match; 00732/00897 ternary). TRUE tainted-arm entries correctly reach.
19. **Lists index/flow-insensitive** (single `ElementAccessor`, like inv 16) — `append` taints the whole
    list; `lst[i]` any index (even post-`pop`) reads tainted → safe append/pop/const-slot FPs → `@Disabled`
    (00348).
20. **Dynamic `getattr` erases receiver type → user-method unresolved (FN).** `obj = getattr(mod,name)();
    obj.doSomething(param)` — `obj` is `Any` → `doSomething` unresolved, arg→return pass-through lost. No
    simple-name fallback for interproc resolution (`7aba04fa6` resolves to a synthetic *unknown* fn with no
    arg→return → still drops). Escalated (ThingFactory: ldapi 00896, xxe 00462/00541, codeinj
    00343/00422/00601). Reproducer = the `@Disabled` entry.
21. **Config-gated sink via `pattern-inside` sibling-statement match.** XXE (611): the parse is dangerous
    only when a preceding `setFeature(_, True)` enabled entities — unify `$P` across the `setFeature` and the
    parse. Hardened FALSE variants omit `setFeature(_,True)` → the sink never fires regardless of taint (13
    safe-parser xxe pass, incl. 01211 vs byte-identical TRUE 01212). Works in taint `pattern-sinks` (samples
    `RuleWithInside` / `RuleWithRealInsideSequence`).
22. **Structural authoring — see CARDINAL 1–4.** Reference forms in `samples-py/`: `RuleWithPatternsSimple`
    (source→sink), `RuleWithMultiplePatternsUnification` (unification + `pattern-inside return`),
    `RuleWithMultiplePatterns` (two intermediate `mk_type*` calls), `TrickyPatternNot` /
    `ObjectMapperPatternNotFull` / `ObjectMapperPatternNotEllipsis` (`pattern-not` excludes the cleaned
    variant), `RuleWithPatternInside`. `...`/`EllipsisStmt` spans intervening statements (interprocedurally
    too). Thread the metavar through the chain or elide it with `...`; a broken chain just won't match.
23. **Validator exclusion needs source+sink+guard unified on one `$M`** (CARDINAL 4). Naive forms fail (all
    dumpable via `PythonRuleEmitTest`): *sink-only + cleaner* → the cleaner's edges have "no positive
    predicate" (no source mark) and are DROPPED (`RuleWithNotInsidePrefix` only "passes" via a tolerated
    `@TaintRuleFalsePositive`); *split source/sink metavars* → cleaner cleans a mark nobody checks. Working
    form `$M = src(...) … sink($M)` + `pattern-not: … validator($M) … sink($M)` → Source taints `$M`,
    Sink+Cleaner both `ContainsMark($M)` on arg0 (dataflow → follows rebinding through
    configparser/list/match/base64/dict). Cleaners fire on the real engine post `95ad3f916` (retires the
    "cleaners no-op" claim). Debug: `SemgrepLoadTrace` `AUTOMATA_TO_TAINT_RULE` "N edges have no positive
    predicate" = your cleaner got dropped.
24. **Thread source metavar into sink** (CARDINAL 2). Split (`$A = src … redirect($URL)`) = syntactic
    co-occurrence: TRUE passes for the wrong reason (masks taint-drops), a FALSE that redirects a const/other
    value FPs. Same `$A` = `ContainsMark($A)` dataflow, follows rebinding.
25. **Collection-element source carries `[...]`** (CARDINAL 3). inv 12 STALE for concrete facts: a concrete
    whole-object fact drops at the first intraproc `x[i]`/NextIter (`mayReadAccessor(values,ElementAccessor)`
    false — the fact starts `TaintMarkAccessor`, not `ElementAccessor`, and isn't `isAbstract()`). Fix in
    `transformAssignmentValue` merges the value's result modifier into the metavar condition so structural
    `$A = getlist(...)[...]` emits `Result[*]` (was a silent no-op). Regression-locked by `PythonRuleEmitTest`
    "subscript-assignment source…" (+ `python-rules/subscript-assign-source.yaml`).
26. **Interprocedural (wrapper) source is STILL structural** (CARDINAL 1). Write the canonical
    `flask.request.form.get(...)` (`get_form_parameter` wrapper) / `flask.request.args.get(...)`
    (`get_query_parameter`), NOT `$W.get_form_parameter(...)` and NOT taint-mode. The lowered source fires at
    the `self.request.form.get` read inside `helpers.separate_request.request_wrapper` (declared-type
    resolution, not last-segment `get`) and flows interprocedurally to the sink. codeinj wrappers
    00342/00890/00891/00894 pass this way.
27. **Receiver-position (`This`) `pattern-not` cleaner fires but doesn't clean the base variable →
    `@Disabled`** (codeinj `startswith`/`endswith` guards; VERIFIED on 00073 by rule-dump + trace; engine
    gap, not a rule bug). The cleaner IS emitted and DOES fire, but for `bar.startswith(...)` it cleans
    only the `bar.$PIR_SELF` `This` may-alias (no must-alias), while the distinct base fact `bar![$M]`
    survives to the sink. Arg-position cleaners work (inv 23) because the arg maps back to the caller var;
    receiver-position ones can't, and the guard has no arg-position call carrying `bar` → no rule reshape
    fixes it. Reproducer = the 14 `@Disabled` codeinj startswith-guard entries (00073 et al.). Fix
    candidate: propagate receiver-cleans to may-aliases (~14 codeinj + analogues). Full trace in the
    insights log.
28. **Subscript-STORE (assignment-target) sinks are unsupported → whole `trustbound`/CWE-501 category
    `@Disabled`** (VERIFIED, engine gap, ESCALATED). The CWE-501 sink is a session write
    `flask.session[k] = v`, which lowers to a `PIRStoreSubscript` (side-effect inst), NOT a call. A
    structural rule whose sink is `sess[$A] = $V` emits ZERO taint rules: `transformAssignment` rejects a
    non-metavar (subscript/attribute) assignment target (`Assignment_target_not_metavar`), collapsing the
    whole `patterns` block (proven — `PythonRuleEmitTest.subscript-assignment sink emits no sink`,
    emit-count 0). And sinks fire only at calls (`PIRMethodCallFlowFunction.applySinkRules`) / attribute
    reads; `PIRMethodSequentFlowFunction.handleStoreSubscript` propagates taint but does NO sink check. So
    no structural rule can express OR fire on a store-target sink. Fix = converter emits a "store sink" for
    a subscript/attribute-target assignment (check taint on key AND value) + engine checks it at
    `handleStoreSubscript`/`handleStoreSubscript`-analogues + a new sink kind. Reproducer: the 37 `@Disabled`
    trustbound entries + the `PythonRuleEmitTest` probe (`python-rules/subscript-assign-sink.yaml`).
29. **Interprocedural char-rebuild loop drops taint (inv-25 family) → `@Disabled`** (deser 00605,
    `helpers.utils.escape_for_html`). A helper that rebuilds its string arg char-by-char
    (`for c in s: ret += c`) drops taint: `s` (scalar) is base-tainted but `for c in s` NextIter doesn't
    taint `c` (concrete whole-object fact doesn't propagate through element/NextIter read, inv 25). VERIFIED
    on 00605: a call-arg probe (`... escape_for_html($A)` as sink) FIRES → taint reaches the call; the drop
    is inside the body. A `config.yaml` passThrough does NOT override an analyzed user fn (no effect). Fix
    candidate = same as inv 25 (propagate concrete whole-object taint through NextIter).

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
