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

- **Branch:** this work now lives on **`saloed/python-support`**. The `saloed/python-owasp-getlist`
  branch and its worktree were retired after folding all benchmark commits into python-support. **Start the
  next session in a fresh worktree off `saloed/python-support`.**
- **Rounds committed (all suite green-or-documented):** sqli (16), cmdi (20), ldapi (29), xxe (28),
  redirect (34), codeinj (53), trustbound (37, all `@Disabled` — store-sink gap inv 28),
  deserialization (54), **pathtraver COMPLETE (168)**, **xpathi COMPLETE (186)**,
  **xss batch 1 (40, all `@Disabled` — return-value-sink gap inv 35)**, **securecookie COMPLETE (39, inv 36)**,
  **hash COMPLETE (151, inv 37)**, **weakrand COMPLETE (326, inv 38)**. **All 14 OWASP categories are now
  authored: 1181 of 1230 entries have a rule + ground-truth `@Test`;** the 49 uncovered are the HELD xss
  entries — deliberately NOT stubbed (all doomed by inv 35 until the return-sink lands). OWASP suite
  **1181 tests: 775 pass / 0 fail / 406 skipped**. The 406 skipped are `@Disabled`-with-verified-reason:
  xss 89 + trustbound 37 (blocked sink-kind gaps inv 35/28); ~113 weakrand SystemRandom (inv 38); and the
  approximation-limited pathtraver/xpathi FPs+FNs (inv 16/18/19/20/23/27/34). The three structural no-flow
  categories use the **crutch-free BARE STRUCTURAL SINK recipe** (a structural sink fires on the call match
  alone — no source, no `ContainsMark`): securecookie (bare `set_cookie(..., secure=False, ...)` sink), hash
  (`pattern-either` of bare `hashlib.md5(...)`/`hashlib.new('md5')` sinks), weakrand (`pattern-either` of bare
  `random.<fn>(...)` sinks) — POSITIVE const-compares where needed, never `pattern-not` cleaners (avoids inv 27).
  The former self-source/downstream-use crutches (make_response, `.update`, `str(...)`) were REMOVED.
- **Next batch: NONE — authoring is DONE. Only the ENGINE PHASE remains** (tackle centrally with the user;
  each has a reproducer/tripwire). Reactivating the 406 skipped is now pure engine work:
  **inv 35** return-value-sink → unblocks xss (89); **inv 28** subscript-store-sink → unblocks trustbound (37);
  **inv 38** resolve `random.SystemRandom()` return type so `.<fn>()` gets a qualified name instead of a
  last-segment-colliding `PIRSimpleNameUnknownFunction` → reactivates ~113 weakrand FALSE (inv-7 QN-resolution
  improvement, likely small); **inv 27** propagate receiver-cleans to may-aliases → ~14 codeinj + the xpathi
  apostrophe-escape FPs. This branch: `owasp-pathtraver-b2-work` (off `saloed/python-support` tip
  `1a5a8ac48`); worktree `/home/pvl/folder/projects/explyt/opentaint-owasp-pt2`. Untracked
  `core/opentaint-sast-test-util` must be copied into any fresh worktree off this branch for gradle to configure.
- **RESOLVED this session:** **inv 29** (char-rebuild NextIter drop) — per-entry workaround: deepen the
  collection source one `[...]` (`getlist(...)[...][...]` → `Result[*][*]`) so char-level taint survives;
  per-entry SAFE, NEVER where the char-rebuild is a real sanitizer (xss). **inv 31** (read_text
  "Entry point not found") — engine fix `a4d733729` (`ClosureAnalyzer` treated unresolved free names as
  closure captures); the 6 read_text entries now pass.
- **Open engine gaps (escalated, deferred to a later engine phase; each has a reproducer/tripwire):**
  - **inv 35** (highest leverage) — return-value sinks unsupported → all 89 xss `@Disabled`/held.
    `return $A` lowers to a `Kind.MethodExit` accept-edge that `PythonTaintRuleGeneration.emitPythonTaintRules`
    rejects (`error("Non method call sinks are not supported yet")`) → 0 sinks. Fix: emit + fire a
    return-value sink (ContainsMark on the `Result`/returned position, checked at method-exit). Tripwire:
    `PythonRuleEmitTest.return-value sink emits no sink` + `python-rules/return-sink.yaml`. Sibling of inv 28.
  - **inv 28** — subscript-STORE sinks unsupported → all 37 trustbound `@Disabled`.
    Fix: emit + fire a store-sink for subscript/attr targets. Tripwire:
    `PythonRuleEmitTest.subscript-assignment sink emits no sink`.
  - **inv 34 → inv 27** — the xpathi apostrophe-escape `str.replace("'",…)` FP is NOT a standalone gap: it's
    an **inv 27** instance. `bar.replace(...)` is receiver-position, so the sanitizing cleaner can't clean the
    base `bar` (only the `$PIR_SELF` may-alias); the `copy.replace` passThrough is merely the propagation path.
    Fixing inv 27 (propagate receiver-cleans to may-aliases) covers these too. (`io.StringIO` half is FIXED —
    see Pass-throughs; no longer a gap.)
  - **inv 27** — receiver-position (`This`) cleaners clean only the `$PIR_SELF` may-alias → ~14 codeinj
    FALSE `@Disabled`. Fix: propagate receiver-cleans to may-aliases.
  - **inv 25/29** — a proper NextIter propagation fix would remove the manual `[...]` workaround + help xss.
  - **inv 20** — dynamic `getattr` dispatch FN (ThingFactory).
  - **Category-level (pathtraver)** — FALSE half needs path-sanitizer modeling (`'../' in bar`,
    `str(p).startswith` guards aren't unifiable cleaners) → many `@Disabled` FPs.
- **Author rules STRUCTURALLY — always** (see CARDINAL RULES). Never taint-mode. Thread the source
  metavar into the sink; use `[...]` on collection-accessor sources; unify the guard metavar for
  validator exclusions.
- **Engine/converter fixes committed:** `PIRMethodQFNameReconstructor` MRO attr resolution (inv 7);
  `pattern-not` cleaner handling (`95ad3f916`, retires the "cleaners no-op" claim, inv 23);
  `PythonPatternToActionListConverter.transformAssignmentValue` preserves the subscript element modifier
  so `$A = src(...)[...]` taints `Result[*]` (inv 25).
- **Pass-throughs committed** — base64 (`b64encode`/`b64decode`/`urlsafe_b64decode`) +
  `builtins.bytes.decode`; **`io.StringIO.write` (`arg(0)`/`kwarg(s)`→`this`) + `io.StringIO.getvalue`
  (`this`→`result`)** (write-into-object/read-back, mirrors `queue.Queue.put`/`get`) in `config.yaml`.
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
    00343/00422/00601). Reproducer = the `@Disabled` entry. **Corollary:** a *FALSE* ThingFactory entry
    passes for free (the FN leaves the var untainted → correctly not-reachable, e.g. pathtraver 00524);
    only *TRUE* ThingFactory entries are FN → `@Disabled` (00517/00526/00612).
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
29. **Char-rebuild/element-NextIter drops taint (inv-25 family); per-entry `[...]` deepening fixes it** (deser
    00605: `escape_for_html` rebuilds `s` char-by-char `for c in s: ret += c`, concrete whole-object mark doesn't
    survive the read). FIX: add one more `[...]` to a collection-accessor source (`getlist(...)[...]`→`[...][...]`,
    verified `Result[*]`→`Result[*][*]`, one extra `ArrayElement`) per element/iteration hop, re-run to verify.
    Per-entry SAFE, does NOT generalize — NEVER where the element-read is a *legit sanitizer* (xss:
    `escape_for_html`/`html.escape` ARE the sanitizer, WANT the drop). Engine fix = propagate concrete taint
    through NextIter (inv 25). Deep write-up + emitted-rule dumps in insights log.
30. **pathtraver sinks + pathlib mechanics** (VERIFIED, pathtraver round). `open($A,...)`/`codecs.open($A,...)`/
    `os.path.exists($A)` thread `$A` on arg0 (f-string `f'{DIR}/{bar}'` carries the mark). For pathlib
    `p = testfiles / bar; p.exists()`: `/` is a **native binop** (no call resolved — a truediv passThrough is
    inert), so `p` is tainted natively; the sink is receiver-position `$A.exists(...)` (metavar receiver →
    This-position `ContainsMark`, fires). `.resolve()` is an unmodeled call that **drops CONCRETE taint** (direct
    `form.get`→bar→resolve→p passes as not-reachable) but **ABSTRACT (wrapper/interproc) taint SURVIVES it**
    (inv 25 family) → wrapper-source resolve variants still FP. FALSE pathtraver guards (`'../' in bar`,
    `str(p).startswith(...)`) are operators/receiver-guards, NOT callable validators → NOT unifiable (inv 23) →
    approximation-limited FPs `@Disabled` (inv 16/18/19).
32. **`request.query_string` source flows end-to-end** (VERIFIED, pathtraver b3, 00906/00907/00910). Model as
    `flask.request.query_string`; concrete taint survives `.decode('utf-8')` (bytes.decode passThrough) → **whole-string
    slicing** `qs[a:]`/`p[:b]` (does NOT drop, unlike an element read) → `urllib.parse.unquote_plus` (arg0→result
    passThrough already in config.yaml — the old "unquote_plus DROPS concrete taint" note is STALE; it now PROPAGATES).
    Also: concrete `getlist(...)[...]` element taint survives `list.append`→`lst[0]` into the sink (00742/00751).

33. **`get_safe_value` wrapper is a genuine NON-source** (VERIFIED, pathtraver b4). Unlike
    `get_form_parameter`/`get_query_parameter` (which return `self.request.form/args.get`, inv 26),
    `request_wrapper.get_safe_value(name)` just `return "bar"` (a literal) → `param` never tainted → all
    10 FALSE entries 01105-01114 pass free (the canonical source rule simply doesn't bind). Same free-pass
    mechanism as inv 17 (`request.path`). Model FALSE query_string/path/const-wrapper entries with a
    non-matching bare-attribute source (`flask.request.query_string`, no `.get` last-segment collision).

34. **xpathi sink resolution + str.replace/StringIO taint mechanics** (VERIFIED, xpathi b1). All three
    xpathi sinks fire by last-segment (inv 3): `elementpath.select($ROOT, $A)` (`select`, $A=2nd/query
    arg), `lxml.etree.XPath($A)` (`XPath`, compile-time sink, arg0), `$T.xpath($A)` (`xpath`, receiver
    metavar, arg0). Thread the request source into the query arg exactly like pathtraver's `open($A)`;
    the f-string/`"".join([...,bar,...])` carrying `bar` propagates the mark. Parameterized
    `root.xpath(query, name=bar)` with a CONST `$name` query → bar rides a kwarg, not the query → the
    query-arg sink never binds it → FALSE passes free (00023/00111). **`str.replace` is NOT a cleaner:**
    `bar.replace("'", "&apos;")` resolves by last-segment `replace` to the `copy.replace` passThrough and
    PROPAGATES taint (VERIFIED — 00199 has ONLY replace between param and the sink, still reaches), so the
    apostrophe-escape sanitizer FPs (00108/00109/00199/00200/00202 @Disabled). **This FP is an inv-27
    instance** (the sanitizer `bar.replace(...)` is receiver-position — `str.replace` returns a new value and
    the escaped result is what flows to the sink, but the structural cleaner can only key on `bar`'s receiver
    occurrence, which inv 27 can't clean); the `copy.replace` passThrough is just the propagation path, not the
    blocker — a working receiver-cleaner (inv-27 fix) would clean it regardless. **`io.StringIO` — FIXED
    (was NOT unexpressible, was a missing passThrough).** `strIO.write(bar); q = strIO.getvalue()` used to
    drop the mark, but the write-into-object/read-back pattern IS expressible exactly like `queue.Queue`:
    added `io.StringIO.write` → `from arg(0)/kwarg(s) to this` and `io.StringIO.getvalue` → `from this to result`
    to `config.yaml`. StringIO queries now propagate. Re-triage: TRUE FN re-enabled as `assertReachable`
    (00112/00113/00217/00304/00554/00555/00858/00944/01218); FALSE entries that only passed because StringIO
    dropped now FP on the underlying approximation and are @Disabled with that reason (00024 configparser
    key-insensitivity inv 16; 00471 path-insensitive match arm inv 18; 00764 dict key-insensitivity inv 16);
    00472 stays @Disabled but on inv 20 alone (ThingFactory getattr leaves bar untainted regardless of StringIO).

31. **RESOLVED (`a4d733729`).** The read_text serialization gap ("Entry point not found" on the 6 entries
    00009/00010/00092/00093/00094/00182) was caused by `ClosureAnalyzer` treating unresolved free names — the
    undefined `e`/`fileName` in a dead `except OSError:` block — as closure captures, breaking closure lowering
    so the POST function never serialized. Fixed in `a4d733729`; all 6 now build and PASS with correct verdicts
    (no rule changes needed — 2 TRUE reach, 4 FALSE cleaned by `unquote_plus`/`.resolve()` drops).

35. **Return-value sinks unsupported → whole `xss`/CWE-79 category `@Disabled`** (VERIFIED, engine gap,
    ESCALATED). The XSS sink is the returned response body: `RESPONSE += f'...{bar}...'; return RESPONSE` — a
    bare return, no `render_template_string`/`make_response`/`.write` CALL (make_response is import-only; the 8
    entries calling it inject a HEADER, not the body). A structural sink `return $A` lowers the source but emits
    ZERO sinks: `transformReturn` → `MethodExit` action, and `emitPythonTaintRules` errors on a `Kind.MethodExit`
    accept-edge ("Non method call sinks are not supported yet"); sinks fire only at calls/attr reads. Reproducer:
    `PythonRuleEmitTest.return-value sink emits no sink` + `python-rules/return-sink.yaml` (sources=1, sinks=0).
    Same shape as inv 28. All 40 xss entries `@Disabled` (no yaml). Fix = emit+fire a return sink; then triage
    FALSE half (`escape_for_html`/`html.escape`/`markupsafe.escape` sanitizers). **HOLD all ~89 xss until fixed.**

36. **securecookie / CWE-614 is EXPRESSIBLE as a BARE STRUCTURAL SINK — no source, no ContainsMark**
    (VERIFIED, spike + full suite; all 39 entries active-pass, 0 `@Disabled`). No data-flow source exists (the vuln
    is the call *configuration*, not taint). **CORRECT crutch-free form: a bare structural sink on the dangerous
    call itself** — a single `pattern:` on `$RESP.set_cookie(..., secure=False, ...)` with NO assignment, NO
    self-source, NO downstream-use. A structural sink fires on the call match alone; the kwarg constant does the
    discrimination:
    ```yaml
    patterns:
      - pattern: $RESP.set_cookie(..., secure=False, ...)
    ```
    Lowers (`PythonRuleEmitTest` `securecookie secure=False lowers to a source-less structural sink`) to **exactly
    one sink** `set_cookie` guarded ONLY by a **positive** `ConstantCmp(kwarg(secure)==False)` — **NO
    `SerializedPythonSource` and NO `ContainsMark`**. FIRES: 00064/00065 (secure=False) reach; 00337 (secure=True)
    fails the const-compare → excluded — VERIFIED by full suite (failures=0). The secure=True/False distinction is
    a POSITIVE `secure=False` match in the sink, NOT a `pattern-not` cleaner (kwarg gap fixed for structural
    const-compares, `kwarg-structural`; positive match sidesteps the RuleCookie/inv-27 receiver-cleaner gap).
    Tripwire: `python-rules/securecookie-probe.yaml`.
    **HISTORY:** the earlier form used a self-source crutch `$RESP = flask.make_response(...) ... $RESP.set_cookie(...)`
    (make_response as a self-source, set_cookie's `ContainsMark(This)` as the sink-reach). The crutch was REMOVED —
    a bare structural sink fires on the call match without any `ContainsMark` predicate.

37. **hash / CWE-328 is EXPRESSIBLE as BARE STRUCTURAL SINKS — no source, no `.update` crutch**
    (VERIFIED, spike + full suite; all 151 entries active-pass, 0 `@Disabled`). No data-flow source (the vuln is
    the *algorithm choice*, not taint). **CORRECT crutch-free form: a `pattern-either` of BARE dangerous calls** —
    no `$H` assignment, no `.update` downstream-use. Each branch is a source-less structural sink on the weak call:
    ```yaml
    patterns:
      - pattern-either:
          - pattern: hashlib.new('md5')
          - pattern: hashlib.new('sha1')
          - pattern: hashlib.md5(...)
          - pattern: hashlib.sha1(...)
    ```
    `pattern-either` lowers to N INDEPENDENT source-less sinks (VERIFIED, `PythonRuleEmitTest`
    `hash weak-digest rule lowers to source-less structural sinks`, tripwire `python-rules/hash-probe.yaml` —
    asserts **NO `SerializedPythonSource`** and no `ContainsMark`). Two shapes:
    - **Shape A** `hashlib.new('md5'/'sha1')` — sink `hashlib.new` guarded by a **POSITIVE**
      `ConstantCmp(arg(0)=='md5') AND NumberOfArgs(1)`. SHA-384/512 fail the const-compare → never fire.
    - **Shape B** `hashlib.md5(...)`/`hashlib.sha1(...)` — the FUNCTION NAME itself is the discriminator: sink
      target `hashlib.md5`, trivially-true condition (kept because the target is a specific — not empty — function).
      SHA-256/512 simply don't match the target → never fire.
    FIRES: 00054 (`new('md5')`), 00057 (`hashlib.md5()`) reach; 00055 (`new('sha384')`), 00061 (`hashlib.sha384()`)
    excluded — VERIFIED by full suite (failures=0).
    **HISTORY:** the earlier form threaded a self-source on the hash object into a receiver-position `.update` sink
    (`$H = hashlib.md5(...) ... $H.update(...)`, `ContainsMark(This)`). Both the `$H` self-source AND the `.update`
    downstream-use were crutches — REMOVED; a structural sink fires on the call match alone.

38. **weakrand / CWE-330 is EXPRESSIBLE as BARE STRUCTURAL SINKS for weak module calls + secrets FALSE, but
    SystemRandom FALSE is NOT (last-segment collision → `@Disabled`)** (VERIFIED, spike + full suite; 226
    active-pass, 100 `@Disabled`). No data-flow source (the vuln is the RNG *choice*: Mersenne-Twister
    `random.<fn>` vs CSPRNG). **CORRECT crutch-free form: a `pattern-either` of BARE dangerous calls** — no
    `str(...)` wrapper. Each branch is a source-less structural sink on the weak `random.<fn>` call (the function
    name IS the discriminator):
    ```yaml
    patterns:
      - pattern-either:
          - pattern: random.normalvariate(...)
          - pattern: random.randint(...)
          - pattern: random.getrandbits(...)
          - pattern: random.random(...)
          - pattern: random.randbytes(...)
    ```
    Each branch lowers (`PythonRuleEmitTest` `weakrand rule lowers to source-less structural sinks per weak
    function`, tripwire `python-rules/weakrand-probe.yaml`) to a **source-less structural sink** `random.<fn>`
    with a trivially-true condition (**NO `SerializedPythonSource`, NO `ContainsMark`**). Fires on the call match.
    - **TRUE (weak module calls) FIRE**: `random.getrandbits(32)` resolves to `PIRQualifiedUnknownFunction:
      random.getrandbits`, `matchesName` `qn==targetName` → sink fires (VERIFIED full suite).
    - **secrets.\* / os.urandom FALSE cleanly excluded**: distinct last segments from the five weak fns → sink
      target never matches → silent.
    - **⚠️ SystemRandom (CSPRNG) FALSE NOT excludable → `@Disabled`**: `random.SystemRandom().getrandbits(32)`
      resolves to `PIRSimpleNameUnknownFunction:getrandbits` (constructor return type unresolved → simple-name
      callee). `matchesName` unconditionally matches a `PIRSimpleNameUnknownFunction` by last segment against ANY
      target → collides with `random.getrandbits` → sink FIRES → FP. **The sink/source distinction does NOT change
      this**: last-segment callee matching is identical whether the weak call is a source or a bare sink — RE-VERIFIED
      under the crutch-free form (temporarily enabled 00044 → still fires → FP). Structurally inseparable; the 100
      SystemRandom entries stay `@Disabled`. **A `pattern-not: random.SystemRandom().<fn>(...)` exclusion does NOT
      help — VERIFIED it is silently DROPPED in conversion**: the emitted rules are byte-identical with/without it
      (no `SerializedPythonSource` for `SystemRandom()`, no `Not` condition), because a source-less structural sink
      engages no mark machinery and a two-call-chain `pattern-not` never lowers to a `Not(ContainsMark)`. Excluding
      SystemRandom would require an engine change (emit a source for `random.SystemRandom()` + lower a chain
      `pattern-not` to a mark-gated negative). Not supported — do not re-attempt at the rule level.
    **HISTORY:** the earlier form nested each weak call in a `str(...)` wrapper crutch (self-source `random.<fn>`
    threaded into a generic `str($T)` sink). The `str(...)` wrapper was REMOVED — a structural sink fires on the
    weak call directly.

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
