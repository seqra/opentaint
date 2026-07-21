# Python OWASP benchmark — insights log

Running notes for future benchmarking sessions. Append findings as you go: source-pattern →
resolved-callee gotchas, precision tricks, pass-throughs added, and FP/FN judged unfixable (with
the reason). See `python-owasp-benchmark-session.md` for the task and harness description.

## Rule authoring

### SQLi sink — parameterized vs interpolated precision
The OWASP SQLi entries discriminate true/false by how `cursor.execute` is called:
- **true (vulnerable):** `cur.execute(sql)` — tainted value is interpolated into the query string.
- **false (safe):** `cur.execute(sql, (bar,))` — parameterized; the tainted value is bound as a
  separate argument and never enters the query string.

A naive sink `$DB.execute($Q, ...)` fires on *any* tainted sub-expression in the match, so the
parameterized-safe form (tainted `bar` in the param tuple) becomes a **false positive**. Restrict
to the query arg with `focus-metavariable` (supported — see
`opentaint-python-querylang/samples-py/{MultiArgSink,RuleWithFirstParamToSink}`):

```yaml
pattern-sinks:
  - patterns:
      - pattern: "$DB.execute($Q, ...)"
      - focus-metavariable: $Q
```

This is the shared SQLi sink for all seed entries.

### Source patterns (flask request surface)
Resolved-callee matching is the fragile part. Known-working shapes for the seed set:

| source in code | pattern |
|---|---|
| `request.form.get(...)` | `flask.request.form.get(...)` |
| `request.form.getlist(...)` | `flask.request.form.getlist(...)` |
| `request.cookies.get(...)` | `flask.request.cookies.get(...)` |
| `request.headers.get(...)` | `flask.request.headers.get(...)` |
| `request.args.get(...)` | `flask.request.args.get(...)` |
| `request.args.getlist(...)` | `flask.request.args.getlist(...)` |
| `request.path` | `flask.request` (attribute source) — verify |
| `request_wrapper(request).get_*` | `flask.request` (attribute) + flask pass-throughs — verify |

The wrapper cases (`helpers.separate_request.request_wrapper`) call `self.request.form.get(...)`
inside a method, so a `flask.request.form.get(...)` pattern likely won't tag them — the receiver is
a `flask.Request`-typed field, not the `flask.request` global. Fallback: `flask.request` attribute
source so the whole request object is tainted through `__init__` → `self.request` → the getter.

### Prefer the *fullest* source pattern; add the subscript for collection accessors
Two authoring rules for source patterns (from the session guidance):

1. **Specify the full source accessor chain**, not a truncated prefix. Write
   `flask.request.form.getlist(...)`, not `flask.request.form`. The accessor method (`.get`,
   `.getlist`, `.values`, …) is what actually returns the tainted value; a truncated `flask.request.form`
   both over-matches unrelated reads and can resolve differently.
2. **When the accessor returns a collection, add a trailing subscript** so the tainted *element* is
   what's captured: `flask.request.form.getlist(...)[...]` (`getlist` → `list`, `values`/`keys`
   iterables, etc.). If both the whole-collection use and the indexed-element use appear, use
   `pattern-either` with both the subscripted and non-subscripted forms:

   ```yaml
   pattern-sources:
     - pattern-either:
         - pattern: "flask.request.form.getlist(...)"
         - pattern: "flask.request.form.getlist(...)[...]"
   ```

   Engine invariant 12 (whole-object taint → subscript element read) makes the bare-collection form
   propagate to `x[i]` intraprocedurally too, but the explicit `[...]` form is the robust default and
   the `pattern-either` covers both call shapes without relying on that path.

### base64 round-trip drops taint (fixed via pass-throughs)
00454 (`base64.b64encode(param.encode()).decode()` round-trip, true) was a FN: `base64.b64encode`
had no pass rule so taint dropped (it showed in `external-methods-without-rules.txt` as
`base64.b64encode [arg(0)]`; note `str.encode` already propagates). Added pass-throughs to
`config.yaml`: `base64.b64encode` (arg0/kwarg(s)→result), `base64.b64decode` (arg0/kwarg(s)→result),
`builtins.bytes.decode` (this→result). 00454 now passes. Same pattern for 00455 uses a dict
round-trip which was already modeled.

## Pass-throughs added
- `base64.b64encode`, `base64.b64decode` (arg(0) + kwarg(s) → result)
- `builtins.bytes.decode` (this → result)

## Known unfixable / accepted FP-FN (this session)

### `match`/`case` unsupported in PIR — 00192, 00287 (@Disabled)
`ast_serializer._serialize_stmt` returns `None` for any `MatchStmt` (falls through to the `else`
branch), so a function whose only assignments live in `case` arms can't build → the analysis can't
find the entry function ("Entry point not found"). Both are `false` (parameterized) entries.
Disabled with a reason. Fixing requires adding `MatchStmt` to the proto + Flat + PIR pipeline —
out of scope for benchmarking.

## cmdi round (CWE-78, 20 entries)

Sink for all: `subprocess.run($CMD, ...)` focus `$CMD` (command built as `argList.append(f"echo {bar}")`
then `subprocess.run(argList)`; sink matches `argList` at base). Sources mirror the SQLi shapes
(`flask.request.form.get/getlist`, `.headers.get/getlist`, `.args.get`, `.form.keys`, and `flask.request`
for the `request_wrapper` cases). TRUE=11 pass, FALSE=3 pass; 8 disabled (see below).

### Engine fix: whole-object taint → subscript element read
Added to `handleAccessorRead` (`PIRMethodSequentFlowFunction`): a fact whose start accessors are all
`TaintMarkAccessor` on the container base means the whole value is tainted, so any `x[i]` read now
propagates the mark. Fixed the `getlist`/`getlist[0]` cases (00267, 00268, 00606, 00607). No regressions
(all SQLi seeds + samples stay green). See invariant 12.

### Unfixable-by-design (this round, @Disabled)
- **00168, 00899** — `match`/`case` unsupported (invariant 4); both TRUE, can't build.
- **00350, 00736** — dict key-insensitivity FP: store keyB(param), read keyA(const) (invariant 16).
- **00512, 00900** — configparser key-insensitivity FP (`.Element`); passthrough needed by 00099 (inv 16).

### Escalated hard engine gaps (@Disabled, reproducer left)
- **00165, 00511** — `list.append` passthrough taints `lst.append.$PIR_SELF.![mark]` not `lst`; `lst[0]`
  read misses it (invariant 14). Reproducer = these two `@Disabled` OWASP entries.
- **00431, 00432** — for-loop `PIRNextIter` unmodeled; `for name in request.form.keys()` never taints
  `name` (invariant 15). Reproducer = `samples-py/ForLoopElementRead` (`@Ignore`d).

### Never-tainted FALSE cases that pass cleanly
- **01097, 01098** — `request.path` not a source (invariant 17).
- **01173** — `request_wrapper.get_safe_value()` returns a constant, so param is never tainted.

## Fixed this session

### `request_wrapper` indirection resolution — 00283, 00284 (was FN, now pass)
`helpers.separate_request.request_wrapper(request).get_form_parameter(name)` whose body is
`return self.request.form.get(name)`. Field/alias flow already worked; the bug was **callee-name
resolution**: `PIRMethodQFNameReconstructor` textually chained the field-access path from `self`
(`...request_wrapper.request.form.get`) instead of resolving the `flask.Request`-typed field. That
field's type is erased to `PIRAnyType` under `--ignore-missing-imports`, so type-based resolution
returned null and the wrong chained name matched no pass-through — and, being non-empty, it also
suppressed the simple-name (`get`) fallback in `PIRCallResolver.resolveCall`.

**Fix (`PIRMethodQFNameReconstructor`, `PIRLoadAttr` transfer):** on a *known* base class, resolve
the attribute against the class and propagate every match — a field/property contributes its declared
type QN, a method contributes its own QN (found by walking the MRO, so inherited methods resolve).
A field with an unresolved (`Any`) type contributes nothing, so downstream calls fall back to
simple-name pass matching (which correctly hits `flask.wrappers.Request.form.get` etc. by last
segment — see `MethodTaintConfigurationResolver.matchesName`). The old code textually chained on any
attribute of a known base, which both mis-resolved unresolved-type fields and (in the interim
version) dropped method QNs.

Related insight: the `flask.wrappers.Request.*` pass-throughs in `config.yaml` only fire when the
receiver resolves to that class; with flask erased to `Any`, the simple-name last-segment match is
what actually carries these. (Open design question from the user: whether request-accessor
`.form`/`.get` entries belong as pass-throughs or source rules — deferred.)

## ldapi round (CWE-90, 29 entries)

Sink for all: `$CONN.search($BASE, $FILTER, ...)` focus `$FILTER` (ldap3 `conn.search(base, filter,
attributes=...)`; only the filter arg is dangerous). Sources mirror the SQLi/cmdi shapes
(`flask.request.form/args/headers.get`, `.getlist(...)[...]`, `.cookies.get`, `.query_string`, and
`flask.request` for `request_wrapper` cases). **18 active pass, 11 @Disabled.**

### Match/case + list.append are FIXED — old invariants 4 & 14 retired
Two engine capabilities landed since earlier rounds:
- **`match`/`case` now builds & analyzes** (`ast_serializer.py:456`). TRUE match entries (00266, 00604,
  00733, 00824) now correctly reach the sink. But flow is **path-insensitive across arms** (new inv 18).
- **`list.append` now propagates** ("Fix list append rule" commit). Lists are index-insensitive (new inv 19).

### Active TRUE (15, pass): 00265, 00266, 00427, 00429, 00430, 00505, 00506, 00604, 00731, 00733, 00823, 00824, 00895, 01193, 01200
Straightforward request→f-string-filter→search flows. 00506 uses configparser (set/get same key, key-insens
passthrough already present). 00895 uses base64 round-trip (passthroughs already present). 00266/00604/00733/
00824 go through `match`/`case`. 00427/00429/00430/01193 use the for-loop keys() source
`flask.request.form.keys(...)[...]` — the loop var `name` (a form KEY) is tainted via NextIter (inv 15,
now supported); the getlist shape was wrong (getlist only in the `if` guard, never reaches the sink).
00427 reads the tainted key back out of a dict; 00429 flows via an always-true-else `bar = param`; 00430
via string concat + slice; 01193 flows `param` straight into the filter f-string.

### Active FALSE (6, pass): 00991, 01095, 01168, 01169, 01170, 01171
- 00991 — query_string→slice→list pattern; passes (list-safe path / source drop). NOTE not a robust "cleaned" pass.
- 01095 — `request.path` not a source (inv 17); rule source is `flask.request.form.get` which never matches.
- 01168/01169/01170/01171 — `request_wrapper.get_safe_value()` returns constant `"bar"` → never tainted.

### Unfixable-by-design (@Disabled)
- **00076, 00990, 00428** (FALSE, FP) — dict / configparser key-insensitivity: store keyB(param), read keyA(const) (inv 16).
  00428 uses the for-loop keys() source (now taints `param`), then stores under keyB but reads the constant slot
  `map['keyA-3150']`; dict is key-insensitive so the tainted keyB read leaks → genuine inv-16 FP (was mis-tagged inv 15).
- **00348** (FALSE, FP) — list index-insensitivity: `lst.append(param); lst.pop(0); bar = lst[1]` reads tainted (inv 19).
- **00077** (FALSE, FP) — path-insensitive match arm: const discriminator picks safe arm, tainted arm still explored (inv 18).
- **00732, 00897** (FALSE, FP) — path-insensitive always-true ternary guard: else-branch (param) taints bar (inv 18).

### Escalated (@Disabled, reproducer = the OWASP entry)
- **00896** (TRUE, FN) — `helpers.ThingFactory.createThing()` uses `getattr(mod, name)()`, so the returned
  object is `Any`; `thing.doSomething(param)` can't resolve to `Thing1`/`Thing2` and the arg→return
  pass-through is lost. Root cause: interprocedural resolution doesn't fall back to simple-name matching for
  user methods on an Any receiver (unlike config pass/sink rules, inv 3). User will investigate later (inv 20).

## xxe round (CWE-611, 28 entries)

Sink for all: an **external-entity-enabled parse** — `xml.dom.minidom.parseString($DOC, $P)` gated by a
preceding `$P.setFeature($F, True)` via statement-sequence `pattern-inside` (see inv 21). Every sample
uses the same `xml.sax.make_parser()` + optional `setFeature(feature_external_ges, True)` + `parseString`
shape; the setFeature line is the TRUE/FALSE discriminator for the "hardened-parser" FALSE variants.
Sources mirror the SQLi/cmdi/ldapi shapes. **20 active pass (6 TRUE + 14 FALSE), 8 @Disabled.**

### Active TRUE (6, pass): 00205, 00294, 00460, 00930, 00931, 01212
- 00205 configparser same-key round-trip; 00294 wrapper form + if/else tainted-else; 00460 headers.get
  direct; 01212 args.getlist direct.
- 00930/00931 (query_string): needed source `flask.request.query_string.decode(...)` — the fullest
  accessor chain. A bare `flask.request` source FN'd NOT because of the attribute read — whole-object
  taint DOES propagate through `request.query_string` — but because the `.decode(...)` call resolves
  to the chained QN `flask.request.query_string.decode` (no passthrough) and, being a resolved name,
  suppresses the simple-name fallback that would hit `builtins.bytes.decode` (inv 22, corrected;
  inv 3/7). Tagging the decode() result directly sidesteps it. 00930 base64 round-trip +
  `urllib.parse.unquote_plus` (passthrough already present); 00931 match/case (case A: bar=param).
  No new pass-throughs needed.

### Active FALSE (14, pass)
Hardened-parser (no `setFeature(_,True)` → sink never fires even though taint often DOES reach the
parse): 00017, 00204, 00291, 00292, 00293, 00459, 00538, 00539, 00678, 00850, 01024, 01122, 01211.
This is the robust way to model the safe variants — no cleaner needed, the sink simply isn't dangerous.
Plus 01025 (dangerous parser but `request.path` source, not matched by `flask.request.args.get` → never
tainted, inv 17).

### Unfixable-by-design (@Disabled)
Dangerous-parser FALSE variants that FP on dataflow-approximation limits:
- 00206, 00759 — configparser key-insensitivity (inv 16): set keyB(param), get keyA(const).
- 00461 — dict key-insensitivity (inv 16).
- 00679 — list index-insensitivity (inv 19): append(param), pop, read lst[1].
- 00540, 00851 — path-insensitive match arms (inv 18): const discriminator picks safe arm, tainted arm explored.

### Escalated (getattr inv 20, confirmed still failing)
- 00462, 00541 (TRUE, FN) — `helpers.ThingFactory.createThing()` uses `getattr(mod, name)()` → Any
  receiver → `thing.doSomething(param)` unresolved. **Verified empirically** by un-disabling + re-running
  (both FAIL). The `7aba04fa6` simple-name fallback does not help — synthetic unknown func has no
  arg→return. Same root cause as ldapi 00896; reproducer = these `@Disabled` OWASP entries.

### Capability-invariant guard applied
No stale "unsupported" invariant found this round. match/case (00931 TRUE reaches, 00540/00851 FALSE
FP as expected) and getattr (inv 20, re-verified failing) both behaved per current engine.

## redirect round (CWE-601, 34 entries) — ALL STRUCTURAL rules

Sink for all: `flask.redirect(...)` (code always calls `import flask; return flask.redirect(bar)`).
Sources mirror prior rounds (cookies/form/args/headers `.get`/`.getlist`, `.form/.headers.keys(...)[...]`
loop, `.query_string.decode(...)`). **28 active pass (13 TRUE + 15 FALSE), 6 @Disabled.** Zero
taint-mode rules — every entry is a structural `patterns:` rule.

### The TRUE/FALSE discriminator is a `urllib.parse.urlparse` + netloc/scheme validator
No TRUE entry uses `urlparse` (they use `unquote_plus`); 9 FALSE entries are safe ONLY because of the
`url = urllib.parse.urlparse(bar); if url.netloc not in [...] or url.scheme != 'https': return` guard.
Modeled structurally with the **unified-`$M` validator-exclusion form** (new invariant 23) — DO read
it before the next validator-guarded category:
```yaml
patterns:
  - pattern: |
      $M = flask.request.<accessor>(...)
      ...
      flask.redirect($M)
  - pattern-not: |
      ...
      urllib.parse.urlparse($M)
      ...
      flask.redirect($M)
```
Source/sink/cleaner all keyed to mark `$M`; sink+cleaner are dataflow `ContainsMark($M, arg0)` checks,
so they fire on the rebound `bar` and the cleaner removes `$M` there. Works for direct (01209) AND
rebinding (00069 configparser, 00151/00420/00816 match, 00419 list, 00598 ThingFactory, 00815 if/else,
00983 dict) guard entries.

**Two dead-ends burned first (both silently emit no working cleaner — confirmed via `PythonRuleEmitTest`
dumps):** (1) sink-only `flask.redirect($URL)` + `pattern-not-inside: urlparse($URL) ...` → bare
`NumberOfArgs` sink, cleaner edges dropped ("no positive predicate"); (2) split `$A=src ... redirect($URL)`
+ `pattern-not ... urlparse($URL) ... redirect($URL)` → source marks `_<S>_`, cleaner cleans `$URL`
(mismatched mark). See invariant 23 for the full autopsy.

### Active TRUE (13, pass): 00067, 00068, 00258, 00418, 00495, 00496, 00596, 00654, 00655, 00814, 00982, 01178, 01208
Plain structural `$A = <source> ... flask.redirect($URL)`. Flows through base64 round-trip (00067/00495),
dict same-key (00068), getlist+index (00258/00814), keys()-loop (00418/00654/00655), configparser same-key
(00596), ternary/if-else tainted arm (00496/00418 — path-insensitive so tainted arm reaches), query_string
decode+slice (00982), direct (01178/01208). All reachable.

### Collection-element source drop (00258/00418/00596/00654/00655/00814 — was FN after inv-24, now fixed)
After the inv-24 metavar unification made the redirect sink a real `ContainsMark($A)` dataflow check, these
6 TRUE entries FN'd ("sink not reached"). Root cause was **not** a rule-shape issue — it's a two-part
engine/lowering gap (full writeup in session-2 invariant 25):
- The 6 entries all flow a **collection element** to the sink: `values = form.getlist(...); param =
  values[0]` (00258/00814/00596 getlist+index) or `for name in request.headers.keys(): param = name`
  (00418/00654/00655 keys-loop). The source (`getlist`/`keys`) taints the whole collection; the value that
  reaches `flask.redirect` is the *element* / loop var.
- **inv 12 is stale for concrete facts:** a concrete whole-object fact `values.![mark]` does NOT propagate
  through an intraprocedural element read or for-loop NextIter — `mayReadAccessor(values, ElementAccessor)`
  is false (fact starts with `TaintMarkAccessor`, not `ElementAccessor`; not abstract). Confirmed the drop
  in `PIRFlowFunctionUtils.mayReadAccessor` / `handleAccessorRead`.
- **Structural-lowering bug:** the source binding `$A = getlist(...)[...]` was supposed to taint the
  element, but `PythonPatternToActionListConverter.transformAssignmentValue` **dropped the `[...]` element
  modifier** (`setResultCondition` replaced the result with just `$A`), so `getlist(...)` and
  `getlist(...)[...]` lowered identically to whole-`Result` taint (verified by dumping emitted rules).
  The whole-object taint then dropped at the first element read/NextIter.
- **Fix (rule-shape + one converter change):** (a) added `[...]` to the 3 getlist rules
  (00258/00596/00814); the 3 keys rules already had it. (b) fixed `transformAssignmentValue` to merge the
  value's existing result modifier into the metavar condition, so `$A = getlist(...)[...]` now taints
  `Result[*]` (element), matching the proven bare taint-mode subscript source. All 6 now pass; no OWASP
  regressions (94→100 passing, 0 failing, skipped unchanged at 33). Regression test:
  `PythonRuleEmitTest.subscript-assignment source binds the metavar to the result element`.
- **Bonus:** keys-source FALSE entries 00419/00420 (urlparse-guarded) previously passed because taint
  dropped at NextIter (masking); now taint flows and the unified-`$M` urlparse cleaner removes it — they
  pass for the right reason.
- **NOT a pure rule-shape issue:** there is no YAML-only way to bind a structural metavar to the element
  (subscripting a bare metavar `$A = $V[...]` fails conversion), so the converter fix was required. It is a
  small, principled lowering fix (not engine grinding) that aligns structural sources with taint-mode.

### Pre-existing unrelated failure (out of scope)
`PythonSampleBasedTest.allowedSpecificConstant` fails on the current branch **independently of this work**
(verified: fails with the converter change stashed). Not touched here.

### Active FALSE (15, pass)
- **9 urlparse-guarded** (unified-`$M`, inv 23): 00069, 00151, 00419, 00420, 00598, 00815, 00816, 00983, 01209.
- **6 never-tainted**: 01091 (`request.path` not a source, inv 17), 01156/01157/01158/01159/01160
  (`request_wrapper.get_safe_value()` returns constant `"bar"`). Rule uses source
  `flask.request.form.getlist(...)` which never matches these files → nothing tainted → not reachable.
  NOTE: source `flask.request.form.get(...)` was a TRAP here — its simple-name `get` collides with
  configparser/dict `.get(...)` (inv 3 last-segment fallback) and FP'd 01157/01160; `getlist` has no
  such collision. Prefer a rare accessor (`getlist`) for never-match sources.

### Unfixable-by-design (@Disabled, 6) — no distinguishing validator CALL to unify a cleaner against
- **00259** — path-insensitive const-true ternary (inv 18): `bar = SAFE if <const-true> else param`.
- **00724** — path-insensitive match arm (inv 18): const `guess` picks safe case, tainted arm still explored.
- **00417, 00722** — configparser key-insensitivity (inv 16): set keyB(param), get keyA(const).
- **00597, 00723** — list index-insensitivity (inv 19): append(param), pop(0), read lst[1].
These are safe only by a runtime key/index/branch value; there is no `urlparse`-style guard call to clean
on, so the unified-`$M` trick doesn't apply.

## codeinj round (CWE-94, 53 entries) — ALL STRUCTURAL rules

Sink: `eval($A)` or `exec($A)` (per entry). Shape: `$A = <request source> ... eval/exec($A)`.
Sources mirror prior rounds: cookies/form/args/headers `.get`, `.form/.args/.headers.getlist(...)[...]`,
`.form.keys(...)[...]` loop, `.query_string.decode(...)`. **26 active pass (17 TRUE + 9 FALSE), 27 @Disabled.**
Suite after round: 180 tests, 0 fail, 54 skipped (126 pass).

### Wrapper source: use the canonical flask accessor (new inv 26)
The `request_wrapper` getters (`get_form_parameter`→`self.request.form.get`, `get_query_parameter`→
`self.request.args.get`) are tagged by the plain source `$A = flask.request.form.get(...)` /
`flask.request.args.get(...)` — NO `$W.get_form_parameter(...)` needed. The structural rule lowers to a
taint rule applied at each attribute read, so marks flow through the full `self.request.form.get` chain
interprocedurally (user-confirmed: not simple-name matching). Verified: 00342/00890/00891/00894 (TRUE) pass.

### Active TRUE (17, pass)
00074 (cookies.get→configparser), 00159 (form.get→list), 00160 (form.get→match A), 00161 (form.get→ternary
else), 00342 (wrapper form→configparser), 00425 (keys loop→str slice), 00503 (headers.get→base64), 00599
(headers.getlist→list), 00728 (args.get→match A), 00729 (args.get→slice), 00819 (args.getlist→bar=param),
00820 (args.getlist→base64), 00890/00891 (wrapper query→param / configparser), 00894 (wrapper query→
`if 'should' in bar: bar=param`), 00986 (query_string→list), 01188 (form.getlist→exec(param) direct).

### Active FALSE (9, pass)
- **5 ThingFactory FN-drop** (00075/00163/00504/00818/00989): `thing.doSomething(param)` where
  `createThing()` uses `getattr` → Any receiver → taint drops (inv 20), so eval/exec never reached even
  though these also carry the startswith guard. Pass via the FN. (These are the FALSE mirror of the
  TRUE ThingFactory entries that FN and are @Disabled.)
- **4 never-tainted** (01164/01165/01166/01167): `request_wrapper.get_safe_value()` returns constant
  `"bar"`; source `flask.request.form.getlist(...)` never matches → nothing tainted.

### The startswith/endswith guard: receiver-position cleaner cleans a PIR_SELF may-alias, not the base var (inv 27, @Disabled 14)
FALSE entries safe only by `if not bar.startswith('\'') or not bar.endswith('\'') or '\'' in bar[1:-1]:
return`. Authored the unified-$M `pattern-not: ... $M.startswith(...) ... sink($M)` (inv 23 shape) for all
14 — **every one FP'd**. Root cause VERIFIED on 00073 (rule-dump via `PythonRuleEmitTest` + engine trace
via `System.err.println` in `PIRMethodCallFlowFunction`, read from the test XML `<system-err>`). Both prior
hypotheses ("doesn't lower to a cleaner" / "if-condition call not reached") are WRONG:
- **The cleaner IS emitted.** Dump shows 4 rules: Source taints `Result`→`$M;1`; Sink `eval` checks
  `ContainsMark($M;1, arg0)`; a Cleaner on `startswith` with `condition=ContainsMark($M;1, pos=This)` /
  `cleans=[TaintClean($M;1, pos=This)]` — it checks the RECEIVER, correctly. No `AUTOMATA_TO_TAINT_RULE`
  "no positive predicate" warning; nothing dropped.
- **The cleaner IS reached and fires.** Trace at the `bar.startswith(...)` call (line 46, inside the
  if-condition): `cleanersFound=2`, condition `evalTrue=true`, cleaner result `fact=null` (receiver fact
  dropped). If-condition nesting is irrelevant.
- **Why the FP persists — no must-alias, PIR_SELF hack.** `bar.startswith(...)` has no real instance at the
  call site; the receiver is a bound-method capture, so the fact entering the call is `bar.$PIR_SELF![$M]`
  (a MAY-alias of `bar`, mapped to `<this>`). The cleaner drops only that `This` fact. The **base-variable
  fact `bar![$M]` is distinct** — the trace shows the mark reaching `eval` on the base var (`var(16)`) while
  the cleaned receiver was `var(17).$PIR_SELF` — and nothing links them without must-alias, so it survives.
- **Discriminating control (confirms it's receiver-vs-base, nothing else).** A minimized sample with an
  identical source→bar→guard→sink flow was run two ways: an ARGUMENT-position guard `check(bar)` (cleaner
  cleans `Argument(idx=0)`) **passed green** — the arg maps back to base `bar` even without reassignment —
  while the receiver-position `bar.startswith(...)` variant FALSE-POSITIVEd. The only difference is guard
  position. Arg-position cleaners work (inv 23); receiver-position ones can't, and the 00073 guard offers no
  arg-position call carrying `bar` → no structural reshape fixes it. (Reproducer removed after verification.)
- **Escalated (engine gap).** Fix candidate: propagate a receiver/`This` clean to may-aliases (clean the
  base var behind `$PIR_SELF`).

@Disabled:
- Pure-guard (tainted value definitely reaches bar): 00073, 00158, 00345, 00423, 00426, 00603, 00893, 00987, 00988.
- Guard + also path-insensitive safe arm (still FP via guard): 00162 (match B), 00730/00821/00892 (if-else
  `'should' not in` → else param), 00822 (ternary).

### Unfixable-by-design (@Disabled, 10) — no distinguishing validator CALL
- path-insensitive if/else or match arm (inv 18): 00156, 00157, 00263, 00264, 00344, 00600.
- configparser key-insensitivity (inv 16): 00346, 00602.
- dict key-insensitivity (inv 16): 00347.
- list index-insensitivity (inv 19): 00424.

### Escalated (inv 20, confirmed still failing this round) — @Disabled TRUE FN
- 00343, 00422, 00601 (TRUE, FN): `helpers.ThingFactory.createThing()` getattr → Any receiver →
  `thing.doSomething(param)` unresolved, arg→return pass-through lost. Verified empirically (all three
  "sink was not reached"). Same root cause as ldapi 00896 / xxe 00462/00541. Reproducer = these @Disabled
  OWASP entries.

### No pass-throughs / engine changes needed this round.

## trustbound round (CWE-501, 37 entries) — BLOCKED on engine gap, ALL @Disabled (inv 28)

Sink for every entry is a **session write** `flask.session[$K] = $V` — a subscript-STORE, a sink shape
new to this category. **The engine cannot express or fire a store-target sink**, so the whole category
is @Disabled. Suite after round: 217 tests, 0 fail / 0 error, 91 skipped (54 prior + 37 trustbound); 126
pass unchanged.

### Root cause — VERIFIED two independent ways (not hand-waved)
1. **Rule dump (converter drops it):** a structural rule whose sink statement is `sess[$A] = $V` emits
   ZERO taint rules. `PythonPatternToActionListConverter.transformAssignment` only binds a metavar target;
   a subscript (or attribute) assignment target hits `transformationFailed("Assignment_target_not_metavar")`,
   which throws out of `transformSequence` → the whole `patterns` block converts to null → no source, no
   sink. Proven by `PythonRuleEmitTest.subscript-assignment sink emits no sink (engine gap)` (probe
   resource `python-rules/subscript-assign-sink.yaml`, PROBE-EMIT-COUNT=0). This tripwire flips (emit
   non-empty) when store sinks become expressible.
2. **Code (engine never checks it):** `flask.session[bar] = v` lowers to `PIRStoreSubscript` (side-effect
   inst; `StatementLowering.kt:77`, `CfgConverter.kt:109`). Sinks are checked only at call sites
   (`PIRMethodCallFlowFunction.applySinkRules`) and attribute reads (`sinksForAttribute`).
   `PIRMethodSequentFlowFunction.handleStoreSubscript` propagates taint (value→obj element) but performs
   NO sink check. So even a hypothetically-authored store sink would never fire.

The tainted data flows into the **key** (`flask.session[bar] = '12345'`, bar tainted — 00072/00154/…) OR
the **value** (`flask.session['userid'] = bar` — 00070/00153/…); both are CWE-501. The rule files record
the intended dual-position structural authoring via `pattern-either` (key `sess[$A]=$V` + value
`sess[$K]=$A`), ready to enable once the gap is fixed.

### Fix sketch (ESCALATED — hard, multi-part; not a benchmark-round fix)
- Converter: accept an `Assign` whose target is a `Subscript`/`Attribute` in sink position and emit a new
  "store sink" that checks taint on BOTH the index/key and the value (roughly: sink on the container write
  with a `ContainsMark` over the key AP and the value AP).
- New sink kind + resolver wiring (a store sink isn't function/attribute-targeted).
- Engine: check store sinks in `handleStoreSubscript` (and the `StoreAttr`/`StoreGlobal` analogues).

### Per-entry ground truth (recorded; sources noted for the enable-later round)
- TRUE key-position (`session[bar]=`): 00072/00154/00155(cookies/form), 00261/00262(form.getlist),
  00341(wrapper form), 00501/00502/00656(headers), 00727(args), 00889(wrapper query), 00985(query_string).
- TRUE value-position (`session['userid']=`): 00153(form), 00260(form.getlist), 00338/00340(wrapper form),
  00497/00499(headers), 00725(args), 00817(args.getlist), 00887/00888(wrapper query), 00984(query_string).
- FALSE that would need post-enable triage: 00070/00152 (configparser key-insens inv 16),
  00071 (never-tainted, param→string not copy), 01092/01093/01094 (`request.path.split` — not a source,
  inv 17), 01161/01162/01163 (`get_safe_value` returns const → never tainted), plus the usual
  configparser/dict/list key-insens (inv 16/19) and path-insensitive-arm (inv 18) variants among
  00155/00262/00339/00421/00498/00500/00726.
- Sources cover cookies/form/args/headers `.get`, `.form/.args.getlist(...)[...]`, `get_form_parameter`/
  `get_query_parameter` wrappers (inv 26 → flask.request.form/args.get), `query_string.decode`.

### No pass-throughs / engine changes made this round (gap escalated, not patched).

## deserialization round (CWE-502, 54 entries) — ALL STRUCTURAL rules

Two sinks, both CALLS:
- **pickle:** `pickle.loads($A)` — payload arrives base64-wrapped
  `pickle.loads(base64.urlsafe_b64decode(bar))`. Threading `$A` into `pickle.loads($A)` lowers to a
  `ContainsMark($A)` check on arg0; arg0 is `urlsafe_b64decode(bar)` → needed the **`base64.urlsafe_b64decode`
  passThrough (arg(0)+kwarg(s)→result)** added to `config.yaml` (was missing; `b64encode/b64decode` already
  present). Every pickle TRUE entry depended on it.
- **yaml:** unsafe `yaml.load($A, ...)` (full Loader) is the vuln; the SAFE variant is a **different callee**
  `yaml.safe_load(...)`. Rule matches `yaml.load` only → the source still matches & taints `bar`, but the
  sink never fires on `safe_load` (last-segment `load`≠`safe_load`, no collision). This is the robust
  safe/unsafe modeling — no cleaner needed (like the xxe hardened-parser). Covers ~19 FALSE entries.

**Suite after round: 271 tests, 0 fail, 100 skipped (171 pass).** Batch = 45 active pass (16 TRUE + 29
FALSE) + 9 `@Disabled`.

### Active TRUE (16): 00078 00164 00270 00433 00507 00510 00657 00734 00735 00825 00827 00898 00992 00993 00994 01216
cookies/form/args/headers `.get`, `.getlist(...)[...]`, `.keys(...)[...]` loop, `query_string.decode`,
`get_query_parameter` wrapper (inv 26 → `flask.request.args.get`). Flows through dict same-key (00433),
match tainted arm (00507), b64 roundtrip (00657), html.escape passthrough (00992), if/else tainted arm
(00898/00993). All reach.

### Active FALSE (29)
- **19 safe by callee** (`yaml.safe_load`): 00079/00080/00081 00271 00434 00435 00514 00609 00659 00660
  00828 00901/00902/00903/00904 00996/00997/00998/00999. Source matches & taints, `yaml.load` sink doesn't
  match `safe_load` → not reachable.
- **9 never-tainted** (source pattern never matches the real request use): 01096 01099 01100/01101/01102
  01228 (`request.path.split`, inv 17) + 01172 01174 01230 (`get_safe_value` returns const). Rule source is a
  `getlist(...)[...]` that never appears in these files.
- **1 copy-semantics** (00509): `copy = string33385(''); string33385 += param; copy += 'const'; bar=copy` →
  `copy` never carries `param` (immutable-string rebind). NotReachable, passes cleanly.

### @Disabled (8)  — 00605 RESOLVED, see inv 29
- **00269** (TRUE, FN, inv 20): ThingFactory `getattr` → Any receiver → `thing.doSomething(param)` unresolved.
- **00349, 00658** (FALSE, FP, inv 16): dict key-insensitivity (store keyB(param), read keyA(const)).
- **00508, 00513, 00608, 00995** (FALSE, FP, inv 18): path-insensitive match/if-else/ternary (const-selected
  safe arm, tainted arm still explored).
- **00826** (FALSE, FP, inv 19): list index-insensitivity (append(param), pop(0), read lst[1]).

### Pass-throughs added: `base64.urlsafe_b64decode` (arg(0)+kwarg(s)→result).

### inv 29 — RESOLVED (00605): char-rebuild element-drop + per-entry `[...]` workaround
- **Symptom.** 00605 (deser, CWE-502) was a FN: tainted `param` flows through user helper
  `helpers.utils.escape_for_html`, whose body rebuilds the string char-by-char (`ret = ''; for c in s: ret += c;
  return ret`) before the result reaches `pickle.loads`. The single-`[...]` source taints the whole string
  object; `for c in s` is a NextIter read that the concrete whole-object fact does NOT survive (inv-25 family:
  `mayReadAccessor(values, ElementAccessor)` false — fact starts `TaintMarkAccessor`, not `ElementAccessor`, and
  isn't `isAbstract()`), so `c` — and thus `ret` — is untainted. VERIFIED earlier: a call-arg probe
  (`… escape_for_html($A)` as sink) FIRED, so taint reaches the call; the drop is strictly inside the body. A
  `config.yaml` passThrough on `escape_for_html` had NO effect (config can't override an analyzed user fn).
- **Fix (per-entry, rule-only).** Add one MORE subscript to the collection-accessor source:
  `flask.request.headers.getlist(...)[...]` → `…getlist(...)[...][...]`. This pushes the source mark one element
  level deeper — to the character level — so the mark that reaches `escape_for_html`'s `s` already lives on the
  element the NextIter reads, survives `for c in s`, propagates to `c`→`ret`, and reaches `pickle.loads`. 00605
  now PASSES; suite green.
- **Emitted-rule proof (CARDINAL 5, `PythonRuleEmitTest` throwaway probe, now removed).** For the same
  source+sink, dumping `source.taint.map { it.pos }`:
  - single `getlist(...)[...]`  → `taint=[WithModifiers(base=Result, modifiers=[ArrayElement])]`  (`Result[*]`)
  - double `getlist(...)[...][...]` → `taint=[WithModifiers(base=Result, modifiers=[ArrayElement, ArrayElement])]` (`Result[*][*]`)
  Exactly ONE extra `ArrayElement` — genuinely one element level deeper, as intended. (The double-subscript source
  path is the same `transformAssignmentValue` merge locked by inv 25's `PythonRuleEmitTest` regressions.)
- **Rule of thumb.** Add one `[...]` per element-read / iteration hop between source and sink; verify by re-running.
- **Caveat — per-entry SAFE, does NOT generalize.** Do NOT apply where the element-read/char-rebuild is a
  *legitimate sanitizer*. In xss especially, `escape_for_html` / `html.escape` ARE the real sanitizers and you
  WANT the drop — deepening the source there would defeat sanitization and FP. Here the helper only *copies*
  (no escaping), so the drop is a pure engine artifact, making the workaround sound for THIS entry only.
- **Engine-fix candidate** (removes the need for the manual `[...]`): propagate concrete whole-object taint
  through NextIter / element reads (same fix as inv 25).

## pathtraver round (CWE-22, 46 entries) — ALL STRUCTURAL rules

Sinks (per entry, threading `$A`): `open($A, ...)`, `codecs.open($A, ...)`, `os.path.exists($A)` (path on
arg0 — the `f'{DIR}/{bar}'` f-string carries the mark), and pathlib **receiver-position** `$A.exists(...)`
(`p = testfiles / bar` — `/` is a NATIVE binop that propagates taint into `p`, so a metavar-receiver sink
checks This on `p`). Sources: cookies/form `.get`, `.form.getlist(...)[...]`, `.form.keys(...)[...]` loop,
`get_form_parameter` wrapper (inv 26 → `flask.request.form.get`). **Suite after round: 317 tests, 0 fail,
126 skipped (191 pass).** Batch = 20 active pass (16 TRUE + 4 FALSE) + 26 `@Disabled`.

### Active TRUE (16, pass): 00001 00002 00008 00085 00087 00089 00171 00172 00173 00175 00178 00180 00273 00277 00351 00353
Direct/if/if-else/dict-same-key/configparser-same-key/string-concat+slice/base64-roundtrip/getlist[...]/
keys-loop/wrapper flows into `open`/`codecs.open`/`os.path.exists`/`pathlib $A.exists`. 00002 (`if 'should' in
bar: bar=param`) and 00008/00085 (`if 'should' not in TestParam: safe else bar=param`) reach path-insensitively.

### Active FALSE (4, pass via concrete-taint-drop at `.resolve()`): 00090 00091 00181 00276
pathlib `p = (testfiles / bar).resolve()`: `.resolve()` is an UNMODELED call that drops the CONCRETE taint
(inv 6 / inv 25 family), so `p.exists()` isn't reached. NOT a robust sanitizer model (they FP once inv-25 is
fixed) — mirrors prior-round accepted taint-drop passes (00991/01173). Their true approximation reason is
inv 19 (00090 list) / inv 18 (00091 ternary, 00181 match) / inv 16 (00276 configparser keyA).

### @Disabled — FN inv 20 (2): 00003 00177
ThingFactory `thing.doSomething(param)` getattr → Any receiver → unresolved (same as prior rounds).

### RESOLVED — build gap (6): 00009 00010 00092 00093 00094 00182  (2 TRUE + 4 FALSE)  (inv 31)
FIXED in `a4d733729`: `ClosureAnalyzer` was treating unresolved free names (undefined `e`/`fileName` in the
dead `except OSError:` block) as closure captures, breaking closure lowering so the POST function never
serialized ("Entry point not found"). Not read_text-specific — the malformed except block was the trigger.
All 6 now build and all 6 PASS with correct verdicts (verify-and-triage, no rule changes needed):
- 00092 TRUE reaches: `param = form.get(...)` → dict same-key (keyB store/read) → `bar` → `p = testfiles / bar`
  (native binop, keeps taint, inv 30) → `p.read_text()` receiver tainted → sink fires. assertReachable ✓.
- 00182 TRUE reaches: `getlist(...)[...]` element source → `values[0]` → str concat+slice `[4:-17]` → `bar`
  → `testfiles / bar` → read_text. Concrete taint survives the concat/slice hops here. assertReachable ✓.
- 00009/00010 FALSE: source wrapped in `urllib.parse.unquote_plus(request.cookies.get(...))` — the unmodeled
  `unquote_plus` drops the concrete mark → param never tainted. Plus `.resolve()`. assertNotReachable ✓.
- 00093/00094 FALSE: `param = form.get(...)` tainted, but `p = (testfiles / bar).resolve()` — the unmodeled
  `.resolve()` drops concrete taint (inv 30) → read_text receiver untainted. assertNotReachable ✓.
No taint-triage fixes required; the hand-authored rules were already correct once the function serialized.

### @Disabled — FP approximation-limited (18)
No FALSE pathtraver variant has a unifiable validator CALL: the guards are `'../' in bar` (a `Contains`
operator) and `str(p).startswith(str(testfiles))` (receiver-position on `str(p)`, not `bar`) — neither is a
callable validator, so the inv-23 unified-`$M` trick doesn't apply.
- inv 18 path-insensitive const if/else/ternary/match: 00004 00086 00088 00095 00174 00176 00184 00274 00352 00354.
- inv 18/23 substring `'../' in bar` guard (dict-same-key 00005 / string-concat 00007 stay tainted): 00005 00007.
- inv 19 list index-insensitivity (append/pop/`lst[i]`): 00006 00179.
- inv 16 configparser/dict key-insensitivity (set keyB(param), read keyA(const)): 00170 00183 00355.
- inv 18 + wrapper ABSTRACT taint survives `.resolve()` (unlike the 4 concrete passes above): 00275.

### No pass-throughs / engine changes this round.
Verified `/` (truediv) is a native binop (a `pathlib.Path.__truediv__` passThrough is inert — never resolved
as a call) and NO TRUE entry uses `.resolve()`, so the initially-added pathlib passThroughs were removed as
unnecessary. Receiver-position sinks (`$A.exists(...)`) fire correctly (metavar receiver → This-position
`ContainsMark`, resolveReceiver → IsMetavar).

## pathtraver round batch 2 (CWE-22, 00356-00616, 40 entries) — ALL STRUCTURAL
Same sink family as batch 1. New source shapes, all resolve like the form.* ones (inv 2 last-segment):
`request.headers.get(...)` → `flask.request.headers.get(...)`; `request.headers.getlist(...)[...]` →
`flask.request.headers.getlist(...)[...]`; `for name in request.headers.keys(): if request.headers.get_all(name): param=name`
keys-loop (inv 15) → `flask.request.headers.keys(...)[...]`; and `request.form.keys()` loop → `flask.request.form.keys(...)[...]`.
Suite after round: **357 tests, 0 fail, 141 skipped (216 pass)** (+40: +18 active pass, +22 @Disabled).
- **Active TRUE (12 reach):** 00357 00438 00439 00444 00445 00449 00516 00523 00529 00610 00613 00615
  (dict-keyB / concat+slice / match-arm-param / ternary-else-param / list / configparser-keyB all keep taint into open/codecs.open/os.path.exists/pathlib $A.exists).
- **Active FALSE (6 pass):** 00446 00448 00527 00528 00616 via `.resolve()` concrete-taint-drop (inv 30);
  **00524 via ThingFactory FN (inv 20)** — the getattr FN leaves `bar` untainted so the FALSE entry correctly
  does NOT reach (a FALSE ThingFactory entry passes for free; only TRUE ThingFactory entries FN → @Disabled).
- **@Disabled FN inv 20 (3, ThingFactory TRUE):** 00517 00526 00612.
- **@Disabled FP approximation-limited (19):** inv 18 path-insensitive if/else/ternary/match:
  00356 00360 00441 00442 00525 00530 00611; inv 18/23 `'../' in bar` substring guard (concat/dict/match arm stays tainted):
  00440 00518 00520 00522; inv 19 list index-insensitivity: 00359 00443 00519 00521 00614; inv 16 dict/configparser
  key-insensitivity (read keyA-const, no `.resolve()` drop): 00358 00361 00447.
- **No pass-throughs / engine changes** (all 12 TRUE reached; no new dropped external methods on TRUE paths).

## pathtraver round batch 3 (CWE-22, 00617-00911, 40 entries) — ALL STRUCTURAL
Same sink family (open / codecs.open / os.path.exists / pathlib `$A.exists`|`$A.read_text`). Sources: headers.keys[...]
loop (00617-00620), `request.args.get` (00661-00667), `request.args.getlist(...)[...]` (00737-00751),
`get_query_parameter` wrapper → `flask.request.args.get` (00831-00838), and NEW **`request.query_string`** source
(00906-00911) → `flask.request.query_string`. Suite after round: **397 tests, 0 fail, 156 skipped (241 pass)**
(+40: +25 active pass, +15 @Disabled). Batch = 18 active TRUE + 7 active FALSE + 15 @Disabled.
- **Active TRUE (18 reach):** 00618 00619 00620 00662 00665 00667 00737 00739 00741 00742 00749 00750 00751 00831
  00835 00906 00907 00910 (configparser-keyB / dict-keyB / base64-roundtrip / match-arm-param / ternary-else-param /
  list-lst[0] / query_string all keep taint into open/codecs.open/pathlib `$A.exists`).
  **00742/00751 confirm concrete getlist[...] element taint SURVIVES list append→`lst[0]`** into the pathlib/open sink.
- **NEW query_string source works (00906/00907/00910 TRUE reach):** `flask.request.query_string` → `.decode('utf-8')`
  (bytes.decode passThrough) → **string slicing `qs[a:]`/`p[:b]`** → `urllib.parse.unquote_plus` (arg0→result passThrough,
  already in config.yaml — the old "unquote_plus DROPS" note is STALE) → param. Concrete taint survives the whole chain
  incl. the slices (whole-string slice does NOT drop, unlike an element read). No rule/config change needed.
- **Active FALSE (7 pass):** 00617 00664 00744 00746 00747 00748 via `.resolve()` concrete-taint-drop (inv 30, real
  reasons inv 16/18); **00833 via ThingFactory FN (inv 20)** — getattr leaves `bar` untainted → correctly not-reached.
- **@Disabled FN inv 20 (1, ThingFactory TRUE):** 00834 (`os.path.exists` sink; getattr `thing.doSomething(param)` unresolved).
- **@Disabled FP approximation-limited (14):** inv 18 path-insensitive match-arm/ternary/if-else: 00666 00738 00832 00837
  00838 00909; inv 18/23 `'../' in bar` substring guard (bar/base64 stays tainted): 00663 00740 00911; inv 19 list
  index-insensitivity (read lst[1]): 00743 00908; inv 16 configparser key-insensitivity (set keyB, read keyA-const, no
  `.resolve()` drop): 00661 00745; inv 18+inv 30 wrapper ABSTRACT taint survives `.resolve()` (match arm): 00836.
- **No pass-throughs / engine changes** (all 18 TRUE reached; unquote_plus/bytes.decode/base64 passThroughs already present).

## pathtraver round batch 4 (CWE-22, 00912-01222, 42 entries — FINAL) — ALL STRUCTURAL
**pathtraver is now COMPLETE (all 168).** Same sink family (open / codecs.open / os.path.exists / pathlib
`$A.exists`|`$A.read_text`). Sources: `request.query_string` (00912-00922), `request.form.get`/`.getlist[...]`/
`.keys()` loop (01179/01183/01192), `request.headers.get` (01196), `request.args.get` (01202), `get_query_parameter`
wrapper → `flask.request.args.get` (01214, inv 26). Suite after round: **439 tests, 0 fail, 162 skipped (277 pass)**
(+42: +36 active pass, +6 @Disabled). Batch = 11 active TRUE + 25 active FALSE (pass-free) + 6 @Disabled.
- **Active TRUE (11 reach):** 00914 00915 00916 00918 00920 (query_string → configparser-keyB / if-not-in-else /
  concat+slice into open/pathlib exists/read_text), 01179 01181 01183 01196 (form.get/getlist[...]/headers.get direct
  → open/os.path.exists), 01192 (form.keys loop → pathlib read_text), 01214 (get_query_parameter wrapper → read_text).
- **Active FALSE pass-free (25):**
  - **request.path source (inv 17, NOT a source) — 13 free:** 01004 01005 01006 01007 01008 01009 01010 01011 01012
    01013 01220 01221 01222. Code reads `parts=request.path.split("/"); param=parts[1]` — server-controlled route,
    never tainted. Modeled with a non-matching bare-attr source (`flask.request.query_string`) → source never binds.
  - **`get_safe_value` const-wrapper source (inv 33, NEW) — 10 free:** 01105 01106 01107 01108 01109 01110 01111 01112
    01113 01114. `request_wrapper.get_safe_value()` returns literal `"bar"` (unlike get_form/query_parameter) → param
    never tainted. Same non-matching-source modeling as inv 17.
  - **query_string source but taint-drop — 2 free:** 00919 (ThingFactory `thing.doSomething(param)` getattr FN, inv 20
    → bar untainted), 00921 (ternary bar + `(testfiles/bar).resolve()` concrete-taint-drop, inv 18/30).
- **@Disabled FP approximation-limited (6):** inv 16 configparser keyA-const read (no `.resolve()` drop): 00912;
  inv 18 path-insensitive const if/else (tainted else explored): 00913; inv 18/23 `'../' in bar`/`'../' in param`
  substring guard (bar=param direct stays tainted): 00917 01180 01202; inv 19 list index-insensitivity: 00922.
- **No pass-throughs / engine changes** (all 11 TRUE reached; query_string/unquote_plus/bytes.decode chain already modeled).
- **NEW (inv 33):** `get_safe_value` returning a literal is a genuine non-source; for FALSE query_string/path/const-wrapper
  entries use a bare-attribute source (`flask.request.query_string`) — no `.get` last-segment collision with configparser.get.

## xpathi batch 1 (CWE-643, 40 entries) — 14 active pass / 26 @Disabled / 0 fail

- **Sinks (all fire, last-segment inv 3):** `elementpath.select($ROOT, $A)` (2nd/query arg), `lxml.etree.XPath($A)`
  (compile-time sink, arg0 — the `run_query = XPath(query)` compilation is where injection is flagged), `$T.xpath($A)`
  (receiver metavar, arg0). Rule shape = pathtraver's `$A = <src>(...)` ... `<sink>(...$A...)`; the query is built by an
  f-string / `"".join([...,bar,...])` that carries the mark. VERIFIED reachable: 00018/00104 (XPath), 00101/00197/00198
  (select), 00107/00207/00210/00211 (xpath).
- **Sources:** cookies.get(unquote_plus) / form.get / form.getlist(...)[...]; all copied from pathtraver templates.
- **str.replace is NOT a cleaner (FP):** `bar.replace("'", "&apos;")` resolves last-segment `replace` → `copy.replace`
  passThrough → PROPAGATES taint. VERIFIED: 00199 (bar=param direct, only replace before sink) reaches. @Disabled the
  apostrophe-escape FALSE variants 00108/00109/00199/00200/00202. (Contrast inv 30 `.resolve()` which DROPS — the
  difference is a matching last-segment passThrough exists for replace.)
- **io.StringIO DROPS taint (FN):** `strIO.write(bar); q = strIO.getvalue()` loses the mark (needs arg→receiver→result,
  which passThrough can't express). @Disabled TRUE 00112/00113; FALSE 00024 (StringIO after configparser) passes free.
- **FALSE pass-free:** 00023/00111 parameterized `xpath(query, name=bar)` (bar in kwarg, const query); 00201 ThingFactory
  getattr FN (inv 20) leaves bar untainted; 00024 StringIO drop.
- **FALSE FP @Disabled (approximation-limited):** dict key-insens inv 16 (00020/00102/00193); list index-insens inv 19
  (00013/00195/00208); path-insens const if/else & ternary inv 18 (00105/00106/00194); match arm inv 18 (00196); and the
  `'` apostrophe substring-guard variants (inv 18/23, guard is `if "'" in bar: return`, an operator not a callable
  validator → not unifiable): 00014/00015/00016/00021/00022/00110/00203.
- **TRUE FN @Disabled:** 00103/00209 ThingFactory getattr (inv 20); 00112/00113 StringIO drop.
- **No pass-throughs / engine changes.** configparser .set/.get flows key-insensitively as before (00104 TRUE reaches).

## xpathi batch 3 (CWE-643, 00468-00761, 40 entries) — 17 active pass / 23 @Disabled / 0 fail

- **All inv 34 patterns re-confirmed; no new invariant, no rule/engine/passthrough changes.** Sinks: `$T.xpath($A)`,
  `lxml.etree.XPath($A)` (00545/00546), `elementpath.select($ROOT,$A)`. Sources: `headers.get` (00468-00472),
  `headers.getlist[...]` (00534-00555), `args.get` (00674-00687), `args.getlist[...]` (00756-00761). Query built by
  f-string / `"".join([...,bar,...])` / `'..'+bar+'..'` — all carry the mark.
- **TRUE active pass (10):** 00534/00535/00536 (dict-keyB/match-arm/ternary → select), 00543 (if 'should' in bar → param),
  00545/00546 (if-else / ternary → XPath compile), 00674/00682 (list index-insens lst[0]=param genuinely tainted → reach),
  00681 (if-else else=param), 00760 (configparser get keyB(param, tainted)).
- **FALSE active pass-free (7):** parameterized `xpath(query, name=bar)` const query, bar in kwarg → query-arg sink never
  binds (00469/00470/00553/00686/00687); StringIO drop (00471); ThingFactory getattr FN leaves bar untainted (00677).
- **TRUE FN @Disabled (4):** StringIO drop 00554/00555 (inv 34); ThingFactory getattr 00761 (inv 20); 00472 both.
- **FALSE FP @Disabled (19):** replace-not-cleaner inv 34 (00537/00548/00675/00676/00683/00756/00757); dict/configparser
  key-insens inv 16 (00542/00551/00683); list index-insens inv 19 (00547/00676); const if/else + ternary + match path-insens
  inv 18 (00468/00544/00548/00680); `'` apostrophe substring guard (operator, not unifiable) inv 23 (00468/00549/00550/
  00552/00684/00685/00758). Most stack two safety mechanisms (e.g. key-insens + replace, path-insens + apostrophe).

## xpathi batch 4 (CWE-643, 40 entries, FALSE-heavy: 6 TRUE) — 18 active pass / 22 @Disabled / 0 fail

- **All inv 34 patterns re-confirmed; no new invariant, no rule/engine/passthrough changes.** Sinks: `$T.xpath($A)`,
  `elementpath.select($ROOT,$A)`, `lxml.etree.XPath($A)`. Sources: `args.getlist[...]` (00762-00764), wrapper
  `helpers.separate_request.request_wrapper(request).get_query_parameter` → canonical `flask.request.args.get(...)`
  (00843-00858, inv 26), `flask.request.query_string` (00927-00944, inv 32), `request.path` FALSE entries modeled with a
  non-matching `flask.request.query_string` source (01022-01030, inv 17/33, same as pathtraver 01004+).
- **TRUE active pass (3):** 00854 (`if 'should' not in TestParam` → else bar=param genuinely tainted), 00932 (list
  lst[0]=param genuine after pop(0)), 00933 (`s='help'; s+=param; s+='...'; bar=s[4:-17]` — string concat + slice keeps
  taint → reaches).
- **FALSE active pass-free (15):** StringIO drop 00764 (inv 34); kwarg `xpath(query, name=bar)` const query, bar in kwarg,
  query-arg sink never binds (00856/00857/00939/00940/00941/00942/00943, inv 34 — 00939/00942 have genuinely-tainted bar,
  still pass free via kwarg); request.path never-tainted (01022/01023/01026/01027/01028/01029/01030, inv 17/33).
- **TRUE FN @Disabled (3):** ThingFactory getattr 00844 (inv 20); io.StringIO drop 00858/00944 (inv 34).
- **FALSE FP @Disabled (19):** replace-not-cleaner inv 34 (00763/00845/00846/00847/00927/00937/00938); configparser/dict
  key-insens inv 16 (00843/00853/00938); list index-insens inv 19 (00934/00936); const if/else + ternary + match path-insens
  inv 18 (00762/00763/00847/00852/00929/00935); `'` apostrophe substring guard (operator, not unifiable) inv 23 (00848/
  00849/00855/00928/00929). Several stack two mechanisms (key-insens + replace, path-insens + apostrophe).

## io.StringIO passThrough fix (supersedes "StringIO DROPS taint" in inv 34 / batches 1-4)

- **Root cause corrected:** the StringIO drop was NOT unexpressible — it was a MISSING passThrough. The
  write-into-object / read-back pattern is the same one `queue.Queue.put`/`.get` already model. Added to
  `config.yaml` (pass-through-only file):
  - `io.StringIO.write` → `from arg(0) to this`, `from kwarg(s) to this`
  - `io.StringIO.getvalue` → `from this to result`
  Last-segment matching (inv 3) means these fire on any `.write(...)`/`.getvalue(...)` call; no over-tainting
  observed in the re-run (suite stayed green). No BytesIO entry exists in the benchmark, so BytesIO not added.
- **TRUE FN re-enabled as `assertReachable` (all pass):** 00112 00113 (b1), 00217 00304 (b2), 00554 00555 (b3),
  00858 00944 (b4), 01218 (b5). StringIO was their sole blocker; they now reach.
- **FALSE that only passed because StringIO dropped — now FP, @Disabled on the underlying approximation:**
  00024 (configparser key-insens, set keyB(param)/get keyA(const), inv 16); 00471 (path-insens match arm,
  const guess 'B' safe, tainted 'A'/'C' arms explored, inv 18); 00764 (dict key-insens, store keyB(param)/read
  keyA(const), inv 16).
- **00472 stays @Disabled but reason narrowed to inv 20 alone:** `bar = thing.doSomething(param)` (ThingFactory
  getattr, Any receiver, doSomething unresolved) leaves bar untainted regardless of StringIO.
- **Suite after fix:** 665 tests, 372 pass, 293 skipped, 0 fail, 0 error.

## xpathi batch 5 (CWE-643, FINAL — completes all 186) — 22 active pass / 4 @Disabled / 0 fail

All verdicts re-confirm existing invariants; no new invariant discovered.
- **22 active assertNotReachable (pass-free):**
  - request.path FALSE + get_safe_value const-wrapper (returns literal "bar") → NON-MATCHING bare-attribute
    source `flask.request.query_string` (inv 17/33): 01031-01039, 01116-01121, 01123-01125, 01225, 01226.
  - kwarg-const-query sink (inv 34): real matching source but `xpath(query, name=param)` has CONST arg0 →
    `$T.xpath($A)` binds the const query, never param → free: 01184 (form.getlist), 01204 (args.get).
- **4 @Disabled (all verified by run — sink message direction confirmed):**
  - **01218 TRUE FN** — io.StringIO write/getvalue drops taint (inv 34); "sink was not reached".
  - **01175 FALSE FP** — cookies.get tainted, safe only via `str.replace("'","&apos;")` apostrophe-escape
    which resolves to `copy.replace` passThrough and PROPAGATES (inv 34).
  - **01198/01217 FALSE FP** — headers.getlist/query_string tainted, safe only via `'` apostrophe substring
    guard (`if '\'' in param: return`), an operator with no unifiable validator call (inv 23).

## xss batch 1 (CWE-79, 40 entries) — CATEGORY BLOCKED: return-value-sink engine gap (inv 35)

**Sink-spike verdict (VERIFIED, headline):** the XSS sink is the returned HTTP **response body**, built as
`RESPONSE += f'...{bar}...'` then a **bare `return RESPONSE`** from the Flask route handler. There is NO
`render_template_string(...)` / `make_response(...)` / `.write(...)` CALL carrying the body (`make_response`
appears only in the `from flask import ...` line; the 8 entries that do call it —
00149/00150/00256/00257/00334/00335/00414/00493, all FALSE — pass `bar` into a HEADER dict
`make_response((RESPONSE, {'h': bar}))`, not the XSS body). All 16 TRUE entries have only `return RESPONSE`.

A structural sink `return $A` does **not fire**: `PythonPatternToActionListConverter.transformReturn` lowers
a return to a `MethodExit` action, and `PythonTaintRuleGeneration.emitPythonTaintRules` handles a sink edge
(`edgesToFinalAccept`) with `Kind.MethodExit` by `ctx.trace.error("Non method call sinks are not supported
yet")` — emitting ZERO sinks (line ~78-80). Sinks fire only at calls / attribute reads
(`PIRMethodCallFlowFunction.applySinkRules`). Same shape as the trustbound store-sink gap (inv 28): a whole
category blocked by an unsupported **sink kind**, not a rule bug.

**Reproducer:** `PythonRuleEmitTest.return-value sink emits no sink (engine gap)` + resource
`python-rules/return-sink.yaml` (`$A = source(...) ... return $A`): asserts the source lowers (1
SerializedPythonSource) but ZERO SerializedPythonSink. Flips to non-empty when return-value-sink support
lands — the signal to enable the 40 @Disabled xss entries.

**Action:** all 40 xss entries added to `OwaspBenchmarkTest.kt` as `@Disabled` `@Test` (16 assertReachable /
24 assertNotReachable per ground truth) citing inv 35. No per-entry rule yaml authored (would be doomed;
would need the same return-sink form). The FALSE half is sanitized by `escape_for_html`/`html.escape`/
`markupsafe.escape` — genuine sanitizers we WANT to drop — but that is moot until the sink can fire at all.

**Fix (engine phase):** emit + fire a return-value sink. Converter: in `emitPythonTaintRules`, map a
`Kind.MethodExit` accept-edge to a new "return sink" (check `ContainsMark` on the returned value / `Result`
position) instead of erroring. Engine: check that sink at the method-exit / `return` instruction. Then
enable the xss block and triage the FALSE half (model the html-escape sanitizers as cleaners).

**Next xss batch: HOLD — category blocked, defer all ~89 xss entries until the return-value-sink engine
phase.** Do not spend rounds authoring xss rules that cannot fire.

---

## securecookie (CWE-614) — SPIKE-PILOT, EXPRESSIBLE, 39/39 active-pass (inv 36)

**Verdict: YES — structural securecookie both LOWERS and FIRES.** Unlike trustbound (inv 28 store-sink) and
xss (inv 35 return-sink), which are blocked by unsupported sink KINDS, securecookie's sink is an ordinary
call (`RESPONSE.set_cookie(...)`) with a distinguishing kwarg. All 39 entries pass as active `@Test`s
(24 assertReachable / 15 assertNotReachable); zero `@Disabled`.

**The shape (uniform across all 39, auto-generated OWASP files).** Every POST handler:
`RESPONSE = make_response(RESPONSE)` then `RESPONSE.set_cookie(cookie, value, path=request.path,
secure=False|True, httponly=True)`. TRUE (vulnerable) = `secure=False` (all 24, explicit — none absent);
FALSE (safe) = `secure=True` (all 15). A request-derived `value` flows in, but CWE-614 is about the flag,
not the value — so we do NOT rely on the value taint (which passes through `escape_for_html`/`encode`/
`decode`, fragile).

**Working rule (identical for every entry, only the `id` differs):**
```yaml
patterns:
  - pattern: |
      $RESP = flask.make_response(...)
      ...
      $RESP.set_cookie(..., secure=False, ...)
```

**Why it works — self-source + positive kwarg const-compare (the two design keys):**
1. **Self-source on the response object.** There is no taint source, so we declare `flask.make_response`
   one: it lowers to a source tainting its `Result` (bound to `$RESP`). The mark rides the response object
   to the immediate `set_cookie` receiver (same var, no intervening rebind) — robust, independent of the
   cookie value's taint. This is the "self-contained sink" idea (prompt step 1) realized via the receiver.
2. **Positive `secure=False` match in the SINK, not a `pattern-not` cleaner.** The emit
   (`PythonRuleEmitTest.securecookie make_response self-source…`) shows the sink checks `ContainsMark(This)`
   (receiver, inv 30) AND `ConstantCmp(kwarg(secure)==False)`. Because all TRUE are `secure=False` and all
   FALSE are `secure=True`, a positive const-compare discriminates perfectly: TRUE fires, FALSE fails the
   compare and is excluded — no cleaner required. This deliberately AVOIDS the `pattern-not`/cleaner path
   that `@Ignore`s `RuleCookie` (its `$C.set_secure(True)` cleaner needs must-alias to kill the receiver
   fact — inv 27 receiver-cleaner gap). We never hit that gap.

**Kwarg gap — NOT hit.** The "semgrep kwarg gap" (kwarg names dropped to AnyArgument) is FIXED for
structural const-compares: the emit test confirms `secure=False` lands on `kwarg(secure)`, not `arg(*)`
(same fix as `kwarg-structural`/`kwarg-not-cleaner`). So True/False are distinguishable.

**VERIFICATION performed (CARDINAL 5):**
- Emit dump (`emitAll`): `sources=1 sinks=1 cleaners=0`; source `flask.make_response`→`Result`; sink
  `set_cookie` `marks=[This]` + `consts=[KwArgument(secure)]`.
- Engine trace (`System.err.println` in `applySinkRules`): `callee=[set_cookie] rules=1` — the sink rule
  reaches the `set_cookie` call.
- Suite: 00064 (secure=False) assertReachable PASS; 00337 (secure=True) assertNotReachable PASS; then all
  39 PASS. Full OWASP suite: 704 tests, 411 pass / 0 fail / 293 skipped (was 372 pass; +39 all active).

**Reproducer / tripwire:** `python-rules/securecookie-probe.yaml` +
`PythonRuleEmitTest.securecookie make_response self-source and secure=False sink lower` (a POSITIVE lock —
asserts the source and the receiver+kwarg sink DO lower, the inverse of the inv 28/35 "emits no sink"
tripwires).

**Recommendation on hash (CWE-328) / weakrand (CWE-330).** Both look expressible with the SAME self-source
recipe and should be pursued — likely EASIER than securecookie:
- These are "dangerous call configuration", not data flow. Model the dangerous call as its own self-source
  AND sink, e.g. `$H = hashlib.md5(...)` (weak-hash) or `random.random()`/`random.randint(...)` used for a
  security value. The sink is a plain call (or the constructor call itself), with NO kwarg discrimination
  needed — simpler than set_cookie's `secure=` compare.
- Open question to verify first (spike, don't assume): whether a single call must be BOTH source and sink
  (self-loop) — if `hashlib.md5(x)` is the whole vuln, the "source" and "sink" coincide on one call. Test
  whether the loader lowers a one-call source+sink and whether the engine fires a sink on the same call it
  sources (dump emit + trace, as here). If a single-call self-sink doesn't fire, fall back to sourcing the
  hashed/random VALUE and sinking where it's used (`.hexdigest()`, `.update(...)`, etc.). Either way the
  sink is a call, so neither is blocked by the inv 28/35 sink-kind gaps. Worth a spike-pilot each.

---

## hash (CWE-328) — batch 1 (50 entries), spike + round (inv 37)

**VERDICT: EXPRESSIBLE, all 50 active-pass, 0 @Disabled.** Confirms the inv-36 corollary. The self-source
recipe works; the "one call is BOTH source and sink" open question did NOT arise — the vuln spans two calls
(`$H = hashlib.<algo>(...)` then `$H.update(...)`), so source (the hash-object constructor) and sink
(`.update` on the receiver) are naturally distinct. No self-loop needed.

**Working rule (identical for every entry — TRUE and FALSE):** one `pattern-either` over the four weak
shapes (see inv 37 for the yaml). `pattern-either` lowers to N independent source+sink pairs.
- Shape A `hashlib.new('md5'/'sha1')`: source `hashlib.new`→Result guarded by POSITIVE
  `ConstantCmp(arg(0)==algo) AND NumberOfArgs(1)`. Strong algos fail the compare → not sourced.
- Shape B `hashlib.md5()`/`hashlib.sha1()`: source is the function name; strong algos don't match the callee.
- Sink `$H.update(...)` = `ContainsMark(This)` (receiver).

**Batch shape/algo survey (all 50):**
- Shape A (`hashlib.new('...')`): TRUE 00054(md5) 00244(sha1) 00319(md5) 00320-00323(sha1) 00409(md5)
  00410(sha1); FALSE 00055(sha384) 00056(sha512) 00245-00246(sha384) 00247(sha512) 00324-00325(sha512)
  00411(sha384).
- Shape B (`hashlib.md5()/sha1()`): TRUE 00057(md5) 00058-00060(sha1) 00140-00141(md5) 00142-00143(sha1)
  00248-00249(md5) 00250-00251(sha1) 00326-00327(md5) 00328-00329(sha1) 00412(md5); FALSE all sha384/sha512.
- No sub-shape needed special handling; no kwargs involved (positional const on shape A, callee name on B).

**VERIFICATION (CARDINAL 5):**
- Emit dump (`emitAll` on `hash-probe.yaml`): shape-A source `hashlib.new`→Result +
  `ConstantCmp(arg(0)=='md5'/'sha1')`; shape-B source `hashlib.md5`/`hashlib.sha1`→Result (no cond); every
  sink `update` with `ContainsMark(This)`. `pattern-either` → one independent pair per branch.
- Suite (firing proof): full OwaspBenchmarkTest 754 tests, 461 pass / 0 fail / 293 skipped (was 411 pass
  post-securecookie; +50 all active). All 50 hash IDs pass; 0 skipped among them.

**Tripwire:** `python-rules/hash-probe.yaml` +
`PythonRuleEmitTest.hash weak-digest rule lowers to per-algo self-source and update sink pairs` (POSITIVE
lock — asserts the per-algo const-compare sources and the receiver `.update` sink lower).

**Recommended next hash batch.** This batch = the 50 entries listed in the task ground truth. The hash
category has ~151 total; the remaining ~101 IDs (all outside the 50 above, in the hash-* benchmark routes)
should reuse the identical `hash-probe`-style `pattern-either` rule verbatim — survey each only to confirm
it's shape A or B with md5/sha1 (TRUE) vs sha256/384/512/blake2 (FALSE); no new rule form expected. Watch
for any `.hexdigest()`-only entry with no `.update()` call (add a `$H.hexdigest(...)` sink branch if found)
and any `hashlib.new(<algo-in-a-variable>)` non-literal (const-compare can't fire → would need @Disable).

---

## weakrand (CWE-330, insecure randomness) — batch 1 (50 entries), inv 38

**Rule form (structural, identical for every entry — template inv 37):** `pattern-either` over the weak
Mersenne-Twister fns, each nested in the universal `str(...)` wrapper:
```yaml
patterns:
  - pattern-either:
      - pattern: str(random.normalvariate(...))
      - pattern: str(random.randint(...))
      - pattern: str(random.getrandbits(...))
      - pattern: str(random.random(...))
      - pattern: str(random.randbytes(...))
```
Lowers to a self-source `random.<fn>`→Result (no condition) + a generic `str($T)` sink =
`ContainsMark(Argument(0))`. No `.update`-style receiver sink exists (RNG consumed inline as
`value = str(random.<fn>(...))[...]`); `str` is the common outer wrapper for all 11 TRUE. randbytes
(`str(base64.b64encode(random.randbytes(32)))`) reaches the `str` sink via the pre-existing
`base64.b64encode` arg(0)→result passthrough in config.yaml.

**Weak fns matched (this batch):** `normalvariate`, `randint`, `getrandbits`, `random`, `randbytes`.

**Per-entry disposition (verified by reading each `value =` line — the prompt's SystemRandom guess was WRONG):**
- **TRUE (11, active pass):** 00025/00026 normalvariate · 00027/00028/00116 randbytes(+b64) · 00029/00030/00031
  randint · 00114/00115 getrandbits · 00117 random.
- **FALSE secrets.\* (23, active pass — cleanly excluded, distinct last segments):** 00032/00033/00034/00035
  /00118/00119 randbelow · 00036/00037/00038 randbits · 00039/00040/00041/00120–00125 token_bytes ·
  00042/00126/00127 token_hex · 00043/00128 token_urlsafe.
- **FALSE SystemRandom CSPRNG (16, `@Disabled` — last-segment collision, inv 38):** 00044/00045/00046/00129
  /00130/00131 getrandbits · 00047/00048/00132/00133 normalvariate · 00049/00134 randbytes · 00050/00051
  randint · 00052/00053 random. `random.SystemRandom().<fn>()` → `PIRSimpleNameUnknownFunction:<fn>` (ctor
  return type unresolved) → `matchesName` last-segment match vs `random.<fn>` → source FIRES → FP. No
  rule-level knob forces qualified-only matching → unfixable structurally.

**VERIFICATION (CARDINAL 5):**
- Emit dump (`emitAll` on `weakrand-probe.yaml`): 5 self-sources `random.{normalvariate,randint,getrandbits,
  random,randbytes}`→Result; `str` sinks with `ContainsMark(Argument(0))`. `pattern-either` → one pair per branch.
- Spike suite+trace (4 entries): 00114 (getrandbits TRUE) PASS, 00025 (normalvariate TRUE) PASS, 00032
  (secrets FALSE) PASS, 00044 (SystemRandom FALSE) FAILED → collision. Trace: `random.getrandbits` →
  `PIRQualifiedUnknownFunction srcRules=1`; SystemRandom → `PIRSimpleNameUnknownFunction:getrandbits srcRules=1`.
- Full suite: OwaspBenchmarkTest 905 tests, 596 pass / 0 fail / 309 skipped. All 34 active weakrand IDs pass;
  16 SystemRandom skipped.

**Tripwire:** `python-rules/weakrand-probe.yaml` +
`PythonRuleEmitTest.weakrand rule lowers to per-function random self-source and str sink pairs`.

**Recommended next weakrand batch (~50 of the remaining ~276).** Reuse the identical `weakrand-probe`-style
`pattern-either` verbatim. Survey each entry's `value =` line only to (a) confirm weak `random.<fn>` (TRUE)
vs secrets/os.urandom (FALSE, auto-excluded) vs `random.SystemRandom().<fn>()` (FALSE → `@Disable` inv 38);
(b) add a new `str(random.<fn>(...))` branch if a weak fn outside the five appears (e.g. `uniform`, `choice`,
`shuffle`, `sample`, `betavariate`, `gauss`, `randrange`); (c) watch for any TRUE entry NOT wrapped in `str`
(would need a different outer sink). os.urandom FALSE need no handling (name never matches).

## Crutch removal — bare structural sinks (securecookie / hash / weakrand)

The three structural no-flow categories were refactored to REMOVE the self-source / downstream-use
"crutch" and use the correct form: **a bare structural sink on the dangerous call itself**, which fires
on the call match alone — NO source, NO `ContainsMark` predicate. VERIFIED FACT: a structural sink
whose lowered condition is a specific-function target (with or without a positive const-compare) survives
sink-discard and fires without any data-flow source. All 516 rule files regenerated (uniform per category);
`OwaspBenchmarkTest` verdicts held identically (full suite failures=0).

**Before → after (rule body):**
- **securecookie (39):** `$RESP = flask.make_response(...) ... $RESP.set_cookie(..., secure=False, ...)`
  → **`$RESP.set_cookie(..., secure=False, ...)`** (single `pattern:`). Emit: 1 sink `set_cookie`,
  `ConstantCmp(kwarg(secure)==False)`, NO source, NO `ContainsMark`.
- **hash (151):** `$H = hashlib.new('md5')/... ... $H.update(...)` (pattern-either) → **`pattern-either` of
  bare `hashlib.new('md5')`, `hashlib.new('sha1')`, `hashlib.md5(...)`, `hashlib.sha1(...)`**. Emit: 4 sinks,
  NO source; the two `hashlib.new` sinks carry `ConstantCmp(arg(0)==algo)`, the `hashlib.md5/sha1` sinks have
  a trivially-true (null) condition (kept — specific function target).
- **weakrand (326):** `str(random.<fn>(...))` (pattern-either) → **`pattern-either` of bare
  `random.<fn>(...)`**. Emit: 5 sinks `random.{normalvariate,randint,getrandbits,random,randbytes}`, all with
  null condition, NO source.

**Verification (CARDINAL 5):**
- Emit dump (scratch `SpikeDumpTest` on candidate probes): every category emits ONLY `SerializedPythonSink`s,
  ZERO `SerializedPythonSource`s. securecookie 1 sink; hash 4 sinks; weakrand 5 sinks. Locked permanently in
  the rewritten `PythonRuleEmitTest` (`… lowers to a source-less structural sink` / `… source-less structural
  sinks`) which now assert `SerializedPythonSource` is empty and no `ContainsMark`.
- Firing spike (11 real entries, verdict = firing signal): securecookie TRUE 00064/00065 reach, FALSE 00337
  excluded; hash TRUE 00054/00057 reach, FALSE 00055/00061 excluded; weakrand TRUE 00025/00026 reach, FALSE
  00032 excluded. All PASS.
- SystemRandom re-check: temporarily enabled 00044 (weakrand SystemRandom `@Disabled`) under the crutch-free
  form → still FIRES (FP), assertNotReachable FAILED. The last-segment callee collision
  (`PIRSimpleNameUnknownFunction:getrandbits` vs target `random.getrandbits`) is identical whether the weak
  call is a source or a bare sink → the 100 SystemRandom entries stay `@Disabled` (inv 38). Reverted.
- Full suite: `OwaspBenchmarkTest` 1181 tests, 775 pass / 0 fail / 406 skipped — unchanged vs before
  (only rule bodies, probes, and docs were touched; no `@Disabled` annotation changed).

**Tripwires updated to the new form:** `python-rules/{securecookie,hash,weakrand}-probe.yaml` +
their `PythonRuleEmitTest` assertions. Session-2 doc inv 36/37/38 rewritten to describe the bare structural
sink as the correct form (crutch history noted).

## xss round batch 1 (CWE-79, 30 entries) — return sinks now WORK (inv 35 stale), ALL STRUCTURAL
Sink for every entry: the returned response body `$A = <src>(...) ... return $A` (template
`BenchmarkTest00096.yaml`). Return-value sinks now fire after the return-sink rebase (17c205419/e122304b0);
the old blanket inv-35 @Disabled reason is STALE. Sources: `request.form.get` (scalar), `getlist(...)[...]`
(→values[0]), `get_form_parameter` wrapper → canonical `flask.request.form.get(...)` (inv 26, ABSTRACT taint),
`for name in request.form.keys()` loop → `flask.request.form.keys(...)[...]` (inv 15). Suite after round:
**1230 tests, 0 fail, 442 skipped (788 pass)** (+13 active-pass over the prior 775). Batch = 13 active-pass
(6 TRUE reach + 7 FALSE not-reach) + 17 @Disabled.

### Active TRUE reach (6): 00096 00169 00187 00272 00278 00281
Direct/if-else/ternary tainted-arm/base64-roundtrip flows into an f-string or `.format(bar,otherarg)`
(DIRECT-arg) response body. 00272/00278/00281 use the get_form_parameter wrapper (abstract source, inv 26).

### Active FALSE not-reach (7): 00149 00150 00186 00190 00256 00257 00364
- 00186 (getlist→markupsafe.escape→f-string): the escape sanitizer is NOT engine-modeled, so it was an FP
  until an ARG-position structural cleaner `pattern-not: ... markupsafe.escape($A) ... return $A` (inv 23)
  cleaned the CONCRETE mark. Now green for the right reason.
- 00190 (getlist→html.escape→`%`) / 00364 (keys→escape_for_html→format(dict)): pass via a DOWNSTREAM concrete
  drop (`%` tuple / dict-wrapped format / char-rebuild), NOT the sanitizer — masked passes (would FP once the
  concrete-element gap is fixed), acceptable like prior-round `.resolve()` drops.
- 00149/00150/00256/00257 (make_response HEADER write): tainted bar goes to the response HEADER not the body;
  the unmodeled `make_response` DROPS the concrete source taint → returned RESPONSE untainted → NOREACH.

### @Disabled — concrete-element FN at collection-wrapped sink-side format (inv 25/29, 5)
00097 (`param.split(' ')[0]`), 00098/00188/00365 (`"{0[bar]}".format(dict)` where dict['bar']=bar),
00189 (`"%s" % (bar, otherarg)` tuple). All TRUE; concrete taint reaches `bar` but DROPS when placed into a
dict/tuple that is then format-expanded. Deepening the SOURCE `[...]`→`[...][...]` is INERT (verified: still
FN) because the dropping collection is built at the SINK side, not the source. Proven differentially:
`.format(bar,otherarg)` DIRECT-arg reaches (00187), `.format(dict)` ABSTRACT reaches (00281), only concrete
dict/tuple-wrapped fails. Scalar `form.get` (00097/00098) can't deepen anyway (no code subscript). Engine-fix
candidate = propagate concrete collection-element taint through format/`%`/subscript (inv 25 family).

### @Disabled — abstract (wrapper) taint survives an unmodeled call / cleaner (inv 25/30, 3)
- 00282 (wrapper→html.escape→`%`): the html.escape arg-cleaner cleans the CONCRETE mark but the ABSTRACT
  wrapper taint survives it (cf. concrete getlist 00186 which cleaned green) → FP.
- 00334/00335 (wrapper→if-else→make_response HEADER): wrapper ABSTRACT taint survives the unmodeled
  make_response (concrete 00256/00257 DROP → pass) → returned RESPONSE tainted → FP.
- 00279 (wrapper→copy-rebind `copy=str(''); s+=param; bar=copy`): abstract source over-propagates through the
  immutable-string copy-rebind (copy never receives param concretely) → FP.

### @Disabled — path-insensitive const branch (inv 18, 4): 00083 (if/else) 00084/00191 (match) 00363 (ternary)
Const guard selects the safe arm but a tainted `bar=param` arm is also explored → FP. Unfixable (no validator CALL).

### @Disabled — dict/configparser key-insensitivity (inv 16, 3): 00082/00280 (dict) 00185 (configparser)
Store keyB(param), read keyA(const); key-insensitive read leaks tainted value → FP.

### @Disabled — ThingFactory getattr FN (inv 20, 1): 00362
`helpers.ThingFactory.createThing().doSomething(param)` — dynamic getattr → Any receiver → user method
unresolved, arg→return lost → TRUE unreachable. Same reproducer class as ldapi 00896 / codeinj 00343.

### No pass-throughs / engine changes this round.
### Recommended for xss batches 2-3
Reuse the return-sink template + the ARG-position escape cleaner (inv 23) for CONCRETE-source escape FALSE
entries. Expect the same @Disabled buckets: concrete-element format(dict)/`%`/split FN (inv 25/29), abstract
wrapper survives escape/make_response (inv 25/30), path-insensitive const arms (inv 18), key-insensitivity
(inv 16), ThingFactory (inv 20). Batches with all-getlist/scalar (concrete) sources will strand fewer TRUE
entries than wrapper-heavy batches.

## xss round batch 2 (CWE-79, 30 entries) — 18 active-pass / 12 @Disabled / 0 fail
Same return-sink template as batch 1 (`BenchmarkTest00096.yaml`). Sources: `headers.get`/`args.get` scalar,
`headers.getlist(...)[...]`/`args.getlist(...)[...]`, `form.keys(...)[...]` (keys-loop, inv 15),
`get_query_parameter` wrapper → canonical `flask.request.args.get(...)` (inv 26). Every predicted bucket
held exactly (12/12 predicted failures matched). Suite after round: **1230 tests, 0 fail, 424 skipped**
(+18 active-pass; 442→424).

### Active TRUE reach (9): 00450 00515 00531 00532 00669 00753 00839 00841 00842
Direct-arg `.format(bar, otherarg)` or f-string response body, fed by: tainted if/ternary/match arm
(path-insensitive), configparser SAME-key set/get, list append/pop/`lst[0]`(=param, index-insensitive),
whole-string concat+slice (`s+=param; s[4:-17]`, inv 32 no-drop). 00839/00841/00842 use the wrapper
(abstract, inv 26). Confirms: f-string + direct-arg `.format` both propagate concrete AND abstract taint.

### Active FALSE not-reach (9): 00367 00414 00437 00452 00493 00591 00670 00671 00672
- 00437 (scalar headers→markupsafe.escape→f-string) / 00452 (scalar→html.escape→dict-format): ARG-position
  escape cleaner (inv 23) cleans the CONCRETE mark → green for the right reason (00437 the only one where the
  escape is the SOLE safety — f-string doesn't drop; 00452 also dict-drops).
- 00414 (keys→html.escape→make_response header): escape cleaner + make_response drop; concrete → NOREACH.
- 00367 (keys→ternary→`%`tuple) / 00671 (scalar→configparser keyB/keyA→`%`tuple) / 00672 (scalar→match→`%`tuple):
  MASKED passes — the tainted arm / key-insensitive leak IS reached but the `%`-tuple sink-side wrap DROPS
  concrete taint → NOREACH. Would FP once the inv-25/29 concrete-element gap is fixed (acceptable, like 00190).
- 00493 (scalar→copy-rebind→make_response header) / 00591 (getlist→dict SAME-key→make_response header) /
  00670 (scalar→copy-rebind→`.format` direct): genuinely-safe value (copy never gets param) and/or make_response
  drop → NOREACH.

### @Disabled — concrete-element FN at collection-wrapped sink-side format (inv 25/29, 6)
00366/00453/00533/00673 (`%`-tuple `(bar, otherarg)`), 00451 (dict `{0[bar]}`.format(dict)),
00754 (`split(...)[0]` THEN dict-format — double sink-side drop). All TRUE; concrete taint reaches `bar` but
DROPS when placed into the tuple/dict that is then `%`/format-expanded. VERIFIED FN by the run (sink not
reached). Deepening the SOURCE `[...]` is inert (drop is sink-side). Same class as batch-1 00189/00098/00097.

### @Disabled — path-insensitive const branch into a NON-dropping sink (inv 18, 3)
00668 (scalar→const ternary→f-string), 00830 (WRAPPER→const ternary→f-string), 00752 (getlist→match→f-string).
Const guard selects the safe arm but the engine explores the tainted `bar=param` arm; the f-string sink does
NOT drop → reaches → FP. (Contrast the `%`/dict batch-1+above entries whose tuple/dict wrap masks the same
path-insensitivity into a pass.) Unfixable (no validator CALL).

### @Disabled — list index-insensitivity (inv 19, 1): 00436
scalar headers→`lst.append('safe'); lst.append(param); lst.append('moresafe'); lst.pop(0); bar=lst[1]` (safe
slot 'moresafe' after pop). Append taints the whole list; `lst[1]` reads tainted → f-string → FP. Same as 00348.

### @Disabled — dict key-insensitivity (inv 16, 1): 00840
WRAPPER→dict store keyB(param), final `bar=map['keyA']`(const 'a-Value'); key-insensitive read leaks the
keyB tainted value; `.format` direct-arg (no drop) → FP.

### @Disabled — abstract (wrapper) taint survives escape cleaner (inv 25/30, 1): 00829
wrapper→markupsafe.escape→f-string. The arg-position escape cleaner cleans the CONCRETE mark (cf concrete
00437 green) but the ABSTRACT wrapper taint survives it; f-string doesn't drop → FP. Same as batch-1 00282.

### No pass-throughs / engine changes this round.
### Note for xss batch 3
Prediction accuracy 12/12. The MASKED-pass pattern (path-insensitive/key-insensitive leak reached but a
sink-side `%`-tuple / dict-format / make_response DROPS it → NOREACH passes) recurs — a NOREACH entry with a
tuple/dict/make_response sink usually passes regardless of the safety mechanism; a NOREACH entry with an
f-string / direct-arg `.format` sink and a tainted-but-unselected arm FPs (inv 18/19/16). REACH entries with
tuple/dict/split sink wraps are inv-25/29 FN. Escape cleaner works ONLY for concrete sources.

## xss round batch 3 (CWE-79, 29 entries) — 24 active-pass / 5 @Disabled / 0 fail
Same return-sink template (`BenchmarkTest00096.yaml`). Sources this batch: `get_query_parameter` wrapper →
`flask.request.args.get(...)` (ABSTRACT, inv 26); `request.query_string.decode('utf-8')` →
`flask.request.query_string` (CONCRETE, survives .decode/whole-slice/unquote_plus, inv 32);
`request.args.getlist(...)[...]`; and two NON-source families modeled with a deliberately-non-matching
`flask.request.query_string` source: `request.path.split("/")` (inv 17, server-controlled route) and
`scr.get_safe_value(...)` (inv 33, returns literal "bar" — VERIFIED in separate_request.py:18-19). Suite
after round: **1230 tests, 0 fail, 400 skipped** (+24 active-pass; 424→400). Predicted buckets held 5/5.

### Active TRUE reach (2): 00924 01210
00924 query_string→`bar = param + '_SafeStuff'` (concat survives)→f-string. 01210 getlist→`values[0]`→f-string.
Concrete taint survives concat / element-index into a non-dropping f-string body.

### Active FALSE not-reach (22)
- Non-source free passes (20): request.path entries 01000/01001/01002/01003/01014/01015/01016/01017/01018/
  01019/01020/01082/01083/01084/01223/01224 (inv 17 — request.path is not a source) + get_safe_value entries
  01103/01104/01115/01155 (inv 33 — literal return). The `flask.request.query_string` source pattern simply
  doesn't bind → 0 sources → NOREACH for the RIGHT reason (accessor genuinely non-attacker-controlled).
- 00926 (query_string→copy-rebind `copy=''; string+=param; copy+='OK'; bar=copy`→`%`tuple): bar never receives
  param concretely → genuinely safe (+ %-tuple would drop anyway). NOREACH.
- 01213 (getlist→`values[0]`→make_response HEADER, body const): concrete param goes to the header dict; unmodeled
  make_response drops concrete → returned body untainted → NOREACH (masked, cf 00256).

### @Disabled — wrapper (abstract) survives make_response HEADER (inv 25/30, 2): 00883 00884
Both get_query_parameter (ABSTRACT) → bar → `make_response((RESPONSE,{header:bar}))`. 00883 via list
append/pop/`lst[1]` (index-insensitive), 00884 via markupsafe.escape (cleans concrete only). Abstract wrapper
taint survives the unmodeled make_response → returned RESPONSE tainted → FP. Same differential as 00334/00335
(concrete make_response header 00256/01213 DROP → pass). VERIFIED by run (sink reached).

### @Disabled — dict key-insensitivity into non-dropping f-string (inv 16, 1): 00905
query_string (concrete)→dict store keyB(param), final read keyA(const 'a-Value')→f-string. Key-insensitive read
leaks the keyB tainted value; f-string doesn't drop → FP. VERIFIED sink reached. Same as 00082/00840.

### @Disabled — concrete-element FN at sink-side wrap (inv 25/29, 2): 00923 00925
Both REACH ground truth, query_string CONCRETE source. 00923 `bar = param.split(' ')[0]` (element read drops
concrete, cf 00097) → f-string not reached. 00925 configparser SAME-key set/get → `'...%s...%s' % (bar,otherarg)`
(%-tuple drops concrete, cf 00189/00671) → not reached. VERIFIED FN by run (sink not reached). Confirms
query_string concrete behaves identically to form/args.get concrete at split()[i] / %-tuple wraps.

### No pass-throughs / engine changes / new invariants this round.
### xss category COMPLETE (all 3 batches): 89/89 authored — 55 active-pass / 34 @Disabled / 0 fail.
