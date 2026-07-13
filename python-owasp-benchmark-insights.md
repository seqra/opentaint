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
