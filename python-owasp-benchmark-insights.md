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

### @Disabled (9)
- **00269** (TRUE, FN, inv 20): ThingFactory `getattr` → Any receiver → `thing.doSomething(param)` unresolved.
- **00605** (TRUE, FN, inv 29 NEW): `escape_for_html` char-rebuild body drops taint. **VERIFIED**: a call-arg
  probe rule (`... helpers.utils.escape_for_html($A)` as sink) FIRES → taint reaches the call; drop is inside
  the `for c in s: ret += c` body (scalar NextIter, inv-25 family). A temp `config.yaml` passThrough on
  `escape_for_html` had NO effect (analyzed user fn, not overridable by config). NOT added globally — it
  would FP future xss where escape_for_html is the real sanitizer.
- **00349, 00658** (FALSE, FP, inv 16): dict key-insensitivity (store keyB(param), read keyA(const)).
- **00508, 00513, 00608, 00995** (FALSE, FP, inv 18): path-insensitive match/if-else/ternary (const-selected
  safe arm, tainted arm still explored).
- **00826** (FALSE, FP, inv 19): list index-insensitivity (append(param), pop(0), read lst[1]).

### Pass-throughs added: `base64.urlsafe_b64decode` (arg(0)+kwarg(s)→result).
