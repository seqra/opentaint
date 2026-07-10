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
