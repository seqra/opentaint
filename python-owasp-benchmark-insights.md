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
