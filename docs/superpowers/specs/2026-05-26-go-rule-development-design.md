# Go Rule Development — Design

## Goal

Author OpenTaint Go taint rules until both target benchmarks report ≥70% TP
of their `truth.sarif` "fail" entries. FP rate is deliberately not capped on
this first pass — recall first, precision later.

## Targets

| Benchmark | Truth-fail (TP target) | Truth-pass (decoys) | CWE classes |
|-----------|-----------------------|---------------------|-------------|
| `go-owasp-converted-mutated` | 148 | 270 | CWE-22, 77/78, 79, 89 |
| `go-sec-code-mutated`       | 181 | 259 | CWE-22, 77, 89 |
| Combined                     | 329 | 529 | 4 distinct CWE classes |

≥70% combined ⇒ catch ≥230 of the 329 truth-fail entries.

Truth-sarif locations have **no line numbers** — only `artifactLocation.uri`.
The comparison script keys on URI alone.

## Architecture

Wiring is already in place: `GoProjectAnalyzer` runs end-to-end on both
benchmarks; bundled `go-config/` ships propagator YAMLs for `fmt`, `strings`,
`path`, `path/filepath`, `io`, `net/url`, `encoding/{json,xml}`, `bytes`,
beego helpers; the analyzer takes user rules via `--ruleset` and loads them
through `SemgrepRuleLoader(listOf(GoLanguageStrategy()))`. So this design
adds **rule files only** — no Kotlin or CLI code changes.

### Rule taxonomy — Approach B (inline per CWE)

Each CWE gets one YAML rule with `mode: taint`, `pattern-either` for sources,
`pattern-either` for sinks. Mirrors the existing `samples-go-massive/` style.
Approach C (split lib + security with `mode: join`) is deferred — the rule
language's join-mode wiring for Go is unverified and validating it would
cost an iteration we don't have to spend.

Layout (mirrors Java side's `security/` convention):

```
.opentaint/rules/go/
  security/
    cmdinj.yaml          (CWE-77, CWE-78)
    path-traversal.yaml  (CWE-22)
    sql-injection.yaml   (CWE-89)
    xss.yaml             (CWE-79)
```

If approximation gaps appear in `external-methods-without-rules.yaml` on a
plausible source→sink path, add:

```
.opentaint/config/
  go-custom-propagators.yaml   (loaded via --approximations-config)
```

## Source catalog (shared across all 4 rules)

Mined from CodeQL's `net.http.model.yml` (`kind=remote`) plus
`stdlib/NetHttp.qll` (`RedirectUnexploitableRequestFields`):

**Method calls on `*http.Request`:**
- `$R.Cookie($K)`, `$R.Cookies()`
- `$R.FormValue($K)`, `$R.PostFormValue($K)`
- `$R.FormFile($K)`
- `$R.MultipartReader()`
- `$R.Referer()`, `$R.UserAgent()`

**Field reads on `*http.Request`** (entire field is remote-tainted):
- `$R.Body`, `$R.GetBody`
- `$R.Form`, `$R.PostForm`, `$R.MultipartForm`
- `$R.Header`, `$R.Trailer`
- `$R.URL`

**Chained accesses commonly used in the benchmarks:**
- `$R.URL.Query()`, `$R.URL.Query().Get($K)`
- `$R.URL.Path`, `$R.URL.RawQuery`, `$R.URL.RawPath`
- `$R.Header.Get($K)`, `$R.Header.Values($K)`
- `$R.Form.Get($K)`, `$R.PostForm.Get($K)`

**Env / args (covers go-sec-code-mutated's env-driven decoys):**
- `os.Getenv($K)`, `os.LookupEnv($K)`
- `os.Args[$I]`, `os.Args`

Beego-style sources (held in reserve — both benches use plain `net/http`):
`(group:beego-context).BeegoInput.{Bind, Cookie, Data, Header, Param, Params,
Query, Refer, Referer, RequestBody, URI, URL, UserAgent}` and
`(group:beego).Controller.{ParseForm, GetFile, GetFiles, GetString, GetStrings,
Input}`. Add only if FN analysis shows they're on the source→sink path.

## Sink catalog per CWE

Mined from CodeQL ext yamls (`*.model.yml`, `kind=<vuln>`). Each rule's
`pattern-sinks` block uses `pattern-either` over these.

### `cmdinj.yaml` (CWE-77 + CWE-78) — 16 ext entries; 6 stdlib

```
os/exec.Command($NAME, ...)               # Arg0
os/exec.CommandContext($CTX, $NAME, ...)  # Arg1
os.StartProcess($NAME, ...)               # Arg0
syscall.Exec($NAME, ...)                  # Arg0
syscall.ForkExec($NAME, ...)              # Arg0
syscall.StartProcess($NAME, ...)          # Arg0
```

### `path-traversal.yaml` (CWE-22) — 27 stdlib entries

```
os.{Chdir, Chmod, Chown, Chtimes, Create, Lchown, Lstat, Mkdir, MkdirAll,
    Open, OpenFile, Readlink, Remove, RemoveAll, Stat, Symlink, Truncate,
    DirFS, ReadDir, ReadFile, MkdirTemp, CreateTemp, WriteFile}($PATH, ...)
io/ioutil.{ReadDir, ReadFile, TempDir, TempFile, WriteFile}($PATH, ...)
net/http.ServeFile($W, $R, $PATH)         # Arg2
```

`os.Link($SRC, $DST)`, `os.Rename($SRC, $DST)`, `os.Symlink($SRC, $DST)`,
`os.NewFile($FD, $NAME)`, `os.Lchown` have either both args or a non-0 arg as
the path — covered by an explicit pattern per method.

### `sql-injection.yaml` (CWE-89) — 24 stdlib + 30 beego-orm; stdlib only on first pass

```
(*database/sql.DB).{Query, QueryRow, Exec, Prepare}($SQL, ...)          # Arg0
(*database/sql.DB).{QueryContext, QueryRowContext, ExecContext,
                    PrepareContext}($CTX, $SQL, ...)                    # Arg1
# same for Conn, Tx, Stmt receivers
```

If after the cmdinj/path passes we find sql FNs concentrated on beego ORM:
add `(group:beego-orm).{Ormer.Raw, QueryBuilder.{Where, From, Select, And,
Or, OrderBy, GroupBy, Having, Set, Update, InsertInto, Values, On},
Condition.Raw, QuerySeter.FilterRaw}`.

### `xss.yaml` (CWE-79) — hand-written, not in ext yamls

```
($W is http.ResponseWriter).Write($BUF)           # Arg0 of method call
fmt.Fprint($W, $X, ...)                           # Arg1+ ; tainted if $X tainted
fmt.Fprintf($W, $FORMAT, $X, ...)                 # Arg2+
fmt.Fprintln($W, $X, ...)                         # Arg1+
io.WriteString($W, $S)                            # Arg1
(*text/template.Template).Execute($W, $DATA)      # Arg1 — no autoescape
(*html/template.Template).Execute($W, $DATA)      # Arg1 — autoescaped; flag at lower priority
```

CodeQL's content-type gating (skip JSON / plain-text responses) is out of
scope for the first pass — recall first.

## Propagation

`GoConfigLoader.getConfig()` already ships passThrough YAMLs for the relevant
stdlib (`fmt`, `strings`, `path`, `path/filepath`, `io`, `net/url`,
`encoding/json`, `encoding/xml`, `bytes`, beego helpers). The first scan runs
without `--approximations-config`.

After scan 1: read `external-methods-without-rules.yaml`. Any method on a
plausible source→sink path that isn't already covered gets a custom
passThrough YAML entry under `.opentaint/config/go-custom-propagators.yaml`,
re-scan, repeat. Sources for new propagators: CodeQL ext yamls
(`kind=taint`), specifically the `Argument[N] → ReturnValue` and
`Argument[N] → Argument[M]` rows.

## Iteration loop

Per CWE, in order **cmdinj → path → sql → xss** (simplest sinks first):

1. Write `security/<cwe>.yaml` with full source-list + sink-list (above).
2. Scan both benchmarks with `--ruleset .opentaint/rules --track-external-methods`.
3. Run `compare.py` (URI-only, per-rule break-out) and record TP / FP / FN
   for the active CWE.
4. If TP < 70% on the CWE:
   - Read 3-5 missed-flow source files. Identify the gap (source pattern
     missing, sink pattern missing, propagator missing).
   - If propagator missing → add a YAML passThrough entry.
   - If source/sink missing → extend the rule's `pattern-either`.
   - If sanitizer required (rare on this pass) → add `pattern-not`.
5. Re-scan, repeat until ≥70% TP for that CWE.
6. Commit the rule and any new propagator entries; move on.

After all 4 classes hit ≥70% individually, verify the combined TP across
both benchmarks also clears 70%.

## Tooling

`benchmarks/compare.py` (already authored as part of the wiring phase) needs
two updates:
1. Key on `artifactLocation.uri` only (truth has no line numbers).
2. Per-CWE TP/FP breakdown — needed to know which rule to iterate next.

The updated script lives outside the main repo (in `benchmarks/`) — no
opentaint-side commit.

## Out of scope

- Sanitizer / `pattern-not` work — only added when a class hits the >70%
  wall.
- Framework-specific rules (beego, gin, echo) — held in reserve.
- Refactor to Approach C (lib + security with `mode: join`) — future work
  once approach B is validated.
- Code-based approximations — Go side has no such mechanism today.

## Exit criteria

- Each of `cmdinj`, `path-traversal`, `sql-injection`, `xss` reaches ≥70% TP
  on each benchmark that contains it.
- Combined TP across both benchmarks ≥70% (≥230 of 329 truth-fail entries).
- All committed rules verified by re-running the full pipeline through
  `opentaint --experimental scan` (not the analyzer JAR directly) so the
  CLI integration is exercised.

## Risks / open questions

- **Beego-ORM appearance**: if either benchmark routes SQL through beego ORM
  (despite the controllers being plain net/http), we'll need the beego SQL
  sinks. Defer until first scan; the ext-yaml entries are pre-mined and
  ready to drop in.
- **`text/template.Execute` semantic**: marking it XSS-sink is correct for
  text templates rendered into HTTP responses but produces FP if the
  template emits JSON or plain text. We accept that FP in the first pass
  (recall first).
- **External-methods-without-rules size**: large monorepos can produce
  many entries; the iteration step needs to *filter* this list to methods
  on a plausible source→sink path, not blindly approximate everything.
