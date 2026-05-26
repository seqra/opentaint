# Go Rule Development Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Author 4 Go taint rules (cmdinj, path-traversal, sql-injection, xss) and iterate them on `go-owasp-converted-mutated` + `go-sec-code-mutated` until ≥70% TP on the combined truth-fail set (329 entries).

**Architecture:** Approach B — one yaml per CWE under `.opentaint/rules/go/security/`, `mode: taint` with `pattern-either` source list and `pattern-either` sink list. Propagation rides on the bundled `go-config/` passthrough catalog; gaps surfaced in `external-methods-without-rules.yaml` get added under `.opentaint/config/go-custom-propagators.yaml`. Recall first — sanitizers/`pattern-not` are reserved for cases where a class hits the >70% wall.

**Tech Stack:** OpenTaint semgrep YAML rule format (`mode: taint`, `pattern-sources`, `pattern-sinks`), Go SSA via `GoIRClient`, kaml-based YAML loader (`GoConfigLoader`), `opentaint --experimental scan` CLI with locally built fat jars.

Working directory: `/drive-testcomp/opentaint-go-rules/opentaint`. Benchmarks live at `/drive-testcomp/opentaint-go-rules/benchmarks/{go-owasp-converted-mutated, go-sec-code-mutated}`. Locally built jars:
- Analyzer: `/drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer.jar`
- Autobuilder: `/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar`

Rules live alongside the benchmarks (one rules tree, reused for both):
- Rules root: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/`
- Custom approximation YAMLs (if needed): `/drive-testcomp/opentaint-go-rules/benchmarks/config/`

---

## File Structure

| File | Responsibility |
|------|----------------|
| `benchmarks/compare.py` (update) | URI-only TP/FP matcher with per-CWE breakdown. |
| `benchmarks/rules/go/security/cmdinj.yaml` (new) | CWE-77/78 rule: `os/exec`, `os`, `syscall` sinks. |
| `benchmarks/rules/go/security/path-traversal.yaml` (new) | CWE-22 rule: `os`, `io/ioutil`, `net/http.ServeFile` sinks. |
| `benchmarks/rules/go/security/sql-injection.yaml` (new) | CWE-89 rule: `database/sql.{DB,Conn,Tx,Stmt}` sinks. |
| `benchmarks/rules/go/security/xss.yaml` (new) | CWE-79 rule: `http.ResponseWriter.Write`, `fmt.Fprint*`, `template.Execute` sinks. |
| `benchmarks/config/go-custom-propagators.yaml` (new, populated only on demand) | Custom passthrough rules added when `external-methods-without-rules.yaml` shows gaps on source→sink paths. |
| `benchmarks/scan.sh` (new) | One-shot scanner script for both benchmarks; sets `GOIR_SERVER_BINARY` and points `opentaint --experimental` at the local jars + rules. |

The `benchmarks/` directory is the scratch area (already exists from the earlier wiring work, already contains `compare.py` and both git clones). Nothing in this plan touches the main `opentaint/` repo source code.

---

## Phase 1 — Tooling

### Task 1: Update `compare.py` to URI-only matching + per-CWE breakdown

**Files:**
- Modify: `/drive-testcomp/opentaint-go-rules/benchmarks/compare.py`

- [ ] **Step 1: Replace the script with the new version**

```python
#!/usr/bin/env python3
"""Compare a benchmark SARIF against truth.sarif.

Truth conventions (per Go benchmarks from flawgarden):
  kind=pass  -> truth says "this should NOT be reported"  (FP territory)
  kind=fail  -> truth says "this is a real bug"           (TP territory)

Truth locations carry only artifactLocation.uri (no line numbers), so we
match on URI alone, scoped per CWE so we can iterate one class at a time.
"""
import json, pathlib, sys
from collections import defaultdict


def load(path):
    data = json.loads(pathlib.Path(path).read_text())
    rows = []
    for run in data.get("runs", []):
        for result in run.get("results", []):
            kind = result.get("kind", "fail")
            rule_id = result.get("ruleId", "?")
            cwe = cwe_of(rule_id)
            for loc in result.get("locations", []) or []:
                uri = loc.get("physicalLocation", {}).get("artifactLocation", {}).get("uri", "")
                if uri:
                    rows.append((cwe, uri, kind, rule_id))
    return rows


def cwe_of(rule_id):
    rid = rule_id.upper()
    if "CWE-22" in rid or "PATH" in rid:
        return "CWE-22"
    if "CWE-77" in rid or "CWE-78" in rid or "COMMAND" in rid or "CMDINJ" in rid:
        return "CWE-78"
    if "CWE-79" in rid or "XSS" in rid:
        return "CWE-79"
    if "CWE-89" in rid or "SQL" in rid:
        return "CWE-89"
    return rid


def by_cwe(rows):
    out = defaultdict(set)
    for cwe, uri, kind, _ in rows:
        out[(cwe, kind)].add(uri)
    return out


def main(report, truth):
    rep = by_cwe(load(report))
    tru = by_cwe(load(truth))
    cwes = sorted({cwe for (cwe, _), _ in {**rep, **tru}.items()})

    fmt = "{:8} {:>5} {:>5} {:>5} {:>5} {:>5} {:>7}"
    print(fmt.format("CWE", "truF", "truP", "rep", "TP", "FP", "TP%"))
    overall_tp = overall_fail = overall_fp = 0
    for cwe in cwes:
        truth_fail = tru.get((cwe, "fail"), set())
        truth_pass = tru.get((cwe, "pass"), set())
        report_uris = rep.get((cwe, "fail"), set()) | rep.get((cwe, "pass"), set())
        tp = len(report_uris & truth_fail)
        fp = len(report_uris & truth_pass)
        pct = (100.0 * tp / len(truth_fail)) if truth_fail else 0.0
        print(fmt.format(cwe, len(truth_fail), len(truth_pass), len(report_uris), tp, fp, f"{pct:.1f}"))
        overall_tp += tp
        overall_fail += len(truth_fail)
        overall_fp += fp
    pct = (100.0 * overall_tp / overall_fail) if overall_fail else 0.0
    print(fmt.format("TOTAL", overall_fail, "", "", overall_tp, overall_fp, f"{pct:.1f}"))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
```

- [ ] **Step 2: Make executable**

```bash
chmod +x /drive-testcomp/opentaint-go-rules/benchmarks/compare.py
```

- [ ] **Step 3: Smoke-test against truth-vs-truth (sanity check the math)**

```bash
/drive-testcomp/opentaint-go-rules/benchmarks/compare.py \
  /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated/truth.sarif \
  /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated/truth.sarif
```

Expected: `CWE-22  101 ... 100.0%`, `CWE-78  87 ...`, `CWE-79  122 ...`, `CWE-89  108 ...`, `TOTAL 418 ... ... 148 ... 100.0`. (Note: truth-fail+truth-pass counts can overlap on a single URI across CWEs; the math is per-CWE.)

- [ ] **Step 4: Commit (scratch dir; init git if missing)**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
[ -d .git ] || git init -q
git add compare.py
git commit -q -m "Update compare.py: URI-only matching, per-CWE breakdown"
```

### Task 2: Create `scan.sh` runner for both benchmarks

**Files:**
- Create: `/drive-testcomp/opentaint-go-rules/benchmarks/scan.sh`

- [ ] **Step 1: Write the script**

```bash
#!/usr/bin/env bash
# Run opentaint scan on both Go benchmarks using local jars + local rules.
# Usage: scan.sh                  → scans both benchmarks
#        scan.sh owasp            → scans only go-owasp-converted-mutated
#        scan.sh sec              → scans only go-sec-code-mutated
set -euo pipefail

REPO=/drive-testcomp/opentaint-go-rules/opentaint
BENCH=/drive-testcomp/opentaint-go-rules/benchmarks
ANALYZER_JAR="$REPO/core/build/libs/opentaint-project-analyzer.jar"
AUTOBUILDER_JAR="$REPO/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar"
RULES="$BENCH/rules"
CONFIG="$BENCH/config/go-custom-propagators.yaml"

case "${1:-both}" in
  owasp) targets=("go-owasp-converted-mutated") ;;
  sec)   targets=("go-sec-code-mutated") ;;
  both|"") targets=("go-owasp-converted-mutated" "go-sec-code-mutated") ;;
  *) echo "usage: $0 [owasp|sec|both]" >&2; exit 2 ;;
esac

extra_args=()
if [ -f "$CONFIG" ]; then
  extra_args+=("--approximations-config" "$CONFIG")
fi

for t in "${targets[@]}"; do
  cd "$BENCH/$t"
  rm -rf .opentaint/results
  mkdir -p .opentaint/results
  echo "===== $t ====="
  opentaint --experimental scan \
    --project-model .opentaint/project \
    --analyzer-jar "$ANALYZER_JAR" \
    --autobuilder-jar "$AUTOBUILDER_JAR" \
    --ruleset "$RULES" \
    -o .opentaint/results/report.sarif \
    --track-external-methods \
    "${extra_args[@]}"
  "$BENCH/compare.py" .opentaint/results/report.sarif truth.sarif
done
```

- [ ] **Step 2: Make executable**

```bash
chmod +x /drive-testcomp/opentaint-go-rules/benchmarks/scan.sh
```

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add scan.sh
git commit -q -m "Add scan.sh runner for both Go benchmarks"
```

---

## Phase 2 — Initial rule files

Authoring style note: OpenTaint Go semgrep patterns use the **imported package name**, not the full Go import path. For example `os/exec.Command(...)` is matched by the pattern `exec.Command(...)`. The samples in `core/opentaint-go-querylang/samples-go-massive/` confirm this style.

### Task 3: Author `cmdinj.yaml`

**Files:**
- Create: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/cmdinj.yaml`

- [ ] **Step 1: Create the rule file**

```yaml
rules:
  - id: go-command-injection
    languages: [go]
    severity: ERROR
    message: Tainted user input reaches OS command execution (command injection)
    metadata:
      cwe: CWE-78
      short-description: Command injection
    mode: taint
    pattern-sources:
      - pattern-either:
          # net/http.Request — method calls
          - pattern: $R.FormValue($K)
          - pattern: $R.PostFormValue($K)
          - pattern: $R.FormFile($K)
          - pattern: $R.Cookie($K)
          - pattern: $R.Cookies()
          - pattern: $R.MultipartReader()
          - pattern: $R.Referer()
          - pattern: $R.UserAgent()
          # net/http.Request — URL chain
          - pattern: $R.URL.Query()
          - pattern: $R.URL.Query().Get($K)
          - pattern: $R.URL.Path
          - pattern: $R.URL.RawQuery
          - pattern: $R.URL.RawPath
          # net/http.Request — Header chain
          - pattern: $R.Header.Get($K)
          - pattern: $R.Header.Values($K)
          # net/http.Request — Form chain
          - pattern: $R.Form.Get($K)
          - pattern: $R.PostForm.Get($K)
          # net/http.Request — field reads
          - pattern: $R.Body
          - pattern: $R.GetBody
          - pattern: $R.Form
          - pattern: $R.PostForm
          - pattern: $R.MultipartForm
          - pattern: $R.Header
          - pattern: $R.Trailer
          - pattern: $R.URL
          # env / args
          - pattern: os.Getenv($K)
          - pattern: os.LookupEnv($K)
          - pattern: os.Args
    pattern-sinks:
      - pattern-either:
          - pattern: exec.Command($NAME, ...)
          - pattern: exec.CommandContext($CTX, $NAME, ...)
          - pattern: exec.LookPath($NAME)
          - pattern: os.StartProcess($NAME, ...)
          - pattern: syscall.Exec($NAME, ...)
          - pattern: syscall.ForkExec($NAME, ...)
          - pattern: syscall.StartProcess($NAME, ...)
```

- [ ] **Step 2: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add rules/go/security/cmdinj.yaml
git commit -q -m "Add cmdinj rule (CWE-77/78) initial source/sink lists"
```

### Task 4: Author `path-traversal.yaml`

**Files:**
- Create: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/path-traversal.yaml`

- [ ] **Step 1: Create the rule file**

The source list is identical to cmdinj — repeated inline (DRY is not worth the join-mode risk in this pass).

```yaml
rules:
  - id: go-path-traversal
    languages: [go]
    severity: ERROR
    message: Tainted user input reaches filesystem path (path traversal)
    metadata:
      cwe: CWE-22
      short-description: Path traversal
    mode: taint
    pattern-sources:
      - pattern-either:
          - pattern: $R.FormValue($K)
          - pattern: $R.PostFormValue($K)
          - pattern: $R.FormFile($K)
          - pattern: $R.Cookie($K)
          - pattern: $R.Cookies()
          - pattern: $R.MultipartReader()
          - pattern: $R.Referer()
          - pattern: $R.UserAgent()
          - pattern: $R.URL.Query()
          - pattern: $R.URL.Query().Get($K)
          - pattern: $R.URL.Path
          - pattern: $R.URL.RawQuery
          - pattern: $R.URL.RawPath
          - pattern: $R.Header.Get($K)
          - pattern: $R.Header.Values($K)
          - pattern: $R.Form.Get($K)
          - pattern: $R.PostForm.Get($K)
          - pattern: $R.Body
          - pattern: $R.GetBody
          - pattern: $R.Form
          - pattern: $R.PostForm
          - pattern: $R.MultipartForm
          - pattern: $R.Header
          - pattern: $R.Trailer
          - pattern: $R.URL
          - pattern: os.Getenv($K)
          - pattern: os.LookupEnv($K)
          - pattern: os.Args
    pattern-sinks:
      - pattern-either:
          - pattern: os.Open($P)
          - pattern: os.OpenFile($P, ...)
          - pattern: os.Create($P)
          - pattern: os.CreateTemp($DIR, $PAT)
          - pattern: os.MkdirTemp($DIR, $PAT)
          - pattern: os.Mkdir($P, ...)
          - pattern: os.MkdirAll($P, ...)
          - pattern: os.Remove($P)
          - pattern: os.RemoveAll($P)
          - pattern: os.ReadFile($P)
          - pattern: os.WriteFile($P, ...)
          - pattern: os.ReadDir($P)
          - pattern: os.Stat($P)
          - pattern: os.Lstat($P)
          - pattern: os.Truncate($P, ...)
          - pattern: os.Chdir($P)
          - pattern: os.Chmod($P, ...)
          - pattern: os.Chown($P, ...)
          - pattern: os.Lchown($P, ...)
          - pattern: os.Chtimes($P, ...)
          - pattern: os.Readlink($P)
          - pattern: os.Rename($A, $B)
          - pattern: os.Link($A, $B)
          - pattern: os.Symlink($A, $B)
          - pattern: os.DirFS($P)
          - pattern: ioutil.ReadFile($P)
          - pattern: ioutil.WriteFile($P, ...)
          - pattern: ioutil.ReadDir($P)
          - pattern: ioutil.TempFile($DIR, $PAT)
          - pattern: ioutil.TempDir($DIR, $PAT)
          - pattern: http.ServeFile($W, $R, $P)
```

- [ ] **Step 2: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add rules/go/security/path-traversal.yaml
git commit -q -m "Add path-traversal rule (CWE-22) initial source/sink lists"
```

### Task 5: Author `sql-injection.yaml`

**Files:**
- Create: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/sql-injection.yaml`

- [ ] **Step 1: Create the rule file**

SQL receivers on `*sql.DB` / `*sql.Conn` / `*sql.Tx` / `*sql.Stmt` are matched syntactically — `$DB.Query($SQL)` will hit any `.Query()` call, accepting some FP for first-pass recall. CodeQL's per-receiver enforcement is a future tightening if FP is later capped.

```yaml
rules:
  - id: go-sql-injection
    languages: [go]
    severity: ERROR
    message: Tainted user input flows into SQL query (SQL injection)
    metadata:
      cwe: CWE-89
      short-description: SQL injection
    mode: taint
    pattern-sources:
      - pattern-either:
          - pattern: $R.FormValue($K)
          - pattern: $R.PostFormValue($K)
          - pattern: $R.FormFile($K)
          - pattern: $R.Cookie($K)
          - pattern: $R.Cookies()
          - pattern: $R.MultipartReader()
          - pattern: $R.Referer()
          - pattern: $R.UserAgent()
          - pattern: $R.URL.Query()
          - pattern: $R.URL.Query().Get($K)
          - pattern: $R.URL.Path
          - pattern: $R.URL.RawQuery
          - pattern: $R.URL.RawPath
          - pattern: $R.Header.Get($K)
          - pattern: $R.Header.Values($K)
          - pattern: $R.Form.Get($K)
          - pattern: $R.PostForm.Get($K)
          - pattern: $R.Body
          - pattern: $R.GetBody
          - pattern: $R.Form
          - pattern: $R.PostForm
          - pattern: $R.MultipartForm
          - pattern: $R.Header
          - pattern: $R.Trailer
          - pattern: $R.URL
          - pattern: os.Getenv($K)
          - pattern: os.LookupEnv($K)
          - pattern: os.Args
    pattern-sinks:
      - pattern-either:
          - pattern: $DB.Query($SQL, ...)
          - pattern: $DB.QueryContext($CTX, $SQL, ...)
          - pattern: $DB.QueryRow($SQL, ...)
          - pattern: $DB.QueryRowContext($CTX, $SQL, ...)
          - pattern: $DB.Exec($SQL, ...)
          - pattern: $DB.ExecContext($CTX, $SQL, ...)
          - pattern: $DB.Prepare($SQL)
          - pattern: $DB.PrepareContext($CTX, $SQL)
```

- [ ] **Step 2: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add rules/go/security/sql-injection.yaml
git commit -q -m "Add sql-injection rule (CWE-89) initial source/sink lists"
```

### Task 6: Author `xss.yaml`

**Files:**
- Create: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/xss.yaml`

- [ ] **Step 1: Create the rule file**

```yaml
rules:
  - id: go-reflected-xss
    languages: [go]
    severity: ERROR
    message: Tainted user input written to HTTP response body (reflected XSS)
    metadata:
      cwe: CWE-79
      short-description: Reflected cross-site scripting
    mode: taint
    pattern-sources:
      - pattern-either:
          - pattern: $R.FormValue($K)
          - pattern: $R.PostFormValue($K)
          - pattern: $R.FormFile($K)
          - pattern: $R.Cookie($K)
          - pattern: $R.Cookies()
          - pattern: $R.MultipartReader()
          - pattern: $R.Referer()
          - pattern: $R.UserAgent()
          - pattern: $R.URL.Query()
          - pattern: $R.URL.Query().Get($K)
          - pattern: $R.URL.Path
          - pattern: $R.URL.RawQuery
          - pattern: $R.URL.RawPath
          - pattern: $R.Header.Get($K)
          - pattern: $R.Header.Values($K)
          - pattern: $R.Form.Get($K)
          - pattern: $R.PostForm.Get($K)
          - pattern: $R.Body
          - pattern: $R.GetBody
          - pattern: $R.Form
          - pattern: $R.PostForm
          - pattern: $R.MultipartForm
          - pattern: $R.Header
          - pattern: $R.Trailer
          - pattern: $R.URL
          - pattern: os.Getenv($K)
          - pattern: os.LookupEnv($K)
          - pattern: os.Args
    pattern-sinks:
      - pattern-either:
          - pattern: $W.Write($BUF)
          - pattern: $W.WriteString($S)
          - pattern: fmt.Fprint($W, ...)
          - pattern: fmt.Fprintf($W, ...)
          - pattern: fmt.Fprintln($W, ...)
          - pattern: io.WriteString($W, $S)
          - pattern: $T.Execute($W, $DATA)
          - pattern: $T.ExecuteTemplate($W, $NAME, $DATA)
```

- [ ] **Step 2: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add rules/go/security/xss.yaml
git commit -q -m "Add xss rule (CWE-79) initial source/sink lists"
```

---

## Phase 3 — Baseline scan with all four rules

### Task 7: First combined scan

**Files:** none (script execution only).

- [ ] **Step 1: Verify analyzer jar is current**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :projectAnalyzerJar 2>&1 | tail -3
ls -lh build/libs/opentaint-project-analyzer.jar
```

Expected: BUILD SUCCESSFUL; jar is ~53 MB.

- [ ] **Step 2: Run both benchmarks**

```bash
/drive-testcomp/opentaint-go-rules/benchmarks/scan.sh both | tee /tmp/scan-baseline.log
```

Expected: each benchmark prints a TP/FP/per-CWE table. SARIF + 2 external-methods YAMLs land in `.opentaint/results/`. The combined TP% is the baseline we must improve.

- [ ] **Step 3: Capture the baseline numbers**

```bash
grep -E "^CWE|^TOTAL" /tmp/scan-baseline.log
```

Record per-CWE TP/FP per benchmark for the iteration phase (Phase 4). No commit — this is measurement only.

---

## Phase 4 — Iterate per CWE

### Handbook: reading `external-methods-without-rules.yaml`

When a benchmark scan emits a non-empty `external-methods-without-rules.yaml`,
that file is the **iteration signal** — every entry is a method the analyzer
walked through on a tainted path but had no model for, so it killed the fact.
Use it as follows:

1. **Open the file** (`head -50 <results>/external-methods-without-rules.yaml`). Each entry is a YAML map like:

   ```yaml
   - method: "pkg/path.FunctionName"
     callSites: 17
     factPositions: ["arg(0)", "this"]
   ```

   `callSites` tells you how impactful modeling this method would be.
   `factPositions` tells you which positions the analyzer was carrying taint
   on at the call — useful for picking the `from:` for the new passThrough.

2. **Filter to the source→sink path of the active CWE.** Inspect the FN source
   files (Step 1 of the iteration task) and identify which entries from the
   list appear between the HTTP source and the CWE-specific sink. Methods
   that don't lie on any plausible source→sink path are no-ops — skip them
   even if they have high callSites.

3. **For each filtered entry, decide one of three actions:**
   - **a. Model with a passThrough entry** (most common) — append to
     `benchmarks/config/go-custom-propagators.yaml`. See the YAML format
     below.
   - **b. Model via the security rule's `pattern-either` instead** — if the
     method is a receiver method (e.g., `(*bytes.Buffer).WriteString`),
     the v1 loader drops receiver-method passThroughs (see "v1 limitation"
     below). Add a pattern that captures the caller shape directly in the
     security yaml.
   - **c. Skip** — if the method is not on any tainted source→sink path for
     the active CWE, leave it alone. Approximating no-op methods wastes
     iteration time.

4. **Confirm the entry "took"** after the next scan: the method should
   disappear from `external-methods-without-rules.yaml` and appear in
   `external-methods-with-rules.yaml`. If it does not, the function name /
   package path doesn't match what the analyzer sees — check the exact
   strings in the original "without-rules" YAML.

### Go YAML approximation format (passThrough)

The format is **structured**, not the JVM-style `pkg.Class#method` shorthand.
Parsed by `GoConfigLoader.parsePassThroughRules`. Each rule:

```yaml
passThrough:
  - function:
      package: <import-path>        # e.g. "strings", "encoding/base64"
      type: <type-name>             # optional, only for receiver methods
      name: <function-or-method>
      receiver: true | false        # true ⇒ method on a named type
    copy:
      - from: <position>
        to:   <position>
      # repeat for each independent taint copy
```

**Positions:**

| Token | Meaning |
|-------|---------|
| `arg(0)`, `arg(1)`, … | nth function argument (excluding receiver) |
| `this` | receiver of a method call |
| `result` | single return value |
| `result(0)`, `result(1)`, … | nth slot of a multi-return |
| `[arg(0), .[*]]` | YAML list: position + modifier(s). `.[*]` = array/slice element |

**v1 limitation:** `GoConfigLoader.parsePassThroughRules` drops any rule
with `receiver: true`. Receiver-method approximations are not loaded
today. For receiver-style helpers, model the caller pattern directly in
the security rule's `pattern-either` instead.

**Worked example.** If `external-methods-without-rules.yaml` lists
`go-sec-code/util.MyHelper` and the source at
`benchmarks/go-sec-code-mutated/util/helpers.go` is:

```go
package util
import "strings"
func MyHelper(s string) string { return strings.ToUpper(s) }
```

then the approximation entry is:

```yaml
passThrough:
  - function:
      package: go-sec-code/util
      name: MyHelper
      receiver: false
    copy:
      - from: arg(0)
        to: result
```

### Mining propagator definitions from CodeQL ext yamls

CodeQL ships authoritative propagator data in
`/drive-testcomp/opentaint-go-rules/codeql/go/ql/lib/ext/*.model.yml`
under `kind=taint`. Each row:

```
[package, type, qualifierIncluded, method, "", "", from-position, to-position, "taint", "manual"]
```

Translation table from CodeQL to OpenTaint Go positions:

| CodeQL | OpenTaint Go |
|--------|--------------|
| `Argument[N]` | `arg(N)` |
| `Argument[receiver]` | `this` (but receiver rules don't load — see limitation above) |
| `ReturnValue` | `result` |
| `ReturnValue[K]` | `result(K)` |
| `.ArrayElement` (modifier) | `.[*]` (list form) |
| `Argument[N..M]` | one rule per index (the parser doesn't expand ranges) |

Quick grep recipe for finding propagators for a known package:

```bash
grep "\"taint\"" /drive-testcomp/opentaint-go-rules/codeql/go/ql/lib/ext/<pkg>.model.yml | head -40
```

Replace `<pkg>` with the package path dots (e.g., `fmt`, `strings`,
`path.filepath`, `encoding.json`). Many of these already ship in the
bundled `core/opentaint-config/go-config/config/go-config/<pkg>.yaml`
— check the bundled file first before duplicating.

### Iteration template (apply per CWE)

a. Identify FN URIs: for the active CWE, list URIs in `truth.sarif` (kind=fail) that the report did NOT find.
b. Read 3-5 of those Go source files.
c. Decide the gap kind:
   - **Source missing**: a request access pattern not in the source list.
   - **Sink missing**: a sink not in the sink list.
   - **Propagator missing**: an external method on the source→sink path that isn't in `external-methods-with-rules.yaml` but is in `external-methods-without-rules.yaml` — apply the handbook above.
d. Apply the fix:
   - Source/sink: extend the relevant rule yaml.
   - Propagator: append to `benchmarks/config/go-custom-propagators.yaml` using the YAML format above (create the file on first use with `passThrough: []` as a starting point and add entries below).
e. Re-scan with `scan.sh`; capture new TP%.
f. Verify any new propagator moved from `external-methods-without-rules.yaml` to `external-methods-with-rules.yaml`.
g. Stop when CWE TP ≥ 70% on both benchmarks (or on the only one that has it, in xss's case).

### Task 8: Iterate `cmdinj` to ≥70% TP

**Files:**
- Modify: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/cmdinj.yaml`
- Possibly modify/create: `/drive-testcomp/opentaint-go-rules/benchmarks/config/go-custom-propagators.yaml`

- [ ] **Step 1: List CWE-78 FN URIs in each benchmark**

```bash
python3 - <<'EOF'
import json, pathlib
for bench in ["go-owasp-converted-mutated", "go-sec-code-mutated"]:
    truth = json.loads(pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/{bench}/truth.sarif").read_text())
    rep   = json.loads(pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/{bench}/.opentaint/results/report.sarif").read_text())
    truth_fail = {l["physicalLocation"]["artifactLocation"]["uri"]
                  for r in truth["runs"][0]["results"] if "78" in r.get("ruleId","") or "77" in r.get("ruleId","")
                  for l in r["locations"]
                  if r.get("kind","fail") == "fail"}
    rep_uris   = {l["physicalLocation"]["artifactLocation"]["uri"]
                  for r in rep["runs"][0]["results"]
                  for l in r["locations"]}
    fn = sorted(truth_fail - rep_uris)
    print(f"=== {bench}: {len(fn)} cmdinj FN ===")
    for u in fn[:10]:
        print("  ", u)
EOF
```

- [ ] **Step 2: Inspect 3-5 FN source files**

For each URI listed above (pick 3-5 with different-looking filename patterns), read the Go source:

```bash
head -80 /drive-testcomp/opentaint-go-rules/benchmarks/<bench>/<uri>
```

Identify the source (how is `r` accessed?), the sink (what `exec.X` is called?), and any obstruction (string helpers, helper functions, switch/case mutations).

- [ ] **Step 3: Extend the rule based on what the FN inspection reveals**

If a request-access pattern is missing (e.g. `$R.URL.RequestURI()` — not modeled), add it to `pattern-sources`. If a sink wasn't covered, add it to `pattern-sinks`. Use this edit template:

```bash
# Open /drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/cmdinj.yaml
# Add `- pattern: <missing-pattern>` under the relevant pattern-either.
```

- [ ] **Step 4: If the gap is a propagator, extend `go-custom-propagators.yaml`**

Read `external-methods-without-rules.yaml` for the benchmark whose FNs you're chasing:

```bash
head -30 /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated/.opentaint/results/external-methods-without-rules.yaml
```

Cross-reference with `external-methods-with-rules.yaml` to confirm the method is genuinely uncovered:

```bash
grep -A 1 '<MethodName>' /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated/.opentaint/results/external-methods-with-rules.yaml || echo "not in with-rules — genuinely uncovered"
```

If the file doesn't exist yet, initialise it:

```bash
mkdir -p /drive-testcomp/opentaint-go-rules/benchmarks/config
cat > /drive-testcomp/opentaint-go-rules/benchmarks/config/go-custom-propagators.yaml <<'EOF'
passThrough: []
EOF
```

Then append entries using the **Go YAML approximation format** documented at the top of this Phase (see "Handbook: reading `external-methods-without-rules.yaml`" and "Go YAML approximation format"). The handbook also covers:
- Filtering the list to methods on the active CWE's source→sink path.
- The v1 receiver-method limitation (use rule patterns instead).
- Mining additional propagator definitions from CodeQL ext yamls.
- How to verify the entry "took" via the post-scan diff.

- [ ] **Step 5: Re-scan**

```bash
/drive-testcomp/opentaint-go-rules/benchmarks/scan.sh both | tee /tmp/scan-cmdinj.log
grep -E "^CWE-78|^TOTAL" /tmp/scan-cmdinj.log
```

- [ ] **Step 6: Decide**

If CWE-78 TP% ≥ 70% on **both** benchmarks → commit and move to Task 9.
Otherwise: go back to Step 1 with the new FN list.

- [ ] **Step 7: Commit when class clears 70%**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add rules/go/security/cmdinj.yaml config/go-custom-propagators.yaml
git commit -q -m "cmdinj: iterate to >=70% TP on both benchmarks"
```

### Task 9: Iterate `path-traversal` to ≥70% TP

**Files:**
- Modify: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/path-traversal.yaml`
- Possibly modify: `/drive-testcomp/opentaint-go-rules/benchmarks/config/go-custom-propagators.yaml`

- [ ] **Step 1: List CWE-22 FN URIs**

```bash
python3 - <<'EOF'
import json, pathlib
for bench in ["go-owasp-converted-mutated", "go-sec-code-mutated"]:
    truth = json.loads(pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/{bench}/truth.sarif").read_text())
    rep   = json.loads(pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/{bench}/.opentaint/results/report.sarif").read_text())
    truth_fail = {l["physicalLocation"]["artifactLocation"]["uri"]
                  for r in truth["runs"][0]["results"] if "22" in r.get("ruleId","")
                  for l in r["locations"]
                  if r.get("kind","fail") == "fail"}
    rep_uris   = {l["physicalLocation"]["artifactLocation"]["uri"]
                  for r in rep["runs"][0]["results"]
                  for l in r["locations"]}
    fn = sorted(truth_fail - rep_uris)
    print(f"=== {bench}: {len(fn)} path-traversal FN ===")
    for u in fn[:10]:
        print("  ", u)
EOF
```

- [ ] **Step 2-7: Apply the iteration template** (same shape as Task 8, Steps 2-7), targeting `path-traversal.yaml`.

Commit message: `path-traversal: iterate to >=70% TP on both benchmarks`.

### Task 10: Iterate `sql-injection` to ≥70% TP

**Files:**
- Modify: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/sql-injection.yaml`
- Possibly modify: `/drive-testcomp/opentaint-go-rules/benchmarks/config/go-custom-propagators.yaml`

- [ ] **Step 1: List CWE-89 FN URIs**

Same Python snippet as Task 8 / 9, with the filter `"89" in r.get("ruleId","")`.

- [ ] **Step 2: First check whether beego-orm sinks are needed**

```bash
for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  echo "=== $bench beego-orm usage in FN files ==="
  python3 - <<EOF
import json, pathlib
truth = json.loads(pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/$bench/truth.sarif").read_text())
fn_uris = [l["physicalLocation"]["artifactLocation"]["uri"]
           for r in truth["runs"][0]["results"] if "89" in r.get("ruleId","") and r.get("kind","fail")=="fail"
           for l in r["locations"]]
for uri in fn_uris[:10]:
    f = pathlib.Path(f"/drive-testcomp/opentaint-go-rules/benchmarks/$bench/{uri}")
    if f.exists():
        txt = f.read_text()
        if "beego" in txt or "orm.NewOrm" in txt or "QuerySeter" in txt:
            print("  beego-style:", uri)
EOF
done
```

If beego-orm patterns appear in FN files, extend the sink list. Patterns from the ext-yaml inventory:

```yaml
- pattern: $O.Raw($SQL, ...)
- pattern: $QB.Where($CLAUSE)
- pattern: $QB.From($T)
- pattern: $QB.Select($COLS, ...)
- pattern: $QB.And($CLAUSE)
- pattern: $QB.Or($CLAUSE)
- pattern: $QB.OrderBy($COLS, ...)
- pattern: $QB.GroupBy($COLS, ...)
- pattern: $QB.Having($CLAUSE)
- pattern: $QB.Update($T)
- pattern: $QB.InsertInto($T, ...)
- pattern: $QB.Values($V, ...)
- pattern: $QS.FilterRaw($COL, $CLAUSE)
```

- [ ] **Step 3-7: Apply the iteration template** until CWE-89 TP ≥ 70%.

Commit message: `sql-injection: iterate to >=70% TP on both benchmarks`.

### Task 11: Iterate `xss` to ≥70% TP

**Files:**
- Modify: `/drive-testcomp/opentaint-go-rules/benchmarks/rules/go/security/xss.yaml`
- Possibly modify: `/drive-testcomp/opentaint-go-rules/benchmarks/config/go-custom-propagators.yaml`

XSS is only present in `go-owasp-converted-mutated` (122 truth entries, 44 fail / 78 pass). The exit criterion targets that single benchmark.

- [ ] **Step 1: List CWE-79 FN URIs**

Same Python pattern, filter `"79" in r.get("ruleId","")`.

- [ ] **Step 2-7: Apply the iteration template** until CWE-79 TP ≥ 70% on `go-owasp-converted-mutated`.

Common XSS-specific gaps to anticipate:
- The response writer is sometimes received as `w http.ResponseWriter` and only used via `fmt.Fprintf(w, ...)`. Already covered.
- Embedded `bytes.Buffer` patterns: `buf.WriteString(...)` then `buf.WriteTo(w)` — needs `bytes.WriteTo` propagator if not already.
- `html/template`: autoescaped, so a real XSS via `template.HTML(input)` only happens when user input is cast to `template.HTML`. Add `pattern: template.HTML($X)` as a source if encountered.

Commit message: `xss: iterate to >=70% TP on go-owasp-converted-mutated`.

---

## Phase 5 — Combined verification

### Task 12: Final scan + report

- [ ] **Step 1: Run a clean scan with all rules + propagators**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :projectAnalyzerJar 2>&1 | tail -3   # ensure jar is current
/drive-testcomp/opentaint-go-rules/benchmarks/scan.sh both | tee /tmp/scan-final.log
```

- [ ] **Step 2: Confirm exit criteria**

```bash
grep -E "^CWE|^TOTAL" /tmp/scan-final.log
```

Required:
- `CWE-78` TP% ≥ 70 on both benchmarks
- `CWE-22` TP% ≥ 70 on both benchmarks
- `CWE-89` TP% ≥ 70 on both benchmarks
- `CWE-79` TP% ≥ 70 on `go-owasp-converted-mutated`
- Combined `TOTAL` TP% ≥ 70 (≥ 230 catches across 329 truth-fail)

If any class is below threshold: return to its iteration task (Phase 4) and continue.

- [ ] **Step 3: Verify via `opentaint --experimental scan` end-to-end (CLI integration)**

The scan.sh script already invokes the CLI (`opentaint --experimental scan`), so this is implicitly covered. As a final sanity check, run one benchmark manually:

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated
opentaint --experimental scan \
  --project-model .opentaint/project \
  --analyzer-jar /drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer.jar \
  --autobuilder-jar /drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar \
  --ruleset /drive-testcomp/opentaint-go-rules/benchmarks/rules \
  -o /tmp/final.sarif \
  --track-external-methods
opentaint summary /tmp/final.sarif --show-findings | head -30
```

Expected: a non-trivial number of findings; CLI summary shows the new rule IDs.

- [ ] **Step 4: Final commit**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git add -A
git commit -q -m "Rule development pass complete: combined >=70% TP across both benches"
```

---

## Self-review notes

- **Spec coverage:** every numbered section in the spec maps to a task. Tooling → Tasks 1-2. Initial rules → Tasks 3-6. Baseline scan → Task 7. Iteration loop → Tasks 8-11 (per CWE). Combined verification → Task 12. Out-of-scope items (sanitizers, framework rules unless gap, Approach C refactor, code-based approximations) are not in the plan.
- **No placeholders:** rule yamls are full, scan.sh is full, compare.py is full, iteration steps name the exact files to read and the exact Python snippets to run.
- **Type/path consistency:** all rule yamls live under `benchmarks/rules/go/security/`, the propagator yaml at `benchmarks/config/go-custom-propagators.yaml`, scan.sh references both. Jar paths and `GOIR_SERVER_BINARY` are consistent (scan.sh sets none — it relies on the analyzer JAR's self-resolution which worked in Task 17 of the wiring-phase plan).

> Note for the executor: the analyzer JAR resolves `GOIR_SERVER_BINARY` itself when invoked via the `opentaint` CLI (the CLI sets up the env). The earlier wiring-phase Task 17 noted that the *gradle* `:runProjectAnalyzer` task needs an explicit `GOIR_SERVER_BINARY`, but `opentaint --experimental scan` does not — confirmed during Phase 8 / 19 of the wiring plan.
