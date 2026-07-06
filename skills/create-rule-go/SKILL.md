---
name: create-rule-go
description: Author and verify an OpenTaint detection rule for a vulnerability class on Go code. Use whenever a Go rule needs to be created for an uncovered vulnerability, or an existing Go rule needs a false-positive or false-negative fix
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Rule (Go)

Author the Go source/sink lib rules a requirement names, write the `go/security` join that
pairs them, and verify against a Go test module's positive/negative samples until every sample
passes

Two roles: the **main** one authors a package's lib rules and the join; a **fix** narrows or
broadens a rule the main scan later flags. Cross-package security joins across many packages are
written by assemble-lib-rules-go; a single new rule's own join is written here

Worked, repo-faithful examples for every vuln class live in
`references/go-semgrep-examples.md` — read it before authoring and copy the closest shape

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Requirements `<requirements>` — the lib unit naming the new sources/sinks, or for a fix the rule to change
- Test module `<test-compiled>` — the compiled Go test model to verify against. Default: `.opentaint/test-compiled/go`
- Test module sources `<test-module>` — where the samples and `rule-test.yaml` live. Default: `.opentaint/test-projects/go`
- Rules directory `<rules-dir>` — where the lib + security rules are written. Default: `.opentaint/rules`
- Tracking file `<tracking-file>` — the lib unit file. Default: `.opentaint/tracking/rules/lib/<name>.yaml`
- PassThrough config `<config-dir>` (optional) — apply on a re-dispatch when the test flow needs a library model that's now built. Default: none

Built-in rules are available at `opentaint health --rules`

## Workflow

### 1. Check existing coverage

Browse built-in Go rules at `opentaint health --rules` for `go/lib` source/sink rules to
reference. A `refs` to a built-in is cheaper and more accurate than a new rule

### 2. Write sources and sinks (`go/lib`)

Prefer referencing built-in `go/lib` rules; write a custom one only when no built-in fits.
Go lib rules are `severity: NOTE` with `options: {lib: true}` and `mode: taint`, use the
typed-receiver pattern syntax (`($R : *http.Request)`), and bind the tainted value as
`$UNTRUSTED`. Scope every rule to its package by wrapping the patterns in a `patterns:` block
led by a `pattern-inside: import "pkg"` guard — the built-in multi-pattern lib rules all do this, so a bare call like
`os.Getenv` or `exec.Command` can't fire in an unrelated file (a single-statement rule can instead
inline the `import "pkg"` line into a bare `pattern: |`, as `go/lib/http-sources-requesturi.yaml` does). Source lib rules use
`pattern-sources` + `label: "$UNTRUSTED"`; sink lib rules use `pattern-sinks` +
`focus-metavariable:` on the tainted argument:

```yaml
rules:
  - id: mylib-source
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted user input originates here
    mode: taint
    pattern-sources:
      - label: "$UNTRUSTED"
        patterns:
          - pattern-inside: |
              import mylib "github.com/acme/mylib"
              ...
          - pattern-either:
              - pattern: "($C : *mylib.Ctx).UserInput($K)"
```

```yaml
rules:
  - id: mylib-sink
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted data reaches a dangerous operation
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import mylib "github.com/acme/mylib"
              ...
          - pattern-either:
              - pattern: "($E : *mylib.Engine).Render($TPL, ...)"
          - focus-metavariable: $TPL
```

Custom lib rules go under `<rules-dir>/go/lib/`, mirroring the built-in layout

### 3. Write the security join (`go/security`)

A lib rule emits nothing alone — pair source and sink in a join. The join references the
**real** lib rules (no generic marker) and is the rule the test manifest names:

```yaml
rules:
  - id: my-ssti-lib-ext
    languages: [go]
    severity: ERROR
    message: Untrusted input reaches a template engine (SSTI)
    metadata:
      cwe: CWE-1336
      short-description: Server-side template injection
    mode: join
    join:
      refs:
        - rule: go/lib/http-sources.yaml#http-sources
          as: src
        - rule: go/lib/my-ssti-sink.yaml#mylib-sink
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
```

For a purely structural rule (a dangerous primitive used at all — weak hash/random), use
`mode: search` + `pattern-either` instead of a join (see the catalog). Security joins go under
`<rules-dir>/go/security/`

### 4. Build the samples and test

Dispatch (or do, when standalone) create-test-project-go to add `PositiveXxx`/`NegativeXxx`
samples and a `rule-test.yaml` entry mapping this rule-id → its samples, then compile the
module. Run the tests, loading your custom rules (`test rule run` auto-loads the built-in
rules, so pass only `<rules-dir>` — a literal `builtin` here would be treated as a path):

```bash
opentaint test rule run <test-compiled> \
  -o .opentaint/test-results/go \
  --ruleset <rules-dir>
```

When the caller passed `<config-dir>`, append `--passthrough-models <config-dir>` —
without it a library function on the test flow drops taint and the positive can't pass. Read
`.opentaint/test-results/go/test-result.json`:

- `falseNegative` (positive didn't trigger) → patterns too narrow; broaden `pattern-either`, check the receiver type and that `$UNTRUSTED` matches across the lib rules and the join `on:`
- `falsePositive` (negative triggered) → patterns too broad; add `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`, or narrow the sink. Inspect the flow that fired with `opentaint summary .opentaint/test-results/go/test-results.sarif --show-findings`
- `skipped` / not run → the manifest entry's rule-id or sample full name is wrong; fix it

### 5. When a positive won't pass after a couple of fixes

A positive that won't trigger after ~2 fix attempts may have a cause no rule edit can fix — a
library function on its flow killing taint. Scan the test model with `--track-external-methods`:

```bash
opentaint scan --project-model <test-compiled> \
  -o .opentaint/test-results/go/diag.sarif \
  --ruleset builtin --ruleset <rules-dir> \
  --track-external-methods
```

Read `dropped-external-methods.yaml` next to it:

- a dropped method on the failing sample's source→sink path → that's the cause: report which methods need a Go passThrough, to be approximated before you're re-dispatched
- nothing dropped and no clear rule cause → report non-convergence for escalation, rather than editing blindly

Either way leave `tests_passing: pending`

## Output

- The new lib rule file(s) under `<rules-dir>/go/lib/` and the security join under `<rules-dir>/go/security/`
- Tracking updated: the lib rules' `rule_id`s/`artifact`, `stages.tests_passing` (per Tracking)
- Report the rule ids, a one-line test summary, and the exact `test rule run` command used
- If blocked (step 5): leave `tests_passing: pending` and report the cause instead

## Tracking

In `<tracking-file>`, once the rules exist and every sample passes:

```yaml
artifact: .opentaint/rules/go/lib/my-ssti-sink.yaml
stages:
  tests_passing: done
```

## Constraints

- Lib rules (source and sink) are `severity: NOTE`, `options: {lib: true}`, and `mode: taint`; only the security join carries `severity: ERROR`
- Security joins (`mode: join`) MUST have `metadata.cwe` and `metadata.short-description`
- Bind the tainted value as `$UNTRUSTED` in every lib source/sink rule; metavariable names must match across `refs` and `on:` or the join won't connect
- Rule IDs must be globally unique; a custom join id must not collide with a built-in (`sql-injection`, `ssrf`, …) or it's dropped silently
- Custom Go rules go under `<rules-dir>/go/{lib,security}/`, never the `java/` tree
- For structural patterns (no dataflow) use `mode: search`; for taint flow use `mode: join`

## Gotchas

- A wrong argument position in a sink focuses the wrong parameter — point `focus-metavariable` at the tainted one
- Refine the rule, never the samples — if a sample is wrong, hand it back to create-test-project-go; don't weaken it to force a pass
- A positive that won't pass because a library function drops taint is not a rule bug — surface it for a Go passThrough (step 5), don't broaden the rule to force it
- The typed-receiver form needs the pointer where the API is pointer-receiver (`($R : *http.Request)`); a value receiver omits the `*`
- Don't unpack or grep the analyzer JAR for built-in rules — its internals aren't a stable API; read the YAMLs from the path `opentaint health --rules` prints
- Keep produced rule YAML comment-free
