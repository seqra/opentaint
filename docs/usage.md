# Usage

> **Run without installing:** every `opentaint <command>` below can be run install-free with `npx @seqra/opentaint <command>` (requires Node.js), e.g. `npx @seqra/opentaint scan`. See [Installation](installation.md#npm).

## Scanning Projects

```bash
# Basic scan (current directory, SARIF written to the cached model directory)
opentaint scan

# Scan a specific project
opentaint scan /path/to/project

# With explicit output path
opentaint scan --output results.sarif /path/to/project

# With custom memory allocation
opentaint scan --max-memory 16G /path/to/project

# With specific severity levels
opentaint scan --severity error --severity warning /path/to/project

# With custom ruleset
opentaint scan --ruleset /path/to/rules.yaml /path/to/project

# With timeout
opentaint scan --timeout 5m /path/to/project
```

## Viewing Results

```bash
# Summary
opentaint summary results.sarif

# With all findings
opentaint summary --show-findings results.sarif

# With full code flow and code snippets
opentaint summary --show-findings --verbose-flow --show-code-snippets results.sarif

# Only error-level findings in a path, with up to 3 nesting levels of flow
opentaint summary results.sarif --severity error --path "src/main/**" --max-nesting-level 3 --show-findings

# Focus a single rule by its leaf name
opentaint summary results.sarif --rule-id sql-injection-in-spring-app --show-findings

# Group the listing by severity
opentaint summary results.sarif --group-by severity --show-findings

# Show all code flows for findings with multiple paths
opentaint summary results.sarif --show-findings --code-flow all

# Re-triage a single finding by its partial fingerprint (the abbrev shown as
# the finding header in the listing)
opentaint summary results.sarif --show-findings --partial-fingerprint deadbeefcafe
```

### IDE Integration

Open `results.sarif` with the [SARIF Viewer](https://marketplace.visualstudio.com/items?itemName=MS-SarifVSCode.sarif-viewer) VS Code extension for a rich, interactive experience.

### GitHub Integration

Use [GitHub Action](https://github.com/seqra/opentaint/tree/main/github) for automated analysis and GitHub code scanning integration:

```yaml
- uses: seqra/opentaint/github@v2
  with:
    path: ./
```

### CodeChecker

Use [CodeChecker](https://github.com/Ericsson/codechecker) for advanced result management, tracking, and team collaboration.

## Commands Reference

| Command | Description |
|---------|-------------|
| `opentaint scan` | Analyze projects (auto-detects the build system, builds, and scans) |
| `opentaint compile` | Build project model separately from scanning |
| `opentaint project` | Create project model from precompiled JARs/classes |
| `opentaint summary` | View SARIF analysis results |
| `opentaint triage` | Compare a report against a baseline and record suppressions |
| `opentaint health` | Show dependency paths and report missing components |
| `opentaint test rule` | Create, run, and debug detection-rule tests |
| `opentaint test approximation` | Create and run dataflow-approximation tests |
| `opentaint pull` | Download the analysis toolchain and Java runtime |
| `opentaint update` | Update to latest version |
| `opentaint prune` | Remove old downloaded artifacts and cached models |

### opentaint scan

Automatically detects the project's build system (Maven or Gradle), builds the project, and runs taint analysis over the result. The source path defaults to the current directory when omitted.

On the first run, the compiled project model is cached in `~/.opentaint/cache/`. Subsequent scans of the same project reuse the cached model, skipping compilation entirely.

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Path to the SARIF report (default: `<model-dir>/sources/opentaint.sarif`) |
| `--recompile` | Force recompilation even if a cached project model exists |
| `--project-model` | Path to a pre-compiled project model (skips compilation) |
| `--timeout`, `-t` | Maximum wall-clock time for analysis (default: `15m`) |
| `--max-memory` | Maximum analyzer heap size (default: `8G`) |
| `--severity` | Run only rules at these severity levels: `note`, `warning`, `error` (default: `warning`, `error`) |
| `--ruleset` | Rules to run: a YAML file, a directory of rules files, or `builtin` (default: `builtin`) |
| `--dry-run` | Validate inputs and show what would run without compiling or scanning |
| `--log-file` | Path to the log file (default: `<cache-dir>/logs/<timestamp>.log`) |
| `--rule-id` | Run only rules with this ID (repeatable) |
| `--exclude-rule-id` | Never run rules matching this ID: full id, bare name, or glob (repeatable; overrides `rules.exclude` from the config, composes with `--rule-id`) |

#### Baseline and gating flags

| Flag | Description |
|------|-------------|
| `--baseline` | Previous SARIF report to compare against and inherit suppressions from |
| `--baseline-state` | Write `result.baselineState` and `run.baselineGuid` into the report (needs `--baseline`) |
| `--fingerprint-key` | partialFingerprints key identifying a finding across reports (default `vulnerabilitySourceSinkHash/v1`) |
| `--error-on-findings` | Exit with code 2 when findings remain; with `--baseline`, only new ones count |
| `--error-on-severity` | Restrict `--error-on-findings` to these levels: `error`, `warning`, `note`, `none` (repeatable, default all) |

With `--baseline`, findings the baseline already accepted stay suppressed and
the summary reports how many are new, unchanged, updated, or fixed. See
[Baselines and suppressions](#baselines-and-suppressions).

#### Rule-authoring flags

These flags are to work with custom approximations:

| Flag | Description |
|------|-------------|
| `--track-external-methods` | Write external-method coverage files next to the SARIF report |
| `--passthrough-models` | Apply pass-through model YAML files or directories (repeatable) |
| `--java-models` | Apply Java dataflow model classes or source directories (repeatable) |

Use external-method tracking when a scan may miss flows through library methods. The dropped-methods file shows where taint was killed because no model was available. The approximated-methods file shows methods already covered by built-in or custom models.

### opentaint health

Show the on-disk paths OpenTaint uses for its dependencies:

```bash
opentaint health
opentaint health --rules
opentaint health --analyzer
```

With no flags, `health` shows the autobuilder, analyzer, built-in rules, and Java runtime, and reports whether each is present. With a single component flag, it prints only the bare path, which is useful for scripts. The command exits non-zero when a selected component is missing. Fetch missing components with `opentaint pull`.

| Flag | Description |
|------|-------------|
| `--autobuilder` | Print only the autobuilder JAR path |
| `--analyzer` | Print only the analyzer JAR path |
| `--rules` | Print only the built-in rules path, downloading rules if needed |
| `--runtime` | Print only the Java runtime path |

### opentaint test

The `test` command group is tooling for rule and approximation development.

#### Rule tests

```bash
opentaint test rule init .opentaint/test-projects/my-rule
opentaint compile .opentaint/test-projects/my-rule/sinks -o .opentaint/test-compiled/my-rule/sinks
opentaint test rule run .opentaint/test-compiled/my-rule/sinks --ruleset .opentaint/rules --ruleset .opentaint/test-projects/my-rule/sinks/test-rules
opentaint test rule reachability java/security/my-rule.yaml:my-rule --project-model .opentaint/test-compiled/my-rule/sinks --ruleset builtin --ruleset .opentaint/rules
```

| Command | Description |
|---------|-------------|
| `opentaint test rule init <output-dir>` | Create source and sink test projects with annotated sample support |
| `opentaint test rule run <project-model>` | Run detection-rule tests on a compiled project model |
| `opentaint test rule reachability <rule-id> [source-path]` | Show why a rule does or does not fire |

#### Approximation tests

```bash
opentaint test approximation init .opentaint/test-projects/my-approximation
opentaint compile .opentaint/test-projects/my-approximation -o .opentaint/test-compiled/my-approximation
opentaint test approximation run .opentaint/test-compiled/my-approximation \
  --java-models .opentaint/dataflow/my-approximation
```

| Command | Description |
|---------|-------------|
| `opentaint test approximation init <output-dir>` | Create a test project with a fixed `Taint.source()` to `Taint.sink(...)` harness |
| `opentaint test approximation run <project-model>` | Run dataflow-approximation tests on a compiled project model |

Rule and approximation test runs write `test-result.json` and `test-results.sarif` to the selected output directory.

### opentaint compile

Compiles Java and Kotlin projects and generates project models for analysis. Useful when you want to separate compilation from scanning or need to inspect the project model.

```bash
opentaint compile --output ./my-project-model /path/to/project
opentaint scan --project-model ./my-project-model
```

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Path to the project model directory to create (required, must not exist) |
| `--dry-run` | Validate inputs and show what would run without compiling |
| `--log-file` | Path to the log file (default: `<cache-dir>/logs/<timestamp>.log`) |

### opentaint summary

View findings from a SARIF report. By default it prints the Scan Summary. Add
`--show-findings` for the detailed listing. The filter flags below narrow the
whole summary (both the counts and the listing). `Rules executed` always
reflects the full set the tool ran.

| Flag | Description |
|------|-------------|
| `--show-findings` | Show every finding in the SARIF report |
| `--show-code-snippets` | Show code snippets for each finding |
| `--verbose-flow` | Show full code flow steps for each finding |
| `--path` | Show only findings whose file path matches this glob (`**` supported, repeatable) |
| `--severity` | Show only findings of this SARIF level: `error`, `warning`, `note`, `none` (repeatable) |
| `--rule-id` | Show only findings for this rule: full id, leaf name (after `:` or last `.`), or glob over the full id (repeatable) |
| `--partial-fingerprint` | Show only findings whose partial fingerprint starts with this value, git-hash style (repeatable). With `--show-findings`, each finding's header reads `Fingerprint: <abbrev>` — copy that value back into this flag to re-focus on it. |
| `--partial-fingerprint-key` | partialFingerprints key matched by `--partial-fingerprint` (default `vulnerabilityWithTraceHash/v1`) |
| `--max-nesting-level` | Collapse code-flow steps deeper than this call-nesting level (`-1` = no cap). Best-effort: depth is derived from step kinds and method names, so flows lacking method info may over-collapse |
| `--group-by` | Group the `--show-findings` listing by `severity`, `rule-id`, or `file-path` (default `file-path`) |
| `--code-flow` | Render code flows: `all`, a 1-based index, or unset (first flow only). On multi-flow findings the listing also shows a `Code flows: <N>` field. |
| `--baseline` | Compare against this SARIF report and show new/unchanged/updated/fixed counts. The file is never modified. |
| `--baseline-state` | Show only findings in this state: `new`, `unchanged`, `updated`, `absent` (repeatable, needs `--baseline`) |
| `--suppressed` | Include suppressed findings in the listing (hidden by default) |
| `--fingerprint-key` | partialFingerprints key identifying a finding across reports (default `vulnerabilitySourceSinkHash/v1`) |

Filters combine as OR within a dimension and AND across dimensions.

### opentaint triage

Compare a SARIF report against a baseline and record decisions about findings.
Nothing is ever deleted: an accepted or deferred finding stays in the report,
marked with a SARIF suppression recording what was decided and why.

```bash
# What changed since the last release? Modifies nothing.
opentaint triage scan.sarif --baseline release.sarif

# We will not fix this one
opentaint triage scan.sarif --accept q3Vf9k --justification "sink is a constant"

# We are not fixing this one yet
opentaint triage scan.sarif --defer 8bc1d2 --justification "waiting on OT-412"
```

| Flag | Description |
|------|-------------|
| `--baseline` | Previous SARIF report to compare against and inherit suppressions from |
| `--baseline-state` | Write `result.baselineState` and `run.baselineGuid` into the report (needs `--baseline`) |
| `--accept` | Accept the finding with this fingerprint prefix — won't fix (repeatable) |
| `--defer` | Defer the finding with this fingerprint prefix — not fixing for now (repeatable) |
| `--unsuppress` | Remove the suppression from the finding with this fingerprint prefix (repeatable) |
| `--justification` | Why the finding is accepted or deferred (required with `--accept`/`--defer`) |
| `--output`, `-o` | Write the triaged report here (default: rewrite the input in place) |
| `--show-findings` | List the findings, not just the summary |
| `--suppressed` | Include suppressed findings in the listing |
| `--fingerprint-key` | partialFingerprints key identifying a finding across reports (default `vulnerabilitySourceSinkHash/v1`) |
| `--error-on-findings` | Exit with code 2 when findings remain; with `--baseline`, only new ones count |
| `--error-on-severity` | Restrict `--error-on-findings` to these levels (repeatable, default all) |

A finding is named by a fingerprint prefix, git-style — the value shown as
`Fingerprint:` by `opentaint summary --show-findings`. An ambiguous or unknown
prefix is an error, never a guess.

Exit codes:

| Code | Meaning |
|------|---------|
| 0 | Triage completed |
| 1 | General failure (bad input, unreadable report) |
| 2 | Findings remain and `--error-on-findings` was set |

## Baselines and suppressions

A baseline is just a SARIF report you kept. Two independent things are built on
it, both expressed in SARIF 2.1.0's own vocabulary.

**Baseline comparison** answers "is this new?". `--baseline old.sarif`
classifies every finding as new, unchanged, updated (same source and sink, a
different path through the code), or fixed. By default this only affects what is
printed; `--baseline-state` also writes `result.baselineState` and
`run.baselineGuid` into the report. Findings are matched by fingerprint, not by
line number, so moving code around does not invent new findings.

**Suppression** answers "did a human accept this?". Presence in a baseline is
not acceptance — a baseline entry that carries no suppression only makes a
finding `unchanged`. A finding is suppressed only when someone decided so with
`opentaint triage`, which writes a SARIF suppression:

| Decision | `suppression.status` | Meaning |
|----------|----------------------|---------|
| `--accept` | `accepted` | The team will not fix this |
| `--defer` | `underReview` | The team is not fixing this for now |

Both hide the finding from the listing and from the failure gate, and both
require a justification. A deferral does not expire on its own; the summary's
`Deferred` count is what keeps it visible.

Decisions travel forward through the baseline. A finding matching a baseline
entry that carries a suppression inherits it verbatim — same status, same
justification, same guid — so a decision is authored once and re-attached by
every later scan for as long as the fingerprint matches. When the code is fixed
and the finding disappears, the decision retires with it.

A typical CI setup keeps the last accepted report and fails only on new work:

```bash
opentaint scan --baseline baselines/main.sarif -o scan.sarif \
    --error-on-findings --error-on-severity error,warning .
```

Suppressions read from a baseline are interpreted conservatively: an entry whose
status is `rejected`, or anything unrecognised, never hides a finding, and the
summary counts it under `Not honored` so nothing disappears quietly.

### opentaint project

Create project models from precompiled JARs or classes when source code isn't available.

```bash
opentaint project --output ./project-model --source-root /path/to/source \
  --classpath /path/to/app.jar --package com.example

opentaint scan --project-model ./project-model
```

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Directory to write the generated project model (required, must not exist) |
| `--source-root` | Path to the project source root (required) |
| `--classpath` | Classpath entries: compiled classes directories or JAR files (required, repeatable) |
| `--package` | Packages to include in the generated model (required, repeatable) |
| `--dependency` | Additional dependency JAR files on the compile classpath (repeatable) |
| `--dry-run` | Validate inputs and show what would run without generating the project model |
| `--log-file` | Path to the log file (default: `<cache-dir>/logs/<timestamp>.log`) |

## Model Caching

When `opentaint scan` compiles a project, the resulting project model is cached in `~/.opentaint/cache/`. The cache directory name is derived from the project path (e.g. `my-project-a1b2c3d4`).

On subsequent scans of the same project, the cached model is reused automatically — compilation is skipped entirely. This makes repeated scans significantly faster.

```bash
# First scan: compiles and caches the model
opentaint scan /path/to/project

# Second scan: reuses the cached model (no compilation)
opentaint scan /path/to/project

# Force recompilation (e.g. after code changes)
opentaint scan --recompile /path/to/project
```

If another scan is actively compiling the same project, the scan aborts with an error instead of compiling concurrently. Multiple read-only scans against the same cached model can run in parallel.

To remove all cached models:

```bash
opentaint prune
```

When `--output` is not specified, the SARIF report is written next to the cached model at `<model-dir>/sources/opentaint.sarif`.

## Global Options

These options apply to all commands:

- `--config string` — Path to configuration file
- `--java-version int` — Java version for analyzer (default: 21)
- `--quiet` / `-q` — Suppress interactive output (spinners, progress bars, JAR streaming)
- `--debug` / `-d` — Enable debug output (stream JAR subprocess output, show debug fields)
- `--color string` — Color mode (`auto`, `always`, `never`), defaults to `auto` (detects terminal)

For persistent configuration using files or environment variables, see the [Configuration](configuration.md) documentation.
