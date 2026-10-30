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
| `opentaint scan` | Analyze projects (auto-detects Maven/Gradle, builds, and scans) |
| `opentaint compile` | Build project model separately from scanning |
| `opentaint project` | Create project model from precompiled JARs/classes |
| `opentaint summary` | View SARIF analysis results |
| `opentaint health` | Show resolved paths for the analyzer, autobuilder, rules, and Java runtime |
| `opentaint test rule` | Create, run, and debug detection-rule tests |
| `opentaint test model` | Create and run dataflow model tests |
| `opentaint model` | Create dataflow model projects |
| `opentaint pull` | Download analyzer dependencies |
| `opentaint update` | Update to latest version |
| `opentaint prune` | Remove stale downloaded artifacts and cached models |

### opentaint scan

Automatically detects Maven/Gradle projects, builds them, and performs security analysis. The source path defaults to the current directory when omitted.

On the first run, the compiled project model is cached in `~/.opentaint/cache/`. Subsequent scans of the same project reuse the cached model, skipping compilation entirely.

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Path to the SARIF report (default: `<model-dir>/sources/opentaint.sarif`) |
| `--recompile` | Force recompilation even if a cached project model exists |
| `--project-model` | Path to a pre-compiled project model (skips compilation) |
| `--timeout`, `-t` | Timeout for analysis (default: `15m`) |
| `--max-memory` | Maximum memory for the analyzer (default: `8G`) |
| `--severity` | Severity levels to report (default: `warning`, `error`) |
| `--ruleset` | YAML rules file or directory (default: `builtin`) |
| `--dry-run` | Validate inputs and show what would run without compiling or scanning |
| `--log-file` | Path to the log file (default: `<cache-dir>/logs/<timestamp>.log`) |

#### Rule-authoring flags

Use these flags when you write custom rules and models:

| Flag | Description |
|------|-------------|
| `--track-external-methods` | Write external-method coverage files next to the SARIF report |
| `--passthrough-models` | Apply pass-through model YAML files or directories (repeatable) |
| `--dataflow-models` | Apply the dataflow models found in a directory (repeatable); see [Applying models](#applying-models) |

Use external-method tracking when a scan may miss flows through library methods. `dropped-external-methods.yaml` lists the methods where taint was killed because no model was available. `approximated-external-methods.yaml` lists the methods already covered by built-in or custom models.

### opentaint health

Show the on-disk paths OpenTaint uses for its dependencies:

```bash
opentaint health
opentaint health --rules
opentaint health --analyzer
```

With no flags, `health` shows the autobuilder, analyzer, built-in rules, and Java runtime. With a single component flag, it prints only the bare path, which is useful for scripts.

| Flag | Description |
|------|-------------|
| `--autobuilder` | Print only the autobuilder JAR path |
| `--analyzer` | Print only the analyzer JAR path |
| `--rules` | Print only the built-in rules path, downloading rules if needed |
| `--runtime` | Print only the Java runtime path |

### opentaint test

The `test` command group is tooling for rule and model development. A test project holds samples and a `rule-test.yaml` that records the verdict each sample must produce.

Java and Go test projects run differently:

- Java: compile the test project with `opentaint compile`, then run the tests on the compiled project model.
- Go: run the tests on the test project directory. The CLI resolves the project dependencies, which may update its `go.mod` and `go.sum`, and loads the samples from source. No `opentaint compile` step is needed.

#### Rule tests

```bash
# Java
opentaint test rule init .opentaint/test-projects/my-rule --language java
opentaint compile .opentaint/test-projects/my-rule/sinks -o .opentaint/test-compiled/my-rule/sinks
opentaint test rule run .opentaint/test-compiled/my-rule/sinks --ruleset .opentaint/rules --ruleset .opentaint/test-projects/my-rule/sinks/test-rules
opentaint test rule reachability java/security/my-rule.yaml:my-rule --project-model .opentaint/test-compiled/my-rule/sinks --ruleset builtin --ruleset .opentaint/rules

# Go
opentaint test rule init .opentaint/test-projects/my-rule --language go
opentaint test rule run .opentaint/test-projects/my-rule/sinks --ruleset .opentaint/rules --ruleset .opentaint/test-projects/my-rule/sinks/test-rules
```

| Command | Description |
|---------|-------------|
| `opentaint test rule init <output-dir> --language LANGUAGE` | Create source and sink test projects with annotated sample support |
| `opentaint test rule run <test-project>` | Run detection-rule tests on a compiled Java project model or a Go test project |
| `opentaint test rule reachability <rule-id> [source-path]` | Trace why a rule can or cannot reach its facts |

`test rule run` also accepts `--dataflow-models` and `--passthrough-models`, so rule tests can apply the models a rule depends on.

#### Model tests

```bash
# Java
opentaint test model init .opentaint/test-projects/my-model \
  --language java \
  --dependency "io.projectreactor:reactor-core:3.8.5"
opentaint compile .opentaint/test-projects/my-model -o .opentaint/test-compiled/my-model
opentaint test model run .opentaint/test-compiled/my-model \
  --dataflow-models .opentaint/dataflow/my-model

# Go
opentaint test model init .opentaint/test-projects/my-model \
  --language go \
  --dependency github.com/acme/library@v1.2.3
opentaint test model run .opentaint/test-projects/my-model \
  --dataflow-models .opentaint/dataflow/my-model
```

| Command | Description |
|---------|-------------|
| `opentaint test model init <output-dir> --language LANGUAGE` | Create a test project with a fixed source-to-sink harness: `Taint.source()` to `Taint.sink(...)` for Java, `taint.Source()` to `taint.Sink(...)` for Go |
| `opentaint test model run <test-project>` | Run dataflow model tests on a compiled Java project model or a Go test project |

`test model run` applies the harness rule for the test project's language. It also accepts `--passthrough-models`.

| Flag | Description |
|------|-------------|
| `--language` | Required test project language, `java` or `go` (`init` only) |
| `--dependency` | Maven coordinate for Java or `module@version` for Go (repeatable, `init` only) |

A Go test project is a Go module with module path `test`, so a sample function is named `test.<Function>` in `rule-test.yaml`.

Rule and model test runs write `test-result.json` and `test-results.sarif` to the selected output directory.

### opentaint compile

Compiles Java and Kotlin projects and generates project models for analysis. For Go modules and workspaces, it writes a project model pointing to the source directory; Go sources are loaded at analysis time. Useful when you want to separate project preparation from scanning or need to inspect the project model.

```bash
opentaint compile --output ./my-project-model /path/to/project
opentaint scan --project-model ./my-project-model
```

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Path to the result project model (required) |
| `--dry-run` | Validate inputs and show what would run without compiling |
| `--log-file` | Path to the log file (default: `<cache-dir>/logs/<timestamp>.log`) |

### opentaint model

A dataflow model describes how taint moves through a library function or method that the analyzer cannot follow. A model is code that refers to the library it models, so models live in their own model project, which pins the library versions. Java and Go models use separate projects.

| Command | Description |
|---------|-------------|
| `opentaint model init <output-dir> --language LANGUAGE` | Create a dataflow model project |
| `opentaint compile models <model-project>` | Compile a Java model project (optional) |

| Flag | Description |
|------|-------------|
| `--language` | Required model language, `java` or `go` (`model init` only) |
| `--dependency` | Maven coordinate for Java or `module@version` for Go (repeatable, `model init` only) |
| `--output`, `-o` | Path to the compiled models (default: `<model-project>/.opentaint/build`, `compile models` only) |

Pin the library versions the target application uses. Running `model init` again keeps the model sources and replaces `build.gradle.kts` for Java or `go.mod` for Go, so pass the full dependency list again.

#### Applying models

`--dataflow-models <dir>` works with `scan`, `test rule run`, and `test model run`. It searches the directory recursively for models in these forms:

| Form | Recognized by | Use |
|------|---------------|-----|
| Java model project | `build.gradle.kts` | Built on demand into `<model-project>/.opentaint/build`; rebuilt when its sources, its dependency pins, or the compiler change |
| Java build output | `approximation.yaml` next to `classes/` | Used as is, for example the output of `compile models` |
| Go model module | `go.mod` with `module opentaint` | Loaded from source |

A directory with one model project per batch, in either language, can therefore be passed as a single flag. The search does not look inside a model it has found and skips directories such as `.opentaint`, `build`, and `.git`. A directory of compiled classes on its own is not a model, and a `go.mod` with another module path is skipped with a warning (passing such a module directly is an error). If the search finds no model in a directory, the CLI prints a warning. Models for a language the analyzed project does not use are ignored.

#### Java models

```bash
opentaint model init .opentaint/dataflow/my-batch \
  --language java \
  --dependency "io.projectreactor:reactor-core:3.8.5"

# Write the model classes under src/main/java, then apply them.
opentaint scan --project-model ./my-project-model \
  --dataflow-models .opentaint/dataflow
```

Name each model class after its target with an `opentaint.` prefix. For example, `opentaint.java.util.Optional` models `java.util.Optional`: its source declares `package opentaint.java.util` and `class Optional`. Existing models that use the `@Approximate` annotation still work, but use the prefix for new models.

Some Kotlin/JVM names are not valid Java names. For these, keep the target package after the prefix and set the real name with `@ApproximatedClassName`, or with `@ApproximatedMethodName` and `@ApproximatedFieldName` for members.

A Java model project compiles against its pinned dependencies and the OpenTaint model support classes only; the analyzed project does not add to them. Run `compile models` to see compilation errors without a scan or test.

#### Go models

```bash
opentaint model init .opentaint/dataflow/my-batch \
  --language go \
  --dependency github.com/acme/library@v1.2.3

# Write the model packages, then apply them.
opentaint scan --project-model ./my-project-model \
  --dataflow-models .opentaint/dataflow
```

A Go model project is a module with module path `opentaint`. Place each model package at `opentaint/` followed by the target import path, and give it the target package name. For example, `opentaint/net/url` models `net/url` and declares `package url`:

```text
my-batch/
├── go.mod                  # module opentaint
└── net/url/model.go        # import path opentaint/net/url
```

```go
package url

// Taint on the input flows to the result.
func QueryUnescape(s string) (string, error) {
	return s, nil
}
```

A model function or method replaces the target with the same name and signature. Target functions that the model does not declare keep their own bodies. A model can add helper functions, methods, variables, constants, types, and struct fields. A model struct lists only the fields that its bodies use: an existing field is matched by name and must have the target field's type, and a new field is added after the target's fields. OpenTaint ignores model `init` functions.

A model can import the analyzed project's packages and their dependencies. Add any other module it needs to the model's `go.mod`, at the version the target application uses, so that the model does not change the dependency versions under analysis.

Model each target package only once across custom and built-in models. A model package applies only when the analyzed project uses its target package.

### opentaint summary

View findings from a SARIF report. By default it prints the Scan Summary; add
`--show-findings` for the detailed listing. The filter flags below narrow the
whole summary (both the counts and the listing); `Rules executed` always
reflects the full set the tool ran.

| Flag | Description |
|------|-------------|
| `--show-findings` | Show all findings |
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

Filters combine as OR within a dimension and AND across dimensions.

### opentaint project

Create project models from precompiled JARs or classes when source code isn't available.

```bash
opentaint project --output ./project-model --source-root /path/to/source \
  --classpath /path/to/app.jar --package com.example

opentaint scan --project-model ./project-model
```

| Flag | Description |
|------|-------------|
| `--output`, `-o` | Output directory for project.yaml (required) |
| `--source-root` | Source root directory (required) |
| `--classpath` | Classpath entries — classes or JAR files (required) |
| `--package` | Project packages (required) |
| `--dependency` | Project dependencies — JAR files |
| `--dry-run` | Validate inputs and show what would run without generating project model |
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
- `--color string` — Color mode (`auto`, `always`, `never`); defaults to `auto` (detects terminal)

For persistent configuration using files or environment variables, see the [Configuration](configuration.md) documentation.
