# Run the CI rule tests with Gradle

This procedure replaces the artifact transfers in
[ci-rules.yaml](../.github/workflows/ci-rules.yaml) with local source builds.
It uses Gradle tasks for compilation, project preparation, analysis and the
result check. It does not download an analyzer JAR, autobuilder JAR or Go server
from CI. It does not use `java -jar` or the OpenTaint CLI distribution.

## What the workflow checks

| CI step | Local Gradle task | Purpose |
| --- | --- | --- |
| Build the test JARs | `:build` in `rules/test` | Compile the Java samples and package the rule resources. |
| Check rule coverage | `:checkRulesCoverage` in `rules/test` | Validate rule YAML and check active rules against `rule-test.yaml`. |
| Run the autobuilder JAR | `:opentaint-jvm-autobuilder:runAutoBuilder` in `core` | Compile and resolve the samples; create a portable Java and Go project. |
| Build/download the Go server | `:opentaint-ir:go:buildGoServer` in `core` | Build the Go SSA server from this checkout. |
| Run the analyzer JAR | `:runProjectAnalyzer` in `core` | Execute the rule samples with `--debug-run-rule-tests`. |
| Check the JSON with jq | `:checkRuleTestResults` from the local init script | Fail for any skipped test, false positive or false negative. |

The JavaExec tasks use this checkout's runtime classpaths. Their dependencies
compile the analyzer and autobuilder. There is no need to package or fetch their
fat JARs. `runProjectAnalyzer` also builds the Go server and sets its absolute
`GOIR_SERVER_BINARY` path through `setupGoEnvironment`.

The workflow's final gate does not fail for `disabled` tests. The local gate has
the same policy. It also rejects a missing file, malformed result lists or a
completely empty result. Analyzer exit status alone does not prove that the rule
expectations pass. The JSON check is required.

## Prerequisites

Use JDK 17, Go 1.26.0 or newer, `protoc` 3.15 or newer, and the checked-in Gradle wrappers. The current
analyzer build targets Java 17. The workflow's JDK 11 analyzer-build step and its
compatibility comment do not match this source revision. Do not copy that JDK
setting into this procedure.

The workflow installs Go 1.25.x, but the current Go server's `go.mod` requires
Go 1.26.0. Preinstall a compatible Go version to avoid an automatic toolchain
download. The protocol uses proto3 optional fields; an older system `protoc`
such as 3.6.1 is insufficient. Put the compatible tools on the login-shell PATH:
the Go build task runs `bash -lc`.

Use a local Gradle dependency cache and Go module cache. Normal dependency
resolution can contact package repositories on a fresh machine. Avoiding CI
artifact downloads is distinct from an entirely offline build. To prohibit all
dependency downloads, populate the caches first, add `--offline` to Gradle, and
use `GOPROXY=off GOTOOLCHAIN=local`. An outer Gradle `--offline` does not reach
the child Gradle commands which the autobuilder starts.

The sample build uses public repositories. The workflow supplies
`SEQRA_GITHUB_ACTOR` and `SEQRA_GITHUB_TOKEN`, but the current sample build does
not read these variables. Do not copy CI secrets into the command line.

## Commands

Run from the repository root. Select a fresh output directory for each run.
Do not reuse an old `project/`, `resolver/` or result file.

```bash
export JAVA_HOME=/path/to/jdk-17
export PATH="$JAVA_HOME/bin:$PATH"
rule_test_repo=$(pwd -P)
rule_test_output="$rule_test_repo/build/rule-validation-$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$rule_test_output"
```

Build the samples and check coverage:

```bash
./rules/test/gradlew -p rules/test :build :checkRulesCoverage \
  --no-daemon --max-workers=2 --console=plain
```

Build the Go server from source:

```bash
./core/gradlew -p core :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=2 --console=plain
```

Create the portable project. The autobuilder invokes the sample Gradle wrapper
again to compile and resolve the complete classpath. Do not run it beside the
sample build: its internal build performs `clean`.

```bash
./core/gradlew -p core :opentaint-jvm-autobuilder:runAutoBuilder \
  --args="--project-root-dir \"$rule_test_repo/rules/test\" --build portable --result-dir \"$rule_test_output/project\" --build-dir \"$rule_test_output/resolver\" --logs-file \"$rule_test_output/autobuild.log\" --verbosity debug" \
  --no-daemon --max-workers=2 --console=plain
```

Run the analyzer and its result gate in the same Gradle invocation:

```bash
./core/gradlew -p core \
  -I "$rule_test_repo/scripts/rule-tests.init.gradle" \
  -PruleTestResults="$rule_test_output/result/test-result.json" \
  :runProjectAnalyzer \
  --args="--project \"$rule_test_output/project/project.yaml\" --output-dir \"$rule_test_output/result\" --logs-file \"$rule_test_output/analyzer.log\" --verbosity debug --semgrep-rule-set \"$rule_test_repo/rules/ruleset\" --debug-run-rule-tests" \
  :checkRuleTestResults \
  --no-daemon --max-workers=2 --console=plain
```

The analyzer task already sets the CI JVM options: 8 GiB maximum heap,
`jdk.util.jar.enableMultiRelease=false` and storage batch size 2,000. Do not
substitute the 16 GiB real-project benchmark configuration. The workflow does
not apply a rule severity filter. Do not add one here.

Keep the model, build log, analyzer log, SARIF and `test-result.json`. Check that
the model and results contain both Java and Go. Project preparation can log a
Java resolution error and still create a Go-only project; a successful process
exit alone does not establish complete sample coverage.

Compare the declared samples with all five result lists too. The Java runner
filters out interfaces, abstract classes and anonymous classes during sample
resolution. An unresolved entry does not enter the `skipped` list. Thus, the CI
gate can pass with uncollected declarations. The
[first local validation](reports/rules-gradle-validation-20261109.md) identifies
two RMI interface samples with this problem. A zero `skipped` count is not proof
that every declared sample ran.

## Bidirectional Java rule validation

The command above reproduces the workflow's default engine. For new-core
validation, add `--ifds-bidirectional` to the analyzer arguments and use a fresh
result directory. The Java rule runner selects the same configured iteration
policy as the ordinary project analyzer. Without the flag, it keeps the legacy
engine. Go samples keep their existing engine in both commands.

Reuse the source-built portable project and run:

```bash
rule_test_bidi_output="$rule_test_output/bidirectional"
mkdir -p "$rule_test_bidi_output"
./core/gradlew -p core \
  -I "$rule_test_repo/scripts/rule-tests.init.gradle" \
  -PruleTestResults="$rule_test_bidi_output/result/test-result.json" \
  :runProjectAnalyzer \
  --args="--project \"$rule_test_output/project/project.yaml\" --output-dir \"$rule_test_bidi_output/result\" --logs-file \"$rule_test_bidi_output/analyzer.log\" --verbosity debug --semgrep-rule-set \"$rule_test_repo/rules/ruleset\" --debug-run-rule-tests --ifds-bidirectional" \
  :checkRuleTestResults \
  --no-daemon --max-workers=2 --console=plain
```

Check actual `BIDI_RUN_START` and `BIDI_ANALYSIS_END` events for each collected
Java sample. Record its latest reached iteration. Do not use a flag or an engine
label alone as proof that the new core ran. A rule suite contains many separate
analyses, so its maximum run label is not one shared project iteration.

Before the runner fix, the flag was ignored by Java rule analysis. The
[first local validation](reports/rules-gradle-validation-20261109.md) is a legacy
result and remains historical evidence. This suite supplements the native
bidirectional tests and bidirectional real-project scans.
