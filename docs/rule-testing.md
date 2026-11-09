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

## Engine scope

This is the workflow's default-engine rule suite. In the current source,
`TestProjectAnalyzer.analyzeTestSample` creates `JIRTaintAnalyzer` without a
`bidiPolicy`. That parameter defaults to `null`. Adding
`--ifds-bidirectional` therefore does not select the new core for Java rule
samples. It can change Spring setup, so it is not an equivalent second run.

Use this suite as an additional validation gate. It does not replace the native
bidirectional suites or the bidirectional real-project scans. Wiring the rule
test runner to the bidirectional policy is a separate change. No analyzer
behavior is changed by this local procedure.
