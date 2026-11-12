package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var (
	testRulesRuleset     []string
	testRulesOutputDir   string
	testRulesTimeout     time.Duration
	testRulesMaxMemory   string
	testRulesRuleID      []string
	testRulesDataflow    []string
	testRulesPassthrough []string
)

var testRuleRunCmd = &cobra.Command{
	Use:   "run <test-project-model>",
	Short: "Run rule tests on a compiled test project",
	Long:  "Run rule tests on a compiled test project.\n\nArguments:\n  <test-project-model>  Test project compiled with `opentaint compile`",
	Example: `  # Run the tests with the built-in ruleset
  opentaint test rule run .opentaint/test-compiled/my-rule/sinks

  # Run the tests with a custom ruleset
  opentaint test rule run .opentaint/test-compiled/my-rule/sinks \
    --ruleset .opentaint/rules

  # Run the tests of one rule
  opentaint test rule run .opentaint/test-compiled/my-rule/sinks \
    --rule-id java/security/sqli.yaml:sql-injection`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		runTestProject(args[0], testProjectOptions{
			label:               "Rule tests",
			kind:                "rule",
			tempDir:             "opentaint-test-rules-*",
			rulesets:            testRulesRuleset,
			outputDir:           testRulesOutputDir,
			timeout:             testRulesTimeout,
			maxMemory:           testRulesMaxMemory,
			ruleIDs:             testRulesRuleID,
			dataflowModels:      testRulesDataflow,
			passthroughModels:   testRulesPassthrough,
			includeBuiltinRules: true,
		})
	},
}

type testProjectOptions struct {
	label               string
	kind                string
	tempDir             string
	rulesets            []string
	outputDir           string
	timeout             time.Duration
	maxMemory           string
	ruleIDs             []string
	dataflowModels      []string
	passthroughModels   []string
	includeBuiltinRules bool
	// harnessRule loads the harness rule of the model tests. It is written to
	// <test-project-model>/test-rules on every run: a ruleset is a directory, because the tests
	// name the rule by its path in the ruleset, and a fresh copy keeps the tests on the rule of
	// this CLI version.
	harnessRule bool
}

// harnessRuleDir is the directory of the harness rule in a model test project model.
const harnessRuleDir = "test-rules"

func runTestProject(projectModelArg string, opts testProjectOptions) {
	projectPath := log.AbsPathOrExit(projectModelArg, "project-model")
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

	if _, err := os.Stat(nativeProjectPath); err != nil {
		if os.IsNotExist(err) {
			out.Fatalf("No project model at `%s`", projectModelArg)
		}
		out.Fatal(fmt.Sprintf("Failed to access the project model `%s`", projectModelArg), err)
	}
	checkModelInputs(opts.dataflowModels, opts.passthroughModels)
	for _, ruleset := range opts.rulesets {
		if _, err := os.Stat(ruleset); os.IsNotExist(err) {
			out.Fatalf("Ruleset `%s` does not exist", ruleset)
		} else if err != nil {
			out.Fatal(fmt.Sprintf("Failed to access the ruleset `%s`", ruleset), err)
		}
	}

	maxMemory, err := utils.ParseMemoryValue(opts.maxMemory)
	if err != nil {
		out.FatalErr(fmt.Errorf("invalid --max-memory value `%s`: %w", opts.maxMemory, err))
	}

	outputDir := opts.outputDir
	if outputDir == "" {
		tmpDir, err := os.MkdirTemp("", opts.tempDir)
		if err != nil {
			out.Fatal("Failed to create a temporary directory", err)
		}
		outputDir = tmpDir
	} else {
		outputDir = log.AbsPathOrExit(outputDir, "output")
		if err := os.MkdirAll(outputDir, 0o755); err != nil {
			out.Fatal("Failed to create the output directory", err)
		}
	}

	timeoutSeconds := int64(opts.timeout / time.Second)
	if timeoutSeconds <= 0 {
		timeoutSeconds = 600
	}

	builder := NewAnalyzerBuilder().
		SetProject(nativeProjectPath).
		SetOutputDir(outputDir).
		SetSarifFileName("test-results.sarif").
		SetIfdsAnalysisTimeout(timeoutSeconds).
		EnableRunRuleTests()

	if opts.includeBuiltinRules {
		rulesPath, err := utils.EnsureRulesPath(out)
		if err != nil {
			fail("Failed to prepare the built-in ruleset", err)
		}
		builder.AddRuleSet(rulesPath)
	}

	if maxMemory != "" {
		builder.SetMaxMemory(maxMemory)
	}

	for _, rs := range opts.rulesets {
		absPath := log.AbsPathOrExit(rs, "ruleset")
		builder.AddRuleSet(absPath)
	}

	if opts.harnessRule {
		ruleDir := filepath.Join(projectPath, harnessRuleDir)
		if err := os.MkdirAll(ruleDir, 0o755); err != nil {
			out.Fatal("Failed to write the harness rule", err)
		}
		if _, err := testmodel.WriteFixedRule(ruleDir); err != nil {
			out.Fatal("Failed to write the harness rule", err)
		}
		builder.AddRuleSet(ruleDir)
	}

	for _, ruleID := range opts.ruleIDs {
		builder.AddRuleID(ruleID)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		fail("Failed to get the analyzer", err)
	}
	builder.SetJarPath(analyzerJarPath)

	for _, classDir := range compileDataflowModels(opts.dataflowModels, analyzerJarPath) {
		builder.AddDataflowApproximations(classDir)
	}
	addPassthroughModels(builder, opts.passthroughModels)

	javaRunner := newAnalyzerJavaRunner()
	if _, err := javaRunner.EnsureJava(); err != nil {
		fail("Failed to find Java for the analyzer", err)
	}

	// Results left by an earlier run would pass for the results of this one.
	resultPath := filepath.Join(outputDir, "test-result.json")
	sarifPath := filepath.Join(outputDir, "test-results.sarif")
	for _, path := range []string{resultPath, sarifPath} {
		if err := utils.RemoveIfExists(path); err != nil {
			fail("Failed to remove the old test results", err)
		}
	}

	var cmdErr *java.JavaCommandError
	// The spinner shows a failed analyzer run as failed, and the error is printed below.
	if err := out.RunWithSpinner("Running "+opts.kind+" tests", func() error {
		var runErr error
		cmdErr, runErr = scanProject(builder, javaRunner)
		if runErr == nil && cmdErr != nil {
			return cmdErr
		}
		return runErr
	}); err != nil && cmdErr == nil {
		fail("Failed to run the analyzer", err)
	}
	analyzerFail := analyzer.Classify(cmdErr)

	if analyzerFail != nil {
		out.Errorf("%s", analyzerFail.Message)
		suggestions := appendLogSuggestion(nil)
		if analyzerLog, ok := analyzerLogSuggestion(analyzerFail, keepAnalyzerLog(builder.LogsFile(), outputDir)); ok {
			suggestions = append(suggestions, analyzerLog)
		}
		if retry, ok := retrySuggestion(analyzerFail.ExitCode, opts.timeout, opts.maxMemory); ok {
			suggestions = append(suggestions, retry)
		}
		out.Suggestions(suggestions...)
		os.Exit(analyzerFail.ExitCode)
	}

	tr, err := analyzer.LoadTestResult(resultPath)
	if err != nil {
		fail("Failed to read the test results", err)
	}
	out.Blank()

	if tr.Failed() == 0 && len(tr.Success) == 0 {
		out.Warnf("No %s tests ran", opts.kind)
		return
	}
	if tr.Failed() == 0 {
		out.Successf("%s", passedLine(opts.kind, len(tr.Success), len(tr.Disabled)))
		return
	}

	printFailedTests(opts, tr, resultPath)
	suggestions := appendLogSuggestion(nil)
	// The analyzer writes no SARIF report when no sample ran, for example when every sample is
	// skipped.
	if utils.PathExists(sarifPath) {
		suggestions = append(suggestions, output.Suggestion{
			Description: "To inspect the failing samples, run:",
			Command:     utils.NewSummaryCommand(sarifPath).WithShowFindings().Build(),
		})
	}
	out.Suggestions(suggestions...)
	os.Exit(2)
}

// printFailedTests prints the number of passed tests and the failed samples by category.
func printFailedTests(opts testProjectOptions, tr *analyzer.TestResult, resultPath string) {
	sb := out.Section(strings.ToUpper(opts.kind[:1])+opts.kind[1:]+" Test Results").
		Field("Passed", len(tr.Success))
	for _, category := range []struct {
		name    string
		samples []analyzer.TestSampleInfo
	}{
		{"False negatives", tr.FalseNegative},
		{"False positives", tr.FalsePositive},
	} {
		if len(category.samples) == 0 {
			continue
		}
		names := make([]any, len(category.samples))
		for i, sample := range category.samples {
			names[i] = sample.Name()
		}
		sb.Child(out.GroupItem(out.FieldItem(category.name, len(category.samples)), names...))
	}
	if len(tr.Skipped) > 0 {
		sb.Child(out.GroupItem(out.FieldItem("Skipped", len(tr.Skipped)), skippedByRule(tr.Skipped)...))
	}
	if len(tr.Disabled) > 0 {
		sb.Field("Disabled", len(tr.Disabled))
	}
	sb.Field("Results", resultPath).Render()

	out.Blank()
	out.Printf("%s failed: %d of %d", opts.label, tr.Failed(), tr.Failed()+len(tr.Success))
}

// skippedByRule groups the skipped samples under the ID of their rule, in the order in which the
// rules first appear. A sample is skipped when the analyzer loaded no rule or several rules with
// that ID.
func skippedByRule(samples []analyzer.TestSampleInfo) []any {
	var ruleIDs []string
	byRule := map[string][]any{}
	for _, sample := range samples {
		id := sample.Rule.ID()
		if _, ok := byRule[id]; !ok {
			ruleIDs = append(ruleIDs, id)
		}
		byRule[id] = append(byRule[id], sample.Name())
	}
	groups := make([]any, len(ruleIDs))
	for i, id := range ruleIDs {
		groups[i] = out.GroupItem(id, byRule[id]...)
	}
	return groups
}

// passedLine says that all the tests of kind ("rule" or "model") passed, with their number.
func passedLine(kind string, passed, disabled int) string {
	line := fmt.Sprintf("All %d %s tests passed", passed, kind)
	if passed == 1 {
		line = fmt.Sprintf("1 %s test passed", kind)
	}
	if disabled > 0 {
		line += fmt.Sprintf(", %d disabled", disabled)
	}
	return line
}

// keepAnalyzerLog copies the analyzer log of a failed run into dir, next to the results, and
// returns the path of the copy. On an error it returns logsFile.
func keepAnalyzerLog(logsFile, dir string) string {
	if logsFile == "" {
		return ""
	}
	kept := filepath.Join(dir, filepath.Base(logsFile))
	if err := utils.CopyFile(logsFile, kept); err != nil {
		output.LogDebugf("Failed to copy the analyzer log to %s: %v", kept, err)
		return logsFile
	}
	return kept
}

func init() {
	testRuleCmd.AddCommand(testRuleRunCmd)

	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleset, "ruleset", nil, "Rules file or directory to load in addition to the built-in ruleset (repeatable)")
	addTestRunFlags(testRuleRunCmd, &testRulesOutputDir, &testRulesTimeout, &testRulesMaxMemory, &testRulesDataflow, &testRulesPassthrough)
	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleID, "rule-id", nil, "Run only the rule with this ID (repeatable)")
}
