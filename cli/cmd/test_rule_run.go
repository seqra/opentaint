package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
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
	Use:   "run <project-model>",
	Short: "Run detection-rule tests on a compiled project model",
	Long: `Run detection rules against the samples declared in rule-test.yaml and report which passed. The built-in rules are always included.

The project-model argument is a compiled project model directory, produced by opentaint compile. Add your own rules with --ruleset, narrow the run to specific rules with --rule-id, and apply models with --java-models or --passthrough-models.

Results are written as test-result.json and a test-results.sarif report to --output, or to a temporary directory when unset.

Compile the test project with opentaint compile before running. Inspect the results afterward with opentaint summary.

` + testExitCodesHelp("All rule tests passed"),
	Example: `  # Run the built-in rules against a compiled model
  opentaint test rule run ./rule-tests/sinks/model

  # Test a custom ruleset and write results to a directory
  opentaint test rule run ./rule-tests/sinks/model --ruleset ./rules -o ./results

  # Run only one rule
  opentaint test rule run ./rule-tests/sinks/model --rule-id <rule-id>`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		runTestProject(args[0], testProjectOptions{
			label:               "Rule tests",
			passedLine:          "All rule tests passed.",
			tempDir:             "opentaint-test-rules-*",
			rulesets:            testRulesRuleset,
			outputDir:           testRulesOutputDir,
			timeout:             testRulesTimeout,
			maxMemory:           testRulesMaxMemory,
			ruleIDs:             testRulesRuleID,
			dataflowApprox:      testRulesDataflow,
			passthroughApprox:   testRulesPassthrough,
			includeBuiltinRules: true,
		})
	},
}

type testProjectOptions struct {
	label               string
	passedLine          string // success status line, matching the documented exit-code 0 row
	tempDir             string
	rulesets            []string
	outputDir           string
	timeout             time.Duration
	maxMemory           string
	ruleIDs             []string
	dataflowApprox      []string
	passthroughApprox   []string
	includeBuiltinRules bool
}

func runTestProject(projectModelArg string, opts testProjectOptions) {
	projectPath := log.AbsPathOrExit(projectModelArg, "project-model")
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

	if _, err := os.Stat(nativeProjectPath); err != nil {
		if os.IsNotExist(err) {
			out.Fatalf("Project model not found: %s", nativeProjectPath)
		}
		out.Fatalf("Cannot access project model %s: %s", nativeProjectPath, err)
	}

	maxMemory, err := utils.ParseMemoryValue(opts.maxMemory)
	if err != nil {
		out.Fatalf("Invalid --max-memory value: %s", err)
	}

	outputDir := opts.outputDir
	if outputDir == "" {
		tmpDir, err := os.MkdirTemp("", opts.tempDir)
		if err != nil {
			out.Fatalf("Failed to create temp dir: %s", err)
		}
		outputDir = tmpDir
	} else {
		outputDir = log.AbsPathOrExit(outputDir, "output")
		if err := os.MkdirAll(outputDir, 0o755); err != nil {
			out.Fatalf("Failed to create output directory: %s", err)
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
			failf("Failed to prepare built-in rules: %s", err)
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

	for _, ruleID := range opts.ruleIDs {
		builder.AddRuleID(ruleID)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		failf("Failed to resolve analyzer: %s", err)
	}
	builder.SetJarPath(analyzerJarPath)

	addDataflowApproximations(builder, opts.dataflowApprox, analyzerJarPath, projectPath)
	addPassthroughApproximations(builder, opts.passthroughApprox)

	javaRunner := newAnalyzerJavaRunner()
	if _, err := javaRunner.EnsureJava(); err != nil {
		failf("Failed to resolve Java for analyzer: %s", err)
	}

	cmdErr, err := scanProject(builder, javaRunner)
	if err != nil {
		failf("%s failed: %s", opts.label, err)
	}
	analyzerFail := analyzer.Classify(cmdErr)

	resultPath := filepath.Join(outputDir, "test-result.json")
	out.Printf("Results directory: %s", outputDir)
	out.Printf("Test results:     %s", resultPath)

	if analyzerFail != nil {
		out.Error(analyzerFail.Message)
		// Test runs do not activate file logging, so the log pointer is usually
		// absent. For resource failures suggest the retry with more resources.
		// Otherwise the --debug re-run is the actionable way to see what failed.
		hint := output.Suggestion{
			Description: "To stream the analyzer output, re-run with --debug:",
			Command:     withFlag(rerunWithoutDryRun(), "--debug"),
		}
		if retry, ok := retrySuggestion(analyzerFail.ExitCode, opts.timeout, opts.maxMemory); ok {
			hint = retry
		}
		out.Suggestions(append(appendLogSuggestion(nil), hint)...)
		os.Exit(analyzerFail.ExitCode)
	}

	tr, err := analyzer.LoadTestResult(resultPath)
	if err != nil {
		failf("%s produced no readable test-result.json: %s", opts.label, err)
	}
	out.Printf("Passed: %d, failed: %d (false negatives: %d, false positives: %d, skipped: %d), disabled: %d",
		len(tr.Success), tr.Failed(), len(tr.FalseNegative), len(tr.FalsePositive), len(tr.Skipped), len(tr.Disabled))

	viewResultsCommand := utils.NewSummaryCommand(filepath.Join(outputDir, "test-results.sarif")).WithShowFindings().Build()

	if tr.Failed() > 0 {
		out.Error(fmt.Sprintf("%s failed", opts.label))
		out.Suggestions(append(appendLogSuggestion(nil), output.Suggestion{
			Description: "To inspect the failing samples, run:",
			Command:     viewResultsCommand,
		})...)
		os.Exit(2)
	}

	out.Successf("%s", opts.passedLine)
	suggest("To view the test results, run:", viewResultsCommand)
}

func init() {
	testRuleCmd.AddCommand(testRuleRunCmd)

	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleset, "ruleset", nil, "Ruleset to test: a YAML file or a directory of .yml or .yaml files (repeatable)")
	addTestRunFlags(testRuleRunCmd, &testRulesOutputDir, &testRulesTimeout, &testRulesMaxMemory, &testRulesDataflow)
	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleID, "rule-id", nil, "Run only rules with this ID (repeatable)")
	testRuleRunCmd.Flags().StringArrayVar(&testRulesPassthrough, "passthrough-models", nil, "Pass-through models: a YAML file or a directory of them (repeatable)")
	testRuleRunCmd.Flags().StringArrayVar(&testRulesPassthrough, "passthrough-approximations", nil, "Pass-through models: a YAML file or a directory of them (repeatable)")
	_ = testRuleRunCmd.Flags().MarkDeprecated("passthrough-approximations", "use --passthrough-models")
}
