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
			passedLine:          "All rule tests passed.",
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
	passedLine          string
	tempDir             string
	rulesets            []string
	outputDir           string
	timeout             time.Duration
	maxMemory           string
	ruleIDs             []string
	dataflowModels      []string
	passthroughModels   []string
	includeBuiltinRules bool
}

func runTestProject(projectModelArg string, opts testProjectOptions) {
	projectPath := log.AbsPathOrExit(projectModelArg, "project-model")
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

	if _, err := os.Stat(nativeProjectPath); err != nil {
		if os.IsNotExist(err) {
			out.Fatalf("No project model at `%s`", projectModelArg)
		}
		out.Fatal(fmt.Sprintf("Failed to access the project model `%s`", projectModelArg), err)
	}

	maxMemory, err := utils.ParseMemoryValue(opts.maxMemory)
	if err != nil {
		out.FatalErr(err)
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

	for _, ruleID := range opts.ruleIDs {
		builder.AddRuleID(ruleID)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		fail("Failed to get the analyzer", err)
	}
	builder.SetJarPath(analyzerJarPath)

	addDataflowModels(builder, opts.dataflowModels, analyzerJarPath)
	addPassthroughModels(builder, opts.passthroughModels)

	javaRunner := newAnalyzerJavaRunner()
	if _, err := javaRunner.EnsureJava(); err != nil {
		fail("Failed to find Java for the analyzer", err)
	}

	cmdErr, err := scanProject(builder, javaRunner)
	if err != nil {
		fail("Failed to run the analyzer", err)
	}
	analyzerFail := analyzer.Classify(cmdErr)

	resultPath := filepath.Join(outputDir, "test-result.json")
	out.Printf("Results directory: %s", outputDir)
	out.Printf("Test results:     %s", resultPath)

	if analyzerFail != nil {
		out.Errorf("%s", analyzerFail.Message)
		suggestions := appendLogSuggestion(nil)
		if analyzerLog, ok := analyzerLogSuggestion(analyzerFail, builder.LogsFile()); ok {
			suggestions = append(suggestions, analyzerLog)
		}
		hint := output.Suggestion{
			Description: "To stream the analyzer output, re-run with --debug:",
			Command:     withFlag(rerunWithoutDryRun(), "--debug"),
		}
		if retry, ok := retrySuggestion(analyzerFail.ExitCode, opts.timeout, opts.maxMemory); ok {
			hint = retry
		}
		out.Suggestions(append(suggestions, hint)...)
		os.Exit(analyzerFail.ExitCode)
	}

	tr, err := analyzer.LoadTestResult(resultPath)
	if err != nil {
		fail("Failed to read the test results", err)
	}
	out.Printf("Passed: %d, failed: %d (false negatives: %d, false positives: %d, skipped: %d), disabled: %d",
		len(tr.Success), tr.Failed(), len(tr.FalseNegative), len(tr.FalsePositive), len(tr.Skipped), len(tr.Disabled))

	viewResultsCommand := utils.NewSummaryCommand(filepath.Join(outputDir, "test-results.sarif")).WithShowFindings().Build()

	if tr.Failed() > 0 {
		out.Printf("%s failed", opts.label)
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

	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleset, "ruleset", nil, "Rules file or directory to load in addition to the built-in ruleset (repeatable)")
	addTestRunFlags(testRuleRunCmd, &testRulesOutputDir, &testRulesTimeout, &testRulesMaxMemory, &testRulesDataflow, &testRulesPassthrough)
	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleID, "rule-id", nil, "Run only the rule with this ID (repeatable)")
}
