package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/seqra/opentaint/internal/globals"
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
	Use:   "run <project-model>",
	Short: "Run detection-rule tests on a compiled project model",
	Long: `Run detection rules against samples annotated with @PositiveRuleSample and
@NegativeRuleSample in the compiled project model.

Exit codes:
  0    All rule tests passed
  1    General failure (configuration or infrastructure error)
  252  Unhandled analyzer exception
  253  Out of memory (try increasing --max-memory)
  254  Analysis timed out (try increasing --timeout)
  255  Project configuration error`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		runTestProject(args[0], testProjectOptions{
			label:             "Rule tests",
			tempDir:           "opentaint-test-rules-*",
			rulesets:          testRulesRuleset,
			outputDir:         testRulesOutputDir,
			timeout:           testRulesTimeout,
			maxMemory:         testRulesMaxMemory,
			ruleIDs:           testRulesRuleID,
			dataflowApprox:    testRulesDataflow,
			passthroughApprox: testRulesPassthrough,
		})
	},
}

// testProjectOptions holds the inputs shared by `test rule run` and `test approximation run`.
type testProjectOptions struct {
	label             string
	tempDir           string
	rulesets          []string
	outputDir         string
	timeout           time.Duration
	maxMemory         string
	ruleIDs           []string
	dataflowApprox    []string
	passthroughApprox []string
}

func runTestProject(projectModelArg string, opts testProjectOptions) {
	projectPath := log.AbsPathOrExit(projectModelArg, "project-model")
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

	if _, err := os.Stat(nativeProjectPath); os.IsNotExist(err) {
		out.Fatalf("Project model not found: %s", nativeProjectPath)
	}

	// Validate max-memory
	maxMemory, err := utils.ParseMemoryValue(opts.maxMemory)
	if err != nil {
		out.Fatalf("Invalid --max-memory value: %s", err)
	}

	// Resolve output directory
	outputDir := opts.outputDir
	if outputDir == "" {
		tmpDir, err := os.MkdirTemp("", opts.tempDir)
		if err != nil {
			out.Fatalf("Failed to create temp dir: %s", err)
		}
		outputDir = tmpDir
		// Note: temp dir is NOT cleaned up so results remain accessible to the agent.
		// The agent should always specify -o to control the output location.
	} else {
		outputDir = log.AbsPathOrExit(outputDir, "output")
		if err := os.MkdirAll(outputDir, 0o755); err != nil {
			out.Fatalf("Failed to create output directory: %s", err)
		}
	}

	// Ensure builtin rules are available
	rulesPath, err := utils.EnsureRulesPath(out)
	if err != nil {
		out.Fatalf("Failed to prepare built-in rules: %s", err)
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
		AddRuleSet(rulesPath).
		EnableRunRuleTests()

	if maxMemory != "" {
		builder.SetMaxMemory(maxMemory)
	}

	// Add user rulesets
	for _, rs := range opts.rulesets {
		absPath := log.AbsPathOrExit(rs, "ruleset")
		builder.AddRuleSet(absPath)
	}

	// Add rule ID filters
	for _, ruleID := range opts.ruleIDs {
		builder.AddRuleID(ruleID)
	}

	analyzerJarPath, err := ensureAnalyzerAvailable()
	if err != nil {
		out.Fatalf("Failed to resolve analyzer: %s", err)
	}
	builder.SetJarPath(analyzerJarPath)

	// Auto-compile .java sources in a --dataflow-approximations dir, as `scan` does.
	addDataflowApproximations(builder, opts.dataflowApprox, analyzerJarPath, projectPath)
	addPassthroughApproximations(builder, opts.passthroughApprox)

	javaRunner := java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Analyzer")).
		WithImageType(java.AdoptiumImageJRE).
		TrySpecificVersion(globals.DefaultJavaVersion)
	if _, err := javaRunner.EnsureJava(); err != nil {
		out.Fatalf("Failed to resolve Java: %s", err)
	}

	cmdErr, err := scanProject(builder, javaRunner)
	if err != nil {
		out.Fatalf("%s failed: %s", opts.label, err)
	}
	analyzerFail := classifyAnalyzerError(cmdErr)

	// Always print output paths so the agent can inspect partial results
	fmt.Printf("Results directory: %s\n", outputDir)
	fmt.Printf("Test results:     %s\n", filepath.Join(outputDir, "test-result.json"))

	if analyzerFail != nil {
		os.Exit(analyzerFail.exitCode)
	}

	fmt.Printf("%s completed successfully\n", opts.label)
}

func init() {
	testRuleCmd.AddCommand(testRuleRunCmd)

	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleset, "ruleset", nil, "Ruleset file or directory to test (repeatable)")
	testRuleRunCmd.Flags().StringVarP(&testRulesOutputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	testRuleRunCmd.Flags().DurationVar(&testRulesTimeout, "timeout", 600*time.Second, "Analysis timeout")
	testRuleRunCmd.Flags().StringVar(&testRulesMaxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g., 8G)")
	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleID, "rule-id", nil, "Run only rules with this ID (repeatable)")
	testRuleRunCmd.Flags().StringArrayVar(&testRulesDataflow, "dataflow-approximations", nil, "Dataflow approximation class directory or Java source directory (repeatable)")
	testRuleRunCmd.Flags().StringArrayVar(&testRulesPassthrough, "passthrough-approximations", nil, "Pass-through approximation YAML file or directory (repeatable)")
}
