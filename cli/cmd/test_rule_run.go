package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/log"
	projectutil "github.com/seqra/opentaint/internal/utils/project"
	"github.com/seqra/opentaint/internal/validation"
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
	Use:   "run <test-project>",
	Short: "Run detection-rule tests on a test project",
	Long: `Run detection rules against the samples specified in rule-test.yaml in the
test project.

` + testProjectArgHelp + `

` + testExitCodesHelp("All rule tests passed"),
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath, projectConfig := prepareTestProject(args[0])
		runTestProject(projectPath, projectConfig, testProjectOptions{
			label:               "Rule tests",
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

// testProjectArgHelp describes the <test-project> argument of the test run commands.
const testProjectArgHelp = `<test-project> is a Go test project directory, or the project model that
'opentaint compile <test-project> -o <project-model>' writes for it. A Java test project
must be compiled first. Go projects are tidied and built before the tests run.`

// prepareTestProject returns the project model to test and its configuration. A Go test
// project directory has no project model, so one is written for it to a temporary directory.
// Every Go project is tidied and built first: the samples are written after the test project
// is created and may import modules its go.mod does not list yet, and a sample that does not
// compile would otherwise only show up as a missing entry point in the analyzer log.
func prepareTestProject(arg string) (string, *projectutil.Config) {
	projectPath := log.AbsPathOrExit(arg, "test-project")
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

	if _, err := os.Stat(nativeProjectPath); err != nil {
		if !os.IsNotExist(err) {
			out.Fatalf("Cannot access project model %s: %s", nativeProjectPath, err)
		}
		if !validation.IsGoSourceProject(projectPath) {
			out.Error(fmt.Sprintf("Project model not found: %s", nativeProjectPath))
			suggest("Compile a Java test project first:",
				utils.NewCompileCommand(arg).WithOutput("<project-model>").Build())
			os.Exit(1)
		}
		modelPath, err := os.MkdirTemp("", "opentaint-test-project-*")
		if err != nil {
			out.Fatalf("Failed to create temp dir for the project model: %s", err)
		}
		if err := projectutil.WriteGoProjectModel(projectPath, modelPath); err != nil {
			out.Fatalf("Failed to write the project model: %s", err)
		}
		projectPath = modelPath
	}

	projectConfig, err := projectutil.LoadConfig(projectPath)
	if err != nil {
		out.Fatalf("Failed to read the project model: %s", err)
	}
	for _, goProject := range projectConfig.GoProjects {
		if err := prepareGoProject(projectPath, goProject.ProjectDir); err != nil {
			out.Fatalf("%s", err)
		}
	}
	return projectPath, projectConfig
}

// prepareGoProject tidies and builds the Go module of a project model's Go project. A workspace
// root without a go.mod of its own is left alone.
func prepareGoProject(projectModelPath, projectDir string) error {
	if !filepath.IsAbs(projectDir) {
		projectDir = filepath.Join(projectModelPath, projectDir)
	}
	if info, err := os.Stat(filepath.Join(projectDir, "go.mod")); err != nil || info.IsDir() {
		return nil
	}
	if err := testproject.TidyGo(projectDir); err != nil {
		return err
	}
	return testproject.BuildGo(projectDir)
}

func runTestProject(projectPath string, projectConfig *projectutil.Config, opts testProjectOptions) {
	nativeProjectPath := filepath.Join(projectPath, "project.yaml")

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
			out.Fatalf("Failed to prepare built-in rules: %s", err)
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
		out.Fatalf("Failed to resolve analyzer: %s", err)
	}
	builder.SetJarPath(analyzerJarPath)

	addDataflowModels(builder, opts.dataflowModels, analyzerJarPath)
	addPassthroughModels(builder, opts.passthroughModels)

	goServerPath := ""
	if len(projectConfig.GoProjects) > 0 {
		goServerPath, err = ensureGoServerAvailable()
		if err != nil {
			out.Fatalf("Failed to resolve the Go server: %s", err)
		}
	}

	javaRunner := newAnalyzerJavaRunner(goServerPath)
	if _, err := javaRunner.EnsureJava(); err != nil {
		out.Fatalf("Failed to resolve Java for analyzer: %s", err)
	}

	cmdErr, err := scanProject(builder, javaRunner)
	if err != nil {
		out.Fatalf("%s failed: %s", opts.label, err)
	}
	analyzerFail := analyzer.Classify(cmdErr)
	if analyzerFail != nil {
		out.Error(analyzerFail.Message)
	}

	resultPath := filepath.Join(outputDir, "test-result.json")
	fmt.Printf("Results directory: %s\n", outputDir)
	fmt.Printf("Test results:     %s\n", resultPath)

	if analyzerFail != nil {
		if analyzerLog, ok := analyzerLogSuggestion(analyzerFail, builder.LogsFile()); ok {
			out.Suggestions(analyzerLog)
		}
		os.Exit(analyzerFail.ExitCode)
	}

	tr, err := analyzer.LoadTestResult(resultPath)
	if err != nil {
		out.Fatalf("%s produced no readable test-result.json: %s", opts.label, err)
	}
	fmt.Printf("Passed: %d, failed: %d (false negatives: %d, false positives: %d, skipped: %d), disabled: %d\n",
		len(tr.Success), tr.Failed(), len(tr.FalseNegative), len(tr.FalsePositive), len(tr.Skipped), len(tr.Disabled))
	if tr.Failed() > 0 {
		out.Error(fmt.Sprintf("%s failed", opts.label))
		os.Exit(2)
	}

	fmt.Printf("%s completed successfully\n", opts.label)
}

func init() {
	testRuleCmd.AddCommand(testRuleRunCmd)

	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleset, "ruleset", nil, "Ruleset file or directory to test (repeatable)")
	addTestRunFlags(
		testRuleRunCmd,
		&testRulesOutputDir,
		&testRulesTimeout,
		&testRulesMaxMemory,
		&testRulesDataflow,
		&testRulesPassthrough,
	)
	testRuleRunCmd.Flags().StringArrayVar(&testRulesRuleID, "rule-id", nil, "Run only rules with this ID (repeatable)")
}
