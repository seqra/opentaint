package cmd

import (
	"os"
	"time"

	"github.com/seqra/opentaint/internal/testapprox"
	projectutil "github.com/seqra/opentaint/internal/utils/project"
	"github.com/spf13/cobra"
)

var (
	testApproxOutputDir string
	testApproxTimeout   time.Duration
	testApproxMaxMemory string
	testApproxDataflow  []string
)

var testModelRunCmd = &cobra.Command{
	Use:   "run <project-model>",
	Short: "Run dataflow model tests on a compiled project model",
	Long: `Run the samples specified in rule-test.yaml with the supplied dataflow models applied.

A built-in source-to-sink harness rule is applied automatically; positive samples reference the
approximation-rule.yaml rule with id "approximation-rule". The rule matches the project model's
language: taint.Source() to taint.Sink() for a Go project, Taint.source() to Taint.sink() otherwise.

` + testExitCodesHelp("All model tests passed"),
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		ruleDir, err := os.MkdirTemp("", "opentaint-approx-rule-*")
		if err != nil {
			out.Fatalf("Failed to create temp dir for harness rule: %s", err)
		}
		if _, err := testapprox.WriteFixedRule(ruleDir, projectModelLanguage(args[0])); err != nil {
			out.Fatalf("Failed to materialize harness rule: %s", err)
		}

		runTestProject(args[0], testProjectOptions{
			label:          "Model tests",
			tempDir:        "opentaint-test-models-*",
			rulesets:       []string{ruleDir},
			outputDir:      testApproxOutputDir,
			timeout:        testApproxTimeout,
			maxMemory:      testApproxMaxMemory,
			dataflowModels: testApproxDataflow,
		})
	},
}

// projectModelLanguage is "go" for a project model with only Go projects and "java" otherwise.
// A model that cannot be read is reported later by the test run.
func projectModelLanguage(projectModel string) string {
	config, err := projectutil.LoadConfig(projectModel)
	if err == nil && len(config.GoProjects) > 0 && len(config.JavaProjects) == 0 {
		return "go"
	}
	return "java"
}

func init() {
	testModelCmd.AddCommand(testModelRunCmd)
	addTestRunFlags(
		testModelRunCmd,
		&testApproxOutputDir,
		&testApproxTimeout,
		&testApproxMaxMemory,
		&testApproxDataflow,
	)
	testApproximationCmd.AddCommand(deprecatedCommand(testModelRunCmd, "run", "opentaint test model run"))
}
