package cmd

import (
	"os"
	"time"

	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/spf13/cobra"
)

var (
	testModelOutputDir   string
	testModelTimeout     time.Duration
	testModelMaxMemory   string
	testModelDataflow    []string
	testModelPassthrough []string
)

var testModelRunCmd = &cobra.Command{
	Use:   "run <project-model>",
	Short: "Run dataflow model tests on a compiled test project",
	Long: `Run the samples that rule-test.yaml declares with the --dataflow-models models applied and report which samples passed

Arguments:
  <project-model>  Test project compiled with "opentaint compile"

The results are written to test-result.json and test-results.sarif in --output, or in a temporary directory when --output is not set

` + testExitCodesHelp("All model tests passed"),
	Example: `  # Test a model project and keep the results
  opentaint test model run ./model-test/model --dataflow-models ./jackson-models -o ./results`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		ruleDir, err := os.MkdirTemp("", "opentaint-model-rule-*")
		if err != nil {
			out.Fatalf("Failed to create temp dir for harness rule: %s", err)
		}
		if _, err := testmodel.WriteFixedRule(ruleDir); err != nil {
			out.Fatalf("Failed to materialize harness rule: %s", err)
		}

		runTestProject(args[0], testProjectOptions{
			label:             "Model tests",
			passedLine:        "All model tests passed.",
			tempDir:           "opentaint-test-models-*",
			rulesets:          []string{ruleDir},
			outputDir:         testModelOutputDir,
			timeout:           testModelTimeout,
			maxMemory:         testModelMaxMemory,
			dataflowModels:    testModelDataflow,
			passthroughModels: testModelPassthrough,
		})
	},
}

func init() {
	testModelCmd.AddCommand(testModelRunCmd)
	addTestRunFlags(testModelRunCmd, &testModelOutputDir, &testModelTimeout, &testModelMaxMemory, &testModelDataflow, &testModelPassthrough)
	testApproximationCmd.AddCommand(deprecatedCommand(testModelRunCmd, "run", "opentaint test model run"))
}
