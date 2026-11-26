package cmd

import (
	"time"

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
	Use:   "run <test-project-model>",
	Short: "Run dataflow model tests on a compiled test project",
	Long:  "Run dataflow model tests on a compiled test project.\n\nArguments:\n  <test-project-model>  Test project compiled with `opentaint compile`",
	Example: `  # Test a model project
  opentaint test model run .opentaint/test-compiled/my-model \
    --dataflow-models .opentaint/dataflow

  # Test pass-through models
  opentaint test model run .opentaint/test-compiled/my-model \
    --passthrough-models .opentaint/pass-through`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		runTestProject(args[0], testProjectOptions{
			label:             "Model tests",
			kind:              "model",
			tempDir:           "opentaint-test-models-*",
			harnessRule:       true,
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
	testApproximationCmd.AddCommand(deprecatedCommand(testModelRunCmd, "opentaint test approximation run", "opentaint test model run"))
}
