package cmd

import (
	"os"
	"time"

	"github.com/seqra/opentaint/internal/testapprox"
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
	Short: "Run Java dataflow model tests on a compiled project model",
	Long: `Run the samples that rule-test.yaml declares, with your Java dataflow models applied. The command reports which samples passed. A fixed source-to-sink harness rule is applied automatically. Positive samples point to it with the id model-rule.

The project-model argument is a compiled project model directory from "opentaint compile". Give the model under test with --java-models.

The command writes test-result.json and a test-results.sarif report to --output. If --output is not set, it writes to a temporary directory.

Compile the test project before you run the tests. To read the results, use "opentaint summary".

` + testExitCodesHelp("All model tests passed"),
	Example: `  # Run a model test on a compiled model
  opentaint test model run ./model-test/model --java-models ./my-model

  # Write the results to a directory
  opentaint test model run ./model-test/model --java-models ./my-model -o ./results

  # Recipe: change a model, then make sure the tests stay green
  opentaint test model run ./model-test/model --java-models ./my-model -o ./results
  opentaint summary ./results/test-results.sarif --show-findings`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		ruleDir, err := os.MkdirTemp("", "opentaint-approx-rule-*")
		if err != nil {
			out.Fatalf("Failed to create temp dir for harness rule: %s", err)
		}
		if _, err := testapprox.WriteFixedRule(ruleDir); err != nil {
			out.Fatalf("Failed to materialize harness rule: %s", err)
		}

		runTestProject(args[0], testProjectOptions{
			label:          "Model tests",
			passedLine:     "All model tests passed.",
			tempDir:        "opentaint-test-approximations-*",
			rulesets:       []string{ruleDir},
			outputDir:      testApproxOutputDir,
			timeout:        testApproxTimeout,
			maxMemory:      testApproxMaxMemory,
			dataflowApprox: testApproxDataflow,
		})
	},
}

func init() {
	testModelCmd.AddCommand(testModelRunCmd)
	addTestRunFlags(testModelRunCmd, &testApproxOutputDir, &testApproxTimeout, &testApproxMaxMemory, &testApproxDataflow)
}
