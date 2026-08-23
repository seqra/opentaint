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

var testApproximationRunCmd = &cobra.Command{
	Use:   "run <project-model>",
	Short: "Run dataflow-approximation tests on a compiled project model",
	Long: `Run the samples declared in rule-test.yaml with the supplied dataflow approximations applied and report which passed. A fixed source-to-sink harness rule is applied automatically; positive samples reference it by id approximation-rule.

The project-model argument is a compiled project model directory, produced by opentaint compile. Supply the approximation under test with --dataflow-approximations.

Results are written as test-result.json and a test-results.sarif report to --output, or to a temporary directory when unset.

Compile the test project with opentaint compile before running. Inspect the results afterward with opentaint summary.

` + testExitCodesHelp("All approximation tests passed"),
	Example: `  # Run an approximation test against a compiled model
  opentaint test approximation run ./approx-test/model --dataflow-approximations ./approx

  # Write results to a directory
  opentaint test approximation run ./approx-test/model --dataflow-approximations ./approx -o ./results`,
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
			label:          "Approximation tests",
			passedLine:     "All approximation tests passed.",
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
	testApproximationCmd.AddCommand(testApproximationRunCmd)
	addTestRunFlags(testApproximationRunCmd, &testApproxOutputDir, &testApproxTimeout, &testApproxMaxMemory, &testApproxDataflow)
}
