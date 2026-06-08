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
	Short: "Run dataflow approximation tests on a compiled project model",
	Long: `Run annotated samples with the supplied dataflow approximations applied.

A built-in source-to-sink harness rule is applied automatically; positive samples reference it as
` + "`@PositiveRuleSample(value = \"approximation-rule.yaml\", id = \"approximation-rule\")`" + `.

Exit codes:
  0    All approximation tests passed
  1    General failure (configuration or infrastructure error)
  252  Unhandled analyzer exception
  253  Out of memory (try increasing --max-memory)
  254  Analysis timed out (try increasing --timeout)
  255  Project configuration error`,
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

	testApproximationRunCmd.Flags().StringVarP(&testApproxOutputDir, "output", "o", "", "Directory for test-result.json and test-results.sarif")
	testApproximationRunCmd.Flags().DurationVar(&testApproxTimeout, "timeout", 600*time.Second, "Analysis timeout")
	testApproximationRunCmd.Flags().StringVar(&testApproxMaxMemory, "max-memory", "8G", "Maximum analyzer heap size (e.g., 8G)")
	testApproximationRunCmd.Flags().StringArrayVar(&testApproxDataflow, "dataflow-approximations", nil, "Dataflow approximation class directory or Java source directory (repeatable)")
}
