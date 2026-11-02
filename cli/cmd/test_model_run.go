package cmd

import (
	"os"
	"time"

	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/spf13/cobra"
)

var (
	testModelOutputDir string
	testModelTimeout   time.Duration
	testModelMaxMemory string
	testModelDataflow  []string
)

var testModelRunCmd = &cobra.Command{
	Use:   "run <project-model>",
	Short: "Run dataflow model tests on a compiled project model",
	Long: `Run the samples specified in rule-test.yaml with the supplied dataflow models applied.

A built-in source-to-sink harness rule is applied automatically; positive samples reference the
model-rule.yaml rule with id "model-rule".

` + testExitCodesHelp("All model tests passed"),
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
			label:          "Model tests",
			tempDir:        "opentaint-test-models-*",
			rulesets:       []string{ruleDir},
			outputDir:      testModelOutputDir,
			timeout:        testModelTimeout,
			maxMemory:      testModelMaxMemory,
			dataflowModels: testModelDataflow,
		})
	},
}

func init() {
	testModelCmd.AddCommand(testModelRunCmd)
	addTestRunFlags(testModelRunCmd, &testModelOutputDir, &testModelTimeout, &testModelMaxMemory, &testModelDataflow)
	testApproximationCmd.AddCommand(deprecatedCommand(testModelRunCmd, "run", "opentaint test model run"))
}
