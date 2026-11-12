package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var initModelDeps []string

var modelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create dataflow model projects",
}

var modelInitCmd = &cobra.Command{
	Use:   "init <model-project>",
	Short: "Create a dataflow model project",
	Long:  "Create a dataflow model project. Use it when the analyzer loses taint in a library method that it cannot see into.\n\nArguments:\n  <model-project>  Directory of the new model project",
	Example: `  # Create a model project for the Jackson version that the app uses
  opentaint model init .opentaint/dataflow \
    --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "model-project")

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatal("Failed to get the analyzer", err)
		}

		existing := models.IsProject(projectPath)
		warnReplacingBuildFile(existing, args[0])

		if err := models.Scaffold(projectPath, initModelDeps, analyzerJarPath); err != nil {
			out.Fatal("Failed to create the model project", err)
		}

		printInitResult(existing, "the model project", args[0])
		out.Suggestions(
			output.Suggestion{Description: "To learn more about the dataflow models, see:", Command: usageDocsURL + "#opentaint-model"},
			output.Suggestion{Description: "To test the models after you write them, run:", Command: fmt.Sprintf("opentaint test model run <test-project-model> --dataflow-models %s", shellQuote(args[0]))},
		)
	},
}

func init() {
	rootCmd.AddCommand(modelCmd)
	modelCmd.AddCommand(modelInitCmd)

	modelInitCmd.Flags().StringArrayVar(&initModelDeps, "dependency", nil,
		"Library that the models refer to, as group:artifact:version (repeatable)")

	approximationCmd := deprecatedGroup(modelCmd, "opentaint approximation", "opentaint model")
	approximationCmd.AddCommand(deprecatedCommand(modelInitCmd, "opentaint approximation init", "opentaint model init"))
	rootCmd.AddCommand(approximationCmd)
}
