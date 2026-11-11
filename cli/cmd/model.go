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
	Use:   "init <output-dir>",
	Short: "Create a dataflow model project",
	Long:  "Create a dataflow model project. Use it when the analyzer loses taint in a library method that it cannot see into.\n\nArguments:\n  <output-dir>  Directory of the new model project",
	Example: `  # Create a model project for the Jackson version that the app uses
  opentaint model init .opentaint/dataflow \
    --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "output-dir")

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatal("Failed to get the analyzer", err)
		}

		// Init replaces the build file but keeps the model sources.
		// Warn the user because this removes dependency pins that they added manually.
		existing := models.IsProject(projectPath)
		if existing {
			out.Warnf("Replacing the build file of the model project at `%s`. "+
				"Use --dependency for every library that the models need, not only the new ones.", args[0])
		}

		if err := models.Scaffold(projectPath, initModelDeps, analyzerJarPath); err != nil {
			out.Fatal("Failed to create the model project", err)
		}

		if existing {
			out.Printf("Model project updated at `%s`", args[0])
		} else {
			out.Printf("Model project initialized at `%s`", args[0])
		}
		out.Suggestions(
			output.Suggestion{Description: "To add the models, write them in:", Command: shellQuote(joinUserPath(args[0], "src", "main", "java"))},
			output.Suggestion{Description: "To test the models, run:", Command: fmt.Sprintf("opentaint test model run <test-project-model> --dataflow-models %s", shellQuote(args[0]))},
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
