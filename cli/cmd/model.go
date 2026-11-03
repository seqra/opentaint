package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var initModelDeps []string

var modelCmd = &cobra.Command{
	Use:   "model",
	Short: "Create dataflow model projects",
	Long: `A dataflow model describes how taint moves through library methods that the analyzer cannot see into. A model project holds such models and pins the library versions they are written against

Compile a model project with "opentaint compile models" and apply it with --dataflow-models`,
}

var modelInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow model project",
	Long: `Create a Gradle project for dataflow models

Arguments:
  <output-dir>  Directory of the new model project

Give each library that the models are written against with --dependency, at the version that the scanned application uses. To change the dependencies of an existing project, run the command again with the full list`,
	Example: `  # Create a project for models of jackson-databind
  opentaint model init ./jackson-models --dependency com.fasterxml.jackson.core:jackson-databind:2.17.2`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "output-dir")

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatalf("Failed to resolve analyzer: %s", err)
		}

		// Init replaces the build file but keeps the model sources.
		// Warn the user because this removes dependency pins that they added manually.
		existing := models.IsProject(projectPath)
		if existing {
			out.Warnf("Replacing the build file of the existing model project at %s; "+
				"pass every dependency the models need, not only the new ones", projectPath)
		}

		if err := models.Scaffold(projectPath, initModelDeps, analyzerJarPath); err != nil {
			out.Fatalf("Failed to create model project: %s", err)
		}

		if existing {
			fmt.Printf("Model project updated at %s\n", projectPath)
		} else {
			fmt.Printf("Model project initialized at %s\n", projectPath)
		}
		suggest("After you write the models, test them with:",
			fmt.Sprintf("opentaint test model run <project-model> --dataflow-models %s", shellQuote(args[0])))
	},
}

func init() {
	rootCmd.AddCommand(modelCmd)
	modelCmd.AddCommand(modelInitCmd)

	modelInitCmd.Flags().StringArrayVar(&initModelDeps, "dependency", nil,
		"Compile-only Maven dependency coordinates the models are written against (repeatable)")

	approximationCmd := &cobra.Command{
		Use:        "approximation",
		Short:      modelCmd.Short,
		Deprecated: "use 'opentaint model' instead",
	}
	approximationCmd.AddCommand(deprecatedCommand(modelInitCmd, "init", "opentaint model init"))
	rootCmd.AddCommand(approximationCmd)
}
