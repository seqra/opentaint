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
	Long: `A dataflow model project holds code-based models of how taint moves through
methods the analyzer cannot see into, together with the exact dependency versions those
models are written against.

Compile one with 'opentaint compile models', and apply it with the
--dataflow-models flag of 'opentaint scan' or 'opentaint test model run'.`,
}

var modelInitCmd = &cobra.Command{
	Use:   "init <output-dir>",
	Short: "Create a dataflow model project",
	Long: `Create a Gradle project for OpenTaint dataflow models.

The project includes:
  - build.gradle.kts with compile-only dependencies, settings.gradle.kts
  - libs/opentaint-approximations-api.jar, the @Approximate annotations and the
    OpentaintNdUtil / ArgumentTypeContext support types
  - src/main/java/ for the model sources, one @Approximate class per target class

Use --dependency to pin the libraries the models are written against, at the exact versions
the target application uses. Those pins are the models' compile environment: they, and
nothing about the project under analysis, decide what the models compile against.`,
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
		suggest("To compile the models run", fmt.Sprintf("opentaint compile models %s", args[0]))
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
