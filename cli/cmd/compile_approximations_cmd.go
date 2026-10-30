package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/approximation"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var compileModelsOutput string

var compileModelsCmd = &cobra.Command{
	Use:   "models <model-project>",
	Short: "Compile a Java dataflow model project",
	Long: `Compile the dataflow models in <model-project> against the
dependencies that project pins in its own build file.

This is the model project, not the project to scan: its build.gradle.kts lists the exact
library versions the models are written against, so the same models compile identically
wherever they are applied.

Scanning and testing build a model project on demand, so running this is only
needed to compile ahead of time or to see compilation errors on their own.`,
	Args: cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "model-project")

		if !approximation.IsProject(projectPath) {
			out.Fatalf("%s is not a model project: it has no build.gradle.kts declaring the "+
				"dependencies its models are written against.\nCreate one with 'opentaint model init %s "+
				"--language java --dependency <group:artifact:version>'", projectPath, args[0])
		}

		outputPath := compileModelsOutput
		if outputPath == "" {
			outputPath = approximation.BuildDir(projectPath)
		} else {
			outputPath = log.AbsPathOrExit(outputPath, "output")
		}

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatalf("Failed to resolve analyzer: %s", err)
		}

		if err := approximation.Build(projectPath, outputPath, newApproximationBuilder(analyzerJarPath)); err != nil {
			out.Fatalf("Model compilation failed: %s", err)
		}

		out.Section("Model Compile Summary").
			Field("Model project", projectPath).
			Field("Compiled models written to", approximation.ClassesDir(outputPath)).
			Render()
		suggest("To apply these models in a scan run",
			fmt.Sprintf("opentaint scan <project-model> --dataflow-models %s", args[0]))
	},
}

func init() {
	compileCmd.AddCommand(compileModelsCmd)

	compileModelsCmd.Flags().StringVarP(&compileModelsOutput, "output", "o", "",
		"Path to the compiled models (default: <model-project>/.opentaint/build)")
	compileCmd.AddCommand(deprecatedCommand(compileModelsCmd, "approximations", "opentaint compile models"))
}
