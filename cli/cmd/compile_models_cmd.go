package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

var compileModelsOutput string

var compileModelsCmd = &cobra.Command{
	Use:   "models <model-project>",
	Short: "Compile a dataflow model project",
	Long:  "Compile a dataflow model project. `opentaint scan` and the test runs compile it on demand, so use this command to see the compiler errors or to compile ahead of time.\n\nArguments:\n  <model-project>  Model project from `opentaint model init`",
	Args:  cobra.ExactArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		projectPath := log.AbsPathOrExit(args[0], "model-project")

		if !models.IsProject(projectPath) {
			failWith(1, fmt.Sprintf("`%s` is not a model project", args[0]), nil, output.Suggestion{
				Description: "To create a model project, run:",
				Command:     fmt.Sprintf("opentaint model init %s --dependency <group:artifact:version>", shellQuote(args[0])),
			})
		}

		outputPath := compileModelsOutput
		if outputPath == "" {
			outputPath = models.BuildDir(projectPath)
		} else {
			outputPath = log.AbsPathOrExit(outputPath, "output")
		}

		analyzerJarPath, err := ensureAnalyzerAvailable()
		if err != nil {
			out.Fatal("Failed to get the analyzer", err)
		}

		builder := newModelBuilder(analyzerJarPath, "Compiling model project")
		err = models.Build(projectPath, outputPath, builder)
		builder.step.Finish(err)
		if err != nil {
			out.Error("Failed to compile the model project", err)
			out.Suggestions(modelBuildLogSuggestions(err)...)
			os.Exit(1)
		}

		out.Blank()
		out.Section("Model Compile Summary").
			Field("Model project", projectPath).
			Field("Compiled models written to", outputPath).
			Render()
		suggest("To scan with these models, run:",
			fmt.Sprintf("opentaint scan <source-path> --dataflow-models %s", shellQuote(args[0])))
	},
}

func init() {
	compileCmd.AddCommand(compileModelsCmd)

	compileModelsCmd.Flags().StringVarP(&compileModelsOutput, "output", "o", "",
		"Path to the compiled models (default: <model-project>/.opentaint/build)")
	compileCmd.AddCommand(deprecatedCommand(compileModelsCmd, "opentaint compile approximations", "opentaint compile models"))
}
