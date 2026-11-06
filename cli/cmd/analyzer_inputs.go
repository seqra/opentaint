package cmd

import (
	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

func addDataflowModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "dataflow-models", nil,
		"Dataflow models: a model project, build output, or class directory (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "dataflow-models", "dataflow-approximations")
}

func addPassthroughModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "passthrough-models", nil,
		"Pass-through models: a YAML file or a directory of them (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "passthrough-models", "passthrough-approximations")
}

// addDataflowModels resolves the paths to compiled model directories.
// It rebuilds a model project when its inputs change.
func addDataflowModels(b *AnalyzerBuilder, paths []string, analyzerJarPath string) {
	if len(paths) == 0 {
		return
	}

	absPaths := make([]string, 0, len(paths))
	for _, modelPath := range paths {
		absPaths = append(absPaths, log.AbsPathOrExit(modelPath, "dataflow-models"))
	}

	classDirs, err := models.ResolveAll(absPaths, newModelBuilder(analyzerJarPath))
	if err != nil {
		out.Fatal("Failed to load the dataflow models", err)
	}
	for _, classDir := range classDirs {
		b.AddDataflowApproximations(classDir)
	}
}

func addPassthroughModels(b *AnalyzerBuilder, paths []string) {
	for _, passthrough := range paths {
		b.AddPassthroughApproximations(log.AbsPathOrExit(passthrough, "passthrough-models"))
	}
}
