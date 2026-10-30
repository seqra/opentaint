package cmd

import (
	"github.com/seqra/opentaint/internal/approximation"
	"github.com/seqra/opentaint/internal/utils/log"
	"github.com/spf13/cobra"
)

func addDataflowModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "dataflow-models", nil,
		"Java or Go model project, Java model build output, or a directory that holds them (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "dataflow-models", "dataflow-approximations")
}

func addPassthroughModelsFlag(cmd *cobra.Command, paths *[]string) {
	cmd.Flags().StringArrayVar(paths, "passthrough-models", nil,
		"Pass-through model YAML file or directory (repeatable)")
	addDeprecatedFlagAlias(cmd.Flags(), "passthrough-models", "passthrough-approximations")
}

// addDataflowModels finds the models in the model paths and passes them to the analyzer:
// Java models as class directories and Go models as model modules. It rebuilds a Java model
// project when its inputs change.
func addDataflowModels(b *AnalyzerBuilder, paths []string, analyzerJarPath string) {
	if len(paths) == 0 {
		return
	}

	absPaths := make([]string, 0, len(paths))
	for _, modelPath := range paths {
		absPaths = append(absPaths, log.AbsPathOrExit(modelPath, "dataflow-models"))
	}

	models, err := approximation.ResolveAll(absPaths, newApproximationBuilder(analyzerJarPath))
	if err != nil {
		out.Fatalf("Failed to apply dataflow models: %s", err)
	}
	for _, warning := range models.Warnings {
		out.Warn(warning)
	}
	for _, classDir := range models.JavaClassDirs {
		b.AddDataflowApproximations(classDir)
	}
	for _, goModelDir := range models.GoModelDirs {
		b.AddGoModel(goModelDir)
	}
}

func addPassthroughModels(b *AnalyzerBuilder, paths []string) {
	for _, passthrough := range paths {
		b.AddPassthroughApproximations(log.AbsPathOrExit(passthrough, "passthrough-models"))
	}
}
