package cmd

import (
	"github.com/seqra/opentaint/internal/utils/log"
)

func addDataflowApproximations(b *AnalyzerBuilder, paths []string, analyzerJarPath, projectModelDir string) {
	for _, approxPath := range paths {
		absApproxPath := log.AbsPathOrExit(approxPath, "dataflow-approximations")
		compiledPath, err := compileApproximationsIfNeeded(absApproxPath, analyzerJarPath, projectModelDir)
		if err != nil {
			out.Fatalf("Approximation compilation failed: %s", err)
		}
		b.AddDataflowApproximations(compiledPath)
	}
}

func addPassthroughApproximations(b *AnalyzerBuilder, paths []string) {
	for _, passthrough := range paths {
		b.AddPassthroughApproximations(log.AbsPathOrExit(passthrough, "passthrough-approximations"))
	}
}
