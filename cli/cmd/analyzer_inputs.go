package cmd

import (
	"github.com/seqra/opentaint/internal/utils/log"
)

// addDataflowApproximations resolves each --dataflow-approximations entry,
// auto-compiling a Java source directory into class files when needed, and
// registers the result on the builder. Shared by `scan` and the `test * run`
// commands so the two stay in lockstep.
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

// addPassthroughApproximations resolves each --passthrough-approximations entry
// to an absolute path and registers it on the builder.
func addPassthroughApproximations(b *AnalyzerBuilder, paths []string) {
	for _, passthrough := range paths {
		b.AddPassthroughApproximations(log.AbsPathOrExit(passthrough, "passthrough-approximations"))
	}
}
