package cmd

import (
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils/java"
)

func newAnalyzerJavaRunner() java.JavaRunner {
	return java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Analyzer")).
		WithImageType(java.AdoptiumImageJRE).
		TrySpecificVersion(globals.DefaultJavaVersion)
}

func newAutobuilderJavaRunner() java.JavaRunner {
	return java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Autobuilder")).
		TrySystem().
		TrySpecificVersion(globals.Config.Java.Version)
}
