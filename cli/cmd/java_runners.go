package cmd

import (
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils/java"
)

// newAnalyzerJavaRunner returns the runner policy for the analyzer JVM: the
// managed Adoptium JRE pinned to the default Java version, never system Java.
func newAnalyzerJavaRunner() java.JavaRunner {
	return java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Analyzer")).
		WithImageType(java.AdoptiumImageJRE).
		TrySpecificVersion(globals.DefaultJavaVersion)
}

// newAutobuilderJavaRunner returns the runner policy for project compilation:
// system Java first, then the user-configured version.
func newAutobuilderJavaRunner() java.JavaRunner {
	return java.NewJavaRunner().
		WithSkipVerify(globals.Config.SkipVerify).
		WithDebugOutput(out.DebugStream("Autobuilder")).
		TrySystem().
		TrySpecificVersion(globals.Config.Java.Version)
}
