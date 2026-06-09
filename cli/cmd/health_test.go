package cmd

import (
	"testing"

	"github.com/seqra/opentaint/internal/globals"
)

func TestResolveHealthComponentUsesAnalyzerJarOverride(t *testing.T) {
	orig := globals.Config.Analyzer.JarPath
	t.Cleanup(func() { globals.Config.Analyzer.JarPath = orig })
	globals.Config.Analyzer.JarPath = "/tmp/custom-analyzer.jar"

	c := resolveHealthComponent("analyzer")
	if c.path != globals.Config.Analyzer.JarPath {
		t.Fatalf("health analyzer path = %q, want override %q", c.path, globals.Config.Analyzer.JarPath)
	}
	// A jar-path override is a custom build, so health must report it as such
	// (matching scan), not as the nominal configured version.
	if want := "custom (" + globals.Config.Analyzer.JarPath + ")"; c.version != want {
		t.Fatalf("health analyzer version = %q, want %q", c.version, want)
	}
}

func TestResolveHealthComponentUsesAutobuilderJarOverride(t *testing.T) {
	orig := globals.Config.Autobuilder.JarPath
	t.Cleanup(func() { globals.Config.Autobuilder.JarPath = orig })
	globals.Config.Autobuilder.JarPath = "/tmp/custom-autobuilder.jar"

	c := resolveHealthComponent("autobuilder")
	if c.path != globals.Config.Autobuilder.JarPath {
		t.Fatalf("health autobuilder path = %q, want override %q", c.path, globals.Config.Autobuilder.JarPath)
	}
}
