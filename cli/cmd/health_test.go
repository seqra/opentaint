package cmd

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils"
)

func TestResolveHealthComponentUsesAnalyzerJarOverride(t *testing.T) {
	orig := globals.Config.Analyzer.JarPath
	t.Cleanup(func() { globals.Config.Analyzer.JarPath = orig })
	globals.Config.Analyzer.JarPath = "/tmp/custom-analyzer.jar"

	c := resolveHealthComponent("analyzer")
	if c.path != globals.Config.Analyzer.JarPath {
		t.Fatalf("health analyzer path = %q, want override %q", c.path, globals.Config.Analyzer.JarPath)
	}
	// A jar-path override is a custom build, so health reports the version as
	// "custom" — bare, since the path is already shown on its own node (no
	// duplication), unlike scan's single-line "custom (<path>)".
	if c.version != "custom" {
		t.Fatalf("health analyzer version = %q, want %q", c.version, "custom")
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

func TestResolveRuntimeComponentIgnoresSystemJava(t *testing.T) {
	// An empty HOME means no managed JRE can exist; the analyzer would download
	// its own JRE, so health must NOT report a system Java as the runtime.
	t.Setenv("HOME", t.TempDir())

	c := resolveHealthComponent("runtime")
	if c.present {
		t.Fatalf("runtime present = true with no managed JRE; health must not report a runtime the analyzer won't use (path %q)", c.path)
	}
}

func TestResolveRuntimeComponentFindsManagedJRE(t *testing.T) {
	home := t.TempDir()
	t.Setenv("HOME", home)
	jreBin := filepath.Join(home, ".opentaint", "install", "jre", "bin")
	if err := os.MkdirAll(jreBin, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(jreBin, "java"), []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	// Without the .versions marker the install tier is stale-filtered, matching
	// the analyzer's own policy — write it so the JRE counts as current.
	if err := utils.WriteInstallVersionMarker(); err != nil {
		t.Fatal(err)
	}

	c := resolveHealthComponent("runtime")
	if !c.present {
		t.Fatalf("runtime present = false, want true with managed JRE at %s", jreBin)
	}
	if want := filepath.Join(jreBin, "java"); c.path != want {
		t.Errorf("runtime path = %q, want %q", c.path, want)
	}
}
