package project

import (
	"os"
	"path/filepath"
	"testing"
)

func writeProjectYaml(t *testing.T, content string) string {
	t.Helper()
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "project.yaml"), []byte(content), 0o644); err != nil {
		t.Fatalf("write project.yaml: %v", err)
	}
	return dir
}

func TestLoadConfigNewFormat(t *testing.T) {
	dir := writeProjectYaml(t, `projectRoot: /proj
javaProjects:
  - sourceRoot: java_0/sources
    modules:
      - moduleSourceRoot: java_0/sources
        packages: [com.example]
        moduleClasses: [java_0/classes/main]
    dependencies:
      - path: libs/a.jar
goProjects:
  - projectDir: go_0
`)

	config, err := LoadConfig(dir)
	if err != nil {
		t.Fatalf("LoadConfig: %v", err)
	}
	if len(config.JavaProjects) != 1 || len(config.GoProjects) != 1 {
		t.Fatalf("expected 1 java + 1 go project, got %d/%d", len(config.JavaProjects), len(config.GoProjects))
	}
	if got := config.PrimarySourceRoot(); got != "/proj" {
		t.Errorf("PrimarySourceRoot = %q, want /proj", got)
	}
	if got := config.AllModules(); len(got) != 1 || got[0].Packages[0] != "com.example" {
		t.Errorf("AllModules = %+v", got)
	}
	if got := config.AllDependencies(); len(got) != 1 || got[0] != "libs/a.jar" {
		t.Errorf("AllDependencies = %+v", got)
	}
	if config.GoProjects[0].ProjectDir != "go_0" {
		t.Errorf("go projectDir = %q", config.GoProjects[0].ProjectDir)
	}
}

func TestLoadConfigLegacyFallback(t *testing.T) {
	dir := writeProjectYaml(t, `sourceRoot: src
javaToolchain: /jdk
modules:
  - moduleSourceRoot: src
    packages: [com.legacy]
    moduleClasses: [dist/app.jar]
dependencies:
  - path: lib/commons-io.jar
`)

	config, err := LoadConfig(dir)
	if err != nil {
		t.Fatalf("LoadConfig: %v", err)
	}
	if len(config.JavaProjects) != 1 {
		t.Fatalf("legacy should wrap into 1 java project, got %d", len(config.JavaProjects))
	}
	jp := config.JavaProjects[0]
	if jp.SourceRoot != "src" || jp.JavaToolchain != "/jdk" {
		t.Errorf("wrapped java project = %+v", jp)
	}
	if got := config.AllModules(); len(got) != 1 || got[0].Packages[0] != "com.legacy" {
		t.Errorf("AllModules = %+v", got)
	}
	if got := config.AllDependencies(); len(got) != 1 || got[0] != "lib/commons-io.jar" {
		t.Errorf("AllDependencies = %+v", got)
	}
	if got := config.PrimarySourceRoot(); got != "src" {
		t.Errorf("PrimarySourceRoot = %q, want src", got)
	}
}

func TestAllDependenciesReturnsPaths(t *testing.T) {
	c := &Config{JavaProjects: []JavaProject{{
		Dependencies: []ResolvedDependency{
			{Path: "/d/os-2.18.0.jar", Group: "org.opensearch.client", Artifact: "opensearch-rest-client", Version: "2.18.0"},
			{Path: "/d/os-3.5.0.jar", Version: "3.5.0"},
		},
	}}}
	got := c.AllDependencies()
	if len(got) != 2 || got[0] != "/d/os-2.18.0.jar" || got[1] != "/d/os-3.5.0.jar" {
		t.Fatalf("unexpected: %v", got)
	}
}

func TestGetSourceRootRelativeResolved(t *testing.T) {
	dir := writeProjectYaml(t, `javaProjects:
  - sourceRoot: java_0/sources
    modules: []
`)
	got, err := GetSourceRoot(dir)
	if err != nil {
		t.Fatalf("GetSourceRoot: %v", err)
	}
	if want := filepath.Join(dir, "java_0/sources"); got != want {
		t.Errorf("GetSourceRoot = %q, want %q", got, want)
	}
}
