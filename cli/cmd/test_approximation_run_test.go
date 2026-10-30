package cmd

import (
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"testing"

	projectutil "github.com/seqra/opentaint/internal/utils/project"
)

func TestProjectModelLanguage(t *testing.T) {
	goProjects := []projectutil.GoProject{{ProjectDir: "go_0"}}
	javaProjects := []projectutil.JavaProject{{SourceRoot: "src"}}
	for name, tc := range map[string]struct {
		config projectutil.Config
		want   string
	}{
		"go":    {projectutil.Config{GoProjects: goProjects}, "go"},
		"java":  {projectutil.Config{JavaProjects: javaProjects}, "java"},
		"mixed": {projectutil.Config{GoProjects: goProjects, JavaProjects: javaProjects}, "java"},
		"empty": {projectutil.Config{}, "java"},
	} {
		t.Run(name, func(t *testing.T) {
			if got := projectModelLanguage(&tc.config); got != tc.want {
				t.Errorf("projectModelLanguage = %q, want %q", got, tc.want)
			}
		})
	}
}

// A Go test project runs from its source directory: it is tidied and gets a project model of its own.
func TestPrepareTestProjectFromGoSources(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no Go toolchain")
	}
	dir := t.TempDir()
	writeTestFile(t, filepath.Join(dir, "go.mod"), "module test\n")
	writeTestFile(t, filepath.Join(dir, "sample.go"), "package test\n")

	modelPath, config := prepareTestProject(dir)

	if modelPath == dir {
		t.Fatal("the project model was written into the test project")
	}
	if _, err := os.Stat(filepath.Join(modelPath, "project.yaml")); err != nil {
		t.Fatalf("no project model written: %v", err)
	}
	if want := []projectutil.GoProject{{ProjectDir: dir}}; !reflect.DeepEqual(config.GoProjects, want) {
		t.Errorf("Go projects = %v, want %v", config.GoProjects, want)
	}
	if projectModelLanguage(config) != "go" {
		t.Errorf("a Go test project is not tested as Go")
	}
	assertTidied(t, dir)
}

// A compiled project model keeps working, and its Go projects are tidied too.
func TestPrepareTestProjectTidiesCompiledGoProjects(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no Go toolchain")
	}
	modelPath := t.TempDir()
	writeTestFile(t, filepath.Join(modelPath, "project.yaml"), "goProjects:\n  - projectDir: go_0\n")
	writeTestFile(t, filepath.Join(modelPath, "go_0", "go.mod"), "module test\n")
	writeTestFile(t, filepath.Join(modelPath, "go_0", "sample.go"), "package test\n")

	gotPath, _ := prepareTestProject(modelPath)

	if gotPath != modelPath {
		t.Errorf("project model = %s, want %s", gotPath, modelPath)
	}
	assertTidied(t, filepath.Join(modelPath, "go_0"))
}

// assertTidied checks that 'go mod tidy' ran in dir: tidy adds the go directive the test go.mod lacks.
func assertTidied(t *testing.T, dir string) {
	t.Helper()
	content, err := os.ReadFile(filepath.Join(dir, "go.mod"))
	if err != nil {
		t.Fatal(err)
	}
	if !regexpGoDirective.Match(content) {
		t.Errorf("go.mod in %s was not tidied:\n%s", dir, content)
	}
}

var regexpGoDirective = regexp.MustCompile(`(?m)^go \d`)
