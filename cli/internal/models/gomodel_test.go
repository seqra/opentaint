package models

import (
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestResolveGoModelModule(t *testing.T) {
	for _, module := range []string{"opentaint", "opentaint/net"} {
		dir := t.TempDir()
		writeFile(t, filepath.Join(dir, "go.mod"), "module "+module+"\n\ngo 1.25.0\n")
		models, err := Resolve(dir, newFakeBuilder(t))
		if err != nil {
			t.Fatalf("module %s: %v", module, err)
		}
		if !reflect.DeepEqual(models.GoModelDirs, []string{dir}) || len(models.JavaClassDirs) != 0 {
			t.Errorf("module %s: Resolve() = %+v, want the module only", module, models)
		}
	}
}

// A Go module that is not a model module is a mistake when passed directly.
func TestResolveRejectsExplicitForeignGoModule(t *testing.T) {
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module opentaintx\n")
	_, err := Resolve(dir, newFakeBuilder(t))
	if err == nil || !strings.Contains(err.Error(), "`opentaintx`, and a Go model project declares `opentaint`") {
		t.Fatalf("error = %v, want the module path requirement", err)
	}
}

// Found below a model path, a Go module that is not a model project is a mistake too, as
// compiled classes there are.
func TestResolveRejectsNestedForeignGoModule(t *testing.T) {
	root := t.TempDir()
	foreign := filepath.Join(root, "app")
	writeFile(t, filepath.Join(foreign, "go.mod"), "module example.com/app\n")
	writeFile(t, filepath.Join(root, "models", "go.mod"), "module opentaint\n")

	_, err := Resolve(root, newFakeBuilder(t))
	if err == nil || !strings.Contains(err.Error(), "`"+foreign+"` is not a model project") {
		t.Fatalf("error = %v, want it to name %s", err, foreign)
	}
	if err := Check(root); err == nil {
		t.Error("Check() accepted a Go module that is not a model project")
	}
}

// One tree can hold models of both languages. Every Go model module is a module of its own,
// so several of them can be passed together.
func TestResolveMixedTree(t *testing.T) {
	root := t.TempDir()
	project := newProject(t, filepath.Join(root, "java-project"))
	output := filepath.Join(root, "java-output")
	writeBuildOutput(t, output, "bytecode")
	first := filepath.Join(root, "go", "first")
	second := filepath.Join(root, "go", "second")
	writeFile(t, filepath.Join(first, "go.mod"), "module opentaint\n")
	writeFile(t, filepath.Join(second, "go.mod"), "module opentaint\n")
	// A model module is not searched further.
	writeFile(t, filepath.Join(first, "nested", "go.mod"), "module opentaint\n")

	builder := newFakeBuilder(t)
	models, err := ResolveAll([]string{root, first}, builder)
	if err != nil {
		t.Fatalf("ResolveAll: %v", err)
	}
	if want := []string{ClassesDir(output), ClassesDir(BuildDir(project))}; !reflect.DeepEqual(models.JavaClassDirs, want) {
		t.Errorf("Java class directories = %v, want %v", models.JavaClassDirs, want)
	}
	if want := []string{first, second}; !reflect.DeepEqual(models.GoModelDirs, want) {
		t.Errorf("Go model directories = %v, want %v", models.GoModelDirs, want)
	}
}
