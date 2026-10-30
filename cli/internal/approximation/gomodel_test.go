package approximation

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
		if !reflect.DeepEqual(models.GoModelDirs, []string{dir}) || len(models.Warnings) != 0 {
			t.Errorf("module %s: Resolve() = %+v, want the module and no warnings", module, models)
		}
	}
}

// A Go module that is not a model module is a mistake when passed directly.
func TestResolveRejectsExplicitForeignGoModule(t *testing.T) {
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module opentaintx\n")
	_, err := Resolve(dir, newFakeBuilder(t))
	if err == nil || !strings.Contains(err.Error(), `must be "opentaint"`) {
		t.Fatalf("error = %v, want the module path requirement", err)
	}
}

// Found below a model path, the same module is skipped with a warning, and so is everything below it.
func TestResolveSkipsNestedForeignGoModule(t *testing.T) {
	root := t.TempDir()
	foreign := filepath.Join(root, "app")
	writeFile(t, filepath.Join(foreign, "go.mod"), "module example.com/app\n")
	writeFile(t, filepath.Join(foreign, "models", "go.mod"), "module opentaint\n")
	model := filepath.Join(root, "models")
	writeFile(t, filepath.Join(model, "go.mod"), "module opentaint\n")

	models, err := Resolve(root, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if !reflect.DeepEqual(models.GoModelDirs, []string{model}) {
		t.Errorf("Go model directories = %v, want [%s]", models.GoModelDirs, model)
	}
	if len(models.Warnings) != 1 || !strings.Contains(models.Warnings[0], foreign) {
		t.Errorf("warnings = %v, want one naming %s", models.Warnings, foreign)
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
	if len(models.Warnings) != 0 {
		t.Errorf("unexpected warnings: %v", models.Warnings)
	}
}
