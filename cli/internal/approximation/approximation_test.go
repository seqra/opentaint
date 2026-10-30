package approximation

import (
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"

	"gopkg.in/yaml.v2"
)

// fakeBuilder records builds and writes a test project model.
type fakeBuilder struct {
	t           *testing.T
	compiled    []string
	fingerprint string
}

func newFakeBuilder(t *testing.T) *fakeBuilder {
	return &fakeBuilder{t: t, fingerprint: "autobuilder 1.0.0"}
}

func (b *fakeBuilder) Fingerprint() (string, error) {
	return b.fingerprint, nil
}

// Prepare writes the same API content for each call.
func (b *fakeBuilder) Prepare(projectDir string) error {
	writeFile(b.t, apiJarPath(projectDir), "api-jar-bytes")
	return nil
}

func (b *fakeBuilder) Compile(projectDir, projectModelDir string) error {
	b.compiled = append(b.compiled, projectDir)
	writeModuleClasses(b.t, projectModelDir, map[string][]string{"c0_main": {"Model"}})
	return nil
}

// writeModuleClasses writes classes and a project descriptor for tests.
func writeModuleClasses(t *testing.T, projectModelDir string, modules map[string][]string) {
	t.Helper()
	moduleDirs := make([]string, 0, len(modules))
	for module, classes := range modules {
		for _, class := range classes {
			writeFile(t, filepath.Join(projectModelDir, "classes", module, "com", "example", class+".class"), "bytecode")
		}
		moduleDirs = append(moduleDirs, module)
	}
	sort.Strings(moduleDirs)

	config := "javaProjects:\n  - sourceRoot: /project\n    modules:\n      - moduleSourceRoot: /project\n        moduleClasses:\n"
	for _, module := range moduleDirs {
		config += "          - classes/" + module + "\n"
	}
	writeFile(t, filepath.Join(projectModelDir, "project.yaml"), config)
}

// resolveJava returns the Java class directories found in paths.
func resolveJava(paths []string, builder Builder) ([]string, error) {
	models, err := ResolveAll(paths, builder)
	if err != nil {
		return nil, err
	}
	return models.JavaClassDirs, nil
}

// writeBuildOutput writes a Java model build output holding one class.
func writeBuildOutput(t *testing.T, dir, bytecode string) {
	t.Helper()
	writeFile(t, filepath.Join(dir, descriptorName), "sourceProject: /elsewhere\n")
	writeFile(t, filepath.Join(dir, classesDirName, "com", "example", "Model.class"), bytecode)
}

func writeFile(t *testing.T, path, content string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

// newProject writes a model project for tests.
func newProject(t *testing.T, dir string) string {
	t.Helper()
	writeFile(t, filepath.Join(dir, "build.gradle.kts"), "dependencies {\n    compileOnly(\"com.foo:bar:1.0\")\n}\n")
	writeFile(t, filepath.Join(dir, "src", "main", "java", "com", "example", "Model.java"), "package com.example;\n")
	return dir
}

func TestResolveBuildsProject(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := newFakeBuilder(t)

	classDirs, err := resolveJava([]string{project}, builder)
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}

	want := ClassesDir(BuildDir(project))
	if len(classDirs) != 1 || classDirs[0] != want {
		t.Fatalf("Resolve() = %v, want [%s]", classDirs, want)
	}
	if len(builder.compiled) != 1 {
		t.Fatalf("expected one build, got %v", builder.compiled)
	}
	if _, err := os.Stat(filepath.Join(want, "com", "example", "Model.class")); err != nil {
		t.Errorf("compiled model not collected: %v", err)
	}
	if _, err := os.Stat(filepath.Join(BuildDir(project), descriptorName)); err != nil {
		t.Errorf("descriptor not written: %v", err)
	}
}

func TestResolveReusesBuildUntilSourcesChange(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := newFakeBuilder(t)

	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("first Resolve: %v", err)
	}
	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("second Resolve: %v", err)
	}
	if len(builder.compiled) != 1 {
		t.Fatalf("unchanged sources rebuilt: %v", builder.compiled)
	}

	writeFile(t, filepath.Join(project, "src", "main", "java", "com", "example", "Model.java"), "package com.example;\n// edited\n")
	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("third Resolve: %v", err)
	}
	if len(builder.compiled) != 2 {
		t.Fatalf("edited model not rebuilt: %v", builder.compiled)
	}
}

// The stamp covers the project, and the project alone does not determine the compiled
// classes: the compiler does too.
func TestResolveRebuildsWhenTheCompilerChanges(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := newFakeBuilder(t)

	for range 2 {
		if _, err := Resolve(project, builder); err != nil {
			t.Fatalf("Resolve: %v", err)
		}
	}
	if len(builder.compiled) != 1 {
		t.Fatalf("an unchanged project was rebuilt: %v", builder.compiled)
	}

	builder.fingerprint = "autobuilder 2.0.0"
	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("Resolve after the upgrade: %v", err)
	}
	if len(builder.compiled) != 2 {
		t.Errorf("an upgraded compiler did not rebuild the models: %v", builder.compiled)
	}
}

func TestResolveRebuildsWhenDependencyPinChanges(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := newFakeBuilder(t)

	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("first Resolve: %v", err)
	}
	writeFile(t, filepath.Join(project, "build.gradle.kts"), "dependencies {\n    compileOnly(\"com.foo:bar:2.0\")\n}\n")
	if _, err := Resolve(project, builder); err != nil {
		t.Fatalf("second Resolve: %v", err)
	}
	if len(builder.compiled) != 2 {
		t.Fatalf("changed dependency pin not rebuilt: %v", builder.compiled)
	}
}

func TestResolveBuiltOutput(t *testing.T) {
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, descriptorName), "sourceProject: \"/somewhere\"\n")
	writeFile(t, filepath.Join(dir, classesDirName, "com", "example", "Model.class"), "bytecode")

	builder := newFakeBuilder(t)
	classDirs, err := resolveJava([]string{dir}, builder)
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(classDirs) != 1 || classDirs[0] != ClassesDir(dir) {
		t.Fatalf("Resolve() = %v, want [%s]", classDirs, ClassesDir(dir))
	}
	if len(builder.compiled) != 0 {
		t.Errorf("built output should not be rebuilt, got %v", builder.compiled)
	}
}

func TestResolveTreeOfProjects(t *testing.T) {
	root := t.TempDir()
	newProject(t, filepath.Join(root, "batch-a"))
	newProject(t, filepath.Join(root, "batch-b"))

	builder := newFakeBuilder(t)
	classDirs, err := resolveJava([]string{root}, builder)
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(classDirs) != 2 {
		t.Fatalf("Resolve() = %v, want both batches", classDirs)
	}
	if len(builder.compiled) != 2 {
		t.Fatalf("expected both projects built, got %v", builder.compiled)
	}

	// The second call must ignore the nested build outputs.
	again, err := resolveJava([]string{root}, builder)
	if err != nil {
		t.Fatalf("second Resolve: %v", err)
	}
	if len(again) != 2 {
		t.Fatalf("second Resolve() = %v, want both batches", again)
	}
	if len(builder.compiled) != 2 {
		t.Fatalf("unchanged projects rebuilt: %v", builder.compiled)
	}
}

// A tree may mix model projects with build outputs; each contributes its own classes.
func TestResolveTreeMixingProjectAndBuildOutput(t *testing.T) {
	root := t.TempDir()
	project := newProject(t, filepath.Join(root, "models"))
	prebuilt := filepath.Join(root, "prebuilt")
	writeFile(t, filepath.Join(prebuilt, descriptorName), "sourceProject: /elsewhere\n")
	writeFile(t, filepath.Join(prebuilt, classesDirName, "com", "example", "Other.class"), "bytecode")

	builder := newFakeBuilder(t)
	classDirs, err := resolveJava([]string{root}, builder)
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	want := []string{ClassesDir(BuildDir(project)), ClassesDir(prebuilt)}
	if !reflect.DeepEqual(classDirs, want) {
		t.Fatalf("Resolve() = %v, want %v", classDirs, want)
	}
	if !reflect.DeepEqual(builder.compiled, []string{project}) {
		t.Fatalf("expected the project to be compiled, got %v", builder.compiled)
	}
}

// The analyzer is handed every path's answer at once, so a directory reached twice must
// contribute once.
func TestResolveAllPassesEachDirectoryOnce(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := newFakeBuilder(t)

	classDirs, err := resolveJava([]string{project, project}, builder)
	if err != nil {
		t.Fatalf("ResolveAll: %v", err)
	}
	if !reflect.DeepEqual(classDirs, []string{ClassesDir(BuildDir(project))}) {
		t.Fatalf("ResolveAll() = %v, want the class directory once", classDirs)
	}
}

// Copies of one class are the ordinary result of passing overlapping paths, and the
// analyzer reads the same class whichever copy it picks.
func TestResolveAllAcceptsIdenticalCopiesOfAClass(t *testing.T) {
	root := t.TempDir()
	first := filepath.Join(root, "first")
	second := filepath.Join(root, "second")
	writeBuildOutput(t, first, "bytecode")
	writeBuildOutput(t, second, "bytecode")

	classDirs, err := resolveJava([]string{first, second}, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("ResolveAll: %v", err)
	}
	if !reflect.DeepEqual(classDirs, []string{ClassesDir(first), ClassesDir(second)}) {
		t.Fatalf("ResolveAll() = %v, want both directories", classDirs)
	}
}

// Two directories offering one class with different content leave the analyzer to pick,
// and nothing says which it picks: the directories must agree on the class content.
func TestResolveAllRejectsClashingClasses(t *testing.T) {
	root := t.TempDir()
	first := filepath.Join(root, "first")
	second := filepath.Join(root, "second")
	writeBuildOutput(t, first, "one bytecode")
	writeBuildOutput(t, second, "another bytecode")

	_, err := ResolveAll([]string{first, second}, newFakeBuilder(t))
	if err == nil {
		t.Fatal("expected two different copies of one class to be rejected")
	}
	for _, want := range []string{"com/example/Model.class", first, second} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error should mention %s, got: %v", want, err)
		}
	}
}

func TestResolveLooseSourcesWarnsAboutMigration(t *testing.T) {
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "com", "example", "Model.java"), "package com.example;\n")

	models, err := Resolve(dir, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(models.Warnings) != 1 || !strings.Contains(models.Warnings[0], "--language java") {
		t.Errorf("warnings = %v, want one pointing at the migration command", models.Warnings)
	}
}

// A path without models is not an error: the scan runs without them and says so.
func TestResolveEmptyDirectoryWarns(t *testing.T) {
	dir := t.TempDir()
	models, err := Resolve(dir, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(models.JavaClassDirs)+len(models.GoModelDirs) != 0 {
		t.Errorf("an empty directory resolved to models: %+v", models)
	}
	if len(models.Warnings) != 1 || !strings.Contains(models.Warnings[0], dir) {
		t.Errorf("warnings = %v, want one naming %s", models.Warnings, dir)
	}
}

// Compiled classes outside a build output are not models any more.
func TestResolveIgnoresBareClassDirectory(t *testing.T) {
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "com", "example", "Model.class"), "bytecode")

	models, err := Resolve(dir, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(models.JavaClassDirs) != 0 || len(models.Warnings) != 1 {
		t.Errorf("Resolve() = %+v, want no class directories and one warning", models)
	}
}

func TestResolveMissingPath(t *testing.T) {
	if _, err := Resolve(filepath.Join(t.TempDir(), "missing"), newFakeBuilder(t)); err == nil {
		t.Fatal("expected a missing model path to be rejected")
	}
	file := filepath.Join(t.TempDir(), "models")
	writeFile(t, file, "")
	if _, err := Resolve(file, newFakeBuilder(t)); err == nil || !strings.Contains(err.Error(), "not a directory") {
		t.Fatalf("Resolve(file) error = %v, want not a directory", err)
	}
}

func TestFailedBuildLeavesTheProjectBuildable(t *testing.T) {
	project := newProject(t, t.TempDir())

	// A failed build must not block the next build.
	if err := Build(project, BuildDir(project), &collidingBuilder{fakeBuilder{t: t}}); err == nil {
		t.Fatal("expected the colliding build to fail")
	}
	if err := Build(project, BuildDir(project), newFakeBuilder(t)); err != nil {
		t.Fatalf("rebuild after a failed build: %v", err)
	}
}

func TestFailedRebuildKeepsThePreviousBuild(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := BuildDir(project)

	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("first build: %v", err)
	}
	if err := Build(project, output, &collidingBuilder{fakeBuilder{t: t}}); err == nil {
		t.Fatal("expected the colliding build to fail")
	}

	// The previous models must remain available.
	if _, err := os.Stat(filepath.Join(ClassesDir(output), "com", "example", "Model.class")); err != nil {
		t.Errorf("a failed rebuild destroyed the previous build: %v", err)
	}
	if !isBuiltOutput(output) {
		t.Error("a failed rebuild left the output unusable")
	}
}

// A build assembles under a path of its own. A second builder of the same output must not
// be able to delete or contribute to it.
func TestBuildKeepsStagingOfARunningBuild(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := BuildDir(project)

	// What another builder of the same output would be assembling. Process 1 always runs.
	foreign := filepath.Join(stagingRoot(output), filepath.Base(output)+"-1")
	writeFile(t, filepath.Join(foreign, classesDirName, "com", "example", "Other.class"), "bytecode")

	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("Build: %v", err)
	}
	if _, err := os.Stat(filepath.Join(foreign, classesDirName, "com", "example", "Other.class")); err != nil {
		t.Errorf("the build deleted a running builder's staging directory: %v", err)
	}
}

// A build killed outright leaves its staging directory behind. The next build reclaims it,
// but only once its owner is gone.
func TestBuildSweepsStagingOfAKilledBuild(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := BuildDir(project)

	abandoned := filepath.Join(stagingRoot(output), filepath.Base(output)+"-2147483646")
	writeFile(t, filepath.Join(abandoned, classesDirName, "com", "example", "Other.class"), "bytecode")

	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("Build: %v", err)
	}
	if _, err := os.Stat(abandoned); !os.IsNotExist(err) {
		t.Errorf("a killed build's staging directory was not reclaimed: %v", err)
	}
}

// Whatever is left behind must be invisible to the resolver: staged classes are not
// compiled models, and resolving them would apply a half-built batch to a scan.
func TestStagingIsInvisibleToTheResolver(t *testing.T) {
	root := t.TempDir()
	output := filepath.Join(root, "out")
	abandoned := filepath.Join(stagingRoot(output), filepath.Base(output)+"-1")
	writeFile(t, filepath.Join(abandoned, classesDirName, "com", "example", "Other.class"), "bytecode")

	models, err := Resolve(root, newFakeBuilder(t))
	if err != nil {
		t.Fatalf("Resolve: %v", err)
	}
	if len(models.JavaClassDirs) != 0 {
		t.Errorf("a leftover staging directory was resolved as compiled models: %v", models.JavaClassDirs)
	}
}

// A completed build leaves no staging or superseded directory behind.
func TestBuildCleansUpAfterItself(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := BuildDir(project)

	for range 2 {
		if err := Build(project, output, newFakeBuilder(t)); err != nil {
			t.Fatalf("Build: %v", err)
		}
	}

	entries, err := os.ReadDir(filepath.Dir(output))
	if err != nil {
		t.Fatal(err)
	}
	for _, entry := range entries {
		if entry.Name() != filepath.Base(output) {
			t.Errorf("build left %s behind next to the output", entry.Name())
		}
	}
}

func TestBuildRefusesToOverwriteUnrelatedDirectory(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := t.TempDir()
	precious := filepath.Join(output, "notes.txt")
	writeFile(t, precious, "important user data")

	// The build must not replace an unrelated directory.
	err := Build(project, output, newFakeBuilder(t))
	if err == nil {
		t.Fatal("expected a build into an unrelated directory to be refused")
	}
	if !strings.Contains(err.Error(), "not a model build output") {
		t.Errorf("unexpected error: %v", err)
	}
	if content, readErr := os.ReadFile(precious); readErr != nil || string(content) != "important user data" {
		t.Errorf("existing content was destroyed: content=%q err=%v", content, readErr)
	}
}

func TestBuildAcceptsEmptyAndPreviousOutputDirectories(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := t.TempDir() // exists and is empty

	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("build into an empty directory: %v", err)
	}
	// A new build can replace the first build.
	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("rebuild over a previous build output: %v", err)
	}
}

func TestBuildWritesReadableDescriptor(t *testing.T) {
	project := newProject(t, t.TempDir())
	output := filepath.Join(t.TempDir(), "out")

	if err := Build(project, output, newFakeBuilder(t)); err != nil {
		t.Fatalf("Build: %v", err)
	}

	raw, err := os.ReadFile(filepath.Join(output, descriptorName))
	if err != nil {
		t.Fatal(err)
	}
	var parsed descriptor
	if err := yaml.Unmarshal(raw, &parsed); err != nil {
		t.Fatalf("descriptor is not valid YAML: %v\n%s", err, raw)
	}
	// The descriptor must mean the same thing wherever the output is read, so it may not
	// carry a path that only exists on the machine that built it.
	if filepath.IsAbs(parsed.SourceProject) {
		t.Errorf("sourceProject = %q, want a path relative to the output", parsed.SourceProject)
	}
	if resolved := filepath.Clean(filepath.Join(output, parsed.SourceProject)); resolved != project {
		t.Errorf("sourceProject resolves to %q, want %q", resolved, project)
	}
	if parsed.Dependencies == nil {
		t.Error("dependencies should be an empty list, not null")
	}
}

func TestBuildRejectsCollidingModelClasses(t *testing.T) {
	project := newProject(t, t.TempDir())
	builder := &collidingBuilder{fakeBuilder{t: t}}

	err := Build(project, BuildDir(project), builder)
	if err == nil {
		t.Fatal("expected colliding model classes to fail the build")
	}
	if !strings.Contains(err.Error(), "exactly one target class") {
		t.Errorf("unexpected error: %v", err)
	}
}

// collidingBuilder writes the same class from two modules.
type collidingBuilder struct{ fakeBuilder }

func (b *collidingBuilder) Compile(projectDir, projectModelDir string) error {
	writeModuleClasses(b.t, projectModelDir, map[string][]string{"c0_main": {"Model"}, "c1_main": {"Model"}})
	return nil
}
