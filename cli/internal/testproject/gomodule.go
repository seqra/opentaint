package testproject

import (
	"errors"
	"fmt"
	"go/version"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"

	"github.com/seqra/opentaint/internal/utils"
	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"
)

// BootstrapGo writes a go.mod for modulePath that requires each module@version dependency.
func BootstrapGo(outputDir, modulePath string, dependencies []string) error {
	content, err := GoModule(modulePath, dependencies, GoVersion())
	if err != nil {
		return err
	}
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(outputDir, goModuleFileName): content,
	})
}

// TidyGo runs `go mod tidy` in dir, so that its go.mod lists the modules that its packages import.
func TidyGo(dir string) error {
	return runGo(dir, "go mod tidy", "mod", "tidy")
}

// BuildGo runs `go build ./...` in dir and discards the output. -buildvcs=false: dir may lie in a
// repository that go cannot read.
func BuildGo(dir string) error {
	return runGo(dir, "go build ./...", "build", "-o", os.DevNull, "-buildvcs=false", "./...")
}

// runGo runs go with args in dir. Its error names the command as name and holds the go output.
func runGo(dir, name string, args ...string) error {
	command := exec.Command("go", args...)
	command.Dir = dir
	output, err := command.CombinedOutput()
	if err == nil {
		return nil
	}
	if details := strings.TrimSpace(string(output)); details != "" {
		err = errors.New(details)
	}
	return fmt.Errorf("`%s` failed: %w", name, err)
}

// GoVersion is the go version of a generated go.mod: that of the local toolchain, else the one that
// built the CLI.
func GoVersion() string {
	goVersion := ""
	if output, err := exec.Command("go", "env", "GOVERSION").Output(); err == nil {
		goVersion = strings.TrimSpace(string(output))
	}
	if !version.IsValid(goVersion) {
		goVersion = runtime.Version()
	}
	if !version.IsValid(goVersion) {
		goVersion = "go1.25.0"
	}
	return strings.TrimPrefix(goVersion, "go")
}

// ErrNotModuleVersion is the error of a Go dependency that is not module@version.
var ErrNotModuleVersion = errors.New("not module@version")

// CheckGoDependency checks that dependency is module@version with a valid module path and
// version.
func CheckGoDependency(dependency string) error {
	path, dependencyVersion, ok := strings.Cut(dependency, "@")
	if !ok || path == "" || dependencyVersion == "" || strings.Contains(dependencyVersion, "@") {
		return ErrNotModuleVersion
	}
	return module.Check(path, dependencyVersion)
}

// GoModule formats a go.mod for modulePath that requires each module@version dependency.
func GoModule(modulePath string, dependencies []string, goVersion string) ([]byte, error) {
	file := new(modfile.File)
	if err := file.AddModuleStmt(modulePath); err != nil {
		return nil, fmt.Errorf("set Go module path: %w", err)
	}
	if err := file.AddGoStmt(goVersion); err != nil {
		return nil, fmt.Errorf("set Go language version: %w", err)
	}

	for _, dependency := range dependencies {
		if err := CheckGoDependency(dependency); err != nil {
			return nil, fmt.Errorf("invalid Go dependency `%s`: %w", dependency, err)
		}
		path, dependencyVersion, _ := strings.Cut(dependency, "@")
		if err := file.AddRequire(path, dependencyVersion); err != nil {
			return nil, fmt.Errorf("add Go dependency `%s`: %w", dependency, err)
		}
	}

	file.SortBlocks()
	content, err := file.Format()
	if err != nil {
		return nil, fmt.Errorf("format Go module: %w", err)
	}
	return content, nil
}
