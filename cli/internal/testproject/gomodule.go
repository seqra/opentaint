package testproject

import (
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
		filepath.Join(outputDir, "go.mod"): content,
	})
}

// TidyGo runs 'go mod tidy' in dir, so its go.mod lists the modules its packages import.
func TidyGo(dir string) error {
	return runGo(dir, "go mod tidy", "mod", "tidy")
}

// BuildGo runs 'go build ./...' in dir, so compile errors in the samples surface before the
// analyzer runs. The build output is discarded.
func BuildGo(dir string) error {
	return runGo(dir, "go build ./...", "build", "-o", os.DevNull, "./...")
}

// runGo runs the go command with args in dir. A failure reports name, dir and the go output.
func runGo(dir, name string, args ...string) error {
	command := exec.Command("go", args...)
	command.Dir = dir
	output, err := command.CombinedOutput()
	if err == nil {
		return nil
	}
	if details := strings.TrimSpace(string(output)); details != "" {
		return fmt.Errorf("'%s' failed in %s:\n%s", name, dir, details)
	}
	return fmt.Errorf("'%s' failed in %s: %w", name, dir, err)
}

// GoVersion is the language version for a generated go.mod: the version of the local Go toolchain,
// so the module builds with the toolchain that will build the samples. Without a local toolchain it
// falls back to the version the CLI was built with.
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
		path, dependencyVersion, ok := strings.Cut(dependency, "@")
		if !ok || path == "" || dependencyVersion == "" || strings.Contains(dependencyVersion, "@") {
			return nil, fmt.Errorf("invalid Go dependency %q: use module@version", dependency)
		}
		if err := module.Check(path, dependencyVersion); err != nil {
			return nil, fmt.Errorf("invalid Go dependency %q: %w", dependency, err)
		}
		if err := file.AddRequire(path, dependencyVersion); err != nil {
			return nil, fmt.Errorf("add Go dependency %q: %w", dependency, err)
		}
	}

	file.SortBlocks()
	content, err := file.Format()
	if err != nil {
		return nil, fmt.Errorf("format Go module: %w", err)
	}
	return content, nil
}
