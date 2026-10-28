package testproject

import (
	"fmt"
	"go/version"
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
