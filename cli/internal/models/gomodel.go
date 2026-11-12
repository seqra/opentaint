package models

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"golang.org/x/mod/modfile"
)

// goModelModulePath is the module path of every Go model module.
const goModelModulePath = "opentaint"

// isGoModelModulePath reports whether a go.mod module path is that of a Go model module:
// "opentaint" or a path below it, so its packages are addressed as opentaint/<target-import-path>.
func isGoModelModulePath(modulePath string) bool {
	return modulePath == goModelModulePath || strings.HasPrefix(modulePath, goModelModulePath+"/")
}

// goModulePath returns the module path declared by the go.mod in dir.
func goModulePath(dir string) (string, error) {
	goMod := filepath.Join(dir, goModuleFile)
	content, err := os.ReadFile(goMod)
	if err != nil {
		return "", fmt.Errorf("failed to read `%s`: %w", goMod, err)
	}
	return modfile.ModulePath(content), nil
}

// checkGoModelModule rejects a Go module that is not a Go model project. The analyzer finds the
// models of a package by its path below the module path opentaint.
func checkGoModelModule(dir string) error {
	modulePath, err := goModulePath(dir)
	if err != nil {
		return err
	}
	if !isGoModelModulePath(modulePath) {
		return fmt.Errorf("`%s` is not a model project: %w", dir, fmt.Errorf(
			"its go.mod declares the module `%s`, and a Go model project declares `%s`",
			modulePath, goModelModulePath))
	}
	return nil
}
