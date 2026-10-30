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
	content, err := os.ReadFile(filepath.Join(dir, goModuleFile))
	if err != nil {
		return "", fmt.Errorf("failed to read the Go model %s: %w", dir, err)
	}
	return modfile.ModulePath(content), nil
}
