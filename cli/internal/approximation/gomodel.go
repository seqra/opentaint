package approximation

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"golang.org/x/mod/modfile"
)

// goModelModulePath is the module path of every Go model module.
const goModelModulePath = "opentaint"

// ValidateGoModel checks that dir is a Go model module: a directory whose go.mod declares module
// "opentaint" or a path below it, so its packages are addressed as opentaint/<target-import-path>.
// The analyzer reports other inputs only while it loads the models.
func ValidateGoModel(dir string) error {
	info, err := os.Stat(dir)
	if err != nil {
		return fmt.Errorf("Go model %s: %w", dir, err)
	}
	if !info.IsDir() {
		return fmt.Errorf("Go model %s is not a directory", dir)
	}
	if !IsGoProject(dir) {
		if IsProject(dir) {
			return fmt.Errorf("%s is a Java approximation project; pass it with --dataflow-approximations", dir)
		}
		return fmt.Errorf("Go model %s has no go.mod; create it with 'opentaint approximation init --language go'", dir)
	}
	path := filepath.Join(dir, goModuleFile)
	content, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("Go model %s: %w", dir, err)
	}
	modulePath := modfile.ModulePath(content)
	if modulePath != goModelModulePath && !strings.HasPrefix(modulePath, goModelModulePath+"/") {
		return fmt.Errorf("Go model %s declares module %q; a Go model module must be %q", dir, modulePath, goModelModulePath)
	}
	return nil
}
