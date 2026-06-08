package utils

import (
	"fmt"
	"os"
)

// WriteFiles writes each path->content entry to disk, creating parent
// directories as needed. It is the shared primitive behind the test-project
// scaffolders (see internal/testrule and internal/testapprox).
func WriteFiles(files map[string][]byte) error {
	for path, content := range files {
		if err := EnsureParentDir(path); err != nil {
			return err
		}
		if err := os.WriteFile(path, content, 0o644); err != nil {
			return fmt.Errorf("write %s: %w", path, err)
		}
	}
	return nil
}
