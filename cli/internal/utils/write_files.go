package utils

import (
	"fmt"
	"os"
)

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
