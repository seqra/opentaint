package sarif

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

// SaveReport writes report to path as indented JSON. The write goes to a
// temporary file in the destination directory and is then renamed over path, so
// a crash mid-write can never leave a truncated report behind — which matters
// because triage rewrites reports in place.
func SaveReport(report *Report, path string) error {
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to encode sarif report: %w", err)
	}
	data = append(data, '\n')

	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	tmp, err := os.CreateTemp(dir, ".sarif-*.tmp")
	if err != nil {
		return fmt.Errorf("failed to create temporary report file: %w", err)
	}
	tmpName := tmp.Name()
	defer func() { _ = os.Remove(tmpName) }() // no-op once the rename below succeeds

	if _, err := tmp.Write(data); err != nil {
		_ = tmp.Close()
		return fmt.Errorf("failed to write sarif report: %w", err)
	}
	if err := tmp.Close(); err != nil {
		return fmt.Errorf("failed to write sarif report: %w", err)
	}
	if err := os.Chmod(tmpName, 0o644); err != nil {
		return fmt.Errorf("failed to set report permissions: %w", err)
	}
	if err := os.Rename(tmpName, path); err != nil {
		return fmt.Errorf("failed to replace sarif report: %w", err)
	}
	return nil
}
