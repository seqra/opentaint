package testrule

import (
	"os"
	"path/filepath"
	"testing"
)

func TestScaffoldGoWritesMarkers(t *testing.T) {
	dir := t.TempDir()
	if err := ScaffoldGo(dir); err != nil {
		t.Fatalf("ScaffoldGo: %v", err)
	}
	for _, path := range []string{
		filepath.Join("taint", "taint.go"),
		filepath.Join(markersDir, filepath.FromSlash(genericGoSourceRule)),
		filepath.Join(markersDir, filepath.FromSlash(genericGoSinkRule)),
	} {
		if _, err := os.Stat(filepath.Join(dir, path)); err != nil {
			t.Errorf("missing %s: %v", path, err)
		}
	}
}
