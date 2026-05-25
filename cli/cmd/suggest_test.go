package cmd

import (
	"testing"

	"github.com/seqra/opentaint/internal/globals"
)

func TestLogSuggestion(t *testing.T) {
	orig := globals.LogPath
	t.Cleanup(func() { globals.LogPath = orig })

	globals.LogPath = ""
	if _, ok := logSuggestion(); ok {
		t.Errorf("expected ok=false when LogPath is empty")
	}

	globals.LogPath = "/tmp/run.log"
	sug, ok := logSuggestion()
	if !ok {
		t.Fatalf("expected ok=true when LogPath is set")
	}
	if sug.Command != "/tmp/run.log" {
		t.Errorf("expected command to be the log path, got %q", sug.Command)
	}
	if sug.Description == "" {
		t.Errorf("expected a non-empty description")
	}
}
