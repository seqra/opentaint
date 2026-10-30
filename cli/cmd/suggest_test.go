package cmd

import (
	"testing"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
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

func TestBuildFailSuggestions(t *testing.T) {
	orig := globals.LogPath
	t.Cleanup(func() { globals.LogPath = orig })

	docker := output.Suggestion{Description: "docker hint", Command: "opentaint --docker"}

	// With a log path: the log pointer leads, then the contextual hint.
	globals.LogPath = "/tmp/run.log"
	got := buildFailSuggestions([]output.Suggestion{docker})
	if len(got) != 2 {
		t.Fatalf("expected 2 suggestions, got %d: %+v", len(got), got)
	}
	if got[0].Command != "/tmp/run.log" {
		t.Errorf("expected log pointer first, got %+v", got[0])
	}
	if got[1] != docker {
		t.Errorf("expected contextual hint last, got %+v", got[1])
	}

	// No log path: only the contextual hint remains.
	globals.LogPath = ""
	got = buildFailSuggestions([]output.Suggestion{docker})
	if len(got) != 1 || got[0] != docker {
		t.Fatalf("expected only the contextual hint, got %+v", got)
	}

	// No contextual and no log: empty slice (renders nothing downstream).
	if got := buildFailSuggestions(nil); len(got) != 0 {
		t.Errorf("expected no suggestions, got %+v", got)
	}
}

func TestAnalyzerLogSuggestion(t *testing.T) {
	for code, want := range map[int]bool{analyzer.ExitException: true, analyzer.ExitOOM: false, analyzer.ExitTimeout: false, 1: false} {
		sug, ok := analyzerLogSuggestion(&analyzer.Error{ExitCode: code}, "/tmp/opentaint-1/analyzer.log")
		if ok != want {
			t.Errorf("exit %d: suggestion shown = %v, want %v", code, ok, want)
		}
		if ok && sug.Command != "/tmp/opentaint-1/analyzer.log" {
			t.Errorf("exit %d: command = %q, want the analyzer log", code, sug.Command)
		}
	}
	if _, ok := analyzerLogSuggestion(nil, "/tmp/analyzer.log"); ok {
		t.Error("a successful run points at the analyzer log")
	}
}
