package cmd

import "testing"

func TestAnalyzerDisplayVersion(t *testing.T) {
	// JAR-path override: report the override path, not the pin.
	if got := analyzerDisplayVersion("analyzer/2026.05.27.68ab20a", "/home/dev/analyzer.jar"); got != "custom (/home/dev/analyzer.jar)" {
		t.Errorf("override case: got %q, want %q", got, "custom (/home/dev/analyzer.jar)")
	}
	// Pinned version, no override: report the pin verbatim (resolved path is irrelevant here).
	if got := analyzerDisplayVersion("analyzer/2026.05.27.68ab20a", ""); got != "analyzer/2026.05.27.68ab20a" {
		t.Errorf("pinned case: got %q, want %q", got, "analyzer/2026.05.27.68ab20a")
	}
}
