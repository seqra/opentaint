package utils

import (
	"testing"

	"github.com/seqra/opentaint/internal/globals"
)

func TestDisplayVersion(t *testing.T) {
	tests := []struct {
		name         string
		version      string
		overridePath string
		resolvedTier string
		resolvedPath string
		want         string
	}{
		{
			name:         "pinned version, no override, managed install tier",
			version:      "analyzer/2026.05.27.68ab20a",
			overridePath: "",
			resolvedTier: TierInstall,
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "analyzer/2026.05.27.68ab20a",
		},
		{
			name:         "jar-path override wins over a present version",
			version:      "analyzer/2026.05.27.68ab20a",
			overridePath: "/home/dev/build/analyzer.jar",
			resolvedTier: TierBundled,
			resolvedPath: "/home/dev/build/analyzer.jar",
			want:         "custom (/home/dev/build/analyzer.jar)",
		},
		{
			name:         "empty pin falls back to resolved path",
			version:      "",
			overridePath: "",
			resolvedTier: TierCache,
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "custom (/opt/opentaint/lib/opentaint-project-analyzer.jar)",
		},
		{
			name:         "override takes precedence over empty pin",
			version:      "",
			overridePath: "/home/dev/build/analyzer.jar",
			resolvedTier: TierInstall,
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "custom (/home/dev/build/analyzer.jar)",
		},
		{
			name:         "bundled tier shows custom path even with a pinned version",
			version:      "rules/v0.2.0",
			overridePath: "",
			resolvedTier: TierBundled,
			resolvedPath: "/opt/opentaint/lib/rules",
			want:         "custom (/opt/opentaint/lib/rules)",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := displayVersion(tt.version, tt.overridePath, tt.resolvedTier, tt.resolvedPath)
			if got != tt.want {
				t.Errorf("displayVersion(%q, %q, %q, %q) = %q, want %q",
					tt.version, tt.overridePath, tt.resolvedTier, tt.resolvedPath, got, tt.want)
			}
		})
	}
}

func TestArtifactDisplayVersion(t *testing.T) {
	analyzer := globals.ArtifactByKind("analyzer")

	override := analyzer.WithVersion("analyzer/2026.05.27.68ab20a")
	if got := ArtifactDisplayVersion(override, "/home/dev/analyzer.jar"); got != "custom (/home/dev/analyzer.jar)" {
		t.Errorf("override case: got %q, want %q", got, "custom (/home/dev/analyzer.jar)")
	}

	pinned := analyzer.WithVersion("analyzer/2026.05.27.68ab20a")
	if got := ArtifactDisplayVersion(pinned, ""); got != "analyzer/2026.05.27.68ab20a" {
		t.Errorf("pinned case: got %q, want %q", got, "analyzer/2026.05.27.68ab20a")
	}
}

func TestArtifactVersionShortVariants(t *testing.T) {
	analyzer := globals.ArtifactByKind("analyzer").WithVersion("analyzer/2026.05.27.68ab20a")

	// Pinned release: kind prefix stripped, identical for both helpers.
	if got := ArtifactVersionWithPath(analyzer, ""); got != "2026.05.27.68ab20a" {
		t.Errorf("WithPath pinned: got %q, want %q", got, "2026.05.27.68ab20a")
	}
	if got := ArtifactVersion(analyzer, ""); got != "2026.05.27.68ab20a" {
		t.Errorf("bare pinned: got %q, want %q", got, "2026.05.27.68ab20a")
	}

	// Custom (jar override): WithPath keeps the path (single-line display),
	// bare collapses to "custom" (the path is shown separately, no dup).
	if got := ArtifactVersionWithPath(analyzer, "/home/dev/analyzer.jar"); got != "custom (/home/dev/analyzer.jar)" {
		t.Errorf("WithPath custom: got %q, want %q", got, "custom (/home/dev/analyzer.jar)")
	}
	if got := ArtifactVersion(analyzer, "/home/dev/analyzer.jar"); got != "custom" {
		t.Errorf("bare custom: got %q, want %q", got, "custom")
	}
}
