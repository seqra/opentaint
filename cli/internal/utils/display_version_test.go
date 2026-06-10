package utils

import (
	"testing"

	"github.com/seqra/opentaint/internal/globals"
)

func TestDisplayVersion(t *testing.T) {
	tests := []struct {
		name           string
		version        string
		overridePath   string
		resolvedTier   string
		resolvedPath   string
		bundledRelease bool
		want           string
	}{
		{
			name:         "pinned version, no override, managed install tier",
			version:      "analyzer/2026.05.27.68ab20a",
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
			name:         "bundled tier without release marker is a local build",
			version:      "rules/v0.2.0",
			resolvedTier: TierBundled,
			resolvedPath: "/opt/opentaint/lib/rules",
			want:         "custom (/opt/opentaint/lib/rules)",
		},
		{
			name:           "bundled tier with release marker keeps the pinned version",
			version:        "analyzer/2026.06.09.fc56601",
			resolvedTier:   TierBundled,
			resolvedPath:   "/home/user/.opentaint/install/lib/opentaint-project-analyzer.jar",
			bundledRelease: true,
			want:           "analyzer/2026.06.09.fc56601",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := displayVersion(tt.version, tt.overridePath, tt.resolvedTier, tt.resolvedPath, tt.bundledRelease)
			if got != tt.want {
				t.Errorf("displayVersion(%q, %q, %q, %q, %v) = %q, want %q",
					tt.version, tt.overridePath, tt.resolvedTier, tt.resolvedPath, tt.bundledRelease, got, tt.want)
			}
		})
	}
}

func TestArtifactDisplayVersionOverride(t *testing.T) {
	override := globals.ArtifactByKind("analyzer").WithVersion("analyzer/2026.05.27.68ab20a")
	override.Override = "/home/dev/analyzer.jar"
	if got := ArtifactDisplayVersion(override); got != "custom (/home/dev/analyzer.jar)" {
		t.Errorf("override case: got %q, want %q", got, "custom (/home/dev/analyzer.jar)")
	}
}

func TestArtifactVersionShortVariants(t *testing.T) {
	custom := globals.ArtifactByKind("analyzer").WithVersion("analyzer/2026.05.27.68ab20a")
	custom.Override = "/home/dev/analyzer.jar"

	if got := ArtifactVersionWithPath(custom); got != "custom (/home/dev/analyzer.jar)" {
		t.Errorf("WithPath custom: got %q, want %q", got, "custom (/home/dev/analyzer.jar)")
	}
	if got := ArtifactVersion(custom); got != "custom" {
		t.Errorf("bare custom: got %q, want %q", got, "custom")
	}
}
