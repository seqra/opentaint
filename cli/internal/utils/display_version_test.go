package utils

import "testing"

func TestDisplayVersion(t *testing.T) {
	tests := []struct {
		name         string
		version      string
		overridePath string
		resolvedPath string
		want         string
	}{
		{
			name:         "pinned version, no override",
			version:      "analyzer/2026.05.27.68ab20a",
			overridePath: "",
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "analyzer/2026.05.27.68ab20a",
		},
		{
			name:         "jar-path override wins over a present version",
			version:      "analyzer/2026.05.27.68ab20a",
			overridePath: "/home/dev/build/analyzer.jar",
			resolvedPath: "/home/dev/build/analyzer.jar",
			want:         "custom (/home/dev/build/analyzer.jar)",
		},
		{
			name:         "empty pin falls back to resolved path",
			version:      "",
			overridePath: "",
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "custom (/opt/opentaint/lib/opentaint-project-analyzer.jar)",
		},
		{
			name:         "override takes precedence over empty pin",
			version:      "",
			overridePath: "/home/dev/build/analyzer.jar",
			resolvedPath: "/opt/opentaint/lib/opentaint-project-analyzer.jar",
			want:         "custom (/home/dev/build/analyzer.jar)",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := DisplayVersion(tt.version, tt.overridePath, tt.resolvedPath)
			if got != tt.want {
				t.Errorf("DisplayVersion(%q, %q, %q) = %q, want %q",
					tt.version, tt.overridePath, tt.resolvedPath, got, tt.want)
			}
		})
	}
}
