package utils

import (
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
)

// ArtifactDisplayVersion renders an artifact's full display label, keeping the
// "<kind>/" version prefix. Used for the SARIF tool version, where the prefix
// is part of the identifier.
func ArtifactDisplayVersion(def globals.ArtifactDef, jarPathOverride string) string {
	tier, path := artifactResolution(def, jarPathOverride)
	return displayVersion(def.Version, jarPathOverride, tier, path)
}

// ArtifactVersionWithPath is the version with the redundant "<kind>/" prefix
// stripped, for a single-line display that has no separate path field (e.g.
// scan's "Analyzer:" node). A custom build keeps its jar path — "custom (<path>)"
// — since that line is the only place the path appears.
func ArtifactVersionWithPath(def globals.ArtifactDef, jarPathOverride string) string {
	return strings.TrimPrefix(ArtifactDisplayVersion(def, jarPathOverride), def.Kind()+"/")
}

// ArtifactVersion is the version for a display that shows the resolved path on
// its own line (e.g. health's tree). A managed release yields the bare version;
// a custom build collapses to "custom", so the path isn't repeated.
func ArtifactVersion(def globals.ArtifactDef, jarPathOverride string) string {
	tier, _ := artifactResolution(def, jarPathOverride)
	if isCustomArtifact(def.Version, jarPathOverride, tier) {
		return "custom"
	}
	return strings.TrimPrefix(def.Version, def.Kind()+"/")
}

// artifactResolution resolves the artifact's tier and path, unless an explicit
// jar override is set (in which case neither is needed).
func artifactResolution(def globals.ArtifactDef, jarPathOverride string) (tier, path string) {
	if jarPathOverride == "" {
		tier, path, _ = resolveArtifactTier(def)
	}
	return tier, path
}

// isCustomArtifact reports whether the artifact is a custom build — an explicit
// jar override, a bundled build next to the binary (whose nominal version may
// not match its content), or an unpinned version — rather than a managed
// install/cache release.
func isCustomArtifact(version, overridePath, resolvedTier string) bool {
	return overridePath != "" || resolvedTier == TierBundled || version == ""
}

// displayVersion renders an artifact's label: a custom build as "custom (<path>)"
// (the override path if set, otherwise the resolved path), and a managed release
// as its version string.
func displayVersion(version, overridePath, resolvedTier, resolvedPath string) string {
	if isCustomArtifact(version, overridePath, resolvedTier) {
		path := overridePath
		if path == "" {
			path = resolvedPath
		}
		return customLabel(path)
	}
	return version
}

func customLabel(path string) string {
	return fmt.Sprintf("custom (%s)", path)
}
