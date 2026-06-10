package utils

import (
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
)

func ArtifactDisplayVersion(def globals.ArtifactDef) string {
	tier, path, bundledRelease := artifactResolution(def)
	return displayVersion(def.Version, def.Override, tier, path, bundledRelease)
}

func ArtifactVersionWithPath(def globals.ArtifactDef) string {
	return strings.TrimPrefix(ArtifactDisplayVersion(def), def.Kind()+"/")
}

func ArtifactVersion(def globals.ArtifactDef) string {
	tier, _, bundledRelease := artifactResolution(def)
	if isCustomArtifact(def.Version, def.Override, tier, bundledRelease) {
		return "custom"
	}
	return strings.TrimPrefix(def.Version, def.Kind()+"/")
}

func artifactResolution(def globals.ArtifactDef) (tier, path string, bundledRelease bool) {
	if def.Override == "" {
		tier, path, _ = resolveArtifactTier(def)
		if tier == TierBundled {
			bundledRelease = IsBundledRelease()
		}
	}
	return tier, path, bundledRelease
}

func isCustomArtifact(version, overridePath, resolvedTier string, bundledRelease bool) bool {
	if overridePath != "" || version == "" {
		return true
	}
	return resolvedTier == TierBundled && !bundledRelease
}

func displayVersion(version, overridePath, resolvedTier, resolvedPath string, bundledRelease bool) string {
	if isCustomArtifact(version, overridePath, resolvedTier, bundledRelease) {
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
