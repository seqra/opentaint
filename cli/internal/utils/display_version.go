package utils

import (
	"fmt"

	"github.com/seqra/opentaint/internal/globals"
)

func ArtifactDisplayVersion(def globals.ArtifactDef, jarPathOverride string) string {
	resolvedTier, resolvedPath := "", ""
	if jarPathOverride == "" {
		resolvedTier, resolvedPath, _ = resolveArtifactTier(def)
	}
	return displayVersion(def.Version, jarPathOverride, resolvedTier, resolvedPath)
}

// displayVersion renders an artifact's display label:
//   - an explicit jar-path override always wins                  -> custom (<override>)
//   - resolved from the bundled tier (a user-controlled build next to the binary,
//     whose nominal version may not match its actual content)    -> custom (<resolvedPath>)
//   - an empty/unpinned version                                  -> custom (<resolvedPath>)
//   - otherwise (a managed install/cache release)                -> the version string
func displayVersion(version, overridePath, resolvedTier, resolvedPath string) string {
	if overridePath != "" {
		return customLabel(overridePath)
	}
	if resolvedTier == TierBundled {
		return customLabel(resolvedPath)
	}
	if version == "" {
		return customLabel(resolvedPath)
	}
	return version
}

func customLabel(path string) string {
	return fmt.Sprintf("custom (%s)", path)
}
