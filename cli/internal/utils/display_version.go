package utils

import (
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
)

// ArtifactVersionShort is ArtifactDisplayVersion without the leading "<kind>/"
// prefix. Use it where the value is already labelled with the artifact kind
// (e.g. an "Analyzer:" tree node), so the kind isn't shown twice. The
// "custom (...)" form carries no such prefix and is returned unchanged.
func ArtifactVersionShort(def globals.ArtifactDef, jarPathOverride string) string {
	return strings.TrimPrefix(ArtifactDisplayVersion(def, jarPathOverride), def.Kind()+"/")
}

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
