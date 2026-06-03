package utils

import (
	"fmt"

	"github.com/seqra/opentaint/internal/globals"
)

func ArtifactDisplayVersion(def globals.ArtifactDef, jarPathOverride string) string {
	resolvedPath := ""
	if jarPathOverride == "" && def.Version == "" {
		resolvedPath, _ = resolveArtifactPath(def)
	}
	return displayVersion(def.Version, jarPathOverride, resolvedPath)
}

func displayVersion(version, overridePath, resolvedPath string) string {
	if overridePath != "" {
		return customLabel(overridePath)
	}
	if version == "" {
		return customLabel(resolvedPath)
	}
	return version
}

func customLabel(path string) string {
	return fmt.Sprintf("custom (%s)", path)
}
