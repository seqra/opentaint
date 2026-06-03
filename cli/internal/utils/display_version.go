package utils

import "fmt"

// DisplayVersion returns the user-facing version label for a dependency.
//
// It returns "custom (<path>)" when the artifact came from an explicit
// JAR-path override (overridePath set) or when no version is pinned
// (version empty); otherwise it returns the version string unchanged.
//
// resolvedPath is the location the artifact was resolved to; it is only used
// for the empty-version fallback. overridePath, when set, is both the source
// of truth and the path shown.
func DisplayVersion(version, overridePath, resolvedPath string) string {
	if overridePath != "" {
		return fmt.Sprintf("custom (%s)", overridePath)
	}
	if version == "" {
		return fmt.Sprintf("custom (%s)", resolvedPath)
	}
	return version
}
