package utils

import (
	"bytes"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/globals"
)

// GetOpenTaintHomePath returns ~/.opentaint/ without creating it.
// Use this when you only need to read/check the directory (e.g. prune scanning).
func GetOpenTaintHomePath() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".opentaint"), nil
}

// GetOpenTaintHome returns ~/.opentaint/, creating it if needed.
func GetOpenTaintHome() (string, error) {
	path, err := GetOpenTaintHomePath()
	if err != nil {
		return "", err
	}
	if err := os.MkdirAll(path, os.ModePerm); err != nil {
		return "", err
	}
	return path, nil
}

// pathExists reports whether a path exists on disk.
func pathExists(p string) bool {
	_, err := os.Stat(p)
	return err == nil
}

// exeDir returns the directory containing the current executable, resolved through symlinks.
// Returns empty string if the path cannot be determined.
func exeDir() string {
	exe, err := os.Executable()
	if err != nil {
		return ""
	}
	exe, err = filepath.EvalSymlinks(exe)
	if err != nil {
		return ""
	}
	return filepath.Dir(exe)
}

// resolveBundledDir locates a bundled artifact directory (e.g. "lib" or "jre")
// relative to the binary, supporting both supported install layouts:
//
//   - flat: <exe-dir>/<name> — the managed install (~/.opentaint/install/) keeps
//     the binary, lib/ and jre/ in the same directory.
//   - FHS:  <exe-dir>/../<name> — `make install` puts the binary in <prefix>/bin
//     and artifacts in <prefix>/lib, so the directory is a sibling of bin/.
//
// The first layout whose directory exists wins. When neither exists it falls
// back to the flat path so callers keep a stable default probe/download target.
// Returns empty string if exeDir is empty (executable path undeterminable).
func resolveBundledDir(exeDir, name string) string {
	if exeDir == "" {
		return ""
	}
	flat := filepath.Join(exeDir, name)
	if pathExists(flat) {
		return flat
	}
	if sibling := filepath.Join(exeDir, "..", name); pathExists(sibling) {
		return sibling
	}
	return flat
}

// GetBundledLibPath returns the path to the bundled lib directory next to the binary.
// Returns empty string if the path cannot be determined.
func GetBundledLibPath() string {
	return resolveBundledDir(exeDir(), "lib")
}

// GetBundledJREPath returns the path to the bundled JRE directory next to the binary.
// Returns empty string if the path cannot be determined.
func GetBundledJREPath() string {
	return resolveBundledDir(exeDir(), "jre")
}

// GetInstallDir returns the path to ~/.opentaint/install/.
// Returns empty string if the home directory cannot be determined.
func GetInstallDir() string {
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	return filepath.Join(home, ".opentaint", "install")
}

// GetInstallLibPath returns the path to the lib directory in ~/.opentaint/install/.
// Returns empty string if the home directory cannot be determined.
func GetInstallLibPath() string {
	if dir := GetInstallDir(); dir != "" {
		return filepath.Join(dir, "lib")
	}
	return ""
}

// GetInstallJREPath returns the path to the jre directory in ~/.opentaint/install/.
// Returns empty string if the home directory cannot be determined.
func GetInstallJREPath() string {
	if dir := GetInstallDir(); dir != "" {
		return filepath.Join(dir, "jre")
	}
	return ""
}

// IsInstallCurrent reports whether the install-tier version marker matches
// the embedded versions.yaml. Returns false if the marker is missing or differs.
func IsInstallCurrent() bool {
	installDir := GetInstallDir()
	if installDir == "" {
		return false
	}
	data, err := os.ReadFile(filepath.Join(installDir, ".versions"))
	if err != nil {
		return false
	}
	return bytes.Equal(data, globals.GetVersionsYAML())
}

// WriteInstallVersionMarker writes the embedded versions.yaml content to
// ~/.opentaint/install/.versions so that future runs can detect stale installs.
func WriteInstallVersionMarker() error {
	installDir := GetInstallDir()
	if installDir == "" {
		return nil
	}
	if err := os.MkdirAll(installDir, 0o755); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(installDir, ".versions"), globals.GetVersionsYAML(), 0o644)
}

// CleanInstallDir removes the install-tier lib and jre directories along with
// the stale .versions marker. This is called before re-downloading after an upgrade.
func CleanInstallDir() error {
	installDir := GetInstallDir()
	if installDir == "" {
		return nil
	}
	for _, sub := range []string{"lib", "jre", ".versions"} {
		if err := os.RemoveAll(filepath.Join(installDir, sub)); err != nil {
			return err
		}
	}
	return nil
}

// ReconcileInstallMarker writes the install-tier version marker if all
// bind-version artifacts are present but the marker is missing or stale.
// This reconciles the marker after SelfUpdate, where the old binary cannot
// write correct data. Safe to call on every command invocation (a few Stat calls).
func ReconcileInstallMarker() {
	if IsInstallCurrent() {
		return
	}
	installLib := GetInstallLibPath()
	if installLib == "" {
		return
	}
	for _, def := range globals.Artifacts() {
		if !pathExists(filepath.Join(installLib, def.LibSubpath)) {
			return
		}
	}
	_ = WriteInstallVersionMarker()
}

// resolveArtifactTier resolves both the storage tier and path for an artifact by
// checking tiers in order:
//  1. Bundled path (next to binary) — only if version matches bindVersion
//  2. Install path (~/.opentaint/install/lib/) — only if version matches bindVersion
//  3. Cache path (~/.opentaint/<cacheName>)
// When no tier exists yet, it returns the last tier as the default download target.
func resolveArtifactTier(def globals.ArtifactDef) (string, string, error) {
	tiers, err := ArtifactTiers(def)
	if err != nil {
		return "", "", err
	}
	if found := FindExisting(CurrentTiers(tiers, IsInstallCurrent())); found != nil {
		return found.Name, found.Path, nil
	}
	last := tiers[len(tiers)-1]
	return last.Name, last.Path, nil
}

// resolveArtifactPath resolves the path for an artifact. See resolveArtifactTier.
func resolveArtifactPath(def globals.ArtifactDef) (string, error) {
	_, path, err := resolveArtifactTier(def)
	return path, err
}

func GetAutobuilderJarPath(version string) (string, error) {
	return resolveArtifactPath(globals.ArtifactByKind("autobuilder").WithVersion(version))
}

func GetAnalyzerJarPath(version string) (string, error) {
	return resolveArtifactPath(globals.ArtifactByKind("analyzer").WithVersion(version))
}

func GetRulesPath(version string) (string, error) {
	return resolveArtifactPath(globals.ArtifactByKind("rules").WithVersion(version))
}
