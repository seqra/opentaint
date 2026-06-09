package utils

import (
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
)

// EnsureRulesPath returns the on-disk path to the built-in rules for the
// configured version, downloading and unpacking them if they are not already
// present. The path is returned even when the download fails, so callers can
// still report where the rules were expected.
func EnsureRulesPath(printer *output.Printer) (string, error) {
	path, err := GetRulesPath(globals.Config.Rules.Version)
	if err != nil {
		return "", err
	}
	if PathExists(path) {
		return path, nil
	}
	if err := DownloadAndUnpackGithubReleaseAsset(
		globals.Config.Owner, globals.Config.Repo,
		globals.Config.Rules.Version, globals.RulesAssetName,
		path, globals.Config.Github.Token, globals.Config.SkipVerify, printer,
	); err != nil {
		return path, err
	}
	return path, nil
}
