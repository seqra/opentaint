package utils

import (
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
)

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
