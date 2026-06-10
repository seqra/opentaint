package cmd

import (
	"errors"
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils"
)

func ensureArtifactJar(def globals.ArtifactDef) (string, error) {
	path, err := utils.ResolveJarPath(def)
	if err != nil {
		return "", fmt.Errorf("failed to construct path to the %s: %w", def.Kind(), err)
	}
	if def.Override != "" {
		return path, nil
	}

	if err := ensureArtifactAvailable(def.Kind(), def.Version, path, func() error {
		return utils.DownloadGithubReleaseAsset(globals.Config.Owner, globals.Config.Repo, def.Version, def.AssetName, path, globals.Config.Github.Token, globals.Config.SkipVerify, out)
	}); err != nil {
		return "", err
	}
	return path, nil
}

func ensureAnalyzerAvailable() (string, error) {
	return ensureArtifactJar(globals.ArtifactByKind("analyzer"))
}

func ensureAutobuilderAvailable() (string, error) {
	return ensureArtifactJar(globals.ArtifactByKind("autobuilder"))
}

func ensureArtifactAvailable(name, version, artifactPath string, download func() error) error {
	if _, err := os.Stat(artifactPath); err == nil {
		return nil
	} else if !errors.Is(err, os.ErrNotExist) {
		return fmt.Errorf("failed to check %s at %s: %w", name, artifactPath, err)
	}

	if !out.IsInteractive() {
		out.Blank()
		if version == "" {
			out.Printf("Downloading %s", name)
		} else {
			out.Printf("Downloading %s version %s", name, version)
		}
	}

	if err := download(); err != nil {
		return fmt.Errorf("failed to download %s: %w", name, err)
	}

	if !out.IsInteractive() {
		out.Printf("Successfully downloaded %s to %s", name, artifactPath)
	}

	return nil
}
