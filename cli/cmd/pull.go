package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"

	"charm.land/lipgloss/v2/tree"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
	"github.com/spf13/cobra"
)

var pullCmd = &cobra.Command{
	Use:   "pull",
	Short: "Download the analysis toolchain and Java runtime",
	Long: `Download the toolchain into the local cache. The toolchain contains the analyzer, the autobuilder, the built-in rules, the go-ssa-server, and a Java runtime. After the download, OpenTaint can build and scan projects without network access.

If a release archive supplied bundled artifacts, OpenTaint uses them. They are not downloaded again.

Run "opentaint pull" one time before your first scan. To remove old downloads, use "opentaint prune".`,
	Example: `  # Download the toolchain before the first scan
  opentaint pull

  # Download a different Java runtime version
  opentaint pull --java-version 17

  # Recipe: prepare a machine that will have no network access
  opentaint pull
  opentaint health`,
	Run: func(cmd *cobra.Command, args []string) {
		out.Section("OpenTaint Pull").
			Field("Autobuilder", globals.Config.Autobuilder.Version).
			Field("Analyzer", globals.Config.Analyzer.Version).
			Field("Rules", globals.Config.Rules.Version).
			Field("GoServer", globals.Config.GoServer.Version).
			Field("Java", globals.Config.Java.Version).
			Render()

		installNextToBinary := true

		// Clean stale install-tier artifacts before downloading
		installCurrent := utils.IsInstallCurrent()
		if !installCurrent {
			if err := utils.CleanInstallDir(); err != nil {
				failf("Failed to clean install directory: %s", err)
			}
		}

		artifacts := globals.Artifacts()

		var summaryNodes []any
		for _, spec := range artifacts {
			node, err := downloadArtifact(spec, installNextToBinary, installCurrent)
			if err != nil {
				failf("Failed to download %s: %s", spec.Kind(), err)
			}
			summaryNodes = append(summaryNodes, node)
		}

		javaNode, err := downloadJava(installNextToBinary, installCurrent)
		if err != nil {
			failf("Failed to download Java: %s", err)
		}
		summaryNodes = append(summaryNodes, javaNode)

		// Write version marker after all downloads succeed
		if err := utils.WriteInstallVersionMarker(); err != nil {
			failf("Failed to write install version marker: %s", err)
		}

		out.Blank()
		out.Section("Pull Summary").
			Child(summaryNodes...).
			Render()

		out.Successf("Pull completed.")
		suggest("To scan your project, run:", "opentaint scan .")
	},
}

func downloadArtifact(spec globals.ArtifactDef, installNextToBinary, installCurrent bool) (*tree.Tree, error) {
	node := out.GroupItem(fmt.Sprintf("%s %s", spec.Name, spec.Version))

	if spec.Override != "" {
		node.Child(fmt.Sprintf("Config override active: scans use %s", spec.Override))
	}

	tiers, err := utils.ArtifactTiers(spec)
	if err != nil {
		return node, err
	}

	if found := utils.FindExisting(utils.CurrentTiers(tiers, installCurrent)); found != nil {
		if found.Name == utils.TierBundled {
			node.Child("Using bundled artifact")
		} else {
			node.Child("Already downloaded")
		}
		return node, nil
	}

	download := func(targetPath string) error {
		if spec.Unpack {
			return utils.DownloadAndUnpackGithubReleaseAsset(globals.Config.Owner, spec.RepoName, spec.Version, spec.AssetName, targetPath, globals.Config.Github.Token, globals.Config.SkipVerify, out)
		}
		return utils.DownloadGithubReleaseAsset(globals.Config.Owner, spec.RepoName, spec.Version, spec.AssetName, targetPath, globals.Config.Github.Token, globals.Config.SkipVerify, out)
	}

	for _, t := range tiers {
		if t.Name == utils.TierBundled && !installNextToBinary {
			continue
		}
		if t.Name != utils.TierCache {
			if err := os.MkdirAll(filepath.Dir(t.Path), 0o755); err != nil {
				output.LogDebugf("Cannot write to %s tier, trying next", t.Name)
				continue
			}
		}
		if err := download(t.Path); err != nil {
			return node, err
		}
		// go-ssa-server is a single native binary and must be executable on unix.
		if spec.Kind() == "goserver" && runtime.GOOS != "windows" {
			if err := os.Chmod(t.Path, 0o755); err != nil {
				return node, fmt.Errorf("failed to mark %s executable: %w", spec.Kind(), err)
			}
		}
		node.Child(fmt.Sprintf("Downloaded to %s", t.Path))
		return node, nil
	}

	return node, fmt.Errorf("no writable location found for %s", spec.Kind())
}

func downloadJava(installNextToBinary, installCurrent bool) (*tree.Tree, error) {
	javaVersion := globals.Config.Java.Version
	node := out.GroupItem(fmt.Sprintf("Java %d", javaVersion))

	if javaVersion < 8 || javaVersion > 25 {
		return node, fmt.Errorf("unsupported Java version: %d (supported range: 8-25)", javaVersion)
	}

	opentaintHome, err := utils.GetOpenTaintHome()
	if err != nil {
		return node, err
	}
	adoptiumOS, adoptiumArch, err := java.MapPlatformToAdoptium(runtime.GOOS, runtime.GOARCH)
	if err != nil {
		return node, err
	}
	cacheDir := filepath.Join(opentaintHome, "jre", fmt.Sprintf("temurin-%d-jre-%s-%s", javaVersion, adoptiumOS, adoptiumArch))

	tiers := utils.JRETiers(javaVersion, cacheDir)

	if found := utils.FindExistingJRE(utils.CurrentTiers(tiers, installCurrent)); found != nil {
		if found.Name == utils.TierBundled {
			node.Child("Using bundled JRE")
		} else {
			node.Child("Already downloaded")
		}
		return node, nil
	}

	for _, t := range tiers {
		if t.Name == utils.TierBundled && !installNextToBinary {
			continue
		}
		if t.Name != utils.TierCache {
			if err := os.MkdirAll(t.Path, 0o755); err != nil {
				output.LogDebugf("Cannot write to %s tier, trying next", t.Name)
				continue
			}
			_ = os.Remove(t.Path)
		}
		javaPath, err := java.EnsureLocalRuntimeAt(javaVersion, java.AdoptiumImageJRE, t.Path, runtime.GOOS, runtime.GOARCH, globals.Config.SkipVerify, out)
		if err != nil {
			return node, err
		}
		node.Child(fmt.Sprintf("Downloaded to %s", javaPath))
		return node, nil
	}

	return node, fmt.Errorf("no writable location found for Java %d", javaVersion)
}

func init() {
	rootCmd.AddCommand(pullCmd)
}
