package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/version"
	"github.com/spf13/cobra"
)

var (
	updateCheck bool
	updateYes   bool
)

var updateCmd = &cobra.Command{
	Use:   "update [version]",
	Short: "Update opentaint to the latest version",
	Long: `Update the opentaint binary in place to the latest release, or to the optional version argument. Only upgrades are supported; downgrading to an older version is refused.

Homebrew and npm installations print the matching package-manager command instead of updating in place. Pass --check to report the latest version without downloading, or --yes to skip the confirmation prompt.

After a successful update, remove superseded artifacts with opentaint prune.`,
	Example: `  # Update to the latest release
  opentaint update

  # Check for a newer version without installing
  opentaint update --check

  # Update to a specific version without prompting
  opentaint update 1.2.3 --yes`,
	Args: cobra.MaximumNArgs(1),
	Run: func(cmd *cobra.Command, args []string) {
		// Check installation method first
		method, exePath := utils.DetectInstallMethod()

		switch method {
		case utils.InstallMethodHomebrew:
			out.Print("opentaint was installed via Homebrew.")
			suggest("To update, run:", "brew upgrade --cask opentaint")
			return
		case utils.InstallMethodNpm:
			out.Print("opentaint was installed via npm.")
			suggest("To update, run:", "npm install -g @seqra/opentaint@latest")
			return
		}

		currentVersion := version.GetVersion()
		if currentVersion == "dev" || currentVersion == "" {
			out.Warn("Cannot determine current version. Update is not supported for development builds.")
			return
		}

		// Determine target version
		var targetVersion, targetTag string
		var err error

		if len(args) > 0 {
			targetVersion = args[0]
			if strings.HasPrefix(targetVersion, "v") {
				targetTag = targetVersion
				targetVersion = targetVersion[1:]
			} else {
				targetTag = "v" + targetVersion
			}
		} else {
			out.Print("Checking for updates...")
			targetVersion, targetTag, err = utils.GetLatestRelease(globals.Config.Owner, globals.Config.Repo, globals.Config.Github.Token)
			if err != nil {
				out.Fatalf("Failed to check for updates: %s", err)
			}
		}

		// Compare versions
		cmp, err := version.CompareVersions(currentVersion, targetVersion)
		if err != nil {
			out.Warnf("Could not compare versions: %s", err)
			out.Printf("Current: %s, Latest: %s", currentVersion, targetVersion)
			if !updateYes {
				suggest("To proceed anyway, run:", withFlag(rerunWithoutDryRun(), "--yes"))
				return
			}
		}

		if cmp == 0 {
			out.Printf("opentaint is already up to date (v%s).", currentVersion)
			return
		}

		if cmp > 0 {
			out.Warnf("Target version v%s is older than current version v%s. Downgrading is not supported.", targetVersion, currentVersion)
			return
		}

		if updateCheck {
			out.Section("Update Available").
				Field("Current version", fmt.Sprintf("v%s", currentVersion)).
				Field("Latest version", fmt.Sprintf("v%s", targetVersion)).
				Render()
			suggest("To update, run:", "opentaint update")
			return
		}

		out.Section("OpenTaint Update").
			Text(fmt.Sprintf("Updating v%s -> v%s", currentVersion, targetVersion)).
			Render()

		if !updateYes {
			if !out.Confirm("Proceed with update?", false) {
				out.Print("Update cancelled.")
				suggest("To update without confirming, run:", "opentaint update --yes")
				return
			}
		}

		// Download the release archive
		tmpDir, err := os.MkdirTemp("", "opentaint-update-*")
		if err != nil {
			out.Fatalf("Failed to create temp directory: %s", err)
		}
		defer func() { _ = os.RemoveAll(tmpDir) }()

		out.Print("Downloading...")
		archivePath, err := utils.DownloadReleaseArchive(globals.Config.Owner, globals.Config.Repo, targetTag, globals.Config.Github.Token, tmpDir, globals.Config.SkipVerify, out)
		if err != nil {
			out.Fatalf("Failed to download release: %s", err)
		}

		// Perform self-update
		installDir := filepath.Dir(exePath)
		out.Print("Installing...")
		if err := utils.SelfUpdate(archivePath, installDir); err != nil {
			out.Fatalf("Failed to update: %s", err)
		}

		out.Successf("Successfully updated to v%s", targetVersion)
		suggest("To clean up old artifacts, run:", "opentaint prune")
	},
}

func init() {
	rootCmd.AddCommand(updateCmd)

	updateCmd.Flags().BoolVar(&updateCheck, "check", false, "Check for updates without downloading")
	updateCmd.Flags().BoolVar(&updateYes, "yes", false, "Skip confirmation prompt")
}
