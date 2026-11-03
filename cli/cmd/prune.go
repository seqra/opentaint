package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/spf13/cobra"
)

var (
	pruneDryRun    bool
	pruneYes       bool
	pruneAll       bool
	pruneArtifacts bool
	pruneRules     bool
	pruneJDK       bool
	pruneModels    bool
	pruneLogs      bool
	pruneInstall   bool
)

// resolveCategories maps CLI flags to a PruneCategory bitmask.
// Returns an error if --all is combined with specific flags.
func resolveCategories() (utils.PruneCategory, error) {
	specific := pruneArtifacts || pruneRules || pruneJDK || pruneModels || pruneLogs || pruneInstall
	if pruneAll && specific {
		return 0, fmt.Errorf("--all cannot be combined with specific category flags (--artifacts, --rules, --jdk, --models, --logs, --install)")
	}
	if pruneAll {
		return utils.PruneCategoriesAll, nil
	}
	if !specific {
		return utils.PruneCategoriesDefault, nil
	}

	flagMap := []struct {
		flag *bool
		cat  utils.PruneCategory
	}{
		{&pruneArtifacts, utils.PruneCategoryArtifacts},
		{&pruneRules, utils.PruneCategoryRules},
		{&pruneJDK, utils.PruneCategoryJDK},
		{&pruneModels, utils.PruneCategoryModels},
		{&pruneLogs, utils.PruneCategoryLogs},
		{&pruneInstall, utils.PruneCategoryInstall},
	}
	var cats utils.PruneCategory
	for _, f := range flagMap {
		if *f.flag {
			cats |= f.cat
		}
	}
	return cats, nil
}

var pruneCmd = &cobra.Command{
	Use:   "prune",
	Short: "Remove stale downloads, cached project models, and logs",
	Long:  "Remove stale downloads, cached project models, and logs from `~/.opentaint`.",
	Example: `  # Remove stale downloads and cached project models
  opentaint prune

  # Remove everything, including the logs and the installed components
  opentaint prune --all`,
	Run: func(cmd *cobra.Command, args []string) {
		categories, err := resolveCategories()
		if err != nil {
			out.FatalErr(err)
		}

		// Acquire global prune lock
		pruneLockPath, err := utils.PruneLockPath()
		if err != nil {
			failf("Failed to resolve prune lock path: %s", err)
		}
		pruneLock, err := utils.TryLockExclusive(pruneLockPath, utils.LockMeta{
			PID:     os.Getpid(),
			Command: "prune",
		})
		if err == utils.ErrLocked {
			failWith(1, "Another prune is already running")
		}
		if err != nil {
			failf("Failed to acquire prune lock: %s", err)
		}
		defer pruneLock.Unlock()

		result, err := utils.ScanForStaleArtifacts(categories)
		if err != nil {
			failf("Failed to scan for stale artifacts: %s", err)
		}

		// Display skipped projects
		if len(result.Skipped) > 0 {
			sb := out.Section("Skipped (compilation in progress)")
			for _, s := range result.Skipped {
				if s.Meta.PID != 0 {
					sb.Text(fmt.Sprintf("%s (locked by PID %d)", s.Path, s.Meta.PID))
				} else {
					sb.Text(fmt.Sprintf("%s (locked)", s.Path))
				}
			}
			sb.Render()
		}

		if result.TotalCount == 0 {
			out.Print("No stale artifacts found. Nothing to prune.")
			return
		}

		sb := out.Section("Stale Artifacts")
		for _, artifact := range result.Stale {
			sb.Text(fmt.Sprintf("%s (%s) - %s", artifact.Path, artifact.Kind, output.FormatSize(artifact.Size)))
		}
		sb.Line().
			Text(fmt.Sprintf("Total: %d items, %s", result.TotalCount, output.FormatSize(result.TotalSize))).
			Render()

		if pruneDryRun {
			out.Print("Dry run complete. No files were deleted.")
			suggest("To delete these artifacts, run:", withFlag(rerunWithoutDryRun(), "--yes"))
			return
		}

		if !pruneYes {
			if !out.Confirm("Delete these artifacts?", false) {
				out.Print("Prune cancelled.")
				suggest("To prune without confirming, run:", withFlag(rerunWithoutDryRun(), "--yes"))
				return
			}
		}

		if err := utils.DeleteArtifacts(result.Stale); err != nil {
			failf("Failed to delete artifacts: %s", err)
		}

		out.Successf("Pruned %d items, freed %s", result.TotalCount, output.FormatSize(result.TotalSize))
		if pruneInstall || pruneAll {
			suggest("To restore the removed components, run:", "opentaint pull")
		}
	},
}

func init() {
	rootCmd.AddCommand(pruneCmd)

	pruneCmd.Flags().BoolVar(&pruneDryRun, "dry-run", false, "Show what would be deleted without deleting")
	pruneCmd.Flags().BoolVar(&pruneYes, "yes", false, "Skip the confirmation prompt")
	pruneCmd.Flags().BoolVar(&pruneAll, "all", false, "Prune all categories")
	pruneCmd.Flags().BoolVar(&pruneArtifacts, "artifacts", false, "Prune stale analyzer and autobuilder downloads")
	pruneCmd.Flags().BoolVar(&pruneRules, "rules", false, "Prune stale rules downloads")
	pruneCmd.Flags().BoolVar(&pruneJDK, "jdk", false, "Prune stale JDK and JRE downloads")
	pruneCmd.Flags().BoolVar(&pruneModels, "models", false, "Prune cached project models")
	pruneCmd.Flags().BoolVar(&pruneLogs, "logs", false, "Prune project log files")
	pruneCmd.Flags().BoolVar(&pruneInstall, "install", false, "Prune the components in ~/.opentaint/install")
}
