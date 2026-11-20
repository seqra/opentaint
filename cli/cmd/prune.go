package cmd

import (
	"fmt"
	"os"
	"slices"

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
	pruneListAll   bool
)

// resolveCategories maps CLI flags to a PruneCategory bitmask.
// Returns an error if --all is combined with specific flags.
func resolveCategories() (utils.PruneCategory, error) {
	specific := pruneArtifacts || pruneRules || pruneJDK || pruneModels || pruneLogs || pruneInstall
	if pruneAll && specific {
		return 0, fmt.Errorf("cannot use --all with --artifacts, --rules, --jdk, --models, --logs, or --install")
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
	Short: "Remove old component versions, cached project models, and logs",
	Long:  "Remove old component versions, cached project models, and logs from `~/.opentaint`.",
	Example: `  # Remove old component versions and cached project models
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
			fail("Failed to find the prune lock", err)
		}
		pruneLock, err := utils.TryLockExclusive(pruneLockPath, utils.LockMeta{
			PID:     os.Getpid(),
			Command: "prune",
		})
		if err == utils.ErrLocked {
			fail("Another prune is running", nil)
		}
		if err != nil {
			fail("Failed to take the prune lock", err)
		}
		defer pruneLock.Unlock()

		result, err := utils.ScanForStaleArtifacts(categories)
		if err != nil {
			fail("Failed to find stale artifacts", err)
		}

		warnSkipped(result.Skipped)

		if result.TotalCount == 0 {
			out.Print("No stale artifacts found")
			return
		}

		printStaleArtifacts(result)

		if pruneDryRun {
			out.Blank()
			out.Print("Dry run complete. No files were deleted.")
			suggest("To delete these artifacts, run:", withFlag(rerunWithoutDryRun(), "--yes"))
			return
		}

		if !pruneYes {
			if !out.Confirm("Delete these artifacts?", false) {
				out.Print("Prune cancelled")
				return
			}
		}

		if err := utils.DeleteArtifacts(result.Stale); err != nil {
			fail("Failed to delete the artifacts", err)
		}

		out.Successf("Pruned %s, freed %s", itemCount(result.TotalCount), output.FormatSize(result.TotalSize))
		if pruneInstall || pruneAll {
			suggest("To restore the removed components, run:", "opentaint pull")
		}
	},
}

// pruneListLimit is the number of paths listed in each category without --list-all.
const pruneListLimit = 20

// pruneGroups are the categories of stale artifacts in the output, with the kinds in each.
var pruneGroups = []struct {
	title string
	kinds []string
}{
	{"Analyzer and autobuilder", []string{utils.StaleKindAnalyzer, utils.StaleKindAutobuilder}},
	{"Built-in ruleset", []string{utils.StaleKindRules}},
	{"JDK and JRE", []string{utils.StaleKindJDK, utils.StaleKindJRE}},
	{"Cached project models", []string{utils.StaleKindModel}},
	{"Project logs", []string{utils.StaleKindLog}},
	{"Installed components", []string{utils.StaleKindInstallLib, utils.StaleKindInstallJRE}},
}

// warnSkipped names the cached project models that prune left alone because another command
// holds their lock: a compile, which records its PID, or a scan.
func warnSkipped(skipped []utils.SkippedProject) {
	if len(skipped) == 0 {
		return
	}
	models := "cached project models"
	if len(skipped) == 1 {
		models = "cached project model"
	}
	paths := make([]string, len(skipped))
	for i, s := range skipped {
		paths[i] = s.Path
		if s.Meta.PID != 0 {
			paths[i] += fmt.Sprintf(" (PID %d)", s.Meta.PID)
		}
	}
	out.WarnDetails(fmt.Sprintf("Skipped %d %s that another process is using", len(skipped), models), paths...)
	out.Blank()
}

// printStaleArtifacts prints the artifacts grouped by category, with the first pruneListLimit
// paths of each category, or all of them with --list-all.
func printStaleArtifacts(result *utils.PruneResult) {
	sb := out.Section("Stale Artifacts")
	for _, group := range pruneGroups {
		var artifacts []utils.StaleArtifact
		var size int64
		for _, artifact := range result.Stale {
			if slices.Contains(group.kinds, artifact.Kind) {
				artifacts = append(artifacts, artifact)
				size += artifact.Size
			}
		}
		if len(artifacts) == 0 {
			continue
		}
		shown := artifacts
		if !pruneListAll && len(shown) > pruneListLimit {
			shown = shown[:pruneListLimit]
		}
		var lines []any
		for _, artifact := range shown {
			lines = append(lines, fmt.Sprintf("%s - %s", artifact.Path, output.FormatSize(artifact.Size)))
		}
		if hidden := len(artifacts) - len(shown); hidden > 0 {
			lines = append(lines, fmt.Sprintf("... and %d more", hidden))
		}
		sb.Child(out.GroupItem(out.FieldItem(group.title, itemsAndSize(len(artifacts), size)), lines...))
	}
	sb.Line().
		Field("Total", itemsAndSize(result.TotalCount, result.TotalSize)).
		Render()
}

// itemsAndSize formats a number of artifacts and their size: "17 items, 5.6 GB".
func itemsAndSize(count int, size int64) string {
	return itemCount(count) + ", " + output.FormatSize(size)
}

func itemCount(count int) string {
	if count == 1 {
		return "1 item"
	}
	return fmt.Sprintf("%d items", count)
}

func init() {
	rootCmd.AddCommand(pruneCmd)

	pruneCmd.Flags().BoolVar(&pruneDryRun, "dry-run", false, "Show what would be deleted without deleting")
	pruneCmd.Flags().BoolVar(&pruneYes, "yes", false, "Skip the confirmation prompt")
	pruneCmd.Flags().BoolVar(&pruneAll, "all", false, "Prune all categories")
	pruneCmd.Flags().BoolVar(&pruneArtifacts, "artifacts", false, "Prune old analyzer and autobuilder versions")
	pruneCmd.Flags().BoolVar(&pruneRules, "rules", false, "Prune old built-in ruleset versions")
	pruneCmd.Flags().BoolVar(&pruneJDK, "jdk", false, "Prune old JDK and JRE versions")
	pruneCmd.Flags().BoolVar(&pruneModels, "models", false, "Prune cached project models")
	pruneCmd.Flags().BoolVar(&pruneLogs, "logs", false, "Prune project log files")
	pruneCmd.Flags().BoolVar(&pruneInstall, "install", false, "Prune the components in ~/.opentaint/install")
	pruneCmd.Flags().BoolVar(&pruneListAll, "list-all", false, "List every path, not only the first 20 of each category")
}
