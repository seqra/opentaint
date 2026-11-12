package cmd

import (
	"os"
	"strings"

	"github.com/seqra/opentaint/internal/utils"
)

// runDryRun ends a dry run: skippedAction is what the run did not do, and goal is what the same
// command does without --dry-run, as in "To <goal>, run:".
func runDryRun(skippedAction, goal string) {
	out.Printf("Dry run complete. Inputs validated, %s skipped.", skippedAction)
	suggest("To "+goal+", run:", rerunWithoutDryRun())
}

func rerunWithoutDryRun() string {
	args := []string{"opentaint"}
	for _, arg := range os.Args[1:] {
		if arg == "--dry-run" || strings.HasPrefix(arg, "--dry-run=") {
			continue
		}
		args = append(args, shellQuote(arg))
	}
	return strings.Join(args, " ")
}

// shellQuote quotes arg so that a command in a next step works when it is pasted.
func shellQuote(arg string) string {
	return utils.ShellQuote(arg)
}
