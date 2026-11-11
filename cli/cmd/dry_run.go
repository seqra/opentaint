package cmd

import (
	"os"
	"strings"
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

func shellQuote(arg string) string {
	if arg != "" && !strings.ContainsFunc(arg, shellUnsafe) {
		return arg
	}
	return "'" + strings.ReplaceAll(arg, "'", `'\''`) + "'"
}

func shellUnsafe(r rune) bool {
	switch {
	case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9':
		return false
	case strings.ContainsRune("_@%+=:,./-", r):
		return false
	}
	return true
}
