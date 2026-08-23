package cmd

import (
	"os"
	"strings"
)

func failOnInvalidInputs(validate func() error) {
	if err := validate(); err != nil {
		out.Fatalf("Input validation failed: %s", err)
	}
}

// runDryRun prints the standard dry-run tail: a status line naming the skipped
// action, then a suggestion to repeat the same invocation without --dry-run.
func runDryRun(skippedAction string) {
	out.Printf("Dry run complete. Inputs validated, %s skipped.", skippedAction)
	suggest("To run for real, run:", rerunWithoutDryRun())
}

// rerunWithoutDryRun reconstructs the current invocation with the --dry-run
// flag removed, so the dry-run tail can suggest the real run verbatim. It works
// from os.Args, which keeps it correct for every command that shares this tail
// (scan, compile, project, test rule reachability).
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

// shellQuote single-quotes an argument that would break when copy-pasted into
// a shell (spaces, quotes). Plain arguments pass through unchanged.
func shellQuote(arg string) string {
	if arg != "" && !strings.ContainsAny(arg, " \t'\"") {
		return arg
	}
	return "'" + strings.ReplaceAll(arg, "'", `'\''`) + "'"
}
