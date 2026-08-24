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
// a shell. Only arguments made of known-inert characters pass through
// unchanged, so globs, variables, and separators survive the round trip.
func shellQuote(arg string) string {
	if arg != "" && !strings.ContainsFunc(arg, shellUnsafe) {
		return arg
	}
	return "'" + strings.ReplaceAll(arg, "'", `'\''`) + "'"
}

// shellUnsafe reports whether a character can change the meaning of an
// unquoted shell word. The safe set mirrors Python's shlex.quote.
func shellUnsafe(r rune) bool {
	switch {
	case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9':
		return false
	case strings.ContainsRune("_@%+=:,./-", r):
		return false
	}
	return true
}
