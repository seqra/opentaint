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

func runDryRun(skippedAction string) {
	out.Printf("Dry run complete. Inputs validated, %s skipped.", skippedAction)
	suggest("To run for real, run:", rerunWithoutDryRun())
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
