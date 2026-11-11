// Package autobuilder reads autobuilder output.
package autobuilder

import (
	"os"
	"regexp"
	"strings"
)

// logLineSeparator precedes the build-tool output in an autobuilder log line.
const logLineSeparator = " - "

// compilerErrorCount matches a javac error summary.
var compilerErrorCount = regexp.MustCompile(`^\d+ errors?$`)

// CompilerDiagnostics returns compiler errors from an autobuilder log.
// It returns an empty string if the log has no compiler error.
func CompilerDiagnostics(logPath string) string {
	log, err := os.ReadFile(logPath)
	if err != nil {
		return ""
	}

	var diagnostics []string
	// Gradle repeats the compiler output in its failure summary and in the stack trace, so
	// each line is kept once.
	seen := make(map[string]bool)
	add := func(message string) {
		if !seen[message] {
			seen[message] = true
			diagnostics = append(diagnostics, "  "+message)
		}
	}
	for _, line := range strings.Split(string(log), "\n") {
		message := strings.TrimSpace(buildOutput(line))
		switch {
		case isCompilerDiagnostic(message):
			add(message)
		case len(diagnostics) > 0 && compilerErrorCount.MatchString(message):
			// javac closes with a count of what it just reported. On its own the line is
			// only something that reads like one, so it is kept as a trailer and never as
			// the diagnostic.
			add(message)
		}
	}
	return strings.Join(diagnostics, "\n")
}

func buildOutput(logLine string) string {
	message := logLine
	if _, after, found := strings.Cut(logLine, logLineSeparator); found {
		message = after
	}
	return strings.TrimRight(message, "\r")
}

func isCompilerDiagnostic(message string) bool {
	// Match javac and kotlinc error formats.
	return strings.Contains(message, ": error: ") || strings.HasPrefix(message, "e: ")
}

// BuildFailure returns what Gradle reports under "What went wrong" in an autobuilder log. It is
// the cause of a build that failed before the compiler reported anything, such as a dependency
// that can not be resolved.
func BuildFailure(logPath string) string {
	log, err := os.ReadFile(logPath)
	if err != nil {
		return ""
	}

	var failure []string
	inside := false
	for _, line := range strings.Split(string(log), "\n") {
		message := strings.TrimRight(buildOutput(line), " \t")
		if !inside {
			inside = message == "* What went wrong:"
			continue
		}
		if strings.TrimSpace(message) == "" || strings.HasPrefix(message, "* ") {
			break
		}
		failure = append(failure, "  "+message)
	}
	return strings.Join(failure, "\n")
}
