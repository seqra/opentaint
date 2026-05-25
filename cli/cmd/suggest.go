package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
)

func suggest(description, command string) {
	out.Suggest(description, command)
}

// logSuggestion returns a Suggestion pointing at the active log file. The
// second result is false when no log file is active (e.g. failures that occur
// before logging is activated), in which case callers omit it.
func logSuggestion() (output.Suggestion, bool) {
	if globals.LogPath == "" {
		return output.Suggestion{}, false
	}
	return output.Suggestion{
		Description: "For full details, check the log file:",
		Command:     globals.LogPath,
	}, true
}

// buildFailSuggestions returns a pointer to the log file (when one exists)
// followed by the contextual hints. The log pointer leads so the user always
// sees where to look for full details first. Building onto a fresh slice avoids
// mutating a caller's backing array when contextual is passed via the spread form.
func buildFailSuggestions(contextual []output.Suggestion) []output.Suggestion {
	var suggestions []output.Suggestion
	if logSug, ok := logSuggestion(); ok {
		suggestions = append(suggestions, logSug)
	}
	return append(suggestions, contextual...)
}

// failWith prints an error message, renders a single Suggestions block leading
// with a pointer to the log file (when one exists) followed by any contextual
// hints, then exits the process with the given code.
func failWith(code int, message string, contextual ...output.Suggestion) {
	out.Error(message)
	out.Suggestions(buildFailSuggestions(contextual)...)
	os.Exit(code)
}

// failf formats an error message and fails with exit code 1 and no contextual
// suggestion. The log-file pointer is still added when a log file exists.
func failf(format string, args ...any) {
	failWith(1, fmt.Sprintf(format, args...))
}
