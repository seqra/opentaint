package cmd

import (
	"fmt"
	"os"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
)

// dockerFallbackHintPrefix is the shared lead-in for the Docker-based fallback
// hints emitted when native compilation can't find a suitable Java. compile and
// scan complete it with their respective "compilation:" / "scan:" suffix.
const dockerFallbackHintPrefix = "If native compilation fails due to missing required Java, set JAVA_HOME according to the project's requirements or try Docker-based "

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

// appendLogSuggestion appends the log-file pointer to s when a log file is
// active and returns s unchanged otherwise. It centralizes the "lead with the
// log" idiom shared by buildFailSuggestions and the scan summary tail.
func appendLogSuggestion(s []output.Suggestion) []output.Suggestion {
	if logSug, ok := logSuggestion(); ok {
		return append(s, logSug)
	}
	return s
}

// buildFailSuggestions returns a pointer to the log file (when one exists)
// followed by the contextual hints. The log pointer leads so the user always
// sees where to look for full details first. Building onto a fresh slice avoids
// mutating a caller's backing array when contextual is passed via the spread form.
func buildFailSuggestions(contextual []output.Suggestion) []output.Suggestion {
	return append(appendLogSuggestion(nil), contextual...)
}

// failWith prints an error message, renders a single Suggestions block leading
// with a pointer to the log file (when one exists) followed by any contextual
// hints, then exits the process with the given code. Use it for operational
// compile/scan failures; pure input/argument errors stay on out.Fatalf with
// their own usage hints.
func failWith(code int, message string, contextual ...output.Suggestion) {
	out.Error(message)
	out.Suggestions(buildFailSuggestions(contextual)...)
	os.Exit(code)
}

// failf formats an error message and fails with exit code 1 and no contextual
// suggestion. The log-file pointer is still added when a log file exists. Use
// it as the drop-in for bare out.Fatalf at operational compile/scan failure
// sites; see failWith.
func failf(format string, args ...any) {
	failWith(1, fmt.Sprintf(format, args...))
}
