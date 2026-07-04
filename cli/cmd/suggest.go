package cmd

import (
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
)

func suggest(description, command string) {
	out.Suggest(description, command)
}

// withFlag appends flag to the command string when it is not already present,
// for suggestions that re-run the current invocation with one extra flag.
func withFlag(command, flag string) string {
	if strings.Contains(command, flag) {
		return command
	}
	return command + " " + flag
}

// retrySuggestion builds the "re-run with more resources" hint for a resource
// analyzer failure. The second result is false for exit codes where a plain
// retry would not help (unhandled exception, configuration error).
func retrySuggestion(exitCode int, timeout time.Duration, maxMemory string) (output.Suggestion, bool) {
	switch exitCode {
	case analyzer.ExitOOM:
		return output.Suggestion{
			Description: "To retry with more memory, run:",
			Command:     rerunReplacingFlag(doubleMemory(maxMemory), "--max-memory"),
		}, true
	case analyzer.ExitTimeout:
		return output.Suggestion{
			Description: "To retry with a longer timeout, run:",
			Command:     rerunReplacingFlag((timeout * 2).String(), "--timeout", "-t"),
		}, true
	}
	return output.Suggestion{}, false
}

// rerunReplacingFlag reconstructs the current invocation with the named flag
// (any alias, in both "--flag value" and "--flag=value" forms) replaced by the
// given value, appended as names[0].
func rerunReplacingFlag(value string, names ...string) string {
	args := []string{"opentaint"}
	skipNext := false
	for _, arg := range os.Args[1:] {
		if skipNext {
			skipNext = false
			continue
		}
		matched := false
		for _, name := range names {
			if arg == name {
				matched = true
				skipNext = true
				break
			}
			if strings.HasPrefix(arg, name+"=") {
				matched = true
				break
			}
		}
		if matched {
			continue
		}
		args = append(args, shellQuote(arg))
	}
	args = append(args, names[0], shellQuote(value))
	return strings.Join(args, " ")
}

// doubleMemory doubles a memory value like 8G or 1024m, falling back to the
// runtime failure message's own 16G example when the value does not parse.
func doubleMemory(value string) string {
	digits := 0
	for digits < len(value) && value[digits] >= '0' && value[digits] <= '9' {
		digits++
	}
	suffix := value[digits:]
	if digits == 0 || len(suffix) > 1 {
		return "16G"
	}
	n, err := strconv.ParseInt(value[:digits], 10, 64)
	if err != nil {
		return "16G"
	}
	return fmt.Sprintf("%d%s", n*2, suffix)
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
