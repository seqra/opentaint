package cmd

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"github.com/seqra/opentaint/internal/analyzer"
	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
)

func suggest(description, command string) {
	out.Suggest(description, command)
}

const (
	maxRetryMemory  = 16
	maxRetryTimeout = 15 * time.Minute
)

func withFlag(command, flag string) string {
	for _, token := range strings.Fields(command) {
		if token == flag || strings.HasPrefix(token, flag+"=") {
			return command
		}
	}
	return command + " " + flag
}

func retrySuggestion(exitCode int, timeout time.Duration, maxMemory string) (output.Suggestion, bool) {
	switch exitCode {
	case analyzer.ExitOOM:
		if memoryGib(maxMemory) >= maxRetryMemory {
			return output.Suggestion{}, false
		}
		next := doubleMemory(maxMemory)
		return output.Suggestion{
			Description: "To retry with more memory, run:",
			Command:     rerunReplacingFlag(next, "--max-memory"),
		}, true
	case analyzer.ExitTimeout:
		// Past the default timeout, a longer one rarely helps: suggest it with no command.
		if timeout >= maxRetryTimeout {
			return output.Suggestion{Description: "To give the analysis more time, use a longer --timeout"}, true
		}
		next := timeout * 2
		if next <= timeout || next > maxRetryTimeout {
			next = maxRetryTimeout
		}
		return output.Suggestion{
			Description: "To retry with a longer timeout, run:",
			Command:     rerunReplacingFlag(utils.ShortDuration(next), "--timeout", "-t"),
		}, true
	}
	return output.Suggestion{}, false
}

// joinUserPath joins elems to a path that the user wrote, and keeps its ./ prefix, so that the
// path in a next step looks like the one that the user wrote.
func joinUserPath(base string, elems ...string) string {
	joined := filepath.Join(append([]string{base}, elems...)...)
	if strings.HasPrefix(base, "./") && !filepath.IsAbs(joined) && !strings.HasPrefix(joined, "../") {
		joined = "./" + joined
	}
	return joined
}

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
	if err != nil || n <= 0 {
		return "16G"
	}
	if memoryGib(value)*2 >= maxRetryMemory {
		return "16G"
	}
	return fmt.Sprintf("%d%s", n*2, suffix)
}

func memoryGib(value string) int {
	digits := 0
	for digits < len(value) && value[digits] >= '0' && value[digits] <= '9' {
		digits++
	}
	suffix := value[digits:]
	if digits == 0 {
		return 0
	}
	n, err := strconv.ParseInt(value[:digits], 10, 64)
	if err != nil || n <= 0 {
		return 0
	}
	switch suffix {
	case "G", "g":
		return int(n)
	case "M", "m":
		return int(n / 1024)
	case "K", "k":
		return int(n / (1024 * 1024))
	case "":
		return int(n / (1024 * 1024 * 1024))
	default:
		return 0
	}
}

func logSuggestion() (output.Suggestion, bool) {
	if globals.LogPath == "" {
		return output.Suggestion{}, false
	}
	return output.Suggestion{
		Description: "To see the full details, open the log:",
		Command:     globals.LogPath,
	}, true
}

// analyzerLogSuggestion points at the analyzer log after an unhandled analyzer exception
// (exit code 252), whose details are only in that log. The second result is false for other
// outcomes, and when the run has its own log file, which already holds the analyzer output.
func analyzerLogSuggestion(fail *analyzer.Error, logsFile string) (output.Suggestion, bool) {
	if fail == nil || fail.ExitCode != analyzer.ExitException || logsFile == "" || globals.LogPath != "" {
		return output.Suggestion{}, false
	}
	return output.Suggestion{
		Description: "To see the analyzer exception, open the analyzer log:",
		Command:     logsFile,
	}, true
}

func appendLogSuggestion(s []output.Suggestion) []output.Suggestion {
	if logSug, ok := logSuggestion(); ok {
		return append(s, logSug)
	}
	return s
}

func buildFailSuggestions(contextual []output.Suggestion) []output.Suggestion {
	return append(appendLogSuggestion(nil), contextual...)
}

// failWith prints the error with its causes from err, which may be nil, and the next steps, and
// exits with code.
func failWith(code int, message string, err error, contextual ...output.Suggestion) {
	out.Error(message, err)
	out.Suggestions(buildFailSuggestions(contextual)...)
	os.Exit(code)
}

// fail prints the error with its causes from err and the log file, and exits with code 1.
func fail(message string, err error) {
	failWith(1, message, err)
}
