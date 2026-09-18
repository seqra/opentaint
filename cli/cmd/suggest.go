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
		if timeout >= maxRetryTimeout {
			return output.Suggestion{}, false
		}
		next := timeout * 2
		if next <= timeout || next > maxRetryTimeout {
			next = maxRetryTimeout
		}
		return output.Suggestion{
			Description: "To retry with a longer timeout, run:",
			Command:     rerunReplacingFlag(next.String(), "--timeout", "-t"),
		}, true
	}
	return output.Suggestion{}, false
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
		Description: "For full details, check the log file:",
		Command:     globals.LogPath,
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

func failWith(code int, message string, contextual ...output.Suggestion) {
	out.Error(message)
	out.Suggestions(buildFailSuggestions(contextual)...)
	os.Exit(code)
}

func failf(format string, args ...any) {
	failWith(1, fmt.Sprintf(format, args...))
}
