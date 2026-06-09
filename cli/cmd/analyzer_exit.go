package cmd

import (
	"fmt"

	"github.com/seqra/opentaint/internal/utils/java"
)

// Analyzer exit codes as seen by the OS (unsigned byte values).
// These correspond to the Kotlin exitProcess() calls in AbstractAnalyzerRunner:
//
//	exitProcess(-1)  → 255  (project configuration error)
//	exitProcess(-2)  → 254  (analysis timeout)
//	exitProcess(-3)  → 253  (out of memory)
//	exitProcess(-4)  → 252  (unhandled exception)
const (
	analyzerExitConfigError = 255
	analyzerExitTimeout     = 254
	analyzerExitOOM         = 253
	analyzerExitException   = 252
)

// analyzerError holds information about an analyzer failure.
// exitCode is the process exit code to forward to os.Exit.
type analyzerError struct {
	exitCode int
}

// analyzerExitMessage returns a human-readable description for a known
// analyzer exit code, or empty string if the code is not recognized.
func analyzerExitMessage(code int) string {
	switch code {
	case analyzerExitConfigError:
		return "project configuration error"
	case analyzerExitTimeout:
		return "analysis timed out — try increasing --timeout or --max-memory"
	case analyzerExitOOM:
		return "out of memory — try increasing --max-memory (e.g. --max-memory 16G)"
	case analyzerExitException:
		return "unhandled analyzer exception"
	default:
		return ""
	}
}

// classifyAnalyzerError prints a human-readable description of an analyzer
// failure and returns the *analyzerError carrying its exit code. Returns nil
// when cmdErr is nil.
//
// The message is printed immediately. The caller is responsible for eventually
// calling os.Exit with the returned exit code after performing any post-failure
// work (e.g. printing summaries).
func classifyAnalyzerError(cmdErr *java.JavaCommandError) *analyzerError {
	if cmdErr == nil {
		return nil
	}

	code := cmdErr.ExitCode
	formatted := fmt.Sprintf("Analysis failed with exit code %d", code)
	if msg := analyzerExitMessage(code); msg != "" {
		formatted = fmt.Sprintf("Analysis failed (exit code %d): %s", code, msg)
	}
	out.Error(formatted)
	return &analyzerError{exitCode: code}
}
