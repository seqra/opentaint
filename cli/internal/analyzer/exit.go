// Package analyzer holds OpenTaint analyzer domain logic that is independent
// of the CLI presentation layer. It currently covers exit-code classification
// for analyzer process failures.
package analyzer

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
	ExitConfigError = 255
	ExitTimeout     = 254
	ExitOOM         = 253
	ExitException   = 252
)

// Error holds information about an analyzer failure. ExitCode is the process
// exit code to forward to os.Exit; Message is a human-readable description.
type Error struct {
	ExitCode int
	Message  string
}

// ExitMessage returns the error message for a known analyzer exit code, or an empty string
// if the code is not known. Classify adds the code to it. The suggestions after the error say
// what to do.
func ExitMessage(code int) string {
	switch code {
	case ExitConfigError:
		return "Analysis failed because of a project configuration error"
	case ExitTimeout:
		return "Analysis timed out"
	case ExitOOM:
		return "Analysis ran out of memory"
	case ExitException:
		return "The analyzer failed with an unhandled exception"
	default:
		return ""
	}
}

// Classify converts a *java.JavaCommandError into an *Error with a formatted
// message. Returns nil when cmdErr is nil. No I/O is performed — the caller
// is responsible for presentation and for calling os.Exit(Error.ExitCode).
func Classify(cmdErr *java.JavaCommandError) *Error {
	if cmdErr == nil {
		return nil
	}

	code := cmdErr.ExitCode
	if msg := ExitMessage(code); msg != "" {
		return &Error{ExitCode: code, Message: fmt.Sprintf("%s (exit code %d)", msg, code)}
	}
	return &Error{
		ExitCode: code,
		Message:  fmt.Sprintf("The analyzer exited with code %d", code),
	}
}
