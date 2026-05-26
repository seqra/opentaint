package util

import (
	"os"
)

// Sink_LogOutput represents a log.Printf / log.Println style sink.
func Sink_LogOutput(msg string) { _ = msg }

// Positive_branch_log: secret logged inside an if-branch.
func Positive_branch_log() {
	t := os.Getenv("GITHUB_TOKEN")
	debug := os.Getenv("DEBUG")
	if debug != "" {
		Sink_LogOutput("github token = " + t)
	}
}

// Negative_branch_other_log: same env var, but log line on this branch is constant.
func Negative_branch_other_log() {
	_ = os.Getenv("GITHUB_TOKEN")
	debug := os.Getenv("DEBUG")
	if debug != "" {
		Sink_LogOutput("debug enabled")
	}
}
