package util

import (
	"os"
)

// Sink_ExecLookPath represents a real os/exec.LookPath(...) call site (command injection sink).
func Sink_ExecLookPath(name string) { _ = name }

// Positive_direct: os.Args directly into LookPath.
func Positive_direct() {
	name := os.Args[1]
	Sink_ExecLookPath(name)
}

// Negative_literal: tainted args ignored.
func Negative_literal() {
	_ = os.Args[1]
	Sink_ExecLookPath("/bin/ls")
}
