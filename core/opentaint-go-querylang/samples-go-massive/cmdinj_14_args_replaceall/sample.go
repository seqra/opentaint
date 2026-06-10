package util

import (
	"os"
	"strings"
)

// Sink_ExecLookPath represents a real os/exec.LookPath(...) call site (command injection sink).
func Sink_ExecLookPath(name string) { _ = name }

// Positive_replaceall: tainted os.Args transformed and reaches sink.
func Positive_replaceall() {
	v := strings.ReplaceAll(os.Args[1], "/", "")
	Sink_ExecLookPath(v)
}

// Negative_replaceall_unused: source flow broken.
func Negative_replaceall_unused() {
	_ = strings.ReplaceAll(os.Args[1], "/", "")
	Sink_ExecLookPath("sh")
}
