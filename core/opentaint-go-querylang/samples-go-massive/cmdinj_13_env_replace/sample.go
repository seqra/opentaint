package util

import (
	"os"
	"strings"
)

// Sink_ExecCommand represents a real os/exec.Command(...) call site (command injection sink).
func Sink_ExecCommand(cmd string) { _ = cmd }

// Positive_replace: env value transformed via Replace then sinked.
func Positive_replace() {
	p := strings.Replace(os.Getenv("PATH_LIKE"), "\\", "/", -1)
	Sink_ExecCommand("cat " + p)
}

// Negative_replace_unused: result not used.
func Negative_replace_unused() {
	_ = strings.Replace(os.Getenv("PATH_LIKE"), "\\", "/", -1)
	Sink_ExecCommand("cat /etc/hosts")
}
