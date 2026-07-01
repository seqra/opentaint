package shexec

import "os/exec"

func Source() string { return "tainted" }

func Positive_shell_exec() {
	cmd := Source()
	_ = exec.Command("sh", "-c", "echo "+cmd)
}

func Negative_safe_exec() {
	arg := Source()
	_ = exec.Command("echo", arg)
}
