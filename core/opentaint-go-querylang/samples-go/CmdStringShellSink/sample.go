package util

import (
	"os"
	"os/exec"
)

func Positive_shell_tainted_arg() {
	bar := os.Getenv("TAINTED")
	_ = exec.Command("sh", "-c", bar)
}

func Positive_bash_tainted_arg() {
	bar := os.Getenv("TAINTED")
	_ = exec.Command("bash", "-c", bar)
}

func Negative_echo_tainted_arg() {
	bar := os.Getenv("TAINTED")
	_ = exec.Command("echo", bar)
}

func Negative_shell_const_args() {
	_ = exec.Command("sh", "-c", "ls")
}
