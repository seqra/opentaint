package util

import (
	"os"
)

// Sink_SubprocessEnv represents appending to exec.Cmd.Env (leaks via subprocess env).
func Sink_SubprocessEnv(entry string) { _ = entry }

// Positive_subprocess_env: AWS secret embedded into a CHILD_TOKEN= env entry.
func Positive_subprocess_env() {
	s := os.Getenv("AWS_SECRET")
	Sink_SubprocessEnv("CHILD_TOKEN=" + s)
}

// Negative_subprocess_env_const: env read but a constant entry passed to subprocess.
func Negative_subprocess_env_const() {
	_ = os.Getenv("AWS_SECRET")
	Sink_SubprocessEnv("CHILD_TOKEN=static")
}
