package util

import (
	"os"
	"os/exec"
)

func Positive_env_combinedoutput() {
	bar := os.Getenv("TAINTED")

	args := []string{"sh", "-c", "echo"}
	argsEnv := []string{bar}

	r := exec.Command(args[0], args[1:]...)
	r.Env = append(r.Env, argsEnv...)

	output, err := r.CombinedOutput()
	if err != nil {
		return
	}
	_ = output
}

func Positive_env_run() {
	bar := os.Getenv("TAINTED")

	r := exec.Command("sh", "-c", "echo")
	r.Env = append(r.Env, bar)

	_ = r.Run()
}

func Negative_const_env() {
	argsEnv := []string{"safe"}

	r := exec.Command("sh", "-c", "echo")
	r.Env = append(r.Env, argsEnv...)

	output, err := r.CombinedOutput()
	if err != nil {
		return
	}
	_ = output
}
