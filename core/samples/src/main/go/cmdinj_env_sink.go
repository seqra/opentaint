package test

import (
	"os"
	"os/exec"
)

func cmdInjEnvSink001T() {
	bar := os.Getenv("TAINTED")

	args := []string{"sh", "-c", "echo"}
	argsEnv := []string{bar}

	r := exec.Command(args[0], args[1:]...)
	r.Env = append(r.Env, argsEnv...)

	wrappedOutput(r)
}

func wrappedOutput(r *exec.Cmd) {
	output, err := r.CombinedOutput()
	if err != nil {
		return
	}
	_ = output
}

func cmdInjEnvSink002F() {
	args := []string{"sh", "-c", "echo"}
	argsEnv := []string{"safe"}

	r := exec.Command(args[0], args[1:]...)
	r.Env = append(r.Env, argsEnv...)

	wrappedOutput(r)
}
