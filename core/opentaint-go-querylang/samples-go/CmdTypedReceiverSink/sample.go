package util

import (
	"os"
	"os/exec"
)

func Positive_typed_run() {
	bar := os.Getenv("TAINTED")

	r := exec.Command("sh", "-c", "echo")
	r.Env = append(r.Env, bar)

	_ = r.Run()
}

func Positive_typed_combinedoutput() {
	bar := os.Getenv("TAINTED")

	r := exec.Command("sh", "-c", "echo")
	r.Env = append(r.Env, bar)

	output, err := r.CombinedOutput()
	if err != nil {
		return
	}
	_ = output
}

func Negative_const_run() {
	r := exec.Command("sh", "-c", "echo")
	r.Env = append(r.Env, "safe")

	_ = r.Run()
}
