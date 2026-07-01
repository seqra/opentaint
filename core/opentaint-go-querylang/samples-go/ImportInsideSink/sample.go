package util

import (
	"context"
	"os"
	"os/exec"
)

func Positive_cmd_name() {
	bar := os.Getenv("TAINTED")
	_ = exec.Command(bar, "-l")
}

func Positive_cmd_context() {
	bar := os.Getenv("TAINTED")
	_ = exec.CommandContext(context.Background(), bar, "-l")
}

func Negative_const_name() {
	_ = exec.Command("ls", "-l")
}
