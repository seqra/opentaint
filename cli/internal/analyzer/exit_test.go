package analyzer

import (
	"testing"

	"github.com/seqra/opentaint/internal/utils/java"
)

func TestClassifyAddsTheExitCode(t *testing.T) {
	for code, want := range map[int]string{
		ExitOOM: "Analysis ran out of memory (exit code 253)",
		3:       "The analyzer exited with code 3",
	} {
		got := Classify(&java.JavaCommandError{ExitCode: code})
		if got.ExitCode != code || got.Message != want {
			t.Errorf("Classify(%d) = %+v, want message %q", code, got, want)
		}
	}
}
