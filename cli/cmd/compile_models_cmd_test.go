package cmd

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/output"
)

// A Go model project needs no compiling: compile models says so and succeeds.
func TestCompileModelsAcceptsGoModelModule(t *testing.T) {
	dir := t.TempDir()
	writeTestFile(t, filepath.Join(dir, "go.mod"), "module opentaint\n\ngo 1.25\n")

	var buf bytes.Buffer
	orig := out
	out = output.NewWithWriter(&buf)
	t.Cleanup(func() { out = orig })

	// A failure would exit the test binary instead of returning.
	compileModelsCmd.Run(compileModelsCmd, []string{dir})

	printed := buf.String()
	for _, want := range []string{
		"Nothing to compile: the analyzer reads the Go models in `" + dir + "` from source",
		"To scan with these models, run:",
		"opentaint scan <source-path> --dataflow-models " + dir,
	} {
		if !strings.Contains(printed, want) {
			t.Errorf("output does not contain %q:\n%s", want, printed)
		}
	}
}
