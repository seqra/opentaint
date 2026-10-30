package cmd

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/output"
)

// A Go model module needs no compilation: compile models explains that and succeeds.
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
		"Go models are loaded from source; no compilation needed",
		"Pass the directory to --dataflow-models",
		"opentaint scan <project> --dataflow-models " + dir,
	} {
		if !strings.Contains(printed, want) {
			t.Errorf("output does not contain %q:\n%s", want, printed)
		}
	}
}
