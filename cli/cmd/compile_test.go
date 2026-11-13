package cmd

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/testmodel"
	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/testrule"
)

func TestCompileNextStep(t *testing.T) {
	plain := t.TempDir()
	if err := os.WriteFile(filepath.Join(plain, "pom.xml"), nil, 0o644); err != nil {
		t.Fatal(err)
	}
	ruleTest := t.TempDir()
	if err := testrule.Scaffold(ruleTest); err != nil {
		t.Fatal(err)
	}
	modelTest := t.TempDir()
	if err := testmodel.Scaffold(modelTest); err != nil {
		t.Fatal(err)
	}

	ruleTestFile := writeRuleTest(t)

	for name, tc := range map[string]struct{ dir, want string }{
		"project":             {plain, "opentaint scan "},
		"rule tests":          {ruleTest, "opentaint test rule run /out --ruleset " + filepath.Join(ruleTest, testrule.MarkersDir)},
		"model tests":         {modelTest, "opentaint test model run /out --dataflow-models <model-project>"},
		"rule-test.yaml only": {ruleTestFile, "opentaint test rule run /out"},
	} {
		t.Run(name, func(t *testing.T) {
			_, command := compileNextStep(tc.dir, tc.dir, "/out")
			if name == "project" {
				if !strings.HasPrefix(command, tc.want) {
					t.Errorf("command = %q, want the prefix %q", command, tc.want)
				}
				return
			}
			if command != tc.want {
				t.Errorf("command = %q, want %q", command, tc.want)
			}
		})
	}
}

func writeRuleTest(t *testing.T) string {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, testproject.RuleTestFileName), []byte("tests: []\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	return dir
}
