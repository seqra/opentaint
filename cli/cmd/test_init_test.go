package cmd

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/spf13/cobra"
)

func TestTestInitCommandsRequireLanguage(t *testing.T) {
	for _, cmd := range []*cobra.Command{testRuleInitCmd, testModelInitCmd} {
		flag := cmd.Flags().Lookup("language")
		if flag == nil {
			t.Fatalf("%s has no language flag", cmd.CommandPath())
		}
		if flag.DefValue != "" {
			t.Fatalf("%s language default = %q, want no default", cmd.CommandPath(), flag.DefValue)
		}
		if len(flag.Annotations[cobra.BashCompOneRequiredFlag]) == 0 {
			t.Fatalf("%s language flag is not required", cmd.CommandPath())
		}
	}
}

func TestOtherTestProjectLanguage(t *testing.T) {
	goDir := t.TempDir()
	if err := os.WriteFile(filepath.Join(goDir, "go.mod"), []byte("module test\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	javaDir := t.TempDir()
	if err := os.WriteFile(filepath.Join(javaDir, "build.gradle.kts"), nil, 0o644); err != nil {
		t.Fatal(err)
	}

	for _, tc := range []struct {
		dir, language string
		wantErr       bool
	}{
		{goDir, "java", true},
		{goDir, "go", false},
		{javaDir, "go", true},
		{javaDir, "java", false},
		{t.TempDir(), "go", false},
	} {
		if err := otherTestProjectLanguage(tc.dir, tc.language); (err != nil) != tc.wantErr {
			t.Errorf("otherTestProjectLanguage(%s, %s) = %v, want error %v", tc.dir, tc.language, err, tc.wantErr)
		}
	}
}

func TestTestRunHint(t *testing.T) {
	for name, tc := range map[string]struct {
		language, runFormat string
		dirs                []string
		want                string
	}{
		"go rule projects": {"go", "opentaint test rule run %s", []string{"t/sinks", "t/sources"},
			"opentaint test rule run t/sinks\nopentaint test rule run t/sources"},
		"go model project": {"go", "opentaint test model run %s --dataflow-models <models>", []string{"t"},
			"opentaint test model run t --dataflow-models <models>"},
		"java model project": {"java", "opentaint test model run %s --dataflow-models <models>", []string{"t"},
			"opentaint compile t -o <project-model>\nopentaint test model run <project-model> --dataflow-models <models>"},
		"java rule projects": {"java", "opentaint test rule run %s", []string{"t/sinks", "t/sources"},
			"opentaint compile <test-project> -o <project-model>\nopentaint test rule run <project-model>"},
	} {
		t.Run(name, func(t *testing.T) {
			_, command := testRunHint(tc.language, tc.runFormat, tc.dirs)
			if command != tc.want {
				t.Errorf("command = %q, want %q", command, tc.want)
			}
			if strings.Contains(command, "go mod tidy") {
				t.Error("the hint still asks for go mod tidy")
			}
		})
	}
}

func TestCompileNextStep(t *testing.T) {
	plain := t.TempDir()
	ruleTest := t.TempDir()
	writeTestFile(t, filepath.Join(ruleTest, "rule-test.yaml"), "")
	modelTest := t.TempDir()
	writeTestFile(t, filepath.Join(modelTest, "rule-test.yaml"), "")
	writeTestFile(t, filepath.Join(modelTest, "approximation-rule.yaml"), "")

	for dir, want := range map[string]string{
		plain:     "opentaint scan",
		ruleTest:  "opentaint test rule run /out",
		modelTest: "opentaint test model run /out --dataflow-models <models>",
	} {
		if _, command := compileNextStep(dir, dir, "/out"); !strings.HasPrefix(command, want) {
			t.Errorf("compileNextStep(%s) = %q, want %q", dir, command, want)
		}
	}
}
