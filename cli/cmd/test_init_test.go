package cmd

import (
	"path/filepath"
	"testing"

	"github.com/spf13/cobra"
)

func TestTestCompileCommand(t *testing.T) {
	tests := []struct {
		outputDir, side, want string
	}{
		{".opentaint/test-projects/my-rule", "<side>",
			"opentaint compile .opentaint/test-projects/my-rule/<side> -o .opentaint/test-compiled/my-rule/<side>"},
		{".opentaint/test-projects/my-rule", "sinks",
			"opentaint compile .opentaint/test-projects/my-rule/sinks -o .opentaint/test-compiled/my-rule/sinks"},
		{".opentaint/test-projects/my-model", "",
			"opentaint compile .opentaint/test-projects/my-model -o .opentaint/test-compiled/my-model"},
		{"./.opentaint/test-projects/my-model/", "",
			"opentaint compile ./.opentaint/test-projects/my-model -o ./.opentaint/test-compiled/my-model"},
		{"/home/user/app/.opentaint/test-projects/my-rule", "sources",
			"opentaint compile /home/user/app/.opentaint/test-projects/my-rule/sources -o /home/user/app/.opentaint/test-compiled/my-rule/sources"},
		{"tests/my rule", "<side>", "opentaint compile 'tests/my rule'/<side>"},
	}
	for _, tc := range tests {
		if got := testCompileCommand(tc.outputDir, tc.side); got != tc.want {
			t.Errorf("testCompileCommand(%q, %q) = %q, want %q", tc.outputDir, tc.side, got, tc.want)
		}
	}
}

func TestTestInitCommandsRequireLanguage(t *testing.T) {
	for _, cmd := range []*cobra.Command{testRuleInitCmd, testModelInitCmd} {
		flag := cmd.Flags().Lookup("language")
		if flag == nil {
			t.Fatalf("%s has no --language flag", cmd.CommandPath())
		}
		if flag.DefValue != "" {
			t.Errorf("%s --language default = %q, want none", cmd.CommandPath(), flag.DefValue)
		}
		if flag.Annotations[cobra.BashCompOneRequiredFlag] == nil {
			t.Errorf("%s --language is not required", cmd.CommandPath())
		}
	}
}

// Init updates a test project in the same language and refuses to mix the languages.
func TestExistingTestProject(t *testing.T) {
	goDir := t.TempDir()
	writeTestFile(t, filepath.Join(goDir, "go.mod"), "module test\n")
	javaDir := t.TempDir()
	writeTestFile(t, filepath.Join(javaDir, "build.gradle.kts"), "")

	for _, tc := range []struct {
		name, dir, language string
		want                bool
		wantErr             string
	}{
		{"new", t.TempDir(), "go", false, ""},
		{"same language", goDir, "go", true, ""},
		{"go project for java", goDir, "java", false, "`" + goDir + "` is a Go test project"},
		{"java project for go", javaDir, "go", false, "`" + javaDir + "` is a Java test project"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := existingTestProject(tc.dir, tc.language)
			if got != tc.want {
				t.Errorf("existing = %v, want %v", got, tc.want)
			}
			if gotErr := errorText(err); gotErr != tc.wantErr {
				t.Errorf("error = %q, want %q", gotErr, tc.wantErr)
			}
		})
	}
}

func errorText(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}
