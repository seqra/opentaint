package cmd

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/spf13/cobra"
)

func TestTestInitCommandsRequireLanguage(t *testing.T) {
	for _, cmd := range []*cobra.Command{testRuleInitCmd, testApproximationInitCmd} {
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
