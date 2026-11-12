package cmd

import (
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
)

func TestModelProjectSuggestions(t *testing.T) {
	tests := []struct {
		name string
		err  error
		want []output.Suggestion
	}{
		{
			name: "no models",
			err:  &models.ProjectNeededError{Path: ".opentaint/dataflow", Reason: models.NoModels},
			want: []output.Suggestion{{
				Description: "To create a model project, run:",
				Command:     "opentaint model init .opentaint/dataflow --language <language> --dependency <library>",
			}},
		},
		{
			name: "plain classes",
			err:  &models.ProjectNeededError{Path: "models/classes", Reason: models.PlainClasses},
			want: []output.Suggestion{{
				Description: "To create a model project, run:",
				Command:     "opentaint model init <model-project> --language java --dependency <group:artifact:version>",
			}},
		},
		{
			name: "other error",
			err:  errors.New("`models` does not exist"),
			want: nil,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			if got := modelProjectSuggestions(tc.err); !reflect.DeepEqual(got, tc.want) {
				t.Errorf("modelProjectSuggestions() = %v, want %v", got, tc.want)
			}
		})
	}
}

func TestCheckPassthroughPath(t *testing.T) {
	write := func(t *testing.T, path string) {
		t.Helper()
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte("passThrough: []\n"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	root := t.TempDir()
	empty := filepath.Join(root, "empty")
	if err := os.MkdirAll(filepath.Join(empty, "sub"), 0o755); err != nil {
		t.Fatal(err)
	}
	hidden := filepath.Join(root, "hidden")
	write(t, filepath.Join(hidden, ".gitkeep"))
	mixed := filepath.Join(root, "mixed")
	write(t, filepath.Join(mixed, "README.md"))
	write(t, filepath.Join(mixed, "java", "jackson.yml"))
	other := filepath.Join(root, "other")
	write(t, filepath.Join(other, "jackson.json"))
	file := filepath.Join(root, "single.yaml")
	write(t, file)
	notYAML := filepath.Join(root, "single.json")
	write(t, notYAML)

	for name, tc := range map[string]struct {
		path, wantErr string
	}{
		"empty directory":        {empty, ""},
		"hidden files only":      {hidden, ""},
		"YAML among other files": {mixed, ""},
		"YAML file":              {file, ""},
		"no YAML files":          {other, "contains no pass-through models"},
		"file that is not YAML":  {notYAML, "is not a pass-through model"},
		"missing":                {filepath.Join(root, "missing"), "does not exist"},
	} {
		t.Run(name, func(t *testing.T) {
			err := checkPassthroughPath(tc.path)
			if tc.wantErr == "" {
				if err != nil {
					t.Fatalf("checkPassthroughPath() = %v, want no error", err)
				}
				return
			}
			if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
				t.Fatalf("checkPassthroughPath() = %v, want an error with %q", err, tc.wantErr)
			}
		})
	}
}
