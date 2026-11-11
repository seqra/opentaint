package cmd

import (
	"errors"
	"reflect"
	"testing"

	"github.com/seqra/opentaint/internal/models"
	"github.com/seqra/opentaint/internal/output"
)

func TestModelProjectSuggestions(t *testing.T) {
	paths := []string{"models", ".opentaint/dataflow"}
	absPaths := []string{"/work/models", "/work/.opentaint/dataflow"}
	initStep := func(path string) output.Suggestion {
		return output.Suggestion{
			Description: "To create a model project, run:",
			Command:     "opentaint model init " + path + " --dependency <group:artifact:version>",
		}
	}

	tests := []struct {
		name string
		err  error
		want []output.Suggestion
	}{
		{
			name: "no models",
			err:  &models.ProjectNeededError{Path: "/work/.opentaint/dataflow", Reason: models.NoModels},
			want: []output.Suggestion{initStep(".opentaint/dataflow")},
		},
		{
			name: "plain classes",
			err:  &models.ProjectNeededError{Path: "/work/models/classes", Reason: models.PlainClasses},
			want: []output.Suggestion{initStep("<model-project>")},
		},
		{
			name: "other error",
			err:  errors.New("`/work/models` does not exist"),
			want: nil,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			if got := modelProjectSuggestions(tc.err, paths, absPaths); !reflect.DeepEqual(got, tc.want) {
				t.Errorf("modelProjectSuggestions() = %v, want %v", got, tc.want)
			}
		})
	}
}
