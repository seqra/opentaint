package cmd

import (
	"reflect"
	"testing"

	"github.com/spf13/pflag"
)

func parseRenamed(t *testing.T, args []string) []string {
	t.Helper()
	var target []string
	fs := pflag.NewFlagSet("test", pflag.ContinueOnError)
	addRenamedStringArrayFlag(fs, &target, "passthrough-models", "passthrough-approximations", "usage")
	if err := fs.Parse(args); err != nil {
		t.Fatalf("parse %v: %v", args, err)
	}
	return target
}

func TestRenamedFlagAccumulatesAcrossBothSpellings(t *testing.T) {
	cases := [][]string{
		{"--passthrough-models", "a.yaml", "--passthrough-approximations", "b.yaml"},
		{"--passthrough-approximations", "a.yaml", "--passthrough-models", "b.yaml"},
	}
	for _, args := range cases {
		got := parseRenamed(t, args)
		if len(got) != 2 {
			t.Errorf("args %v: got %v, want both values kept", args, got)
		}
	}
}

func TestRenamedFlagKeepsRepeatsInOrder(t *testing.T) {
	got := parseRenamed(t, []string{
		"--passthrough-models", "a.yaml",
		"--passthrough-models", "b.yaml",
		"--passthrough-approximations", "c.yaml",
	})
	if want := []string{"a.yaml", "b.yaml", "c.yaml"}; !reflect.DeepEqual(got, want) {
		t.Errorf("got %v, want %v", got, want)
	}
}

func TestRenamedFlagAliasIsDeprecatedAndHidden(t *testing.T) {
	var target []string
	fs := pflag.NewFlagSet("test", pflag.ContinueOnError)
	addRenamedStringArrayFlag(fs, &target, "passthrough-models", "passthrough-approximations", "usage")
	alias := fs.Lookup("passthrough-approximations")
	if alias == nil || alias.Deprecated == "" {
		t.Fatal("alias must be registered and marked deprecated")
	}
	if fs.Lookup("passthrough-models").Deprecated != "" {
		t.Error("the new spelling must not be deprecated")
	}
}
