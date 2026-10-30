package cmd

import (
	"reflect"
	"strings"
	"testing"

	"github.com/spf13/cobra"
)

func TestDeprecatedCommandsPointAtTheirNewNames(t *testing.T) {
	for _, tc := range []struct {
		old     []string
		newPath string
		flag    string
	}{
		{[]string{"approximation", "init"}, "opentaint model init", "language"},
		{[]string{"compile", "approximations"}, "opentaint compile models", "output"},
		{[]string{"test", "approximation", "init"}, "opentaint test model init", "language"},
		{[]string{"test", "approximation", "run"}, "opentaint test model run", "dataflow-models"},
	} {
		t.Run(strings.Join(tc.old, " "), func(t *testing.T) {
			command, rest, err := rootCmd.Find(tc.old)
			if err != nil || len(rest) != 0 || command.Name() != tc.old[len(tc.old)-1] {
				t.Fatalf("Find(%v) = %s %v %v", tc.old, command.CommandPath(), rest, err)
			}
			if !strings.Contains(command.Deprecated, tc.newPath) {
				t.Errorf("Deprecated = %q, want it to name %q", command.Deprecated, tc.newPath)
			}
			if command.IsAvailableCommand() {
				t.Error("a deprecated command is listed in help")
			}
			if command.Run == nil || command.Flags().Lookup(tc.flag) == nil {
				t.Errorf("the alias does not run the new command with its flags")
			}

			current, _, err := rootCmd.Find(strings.Fields(strings.TrimPrefix(tc.newPath, "opentaint ")))
			if err != nil || current.Deprecated != "" || !current.IsAvailableCommand() {
				t.Errorf("new command %s is missing or hidden: %v", tc.newPath, err)
			}
		})
	}
}

func TestDeprecatedFlagAliasesFeedTheNewFlag(t *testing.T) {
	var dataflow, passthrough []string
	command := &cobra.Command{Use: "probe", Run: func(*cobra.Command, []string) {}}
	addDataflowModelsFlag(command, &dataflow)
	addPassthroughModelsFlag(command, &passthrough)

	err := command.ParseFlags([]string{
		"--dataflow-models", "a", "--dataflow-approximations", "b",
		"--passthrough-approximations", "c", "--passthrough-models", "d",
	})
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(dataflow, []string{"a", "b"}) {
		t.Errorf("dataflow models = %v, want [a b]", dataflow)
	}
	if !reflect.DeepEqual(passthrough, []string{"c", "d"}) {
		t.Errorf("passthrough models = %v, want [c d]", passthrough)
	}
	for _, old := range []string{"dataflow-approximations", "passthrough-approximations"} {
		flag := command.Flags().Lookup(old)
		if !flag.Hidden || !strings.Contains(flag.Deprecated, "-models") {
			t.Errorf("--%s: hidden=%v deprecated=%q, want a hidden alias naming the new flag", old, flag.Hidden, flag.Deprecated)
		}
	}
}

func TestModelFlagsOnAnalyzerCommands(t *testing.T) {
	for _, command := range []*cobra.Command{scanCmd, testRuleRunCmd, testModelRunCmd} {
		for _, name := range []string{"dataflow-models", "dataflow-approximations"} {
			if command.Flags().Lookup(name) == nil {
				t.Errorf("%s has no --%s", command.CommandPath(), name)
			}
		}
	}
	for _, command := range []*cobra.Command{scanCmd, testRuleRunCmd} {
		for _, name := range []string{"passthrough-models", "passthrough-approximations"} {
			if command.Flags().Lookup(name) == nil {
				t.Errorf("%s has no --%s", command.CommandPath(), name)
			}
		}
	}
}
