package cmd

import (
	"bytes"
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
		{[]string{"approximation", "init"}, "opentaint model init", "dependency"},
		{[]string{"compile", "approximations"}, "opentaint compile models", "output"},
		{[]string{"test", "approximation", "init"}, "opentaint test model init", "dependency"},
		{[]string{"test", "approximation", "run"}, "opentaint test model run", "dataflow-models"},
	} {
		t.Run(strings.Join(tc.old, " "), func(t *testing.T) {
			command, rest, err := rootCmd.Find(tc.old)
			if err != nil || len(rest) != 0 || command.Name() != tc.old[len(tc.old)-1] {
				t.Fatalf("Find(%v) = %s %v %v", tc.old, command.CommandPath(), rest, err)
			}
			if got := command.Annotations[renamedTo]; got != tc.newPath {
				t.Errorf("renamed to %q, want %q", got, tc.newPath)
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
		if !flag.Hidden || !strings.HasSuffix(flag.Annotations[renamedTo][0], "-models") {
			t.Errorf("--%s: hidden=%v annotations=%v, want a hidden alias naming the new flag", old, flag.Hidden, flag.Annotations)
		}
	}
}

func TestModelFlagsOnAnalyzerCommands(t *testing.T) {
	for _, command := range []*cobra.Command{scanCmd, testRuleRunCmd, testModelRunCmd} {
		for _, name := range []string{"dataflow-models", "dataflow-approximations", "passthrough-models", "passthrough-approximations"} {
			if command.Flags().Lookup(name) == nil {
				t.Errorf("%s has no --%s", command.CommandPath(), name)
			}
		}
	}
}

func TestDeprecatedGroupHelpIsTheHelpOfTheNewGroup(t *testing.T) {
	var buf bytes.Buffer
	rootCmd.SetOut(&buf)
	t.Cleanup(func() { rootCmd.SetOut(nil) })

	for _, tc := range []struct {
		old  []string
		want string
	}{
		{[]string{"approximation"}, "opentaint model <command>"},
		{[]string{"test", "approximation"}, "opentaint test model <command>"},
		// A subcommand of a deprecated group keeps its own help.
		{[]string{"approximation", "init"}, "opentaint approximation init <model-project>"},
		{[]string{"test", "approximation", "run"}, "opentaint test approximation run <test-project-model>"},
	} {
		t.Run(strings.Join(tc.old, " "), func(t *testing.T) {
			command, _, err := rootCmd.Find(tc.old)
			if err != nil {
				t.Fatal(err)
			}
			buf.Reset()
			command.HelpFunc()(command, nil)
			if !strings.Contains(buf.String(), tc.want) {
				t.Errorf("help does not contain %q:\n%s", tc.want, buf.String())
			}
		})
	}
}
