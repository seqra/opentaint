package cmd

import (
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/output"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/spf13/cobra"
)

var (
	healthAutobuilder bool
	healthAnalyzer    bool
	healthRules       bool
	healthGoServer    bool
	healthRuntime     bool
)

type healthComponent struct {
	name    string
	version string
	path    string
	present bool
}

var healthCmd = &cobra.Command{
	Use:   "health",
	Short: "Show the installed components and their paths",
	Long:  "Show the installed components and their paths.",
	Args:  cobra.NoArgs,
	Run: func(cmd *cobra.Command, args []string) {
		runHealth()
	},
}

func init() {
	rootCmd.AddCommand(healthCmd)
	healthCmd.Flags().BoolVar(&healthAutobuilder, "autobuilder", false, "Print only the autobuilder JAR path")
	healthCmd.Flags().BoolVar(&healthAnalyzer, "analyzer", false, "Print only the analyzer JAR path")
	healthCmd.Flags().BoolVar(&healthRules, "rules", false, "Print only the built-in ruleset path")
	healthCmd.Flags().BoolVar(&healthGoServer, "go-server", false, "Print only the Go server path")
	healthCmd.Flags().BoolVar(&healthRuntime, "runtime", false, "Print only the Java runtime path")
}

func runHealth() {
	var requested []string
	if healthAutobuilder {
		requested = append(requested, "autobuilder")
	}
	if healthAnalyzer {
		requested = append(requested, "analyzer")
	}
	if healthRules {
		requested = append(requested, "rules")
	}
	if healthGoServer {
		requested = append(requested, "goserver")
	}
	if healthRuntime {
		requested = append(requested, "runtime")
	}
	if len(requested) == 0 {
		requested = []string{"autobuilder", "analyzer", "rules", "goserver", "runtime"}
	}

	components := make([]healthComponent, 0, len(requested))
	for _, key := range requested {
		components = append(components, resolveHealthComponent(key))
	}

	if len(requested) == 1 {
		c := components[0]
		if c.path != "" {
			fmt.Println(c.path)
		}
		if !c.present {
			if c.path == "" {
				out.Fatalf("%s could not be resolved", c.name)
			}
			out.Fatalf("%s missing at %s", c.name, c.path)
		}
		return
	}

	sb := out.Section("OpenTaint Health")
	var missing []string
	for _, c := range components {
		if !c.present {
			missing = append(missing, c.name)
		}
		sb.FieldGroup(c.name, componentItems(c, true)...)
	}
	sb.Render()
	if len(missing) > 0 {
		out.Blank()
		out.Errorf("Missing components: %s", strings.Join(missing, ", "))
		out.Suggest("To download the missing components, run:", "opentaint pull")
		os.Exit(1)
	}
}

// componentItems are the items of a component in a block: its version and its path. A component
// that is not on disk has no path, or, with markMissing, a path that is marked as missing.
func componentItems(c healthComponent, markMissing bool) []any {
	var items []any
	if c.version != "" {
		items = append(items, out.FieldItem("Version", c.version))
	}
	switch {
	case c.present:
		items = append(items, out.FieldItem("Path", c.path))
	case markMissing:
		missing := out.Theme().Error.Render("missing")
		if c.path != "" {
			missing = c.path + " (" + missing + ")"
		}
		items = append(items, out.FieldItem("Path", missing))
	}
	return items
}

func resolveHealthComponent(key string) healthComponent {
	switch key {
	case "autobuilder", "analyzer", "goserver":
		return resolveArtifactComponent(key)
	case "rules":
		return resolveRulesComponent()
	case "runtime":
		return resolveRuntimeComponent()
	default:
		return healthComponent{name: key}
	}
}

// resolveArtifactComponent resolves a downloadable artifact (a JAR or the
// go-ssa-server binary) through the standard tiers and the dev override.
func resolveArtifactComponent(kind string) healthComponent {
	def := globals.ArtifactByKind(kind)
	path, err := utils.ResolveJarPath(def)
	version := utils.ArtifactVersion(def)
	return healthComponent{def.Label(), version, path, err == nil && utils.PathExists(path)}
}

func resolveRulesComponent() healthComponent {
	c := healthComponent{name: "Built-in ruleset", version: utils.ArtifactVersion(globals.ArtifactByKind("rules"))}
	path, err := utils.EnsureRulesPath(out)
	c.path = path
	if err != nil {
		fmt.Fprint(os.Stderr, output.FormatError(fmt.Errorf("failed to prepare the built-in ruleset: %w", err)))
		return c
	}
	c.present = utils.PathExists(path)
	return c
}

func resolveRuntimeComponent() healthComponent {
	c := healthComponent{
		name:    "Runtime",
		version: "Java " + strconv.Itoa(globals.DefaultJavaVersion) + " (builtin)",
	}
	if jre := utils.FindCurrentManagedJRE(); jre != nil {
		c.path = utils.JavaBinaryPath(jre.Path)
		c.present = true
		return c
	}
	if jre := utils.GetInstallJREPath(); jre != "" {
		c.path = utils.JavaBinaryPath(jre)
	}
	return c
}
