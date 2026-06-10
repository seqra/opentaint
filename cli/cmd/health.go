package cmd

import (
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/spf13/cobra"
)

var (
	healthAutobuilder bool
	healthAnalyzer    bool
	healthRules       bool
	healthRuntime     bool
)

// healthComponent is one resolved dependency in the health report.
type healthComponent struct {
	name    string
	version string
	path    string
	present bool
}

// healthCmd represents the health command.
var healthCmd = &cobra.Command{
	Use:   "health",
	Short: "Show resolved dependency paths",
	Long: `Show the on-disk paths OpenTaint uses for the autobuilder, analyzer,
built-in rules, and Java runtime.

Use --autobuilder, --analyzer, --rules, or --runtime to select components. When
exactly one component is selected, only its path is printed. The command does
not download artifacts except built-in rules, which are fetched on demand.

The exit code is non-zero when any selected component is missing.`,
	Args: cobra.NoArgs,
	RunE: func(cmd *cobra.Command, args []string) error {
		return runHealth()
	},
}

func init() {
	rootCmd.AddCommand(healthCmd)
	healthCmd.Flags().BoolVar(&healthAutobuilder, "autobuilder", false, "Print only the autobuilder JAR path")
	healthCmd.Flags().BoolVar(&healthAnalyzer, "analyzer", false, "Print only the analyzer JAR path")
	healthCmd.Flags().BoolVar(&healthRules, "rules", false, "Print only the built-in rules path, downloading rules if needed")
	healthCmd.Flags().BoolVar(&healthRuntime, "runtime", false, "Print only the Java runtime path")
}

func runHealth() error {
	// No flags shows every component, in fixed order.
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
	if healthRuntime {
		requested = append(requested, "runtime")
	}
	if len(requested) == 0 {
		requested = []string{"autobuilder", "analyzer", "rules", "runtime"}
	}

	components := make([]healthComponent, 0, len(requested))
	for _, key := range requested {
		components = append(components, resolveHealthComponent(key))
	}

	// A single flag prints just the bare path, for scripting.
	if len(requested) == 1 {
		c := components[0]
		if c.path != "" {
			fmt.Println(c.path)
		}
		if !c.present {
			if c.path == "" {
				return fmt.Errorf("%s could not be resolved", c.name)
			}
			return fmt.Errorf("%s missing at %s", c.name, c.path)
		}
		return nil
	}

	sb := out.Section("OpenTaint Health")
	th := out.Theme()
	var missing []string
	for _, c := range components {
		node := out.GroupItem(th.FieldKey.Render(c.name))
		if c.version != "" {
			node.Child(th.FieldValue.Render(c.version))
		}
		path := c.path
		if !c.present {
			path += "  " + th.Error.Render("missing")
			missing = append(missing, c.name)
		}
		node.Child(th.FieldValue.Render(path))
		sb.Child(node)
	}
	sb.Render()
	if len(missing) > 0 {
		return fmt.Errorf("missing components: %s", strings.Join(missing, ", "))
	}
	return nil
}

// resolveHealthComponent resolves a component's path and presence. Only the
// rules are fetched on demand; the rest are reported as-is.
func resolveHealthComponent(key string) healthComponent {
	switch key {
	case "autobuilder", "analyzer":
		return resolveJarComponent(key)
	case "rules":
		return resolveRulesComponent()
	case "runtime":
		return resolveRuntimeComponent()
	default:
		return healthComponent{name: key}
	}
}

// resolveJarComponent resolves a jar-backed artifact (autobuilder/analyzer).
func resolveJarComponent(kind string) healthComponent {
	def := globals.ArtifactByKind(kind)
	path, err := utils.ResolveJarPath(def)
	version := utils.ArtifactVersion(def)
	return healthComponent{def.Name, version, path, err == nil && utils.PathExists(path)}
}

// resolveRulesComponent resolves the built-in rules directory, downloading it
// on demand so `health --rules` replaces `dev rules-path`.
func resolveRulesComponent() healthComponent {
	c := healthComponent{name: "Rules", version: utils.ArtifactVersion(globals.ArtifactByKind("rules"))}
	// EnsureRulesPath returns the expected path even on failure, so the report
	// can still show where the rules belong, flagged as missing.
	path, err := utils.EnsureRulesPath(out)
	c.path = path
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to prepare built-in rules: %s\n", err)
		return c
	}
	c.present = utils.PathExists(path)
	return c
}

// resolveRuntimeComponent reports the managed JRE the analyzer actually runs
// on. The analyzer's runner never consults a system Java (it pins the managed
// Adoptium JRE), so neither does health; when no managed JRE exists yet, the
// reported path is where the analyzer will download one on first use.
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
