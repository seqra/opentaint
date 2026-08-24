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

type healthComponent struct {
	name    string
	version string
	path    string
	present bool
}

var healthCmd = &cobra.Command{
	Use:   "health",
	Short: "Show dependency paths and report missing components",
	Long: `Show the paths of the components on this computer. The components are the autobuilder, the analyzer, the built-in rules, and the Java runtime. The command shows if each component is present.

To select components, use --autobuilder, --analyzer, --rules, or --runtime. With no flag, the command shows all four components. If you select exactly one component, only its path is printed. This output is good for scripts.

Only the built-in rules are downloaded when they are missing. No other component is downloaded.

If a selected component is missing, the command exits with a code that is not zero. To download the missing components, run "opentaint pull".`,
	Example: `  # Show all components and their paths
  opentaint health

  # Print only the analyzer JAR path, for a script
  opentaint health --analyzer

  # Make sure the Java runtime is present
  opentaint health --runtime

  # Recipe: use the built-in rules path in a script
  RULES=$(opentaint health --rules)
  opentaint scan . --ruleset "$RULES" --ruleset ./extra-rules -o report.sarif`,
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
		out.Suggest("To download the missing components, run:", "opentaint pull")
		return fmt.Errorf("missing components: %s", strings.Join(missing, ", "))
	}
	return nil
}

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

func resolveJarComponent(kind string) healthComponent {
	def := globals.ArtifactByKind(kind)
	path, err := utils.ResolveJarPath(def)
	version := utils.ArtifactVersion(def)
	return healthComponent{def.Name, version, path, err == nil && utils.PathExists(path)}
}

func resolveRulesComponent() healthComponent {
	c := healthComponent{name: "Rules", version: utils.ArtifactVersion(globals.ArtifactByKind("rules"))}
	path, err := utils.EnsureRulesPath(out)
	c.path = path
	if err != nil {
		fmt.Fprintf(os.Stderr, "Failed to prepare built-in rules: %s\n", err)
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
