package cmd

import (
	"fmt"
	"os"
	"strconv"

	"github.com/seqra/opentaint/internal/globals"
	"github.com/seqra/opentaint/internal/utils"
	"github.com/seqra/opentaint/internal/utils/java"
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
not download artifacts except built-in rules, which are fetched on demand.`,
	Args: cobra.NoArgs,
	Run: func(cmd *cobra.Command, args []string) {
		runHealth()
	},
}

func init() {
	rootCmd.AddCommand(healthCmd)
	healthCmd.Flags().BoolVar(&healthAutobuilder, "autobuilder", false, "Print only the autobuilder JAR path")
	healthCmd.Flags().BoolVar(&healthAnalyzer, "analyzer", false, "Print only the analyzer JAR path")
	healthCmd.Flags().BoolVar(&healthRules, "rules", false, "Print only the built-in rules path, downloading rules if needed")
	healthCmd.Flags().BoolVar(&healthRuntime, "runtime", false, "Print only the Java runtime path")
}

func runHealth() {
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
		fmt.Println(c.path)
		if !c.present {
			fmt.Fprintf(os.Stderr, "%s missing at %s\n", c.name, c.path)
		}
		return
	}

	sb := out.Section("OpenTaint Health")
	th := out.Theme()
	for _, c := range components {
		node := out.GroupItem(th.FieldKey.Render(c.name + ":"))
		if c.version != "" {
			node.Child(th.FieldValue.Render(c.version))
		}
		path := c.path
		if !c.present {
			path += "  " + th.Error.Render("missing")
		}
		node.Child(th.FieldValue.Render(path))
		sb.Child(node)
	}
	sb.Render()
}

// resolveHealthComponent resolves a component's path and presence. Only the
// rules are fetched on demand; the rest are reported as-is.
func resolveHealthComponent(key string) healthComponent {
	switch key {
	case "autobuilder":
		def := globals.ArtifactByKind("autobuilder")
		path, err := utils.ResolveJarPath(def)
		version := utils.ArtifactVersion(def, globals.Config.Autobuilder.JarPath)
		return healthComponent{"Autobuilder", version, path, err == nil && utils.PathExists(path)}
	case "analyzer":
		def := globals.ArtifactByKind("analyzer")
		path, err := utils.ResolveJarPath(def)
		version := utils.ArtifactVersion(def, globals.Config.Analyzer.JarPath)
		return healthComponent{"Analyzer", version, path, err == nil && utils.PathExists(path)}
	case "rules":
		return resolveRulesComponent()
	case "runtime":
		return resolveRuntimeComponent()
	default:
		return healthComponent{name: key}
	}
}

// resolveRulesComponent resolves the built-in rules directory, downloading it
// on demand so `health --rules` replaces `dev rules-path`.
func resolveRulesComponent() healthComponent {
	c := healthComponent{name: "Rules", version: utils.ArtifactVersion(globals.ArtifactByKind("rules"), "")}
	path, err := utils.GetRulesPath(globals.Config.Rules.Version)
	if err != nil {
		return c
	}
	c.path = path
	if utils.PathExists(path) {
		c.present = true
		return c
	}
	if dlErr := utils.DownloadAndUnpackGithubReleaseAsset(
		globals.Config.Owner, globals.Config.Repo,
		globals.Config.Rules.Version, globals.RulesAssetName,
		path, globals.Config.Github.Token, globals.Config.SkipVerify, out,
	); dlErr != nil {
		fmt.Fprintf(os.Stderr, "Error downloading rules: %s\n", dlErr)
		return c
	}
	c.present = utils.PathExists(path)
	return c
}

// resolveRuntimeComponent reports the Java the analyzer runs on, and where it
// comes from: "builtin" is the JRE OpenTaint manages itself (downloaded/bundled
// into its own install), "system" is a Java already on the user's PATH.
func resolveRuntimeComponent() healthComponent {
	c := healthComponent{name: "Runtime"}
	if jre := utils.FindExistingJRE(utils.ManagedJRETiers()); jre != nil {
		c.path = utils.JavaBinaryPath(jre.Path)
		c.version = "Java " + strconv.Itoa(globals.DefaultJavaVersion) + " (builtin)"
		c.present = true
		return c
	}
	if sys := java.DetectSystemJava(); sys != nil {
		c.path = sys.Path
		c.version = "Java " + sys.FullVersion + " (system)"
		c.present = true
		return c
	}
	c.version = "Java " + strconv.Itoa(globals.DefaultJavaVersion) + " (builtin)"
	if jre := utils.GetInstallJREPath(); jre != "" {
		c.path = utils.JavaBinaryPath(jre)
	}
	return c
}
