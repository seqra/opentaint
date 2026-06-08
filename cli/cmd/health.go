package cmd

import (
	"fmt"
	"os"
	"strconv"
	"strings"

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

// healthCmd represents the health command
var healthCmd = &cobra.Command{
	Use:   "health",
	Short: "Print the resolved dependency paths",
	Long: `Print the on-disk paths OpenTaint resolves for its dependencies: autobuilder,
analyzer, rules, and the Java runtime.

Pass --autobuilder, --analyzer, --rules or --runtime to show only those; with a
single flag just the bare path is printed. Nothing is downloaded except the
rules, which are fetched on demand.`,
	Args: cobra.NoArgs,
	Run: func(cmd *cobra.Command, args []string) {
		runHealth()
	},
}

func init() {
	rootCmd.AddCommand(healthCmd)
	healthCmd.Flags().BoolVar(&healthAutobuilder, "autobuilder", false, "Show only the autobuilder JAR path")
	healthCmd.Flags().BoolVar(&healthAnalyzer, "analyzer", false, "Show only the analyzer JAR path")
	healthCmd.Flags().BoolVar(&healthRules, "rules", false, "Show only the built-in rules path (downloads on demand)")
	healthCmd.Flags().BoolVar(&healthRuntime, "runtime", false, "Show only the Java runtime path")
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
	for _, c := range components {
		value := c.path
		if c.version != "" {
			value = shortVersion(c.version) + "  " + c.path
		}
		if !c.present {
			value += "  " + out.Theme().Error.Render("missing")
		}
		sb.Field(c.name, value)
	}
	sb.Render()
}

// resolveHealthComponent resolves a component's path and presence. Only the
// rules are fetched on demand; the rest are reported as-is.
func resolveHealthComponent(key string) healthComponent {
	switch key {
	case "autobuilder":
		path, err := utils.GetAutobuilderJarPath(globals.Config.Autobuilder.Version)
		return healthComponent{"Autobuilder", globals.Config.Autobuilder.Version, path, err == nil && utils.PathExists(path)}
	case "analyzer":
		path, err := utils.GetAnalyzerJarPath(globals.Config.Analyzer.Version)
		return healthComponent{"Analyzer", globals.Config.Analyzer.Version, path, err == nil && utils.PathExists(path)}
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
	c := healthComponent{name: "Rules", version: globals.Config.Rules.Version}
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

// resolveRuntimeComponent reports the Java the analyzer uses: a managed JRE if
// present, otherwise system Java.
func resolveRuntimeComponent() healthComponent {
	c := healthComponent{name: "Runtime"}
	if jre := utils.FindExistingJRE(utils.ManagedJRETiers()); jre != nil {
		c.path = utils.JavaBinaryPath(jre.Path)
		c.version = "Java " + strconv.Itoa(globals.DefaultJavaVersion) + " · managed"
		c.present = true
		return c
	}
	if sys := java.DetectSystemJava(); sys != nil {
		c.path = sys.Path
		c.version = "Java " + sys.FullVersion + " · " + sys.Vendor
		c.present = true
		return c
	}
	c.version = "Java " + strconv.Itoa(globals.DefaultJavaVersion)
	if jre := utils.GetInstallJREPath(); jre != "" {
		c.path = utils.JavaBinaryPath(jre)
	}
	return c
}

// shortVersion strips the artifact-kind prefix (e.g. "rules/v0.1.1" → "v0.1.1").
func shortVersion(v string) string {
	if idx := strings.LastIndex(v, "/"); idx >= 0 {
		return v[idx+1:]
	}
	return v
}
