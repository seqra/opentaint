package globals

import (
	_ "embed"
	"fmt"
	"runtime"
	"time"

	"gopkg.in/yaml.v2"
)

//go:embed versions.yaml
var versionsYAML []byte

type versions struct {
	Analyzer    string `yaml:"analyzer"`
	Autobuilder string `yaml:"autobuilder"`
	Rules       string `yaml:"rules"`
	GoServer    string `yaml:"go-server"`
	Java        int    `yaml:"java"`
}

var BindVersions = func() versions {
	var v versions
	if err := yaml.Unmarshal(versionsYAML, &v); err != nil {
		panic(fmt.Sprintf("failed to parse embedded versions.yaml: %v", err))
	}
	return v
}()

var (
	AnalyzerBindVersion    = BindVersions.Analyzer
	AutobuilderBindVersion = BindVersions.Autobuilder
	RulesBindVersion       = BindVersions.Rules
	GoServerBindVersion    = BindVersions.GoServer
	DefaultJavaVersion     = BindVersions.Java
)

const RepoOwner = "seqra"
const RepoName = "opentaint"

const AutobuilderAssetName = "opentaint-project-auto-builder.jar"
const AnalyzerAssetName = "opentaint-project-analyzer.jar"
const RulesAssetName = "opentaint-rules.tar.gz"

// GoServerAssetNamePrefix is the per-platform go-ssa-server asset filename prefix.
const GoServerAssetNamePrefix = "go-ssa-server_"

// GoServerAssetName returns the platform-specific name of the go-ssa-server
// release asset. The name follows the contract of the release pipeline:
// "go-ssa-server_<GOOS>_<GOARCH>", with ".exe" added on windows. It uses the
// raw runtime.GOOS and runtime.GOARCH values (no Adoptium-style mapping).
func GoServerAssetName() string {
	name := fmt.Sprintf("%s%s_%s", GoServerAssetNamePrefix, runtime.GOOS, runtime.GOARCH)
	if runtime.GOOS == "windows" {
		name += ".exe"
	}
	return name
}

type Scan struct {
	Timeout       time.Duration `mapstructure:"timeout"`
	MaxMemory     string        `mapstructure:"max_memory"`
	CodeFlowLimit int64         `mapstructure:"code_flow_limit"`
}

type Output struct {
	Debug bool   `mapstructure:"debug"`
	Color string `mapstructure:"color"`
	Quiet bool   `mapstructure:"quiet"`
}

type Github struct {
	Token string `mapstructure:"token"`
}

type Analyzer struct {
	Version string `mapstructure:"version"`
	JarPath string `mapstructure:"jar_path"`
}

type Autobuilder struct {
	Version string `mapstructure:"version"`
	JarPath string `mapstructure:"jar_path"`
}

type Rules struct {
	Version string `mapstructure:"version"`
	// Only and Exclude control which rules the analyzer runs. They are rule
	// selection, not suppression: an excluded rule never loads, so it produces
	// nothing in the report. Entries match a full "path.yaml:id", a bare rule
	// name, or a glob over either.
	Only    []string `mapstructure:"only"`
	Exclude []string `mapstructure:"exclude"`
}

type GoServer struct {
	Version string `mapstructure:"version"`
	Binary  string `mapstructure:"binary"`
}

type Java struct {
	Version int `mapstructure:"version"`
}

type ConfigType struct {
	Scan   Scan   `mapstructure:"scan"`
	Output Output `mapstructure:"output"`

	Github      Github      `mapstructure:"github"`
	Analyzer    Analyzer    `mapstructure:"analyzer"`
	Autobuilder Autobuilder `mapstructure:"autobuilder"`
	Rules       Rules       `mapstructure:"rules"`
	GoServer    GoServer    `mapstructure:"go-server"`
	Java        Java        `mapstructure:"java"`
	Owner       string      `mapstructure:"owner"`
	Repo        string      `mapstructure:"repo"`
	SkipVerify  bool        `mapstructure:"skip-verify"`
}

var Config ConfigType

var LogPath string

var ConfigFile string

// GetVersionsYAML returns the raw embedded versions.yaml content.
func GetVersionsYAML() []byte {
	return versionsYAML
}
