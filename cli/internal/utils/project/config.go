package project

import (
	"fmt"
	"os"
	"path/filepath"

	"gopkg.in/yaml.v2"
)

type Config struct {
	ProjectRoot  string        `yaml:"projectRoot,omitempty"`
	JavaProjects []JavaProject `yaml:"javaProjects,omitempty"`
	GoProjects   []GoProject   `yaml:"goProjects,omitempty"`
}

type JavaProject struct {
	SourceRoot    string   `yaml:"sourceRoot"`
	JavaToolchain string   `yaml:"javaToolchain,omitempty"`
	Modules       []Module `yaml:"modules"`
	Dependencies  []string `yaml:"dependencies,omitempty"`
}

type GoProject struct {
	ProjectDir string `yaml:"projectDir"`
	// GoToolchain is GOROOT of the Go installation that the autobuilder found. The analyzer runs
	// `go` from it, and skips a Go project that has none.
	GoToolchain string `yaml:"goToolchain,omitempty"`
}

// GoToolchainProblem tells why the analyzer skips the Go project: the project model records no Go
// toolchain for it, or the recorded one has no `go`. It is empty for a project that is analyzed.
func (p GoProject) GoToolchainProblem(projectModelPath string) string {
	if p.GoToolchain == "" {
		return "the project model has no Go toolchain"
	}
	goRoot := p.GoToolchain
	if !filepath.IsAbs(goRoot) {
		goRoot = filepath.Join(projectModelPath, goRoot)
	}
	for _, name := range []string{"go", "go.exe"} {
		if info, err := os.Stat(filepath.Join(goRoot, "bin", name)); err == nil && info.Mode().IsRegular() {
			return ""
		}
	}
	return fmt.Sprintf("the Go toolchain `%s` of the project model does not exist", p.GoToolchain)
}

// SkippedGoProjects returns why the analyzer skips Go projects of the model, one cause for each
// skipped project.
func (c *Config) SkippedGoProjects(projectModelPath string) []string {
	var problems []string
	for _, goProject := range c.GoProjects {
		if problem := goProject.GoToolchainProblem(projectModelPath); problem != "" {
			problems = append(problems, problem)
		}
	}
	return problems
}

type Module struct {
	ModuleSourceRoot string   `yaml:"moduleSourceRoot"`
	Packages         []string `yaml:"packages"`
	ModuleClasses    []string `yaml:"moduleClasses"`
}

type legacyConfig struct {
	SourceRoot    string   `yaml:"sourceRoot"`
	JavaToolchain string   `yaml:"javaToolchain,omitempty"`
	Modules       []Module `yaml:"modules"`
	Dependencies  []string `yaml:"dependencies,omitempty"`
}

func LoadConfig(projectModelPath string) (*Config, error) {
	projectYamlPath := filepath.Join(projectModelPath, "project.yaml")
	yamlData, err := os.ReadFile(projectYamlPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read project.yaml: %w", err)
	}

	var config Config
	if err := yaml.Unmarshal(yamlData, &config); err != nil {
		return nil, fmt.Errorf("failed to parse project.yaml: %w", err)
	}

	if len(config.JavaProjects) == 0 && len(config.GoProjects) == 0 {
		var legacy legacyConfig
		if err := yaml.Unmarshal(yamlData, &legacy); err != nil {
			return nil, fmt.Errorf("failed to parse project.yaml: %w", err)
		}
		if legacy.SourceRoot != "" || len(legacy.Modules) > 0 || len(legacy.Dependencies) > 0 {
			config.JavaProjects = []JavaProject{{
				SourceRoot:    legacy.SourceRoot,
				JavaToolchain: legacy.JavaToolchain,
				Modules:       legacy.Modules,
				Dependencies:  legacy.Dependencies,
			}}
		}
	}

	return &config, nil
}

func (c *Config) AllModules() []Module {
	var modules []Module
	for _, jp := range c.JavaProjects {
		modules = append(modules, jp.Modules...)
	}
	return modules
}

func (c *Config) AllDependencies() []string {
	var deps []string
	for _, jp := range c.JavaProjects {
		deps = append(deps, jp.Dependencies...)
	}
	return deps
}

func (c *Config) PrimarySourceRoot() string {
	if c.ProjectRoot != "" {
		return c.ProjectRoot
	}
	if len(c.JavaProjects) > 0 {
		return c.JavaProjects[0].SourceRoot
	}
	if len(c.GoProjects) > 0 {
		return c.GoProjects[0].ProjectDir
	}
	return ""
}

func GetSourceRoot(projectModelPath string) (string, error) {
	config, err := LoadConfig(projectModelPath)
	if err != nil {
		return "", err
	}

	sourceRoot := config.PrimarySourceRoot()
	if filepath.IsAbs(sourceRoot) {
		return sourceRoot, nil
	}

	return filepath.Join(projectModelPath, sourceRoot), nil
}
