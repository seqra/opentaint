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
