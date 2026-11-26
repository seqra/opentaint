package testproject

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/utils"
)

// Language returns the language of the test project in dir, java or go, or "" when dir holds
// no test project.
func Language(dir string) string {
	switch {
	case isFile(filepath.Join(dir, buildFileName)):
		return "java"
	case isFile(filepath.Join(dir, goModuleFileName)):
		return "go"
	}
	return ""
}

const goModuleFileName = "go.mod"

func isFile(path string) bool {
	info, err := os.Stat(path)
	return err == nil && !info.IsDir()
}

const buildFileName = "build.gradle.kts"

func Bootstrap(outputDir, projectName string, dependencies []string) error {
	return BootstrapWithLocalJars(outputDir, projectName, dependencies, nil)
}

// BootstrapWithLocalJars adds project-relative jars to the compile-only classpath.
func BootstrapWithLocalJars(outputDir, projectName string, dependencies, localJars []string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(outputDir, buildFileName):         buildGradle(dependencies, localJars),
		filepath.Join(outputDir, "settings.gradle.kts"): settingsGradle(projectName),
	})
}

func buildGradle(dependencies, localJars []string) []byte {
	var sb strings.Builder
	sb.WriteString(`plugins {
    java
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

repositories {
    mavenCentral()
}

dependencies {
`)
	for _, jar := range localJars {
		fmt.Fprintf(&sb, "    compileOnly(files(%q))\n", filepath.ToSlash(jar))
	}
	for _, dep := range dependencies {
		fmt.Fprintf(&sb, "    compileOnly(%q)\n", dep)
	}
	sb.WriteString("}\n")
	return []byte(sb.String())
}

func settingsGradle(projectName string) []byte {
	return fmt.Appendf(nil, "rootProject.name = %q\n", projectName)
}
