package testproject

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/utils"
)

func Bootstrap(outputDir, projectName string, dependencies []string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(outputDir, "build.gradle.kts"):    buildGradle(dependencies),
		filepath.Join(outputDir, "settings.gradle.kts"): settingsGradle(projectName),
	})
}

func buildGradle(dependencies []string) []byte {
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
	for _, dep := range dependencies {
		fmt.Fprintf(&sb, "    compileOnly(%q)\n", dep)
	}
	sb.WriteString("}\n")
	return []byte(sb.String())
}

func settingsGradle(projectName string) []byte {
	return fmt.Appendf(nil, "rootProject.name = %q\n", projectName)
}
