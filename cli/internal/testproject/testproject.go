package testproject

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/seqra/opentaint/internal/testutil"
	"github.com/seqra/opentaint/internal/utils"
)

func Bootstrap(outputDir, projectName string, dependencies []string, testUtilJarSrc string) error {
	if err := utils.CopyFile(testUtilJarSrc, filepath.Join(outputDir, "libs", testutil.JarName)); err != nil {
		return fmt.Errorf("copy test-util JAR: %w", err)
	}
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(outputDir, "build.gradle.kts"):    buildGradle(dependencies),
		filepath.Join(outputDir, "settings.gradle.kts"): settingsGradle(projectName),
	})
}

func buildGradle(dependencies []string) []byte {
	var sb strings.Builder
	fmt.Fprintf(&sb, `plugins {
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
    compileOnly(files("libs/%s"))
`, testutil.JarName)
	for _, dep := range dependencies {
		fmt.Fprintf(&sb, "    compileOnly(%q)\n", dep)
	}
	sb.WriteString("}\n")
	return []byte(sb.String())
}

func settingsGradle(projectName string) []byte {
	return fmt.Appendf(nil, "rootProject.name = %q\n", projectName)
}
