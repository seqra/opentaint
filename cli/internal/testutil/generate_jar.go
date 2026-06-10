//go:build ignore

package main

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

const (
	jarName   = "opentaint-sast-test-util.jar"
	sourceJar = "../../../core/opentaint-sast-test-util/build/libs/opentaint-sast-test-util.jar"
	outputDir = "jar"
)

func main() {
	if err := utils.CopyFile(sourceJar, filepath.Join(outputDir, jarName)); err != nil {
		fmt.Fprintf(os.Stderr, "generate test-util jar: %v; build it with 'cd ../../../core && ./gradlew :opentaint-sast-test-util:jar'\n", err)
		os.Exit(1)
	}
}
