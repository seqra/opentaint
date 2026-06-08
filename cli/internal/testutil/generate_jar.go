//go:build ignore

package main

import (
	"fmt"
	"io"
	"os"
	"path/filepath"
)

const (
	jarName   = "opentaint-sast-test-util.jar"
	sourceJar = "../../../core/opentaint-sast-test-util/build/libs/opentaint-sast-test-util.jar"
	outputDir = "jar"
)

func main() {
	if err := copyJar(); err != nil {
		fmt.Fprintf(os.Stderr, "generate test-util jar: %v\n", err)
		os.Exit(1)
	}
}

func copyJar() error {
	if err := os.MkdirAll(outputDir, 0o755); err != nil {
		return fmt.Errorf("create %s: %w", outputDir, err)
	}

	in, err := os.Open(sourceJar)
	if err != nil {
		return fmt.Errorf("open %s: %w; build it with 'cd ../../../core && ./gradlew :opentaint-sast-test-util:jar'", sourceJar, err)
	}
	defer in.Close()

	outPath := filepath.Join(outputDir, jarName)
	out, err := os.Create(outPath)
	if err != nil {
		return fmt.Errorf("create %s: %w", outPath, err)
	}
	defer out.Close()

	if _, err := io.Copy(out, in); err != nil {
		return fmt.Errorf("copy %s to %s: %w", sourceJar, outPath, err)
	}

	return nil
}
