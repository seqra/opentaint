// Package testutil embeds the opentaint-sast-test-util.jar and extracts it
// on demand to ~/.opentaint/test-util/ when no bundled copy is available.
package testutil

import (
	"crypto/sha256"
	"embed"
	"encoding/hex"
	"fmt"
	"os"
	"path"
	"path/filepath"
	"strings"
)

//go:generate go run ./generate_jar.go

//go:embed jar/*
var jarFiles embed.FS

// JarName is the filename of the test-util JAR.
const JarName = "opentaint-sast-test-util.jar"

func contentHash(jarData []byte) string {
	h := sha256.Sum256(jarData)
	return hex.EncodeToString(h[:])
}

// ExtractJar extracts the embedded test-util JAR to ~/.opentaint/test-util/
// and returns the path to the extracted JAR. Uses a SHA-256 content hash
// marker for staleness detection so the extracted copy is refreshed when the
// binary is rebuilt with a newer JAR.
func ExtractJar() (string, error) {
	jarData, err := embeddedJarData()
	if err != nil {
		return "", err
	}

	home, err := os.UserHomeDir()
	if err != nil {
		return "", fmt.Errorf("cannot determine home directory: %w", err)
	}
	extractDir := filepath.Join(home, ".opentaint", "test-util")
	extractPath := filepath.Join(extractDir, JarName)
	markerPath := filepath.Join(extractDir, ".content-hash")
	wantHash := contentHash(jarData)

	if !needsExtract(markerPath, wantHash) && fileExists(extractPath) {
		return extractPath, nil
	}

	if err := os.MkdirAll(extractDir, 0o755); err != nil {
		return "", fmt.Errorf("create dir: %w", err)
	}
	if err := os.WriteFile(extractPath, jarData, 0o644); err != nil {
		return "", fmt.Errorf("write JAR: %w", err)
	}
	if err := os.WriteFile(markerPath, []byte(wantHash+"\n"), 0o644); err != nil {
		return "", fmt.Errorf("write marker: %w", err)
	}
	return extractPath, nil
}

func embeddedJarData() ([]byte, error) {
	jarData, err := jarFiles.ReadFile(path.Join("jar", JarName))
	if err != nil {
		return nil, fmt.Errorf("embedded %s is missing; build it with 'cd core && ./gradlew :opentaint-sast-test-util:jar', then run 'cd cli && go generate ./internal/testutil': %w", JarName, err)
	}
	return jarData, nil
}

func needsExtract(markerPath, wantHash string) bool {
	data, err := os.ReadFile(markerPath)
	if err != nil {
		return true
	}
	return strings.TrimSpace(string(data)) != wantHash
}

func fileExists(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}
