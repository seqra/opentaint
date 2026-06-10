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

	"github.com/seqra/opentaint/internal/utils"
)

//go:generate go run ./generate_jar.go

//go:embed jar/*
var jarFiles embed.FS

const JarName = "opentaint-sast-test-util.jar"

func ResolveJar() (string, error) {
	if libPath := utils.GetBundledLibPath(); libPath != "" {
		candidate := filepath.Join(libPath, JarName)
		if utils.PathExists(candidate) {
			return candidate, nil
		}
	}

	if libPath := utils.GetInstallLibPath(); libPath != "" {
		candidate := filepath.Join(libPath, JarName)
		if utils.PathExists(candidate) {
			return candidate, nil
		}
	}

	if exe, err := os.Executable(); err == nil {
		exe, _ = filepath.EvalSymlinks(exe)
		dir := filepath.Dir(exe)
		for range 4 {
			candidate := filepath.Join(dir, "core", "opentaint-sast-test-util", "build", "libs", JarName)
			if utils.PathExists(candidate) {
				return candidate, nil
			}
			dir = filepath.Dir(dir)
		}
	}

	if extracted, err := extractJar(); err == nil {
		return extracted, nil
	}

	return "", fmt.Errorf(
		"%s not found; build it with 'cd core && ./gradlew :opentaint-sast-test-util:jar' or reinstall opentaint",
		JarName,
	)
}

func contentHash(jarData []byte) string {
	h := sha256.Sum256(jarData)
	return hex.EncodeToString(h[:])
}

func extractJar() (string, error) {
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

	if !needsExtract(markerPath, wantHash) && utils.PathExists(extractPath) {
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
