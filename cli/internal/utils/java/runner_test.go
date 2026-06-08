package java

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestUnsetJavaEnvironmentVariables(t *testing.T) {
	tests := []struct {
		name        string
		setupEnv    map[string]string
		expectedMsg []string
	}{
		{
			name: "unset_multiple_java_variables",
			setupEnv: map[string]string{
				"JAVA_HOME":        "/usr/lib/jvm/java-11",
				"JAVA_8_HOME":      "/usr/lib/jvm/java-8",
				"JAVA_17_HOME":     "/usr/lib/jvm/java-17",
				"JAVA_LATEST_HOME": "/usr/lib/jvm/java-latest",
				"NON_JAVA_VAR":     "should_remain",
			},
			expectedMsg: []string{
				"Unsetting JAVA_HOME",
				"Unsetting JAVA_8_HOME",
				"Unsetting JAVA_17_HOME",
				"Unsetting JAVA_LATEST_HOME",
			},
		},
		{
			name: "unset_partial_java_variables",
			setupEnv: map[string]string{
				"JAVA_HOME":    "/usr/lib/jvm/java-11",
				"JAVA_11_HOME": "/usr/lib/jvm/java-11",
				"OTHER_VAR":    "keep_this",
			},
			expectedMsg: []string{
				"Unsetting JAVA_HOME",
				"Unsetting JAVA_11_HOME",
			},
		},
		{
			name: "no_java_variables_set",
			setupEnv: map[string]string{
				"PATH": "/usr/bin",
				"HOME": "/home/user",
			},
			expectedMsg: []string{
				"JAVA_HOME not set",
				"JAVA_8_HOME not set",
				"JAVA_11_HOME not set",
				"JAVA_17_HOME not set",
				"JAVA_LATEST_HOME not set",
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Save original environment
			origEnv := make(map[string]string)
			javaVars := []string{"JAVA_HOME", "JAVA_8_HOME", "JAVA_11_HOME", "JAVA_17_HOME", "JAVA_LATEST_HOME"}
			for _, v := range javaVars {
				if val := os.Getenv(v); val != "" {
					origEnv[v] = val
				}
			}

			// Clear Java environment variables first
			for _, v := range javaVars {
				_ = os.Unsetenv(v)
			}

			// Setup test environment
			for key, value := range tt.setupEnv {
				_ = os.Setenv(key, value)
			}

			// Call function under test
			unsetJavaEnvironmentVariables()

			// Verify Java variables are unset
			for _, v := range javaVars {
				if val := os.Getenv(v); val != "" {
					t.Errorf("Expected %s to be unset, but found value: %s", v, val)
				}
			}

			// Verify non-Java variables remain
			for key, expectedValue := range tt.setupEnv {
				if !strings.HasPrefix(key, "JAVA_") {
					if actual := os.Getenv(key); actual != expectedValue {
						t.Errorf("Expected %s=%s to remain, but got %s", key, expectedValue, actual)
					}
				}
			}

			// Cleanup: restore original environment
			for _, v := range javaVars {
				_ = os.Unsetenv(v)
				if val, exists := origEnv[v]; exists {
					_ = os.Setenv(v, val)
				}
			}
			for key := range tt.setupEnv {
				if !strings.HasPrefix(key, "JAVA_") {
					_ = os.Unsetenv(key)
				}
			}
		})
	}
}

func TestGetCleanEnvironment(t *testing.T) {
	tests := []struct {
		name          string
		setupEnv      map[string]string
		shouldExclude []string
		shouldInclude []string
	}{
		{
			name: "exclude_all_java_variables",
			setupEnv: map[string]string{
				"JAVA_HOME":        "/usr/lib/jvm/java-11",
				"JAVA_8_HOME":      "/usr/lib/jvm/java-8",
				"JAVA_11_HOME":     "/usr/lib/jvm/java-11",
				"JAVA_17_HOME":     "/usr/lib/jvm/java-17",
				"JAVA_LATEST_HOME": "/usr/lib/jvm/java-latest",
				"PATH":             "/usr/bin:/bin",
				"HOME":             "/home/user",
				"USER":             "testuser",
			},
			shouldExclude: []string{"JAVA_HOME", "JAVA_8_HOME", "JAVA_11_HOME", "JAVA_17_HOME", "JAVA_LATEST_HOME"},
			shouldInclude: []string{"PATH", "HOME", "USER"},
		},
		{
			name: "exclude_partial_java_variables",
			setupEnv: map[string]string{
				"JAVA_HOME":   "/usr/lib/jvm/java-11",
				"JAVA_8_HOME": "/usr/lib/jvm/java-8",
				"PATH":        "/usr/bin:/bin",
				"SHELL":       "/bin/bash",
			},
			shouldExclude: []string{"JAVA_HOME", "JAVA_8_HOME"},
			shouldInclude: []string{"PATH", "SHELL"},
		},
		{
			name: "no_java_variables_in_environment",
			setupEnv: map[string]string{
				"PATH":  "/usr/bin:/bin",
				"HOME":  "/home/user",
				"SHELL": "/bin/bash",
			},
			shouldExclude: []string{},
			shouldInclude: []string{"PATH", "HOME", "SHELL"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Save original environment
			origEnv := os.Environ()

			// Clear environment
			os.Clearenv()

			// Setup test environment
			for key, value := range tt.setupEnv {
				_ = os.Setenv(key, value)
			}

			// Create runner and get clean environment
			runner := &javaRunner{}
			cleanEnv := runner.getCleanEnvironment()

			// Convert to map for easier testing
			envMap := make(map[string]string)
			for _, env := range cleanEnv {
				parts := strings.SplitN(env, "=", 2)
				if len(parts) == 2 {
					envMap[parts[0]] = parts[1]
				}
			}

			// Verify excluded variables are not present
			for _, excludedVar := range tt.shouldExclude {
				if _, exists := envMap[excludedVar]; exists {
					t.Errorf("Expected %s to be excluded from clean environment, but it was present", excludedVar)
				}
			}

			// Verify included variables are present with correct values
			for _, includedVar := range tt.shouldInclude {
				expectedValue, expectedExists := tt.setupEnv[includedVar]
				actualValue, actualExists := envMap[includedVar]

				if !expectedExists {
					continue // Skip if variable wasn't set in test
				}

				if !actualExists {
					t.Errorf("Expected %s to be included in clean environment, but it was missing", includedVar)
				} else if actualValue != expectedValue {
					t.Errorf("Expected %s=%s in clean environment, but got %s=%s", includedVar, expectedValue, includedVar, actualValue)
				}
			}

			// Restore original environment
			os.Clearenv()
			for _, env := range origEnv {
				parts := strings.SplitN(env, "=", 2)
				if len(parts) == 2 {
					_ = os.Setenv(parts[0], parts[1])
				}
			}
		})
	}
}

func TestNewJavaRunner(t *testing.T) {
	runner := NewJavaRunner()

	// Type assertion to access internal fields
	jr, ok := runner.(*javaRunner)
	if !ok {
		t.Fatal("Expected *javaRunner type")
	}

	if jr.trySystemStrategy {
		t.Error("Expected trySystemStrategy to be false by default")
	}

	if jr.specificStrategy != nil {
		t.Error("Expected specificStrategy to be nil by default")
	}
}

func TestJavaRunner_TrySystem(t *testing.T) {
	runner := NewJavaRunner()
	runner = runner.TrySystem()

	jr, ok := runner.(*javaRunner)
	if !ok {
		t.Fatal("Expected *javaRunner type")
	}

	if !jr.trySystemStrategy {
		t.Error("Expected trySystemStrategy to be true after TrySystem()")
	}
}

func TestJavaRunner_TrySpecificVersion(t *testing.T) {
	tests := []struct {
		name    string
		version int
	}{
		{"java_8", 8},
		{"java_11", 11},
		{"java_17", 17},
		{"java_21", 21},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			runner := NewJavaRunner()
			runner = runner.TrySpecificVersion(tt.version)

			jr, ok := runner.(*javaRunner)
			if !ok {
				t.Fatal("Expected *javaRunner type")
			}

			if jr.specificStrategy == nil {
				t.Error("Expected specificStrategy to be set after TrySpecificVersion()")
			} else if *jr.specificStrategy != tt.version {
				t.Errorf("Expected specificStrategy to be %d, got %d", tt.version, *jr.specificStrategy)
			}
		})
	}
}

func TestJavaRunner_GetJavaResolutions_NoStrategy(t *testing.T) {
	runner := NewJavaRunner()
	resolutions := runner.GetJavaResolutions()

	if len(resolutions) != 1 {
		t.Errorf("Expected 1 resolution for no strategy, got %d", len(resolutions))
	}

	// Test that the resolution returns an error
	_, _, err := resolutions[0]()
	if err == nil {
		t.Error("Expected error when no strategy is configured")
	}
	if !strings.Contains(err.Error(), "no Java resolution strategies configured") {
		t.Errorf("Expected specific error message, got: %s", err.Error())
	}
}

func TestJavaRunner_GetJavaResolutions_SystemStrategy(t *testing.T) {
	runner := NewJavaRunner().TrySystem()
	resolutions := runner.GetJavaResolutions()

	if len(resolutions) != 1 {
		t.Errorf("Expected 1 resolution for system strategy, got %d", len(resolutions))
	}

	// Note: We can't easily test the actual resolution without mocking the system detection
	// This test verifies the strategy is set up correctly
}

func TestJavaRunner_GetJavaResolutions_SpecificStrategy(t *testing.T) {
	runner := NewJavaRunner().TrySpecificVersion(11)
	resolutions := runner.GetJavaResolutions()

	// 2 resolutions: bundled JRE (first) + specific version download (fallback)
	if len(resolutions) != 2 {
		t.Errorf("Expected 2 resolutions for specific strategy (bundled + download), got %d", len(resolutions))
	}
}

func TestJavaRunner_GetJavaResolutions_BothStrategies(t *testing.T) {
	runner := NewJavaRunner().TrySystem().TrySpecificVersion(11)
	resolutions := runner.GetJavaResolutions()

	if len(resolutions) != 1 {
		t.Errorf("Expected 1 resolution for fallback strategy, got %d", len(resolutions))
	}
}

func TestJavaRunner_ExecuteJavaCommand_NoArgs(t *testing.T) {
	runner := NewJavaRunner()

	cmdErr, err := runner.ExecuteJavaCommand([]string{}, func(error) bool { return true })

	if cmdErr != nil {
		t.Error("Expected no JavaCommandError for missing arguments")
	}
	if err == nil {
		t.Error("Expected error when no arguments provided")
	}
	if !strings.Contains(err.Error(), "no Java command arguments provided") {
		t.Errorf("Expected specific error message, got: %s", err.Error())
	}
}

func TestEnvironmentVariableList(t *testing.T) {
	// Test that we're tracking the correct Java environment variables
	expectedVars := []string{
		"JAVA_HOME",
		"JAVA_8_HOME",
		"JAVA_11_HOME",
		"JAVA_17_HOME",
		"JAVA_LATEST_HOME",
	}

	// This test ensures consistency between unsetJavaEnvironmentVariables
	// and getCleanEnvironment methods
	runner := &javaRunner{}

	// Setup environment with all Java variables
	for _, v := range expectedVars {
		_ = os.Setenv(v, "/test/path")
	}
	_ = os.Setenv("NON_JAVA", "keep")

	cleanEnv := runner.getCleanEnvironment()

	// Check that Java variables are excluded
	envMap := make(map[string]string)
	for _, env := range cleanEnv {
		parts := strings.SplitN(env, "=", 2)
		if len(parts) == 2 {
			envMap[parts[0]] = parts[1]
		}
	}

	for _, javaVar := range expectedVars {
		if _, exists := envMap[javaVar]; exists {
			t.Errorf("Java variable %s should be excluded from clean environment", javaVar)
		}
	}

	if _, exists := envMap["NON_JAVA"]; !exists {
		t.Error("Non-Java variable should be included in clean environment")
	}

	// Cleanup
	for _, v := range expectedVars {
		_ = os.Unsetenv(v)
	}
	_ = os.Unsetenv("NON_JAVA")
}

// --- WithExtraEnv: builder semantics ---

func TestJavaRunner_WithExtraEnv_NilAndEmptyAreNoOps(t *testing.T) {
	j := &javaRunner{}

	ret := j.WithExtraEnv(nil)
	if jr, ok := ret.(*javaRunner); !ok || jr != j {
		t.Fatalf("WithExtraEnv(nil) should return the same usable *javaRunner")
	}
	if j.extraEnv != nil {
		t.Errorf("WithExtraEnv(nil) should not allocate extraEnv, got %v", j.extraEnv)
	}

	ret = j.WithExtraEnv(map[string]string{})
	if jr, ok := ret.(*javaRunner); !ok || jr != j {
		t.Fatalf("WithExtraEnv(empty) should return the same usable *javaRunner")
	}
	if j.extraEnv != nil {
		t.Errorf("WithExtraEnv(empty) should not allocate extraEnv, got %v", j.extraEnv)
	}
}

func TestJavaRunner_WithExtraEnv_MergeLaterWins(t *testing.T) {
	j := &javaRunner{}
	j.WithExtraEnv(map[string]string{"A": "1", "B": "2"})
	j.WithExtraEnv(map[string]string{"B": "20", "C": "3"})

	want := map[string]string{"A": "1", "B": "20", "C": "3"}
	if len(j.extraEnv) != len(want) {
		t.Fatalf("extraEnv = %v, want %v", j.extraEnv, want)
	}
	for k, v := range want {
		if j.extraEnv[k] != v {
			t.Errorf("extraEnv[%q] = %q, want %q (later WithExtraEnv call should win)", k, j.extraEnv[k], v)
		}
	}
}

// --- executeWithJava: extra env reaches the child process ---
//
// These tests re-execute the test binary itself as the "java" process via
// executeWithJava and have the child (TestHelperProcess) dump its environment
// to a file, so we can assert what actually ended up in cmd.Env on each
// resolution strategy. No real JVM is required.

// runHelperEnv runs executeWithJava with the test binary as the child process
// and returns the environment that child observed. The GO_WANT_HELPER_PROCESS
// gate is injected through the runner's own extra-env mechanism, so if extra
// env failed to reach the child the helper would never activate and the env
// file would be missing (surfaced as a clear failure here).
func runHelperEnv(t *testing.T, j *javaRunner, strategy ResolutionStrategy) map[string]string {
	t.Helper()

	outFile := filepath.Join(t.TempDir(), "child-env.txt")
	j.WithExtraEnv(map[string]string{"GO_WANT_HELPER_PROCESS": "1"})

	args := []string{"-test.run=TestHelperProcess", "--", outFile}
	cmdErr, err := j.executeWithJava(os.Args[0], strategy, args, func(error) bool { return true })
	if err != nil {
		t.Fatalf("executeWithJava returned setup error: %v", err)
	}
	if cmdErr != nil {
		t.Fatalf("helper process exited non-zero: %v", cmdErr)
	}

	raw, err := os.ReadFile(outFile)
	if err != nil {
		t.Fatalf("reading child env file (extra env likely not propagated to child): %v", err)
	}

	env := map[string]string{}
	for _, line := range strings.Split(string(raw), "\n") {
		if line == "" {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) == 2 {
			env[parts[0]] = parts[1]
		}
	}
	return env
}

func TestJavaRunner_ExtraEnv_SystemStrategy_AppendsAndPreservesInherited(t *testing.T) {
	// Set an inherited variable in the parent environment. On the System path
	// cmd.Env starts nil and must be seeded from os.Environ() so inherited
	// variables survive alongside the appended extra entry.
	t.Setenv("OPENTAINT_INHERITED_SYS", "inherited-value")

	j := (&javaRunner{}).WithExtraEnv(map[string]string{
		"OPENTAINT_EXTRA_ENV_TEST": "extra-value",
	}).(*javaRunner)

	env := runHelperEnv(t, j, System)

	if got := env["OPENTAINT_EXTRA_ENV_TEST"]; got != "extra-value" {
		t.Errorf("child OPENTAINT_EXTRA_ENV_TEST = %q, want %q (extra env not appended on System path)", got, "extra-value")
	}
	if got := env["OPENTAINT_INHERITED_SYS"]; got != "inherited-value" {
		t.Errorf("child OPENTAINT_INHERITED_SYS = %q, want %q (inherited env dropped; cmd.Env not seeded from os.Environ() on System path)", got, "inherited-value")
	}
}

func TestJavaRunner_ExtraEnv_SpecificStrategy_AppendsAfterCleanEnv(t *testing.T) {
	// Specific strategy uses the clean environment (Java vars stripped) and then
	// appends the extra entries.
	t.Setenv("OPENTAINT_INHERITED_SPECIFIC", "kept-value")
	t.Setenv("JAVA_HOME", "/fake/java/home")

	j := (&javaRunner{}).WithExtraEnv(map[string]string{
		"OPENTAINT_EXTRA_ENV_TEST": "extra-value",
	}).(*javaRunner)

	env := runHelperEnv(t, j, Specific)

	if got := env["OPENTAINT_EXTRA_ENV_TEST"]; got != "extra-value" {
		t.Errorf("child OPENTAINT_EXTRA_ENV_TEST = %q, want %q (extra env not appended on Specific path)", got, "extra-value")
	}
	if got := env["OPENTAINT_INHERITED_SPECIFIC"]; got != "kept-value" {
		t.Errorf("child OPENTAINT_INHERITED_SPECIFIC = %q, want %q (non-Java inherited env should survive clean env)", got, "kept-value")
	}
	if _, present := env["JAVA_HOME"]; present {
		t.Errorf("child JAVA_HOME should be stripped by clean environment on Specific path, but it was present")
	}
}

// TestHelperProcess is not a real test. It is re-executed as the child "java"
// process by the env-injection tests above. When the GO_WANT_HELPER_PROCESS
// gate (passed through the runner's extra env) is present it writes the child's
// full environment to the file named after "--" and exits; otherwise it is a
// no-op for normal test runs.
func TestHelperProcess(t *testing.T) {
	if os.Getenv("GO_WANT_HELPER_PROCESS") != "1" {
		return
	}

	args := os.Args
	for len(args) > 0 {
		if args[0] == "--" {
			args = args[1:]
			break
		}
		args = args[1:]
	}
	if len(args) < 1 {
		fmt.Fprintln(os.Stderr, "helper: missing output file argument")
		os.Exit(2)
	}
	if err := os.WriteFile(args[0], []byte(strings.Join(os.Environ(), "\n")), 0o644); err != nil {
		fmt.Fprintln(os.Stderr, "helper: write env:", err)
		os.Exit(3)
	}
	os.Exit(0)
}
