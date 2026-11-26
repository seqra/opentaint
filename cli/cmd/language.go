package cmd

import (
	"errors"
	"fmt"
	"strings"

	"github.com/seqra/opentaint/internal/testproject"
)

// parseLanguage returns the value of a --language flag, java or go. It stops the command on
// another value.
func parseLanguage(value string) string {
	language := strings.ToLower(strings.TrimSpace(value))
	if language != "java" && language != "go" {
		out.Fatalf("Invalid --language value `%s`, use java or go", value)
	}
	return language
}

// languageName is the name of a --language value in a sentence.
func languageName(language string) string {
	if language == "go" {
		return "Go"
	}
	return "Java"
}

// checkGoDependencies stops the command on a --dependency value that is not a valid
// module@version.
func checkGoDependencies(dependencies []string) {
	for _, dependency := range dependencies {
		err := testproject.CheckGoDependency(dependency)
		if errors.Is(err, testproject.ErrNotModuleVersion) {
			out.Fatalf("Invalid --dependency value `%s`, use module@version", dependency)
		}
		if err != nil {
			out.Fatal(fmt.Sprintf("Invalid --dependency value `%s`", dependency), err)
		}
	}
}
