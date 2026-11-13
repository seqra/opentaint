package cmd

import "strings"

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
