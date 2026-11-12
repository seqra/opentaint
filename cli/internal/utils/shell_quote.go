package utils

import "regexp"

// placeholderPattern matches a placeholder of a next step, such as <source-path> or
// <group:artifact:version>, which stands for a value that the user fills in.
var placeholderPattern = regexp.MustCompile(`^<[a-z0-9:-]+>$`)

// ShellQuote quotes arg for the shell of the platform, so that a command in a next step works
// when it is pasted. It leaves an argument that needs no quotes, and a placeholder, as it is.
func ShellQuote(arg string) string {
	if placeholderPattern.MatchString(arg) {
		return arg
	}
	return platformShellQuote(arg)
}
