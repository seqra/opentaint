//go:build !windows

package utils

import "strings"

// platformShellQuote quotes arg for a POSIX shell, with single quotes only when arg needs them.
func platformShellQuote(arg string) string {
	if arg != "" && !strings.ContainsFunc(arg, shellUnsafe) {
		return arg
	}
	return "'" + strings.ReplaceAll(arg, "'", `'\''`) + "'"
}

func shellUnsafe(r rune) bool {
	switch {
	case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9':
		return false
	case strings.ContainsRune("_@%+=:,./-", r):
		return false
	}
	return true
}
