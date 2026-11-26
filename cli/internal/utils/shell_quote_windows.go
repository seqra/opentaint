//go:build windows

package utils

import "syscall"

// platformShellQuote quotes arg as a Windows program reads its command line, with double quotes
// only when arg needs them. cmd.exe and PowerShell both pass such an argument through.
func platformShellQuote(arg string) string {
	return syscall.EscapeArg(arg)
}
