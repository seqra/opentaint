package util

import (
	"bufio"
	"net/http"
	"os"
	"strings"
)

// Positive_stdin_post: URL read from stdin (representing decoded-from-input config)
// posted to. SSRF — attacker controls destination.
func Positive_stdin_post() {
	line, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	line = strings.TrimSpace(line)
	_, _ = http.Post(line, "application/json", nil)
}

// Negative_stdin_body_only: stdin reaches body, not URL — focus-metavariable
// on $URL means this should NOT be flagged.
func Negative_stdin_body_only() {
	body, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	_, _ = http.Post("https://internal.svc/log", "text/plain", strings.NewReader(body))
}
