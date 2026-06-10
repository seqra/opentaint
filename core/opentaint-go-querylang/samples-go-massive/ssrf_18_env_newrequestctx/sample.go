package util

import (
	"context"
	"net/http"
	"os"
)

// Positive_newreqctx: env URL reaches URL arg of NewRequestWithContext.
func Positive_newreqctx() {
	u := os.Getenv("UPSTREAM")
	req, _ := http.NewRequestWithContext(context.Background(), "GET", u, nil)
	_ = req
}

// Negative_newreqctx_method_only: env value used only as method, not URL.
func Negative_newreqctx_method_only() {
	m := os.Getenv("HTTP_METHOD")
	req, _ := http.NewRequestWithContext(context.Background(), m, "https://internal.svc/api", nil)
	_ = req
}
