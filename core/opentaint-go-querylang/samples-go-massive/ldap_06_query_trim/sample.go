package util

import (
	"fmt"
	"net/http"
	"strings"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_query_trim_sprintf: URL query passed through TrimSpace then into LDAP filter.
func Positive_query_trim_sprintf() {
	q := r.URL.Query().Get("sn")
	t := strings.TrimSpace(q)
	f := fmt.Sprintf("(sn=%s)", t)
	Sink_LdapSearch(f)
}

// Negative_query_const_trim: query read but constant filter sent.
func Negative_query_const_trim() {
	_ = r.URL.Query().Get("sn")
	Sink_LdapSearch("(sn=smith)")
}
