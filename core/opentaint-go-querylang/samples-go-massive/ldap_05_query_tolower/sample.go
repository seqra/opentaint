package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_query_lower: URL query value lowercased then placed into LDAP filter.
func Positive_query_lower() {
	q := r.URL.Query().Get("dept")
	lo := strings.ToLower(q)
	Sink_LdapSearch("(ou=" + lo + ")")
}

// Negative_query_const: query read but constant filter sent.
func Negative_query_const() {
	_ = r.URL.Query().Get("dept")
	Sink_LdapSearch("(ou=eng)")
}
