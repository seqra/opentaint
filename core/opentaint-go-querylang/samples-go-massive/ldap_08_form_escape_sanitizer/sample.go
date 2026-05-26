package util

import (
	"net/http"
	"strings"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// escapeLdapFilter escapes LDAP metacharacters per RFC 4515.
func escapeLdapFilter(s string) string {
	s = strings.ReplaceAll(s, `\`, `\5c`)
	s = strings.ReplaceAll(s, `*`, `\2a`)
	s = strings.ReplaceAll(s, `(`, `\28`)
	s = strings.ReplaceAll(s, `)`, `\29`)
	return s
}

// Positive_unsanitized: FormValue into LDAP filter without escaping.
func Positive_unsanitized() {
	u := r.FormValue("uid")
	Sink_LdapSearch("(uid=" + u + ")")
}

// Negative_escaped: FormValue passed through escapeLdapFilter sanitizer.
func Negative_escaped() {
	u := r.FormValue("uid")
	u = escapeLdapFilter(u)
	Sink_LdapSearch("(uid=" + u + ")")
}
