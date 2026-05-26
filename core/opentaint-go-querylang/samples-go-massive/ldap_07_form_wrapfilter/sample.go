package util

import (
	"net/http"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// wrapFilter wraps a user value as an LDAP equality clause.
func wrapFilter(s string) string {
	return "(&(objectClass=user)(uid=" + s + "))"
}

// Positive_form_wrapfilter: FormValue passed through wrapFilter helper into LDAP sink.
func Positive_form_wrapfilter() {
	u := r.FormValue("u")
	f := wrapFilter(u)
	Sink_LdapSearch(f)
}

// Negative_form_unused_wrap: FormValue read but constant filter used.
func Negative_form_unused_wrap() {
	_ = r.FormValue("u")
	Sink_LdapSearch("(&(objectClass=user)(uid=admin))")
}
