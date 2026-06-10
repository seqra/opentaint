package util

import (
	"fmt"
	"net/http"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_form_sprintf: FormValue formatted into LDAP filter.
func Positive_form_sprintf() {
	u := r.FormValue("user")
	f := fmt.Sprintf("(uid=%s)", u)
	Sink_LdapSearch(f)
}

// Negative_form_const: FormValue read but constant filter used.
func Negative_form_const() {
	_ = r.FormValue("user")
	Sink_LdapSearch("(uid=guest)")
}
