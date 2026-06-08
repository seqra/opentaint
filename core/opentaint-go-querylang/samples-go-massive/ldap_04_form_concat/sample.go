package util

import (
	"net/http"
)

var r *http.Request

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_form_concat: FormValue concatenated into LDAP search filter.
func Positive_form_concat() {
	mail := r.FormValue("mail")
	f := "(mail=" + mail + ")"
	Sink_LdapSearch(f)
}

// Negative_form_concat_const: FormValue read but constant filter used.
func Negative_form_concat_const() {
	_ = r.FormValue("mail")
	Sink_LdapSearch("(mail=root@example.com)")
}
