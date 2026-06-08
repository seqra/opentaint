package util

import (
	"os"
)

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_env_concat: env concatenated directly into LDAP filter.
func Positive_env_concat() {
	cn := os.Getenv("LDAP_CN")
	f := "(cn=" + cn + ")"
	Sink_LdapSearch(f)
}

// Negative_const_concat: env read but constant filter used.
func Negative_const_concat() {
	_ = os.Getenv("LDAP_CN")
	Sink_LdapSearch("(cn=admin)")
}
