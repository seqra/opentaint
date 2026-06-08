package util

import (
	"fmt"
	"os"
)

// Sink_LdapSearch represents an LDAP search call site that takes a raw filter string.
func Sink_LdapSearch(filter string) { _ = filter }

// Positive_env_filter: env interpolated into LDAP filter via Sprintf and queried.
func Positive_env_filter() {
	u := os.Getenv("LDAP_UID")
	f := fmt.Sprintf("(uid=%s)", u)
	Sink_LdapSearch(f)
}

// Negative_env_const_filter: env read but constant LDAP filter.
func Negative_env_const_filter() {
	_ = os.Getenv("LDAP_UID")
	Sink_LdapSearch("(uid=*)")
}
