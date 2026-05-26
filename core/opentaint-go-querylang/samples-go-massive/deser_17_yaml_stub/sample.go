package util

import (
	"os"
)

// Sink_DecodeYAML stands in for yaml.Unmarshal (no 3rd-party imports allowed).
func Sink_DecodeYAML(data []byte, out interface{}) error { _ = data; _ = out; return nil }

// unmarshalYaml is a local helper (matches the prompt's stub signature).
func unmarshalYaml(data []byte, out interface{}) error { return Sink_DecodeYAML(data, out) }

// Conf is the deserialization target.
type Conf struct {
	Key string
}

// Positive_yaml: tainted env reaches Sink_DecodeYAML.
func Positive_yaml() {
	v := os.Getenv("YAML_BLOB")
	var out Conf
	_ = Sink_DecodeYAML([]byte(v), &out)
}

// Positive_yaml_helper: same via the unmarshalYaml helper (which calls the sink).
func Positive_yaml_helper() {
	v := os.Getenv("YAML_BLOB2")
	var out Conf
	_ = unmarshalYaml([]byte(v), &out)
}

// Negative_yaml_const: env read but constant decoded.
func Negative_yaml_const() {
	_ = os.Getenv("YAML_BLOB")
	var out Conf
	_ = Sink_DecodeYAML([]byte("key: safe"), &out)
}
