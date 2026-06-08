// Package testrule bundles the generic Taint source/sink lib rules and the Taint
// helper scaffolded into a rule test project, so a package's source/sink lib rules can
// be exercised against a fixed, type-agnostic counterpart (the generic marker), the way
// testapprox bundles the fixed approximation rule.
package testrule

import (
	_ "embed"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

//go:embed example/rules/java/lib/test/generic-source.yaml
var genericSource []byte

//go:embed example/rules/java/lib/test/generic-sink.yaml
var genericSink []byte

// Marker locations, relative to the test project root. The marker lib rules and the
// test join an agent writes alongside them live only under MarkersDir — never in
// .opentaint/rules — so they never reach the main project scan. The rule paths double
// as the values an agent refs from a test join (relative to the test-rules root).
const (
	MarkersDir        = "test-rules"
	GenericSourceRule = "java/lib/test/generic-source.yaml"
	GenericSinkRule   = "java/lib/test/generic-sink.yaml"
)

// Scaffold writes the Taint helper into the project sources and the generic
// source/sink marker lib rules into the project's test-rules ruleset.
func Scaffold(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"):       taintJava,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(GenericSourceRule)): genericSource,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(GenericSinkRule)):   genericSink,
	})
}
