package testrule

import (
	_ "embed"
	"path/filepath"

	"github.com/seqra/opentaint/internal/testproject"
	"github.com/seqra/opentaint/internal/utils"
)

//go:embed example/src/main/java/test/Taint.java
var taintJava []byte

//go:embed example/rules/java/lib/test/generic-source.yaml
var genericSource []byte

//go:embed example/rules/java/lib/test/generic-sink.yaml
var genericSink []byte

//go:embed example/rule-test.yaml
var ruleTestTemplate []byte

//go:embed example/go/taint/taint.go
var taintGo []byte

//go:embed example/rules/go/lib/test/generic-source.yaml
var genericGoSource []byte

//go:embed example/rules/go/lib/test/generic-sink.yaml
var genericGoSink []byte

//go:embed example/go/rule-test.yaml
var goRuleTestTemplate []byte

// MarkersDir is the directory of a rule test project that holds the generic marker rules and
// the rules that join them to the rules under test. The tests load it as a ruleset.
const MarkersDir = "test-rules"

const (
	genericSourceRule   = "java/lib/test/generic-source.yaml"
	genericSinkRule     = "java/lib/test/generic-sink.yaml"
	genericGoSourceRule = "go/lib/test/generic-source.yaml"
	genericGoSinkRule   = "go/lib/test/generic-sink.yaml"
)

func Scaffold(projectDir string) error {
	if err := utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"):       taintJava,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(genericSourceRule)): genericSource,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(genericSinkRule)):   genericSink,
	}); err != nil {
		return err
	}
	return testproject.WriteRuleTestFile(projectDir, ruleTestTemplate)
}

// ScaffoldGo writes the generic marker of a Go rule test project: the taint package, its lib
// rules, and rule-test.yaml.
func ScaffoldGo(projectDir string) error {
	if err := utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "taint", "taint.go"):                                 taintGo,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(genericGoSourceRule)): genericGoSource,
		filepath.Join(projectDir, MarkersDir, filepath.FromSlash(genericGoSinkRule)):   genericGoSink,
	}); err != nil {
		return err
	}
	return testproject.WriteRuleTestFile(projectDir, goRuleTestTemplate)
}
