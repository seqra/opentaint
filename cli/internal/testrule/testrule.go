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

const (
	markersDir        = "test-rules"
	genericSourceRule = "java/lib/test/generic-source.yaml"
	genericSinkRule   = "java/lib/test/generic-sink.yaml"
)

func Scaffold(projectDir string) error {
	if err := utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"):       taintJava,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSourceRule)): genericSource,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSinkRule)):   genericSink,
	}); err != nil {
		return err
	}
	return testproject.WriteRuleTestFile(projectDir, ruleTestTemplate)
}
