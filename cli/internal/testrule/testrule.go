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

//go:embed example/rules/java/lib/test/generic-source-starred.yaml
var genericSourceStarred []byte

//go:embed example/rules/java/lib/test/generic-sink.yaml
var genericSink []byte

//go:embed example/rules/java/lib/test/generic-sink-starred.yaml
var genericSinkStarred []byte

const (
	markersDir               = "test-rules"
	genericSourceRule        = "java/lib/test/generic-source.yaml"
	genericSourceStarredRule = "java/lib/test/generic-source-starred.yaml"
	genericSinkRule          = "java/lib/test/generic-sink.yaml"
	genericSinkStarredRule   = "java/lib/test/generic-sink-starred.yaml"
)

func Scaffold(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"):              taintJava,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSourceRule)):        genericSource,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSourceStarredRule)): genericSourceStarred,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSinkRule)):          genericSink,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSinkStarredRule)):   genericSinkStarred,
	})
}
