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

//go:embed example/go/taint/taint.go
var taintGo []byte

//go:embed example/rules/go/lib/test/generic-source.yaml
var genericGoSource []byte

//go:embed example/rules/go/lib/test/generic-sink.yaml
var genericGoSink []byte

const (
	markersDir          = "test-rules"
	genericSourceRule   = "java/lib/test/generic-source.yaml"
	genericSinkRule     = "java/lib/test/generic-sink.yaml"
	genericGoSourceRule = "go/lib/test/generic-source.yaml"
	genericGoSinkRule   = "go/lib/test/generic-sink.yaml"
)

func Scaffold(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "src", "main", "java", "test", "Taint.java"):       taintJava,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSourceRule)): genericSource,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericSinkRule)):   genericSink,
	})
}

// ScaffoldGo writes the Go marker: the taint package and its generic lib rules.
func ScaffoldGo(projectDir string) error {
	return utils.WriteFiles(map[string][]byte{
		filepath.Join(projectDir, "taint", "taint.go"):                                 taintGo,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericGoSourceRule)): genericGoSource,
		filepath.Join(projectDir, markersDir, filepath.FromSlash(genericGoSinkRule)):   genericGoSink,
	})
}
