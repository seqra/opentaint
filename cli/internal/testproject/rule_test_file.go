package testproject

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

// RuleTestFileName is the file in the test project root that declares the test samples.
const RuleTestFileName = "rule-test.yaml"

// WriteRuleTestFile writes the rule-test.yaml template into projectDir. An existing file holds
// the samples of the user, so it is kept.
func WriteRuleTestFile(projectDir string, template []byte) error {
	path := filepath.Join(projectDir, RuleTestFileName)
	if _, err := os.Stat(path); err == nil {
		return nil
	} else if !errors.Is(err, os.ErrNotExist) {
		return fmt.Errorf("check %s: %w", path, err)
	}
	return utils.WriteFiles(map[string][]byte{path: template})
}
