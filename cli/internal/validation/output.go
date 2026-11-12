package validation

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"github.com/seqra/opentaint/internal/load_trace"
	"github.com/seqra/opentaint/internal/sarif"
	"github.com/seqra/opentaint/internal/utils/project"
)

func ValidateProjectModelOutput(outputDir string) (*project.Config, error) {
	if err := requireDirExists(outputDir, "output project model directory"); err != nil {
		return nil, err
	}

	projectModelFile := filepath.Join(outputDir, "project.yaml")
	if _, err := requireFileExists(projectModelFile, "project model file"); err != nil {
		return nil, err
	}

	return project.LoadConfig(outputDir)
}

func ValidateSarifOutput(absSarifPath string) (*sarif.Report, error) {
	info, err := requireFileExists(absSarifPath, "sarif output file")
	if err != nil {
		return nil, err
	}
	if info.Size() == 0 {
		return nil, fmt.Errorf("SARIF report `%s` is empty", absSarifPath)
	}

	report, err := sarif.LoadReport(absSarifPath)
	if err != nil {
		return nil, fmt.Errorf("failed to parse SARIF report `%s`: %w", absSarifPath, err)
	}
	if len(report.Runs) == 0 {
		return nil, fmt.Errorf("SARIF report `%s` has no runs", absSarifPath)
	}

	return report, nil
}

func ValidateRuleLoadTraceOutput(absSemgrepRuleLoadTracePath string) (*load_trace.SemgrepLoadTrace, error) {
	if _, err := requireFileExists(absSemgrepRuleLoadTracePath, "rule load trace file"); err != nil {
		return nil, err
	}

	data, err := os.ReadFile(absSemgrepRuleLoadTracePath)
	if err != nil {
		return nil, fmt.Errorf("failed to read rule load trace `%s`: %w", absSemgrepRuleLoadTracePath, err)
	}

	var trace load_trace.SemgrepLoadTrace
	if err := json.Unmarshal(data, &trace); err != nil {
		return nil, fmt.Errorf("failed to parse rule load trace `%s`: %w", absSemgrepRuleLoadTracePath, err)
	}

	return &trace, nil
}
