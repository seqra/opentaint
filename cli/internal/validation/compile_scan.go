package validation

import (
	"fmt"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

func ValidateCompileInputs(absProjectRoot, absOutputProjectModelPath string) error {
	if err := requireDirExists(absProjectRoot, "project directory"); err != nil {
		return err
	}

	if err := requirePathNotExists(absOutputProjectModelPath, "output directory"); err != nil {
		return err
	}

	if !utils.IsSupportedArch() {
		return fmt.Errorf("unsupported architecture `%s`, OpenTaint runs on amd64 and arm64", utils.GetArch())
	}

	return nil
}

func ValidateScanInputs(absUserProjectRoot, absProjectModelPath, absSarifReportPath string, nonBuiltinRulesetPaths, severities []string, maxMemoryValue string, requiresProjectModel bool) (string, error) {
	if err := requireDirExists(absUserProjectRoot, "project path"); err != nil {
		return "", err
	}

	if requiresProjectModel {
		projectModelFile := filepath.Join(absProjectModelPath, "project.yaml")
		if _, err := requireFileExists(projectModelFile, "project model file"); err != nil {
			return "", err
		}
	}

	for _, ruleSetPath := range nonBuiltinRulesetPaths {
		if err := requirePathExists(ruleSetPath, "ruleset path"); err != nil {
			return "", err
		}
	}

	for _, severity := range severities {
		switch severity {
		case "error", "warning", "note":
		default:
			return "", fmt.Errorf("invalid --severity value `%s`, use note, warning, or error", severity)
		}
	}

	if maxMemoryValue == "" {
		return "", nil
	}

	parsedMaxMemory, err := utils.ParseMemoryValue(maxMemoryValue)
	if err != nil {
		return "", fmt.Errorf("invalid --max-memory value `%s`: %w", maxMemoryValue, err)
	}

	return parsedMaxMemory, nil
}
