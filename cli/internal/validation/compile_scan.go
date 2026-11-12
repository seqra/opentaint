package validation

import (
	"fmt"
	"path/filepath"

	"github.com/seqra/opentaint/internal/utils"
)

// ValidateCompileInputs checks the inputs of a compile. The errors name the paths as they are
// given, so pass them as the user wrote them where there is a choice.
func ValidateCompileInputs(projectRoot, outputProjectModelPath string) error {
	if err := requireDirExists(projectRoot, "project directory"); err != nil {
		return err
	}

	if err := requirePathNotExists(outputProjectModelPath, "output directory"); err != nil {
		return err
	}

	if !utils.IsSupportedArch() {
		return fmt.Errorf("unsupported architecture `%s`, OpenTaint runs on amd64 and arm64", utils.GetArch())
	}

	return nil
}

// ValidateScanInputs checks the inputs of a scan. The errors name the paths as they are given, so
// pass them as the user wrote them where there is a choice.
func ValidateScanInputs(userProjectRoot, absProjectModelPath, absSarifReportPath string, rulesetPaths, severities []string, maxMemoryValue string, requiresProjectModel bool) (string, error) {
	if err := requireDirExists(userProjectRoot, "project path"); err != nil {
		return "", err
	}

	if requiresProjectModel {
		projectModelFile := filepath.Join(absProjectModelPath, "project.yaml")
		if _, err := requireFileExists(projectModelFile, "project model file"); err != nil {
			return "", err
		}
	}

	for _, ruleSetPath := range rulesetPaths {
		if err := requirePathExists(ruleSetPath, "ruleset"); err != nil {
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
