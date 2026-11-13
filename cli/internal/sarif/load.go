package sarif

import (
	"os"
)

// LoadReport reads and parses the SARIF report at path. The errors are those of the read and
// of the parse: the caller says which report failed to load.
func LoadReport(path string) (*Report, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}

	report, err := UnmarshalReport(data)
	if err != nil {
		return nil, err
	}

	return &report, nil
}
