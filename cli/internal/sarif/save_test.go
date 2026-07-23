package sarif

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"testing"
)

// A report shaped like real analyzer output: schema/version envelope, tool
// driver with rules, uri bases, a result with fingerprints and a code flow.
const realisticSarif = `{
  "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
  "version": "2.1.0",
  "runs": [
    {
      "tool": {
        "driver": {
          "name": "OpenTaint",
          "version": "1.2.3",
          "semanticVersion": "1.2.3",
          "rules": [
            {
              "id": "java.sqli",
              "name": "java.sqli",
              "shortDescription": {"text": "SQL injection"},
              "properties": {"tags": ["CWE-89"], "precision": "high"}
            }
          ]
        }
      },
      "originalUriBaseIds": {"%SRCROOT%": {"uri": "/project"}},
      "results": [
        {
          "ruleId": "java.sqli",
          "level": "error",
          "message": {"text": "Tainted value reaches a SQL sink"},
          "partialFingerprints": {
            "vulnerabilityWithTraceHash/v1": "trace-hash-aaa",
            "vulnerabilitySourceSinkHash/v1": "src-sink-aaa"
          },
          "locations": [
            {
              "physicalLocation": {
                "artifactLocation": {"uri": "src/Dao.java", "uriBaseId": "%SRCROOT%"},
                "region": {"startLine": 42, "startColumn": 9}
              }
            }
          ],
          "codeFlows": [
            {
              "threadFlows": [
                {
                  "locations": [
                    {
                      "location": {
                        "physicalLocation": {
                          "artifactLocation": {"uri": "src/Controller.java", "uriBaseId": "%SRCROOT%"},
                          "region": {"startLine": 10}
                        },
                        "logicalLocations": [{"fullyQualifiedName": "com.example.Controller#handle"}]
                      },
                      "kinds": ["taint", "source"],
                      "executionOrder": 1
                    }
                  ]
                }
              ]
            }
          ]
        }
      ]
    }
  ]
}`

func TestSaveReportRoundTripsRealisticReport(t *testing.T) {
	report, err := UnmarshalReport([]byte(realisticSarif))
	if err != nil {
		t.Fatalf("unmarshal: %v", err)
	}

	path := filepath.Join(t.TempDir(), "out.sarif")
	if err := SaveReport(&report, path); err != nil {
		t.Fatalf("save: %v", err)
	}

	written, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read back: %v", err)
	}

	// Compare as generic JSON so key order and indentation are irrelevant: the
	// question is whether any field was dropped or altered by the round trip.
	var before, after any
	if err := json.Unmarshal([]byte(realisticSarif), &before); err != nil {
		t.Fatalf("unmarshal expected: %v", err)
	}
	if err := json.Unmarshal(written, &after); err != nil {
		t.Fatalf("unmarshal written: %v", err)
	}
	if !reflect.DeepEqual(before, after) {
		t.Errorf("round trip lost or changed data\nbefore: %s\nafter:  %s", realisticSarif, written)
	}
}

func TestSaveReportCreatesParentDirectories(t *testing.T) {
	report := makeReport(makeResult("a", Error, "a.java", 1, nil))
	path := filepath.Join(t.TempDir(), "nested", "dir", "out.sarif")
	if err := SaveReport(report, path); err != nil {
		t.Fatalf("save: %v", err)
	}
	if _, err := os.Stat(path); err != nil {
		t.Errorf("expected file at %s: %v", path, err)
	}
}

func TestSaveReportLeavesNoTempFileBehind(t *testing.T) {
	dir := t.TempDir()
	report := makeReport(makeResult("a", Error, "a.java", 1, nil))
	if err := SaveReport(report, filepath.Join(dir, "out.sarif")); err != nil {
		t.Fatalf("save: %v", err)
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		t.Fatalf("readdir: %v", err)
	}
	if len(entries) != 1 || entries[0].Name() != "out.sarif" {
		var names []string
		for _, e := range entries {
			names = append(names, e.Name())
		}
		t.Errorf("expected only out.sarif, got %v", names)
	}
}

func TestSaveReportOverwritesAtomically(t *testing.T) {
	path := filepath.Join(t.TempDir(), "out.sarif")
	if err := os.WriteFile(path, []byte("stale contents"), 0o644); err != nil {
		t.Fatalf("seed: %v", err)
	}
	report := makeReport(makeResult("a", Error, "a.java", 1, nil))
	if err := SaveReport(report, path); err != nil {
		t.Fatalf("save: %v", err)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read back: %v", err)
	}
	if _, err := UnmarshalReport(data); err != nil {
		t.Errorf("overwritten file is not valid SARIF: %v", err)
	}
}
