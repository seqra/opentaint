package sarif

import (
	"reflect"
	"testing"
)

func TestParseGroupDimension(t *testing.T) {
	cases := map[string]groupDimension{
		"":          groupByFilePath,
		"file-path": groupByFilePath,
		"severity":  groupBySeverity,
		"rule-id":   groupByRuleID,
	}
	for in, want := range cases {
		got, err := ParseGroupDimension(in)
		if err != nil || got != want {
			t.Errorf("ParseGroupDimension(%q) = %v, %v; want %v", in, got, err, want)
		}
	}
	if _, err := ParseGroupDimension("nope"); err == nil {
		t.Error("expected error for invalid dimension")
	}
}

func TestGroupKey(t *testing.T) {
	r := makeResult("rules:sqli", Error, "src/A.java", 1, nil)

	if k, l := groupKey(&r, groupBySeverity); k != "error" || l != "ERROR" {
		t.Errorf("severity groupKey = %q/%q", k, l)
	}
	if k, l := groupKey(&r, groupByRuleID); k != "rules:sqli" || l != "rules:sqli" {
		t.Errorf("rule-id groupKey = %q/%q", k, l)
	}
	if k, l := groupKey(&r, groupByFilePath); k != "src/A.java" || l != "src/A.java" {
		t.Errorf("file-path groupKey = %q/%q", k, l)
	}
}

func TestSortGroups(t *testing.T) {
	sev := []string{"note", "error", "none", "warning"}
	sortGroups(sev, groupBySeverity)
	want := []string{"error", "warning", "note", "none"}
	if !reflect.DeepEqual(sev, want) {
		t.Errorf("severity order = %v, want %v", sev, want)
	}

	files := []string{"b.java", "a.java"}
	sortGroups(files, groupByFilePath)
	if !reflect.DeepEqual(files, []string{"a.java", "b.java"}) {
		t.Errorf("file order = %v", files)
	}
}
