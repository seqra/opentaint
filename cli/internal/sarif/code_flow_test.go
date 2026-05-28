package sarif

import (
	"reflect"
	"testing"
)

func TestParseCodeFlowSelection(t *testing.T) {
	cases := []struct {
		in     string
		want   CodeFlowSelection
		hasErr bool
	}{
		{"", CodeFlowSelection{}, false},
		{" ", CodeFlowSelection{}, false},
		{"all", CodeFlowSelection{All: true}, false},
		{"ALL", CodeFlowSelection{All: true}, false},
		{"  all  ", CodeFlowSelection{All: true}, false},
		{"1", CodeFlowSelection{Index: 1}, false},
		{"42", CodeFlowSelection{Index: 42}, false},
		{"0", CodeFlowSelection{}, true},
		{"-1", CodeFlowSelection{}, true},
		{"two", CodeFlowSelection{}, true},
		{"1.5", CodeFlowSelection{}, true},
		{"all,1", CodeFlowSelection{}, true},
	}
	for _, c := range cases {
		t.Run(c.in, func(t *testing.T) {
			got, err := ParseCodeFlowSelection(c.in)
			if (err != nil) != c.hasErr {
				t.Fatalf("err = %v, hasErr=%v", err, c.hasErr)
			}
			if !c.hasErr && !reflect.DeepEqual(got, c.want) {
				t.Errorf("got %+v, want %+v", got, c.want)
			}
		})
	}
}

func TestSelectedIndices(t *testing.T) {
	cases := []struct {
		name  string
		sel   CodeFlowSelection
		total int
		want  []int
	}{
		{"unset / total 0", CodeFlowSelection{}, 0, nil},
		{"unset / total 1", CodeFlowSelection{}, 1, []int{1}},
		{"unset / total 3", CodeFlowSelection{}, 3, []int{1}},
		{"all / total 0", CodeFlowSelection{All: true}, 0, nil},
		{"all / total 1", CodeFlowSelection{All: true}, 1, []int{1}},
		{"all / total 3", CodeFlowSelection{All: true}, 3, []int{1, 2, 3}},
		{"specific in range", CodeFlowSelection{Index: 2}, 3, []int{2}},
		{"specific equals total", CodeFlowSelection{Index: 3}, 3, []int{3}},
		{"specific out of range", CodeFlowSelection{Index: 5}, 3, nil},
		{"specific on total 0", CodeFlowSelection{Index: 1}, 0, nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got := c.sel.selectedIndices(c.total)
			if !reflect.DeepEqual(got, c.want) {
				t.Errorf("selectedIndices = %v, want %v", got, c.want)
			}
		})
	}
}

func TestClassifyTaintFlowAt(t *testing.T) {
	// A result with two code flows, each carrying a single distinctive step.
	r := makeResult("r", Error, "a.java", 1, nil)
	r.CodeFlows = []CodeFlow{
		{ThreadFlows: []ThreadFlow{{Locations: []ThreadFlowLocation{makeStep(1, []string{"source"}, "alpha")}}}},
		{ThreadFlows: []ThreadFlow{{Locations: []ThreadFlowLocation{makeStep(1, []string{"source"}, "beta")}}}},
	}

	got0, err := classifyTaintFlowAt(&r, 0)
	if err != nil || len(got0) != 1 || stepMethod(got0[0]) != "alpha" {
		t.Errorf("flow 0 = %+v, err=%v; want method=alpha", got0, err)
	}
	got1, err := classifyTaintFlowAt(&r, 1)
	if err != nil || len(got1) != 1 || stepMethod(got1[0]) != "beta" {
		t.Errorf("flow 1 = %+v, err=%v; want method=beta", got1, err)
	}
	if _, err := classifyTaintFlowAt(&r, 2); err == nil {
		t.Error("expected out-of-range error for flow 2")
	}
	empty := makeResult("r", Error, "a.java", 1, nil)
	if _, err := classifyTaintFlowAt(&empty, 0); err == nil {
		t.Error("expected error for result with no code flows")
	}
}
