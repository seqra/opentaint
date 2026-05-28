package sarif

import (
	"reflect"
	"testing"
)

func steps(tfls ...ThreadFlowLocation) []classifiedStep {
	out := make([]classifiedStep, len(tfls))
	for i, s := range tfls {
		out[i] = classifiedStep{Step: s}
	}
	return out
}

func TestDeriveNestingLevels(t *testing.T) {
	// main() -> call helper() -> (deep) -> return to main() -> sink in main()
	s := steps(
		makeStep(1, []string{"source"}, "main"),       // 0
		makeStep(2, []string{"call"}, "main"),          // 0 (call pushes main@0)
		makeStep(3, []string{"unknown"}, "helper"),     // 1 (inside helper)
		makeStep(4, []string{"call"}, "helper"),        // 1 (call pushes helper@1)
		makeStep(5, []string{"unknown"}, "deep"),       // 2 (inside deep)
		makeStep(6, []string{"sink"}, "main"),          // 0 (return to main)
	)
	got := deriveNestingLevels(s)
	want := []int{0, 0, 1, 1, 2, 0}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("deriveNestingLevels = %v, want %v", got, want)
	}
}

func TestShapeFlowHidesDeepSteps(t *testing.T) {
	s := steps(
		makeStep(1, []string{"source"}, "main"),
		makeStep(2, []string{"call"}, "main"),      // level 0, kept (call boundary in main)
		makeStep(3, []string{"unknown"}, "helper"), // level 1, hidden at maxLevel 0
		makeStep(4, []string{"unknown"}, "helper"), // level 1, hidden at maxLevel 0
		makeStep(5, []string{"sink"}, "main"),
	)
	items := shapeFlow(s, 0)
	// Expect: source, call(level 0), hidden(2), sink.
	if len(items) != 4 {
		t.Fatalf("expected 4 render items, got %d", len(items))
	}
	if items[0].step == nil || items[1].step == nil || items[3].step == nil {
		t.Error("expected source, call, and sink steps to be kept")
	}
	if items[2].step != nil || items[2].hidden != 2 {
		t.Errorf("expected a hidden(2) placeholder at index 2, got %+v", items[2])
	}
}

func TestShapeFlowKeepsAllWhenWithinLevel(t *testing.T) {
	s := steps(
		makeStep(1, []string{"source"}, "main"),
		makeStep(2, []string{"sink"}, "main"),
	)
	items := shapeFlow(s, 0)
	if len(items) != 2 || items[0].step == nil || items[1].step == nil {
		t.Errorf("expected both steps kept, got %d items", len(items))
	}
}
