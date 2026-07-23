package sarif

import (
	"encoding/json"
	"testing"
)

func TestPropertyBagPreservesUnknownKeys(t *testing.T) {
	const in = `{"tags":["CWE-89"],"precision":"high","confidence":0.75,"nested":{"a":[1,2]}}`
	var bag PropertyBag
	if err := json.Unmarshal([]byte(in), &bag); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	if len(bag.Tags) != 1 || bag.Tags[0] != "CWE-89" {
		t.Errorf("tags not decoded: %v", bag.Tags)
	}

	out, err := json.Marshal(bag)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	var before, after map[string]any
	if err := json.Unmarshal([]byte(in), &before); err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(out, &after); err != nil {
		t.Fatal(err)
	}
	for k, v := range before {
		got, ok := after[k]
		if !ok {
			t.Errorf("key %q was dropped", k)
			continue
		}
		if toJSON(t, got) != toJSON(t, v) {
			t.Errorf("key %q changed: %s -> %s", k, toJSON(t, v), toJSON(t, got))
		}
	}
}

func TestPropertyBagPreservesLargeIntegersExactly(t *testing.T) {
	const in = `{"id":9007199254740993}`
	var bag PropertyBag
	if err := json.Unmarshal([]byte(in), &bag); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	out, err := json.Marshal(bag)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if string(out) != in {
		t.Errorf("got %s, want %s", out, in)
	}
}

func TestPropertyBagWithOnlyTags(t *testing.T) {
	bag := PropertyBag{Tags: []string{"a", "b"}}
	out, err := json.Marshal(bag)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if string(out) != `{"tags":["a","b"]}` {
		t.Errorf("got %s", out)
	}
}

func TestPropertyBagEmptyMarshalsToEmptyObject(t *testing.T) {
	out, err := json.Marshal(PropertyBag{})
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if string(out) != `{}` {
		t.Errorf("got %s, want {}", out)
	}
}

func TestPropertyBagNonStringTagsAreNotLost(t *testing.T) {
	// A malformed bag must still round-trip rather than silently dropping tags.
	const in = `{"tags":"not-an-array"}`
	var bag PropertyBag
	if err := json.Unmarshal([]byte(in), &bag); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	out, err := json.Marshal(bag)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	if string(out) != in {
		t.Errorf("got %s, want %s", out, in)
	}
}

func toJSON(t *testing.T, v any) string {
	t.Helper()
	b, err := json.Marshal(v)
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}
