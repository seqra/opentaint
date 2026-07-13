package rules

import (
	"os"
	"path/filepath"
	"testing"
)

func writeRule(t *testing.T, root, relPath, content string) {
	t.Helper()
	full := filepath.Join(root, filepath.FromSlash(relPath))
	if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(full, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestExpandRuleIDs_CollectsJoinRefs(t *testing.T) {
	root := t.TempDir()
	writeRule(t, root, "java/security/xss.yaml", `
rules:
  - id: xss
    mode: join
    join:
      refs:
        - rule: java/lib/generic/src.yaml#src
          as: untrusted
        - rule: java/lib/generic/sink.yaml#sink
          as: sink
`)
	writeRule(t, root, "java/lib/generic/src.yaml", "rules:\n  - id: src\n    options: {lib: true}\n")
	writeRule(t, root, "java/lib/generic/sink.yaml", "rules:\n  - id: sink\n    options: {lib: true}\n")

	got := ExpandRuleIDs([]string{"java/security/xss.yaml:xss"}, []string{root})
	want := []string{
		"java/security/xss.yaml:xss",
		"java/lib/generic/src.yaml:src",
		"java/lib/generic/sink.yaml:sink",
	}
	assertEqual(t, got, want)
}

func TestExpandRuleIDs_Transitive(t *testing.T) {
	root := t.TempDir()
	writeRule(t, root, "a.yaml", "rules:\n  - id: a\n    join:\n      refs:\n        - rule: b.yaml#b\n")
	writeRule(t, root, "b.yaml", "rules:\n  - id: b\n    join:\n      refs:\n        - rule: c.yaml#c\n")
	writeRule(t, root, "c.yaml", "rules:\n  - id: c\n")

	got := ExpandRuleIDs([]string{"a.yaml:a"}, []string{root})
	assertEqual(t, got, []string{"a.yaml:a", "b.yaml:b", "c.yaml:c"})
}

func TestExpandRuleIDs_CycleAndDuplicates(t *testing.T) {
	root := t.TempDir()
	writeRule(t, root, "a.yaml", "rules:\n  - id: a\n    join:\n      refs:\n        - rule: b.yaml#b\n")
	writeRule(t, root, "b.yaml", "rules:\n  - id: b\n    join:\n      refs:\n        - rule: a.yaml#a\n")

	got := ExpandRuleIDs([]string{"a.yaml:a", "a.yaml:a"}, []string{root})
	assertEqual(t, got, []string{"a.yaml:a", "b.yaml:b"})
}

func TestExpandRuleIDs_UnresolvedPassesThrough(t *testing.T) {
	root := t.TempDir()
	got := ExpandRuleIDs([]string{"does/not/exist.yaml:x"}, []string{root})
	assertEqual(t, got, []string{"does/not/exist.yaml:x"})
}

func TestExpandRuleIDs_MultipleRoots(t *testing.T) {
	builtin := t.TempDir()
	custom := t.TempDir()
	writeRule(t, custom, "java/security/my.yaml", "rules:\n  - id: my\n    join:\n      refs:\n        - rule: java/lib/generic/src.yaml#src\n")
	writeRule(t, builtin, "java/lib/generic/src.yaml", "rules:\n  - id: src\n")

	got := ExpandRuleIDs([]string{"java/security/my.yaml:my"}, []string{builtin, custom})
	assertEqual(t, got, []string{"java/security/my.yaml:my", "java/lib/generic/src.yaml:src"})
}

func assertEqual(t *testing.T, got, want []string) {
	t.Helper()
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("got %v, want %v", got, want)
		}
	}
}

func TestExpandRuleIDs_BareSameFileRef(t *testing.T) {
	root := t.TempDir()
	writeRule(t, root, "java/security/deser.yaml", `
rules:
  - id: unsafe-deserialization
    mode: join
    join:
      refs:
        - rule: unsafe-object-mapper-sink
          as: sink
  - id: unsafe-object-mapper-sink
    options: {lib: true}
`)

	got := ExpandRuleIDs([]string{"java/security/deser.yaml:unsafe-deserialization"}, []string{root})
	want := []string{
		"java/security/deser.yaml:unsafe-deserialization",
		"java/security/deser.yaml:unsafe-object-mapper-sink",
	}
	assertEqual(t, got, want)
}

func TestExpandRuleIDs_BareRefTransitive(t *testing.T) {
	root := t.TempDir()
	writeRule(t, root, "a.yaml", `
rules:
  - id: a
    join:
      refs:
        - rule: helper
  - id: helper
    join:
      refs:
        - rule: b.yaml#b
`)
	writeRule(t, root, "b.yaml", "rules:\n  - id: b\n")

	got := ExpandRuleIDs([]string{"a.yaml:a"}, []string{root})
	want := []string{"a.yaml:a", "a.yaml:helper", "b.yaml:b"}
	assertEqual(t, got, want)
}
