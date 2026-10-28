package main

import (
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"reflect"
	"testing"
)

func TestExtractCallSites(t *testing.T) {
	dir := t.TempDir()
	files := map[string]string{
		"go.mod": "module example.com/app\n\ngo 1.25.0\n",
		"lib/lib.go": `package lib
func Direct(string) {}
func Assigned(string) {}
func Callback(string) {}
func Generic[T any](T) {}
func Unused(string) {}
func Variadic(string, ...any) {}
type Worker struct{}
func (*Worker) Bound(string) {}
func (Worker) Expression(string) {}
type Box[T any] struct{}
func (*Box[T]) Get() {}
`,
		"app.go": `package app
import (
    "example.com/app/lib"
    "fmt"
    "io"
)
var stored = lib.Callback
func use(w *lib.Worker, s fmt.Stringer, rc io.ReadCloser, box *lib.Box[string]) {
    lib.Direct("value")
    f := lib.Assigned
    f("value")
    g := lib.Generic[string]
    g("value")
    method := w.Bound
    method("value")
    expression := lib.Worker.Expression
    expression(*w, "value")
    stored("value")
    lib.Variadic("value", 1, 2)
    _ = s.String()
    _, _ = rc.Read(nil)
    box.Get()
}
`,
	}
	for name, content := range files {
		path := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	rows, err := extract(dir)
	if err != nil {
		t.Fatal(err)
	}
	// A call through a package variable has no static callee, so Callback is absent; a
	// variadic tail is one packed argument, as in the analyzer's `args:<count>`. An interface call
	// is named by the receiver's static type and a generic callee by its instance, as the analyzer
	// names them.
	want := []usage{
		{Method: "(*example.com/app/lib.Box[string]).Get[string]", Signature: "args:0"},
		{Method: "(*example.com/app/lib.Worker).Bound", Signature: "args:1"},
		{Method: "(example.com/app/lib.Worker).Expression", Signature: "args:1"},
		{Method: "(fmt.Stringer).String", Signature: "args:0"},
		{Method: "(io.ReadCloser).Read", Signature: "args:1"},
		{Method: "example.com/app/lib.Assigned", Signature: "args:1"},
		{Method: "example.com/app/lib.Direct", Signature: "args:1"},
		{Method: "example.com/app/lib.Generic[string]", Signature: "args:1"},
		{Method: "example.com/app/lib.Variadic", Signature: "args:2"},
	}
	if !reflect.DeepEqual(rows, want) {
		t.Fatalf("usages = %#v, want %#v", rows, want)
	}
}

func TestExtractRejectsNonModule(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "x.go"), []byte("package x\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := extract(dir); err == nil {
		t.Fatal("extract succeeded on a directory without a Go module")
	}
}

func TestFunctionName(t *testing.T) {
	pkg := types.NewPackage("example.com/module/lib", "lib")
	params := types.NewTuple(types.NewParam(token.NoPos, pkg, "value", types.Typ[types.String]))
	results := types.NewTuple(types.NewParam(token.NoPos, pkg, "result", types.Typ[types.String]))

	plainSig := types.NewSignatureType(nil, nil, nil, params, results, false)
	plain := types.NewFunc(token.NoPos, pkg, "Transform", plainSig)
	if got := functionName(plain, plainSig); got != "example.com/module/lib.Transform" {
		t.Fatalf("package function name = %q", got)
	}

	typeName := types.NewTypeName(token.NoPos, pkg, "Worker", nil)
	named := types.NewNamed(typeName, types.NewStruct(nil, nil), nil)
	receiver := types.NewVar(token.NoPos, pkg, "worker", types.NewPointer(named))
	methodSig := types.NewSignatureType(receiver, nil, nil, params, results, false)
	method := types.NewFunc(token.NoPos, pkg, "Transform", methodSig)
	if got := functionName(method, methodSig); got != "(*example.com/module/lib.Worker).Transform" {
		t.Fatalf("method name = %q", got)
	}
}
