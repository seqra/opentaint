// go-usage is the Go counterpart of `javap -c`: it builds the SSA form of the project's packages
// (the form the analyzer reads) and prints the static callee of every call site as JSON
// {method, signature} rows, named the way the analyzer names an external method.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"go/types"
	"os"
	"sort"
	"strings"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

type usage struct {
	Method    string `json:"method"`
	Signature string `json:"signature"`
}

func main() {
	dir := flag.String("dir", "", "Go project directory")
	flag.Parse()
	if *dir == "" {
		fmt.Fprintln(os.Stderr, "--dir is required")
		os.Exit(2)
	}

	rows, err := extract(*dir)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := json.NewEncoder(os.Stdout).Encode(rows); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func extract(dir string) ([]usage, error) {
	cfg := &packages.Config{
		Mode: packages.NeedName | packages.NeedFiles | packages.NeedCompiledGoFiles |
			packages.NeedImports | packages.NeedSyntax |
			packages.NeedTypes | packages.NeedTypesInfo | packages.NeedTypesSizes,
		Dir: dir,
	}
	loaded, err := packages.Load(cfg, "./...")
	if err != nil {
		return nil, fmt.Errorf("load Go packages: %w", err)
	}
	// Like javap on an unreadable class, a package that does not type-check is skipped.
	var project []*packages.Package
	for _, pkg := range loaded {
		if len(pkg.Errors) != 0 {
			fmt.Fprintf(os.Stderr, "warning: skipping %s: %v\n", pkg.PkgPath, pkg.Errors[0])
			continue
		}
		project = append(project, pkg)
	}
	// With nothing readable, an empty result would read as "no usages".
	if len(project) == 0 {
		return nil, fmt.Errorf("no Go package in %s could be loaded", dir)
	}

	// The analyzer builds instantiated generics, so a generic callee is named by its instance.
	prog, ssaPkgs := ssautil.Packages(project, ssa.InstantiateGenerics)
	prog.Build()
	own := make(map[*ssa.Package]bool, len(ssaPkgs))
	for _, pkg := range ssaPkgs {
		own[pkg] = true
	}

	seen := make(map[usage]bool)
	for fn := range ssautil.AllFunctions(prog) {
		if !own[declaringPackage(fn)] {
			continue
		}
		for _, block := range fn.Blocks {
			for _, instr := range block.Instrs {
				call, ok := instr.(ssa.CallInstruction)
				if !ok {
					continue
				}
				if row, ok := calledFunction(call.Common()); ok {
					seen[row] = true
				}
			}
		}
	}

	rows := make([]usage, 0, len(seen))
	for row := range seen {
		rows = append(rows, row)
	}
	sort.Slice(rows, func(i, j int) bool {
		if rows[i].Method != rows[j].Method {
			return rows[i].Method < rows[j].Method
		}
		return rows[i].Signature < rows[j].Signature
	})
	return rows, nil
}

// declaringPackage is the package of fn, or of its generic origin for an instance.
func declaringPackage(fn *ssa.Function) *ssa.Package {
	if fn.Package() == nil && fn.Origin() != nil {
		return fn.Origin().Package()
	}
	return fn.Package()
}

// calledFunction names the function a call site reaches as the analyzer names it, with the
// analyzer's `args:<count>` signature:
//   - an invoke is the method of the receiver's static type, `(pkg.Interface).Method`;
//   - a bound method or method expression is the method it wraps;
//   - any other static callee is its SSA name, so a generic instance keeps its type arguments.
//
// Calls through function values have no static callee.
func calledFunction(call *ssa.CallCommon) (usage, bool) {
	if call.IsInvoke() {
		sig := call.Method.Type().(*types.Signature)
		return usage{
			Method:    "(" + types.TypeString(call.Value.Type(), nil) + ")." + call.Method.Name(),
			Signature: arity(sig),
		}, true
	}
	callee := call.StaticCallee()
	if callee == nil {
		return usage{}, false
	}
	switch {
	case callee.Synthetic == "package initializer":
		// Package initialization is not a call the analyzer reports.
		return usage{}, false
	case strings.HasPrefix(callee.Synthetic, "bound method wrapper"),
		strings.HasPrefix(callee.Synthetic, "thunk"):
		fn, ok := callee.Object().(*types.Func)
		if !ok {
			return usage{}, false
		}
		sig := fn.Type().(*types.Signature)
		return usage{Method: functionName(fn, sig), Signature: arity(sig)}, true
	}
	return usage{Method: callee.String(), Signature: arity(callee.Signature)}, true
}

func arity(sig *types.Signature) string {
	return fmt.Sprintf("args:%d", sig.Params().Len())
}

func functionName(fn *types.Func, sig *types.Signature) string {
	pkgPath := ""
	if fn.Pkg() != nil {
		pkgPath = fn.Pkg().Path() + "."
	}
	if sig.Recv() == nil {
		return pkgPath + fn.Name()
	}

	receiver := sig.Recv().Type()
	pointer := false
	if ptr, ok := receiver.(*types.Pointer); ok {
		pointer = true
		receiver = ptr.Elem()
	}
	named, ok := receiver.(*types.Named)
	if !ok {
		return pkgPath + fn.Name()
	}
	prefix := "("
	if pointer {
		prefix += "*"
	}
	return prefix + pkgPath + named.Obj().Name() + ")." + fn.Name()
}
