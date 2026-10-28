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

	prog, ssaPkgs := ssautil.Packages(project, ssa.BuilderMode(0))
	prog.Build()
	own := make(map[*ssa.Package]bool, len(ssaPkgs))
	for _, pkg := range ssaPkgs {
		own[pkg] = true
	}

	seen := make(map[usage]bool)
	for fn := range ssautil.AllFunctions(prog) {
		if !own[fn.Package()] {
			continue
		}
		for _, block := range fn.Blocks {
			for _, instr := range block.Instrs {
				call, ok := instr.(ssa.CallInstruction)
				if !ok {
					continue
				}
				if callee := calledFunction(call.Common()); callee != nil {
					seen[usageOf(callee)] = true
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

// calledFunction is the declared function a call site reaches: the interface method of an
// invoke, or the static callee with a generic instance, bound method or method expression
// resolved to the function it wraps. Calls through function values have no static callee.
func calledFunction(call *ssa.CallCommon) *types.Func {
	if call.IsInvoke() {
		return call.Method
	}
	callee := call.StaticCallee()
	if callee == nil {
		return nil
	}
	if origin := callee.Origin(); origin != nil {
		callee = origin
	}
	fn, _ := callee.Object().(*types.Func)
	return fn
}

// usageOf names a function as the analyzer does (`pkg.Func`, `(pkg.Type).Method`,
// `(*pkg.Type).Method`) with the analyzer's `args:<count>` signature.
func usageOf(fn *types.Func) usage {
	sig := fn.Type().(*types.Signature)
	return usage{
		Method:    functionName(fn, sig),
		Signature: fmt.Sprintf("args:%d", sig.Params().Len()),
	}
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
