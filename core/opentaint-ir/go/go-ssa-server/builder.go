package server

import (
	"fmt"
	"log"
	"os"
	"runtime"
	"sort"
	"strings"
	"sync"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

func buildSSA(req *pb.BuildProgramRequest) (*ssa.Program, []*ssa.Package, map[string]*packages.Package, error) {
	return buildSSAWithPackageErrors(req, false)
}

func buildSSAWithPackageErrors(req *pb.BuildProgramRequest, failOnPackageErrors bool) (*ssa.Program, []*ssa.Package, map[string]*packages.Package, error) {
	return buildSSAWithPackageErrorsAndEnv(req, failOnPackageErrors, nil)
}

func buildSSAWithPackageErrorsAndEnv(
	req *pb.BuildProgramRequest,
	failOnPackageErrors bool,
	extraEnv []string,
) (*ssa.Program, []*ssa.Package, map[string]*packages.Package, error) {
	cfg := &packages.Config{
		Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedTypes |
			packages.NeedTypesInfo | packages.NeedImports | packages.NeedDeps |
			packages.NeedName | packages.NeedModule,
		Dir: req.WorkingDir,
	}
	if len(extraEnv) > 0 {
		cfg.Env = append(os.Environ(), extraEnv...)
	}
	if len(req.BuildTags) > 0 {
		cfg.BuildFlags = []string{"-tags=" + strings.Join(req.BuildTags, ",")}
	}
	if req.Gopath != "" {
		if cfg.Env == nil {
			cfg.Env = os.Environ()
		}
		cfg.Env = append(cfg.Env, "GOPATH="+req.Gopath)
	}
	if req.Goroot != "" {
		if cfg.Env == nil {
			cfg.Env = os.Environ()
		}
		cfg.Env = append(cfg.Env, "GOROOT="+req.Goroot)
	}

	patterns := req.Patterns
	if len(patterns) == 0 {
		patterns = []string{"./..."}
	}
	loaded, err := packages.Load(cfg, patterns...)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("packages.Load: %w", err)
	}

	info := make(map[string]*packages.Package)
	packages.Visit(loaded, func(p *packages.Package) bool {
		if _, ok := info[p.PkgPath]; !ok {
			info[p.PkgPath] = p
		}
		return true
	}, nil)
	for _, p := range loaded {
		for _, e := range p.Errors {
			log.Printf("WARN: package %s: %v", p.PkgPath, e)
		}
	}
	if failOnPackageErrors {
		var loadErrors []string
		packages.Visit(loaded, func(p *packages.Package) bool {
			for _, e := range p.Errors {
				loadErrors = append(loadErrors, fmt.Sprintf("%s: %v", p.PkgPath, e))
			}
			return true
		}, nil)
		if len(loadErrors) > 0 {
			sort.Strings(loadErrors)
			return nil, nil, nil, fmt.Errorf("Go model does not compile:\n%s", strings.Join(loadErrors, "\n"))
		}
	}

	mode := ssa.BuilderMode(0)
	if req.InstantiateGenerics {
		mode |= ssa.InstantiateGenerics
	}
	if req.SanityCheck {
		mode |= ssa.SanityCheckFunctions
	}
	prog, _ := ssautil.AllPackages(loaded, mode)

	all := make([]*ssa.Package, 0, len(prog.AllPackages()))
	for _, p := range prog.AllPackages() {
		if p != nil && p.Pkg != nil {
			all = append(all, p)
		}
	}
	sort.Slice(all, func(i, j int) bool { return all[i].Pkg.Path() < all[j].Pkg.Path() })

	return prog, all, info, nil
}

// buildBodies builds SSA function bodies. In PROJECT mode only project packages
// are built: other bodies are never serialized, and the ones project code needs
// (generic instances, wrappers) are built on demand by the SSA builder.
func buildBodies(
	prog *ssa.Program,
	pkgs []*ssa.Package,
	info map[string]*packages.Package,
	mode pb.LoadMode,
	projectModulePaths map[string]bool,
	onlyListedProjectModules bool,
) {
	if mode == pb.LoadMode_LOAD_MODE_FULL {
		prog.Build()
		return
	}
	var wg sync.WaitGroup
	sem := make(chan struct{}, runtime.GOMAXPROCS(0))
	for _, p := range pkgs {
		isStdlib, isDep := classifyPackage(info[p.Pkg.Path()], projectModulePaths, onlyListedProjectModules)
		if isStdlib || isDep {
			continue
		}
		wg.Add(1)
		sem <- struct{}{}
		go func(p *ssa.Package) {
			defer func() { <-sem; wg.Done() }()
			p.Build()
		}(p)
	}
	wg.Wait()
}

func classifyPackage(
	p *packages.Package,
	projectModulePaths map[string]bool,
	onlyListedProjectModules bool,
) (isStdlib bool, isDependency bool) {
	if p == nil {
		return false, true
	}
	isStdlib = p.Module == nil && !strings.Contains(p.PkgPath, ".")
	if isStdlib {
		return true, false
	}
	isProject := p.Module != nil && (projectModulePaths[p.Module.Path] ||
		(!onlyListedProjectModules && p.Module.Main))
	return false, !isProject
}
