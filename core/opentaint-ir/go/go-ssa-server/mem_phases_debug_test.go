package server

// Usage: GOIR_MEM_DIR=/path/to/project go test -run TestMemPhases -v

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"sort"
	"testing"
	"time"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"google.golang.org/protobuf/proto"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

func memLine(t *testing.T, phase string, start time.Time) {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	const mib = 1024 * 1024
	t.Logf("%-28s t=%6.1fs heapAlloc=%5dMiB heapSys=%5dMiB sys=%5dMiB totalAlloc=%6dMiB numGC=%d",
		phase, time.Since(start).Seconds(), m.HeapAlloc/mib, m.HeapSys/mib, m.Sys/mib, m.TotalAlloc/mib, m.NumGC)
}

func liveAfterGC(t *testing.T, out, phase string, start time.Time) {
	runtime.GC()
	memLine(t, phase+" (live after GC)", start)
	if out == "" {
		return
	}
	f, err := os.Create(filepath.Join(out, "heap-"+phase+".pprof"))
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	if err := pprof.WriteHeapProfile(f); err != nil {
		t.Fatal(err)
	}
}

// buildSSAProjectOnly is buildSSA that builds SSA bodies only for project packages.
func buildSSAProjectOnly(req *pb.BuildProgramRequest) (*ssa.Program, []*ssa.Package, map[string]*packages.Package, error) {
	cfg := &packages.Config{
		Mode: packages.NeedFiles | packages.NeedSyntax | packages.NeedTypes |
			packages.NeedTypesInfo | packages.NeedImports | packages.NeedDeps |
			packages.NeedName | packages.NeedModule,
		Dir: req.WorkingDir,
	}
	loaded, err := packages.Load(cfg, req.Patterns...)
	if err != nil {
		return nil, nil, nil, err
	}
	info := make(map[string]*packages.Package)
	packages.Visit(loaded, func(p *packages.Package) bool {
		if _, ok := info[p.PkgPath]; !ok {
			info[p.PkgPath] = p
		}
		return true
	}, nil)
	mode := ssa.BuilderMode(0)
	if req.InstantiateGenerics {
		mode |= ssa.InstantiateGenerics
	}
	if req.SanityCheck {
		mode |= ssa.SanityCheckFunctions
	}
	prog, _ := ssautil.AllPackages(loaded, mode)
	built := 0
	for _, p := range prog.AllPackages() {
		if p == nil || p.Pkg == nil {
			continue
		}
		isStdlib, isDep := classifyPackage(info[p.Pkg.Path()], map[string]bool{}, false)
		if !isStdlib && !isDep {
			p.Build()
			built++
		}
	}
	fmt.Fprintf(os.Stderr, "project-only: built %d packages\n", built)
	all := make([]*ssa.Package, 0, len(prog.AllPackages()))
	for _, p := range prog.AllPackages() {
		if p != nil && p.Pkg != nil {
			all = append(all, p)
		}
	}
	sort.Slice(all, func(i, j int) bool { return all[i].Pkg.Path() < all[j].Pkg.Path() })
	return prog, all, info, nil
}

func TestMemPhases(t *testing.T) {
	dir := os.Getenv("GOIR_MEM_DIR")
	if dir == "" {
		t.Skip("GOIR_MEM_DIR not set")
	}
	out := os.Getenv("GOIR_MEM_OUT")
	gcOnPhases := os.Getenv("GOIR_MEM_GC") != ""
	if out != "" {
		_ = os.MkdirAll(out, 0o755)
	}

	var peakHeap, peakSys uint64
	stop := make(chan struct{})
	go func() {
		tk := time.NewTicker(100 * time.Millisecond)
		defer tk.Stop()
		for {
			select {
			case <-stop:
				return
			case <-tk.C:
				var m runtime.MemStats
				runtime.ReadMemStats(&m)
				if m.HeapAlloc > peakHeap {
					peakHeap = m.HeapAlloc
				}
				if m.Sys > peakSys {
					peakSys = m.Sys
				}
			}
		}
	}()

	start := time.Now()
	req := &pb.BuildProgramRequest{
		Patterns:            []string{"./..."},
		WorkingDir:          dir,
		Mode:                pb.LoadMode_LOAD_MODE_PROJECT,
		InstantiateGenerics: true,
		SanityCheck:         true,
	}
	memLine(t, "start", start)
	var (
		prog *ssa.Program
		pkgs []*ssa.Package
		info map[string]*packages.Package
		err  error
	)
	if os.Getenv("GOIR_MEM_PROJECT_ONLY") != "" {
		prog, pkgs, info, err = buildSSAProjectOnly(req)
	} else {
		prog, pkgs, info, err = buildSSA(req)
	}
	if err != nil {
		t.Fatal(err)
	}
	memLine(t, "after load+ssa build", start)
	if gcOnPhases {
		liveAfterGC(t, out, "1-ssa", start)
	}

	ser := newSerializerForBuild(prog, pkgs, info, req.Mode, map[string]bool{})
	program, serErrs := ser.serializeProgram()
	memLine(t, "after serializeProgram", start)
	if gcOnPhases {
		liveAfterGC(t, out, "2-serialized", start)
	}

	b, err := proto.Marshal(program)
	if err != nil {
		t.Fatal(err)
	}
	memLine(t, "after proto.Marshal", start)
	if gcOnPhases {
		liveAfterGC(t, out, "3-marshalled", start)
	}
	close(stop)
	t.Logf("serErrs=%d packages=%d functionBodies=%d types=%d marshalledSize=%dMiB",
		len(serErrs), len(program.Packages), len(program.FunctionBodies), len(program.Types), len(b)/(1024*1024))
	t.Logf("PEAK sampled heapAlloc=%dMiB sys=%dMiB", peakHeap/(1024*1024), peakSys/(1024*1024))
	runtime.KeepAlive(prog)
	runtime.KeepAlive(program)
	runtime.KeepAlive(b)
	fmt.Fprintln(os.Stderr, "done")
}
