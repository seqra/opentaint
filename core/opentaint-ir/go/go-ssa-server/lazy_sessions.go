package server

import (
	"fmt"
	"log"
	"os"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

const (
	lazySessionTTL         = 30 * time.Minute
	lazySessionMaxSessions = 128
)

type sessionManager struct {
	mu       sync.Mutex
	nextID   uint64
	sessions map[string]*lazySession
}

type packageSummary struct {
	id  int32
	pkg *packages.Package
}

type lazySession struct {
	mu sync.Mutex

	id         string
	req        *pb.OpenSessionRequest
	createdAt  time.Time
	lastAccess time.Time

	ids *idAllocator

	packageSummaries []*packageSummary
	packageByID      map[int32]*packageSummary
	packageByPath    map[string]*packageSummary

	prog    *ssa.Program
	ssaPkgs map[string]*ssa.Package
	built   bool
}

func newSessionManager() *sessionManager {
	return &sessionManager{sessions: make(map[string]*lazySession)}
}

func (m *sessionManager) create(req *pb.OpenSessionRequest) (*lazySession, error) {
	if req.IncludeDependencies || req.IncludeStdlib {
		return nil, fmt.Errorf("lazy include_dependencies/include_stdlib are not supported yet")
	}
	pkgs, elapsed, err := loadPackageList(req)
	if err != nil {
		return nil, err
	}

	id := atomic.AddUint64(&m.nextID, 1)
	now := time.Now()
	sess := &lazySession{
		id:            strconv.FormatUint(id, 10),
		req:           req,
		createdAt:     now,
		lastAccess:    now,
		ids:           newIDAllocator(),
		packageByID:   make(map[int32]*packageSummary),
		packageByPath: make(map[string]*packageSummary),
		ssaPkgs:       make(map[string]*ssa.Package),
	}
	for i, pkg := range pkgs {
		ps := &packageSummary{id: int32(i + 1), pkg: pkg}
		sess.packageSummaries = append(sess.packageSummaries, ps)
		sess.packageByID[ps.id] = ps
		sess.packageByPath[pkg.PkgPath] = ps
	}
	_ = elapsed

	m.mu.Lock()
	m.cleanupLocked(time.Now())
	if len(m.sessions) >= lazySessionMaxSessions {
		m.evictOldestLocked()
	}
	m.sessions[sess.id] = sess
	m.mu.Unlock()
	return sess, nil
}

func (m *sessionManager) get(id string) (*lazySession, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.cleanupLocked(time.Now())
	sess, ok := m.sessions[id]
	if ok {
		sess.lastAccess = time.Now()
	}
	return sess, ok
}

func (m *sessionManager) close(id string) bool {
	m.mu.Lock()
	sess, ok := m.sessions[id]
	if !ok {
		m.mu.Unlock()
		return false
	}
	delete(m.sessions, id)
	m.mu.Unlock()

	// The SSA program plus the per-session id-allocator maps pin the entire
	// parsed/type-checked package graph (often hundreds of MB). Without an
	// explicit nil-out Go's GC keeps the whole arena alive through whatever
	// transient stack reference still touches the *lazySession. Explicitly
	// release here so back-to-back OpenSession calls don't accumulate.
	sess.release()
	// Encourage the runtime to return freed pages to the OS — without this,
	// long-running batches see RSS grow even as the in-use heap shrinks.
	runtime.GC()
	debug.FreeOSMemory()
	return true
}

func (m *sessionManager) cleanupLocked(now time.Time) {
	for id, sess := range m.sessions {
		if now.Sub(sess.lastAccess) > lazySessionTTL {
			delete(m.sessions, id)
			sess.release()
		}
	}
}

// evictOldestLocked drops the LRU session, but only if that LRU session is
// itself older than the idle TTL. This prevents eviction of sessions that
// are still actively being used while LRU index churns.
func (m *sessionManager) evictOldestLocked() {
	now := time.Now()
	var oldestID string
	var oldest time.Time
	for id, sess := range m.sessions {
		if oldestID == "" || sess.lastAccess.Before(oldest) {
			oldestID = id
			oldest = sess.lastAccess
		}
	}
	if oldestID == "" {
		return
	}
	if now.Sub(oldest) < lazySessionTTL {
		return // LRU is still fresh; skip eviction
	}
	sess := m.sessions[oldestID]
	delete(m.sessions, oldestID)
	sess.release()
}

// touch updates the lastAccess timestamp under the manager lock. Used by
// RPC handlers to keep actively-streaming sessions alive even when no `get`
// call has been made for a while.
func (m *sessionManager) touch(id string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if sess, ok := m.sessions[id]; ok {
		sess.lastAccess = time.Now()
	}
}

func loadPackageList(req *pb.OpenSessionRequest) ([]*packages.Package, time.Duration, error) {
	start := time.Now()
	cfg := packageConfigFromLazy(req, packages.NeedName|packages.NeedFiles|packages.NeedCompiledGoFiles|packages.NeedModule)
	pkgs, err := packages.Load(cfg, req.Patterns...)
	if err != nil {
		return nil, 0, fmt.Errorf("packages.Load package list: %w", err)
	}
	// Drop synthetic pattern placeholders: when `packages.Load` cannot
	// resolve a pattern (e.g. `./api/...` against a module without an `api`
	// subdir) it returns a fake package whose `PkgPath` equals the pattern,
	// no Go files, no Name, and a load error. Surfacing it as a real package
	// summary would later trigger sanity-check failures on the client. Eager
	// `BuildProgram` simply ignores such packages because they never get
	// SSA-built; we do the same here.
	filtered := pkgs[:0]
	for _, p := range pkgs {
		if p.Name == "" && len(p.GoFiles) == 0 && len(p.CompiledGoFiles) == 0 && len(p.Errors) > 0 {
			for _, e := range p.Errors {
				log.Printf("WARN: dropping unresolved pattern package %s: %v", p.PkgPath, e)
			}
			continue
		}
		filtered = append(filtered, p)
	}
	return filtered, time.Since(start), nil
}

// release drops every reference the session holds to parsed packages, SSA
// state, and the per-session id-allocator. Called from sessionManager.close so
// memory can be reclaimed even while the *lazySession struct itself is briefly
// kept alive by an in-flight handler frame.
func (s *lazySession) release() {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.prog = nil
	s.ssaPkgs = nil
	s.packageSummaries = nil
	s.packageByID = nil
	s.packageByPath = nil
	s.ids = nil
	s.built = false
}

func (s *lazySession) loadPackage(id int32) (*serializer, *ssa.Package, time.Duration, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	ps, err := s.findPackage(id)
	if err != nil {
		return nil, nil, 0, err
	}
	start := time.Now()
	if err := s.ensureProgramBuilt(); err != nil {
		return nil, nil, 0, err
	}
	ssaPkg := s.ssaPkgs[ps.pkg.PkgPath]
	if ssaPkg == nil {
		// SSA build skipped this package (typically because it has type
		// errors or transitively imports an ill-typed dependency). Return
		// a placeholder serializer that emits a minimal empty ProtoPackage
		// so the client can mark the package loaded without any members.
		// Eager `BuildProgram` silently omits such packages from the program
		// stream too; we mirror that behavior here instead of failing the
		// whole session.
		log.Printf("lazy session %s: SSA package missing for %s; returning empty placeholder", s.id, ps.pkg.PkgPath)
		ser := newPlaceholderPackageSerializer(s.prog, ps, s.ids)
		return ser, nil, time.Since(start), nil
	}
	ser := newLazyPackageSerializer(s.prog, ssaPkg, s.ids)
	return ser, ssaPkg, time.Since(start), nil
}

func (s *lazySession) loadFunctionBody(functionID int32) (*serializer, *ssa.Function, time.Duration, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	start := time.Now()
	if err := s.ensureProgramBuilt(); err != nil {
		return nil, nil, 0, err
	}
	target := s.ids.functionByID(functionID)
	if target == nil {
		return nil, nil, 0, fmt.Errorf("function id %d is unknown; load its package first", functionID)
	}
	if len(target.Blocks) == 0 {
		return nil, nil, 0, fmt.Errorf("function %s has no SSA body", target.String())
	}
	ser := newLazyFunctionBodySerializer(s.prog, target, s.ids)
	return ser, target, time.Since(start), nil
}

func (s *lazySession) ensureProgramBuilt() error {
	if s.prog == nil {
		cfg := packageConfigFromLazy(s.req, packages.NeedFiles|packages.NeedSyntax|packages.NeedTypes|packages.NeedTypesInfo|packages.NeedImports|packages.NeedDeps|packages.NeedName|packages.NeedModule)
		pkgs, err := packages.Load(cfg, s.req.Patterns...)
		if err != nil {
			return fmt.Errorf("packages.Load SSA: %w", err)
		}
		for _, pkg := range pkgs {
			for _, e := range pkg.Errors {
				log.Printf("WARN: package %s: %v", pkg.PkgPath, e)
			}
		}
		mode := ssa.BuilderMode(0)
		if s.req.InstantiateGenerics {
			mode |= ssa.InstantiateGenerics
		}
		if s.req.SanityCheck {
			mode |= ssa.SanityCheckFunctions
		}
		prog, ssaPkgs := ssautil.AllPackages(pkgs, mode)
		s.prog = prog
		for _, p := range ssaPkgs {
			if p != nil && p.Pkg != nil {
				s.ssaPkgs[p.Pkg.Path()] = p
				if ps := s.packageByPath[p.Pkg.Path()]; ps != nil {
					s.ids.bindPackageID(p, ps.id)
				}
			}
		}
	}
	// Program-wide SSA build on first materialization. x/tools's
	// (*ssa.Package).Build() is not safe to use on a single package without
	// also building its dependencies; cross-package call resolution and
	// generic instantiations need every dependent to have been Built first.
	// This is a documented x/tools limitation, so we accept the eager SSA
	// build cost once per session here.
	if !s.built {
		s.prog.Build()
		s.built = true
	}
	return nil
}

func (s *lazySession) findPackage(id int32) (*packageSummary, error) {
	if id != 0 {
		if ps := s.packageByID[id]; ps != nil {
			return ps, nil
		}
	}
	return nil, fmt.Errorf("package not found: id=%d", id)
}

func (s *lazySession) protoPackageSummaries() []*pb.ProtoPackageSummary {
	out := make([]*pb.ProtoPackageSummary, 0, len(s.packageSummaries))
	rootPaths := make(map[string]bool, len(s.req.Patterns))
	for _, p := range s.req.Patterns {
		rootPaths[p] = true
	}
	for _, ps := range s.packageSummaries {
		pkg := ps.pkg
		pp := &pb.ProtoPackageSummary{
			Id:              ps.id,
			ImportPath:      pkg.PkgPath,
			Name:            pkg.Name,
			GoFiles:         append([]string(nil), pkg.GoFiles...),
			CompiledGoFiles: append([]string(nil), pkg.CompiledGoFiles...),
		}
		if pkg.Module != nil {
			pp.ModulePath = pkg.Module.Path
			pp.ModuleDir = pkg.Module.Dir
		}
		pp.IsStdlib = pkg.Module == nil && !strings.Contains(pkg.PkgPath, ".")
		pp.IsDependency = !rootPaths[pkg.PkgPath]
		for _, e := range pkg.Errors {
			pp.Errors = append(pp.Errors, e.Msg)
		}
		out = append(out, pp)
	}
	sort.Slice(out, func(i, j int) bool { return out[i].ImportPath < out[j].ImportPath })
	return out
}

func packageConfigFromLazy(req *pb.OpenSessionRequest, mode packages.LoadMode) *packages.Config {
	cfg := &packages.Config{Mode: mode, Dir: req.WorkingDir}
	if len(req.BuildTags) > 0 {
		cfg.BuildFlags = []string{"-tags=" + strings.Join(req.BuildTags, ",")}
	}
	if req.Gopath != "" {
		env := os.Environ()
		env = append(env, "GOPATH="+req.Gopath)
		cfg.Env = env
	}
	if req.Goroot != "" {
		if cfg.Env == nil {
			cfg.Env = os.Environ()
		}
		cfg.Env = append(cfg.Env, "GOROOT="+req.Goroot)
	}
	return cfg
}
