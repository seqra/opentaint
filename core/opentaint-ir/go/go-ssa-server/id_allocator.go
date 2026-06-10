package server

import (
	"go/types"
	"log"
	"sync"

	"golang.org/x/tools/go/ssa"
)

// idAllocator is the per-session table mapping SSA / types entities to
// stable wire IDs. All public methods are safe for concurrent use; a single
// internal Mutex guards every map and counter so that concurrent RPC stream
// loops sharing the same session cannot corrupt the maps.
type idAllocator struct {
	mu sync.Mutex

	typeIDs     map[types.Type]int32
	packageIDs  map[*ssa.Package]int32
	functionIDs map[*ssa.Function]int32
	namedIDs    map[*types.TypeName]int32
	globalIDs   map[*ssa.Global]int32
	constIDs    map[*ssa.NamedConst]int32

	// Reverse lookup tables maintained alongside the forward maps.
	functionByIDMap map[int32]*ssa.Function

	// Per-session "already streamed to the client" sets. These are appended
	// to (never cleared) so that subsequent calls only re-stream entities
	// that have not yet been delivered.
	streamedTypes     map[types.Type]bool
	streamedFunctions map[*ssa.Function]bool
	streamedGlobals   map[*ssa.Global]bool

	nextTypeID     int32
	nextPackageID  int32
	nextFunctionID int32
	nextNamedID    int32
	nextGlobalID   int32
	nextConstID    int32
}

func newIDAllocator() *idAllocator {
	return &idAllocator{
		typeIDs:           make(map[types.Type]int32),
		packageIDs:        make(map[*ssa.Package]int32),
		functionIDs:       make(map[*ssa.Function]int32),
		namedIDs:          make(map[*types.TypeName]int32),
		globalIDs:         make(map[*ssa.Global]int32),
		constIDs:          make(map[*ssa.NamedConst]int32),
		functionByIDMap:   make(map[int32]*ssa.Function),
		streamedTypes:     make(map[types.Type]bool),
		streamedFunctions: make(map[*ssa.Function]bool),
		streamedGlobals:   make(map[*ssa.Global]bool),
		nextTypeID:        1,
		nextPackageID:     1,
		nextFunctionID:    1,
		nextNamedID:       1,
		nextGlobalID:      1,
		nextConstID:       1,
	}
}

func (a *idAllocator) typeID(t types.Type) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.typeIDs[t]; ok {
		return id
	}
	id := a.nextTypeID
	a.nextTypeID++
	a.typeIDs[t] = id
	return id
}

func (a *idAllocator) packageID(p *ssa.Package) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.packageIDs[p]; ok {
		return id
	}
	id := a.nextPackageID
	a.nextPackageID++
	a.packageIDs[p] = id
	return id
}

// bindPackageID forces p to use the supplied id (sourced from the package
// summary). If a different id was already allocated for p, log a warning and
// overwrite — the summary id is authoritative for cross-RPC stability. This
// catches mis-orderings deterministically rather than silently diverging.
func (a *idAllocator) bindPackageID(p *ssa.Package, id int32) {
	if p == nil || id <= 0 {
		return
	}
	a.mu.Lock()
	defer a.mu.Unlock()
	if existing, ok := a.packageIDs[p]; ok && existing != id {
		log.Printf("WARN: bindPackageID mismatch for %s: existing=%d, summary=%d; overwriting to summary id", p.Pkg.Path(), existing, id)
	}
	a.packageIDs[p] = id
	if a.nextPackageID <= id {
		a.nextPackageID = id + 1
	}
}

func (a *idAllocator) functionID(f *ssa.Function) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.functionIDs[f]; ok {
		return id
	}
	id := a.nextFunctionID
	a.nextFunctionID++
	a.functionIDs[f] = id
	a.functionByIDMap[id] = f
	return id
}

func (a *idAllocator) functionByID(id int32) *ssa.Function {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.functionByIDMap[id]
}

func (a *idAllocator) namedID(n *types.TypeName) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.namedIDs[n]; ok {
		return id
	}
	id := a.nextNamedID
	a.nextNamedID++
	a.namedIDs[n] = id
	return id
}

func (a *idAllocator) globalID(g *ssa.Global) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.globalIDs[g]; ok {
		return id
	}
	id := a.nextGlobalID
	a.nextGlobalID++
	a.globalIDs[g] = id
	return id
}

func (a *idAllocator) constID(c *ssa.NamedConst) int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	if id, ok := a.constIDs[c]; ok {
		return id
	}
	id := a.nextConstID
	a.nextConstID++
	a.constIDs[c] = id
	return id
}

// ─── Streamed-set tracking ──────────────────────────────────────────

func (a *idAllocator) isTypeStreamed(t types.Type) bool {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.streamedTypes[t]
}

func (a *idAllocator) markTypeStreamed(t types.Type) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.streamedTypes[t] = true
}

func (a *idAllocator) isFunctionStreamed(f *ssa.Function) bool {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.streamedFunctions[f]
}

func (a *idAllocator) markFunctionStreamed(f *ssa.Function) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.streamedFunctions[f] = true
}

func (a *idAllocator) isGlobalStreamed(g *ssa.Global) bool {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.streamedGlobals[g]
}

func (a *idAllocator) markGlobalStreamed(g *ssa.Global) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.streamedGlobals[g] = true
}

// snapshotFunctionIDs returns a copy of the function→id map for safe
// iteration outside the allocator lock. Used by code paths that need to
// scan all known functions (e.g. external stub collection) without
// holding the lock during downstream calls.
func (a *idAllocator) snapshotFunctionIDs() map[*ssa.Function]int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	out := make(map[*ssa.Function]int32, len(a.functionIDs))
	for k, v := range a.functionIDs {
		out[k] = v
	}
	return out
}

func (a *idAllocator) snapshotNamedIDs() map[*types.TypeName]int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	out := make(map[*types.TypeName]int32, len(a.namedIDs))
	for k, v := range a.namedIDs {
		out[k] = v
	}
	return out
}

func (a *idAllocator) snapshotTypeIDs() map[types.Type]int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	out := make(map[types.Type]int32, len(a.typeIDs))
	for k, v := range a.typeIDs {
		out[k] = v
	}
	return out
}

func (a *idAllocator) snapshotGlobalIDs() map[*ssa.Global]int32 {
	a.mu.Lock()
	defer a.mu.Unlock()
	out := make(map[*ssa.Global]int32, len(a.globalIDs))
	for k, v := range a.globalIDs {
		out[k] = v
	}
	return out
}
