package server

import (
	"context"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
	"google.golang.org/grpc/metadata"
)

type loadPackageRecorder struct {
	pb.GoSSAService_LoadPackageServer
	responses []*pb.LoadPackageResponse
}

func (s *loadPackageRecorder) Send(resp *pb.LoadPackageResponse) error {
	s.responses = append(s.responses, resp)
	return nil
}

func (s *loadPackageRecorder) SetHeader(metadata.MD) error  { return nil }
func (s *loadPackageRecorder) SendHeader(metadata.MD) error { return nil }
func (s *loadPackageRecorder) SetTrailer(metadata.MD)       {}
func (s *loadPackageRecorder) Context() context.Context     { return context.Background() }
func (s *loadPackageRecorder) SendMsg(any) error            { return nil }
func (s *loadPackageRecorder) RecvMsg(any) error            { return io.EOF }

type loadFunctionBodyRecorder struct {
	pb.GoSSAService_LoadFunctionBodyServer
	responses []*pb.LoadFunctionBodyResponse
}

func (s *loadFunctionBodyRecorder) Send(resp *pb.LoadFunctionBodyResponse) error {
	s.responses = append(s.responses, resp)
	return nil
}

func (s *loadFunctionBodyRecorder) SetHeader(metadata.MD) error  { return nil }
func (s *loadFunctionBodyRecorder) SendHeader(metadata.MD) error { return nil }
func (s *loadFunctionBodyRecorder) SetTrailer(metadata.MD)       {}
func (s *loadFunctionBodyRecorder) Context() context.Context     { return context.Background() }
func (s *loadFunctionBodyRecorder) SendMsg(any) error            { return nil }
func (s *loadFunctionBodyRecorder) RecvMsg(any) error            { return io.EOF }

func TestLazySessionOpenListsPackagesWithoutSSA(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")

	resp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	if resp.GetError() != nil {
		t.Fatalf("OpenSession protocol error: %s", resp.GetError().GetMessage())
	}
	if resp.GetSessionId() == "" {
		t.Fatal("OpenSession returned an empty session id")
	}
	if len(resp.GetPackages()) != 1 {
		t.Fatalf("OpenSession package count = %d, want 1", len(resp.GetPackages()))
	}
	pkg := resp.GetPackages()[0]
	if pkg.GetImportPath() != "example.com/lazyfixture" {
		t.Fatalf("OpenSession import path = %q, want example.com/lazyfixture", pkg.GetImportPath())
	}
	if server.sessions.sessions[resp.GetSessionId()].prog != nil {
		t.Fatal("OpenSession eagerly initialized SSA program")
	}
}

func TestLazyPackageLoadReturnsDeclarationsWithoutBodies(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")

	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	stream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, stream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}

	var packageDef *pb.ProtoPackage
	for _, resp := range stream.responses {
		if resp.GetError() != nil {
			t.Fatalf("LoadPackage protocol error: %s", resp.GetError().GetMessage())
		}
		if _, ok := resp.GetPayload().(*pb.LoadPackageResponse_PackageDef); ok {
			packageDef = resp.GetPackageDef()
		}
	}
	if packageDef == nil {
		t.Fatal("LoadPackage did not stream a package definition")
	}
	if len(packageDef.GetFunctions()) < 2 {
		t.Fatalf("LoadPackage function count = %d, want at least 2", len(packageDef.GetFunctions()))
	}
	for _, fn := range packageDef.GetFunctions() {
		if !fn.GetHasBody() {
			t.Fatalf("function %s did not advertise an available body", fn.GetName())
		}
	}
	for _, resp := range stream.responses {
		if resp.GetPayload() == nil {
			continue
		}
		switch resp.GetPayload().(type) {
		case *pb.LoadPackageResponse_TypeDef, *pb.LoadPackageResponse_PackageDef, *pb.LoadPackageResponse_Summary:
			// expected signature-only payloads
		default:
			t.Fatalf("LoadPackage streamed unexpected payload type %T", resp.GetPayload())
		}
	}
}

func TestLazyFunctionBodyLoadReturnsOnlyRequestedBodyAndCachesSSA(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")

	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	pkgStream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, pkgStream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}

	var targetID int32
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				if fn.GetName() == "First" {
					targetID = fn.GetId()
				}
			}
		}
	}
	if targetID == 0 {
		t.Fatal("LoadPackage did not return function First")
	}

	sess := server.sessions.sessions[openResp.GetSessionId()]
	progBeforeBodyLoad := sess.prog
	bodyStream := &loadFunctionBodyRecorder{}
	if err := server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: targetID}, bodyStream); err != nil {
		t.Fatalf("LoadFunctionBody returned error: %v", err)
	}
	if sess.prog != progBeforeBodyLoad {
		t.Fatal("LoadFunctionBody rebuilt the session SSA program instead of reusing cached state")
	}

	bodyCount := 0
	for _, resp := range bodyStream.responses {
		if resp.GetError() != nil {
			t.Fatalf("LoadFunctionBody protocol error: %s", resp.GetError().GetMessage())
		}
		if body := resp.GetFunctionBody(); body != nil {
			bodyCount++
			if body.GetFunctionId() != targetID {
				t.Fatalf("LoadFunctionBody streamed body for function id %d, want %d", body.GetFunctionId(), targetID)
			}
			if len(body.GetBlocks()) == 0 {
				t.Fatal("LoadFunctionBody streamed an empty body")
			}
		}
	}
	if bodyCount != 1 {
		t.Fatalf("LoadFunctionBody body count = %d, want 1", bodyCount)
	}
}

func TestLazyPackageIDsStableWhenLoadingOutOfOrder(t *testing.T) {
	dir := writeMultiPackageFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	var target *pb.ProtoPackageSummary
	for _, pkg := range openResp.GetPackages() {
		if pkg.GetImportPath() == "example.com/lazyfixture/b" {
			target = pkg
			break
		}
	}
	if target == nil {
		t.Fatalf("did not find package b in summaries: %v", openResp.GetPackages())
	}
	stream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: target.GetId()}, stream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}
	var packageDef *pb.ProtoPackage
	for _, resp := range stream.responses {
		if resp.GetError() != nil {
			t.Fatalf("LoadPackage protocol error: %s", resp.GetError().GetMessage())
		}
		if pp := resp.GetPackageDef(); pp != nil {
			packageDef = pp
		}
	}
	if packageDef == nil {
		t.Fatal("LoadPackage did not stream package definition")
	}
	if packageDef.GetId() != target.GetId() {
		t.Fatalf("loaded package id = %d, want summary id %d", packageDef.GetId(), target.GetId())
	}
}

func TestLazyFunctionBodyStreamsBodyLocalTypesAndExternalCalleeStubs(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	pkgStream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, pkgStream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}
	var targetID int32
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				if fn.GetName() == "BodyLocal" {
					targetID = fn.GetId()
				}
			}
		}
	}
	if targetID == 0 {
		t.Fatal("LoadPackage did not return function BodyLocal")
	}
	bodyStream := &loadFunctionBodyRecorder{}
	if err := server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: targetID}, bodyStream); err != nil {
		t.Fatalf("LoadFunctionBody returned error: %v", err)
	}
	var sawStructType, sawFmtStub bool
	for _, resp := range bodyStream.responses {
		if resp.GetError() != nil {
			t.Fatalf("LoadFunctionBody protocol error: %s", resp.GetError().GetMessage())
		}
		if td := resp.GetTypeDef(); td != nil && td.GetStructType() != nil {
			sawStructType = true
		}
		if pp := resp.GetPackageDef(); pp != nil {
			for _, fn := range pp.GetFunctions() {
				if pp.GetImportPath() == "fmt" && fn.GetName() == "Sprint" {
					sawFmtStub = true
				}
				if fn.GetName() == "Second" {
					t.Fatal("LoadFunctionBody over-streamed unrelated known package function Second")
				}
			}
		}
	}
	if !sawStructType {
		t.Fatal("LoadFunctionBody did not stream a body-local struct type definition")
	}
	if !sawFmtStub {
		t.Fatal("LoadFunctionBody did not stream metadata for referenced fmt.Sprint callee")
	}
}

func TestLazyPackageStreamsClosureMetadata(t *testing.T) {
	// Per M11/M18: anonymous closures and instantiated generics are now
	// enumerated by LoadPackage via ssautil.AllFunctions, so the closure
	// inside ClosureFactory appears in the loaded user package directly.
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	pkgStream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, pkgStream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}
	var factoryID int32
	var sawClosure bool
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				if fn.GetName() == "ClosureFactory" {
					factoryID = fn.GetId()
				}
			}
		}
	}
	if factoryID == 0 {
		t.Fatal("LoadPackage did not return ClosureFactory")
	}
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				if fn.GetParentFunctionId() == factoryID {
					sawClosure = true
				}
			}
		}
	}
	if !sawClosure {
		t.Fatal("LoadPackage did not include the anonymous closure of ClosureFactory in pp.Functions")
	}
}

func TestLazyFunctionBodyDoesNotSerializeUnrelatedPackage(t *testing.T) {
	dir := writeMultiPackageFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	var pkgA *pb.ProtoPackageSummary
	for _, pkg := range openResp.GetPackages() {
		if pkg.GetImportPath() == "example.com/lazyfixture/a" {
			pkgA = pkg
			break
		}
	}
	if pkgA == nil {
		t.Fatal("did not find package a summary")
	}
	pkgStream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: pkgA.GetId()}, pkgStream); err != nil {
		t.Fatalf("LoadPackage returned error: %v", err)
	}
	var targetID int32
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				if fn.GetName() == "A" {
					targetID = fn.GetId()
				}
			}
		}
	}
	if targetID == 0 {
		t.Fatal("LoadPackage did not return function A")
	}
	bodyStream := &loadFunctionBodyRecorder{}
	if err := server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: targetID}, bodyStream); err != nil {
		t.Fatalf("LoadFunctionBody returned error: %v", err)
	}
	for _, resp := range bodyStream.responses {
		if resp.GetError() != nil {
			t.Fatalf("LoadFunctionBody protocol error: %s", resp.GetError().GetMessage())
		}
		if pp := resp.GetPackageDef(); pp != nil && pp.GetImportPath() == "example.com/lazyfixture/b" {
			t.Fatal("LoadFunctionBody serialized unrelated package b declarations")
		}
		if body := resp.GetFunctionBody(); body != nil && body.GetFunctionId() != targetID {
			t.Fatalf("LoadFunctionBody serialized unrelated function body id %d", body.GetFunctionId())
		}
	}
}

func TestLazyOpenRejectsUnsupportedIncludeFlags(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")
	req := lazyFixtureRequest(dir)
	req.IncludeStdlib = true
	resp, err := server.OpenSession(context.Background(), req)
	if err != nil {
		t.Fatalf("OpenSession returned transport error: %v", err)
	}
	if resp.GetError() == nil || !strings.Contains(resp.GetError().GetMessage(), "not supported") {
		t.Fatalf("OpenSession error = %v, want unsupported include flags", resp.GetError())
	}
}

// TestLazyConcurrentLoadIsRaceFree exercises concurrent LoadPackage +
// LoadFunctionBody on a single session under -race to catch idAllocator
// concurrent-map writes (review id C1).
func TestLazyConcurrentLoadIsRaceFree(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	pkgID := openResp.GetPackages()[0].GetId()
	// Warm up by doing one LoadPackage so function IDs are present.
	warm := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: pkgID}, warm); err != nil {
		t.Fatalf("warm LoadPackage error: %v", err)
	}
	var firstID, secondID int32
	for _, resp := range warm.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				switch fn.GetName() {
				case "First":
					firstID = fn.GetId()
				case "Second":
					secondID = fn.GetId()
				}
			}
		}
	}
	if firstID == 0 || secondID == 0 {
		t.Fatalf("warm load missing function ids: first=%d second=%d", firstID, secondID)
	}
	done := make(chan error, 4)
	go func() {
		rec := &loadPackageRecorder{}
		done <- server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: pkgID}, rec)
	}()
	go func() {
		rec := &loadFunctionBodyRecorder{}
		done <- server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: firstID}, rec)
	}()
	go func() {
		rec := &loadFunctionBodyRecorder{}
		done <- server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: secondID}, rec)
	}()
	go func() {
		rec := &loadPackageRecorder{}
		done <- server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: pkgID}, rec)
	}()
	for i := 0; i < 4; i++ {
		if err := <-done; err != nil {
			t.Fatalf("concurrent rpc error: %v", err)
		}
	}
}

// TestLazyTwoBodyLoadsBothSeeSharedType: two body loads of distinct
// functions sharing the same body-local type must both deliver a usable
// reference (review ids M3 + M17). The first stream sends the
// ProtoTypeDefinition; the second is allowed to skip it because the
// session-wide streamedTypes set already marked it as delivered.
// What MUST hold is that no second-stream TypeId is referenced that the
// client has never seen.
func TestLazyTwoBodyLoadsBothSeeSharedType(t *testing.T) {
	dir := writeSharedTypeFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession returned error: %v", err)
	}
	pkgStream := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, pkgStream); err != nil {
		t.Fatalf("LoadPackage error: %v", err)
	}
	var id1, id2 int32
	for _, resp := range pkgStream.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			for _, fn := range pkg.GetFunctions() {
				switch fn.GetName() {
				case "UseShared1":
					id1 = fn.GetId()
				case "UseShared2":
					id2 = fn.GetId()
				}
			}
		}
	}
	if id1 == 0 || id2 == 0 {
		t.Fatalf("missing function ids: %d %d", id1, id2)
	}
	knownTypes := make(map[int32]bool)
	collectKnown := func(td *pb.ProtoTypeDefinition) {
		if td == nil {
			return
		}
		knownTypes[td.GetId()] = true
	}
	for _, resp := range pkgStream.responses {
		collectKnown(resp.GetTypeDef())
	}
	run := func(fid int32) {
		body := &loadFunctionBodyRecorder{}
		if err := server.LoadFunctionBody(&pb.LoadFunctionBodyRequest{SessionId: openResp.GetSessionId(), FunctionId: fid}, body); err != nil {
			t.Fatalf("LoadFunctionBody %d: %v", fid, err)
		}
		for _, resp := range body.responses {
			if resp.GetError() != nil {
				t.Fatalf("body protocol error: %s", resp.GetError().GetMessage())
			}
			collectKnown(resp.GetTypeDef())
			if b := resp.GetFunctionBody(); b != nil {
				for _, blk := range b.GetBlocks() {
					for _, inst := range blk.GetInstructions() {
						if tid := inst.GetTypeId(); tid != 0 && !knownTypes[tid] {
							t.Fatalf("body of function %d references unknown TypeId %d", fid, tid)
						}
					}
				}
			}
		}
	}
	run(id1)
	run(id2)
}

// TestLazyImportsReferenceStdlibStub: stdlib import (fmt) must be present
// in ImportIds of the loaded user package and a corresponding stub package
// must be streamed (review id M20).
func TestLazyImportsReferenceStdlibStub(t *testing.T) {
	dir := writeLazyFixture(t)
	server := NewGoSSAServer("test", "go-test")
	openResp, err := server.OpenSession(context.Background(), lazyFixtureRequest(dir))
	if err != nil {
		t.Fatalf("OpenSession error: %v", err)
	}
	rec := &loadPackageRecorder{}
	if err := server.LoadPackage(&pb.LoadPackageRequest{SessionId: openResp.GetSessionId(), PackageId: openResp.GetPackages()[0].GetId()}, rec); err != nil {
		t.Fatalf("LoadPackage error: %v", err)
	}
	var userPkg *pb.ProtoPackage
	stubsByID := make(map[int32]*pb.ProtoPackage)
	for _, resp := range rec.responses {
		if pkg := resp.GetPackageDef(); pkg != nil {
			if pkg.GetImportPath() == "example.com/lazyfixture" {
				userPkg = pkg
			} else {
				stubsByID[pkg.GetId()] = pkg
			}
		}
	}
	if userPkg == nil {
		t.Fatal("user package not streamed")
	}
	var fmtImportID int32
	for _, id := range userPkg.GetImportIds() {
		if stub, ok := stubsByID[id]; ok && stub.GetImportPath() == "fmt" {
			fmtImportID = id
		}
	}
	if fmtImportID == 0 {
		t.Fatalf("user package ImportIds did not reference fmt stub; got %v / stubs %v", userPkg.GetImportIds(), stubKeys(stubsByID))
	}
}

func stubKeys(m map[int32]*pb.ProtoPackage) []string {
	out := make([]string, 0, len(m))
	for _, v := range m {
		out = append(out, v.GetImportPath())
	}
	return out
}

func writeSharedTypeFixture(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module example.com/lazyfixture\n\ngo 1.22\n")
	writeFile(t, filepath.Join(dir, "shared.go"), `package lazyfixture

type sharedLocal struct{ Name string; N int }

func UseShared1() int {
	s := sharedLocal{Name: "a", N: 1}
	return s.N
}

func UseShared2() string {
	s := sharedLocal{Name: "b", N: 2}
	return s.Name
}
`)
	return dir
}

func TestSessionManagerCleanupBoundsSessions(t *testing.T) {
	m := newSessionManager()
	now := time.Now()
	m.sessions["old"] = &lazySession{id: "old", lastAccess: now.Add(-lazySessionTTL - time.Second)}
	m.sessions["new"] = &lazySession{id: "new", lastAccess: now}
	m.cleanupLocked(now)
	if _, ok := m.sessions["old"]; ok {
		t.Fatal("cleanup retained expired session")
	}
	if _, ok := m.sessions["new"]; !ok {
		t.Fatal("cleanup removed fresh session")
	}
}

func lazyFixtureRequest(dir string) *pb.OpenSessionRequest {
	return &pb.OpenSessionRequest{
		WorkingDir:          dir,
		Patterns:            []string{"./..."},
		InstantiateGenerics: true,
		SanityCheck:         true,
		IncludeDependencies: false,
		IncludeStdlib:       false,
	}
}

func writeLazyFixture(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module example.com/lazyfixture\n\ngo 1.22\n")
	writeFile(t, filepath.Join(dir, "lazy.go"), `package lazyfixture

import "fmt"

func First(x int) int {
	if x > 0 {
		return x + 1
	}
	return -x
}

func Second(y int) int {
	return First(y) * 2
}

func BodyLocal(x int) string {
	local := struct{ Name string }{Name: "v"}
	return fmt.Sprint(local, x)
}

func ClosureFactory(x int) func() int {
	return func() int { return x }
}
`)
	return dir
}

func writeMultiPackageFixture(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module example.com/lazyfixture\n\ngo 1.22\n")
	writeFile(t, filepath.Join(dir, "a", "a.go"), `package a

func A() int { return 1 }
`)
	writeFile(t, filepath.Join(dir, "b", "b.go"), `package b

func B() int { return 2 }
`)
	return dir
}

func writeFile(t *testing.T, path string, content string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("mkdir for %s: %v", path, err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatalf("write %s: %v", path, err)
	}
}
