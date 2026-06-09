package server

import (
	"context"
	"io"
	"net"
	"os"
	"path/filepath"
	"testing"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/test/bufconn"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

func writeTinyModule(t *testing.T) string {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module example.com/m\ngo 1.22\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	src := "package main\nimport \"strings\"\nfunc Greet(s string) string { return strings.ToUpper(s) }\nfunc main() { println(Greet(\"x\")) }\n"
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	return dir
}

func runBuild(t *testing.T, req *pb.BuildProgramRequest) ([]*pb.ProtoPackage, map[int32]bool) {
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer()
	pb.RegisterGoSSAServiceServer(srv, NewGoSSAServer("test", "test"))
	go srv.Serve(lis)
	defer srv.Stop()

	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()),
		// The bulk program payload can exceed gRPC's default 4 MB receive limit;
		// mirror the production client (GoSsaServerProcess) which allows 256 MB.
		grpc.WithDefaultCallOptions(grpc.MaxCallRecvMsgSize(256*1024*1024)))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()

	stream, err := pb.NewGoSSAServiceClient(conn).BuildProgram(context.Background(), req)
	if err != nil {
		t.Fatal(err)
	}
	var pkgs []*pb.ProtoPackage
	bodies := map[int32]bool{}
	for {
		resp, err := stream.Recv()
		if err != nil {
			if err != io.EOF {
				t.Fatalf("stream error: %v", err)
			}
			break
		}
		switch p := resp.Payload.(type) {
		case *pb.BuildProgramResponse_Program:
			pkgs = append(pkgs, p.Program.Packages...)
			for _, b := range p.Program.FunctionBodies {
				bodies[b.FunctionId] = true
			}
		case *pb.BuildProgramResponse_PackageDef:
			pkgs = append(pkgs, p.PackageDef)
		case *pb.BuildProgramResponse_FunctionBody:
			bodies[p.FunctionBody.FunctionId] = true
		case *pb.BuildProgramResponse_Error:
			if p.Error.Fatal {
				t.Fatalf("fatal: %s", p.Error.Message)
			}
		}
	}
	return pkgs, bodies
}

func findPkg(pkgs []*pb.ProtoPackage, path string) *pb.ProtoPackage {
	for _, p := range pkgs {
		if p.ImportPath == path {
			return p
		}
	}
	return nil
}

func bodyIDsOf(p *pb.ProtoPackage, bodies map[int32]bool) (withBody, total int) {
	for _, f := range p.Functions {
		if f.HasBody {
			total++
			if bodies[f.Id] {
				withBody++
			}
		}
	}
	return
}

func TestBuildProgram_ProjectMode_NoStdlibBodies(t *testing.T) {
	dir := writeTinyModule(t)
	pkgs, bodies := runBuild(t, &pb.BuildProgramRequest{WorkingDir: dir, Patterns: []string{"./..."}, Mode: pb.LoadMode_LOAD_MODE_PROJECT, InstantiateGenerics: true, SanityCheck: true})

	main := findPkg(pkgs, "example.com/m")
	if main == nil || main.IsDependency || main.IsStdlib {
		t.Fatalf("main package missing or misclassified: %+v", main)
	}
	wb, total := bodyIDsOf(main, bodies)
	if total == 0 || wb != total {
		t.Fatalf("project bodies: want all %d, got %d", total, wb)
	}
	strs := findPkg(pkgs, "strings")
	if strs == nil || !strs.IsStdlib {
		t.Fatalf("strings not present/stdlib: %+v", strs)
	}
	if wb, _ := bodyIDsOf(strs, bodies); wb != 0 {
		t.Fatalf("PROJECT mode streamed %d stdlib bodies, want 0", wb)
	}
}

func TestBuildProgram_FullMode_StreamsStdlibBodies(t *testing.T) {
	dir := writeTinyModule(t)
	pkgs, bodies := runBuild(t, &pb.BuildProgramRequest{WorkingDir: dir, Patterns: []string{"./..."}, Mode: pb.LoadMode_LOAD_MODE_FULL, InstantiateGenerics: true, SanityCheck: true})
	strs := findPkg(pkgs, "strings")
	if strs == nil {
		t.Fatal("strings package missing in FULL mode")
	}
	if !strs.IsStdlib {
		t.Fatalf("strings not stdlib: %+v", strs)
	}
	if wb, _ := bodyIDsOf(strs, bodies); wb == 0 {
		t.Fatal("FULL mode streamed no stdlib bodies")
	}
}
