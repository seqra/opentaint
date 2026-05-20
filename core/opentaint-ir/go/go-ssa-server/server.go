package server

import (
	"context"
	"sync/atomic"
	"time"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

type goSSAServer struct {
	pb.UnimplementedGoSSAServiceServer
	version      string
	goVersion    string
	sessions     *sessionManager
	lastActivity atomic.Int64 // UnixNano of last RPC handler call
}

func NewGoSSAServer(version, goVersion string) *goSSAServer {
	s := &goSSAServer{version: version, goVersion: goVersion, sessions: newSessionManager()}
	s.lastActivity.Store(time.Now().UnixNano())
	return s
}

func (s *goSSAServer) touchActivity() {
	s.lastActivity.Store(time.Now().UnixNano())
}

// StartIdleWatchdog runs a goroutine that periodically checks whether the
// server has been idle (no RPC activity and no live sessions) for longer than
// `timeout`. If so, it invokes `shutdown`. A timeout of 0 disables the
// watchdog. The watchdog stops when `stop` is closed.
func (s *goSSAServer) StartIdleWatchdog(timeout time.Duration, shutdown func(), stop <-chan struct{}) {
	if timeout <= 0 {
		return
	}
	go func() {
		ticker := time.NewTicker(timeout / 4)
		if timeout/4 < time.Second {
			ticker.Stop()
			ticker = time.NewTicker(time.Second)
		}
		defer ticker.Stop()
		for {
			select {
			case <-stop:
				return
			case now := <-ticker.C:
				if s.sessionCount() > 0 {
					continue
				}
				last := time.Unix(0, s.lastActivity.Load())
				if now.Sub(last) > timeout {
					shutdown()
					return
				}
			}
		}
	}()
}

func (s *goSSAServer) sessionCount() int {
	s.sessions.mu.Lock()
	defer s.sessions.mu.Unlock()
	return len(s.sessions.sessions)
}

func (s *goSSAServer) Ping(ctx context.Context, req *pb.PingRequest) (*pb.PingResponse, error) {
	s.touchActivity()
	return &pb.PingResponse{
		Version:   s.version,
		GoVersion: s.goVersion,
	}, nil
}

func (s *goSSAServer) OpenSession(ctx context.Context, req *pb.OpenSessionRequest) (*pb.OpenSessionResponse, error) {
	s.touchActivity()
	startTime := time.Now()
	sess, err := s.sessions.create(req)
	if err != nil {
		return &pb.OpenSessionResponse{Error: &pb.ProtoError{Message: err.Error(), Fatal: true}}, nil
	}
	return &pb.OpenSessionResponse{
		SessionId: sess.id,
		Packages:  sess.protoPackageSummaries(),
		Summary: &pb.ProtoBuildSummary{
			PackageCount: int32(len(sess.packageSummaries)),
			BuildTimeMs:  time.Since(startTime).Milliseconds(),
		},
	}, nil
}

func (s *goSSAServer) LoadPackage(req *pb.LoadPackageRequest, stream pb.GoSSAService_LoadPackageServer) error {
	s.touchActivity()
	startTime := time.Now()
	s.sessions.touch(req.SessionId)
	sess, ok := s.sessions.get(req.SessionId)
	if !ok {
		return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_Error{Error: &pb.ProtoError{Message: "unknown session", Fatal: true}}})
	}
	ser, _, _, err := sess.loadPackage(req.PackageId)
	if err != nil {
		return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_Error{Error: &pb.ProtoError{Message: err.Error(), Fatal: true}}})
	}
	sendType := func(td *pb.ProtoTypeDefinition) error {
		return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_TypeDef{TypeDef: td}})
	}
	sendPkg := func(pp *pb.ProtoPackage) error {
		return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_PackageDef{PackageDef: pp}})
	}
	if err := streamCollectedTypesAndMark(ser, sendType); err != nil {
		return err
	}
	if ser.placeholderPackage != nil {
		if err := sendPkg(ser.serializePlaceholderPackage()); err != nil {
			return err
		}
		return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_Summary{Summary: &pb.ProtoBuildSummary{
			PackageCount: 1,
			BuildTimeMs:  time.Since(startTime).Milliseconds(),
		}}})
	}
	// Serialize user packages first so their ImportIds get assigned and
	// importedExternalSSA is populated. Then emit minimal stubs for those
	// imports so clients can resolve ImportIds without separate LoadPackage
	// round-trips.
	userPkgDefs := make([]*pb.ProtoPackage, 0, len(ser.pkgs))
	for _, pkg := range ser.pkgs {
		userPkgDefs = append(userPkgDefs, ser.serializePackage(pkg))
	}
	for _, stub := range ser.importStubPackages() {
		if err := sendPkg(stub); err != nil {
			return err
		}
		ser.stats.packageCount++
	}
	for _, def := range userPkgDefs {
		if err := sendPkg(def); err != nil {
			return err
		}
		ser.stats.packageCount++
	}
	markStreamedAfterSend(ser)
	return stream.Send(&pb.LoadPackageResponse{Payload: &pb.LoadPackageResponse_Summary{Summary: &pb.ProtoBuildSummary{
		PackageCount:  int32(ser.stats.packageCount),
		FunctionCount: int32(ser.stats.functionCount),
		TypeCount:     int32(ser.stats.typeCount),
		BuildTimeMs:   time.Since(startTime).Milliseconds(),
	}}})
}

func (s *goSSAServer) LoadFunctionBody(req *pb.LoadFunctionBodyRequest, stream pb.GoSSAService_LoadFunctionBodyServer) error {
	s.touchActivity()
	startTime := time.Now()
	s.sessions.touch(req.SessionId)
	sess, ok := s.sessions.get(req.SessionId)
	if !ok {
		return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_Error{Error: &pb.ProtoError{Message: "unknown session", Fatal: true}}})
	}
	ser, fn, _, err := sess.loadFunctionBody(req.FunctionId)
	if err != nil {
		return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_Error{Error: &pb.ProtoError{Message: err.Error(), Fatal: true}}})
	}
	sendType := func(td *pb.ProtoTypeDefinition) error {
		return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_TypeDef{TypeDef: td}})
	}
	sendPkg := func(pp *pb.ProtoPackage) error {
		return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_PackageDef{PackageDef: pp}})
	}
	if err := streamCollectedTypesAndMark(ser, sendType); err != nil {
		return err
	}
	for _, pkg := range ser.externalPackageStubs() {
		if err := sendPkg(pkg); err != nil {
			return err
		}
		ser.stats.packageCount++
	}
	if err := stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_FunctionDef{FunctionDef: ser.serializeFunction(fn)}}); err != nil {
		return err
	}
	ser.ids.markFunctionStreamed(fn)
	markStreamedAfterSend(ser)
	body, err := ser.serializeFunctionBody(fn)
	if err != nil {
		return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_Error{Error: &pb.ProtoError{Message: err.Error(), FunctionName: fn.String(), Fatal: true}}})
	}
	if err := stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_FunctionBody{FunctionBody: body}}); err != nil {
		return err
	}
	return stream.Send(&pb.LoadFunctionBodyResponse{Payload: &pb.LoadFunctionBodyResponse_Summary{Summary: &pb.ProtoBuildSummary{
		FunctionCount:    1,
		TypeCount:        int32(ser.stats.typeCount),
		InstructionCount: int32(ser.stats.instructionCount),
		BuildTimeMs:      time.Since(startTime).Milliseconds(),
	}}})
}

func (s *goSSAServer) CloseSession(ctx context.Context, req *pb.CloseSessionRequest) (*pb.CloseSessionResponse, error) {
	s.touchActivity()
	s.sessions.touch(req.SessionId)
	return &pb.CloseSessionResponse{Closed: s.sessions.close(req.SessionId)}, nil
}

// streamCollectedTypesAndMark sends every collected type definition through
// the supplied callback, updates the serializer's per-session streamed-types
// set, and bumps the type counter. Shared by LoadPackage and LoadFunctionBody
// handlers — both emit the same set of type defs at the start of their
// response stream.
func streamCollectedTypesAndMark(ser *serializer, send func(*pb.ProtoTypeDefinition) error) error {
	for _, t := range ser.allTypes {
		td := ser.serializeType(t)
		if td == nil {
			continue
		}
		if err := send(td); err != nil {
			return err
		}
		ser.ids.markTypeStreamed(t)
		ser.stats.typeCount++
	}
	return nil
}

// markStreamedAfterSend marks every function and global serialized in this
// call as streamed so subsequent loads do not re-emit them.
func markStreamedAfterSend(ser *serializer) {
	for fn := range ser.serializedFunctions {
		ser.ids.markFunctionStreamed(fn)
	}
	for _, g := range ser.allGlobals {
		ser.ids.markGlobalStreamed(g)
	}
}
