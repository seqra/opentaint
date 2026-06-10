package server

import (
	"context"
	"fmt"
	"sync/atomic"
	"time"

	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

type goSSAServer struct {
	pb.UnimplementedGoSSAServiceServer
	version      string
	goVersion    string
	lastActivity atomic.Int64
	inFlight     atomic.Int64
}

func NewGoSSAServer(version, goVersion string) *goSSAServer {
	s := &goSSAServer{version: version, goVersion: goVersion}
	s.lastActivity.Store(time.Now().UnixNano())
	return s
}

func (s *goSSAServer) touchActivity() {
	s.lastActivity.Store(time.Now().UnixNano())
}

func (s *goSSAServer) StartIdleWatchdog(timeout time.Duration, shutdown func(), stop <-chan struct{}) {
	if timeout <= 0 {
		return
	}
	go func() {
		interval := timeout / 4
		if interval < time.Second {
			interval = time.Second
		}
		ticker := time.NewTicker(interval)
		defer ticker.Stop()
		for {
			select {
			case <-stop:
				return
			case now := <-ticker.C:
				if s.inFlight.Load() > 0 {
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

func (s *goSSAServer) Ping(ctx context.Context, req *pb.PingRequest) (*pb.PingResponse, error) {
	s.touchActivity()
	return &pb.PingResponse{Version: s.version, GoVersion: s.goVersion}, nil
}

func (s *goSSAServer) BuildProgram(req *pb.BuildProgramRequest, stream pb.GoSSAService_BuildProgramServer) error {
	s.touchActivity()
	s.inFlight.Add(1)
	defer func() {
		s.inFlight.Add(-1)
		s.touchActivity()
	}()
	startTime := time.Now()

	prog, pkgs, info, err := buildSSA(req)
	if err != nil {
		return stream.Send(&pb.BuildProgramResponse{
			Payload: &pb.BuildProgramResponse_Error{Error: &pb.ProtoError{Message: err.Error(), Fatal: true}},
		})
	}

	projectModulePaths := make(map[string]bool, len(req.ProjectModulePaths))
	for _, m := range req.ProjectModulePaths {
		projectModulePaths[m] = true
	}

	ser := newSerializerForBuild(prog, pkgs, info, req.Mode, projectModulePaths)

	program, serErrs := ser.serializeProgram()
	for _, e := range serErrs {
		if err := stream.Send(&pb.BuildProgramResponse{Payload: &pb.BuildProgramResponse_Error{Error: e}}); err != nil {
			return err
		}
	}

	if err := stream.Send(&pb.BuildProgramResponse{Payload: &pb.BuildProgramResponse_Program{Program: program}}); err != nil {
		return fmt.Errorf("streaming program: %w", err)
	}

	return stream.Send(&pb.BuildProgramResponse{
		Payload: &pb.BuildProgramResponse_Summary{Summary: &pb.ProtoBuildSummary{
			PackageCount:     int32(ser.stats.packageCount),
			FunctionCount:    int32(ser.stats.functionCount),
			TypeCount:        int32(ser.stats.typeCount),
			InstructionCount: int32(ser.stats.instructionCount),
			BuildTimeMs:      time.Since(startTime).Milliseconds(),
		}},
	})
}
