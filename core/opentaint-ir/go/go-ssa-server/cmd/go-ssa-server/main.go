package main

import (
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"os"
	"runtime"
	"time"

	"google.golang.org/grpc"

	server "github.com/opentaint/go-ir/go-ssa-server"
	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

const version = "0.1.0"

// watchStdinAndExit reads from the provided reader until EOF or any other
// read error. When that happens the process is presumed to have lost its
// parent (the JVM that spawned us), so `shutdown` is invoked.
func watchStdinAndExit(r io.Reader, shutdown func()) {
	_, err := io.Copy(io.Discard, r)
	if err == nil || err == io.EOF || err == io.ErrUnexpectedEOF {
		log.Printf("stdin closed, shutting down")
	} else {
		log.Printf("stdin read error (%v), shutting down", err)
	}
	shutdown()
}

// makeGrpcShutdown returns a shutdown function that calls GracefulStop in a
// goroutine and falls back to os.Exit after `hardTimeout` so a wedged
// streaming RPC cannot keep the process alive forever.
func makeGrpcShutdown(srv *grpc.Server, hardTimeout time.Duration) func() {
	return func() {
		go srv.GracefulStop()
		time.AfterFunc(hardTimeout, func() { os.Exit(0) })
	}
}

func main() {
	port := flag.Int("port", 0, "port to listen on (0 = random)")
	idleTimeout := flag.Duration("idle-timeout", 15*time.Minute, "shut the server down after this much idle time with no sessions (0 disables)")
	flag.Parse()

	lis, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", *port))
	if err != nil {
		fmt.Fprintf(os.Stderr, "ERROR:%v\n", err)
		os.Exit(1)
	}

	actualPort := lis.Addr().(*net.TCPAddr).Port
	// Print the port so the Kotlin client can read it
	fmt.Printf("LISTENING:%d\n", actualPort)

	srv := grpc.NewServer()
	goSSA := server.NewGoSSAServer(version, runtime.Version())
	pb.RegisterGoSSAServiceServer(srv, goSSA)

	shutdown := makeGrpcShutdown(srv, 3*time.Second)

	// Mechanism A: stdin-EOF watcher. The Kotlin parent keeps the stdin pipe
	// open for the lifetime of the child; when the JVM dies (for any reason)
	// the OS closes the write end and we observe EOF here.
	go watchStdinAndExit(os.Stdin, shutdown)

	// Mechanism C: idle timeout watchdog (defense in depth).
	idleStop := make(chan struct{})
	goSSA.StartIdleWatchdog(*idleTimeout, shutdown, idleStop)

	if err := srv.Serve(lis); err != nil {
		fmt.Fprintf(os.Stderr, "ERROR:%v\n", err)
		os.Exit(1)
	}
	close(idleStop)
}
