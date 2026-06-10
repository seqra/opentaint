package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"os"
	"os/signal"
	"runtime"
	"runtime/debug"
	"syscall"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	server "github.com/opentaint/go-ir/go-ssa-server"
	pb "github.com/opentaint/go-ir/go-ssa-server/proto/goir"
)

const version = "0.1.0"

// configureLogging routes diagnostics to stderr with timestamps so that crash
// logs captured by the Kotlin client can be correlated in time, and forces the
// runtime to print *all* goroutine stacks on a panic / fatal error. Without the
// latter, an OOM or panic in one worker prints only its own stack, which is
// rarely enough to explain the failure after the fact on CI.
func configureLogging() {
	log.SetOutput(os.Stderr)
	log.SetPrefix("[go-ssa-server] ")
	log.SetFlags(log.LstdFlags | log.Lmicroseconds | log.LUTC)
	// Equivalent to GOTRACEBACK=all: dump every goroutine on crash.
	debug.SetTraceback("all")
}

// logStartupInfo records the environment of the process. When a build later
// dies with "Network closed for unknown reason", these values (pid, CPU count,
// memory limit) are the first things needed to tell an OOM-kill apart from a
// logic panic.
func logStartupInfo(port int) {
	limit := debug.SetMemoryLimit(-1) // read-only query of the current soft limit
	log.Printf(
		"starting version=%s go=%s pid=%d port=%d GOMAXPROCS=%d NumCPU=%d GOMEMLIMIT=%d",
		version, runtime.Version(), os.Getpid(), port,
		runtime.GOMAXPROCS(0), runtime.NumCPU(), limit,
	)
}

// logMemStats prints a one-line snapshot of heap usage. Tagged with `reason`
// so periodic samples and the final pre-shutdown sample are distinguishable.
func logMemStats(reason string) {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	const mib = 1024 * 1024
	log.Printf(
		"memstats(%s): heapAlloc=%dMiB heapSys=%dMiB heapInuse=%dMiB stackInuse=%dMiB sys=%dMiB numGC=%d goroutines=%d",
		reason, m.HeapAlloc/mib, m.HeapSys/mib, m.HeapInuse/mib, m.StackInuse/mib,
		m.Sys/mib, m.NumGC, runtime.NumGoroutine(),
	)
}

// startMemStatsLogger periodically samples memory so a gradual climb towards an
// OOM-kill is visible in the captured stderr right up to the moment the kernel
// terminates the process. A zero or negative interval disables it.
func startMemStatsLogger(interval time.Duration, stop <-chan struct{}) {
	if interval <= 0 {
		return
	}
	go func() {
		ticker := time.NewTicker(interval)
		defer ticker.Stop()
		for {
			select {
			case <-stop:
				return
			case <-ticker.C:
				logMemStats("periodic")
			}
		}
	}()
}

// installSignalHandler logs and gracefully shuts down on the termination
// signals we *can* observe. An OOM-kill (SIGKILL) cannot be caught, so the
// absence of any signal log next to a sudden death is itself a strong signal
// that the kernel OOM-killer was responsible. SIGQUIT is intentionally left to
// the Go runtime, whose default handler dumps all goroutine stacks.
func installSignalHandler(shutdown func()) {
	ch := make(chan os.Signal, 1)
	signal.Notify(ch, syscall.SIGINT, syscall.SIGTERM, syscall.SIGHUP)
	go func() {
		sig := <-ch
		log.Printf("received signal %v, shutting down", sig)
		logMemStats("signal")
		shutdown()
	}()
}

// recoveryUnaryInterceptor converts a panic in a unary handler into an
// Internal error instead of letting it crash the whole server process.
func recoveryUnaryInterceptor(
	ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler,
) (resp interface{}, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = recoverToStatus(info.FullMethod, r)
		}
	}()
	return handler(ctx, req)
}

// recoveryStreamInterceptor does the same for streaming handlers. BuildProgram
// is a server-streaming RPC, and a panic deep inside the SSA builder or
// serializer would otherwise tear down the process mid-stream — which is
// exactly what the client observes as "UNAVAILABLE: Network closed for unknown
// reason". Recovering here turns that into an actionable gRPC error carrying
// the panic value, while the full stack is written to stderr.
func recoveryStreamInterceptor(
	srv interface{}, ss grpc.ServerStream, info *grpc.StreamServerInfo, handler grpc.StreamHandler,
) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = recoverToStatus(info.FullMethod, r)
		}
	}()
	return handler(srv, ss)
}

// recoverToStatus logs the panic with a full stack trace and maps it to a
// gRPC Internal status so the client receives a descriptive error.
func recoverToStatus(method string, r interface{}) error {
	stack := debug.Stack()
	log.Printf("PANIC in %s: %v\n%s", method, r, stack)
	return status.Errorf(codes.Internal, "server panic in %s: %v", method, r)
}

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
	memLogInterval := flag.Duration("mem-log-interval", 30*time.Second, "interval for periodic memory-usage logging to stderr (0 disables)")
	flag.Parse()

	configureLogging()

	lis, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", *port))
	if err != nil {
		log.Printf("ERROR: listen failed: %v", err)
		fmt.Fprintf(os.Stderr, "ERROR:%v\n", err)
		os.Exit(1)
	}

	actualPort := lis.Addr().(*net.TCPAddr).Port
	logStartupInfo(actualPort)
	// Print the port so the Kotlin client can read it
	fmt.Printf("LISTENING:%d\n", actualPort)

	srv := grpc.NewServer(
		grpc.ChainUnaryInterceptor(recoveryUnaryInterceptor),
		grpc.ChainStreamInterceptor(recoveryStreamInterceptor),
	)
	goSSA := server.NewGoSSAServer(version, runtime.Version())
	pb.RegisterGoSSAServiceServer(srv, goSSA)

	shutdown := makeGrpcShutdown(srv, 3*time.Second)

	// Mechanism A: stdin-EOF watcher. The Kotlin parent keeps the stdin pipe
	// open for the lifetime of the child; when the JVM dies (for any reason)
	// the OS closes the write end and we observe EOF here.
	go watchStdinAndExit(os.Stdin, shutdown)

	// Mechanism B: OS signal handler (logs the signal before shutting down).
	installSignalHandler(shutdown)

	// Mechanism C: idle timeout watchdog (defense in depth).
	idleStop := make(chan struct{})
	goSSA.StartIdleWatchdog(*idleTimeout, shutdown, idleStop)

	// Periodic memory diagnostics so an approaching OOM is visible on stderr.
	startMemStatsLogger(*memLogInterval, idleStop)

	if err := srv.Serve(lis); err != nil {
		log.Printf("ERROR: serve failed: %v", err)
		fmt.Fprintf(os.Stderr, "ERROR:%v\n", err)
		os.Exit(1)
	}
	logMemStats("shutdown")
	close(idleStop)
}
