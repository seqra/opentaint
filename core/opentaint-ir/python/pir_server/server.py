import os
import signal
import sys
import threading
import grpc
import mypy.defaults
from concurrent import futures
from pir_server.service import PIRServiceServicer
from pir_server.proto import pir_pb2_grpc

WORKER_STACK_SIZE = 16 * 1024 * 1024
STOP_GRACE_SECONDS = 1
STOP_TIMEOUT_SECONDS = 1

_shutdown_lock = threading.Lock()


def _shutdown(server):
    # One-shot latch, never released: stdin EOF and SIGTERM both land here.
    if not _shutdown_lock.acquire(blocking=False):
        return
    server.stop(STOP_GRACE_SECONDS).wait(STOP_TIMEOUT_SECONDS)
    os._exit(0)


def _parent_watchdog(server):
    try:
        # Block until stdin returns EOF (parent died / pipe closed)
        while True:
            data = sys.stdin.buffer.read(1)
            if not data:
                break
    except Exception:
        pass

    _shutdown(server)


def serve(port: int = 0):
    threading.stack_size(WORKER_STACK_SIZE)
    sys.setrecursionlimit(mypy.defaults.RECURSION_LIMIT)

    server = grpc.server(
        futures.ThreadPoolExecutor(max_workers=1),
        maximum_concurrent_rpcs=1,
        options=[
            ("grpc.max_send_message_length", 256 * 1024 * 1024),
            ("grpc.max_receive_message_length", 256 * 1024 * 1024),
        ],
    )
    pir_pb2_grpc.add_PIRServiceServicer_to_server(PIRServiceServicer(), server)
    actual_port = server.add_insecure_port(f"127.0.0.1:{port}")
    if actual_port == 0:
        raise RuntimeError(f"failed to bind 127.0.0.1:{port}")
    server.start()

    signal.signal(signal.SIGTERM, lambda *_: _shutdown(server))

    watchdog = threading.Thread(target=_parent_watchdog, args=(server,), daemon=True)
    watchdog.start()

    sys.stdout.write(f"READY:{actual_port}\n")
    sys.stdout.flush()

    server.wait_for_termination()
