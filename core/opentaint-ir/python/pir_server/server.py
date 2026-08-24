import os
import sys
import threading
import grpc
from concurrent import futures
from pir_server.service import PIRServiceServicer
from pir_server.proto import pir_pb2_grpc


def _parent_watchdog(server):
    try:
        # Block until stdin returns EOF (parent died / pipe closed)
        while True:
            data = sys.stdin.buffer.read(1)
            if not data:
                break
    except Exception:
        pass

    server.stop(grace=2)
    os._exit(0)


def serve(port: int = 0):
    server = grpc.server(
        futures.ThreadPoolExecutor(max_workers=4),
        options=[
            ("grpc.max_send_message_length", 256 * 1024 * 1024),
            ("grpc.max_receive_message_length", 256 * 1024 * 1024),
        ],
    )
    pir_pb2_grpc.add_PIRServiceServicer_to_server(PIRServiceServicer(), server)
    actual_port = server.add_insecure_port(f"127.0.0.1:{port}")
    server.start()

    watchdog = threading.Thread(target=_parent_watchdog, args=(server,), daemon=True)
    watchdog.start()

    sys.stdout.write(f"READY:{actual_port}\n")
    sys.stdout.flush()

    server.wait_for_termination()
