import os
import sys
import grpc
from pir_server.proto import pir_pb2, pir_pb2_grpc
from pir_server.builder.project_builder import ProjectBuilder
from pir_server.executor import execute_function


class PIRServiceServicer(pir_pb2_grpc.PIRServiceServicer):
    def BuildProject(self, request, context):
        builder = ProjectBuilder(
            sources=list(request.sources),
            mypy_flags=list(request.mypy_flags),
            python_version=request.python_version or None,
            package_roots=list(request.package_roots),
        )
        for module_proto in builder.build():
            yield module_proto

    # Keep BuildProjectAst as alias for backward compatibility
    def BuildProjectAst(self, request, context):
        return self.BuildProject(request, context)

    def BuildModule(self, request, context):
        try:
            builder = ProjectBuilder(
                sources=[request.source_path],
                mypy_flags=list(request.mypy_flags),
                python_version=request.python_version or None,
                package_roots=list(request.package_roots),
            )
            for module_proto in builder.build():
                if module_proto.name == request.module_name:
                    return module_proto
            context.set_code(grpc.StatusCode.NOT_FOUND)
            context.set_details(f"Module '{request.module_name}' not found")
            return pir_pb2.MypyModuleProto()
        except Exception as e:
            context.set_code(grpc.StatusCode.INTERNAL)
            context.set_details(str(e))
            return pir_pb2.MypyModuleProto()

    def ExecuteFunction(self, request, context):
        return execute_function(request)

    def Ping(self, request, context):
        import mypy.version

        return pir_pb2.PingResponse(
            version="0.2.0",
            python_version=f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
            mypy_version=mypy.version.__version__,
        )

    def Shutdown(self, request, context):
        import threading

        threading.Timer(0.1, lambda: os._exit(0)).start()
        return pir_pb2.ShutdownResponse()
