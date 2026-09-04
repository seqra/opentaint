import sys
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

    def ExecuteFunction(self, request, context):
        return execute_function(request)

    def Ping(self, request, context):
        import mypy.version

        return pir_pb2.PingResponse(
            version="0.2.0",
            python_version=f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
            mypy_version=mypy.version.__version__,
        )
