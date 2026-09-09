import sys
import grpc
import mypy.version
from pir_server.proto import pir_pb2, pir_pb2_grpc
from pir_server.builder.project_builder import (
    InvalidMypyFlags,
    InvalidPackageRoot,
    InvalidPythonVersion,
    ProjectBuilder,
)
from pir_server.executor import InvalidExecuteRequest, execute_function


class PIRServiceServicer(pir_pb2_grpc.PIRServiceServicer):
    def BuildProject(self, request, context):
        builder = ProjectBuilder(
            sources=list(request.sources),
            mypy_flags=list(request.mypy_flags),
            python_version=request.python_version or None,
            package_roots=list(request.package_roots),
        )
        try:
            yield from builder.build()
        except (InvalidMypyFlags, InvalidPythonVersion, InvalidPackageRoot) as e:
            context.abort(grpc.StatusCode.INVALID_ARGUMENT, str(e))
            return

    def ExecuteFunction(self, request, context):
        try:
            return execute_function(request)
        except InvalidExecuteRequest as e:
            context.abort(grpc.StatusCode.INVALID_ARGUMENT, str(e))
            return None

    def Ping(self, request, context):
        return pir_pb2.PingResponse(
            python_version=f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
            mypy_version=mypy.version.__version__,
        )
