from __future__ import annotations
from typing import Iterator
import contextlib
import io
import os
import sys
import time
import mypy.build
import mypy.defaults
import mypy.main
import mypy.options
from mypy.errors import CompileError
from mypy.find_sources import InvalidSourceList, SourceFinder
from mypy.fscache import FileSystemCache
from mypy.nodes import MypyFile
from pir_server.proto import pir_pb2
from pir_server.builder.ast_serializer import AstSerializer


class InvalidMypyFlags(ValueError):
    pass


class InvalidPackageRoot(ValueError):
    pass


class InvalidPythonVersion(ValueError):
    pass


def parse_python_version(value):
    parts = value.split(".")
    if len(parts) < 2 or not all(p.isdigit() for p in parts[:2]):
        raise InvalidPythonVersion(
            f"Malformed python_version {value!r}; expected 'MAJOR.MINOR'"
        )
    version = (int(parts[0]), int(parts[1]))
    minimum = mypy.defaults.PYTHON3_VERSION_MIN
    if version < minimum:
        raise InvalidPythonVersion(
            f"python_version {value} is below mypy's minimum supported target "
            f"{minimum[0]}.{minimum[1]}"
        )
    host = sys.version_info[:2]
    if version > host:
        raise InvalidPythonVersion(
            f"python_version {value} exceeds the PIR server interpreter "
            f"{host[0]}.{host[1]}; mypy parses with the host ast"
        )
    return version


class ProjectBuilder:
    def __init__(
        self,
        sources: list[str],
        package_roots: list[str],
        mypy_flags: list[str] | None = None,
        python_version: str | None = None,
    ):
        self.sources = sources
        self.package_roots = list(package_roots)
        self.mypy_flags = mypy_flags or []
        self.python_version = python_version

    def _build_options(self) -> mypy.options.Options:
        if self.mypy_flags:
            captured = io.StringIO()
            try:
                with contextlib.redirect_stdout(captured):
                    _, options = mypy.main.process_options(
                        list(self.mypy_flags),
                        stdout=captured,
                        stderr=captured,
                        require_targets=False,
                    )
            except SystemExit as e:
                message = captured.getvalue().strip() or str(e)
                raise InvalidMypyFlags(message[:2000]) from e
        else:
            options = mypy.options.Options()

        if self.python_version:
            options.python_version = parse_python_version(self.python_version)
        options.explicit_package_bases = True
        options.mypy_path = list(self.package_roots)

        options.incremental = False
        options.preserve_asts = True
        options.export_types = True
        options.python_executable = None
        options.semantic_analysis_only = True
        return options

    def build(self) -> Iterator[pir_pb2.MypyModuleProto]:
        try:
            options = self._build_options()
        except InvalidMypyFlags as e:
            yield pir_pb2.MypyModuleProto(
                name="__build_errors__",
                errors=[f"Invalid mypy flags {self.mypy_flags}: {e}"],
            )
            return
        except InvalidPythonVersion as e:
            yield pir_pb2.MypyModuleProto(
                name="__build_errors__",
                errors=[str(e)],
            )
            return

        try:
            self._validate_package_roots()
        except InvalidPackageRoot as e:
            yield pir_pb2.MypyModuleProto(
                name="__build_errors__",
                errors=[str(e)],
            )
            return

        mypy_sources = []
        all_file_paths = []

        for s in self.sources:
            if os.path.isfile(s):
                all_file_paths.append(os.path.abspath(s))
            elif os.path.isdir(s):
                for root, dirs, files in os.walk(s):
                    for f in files:
                        if f.endswith(".py"):
                            all_file_paths.append(
                                os.path.abspath(os.path.join(root, f))
                            )

        fscache = FileSystemCache()
        finder = SourceFinder(fscache, options)

        seen_modules: dict[str, str] = {}
        for path in all_file_paths:
            try:
                mod_name, base_dir = finder.crawl_up(path)
            except InvalidSourceList as e:
                print(f"WARNING: Skipping {path}: {e}", file=sys.stderr)
                continue
            if mod_name in seen_modules:
                print(
                    f"WARNING: Duplicate module '{mod_name}': "
                    f"{path} (already: {seen_modules[mod_name]}), skipping",
                    file=sys.stderr,
                )
                continue
            seen_modules[mod_name] = path
            mypy_sources.append(
                mypy.build.BuildSource(path=path, module=mod_name, base_dir=base_dir)
            )

        if not mypy_sources:
            return

        print(f"PIR: Building {len(mypy_sources)} sources...", file=sys.stderr)

        try:
            result = mypy.build.build(
                sources=mypy_sources,
                options=options,
                fscache=fscache,
            )
        except CompileError as e:
            yield from self._errors_to_unknown_modules(e.messages, seen_modules)
            return
        except Exception as e:
            yield from self._exception_to_unknown_modules(e, seen_modules)
            return

        if result.errors:
            print(
                f"PIR: mypy reported {len(result.errors)} errors (non-fatal)",
                file=sys.stderr,
            )

        source_paths = set()
        for s in self.sources:
            source_paths.add(os.path.abspath(s))

        emitted = 0
        last_log = time.monotonic()
        total = sum(
            1
            for _, st in result.graph.items()
            if st.tree and self._should_include(st, source_paths)
        )

        for module_name, state in result.graph.items():
            tree: MypyFile | None = state.tree
            if tree is None:
                continue
            if not self._should_include(state, source_paths):
                continue

            now = time.monotonic()
            if now - last_log >= 10.0:
                print(
                    f"PIR: Serializing module {emitted}/{total}: {module_name}",
                    file=sys.stderr,
                )
                last_log = now

            try:
                serializer = AstSerializer(
                    tree=tree,
                    types=result.types,
                    module_name=module_name,
                )
                yield serializer.serialize()
            except Exception as e:
                print(
                    f"WARNING: Failed to serialize module {module_name}: "
                    f"{type(e).__name__}: {e}",
                    file=sys.stderr,
                )
                yield pir_pb2.MypyModuleProto(
                    name=module_name,
                    path=getattr(tree, "path", ""),
                    errors=[f"{type(e).__name__}: {e}"],
                )

            emitted += 1

        print(f"PIR: Done. Emitted {emitted} modules.", file=sys.stderr)

    def _errors_to_unknown_modules(
        self, messages: list[str], seen_modules: dict[str, str]
    ) -> Iterator[pir_pb2.MypyModuleProto]:
        path_to_module = sorted(
            ((v, k) for k, v in seen_modules.items()),
            key=lambda x: -len(x[0]),
        )

        module_errors: dict[str, list[str]] = {}
        unmapped: list[str] = []

        for msg in messages:
            mapped = False
            for path, mod in path_to_module:
                if path in msg:
                    module_errors.setdefault(mod, []).append(msg)
                    mapped = True
                    break
            if not mapped:
                for path, mod in path_to_module:
                    rel = os.path.relpath(path)
                    if rel in msg:
                        module_errors.setdefault(mod, []).append(msg)
                        mapped = True
                        break
            if not mapped:
                unmapped.append(msg)

        for mod_name, errors in module_errors.items():
            path = seen_modules.get(mod_name, "")
            yield pir_pb2.MypyModuleProto(
                name=mod_name,
                path=path,
                errors=errors,
            )

        if unmapped:
            yield pir_pb2.MypyModuleProto(
                name="__build_errors__",
                errors=unmapped,
            )

    def _exception_to_unknown_modules(
        self, exc: Exception, seen_modules: dict[str, str]
    ) -> Iterator[pir_pb2.MypyModuleProto]:
        import traceback as tb

        error_msg = f"{type(exc).__name__}: {exc}"
        print(f"mypy build failed: {error_msg}", file=sys.stderr)
        tb.print_exc()

        exc_str = str(exc)
        tb_str = "".join(tb.format_exception(type(exc), exc, exc.__traceback__))

        best_match: str | None = None
        for mod_name in seen_modules:
            if mod_name in exc_str:
                if best_match is None or len(mod_name) > len(best_match):
                    best_match = mod_name
        if best_match:
            yield pir_pb2.MypyModuleProto(
                name=best_match,
                path=seen_modules[best_match],
                errors=[error_msg],
            )
            return

        for path, mod_name in sorted(
            ((v, k) for k, v in seen_modules.items()), key=lambda x: -len(x[0])
        ):
            if path in tb_str or os.path.relpath(path) in tb_str:
                yield pir_pb2.MypyModuleProto(
                    name=mod_name,
                    path=path,
                    errors=[error_msg],
                )
                return

        yield pir_pb2.MypyModuleProto(
            name="__build_errors__",
            errors=[error_msg],
        )

    def _validate_package_roots(self) -> None:
        if not self.package_roots:
            raise InvalidPackageRoot("package_roots must not be empty")

        probe = mypy.options.Options()
        probe.explicit_package_bases = False
        finder = SourceFinder(FileSystemCache(), probe)

        for root in self.package_roots:
            abs_root = os.path.abspath(root)
            if not os.path.isdir(abs_root):
                raise InvalidPackageRoot(f"package root is not a directory: {root}")
            package, base = finder.crawl_up_dir(abs_root)
            if package:
                raise InvalidPackageRoot(
                    f"package root {abs_root} is inside package '{package}'; "
                    f"pass {base} instead"
                )

    def _should_include(self, state, source_paths: set[str]) -> bool:
        if state.path is None:
            return False
        abs_path = os.path.abspath(state.path)
        for src in source_paths:
            if abs_path.startswith(src) or abs_path == src:
                return True
        return False
