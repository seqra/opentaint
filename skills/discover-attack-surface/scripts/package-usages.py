#!/usr/bin/env python3
"""List package methods used by compiled project classes via javap."""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from bisect import bisect_right
from pathlib import Path


CLASSFILE_RE = re.compile(r"^Classfile (.+)$")
SOURCE_RE = re.compile(r'^(?:SourceFile:\s+|Compiled from\s+)"(.+)"$')
CALL_RE = re.compile(
    r"^\s*(\d+):\s+invoke\w+\s+#\d+(?:,\s+\d+)?\s+//\s+"
    r"(?:Method|InterfaceMethod)\s+(.+)$"
)
DYNAMIC_RE = re.compile(
    r"^\s*(\d+):\s+invokedynamic\s+#\d+(?:,\s+\d+)?\s+//\s+InvokeDynamic\s+#(\d+):"
)
LINE_RE = re.compile(r"^line\s+(\d+):\s+(\d+)$")
BOOTSTRAP_INDEX_RE = re.compile(r"^\s*(\d+):")
REF_INVOKE_RE = re.compile(r"REF_invoke\w+\s+([^:]+):(\S+)")


def q(value):
    if value is None:
        return "null"
    if isinstance(value, int):
        return str(value)
    return json.dumps(str(value), ensure_ascii=False)


def source_root(model_dir):
    project_yaml = model_dir / "project.yaml"
    if project_yaml.exists():
        for line in project_yaml.read_text().splitlines():
            if line.strip().startswith("sourceRoot:"):
                return model_dir / line.split(":", 1)[1].strip()
    return model_dir / "sources"


def source_index(root):
    index = {}
    markers = (
        ("src", "main", "java"), ("src", "test", "java"),
        ("src", "main", "kotlin"), ("src", "test", "kotlin"),
        ("src", "main", "groovy"), ("src", "test", "groovy"),
    )
    if not root.exists():
        return index
    for pattern in ("*.java", "*.kt", "*.groovy"):
        for path in root.rglob(pattern):
            rel = str(path.resolve().relative_to(root.resolve()))
            index.setdefault(rel, rel)
            parts = Path(rel).parts
            for marker in markers:
                for i in range(0, len(parts) - len(marker)):
                    if parts[i:i + len(marker)] == marker:
                        index.setdefault(str(Path(*parts[i + len(marker):])), rel)
                        break
    return index


def class_roots(model_dir):
    classes_dir = model_dir / "classes"
    return sorted(path.resolve() for path in classes_dir.iterdir() if path.is_dir())


def class_from_path(path, roots):
    path = Path(path).resolve()
    for root in roots:
        try:
            return str(path.relative_to(root).with_suffix("")).replace(os.sep, ".")
        except ValueError:
            pass
    return None


def source_for(index, cls, source_file):
    if not cls or not source_file:
        return None
    package = cls.rsplit(".", 1)[0] if "." in cls else ""
    key = str(Path(*package.split(".")) / source_file) if package else source_file
    return index.get(key)


def line_for(lines, offset):
    if not lines:
        return None
    offsets = [item[0] for item in lines]
    pos = bisect_right(offsets, offset) - 1
    return lines[pos][1] if pos >= 0 else None


def target(ref, package):
    if ":" not in ref:
        return None
    name, descriptor = ref.split(":", 1)
    name = name.replace('"', "").replace("/", ".").strip()
    if "." not in name:
        return None
    owner, method = name.rsplit(".", 1)
    if owner != package and not owner.startswith(package + "."):
        return None
    return f"{owner}#{method}{descriptor.strip()}"


def javap_usages(package, model_dir, deps_dir):
    if not shutil.which("javap"):
        raise SystemExit("javap not found on PATH; install/use a JDK")

    roots = class_roots(model_dir)
    classes = [path for root in roots for path in sorted(root.rglob("*.class"))]
    if not classes:
        raise SystemExit(f"no .class files found under {model_dir / 'classes'}")

    jars = sorted(str(path.resolve()) for path in deps_dir.glob("*.jar")) if deps_dir.exists() else []
    classpath = os.pathsep.join([str(root) for root in roots] + jars)
    sources = source_index(source_root(model_dir))

    found = {}
    cls = src_file = None
    calls = []
    dynamic_calls = []
    pending_dynamic = []
    line_table = []
    in_line_table = False
    in_bootstrap = False
    bootstrap = None
    bootstrap_targets = {}

    def add_found(fn, src, line):
        found.setdefault(fn, {"function": fn, "source": src, "line": line})

    def flush():
        nonlocal calls, dynamic_calls, line_table
        src = source_for(sources, cls, src_file)
        for offset, fn in calls:
            add_found(fn, src, line_for(line_table, offset))
        for offset, index in dynamic_calls:
            pending_dynamic.append((index, src, line_for(line_table, offset)))
        calls, dynamic_calls, line_table = [], [], []

    def flush_dynamic():
        for index, src, line in pending_dynamic:
            for fn in bootstrap_targets.get(index, []):
                add_found(fn, src, line)
        pending_dynamic.clear()

    def parse(line):
        nonlocal cls, src_file, calls, dynamic_calls, line_table, in_line_table
        nonlocal in_bootstrap, bootstrap
        stripped = line.strip()

        match = CLASSFILE_RE.match(stripped)
        if match:
            flush()
            flush_dynamic()
            cls = class_from_path(match.group(1), roots)
            src_file = None
            bootstrap_targets.clear()
            bootstrap = None
            in_bootstrap = False
            in_line_table = False
            return

        match = SOURCE_RE.match(stripped)
        if match:
            src_file = match.group(1)
            return

        if stripped == "BootstrapMethods:":
            flush()
            in_bootstrap = True
            bootstrap = None
            return
        if in_bootstrap:
            match = BOOTSTRAP_INDEX_RE.match(line)
            if match:
                bootstrap = int(match.group(1))
            match = REF_INVOKE_RE.search(line)
            if match and bootstrap is not None:
                fn = target(f"{match.group(1)}:{match.group(2)}", package)
                if fn:
                    bootstrap_targets.setdefault(bootstrap, set()).add(fn)
            return

        if line.startswith("  ") and not line.startswith("    "):
            if "(" in stripped or stripped == "static {};":
                flush()
                in_line_table = False
                return

        if stripped == "LineNumberTable:":
            in_line_table = True
            return
        if in_line_table:
            match = LINE_RE.match(stripped)
            if match:
                line_table.append((int(match.group(2)), int(match.group(1))))
                return
            in_line_table = False

        match = CALL_RE.match(line)
        if match:
            fn = target(match.group(2), package)
            if fn:
                calls.append((int(match.group(1)), fn))
            return

        match = DYNAMIC_RE.match(line)
        if match:
            dynamic_calls.append((int(match.group(1)), int(match.group(2))))

    for i in range(0, len(classes), 100):
        batch = [str(path) for path in classes[i:i + 100]]
        proc = subprocess.run(
            ["javap", "-classpath", classpath, "-verbose", "-p", "-c", "-l", *batch],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if proc.returncode:
            sys.stderr.write(proc.stderr)
            raise SystemExit(proc.returncode)
        for line in proc.stdout.splitlines():
            parse(line)
    flush()
    flush_dynamic()
    return [found[key] for key in sorted(found)]


def write_yaml(path, functions):
    lines = ["functions:"]
    if not functions:
        lines.append("  []")
    for item in functions:
        lines.append(f"  - function: {q(item['function'])}")
        lines.append(f"    source: {q(item['source'])}")
        lines.append(f"    line: {q(item['line'])}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description="Extract javap method calls for a package prefix.")
    parser.add_argument("--package", required=True, help="package prefix, e.g. org.pf4j")
    parser.add_argument("--model-dir", default=".opentaint/project")
    parser.add_argument("--deps-dir", help="default: <model-dir>/dependencies")
    parser.add_argument("--output", required=True, help="YAML output file")
    args = parser.parse_args()

    model_dir = Path(args.model_dir)
    deps_dir = Path(args.deps_dir) if args.deps_dir else model_dir / "dependencies"
    functions = javap_usages(args.package.replace("/", "."), model_dir, deps_dir)
    write_yaml(Path(args.output), functions)
    print(f"wrote {args.output} ({len(functions)} functions)")


if __name__ == "__main__":
    main()
