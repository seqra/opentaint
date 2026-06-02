#!/usr/bin/env python3
"""Render an opentaint package.json from a template.

Loads a template package.json, applies the given fields, and writes the result
with stable 2-space indentation and a trailing newline. Used by
build-npm-packages.sh to generate the main and per-platform package manifests
without constructing JSON in the shell.

Usage:
  render-package-json.py --template <tmpl> --out <out> --version <v> \\
      [--name <name>] [--os <os>] [--cpu <cpu>] \\
      [--optional-dep <name>=<version> ...]

  --name / --os / --cpu        per-platform package fields (os/cpu become
                               single-element arrays, as npm expects)
  --optional-dep name=version  appended to optionalDependencies (repeatable);
                               used for the main package's pinned platform deps
"""

import argparse
import json
import sys


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--template", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--version", required=True)
    parser.add_argument("--name")
    parser.add_argument("--os")
    parser.add_argument("--cpu")
    parser.add_argument("--optional-dep", action="append", default=[], dest="optional_deps")
    args = parser.parse_args(argv)

    with open(args.template) as f:
        pkg = json.load(f)

    pkg["version"] = args.version
    if args.name is not None:
        pkg["name"] = args.name
    if args.os is not None:
        pkg["os"] = [args.os]
    if args.cpu is not None:
        pkg["cpu"] = [args.cpu]

    if args.optional_deps:
        deps = pkg.setdefault("optionalDependencies", {})
        for pair in args.optional_deps:
            name, _, ver = pair.partition("=")
            if not name or not ver:
                parser.error(f"--optional-dep must be name=version, got: {pair!r}")
            deps[name] = ver

    with open(args.out, "w") as f:
        json.dump(pkg, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    main(sys.argv[1:])
