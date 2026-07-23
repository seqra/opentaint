#!/usr/bin/env python3
"""Structural lint for the Java passThrough config (model/java/config).

Invariants (see docs/superpowers/specs/2026-07-23-rule-storage-rekey-design.md):
  I1 no class has a slot written by one property and read by a different one
  I2 every named slot has at least one writer and one reader
  I3 every array param feeding a scalar target has an explicit [*] edge
  I4 no [*] on a non-array-typed position
  I5 no out-of-range arg(n)
  I6 no <rule-storage> anywhere in the Java config (final gate)
"""
import json
import os
import re
import sys
from typing import NamedTuple, Optional

import yaml


class Copy(NamedTuple):
    frm: tuple
    to: tuple


class Entry(NamedTuple):
    file: str
    func: object
    sig: object
    copies: list


class Finding(NamedTuple):
    code: str
    file: str
    func: str
    detail: str


def _pos(v) -> tuple:
    return tuple(v) if isinstance(v, list) else (v,)


def func_name(func) -> str:
    return func if isinstance(func, str) else json.dumps(func, sort_keys=True)


def load_entries(root: str) -> list:
    entries = []
    for dirpath, _, files in os.walk(root):
        for name in sorted(files):
            if not name.endswith((".yaml", ".yml")):
                continue
            path = os.path.join(dirpath, name)
            with open(path) as fh:
                doc = yaml.safe_load(fh)
            if not isinstance(doc, dict):
                continue
            rel = os.path.relpath(path, root)
            for raw in doc.get("passThrough") or []:
                copies = [Copy(_pos(c["from"]), _pos(c["to"])) for c in raw.get("copy") or []]
                entries.append(Entry(rel, raw.get("function"), raw.get("signature"), copies))
    return entries


def arity(sig) -> Optional[int]:
    """Number of declared parameters, or None when unknown/wildcarded."""
    if isinstance(sig, dict):
        params = sig.get("params")
        return None if params is None else len(params)
    if not isinstance(sig, str) or not sig.startswith("("):
        return None
    inner = sig[1:sig.index(")")].strip()
    if "*" in inner:
        return None
    return 0 if inner == "" else len(inner.split(","))


_ARG = re.compile(r"arg\((\d+)\)")


def check_arg_range(entries) -> list:
    findings = []
    for e in entries:
        n = arity(e.sig)
        if n is None:
            continue
        for c in e.copies:
            for side in (c.frm, c.to):
                m = _ARG.fullmatch(side[0])
                if m and int(m.group(1)) >= n:
                    findings.append(Finding(
                        "I5", e.file, func_name(e.func),
                        f"{side[0]} but signature declares {n} parameter(s)"))
    return findings
