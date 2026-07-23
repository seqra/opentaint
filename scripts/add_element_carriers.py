#!/usr/bin/env python3
"""Add the element carriers that config_lint's I3 invariant reports as missing.

A whole copy `arg(N) -> T` re-roots `arg(N)[i]` to `T[i]`, which is a dead fact
when T is a scalar, so the explicit `[arg(N),'[*]'] -> T` edge is the only thing
carrying element taint. This adds exactly the edges I3 asks for -- the fix set is
the lint's own findings, so it cannot drift from the gate.
"""
import argparse
import sys

import yaml

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import config_lint as cl
from rekey_holder import DUMP_WIDTH


def _as_tuple(v):
    return tuple(v) if isinstance(v, list) else (v,)


def add_carriers(doc: dict, file_rel: str):
    added = 0
    for entry in doc.get("passThrough") or []:
        copies = entry.get("copy") or []
        e = cl.Entry(file_rel, entry.get("function"), entry.get("signature"),
                     [cl.Copy(_as_tuple(c["from"]), _as_tuple(c["to"])) for c in copies])
        missing = cl.check_element_carrier([e])
        if not missing:
            continue
        present = {(c.frm, c.to) for c in e.copies}
        new_copies = list(copies)
        for c in e.copies:
            if "[*]" in c.frm or "[*]" in c.to:
                continue
            src_t = cl.position_type(e, c.frm)
            if src_t is None or not src_t.endswith("[]"):
                continue
            if cl._dst_holds_element(e, c.to):
                continue
            carrier = (c.frm + ("[*]",), c.to)
            if carrier in present:
                continue
            present.add(carrier)
            new_copies.append({
                "from": list(carrier[0]),
                "to": list(carrier[1]) if len(carrier[1]) > 1 else carrier[1][0],
            })
            added += 1
        entry["copy"] = new_copies
    return doc, added


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--file", required=True)
    args = ap.parse_args(argv)
    with open(args.file) as fh:
        doc = yaml.safe_load(fh)
    out, added = add_carriers(doc, args.file)
    with open(args.file, "w") as fh:
        yaml.safe_dump(out, fh, default_flow_style=False, sort_keys=False, width=DUMP_WIDTH)
    print(f"added {added} element carrier(s) to {args.file}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
