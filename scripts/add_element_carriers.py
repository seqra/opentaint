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


def _entry_of(file_rel, entry, copies):
    return cl.Entry(file_rel, entry.get("function"), entry.get("signature"),
                     [cl.Copy(_as_tuple(c["from"]), _as_tuple(c["to"])) for c in copies])


def _find_culprit(file_rel, entry, copies, finding_count):
    """The copy whose removal makes an I3 finding disappear -- i.e. the copy
    the gate is blaming. Consults check_element_carrier as a black box: this
    function never re-derives *when* a carrier is needed (that is entirely
    the gate's call), only *which* already-flagged copy a finding names, so
    the fix set can never drift from what I3 actually checks.
    """
    for i in range(len(copies)):
        trial = copies[:i] + copies[i + 1:]
        if len(cl.check_element_carrier([_entry_of(file_rel, entry, trial)])) < finding_count:
            return i
    return None


def add_carriers(doc: dict, file_rel: str):
    added = 0
    for entry in doc.get("passThrough") or []:
        copies = list(entry.get("copy") or [])
        while True:
            findings = cl.check_element_carrier([_entry_of(file_rel, entry, copies)])
            if not findings:
                break
            culprit = _find_culprit(file_rel, entry, copies, len(findings))
            if culprit is None:
                break  # defensive: no single copy's removal explains the finding
            c = cl.Copy(_as_tuple(copies[culprit]["from"]), _as_tuple(copies[culprit]["to"]))
            carrier_from, carrier_to = c.frm + ("[*]",), c.to
            copies.append({
                "from": list(carrier_from),
                "to": list(carrier_to) if len(carrier_to) > 1 else carrier_to[0],
            })
            added += 1
        entry["copy"] = copies
    # `added` counts carriers emitted, which can be fewer than the raw I3
    # finding count: two identical whole-copies in one entry produce two
    # findings but need only one carrier. The repaired document satisfies the
    # gate either way -- do not treat `added` as a finding count.
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
