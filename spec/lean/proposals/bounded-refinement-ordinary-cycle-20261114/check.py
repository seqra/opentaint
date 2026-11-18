#!/usr/bin/env python3
"""Check the ordinary-code uncapped counterexample and proposal references."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    out = args.out.resolve()
    frontier = package.parent / 'bounded-refinement-frontier-20261114'
    subprocess.run(['python3', str(frontier / 'check.py'), '--out', str(out)], check=True)
    receipt_path = out / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    source = package / 'OrdinaryCycle.lean'
    contents = source.read_text()
    assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                         contents, re.M)
    names = re.findall(r'^(?:@\[simp\]\s+)?theorem\s+(\w+)', contents, re.M)
    for name in names:
        assert f'#print axioms BoundedOrdinaryCycle.{name}\n' in contents, name
    shutil.copy2(source, out / source.name)
    result = subprocess.run(['lean', '-o', 'OrdinaryCycle.olean', source.name], cwd=out,
                            env={**os.environ, 'LEAN_PATH': str(out)},
                            text=True, capture_output=True)
    log = result.stdout + result.stderr
    (out / 'OrdinaryCycle.txt').write_text(log)
    if result.returncode:
        print(log)
        raise SystemExit(result.returncode)
    assert 'warning:' not in log, log
    audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
    assert len(audited) == len(names)
    for theorem, axioms in audited:
        assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (theorem, axioms)
    receipt['models']['OrdinaryCycle'] = dict(source=str(source),
        sha256=hashlib.sha256(source.read_bytes()).hexdigest(), auditedDeclarations=len(audited))
    receipt['auditedDeclarations'] += len(audited)
    receipt['scope'] = 'ordinary-code global-cut recurrence; C2/C5; two-call forward/backward pipeline; uncapped induction'
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(receipt['models']),
        auditedDeclarations=receipt['auditedDeclarations'], newCycleDeclarations=len(audited),
        receipt=str(receipt_path)), indent=2))


if __name__ == '__main__':
    main()
