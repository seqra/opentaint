#!/usr/bin/env python3
"""Check proposed uniform-NE coverage and closed old/new regression traces."""
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
    counterexample = package.parent / 'bounded-refinement-ordinary-cycle-20261114'
    subprocess.run(['python3', str(counterexample / 'check.py'), '--out', str(out)], check=True)
    receipt_path = out / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    count = 0
    for name in ['UniformCoverage', 'Closure', 'Regressions', 'VirtualProviders']:
        source = package / (name + '.lean')
        contents = source.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             contents, re.M)
        names = re.findall(r'^(?:@\[simp\]\s+)?theorem\s+(\w+)', contents, re.M)
        printed = re.findall(r'^#print axioms ([\w.]+)', contents, re.M)
        assert len(printed) == len(names)
        for theorem in names:
            assert any(p.endswith('.' + theorem) for p in printed), theorem
        shutil.copy2(source, out / source.name)
        result = subprocess.run(['lean', '-o', name + '.olean', source.name], cwd=out,
                                env={**os.environ, 'LEAN_PATH': str(out)},
                                text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (name + '.txt')).write_text(log)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        assert 'warning:' not in log, log
        audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert len(audited) == len(names), name
        for theorem, axioms in audited:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (theorem, axioms)
        receipt['models'][name] = dict(source=str(source),
            sha256=hashlib.sha256(source.read_bytes()).hexdigest(), auditedDeclarations=len(audited))
        count += len(audited)
    receipt['auditedDeclarations'] += count
    receipt['scope'] = 'uniform FLOW/NE output coverage; closed old/new/BB run3 fixed points; regressions; warm NORMAL views'
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(receipt['models']),
        auditedDeclarations=receipt['auditedDeclarations'], newDeclarations=count,
        receipt=str(receipt_path)), indent=2))


if __name__ == '__main__':
    main()
