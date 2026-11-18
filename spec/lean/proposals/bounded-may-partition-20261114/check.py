#!/usr/bin/env python3
"""Compile the bounded-partition investigation in a fresh external directory."""
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
    parser.add_argument('--partition-only', action='store_true')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    reference = package.parent / 'non-empty-may-20261113'
    cycle = package.parent / 'non-empty-may-acyclic-cycle-20261113'
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    modules = [('NonEmptyMay', reference), ('Policy', reference)]
    if not args.partition_only:
        modules += [('Restriction', reference), ('Coverage', reference),
                    ('Cycle', cycle), ('BbTrace', cycle)]
    modules += [('Partition', package)]
    if not args.partition_only:
        modules += [('Investigation', package)]
    audited_total = 0
    models = {}
    for name, directory in modules:
        source = directory / (name + '.lean')
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             source.read_text(), re.M), source
        shutil.copy2(source, out / source.name)
        result = subprocess.run(['lean', '-o', name + '.olean', source.name],
            cwd=out, env={**os.environ, 'LEAN_PATH': str(out)},
            text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (name + '.txt')).write_text(log)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert audited, name
        for theorem, axioms in audited:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (theorem, axioms)
        audited_total += len(audited)
        models[name] = dict(source=str(source),
            sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            auditedDeclarations=len(audited))
    receipt = dict(leanVersion=subprocess.check_output(['lean', '--version'], text=True).strip(),
        scope='finite guard partition and acyclic prefix reference; not native correspondence',
        models=models, auditedDeclarations=audited_total)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(modules),
        auditedDeclarations=audited_total, receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
