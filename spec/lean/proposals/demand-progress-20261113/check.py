#!/usr/bin/env python3
"""Check the finite prefix reference and progress obstructions externally."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--handoff', action='store_true', help='also check executable evidence composition and coverage')
    parser.add_argument('--calls', action='store_true', help='also check method-relative call evidence binding')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    reference = package.parent / 'non-empty-may-20261113'
    cycle = package.parent / 'non-empty-may-acyclic-cycle-20261113'
    repo = package.parents[3]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    models = {}
    total = 0
    names = ['NonEmptyMay', 'Policy', 'Restriction', 'Coverage', 'Cycle', 'BbTrace', 'Progress']
    if args.handoff or args.calls:
        names.append('Handoff')
    if args.calls:
        names.append('Calls')
    for name in names:
        directory = package if name in {'Progress','Handoff','Calls'} else cycle if name in {'Cycle', 'BbTrace'} else reference
        source = directory / (name + '.lean')
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             source.read_text(), re.M), source
        shutil.copy2(source, out / source.name)
        result = subprocess.run(['lean', '-o', name + '.olean', source.name], cwd=out,
            env={**os.environ, 'LEAN_PATH': str(out)}, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (name + '.txt')).write_text(log)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert audited, name
        for theorem, axioms in audited:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (theorem, axioms)
        total += len(audited)
        models[name] = dict(source=str(source.relative_to(repo)), sourceSha256=sha(source),
            objectSha256=sha(out / (name + '.olean')), auditedDeclarations=len(audited))
    receipt = dict(leanVersion=subprocess.check_output(['lean', '--version'], text=True).strip(),
        scope='neutral-prefix call evidence binding and handoff checker; no native scheduler theorem' if args.calls else
              'finite prefix evidence checker and existing progress reference; no production termination theorem' if args.handoff else
              'finite acyclic prefix reference; existing demand cycles; no production termination theorem',
        models=models, auditedDeclarations=total)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(models), auditedDeclarations=total,
                         receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
