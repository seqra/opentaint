#!/usr/bin/env python3
"""Check the finite guidance model against the unchanged scalar C2 model."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parents[1]
BASE = LEAN_ROOT / 'proposals/initial-emission/RestrictedInitialPolicy.lean'
MODEL = HERE / 'GuidanceFrontier.lean'
PRODUCER = HERE / 'ProducerGuidance.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    modules = []
    for path, count in ((MODEL, 16), (PRODUCER, 23)):
        model = path.read_text()
        assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b', model, re.M)
        assert not re.search(r'\b(?:sorry|admit|Classical)\b', re.sub(r'/\-.*?\-/', '', model, flags=re.S))
        names = re.findall(r'^theorem (\w+)', model, re.M)
        printed = re.findall(r'^#print axioms (\w+)', model, re.M)
        assert len(names) == count and names == printed
        modules.append({'file': path.name, 'sha256': sha(path), 'theorems': count})
    with tempfile.TemporaryDirectory(prefix='guidance-frontier-') as temporary:
        env = dict(os.environ)
        env['LEAN_PATH'] = temporary + os.pathsep + env.get('LEAN_PATH', '')
        commands = [
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'RestrictedInitialPolicy.olean'), str(BASE)],
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'GuidanceFrontier.olean'), str(MODEL)],
            ['lake', 'env', 'lean', '-M2048', str(PRODUCER)],
        ]
        outputs = []
        for command in commands:
            result = subprocess.run(command, cwd=LEAN_ROOT, env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(result.stdout)
            assert 'error:' not in result.stdout and 'sorryAx' not in result.stdout
            outputs.append(result.stdout)
    all_output = '\n'.join(outputs)
    for dependencies in re.findall(r'depends on axioms:\s*\[([^]]*)\]', all_output, re.S):
        assert set(dependencies.replace('\n', '').replace(' ', '').split(',')) <= {'propext', 'Quot.sound'}
    audit = [line for output in outputs[1:] for line in output.splitlines()
             if line.startswith(("'GuidanceFrontier.", "'ProducerGuidance."))]
    total = sum(module['theorems'] for module in modules)
    assert len(audit) == total
    receipt = {
        'state': 'PASS', 'model': MODEL.name, 'modelSha256': sha(MODEL),
        'base': str(BASE.relative_to(LEAN_ROOT)), 'baseSha256': sha(BASE),
        'leanToolchain': (LEAN_ROOT / 'lean-toolchain').read_text().strip(),
        'theorems': total, 'modules': modules, 'axiomAudit': audit,
        'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'scope': 'finite C2 images, coordinate add/delta, exact paired-label handoff and same-head mx request union; unchanged scalar emit',
        'notProved': ['producer retention before normalization', 'production C5 restriction and budgets',
                      'role transitions and engine adapters', 'whole-engine effect or final Conductor recovery'],
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
