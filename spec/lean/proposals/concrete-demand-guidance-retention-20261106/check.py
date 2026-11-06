#!/usr/bin/env python3
"""Root-only Lean checker for the unselected concrete-MAY retention proposal."""
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
MODEL = HERE / 'ConcreteGuidance.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    model = MODEL.read_text()
    uncommented = re.sub(r'/\-.*?\-/', '', model, flags=re.S)
    uncommented = re.sub(r'--[^\n]*', '', uncommented)
    assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b', uncommented, re.M)
    assert not re.search(r'\b(?:sorry|admit|Classical)\b', uncommented)
    assert re.findall(r'^import (.+)$', uncommented, re.M) == ['RestrictedInitialPolicy']
    names = re.findall(r'^theorem (\w+)', model, re.M)
    printed = re.findall(r'^#print axioms (\w+)', model, re.M)
    assert names and len(names) == len(set(names)) and names == printed
    with tempfile.TemporaryDirectory(prefix='concrete-may-proposal-') as temporary:
        env = dict(os.environ)
        env['LEAN_PATH'] = temporary + os.pathsep + env.get('LEAN_PATH', '')
        commands = [
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'RestrictedInitialPolicy.olean'), str(BASE)],
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'ConcreteGuidance.olean'), str(MODEL)],
        ]
        outputs = []
        for command in commands:
            result = subprocess.run(command, cwd=LEAN_ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(result.stdout)
            assert 'error:' not in result.stdout and 'sorryAx' not in result.stdout
            outputs.append(result.stdout)
    for dependencies in re.findall(r'depends on axioms:\s*\[([^]]*)\]', '\n'.join(outputs), re.S):
        assert set(filter(None, dependencies.replace('\n', '').replace(' ', '').split(','))) <= {'propext', 'Quot.sound'}
    audit = [line for line in outputs[1].splitlines() if line.startswith("'ConcreteGuidance.")]
    assert len(audit) == len(names)
    assert 'CONCRETE_GUIDANCE_WITNESS=true' in outputs[1]
    assert 'CONCRETE_GUIDANCE_WITNESS=false' not in outputs[1]
    receipt = {
        'schema': 'concrete-demand-guidance-proposal-proof-check-v1',
        'state': 'PASS_PROPOSAL_LOCAL_MODEL_ONLY_BEHAVIOR_NOT_SELECTED',
        'model': MODEL.name, 'modelSha256': sha(MODEL),
        'base': str(BASE.relative_to(LEAN_ROOT)), 'baseSha256': sha(BASE),
        'checkerSha256': sha(Path(__file__)),
        'leanToolchain': (LEAN_ROOT / 'lean-toolchain').read_text().strip(),
        'theorems': len(names), 'theoremNames': names, 'axiomAudit': audit,
        'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'executableWitness': True,
        'scope': 'Conditional supplied FULL concrete MAY coordinates under DEMAND/ANY/Empty-E; separate support/protection streams; current EXACT view unchanged; unchanged finite scalar C2 cells and exact paired-owner projection.',
        'notProved': ['Native canonicalizer/group equivalence', 'Every producer/adaptor supplies the child coordinate',
                      'Same-head MAY/EXACT guide-image preservation', 'C5/budget/call/ND/static/alias/manager-role correctness',
                      'Nonempty E or STAR/MUST/NORMAL/FLOW repair', 'Shared-loop recovery or full-project quality'],
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        assert args.output.resolve() != (HERE / 'preparation.json').resolve()
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
