#!/usr/bin/env python3
"""Root-only check of the NORMAL STAR/FLOW admission counterexample."""
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
MODEL = HERE / 'NormalStarFlowAdmissionGap.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    model = MODEL.read_text()
    source = re.sub(r'/\-.*?\-/', '', model, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    assert re.findall(r'^import (.+)$', source, re.M) == ['RestrictedInitialPolicy']
    assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b', source, re.M)
    assert not re.search(r'\b(?:sorry|admit|Classical)\b', source)
    names = re.findall(r'^theorem (\w+)', model, re.M)
    assert names and names == re.findall(r'^#print axioms (\w+)', model, re.M)
    with tempfile.TemporaryDirectory(prefix='normal-star-flow-gap-') as temporary:
        env = dict(os.environ)
        env['LEAN_PATH'] = temporary + os.pathsep + env.get('LEAN_PATH', '')
        commands = [
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'RestrictedInitialPolicy.olean'), str(BASE)],
            ['lake', 'env', 'lean', '-M2048', '-o', str(Path(temporary) / 'NormalStarFlowAdmissionGap.olean'), str(MODEL)],
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
    audit = [line for line in outputs[1].splitlines() if line.startswith("'NormalStarFlowAdmissionGap.")]
    assert len(audit) == len(names)
    assert 'NORMAL_STAR_FLOW_GAP=true' in outputs[1] and 'NORMAL_STAR_FLOW_GAP=false' not in outputs[1]
    receipt = {
        'schema': 'normal-star-flow-admission-gap-proof-check-v1',
        'state': 'PASS_COUNTEREXAMPLE_ONLY_ADMISSION_DECISION_PENDING',
        'model': MODEL.name, 'modelSha256': sha(MODEL), 'checkerSha256': sha(Path(__file__)),
        'scalarSourceSha256': sha(BASE), 'theorems': len(names), 'theoremNames': names,
        'axiomAudit': audit, 'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'scope': 'Existing same-head ANY demand/STAR FLOW rejection, a typed NORMAL STAR/FLOW read suffix adapter, and f/g exact full-T composition including empty suffix; ordinary bases/countable fields/Empty E.',
        'notProved': ['New policy or emitter correctness', 'Termination', 'Native AP equivalence beyond separately prepared isolated witness',
                      'Actor scheduling/C2 acceptance or real-program recovery', 'STAR/MUST substitution or changed layer/field/rule/mark semantics'],
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        assert args.output.resolve().parent == HERE and args.output.name == 'normal-star-gap-checks.json'
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
