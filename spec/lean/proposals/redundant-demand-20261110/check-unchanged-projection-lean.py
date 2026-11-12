#!/usr/bin/env python3
"""Repeat the constructive UnchangedProjectionCover checks and axiom audit."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
MODEL = HERE / 'UnchangedProjectionCover.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    output = args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source = MODEL.read_text()
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|\bClassical\.|^\s*axiom\b', source, re.M)
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
    names = re.findall(r'^theorem (\w+)', source, re.M)
    generic = re.findall(r'^theorem (\w+)', source.split('/-! Executable positive')[0], re.M)
    assert len(names) == len(set(names)) and len(generic) >= 14
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'spec/lean', text=True).strip()
    runs = []
    for path, name in [(MODEL, 'model')]:
        command = ['lake', 'env', 'lean', str(path)]
        result = subprocess.run(command, cwd=ROOT / 'spec/lean', text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = output / (name + '.txt')
        log.write_text(result.stdout)
        assert result.returncode == 0, result.stdout
        runs.append({'command': command, 'exitCode': result.returncode,
                     'log': log.name, 'logSha256': sha(log)})
    audit = output / 'AxiomAudit.lean'
    audit.write_text(source + '\n' + '\n'.join('#print axioms UnchangedProjectionCover.' + n for n in names) + '\n')
    command = ['lake', 'env', 'lean', str(audit)]
    result = subprocess.run(command, cwd=ROOT / 'spec/lean', text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = output / 'axioms.txt'
    log.write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    seen = set()
    for line in result.stdout.splitlines():
        if 'depends on axioms:' in line:
            seen.update(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', line.split('depends on axioms:')[1]))
    assert seen <= {'propext', 'Quot.sound'}, seen
    assert 'Classical.choice' not in result.stdout
    for name in names:
        assert ('UnchangedProjectionCover.' + name) in result.stdout, 'Missing theorem audit: ' + name
    receipt = {
        'schema': 'redundant-demand-unchanged-projection-cover-lean-v1',
        'predicate': 'UnchangedProjectionCover', 'version': 1,
        'createdAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'runtimeReference': '14d7b63369d94f49d4c551be8405ed7719f267cc',
        'leanVersion': version, 'toolchain': 'leanprover/lean4:v4.33.1',
        'modelSource': str(MODEL.relative_to(ROOT)), 'modelSha256': sha(MODEL),
        'checkerSha256': sha(Path(__file__)), 'genericTheorems': generic,
        'executableExamples': [n for n in names if n not in generic],
        'theoremCount': len(names), 'runs': runs,
        'axiomAudit': {'command': command, 'exitCode': result.returncode,
                       'sourceSha256': sha(audit), 'logSha256': sha(log),
                       'allTheoremsAudited': len(names), 'dependencies': sorted(seen)},
        'jointRemoval': 'For any R subset U and all checked Q, projections of (O without R) without Q equal projections of O without R; R and Q can overlap',
        'scope': 'Exact finite next-run projection membership, preserved stable state, deterministic future states/observations and nondeterministic finite traces',
        'nativeSourceCorrespondenceValidated': False,
        'actualCorpusCertificatesVerified': False,
        'productionChanged': False,
        'limits': ['Native emit must equal the complete real projection, including paired endpoints and ports',
                   'The native projection encoding must be injective over full normalized row identities',
                   'Raw stores, NORMAL persistence, reports, seeds and source hits remain unchanged',
                   'No raw edge or ND premise deletion is proved',
                   'These generic proofs do not by themselves classify a campaign occurrence'],
    }
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'theorems': len(names), 'generic': len(generic),
                      'examples': len(names) - len(generic), 'axioms': sorted(seen)}))


if __name__ == '__main__':
    main()
