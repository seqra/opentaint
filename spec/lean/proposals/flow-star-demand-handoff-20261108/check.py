#!/usr/bin/env python3
"""Check the pinned C5 package and the STAR-demand projection bridge."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    out = args.output_directory.resolve()
    assert not out.exists(), 'Select a fresh directory; preserve old receipts.'
    out.mkdir(parents=True)
    pinned = HERE.parent / 'subsumption-initial-demand-20261107'
    receipt = dict(state='STARTED', checkedAtUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   proofScope='Selected C5 followed by existing guidance projection; format and paired-row preservation only.',
                   nativeAnalyzerProved=False, allPrincipalProgramsProved=False)
    try:
        result = subprocess.run([sys.executable, str(pinned / 'check.py'), '--output-directory', str(out / 'components')],
                                cwd=REPO, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / 'components.log').write_text(result.stdout)
        assert result.returncode == 0, 'The pinned component package must pass first.'
        source = HERE / 'Handoff.lean'
        code = re.sub(r'/-.*?-/', '', source.read_text(), flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'\b(?:sorry|admit|axiom|Classical|noncomputable|unsafe|partial)\b', code)
        names = ['FlowStarDemandHandoff.' + name for name in re.findall(r'^theorem (\w+)', code, re.M)]
        env = dict(os.environ, LEAN_PATH=str(out / 'components'))
        result = subprocess.run(['lake', 'env', 'lean', '--root=' + str(HERE), '-M2048',
                                 '-o', str(out / 'Handoff.olean'), str(source)],
                                cwd=REPO / 'spec' / 'lean', env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / 'Handoff.log').write_text(result.stdout)
        assert result.returncode == 0, 'See Handoff.log.'
        assert 'sorryAx' not in result.stdout
        found = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", result.stdout, re.M)
        assert found == names
        for name, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S):
            used = set(filter(None, deps.replace('\n', '').replace(' ', '').split(',')))
            assert used <= {'propext', 'Quot.sound'}, (name, used)
        receipt.update(state='PASS_LOCAL_COMPONENTS_ONLY', checkedBridgeTheorems=len(names),
                       bridgeTheorems=names, sourceSha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                       pinnedPackageReceipt=json.loads((out / 'components' / 'checks.json').read_text()))
    finally:
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['state', 'checkedBridgeTheorems', 'allPrincipalProgramsProved']}))


if __name__ == '__main__':
    main()
