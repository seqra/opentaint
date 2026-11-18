#!/usr/bin/env python3
"""Recheck all old examples and same-lane uniform termination of the protected cycle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    package=Path(__file__).resolve().parent
    out=args.out.resolve()
    previous=package.parent/'protected-cleaner-growth-cycle-20261114'
    subprocess.run(['python3',str(previous/'check.py'),'--out',str(out)],check=True)
    receipt_path=out/'receipt.json'
    receipt=json.loads(receipt_path.read_text())
    added=0
    for module in ['UniformService','MarkedClosure','PacketOrder','Acceptance']:
        source=package/(module+'.lean')
        contents=source.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',contents,re.M)
        names=re.findall(r'^(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M)
        printed=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
        assert len(names)==len(printed)
        assert all(any(p.endswith('.'+name)for p in printed)for name in names)
        shutil.copy2(source,out/source.name)
        result=subprocess.run(['lean','-o',module+'.olean',source.name],cwd=out,
            env={**os.environ,'LEAN_PATH':str(out)},text=True,capture_output=True)
        log=result.stdout+result.stderr
        (out/(module+'.txt')).write_text(log)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        assert 'warning:' not in log,log
        audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
        assert len(audited)==len(names)
        for name,axioms in audited:
            assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(name,axioms)
        receipt['models'][module]=dict(source=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
        receipt['auditedDeclarations']+=len(audited)
        added+=len(audited)
    receipt['scope']='Same-lane NORMAL uniform-to-NE coverage, complete concrete/FLOW/mx/H two-call closure, reply packet order and every old acceptance case'
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',modules=len(receipt['models']),auditedDeclarations=receipt['auditedDeclarations'],newDeclarations=added,receipt=str(receipt_path)),indent=2))


if __name__=='__main__':
    main()
