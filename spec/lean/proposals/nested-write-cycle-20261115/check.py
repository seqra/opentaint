#!/usr/bin/env python3
"""Rebuild and audit the constructive, uncapped nested-write counterexample."""
import argparse,hashlib,json,os,re,shutil,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--reuse-dependencies',action='store_true');a=p.parse_args();pkg=Path(__file__).resolve().parent;out=a.out.resolve()
 if not a.reuse_dependencies:
  subprocess.run(['python3',str(pkg.parent/'exclusion-child-replay-20261115'/'check.py'),'--out',str(out)],check=True)
 receipt=json.loads((out/'receipt.json').read_text())
 if a.reuse_dependencies:
  for name,entry in receipt['models'].items():
   assert (out/(name+'.olean')).is_file(),name
   assert hashlib.sha256(Path(entry['source']).read_bytes()).hexdigest()==entry['sha256'],name
 added=0
 for name in ['NestedWriteReplay','NestedWriteCold','NestedWriteBodies','NestedWriteStable','NestedWriteConcrete','NestedWriteControl']:
  src=pkg/(name+'.lean');contents=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M);prints=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
  assert len(claims)==len(prints)and all(any(n.endswith('.'+c)for n in prints)for c in claims),(name,claims,prints)
  shutil.copy2(src,out/src.name)
  proc=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
  log=proc.stdout+proc.stderr;(out/(name+'.txt')).write_text(log)
  if proc.returncode:raise RuntimeError(name+': '+log[:5000])
  assert 'warning:'not in log,log[:2000]
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims),(name,len(audited),len(claims))
  for n,axioms in audited:assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
  receipt['models'][name]=dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited));added+=len(audited)
 receipt['auditedDeclarations']=sum(x['auditedDeclarations']for x in receipt['models'].values())
 receipt['scope']='Synthetic fully analyzed ordinary nested-write core forms; complete cold return-cone C2/C5/caller packets through run-11; arbitrary later two-phase recurrence with ZERO/Target continuation; exact concrete negative reachability. Native operator tests, not an end-to-end JVM-front-end or production implementation run.'
 receipt['latestColdRun']=11;receipt['finiteExplorationLatestRun']=61;receipt['newDeclarations']=added
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=added,auditedDeclarations=receipt['auditedDeclarations'],modules=len(receipt['models']),receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
