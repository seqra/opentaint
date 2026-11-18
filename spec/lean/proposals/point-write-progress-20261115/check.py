#!/usr/bin/env python3
"""Constructive point-write progress proofs and all old/new cold references."""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess
from pathlib import Path

def main():
 q=argparse.ArgumentParser();q.add_argument('--out',type=Path,required=True);q.add_argument('--dependencies',type=Path);a=q.parse_args();pkg=Path(__file__).resolve().parent;out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
 if a.dependencies:
  base=a.dependencies.resolve();receipt=json.loads((base/'receipt.json').read_text())
  for name,entry in receipt['models'].items():
   assert hashlib.sha256(Path(entry['source']).read_bytes()).hexdigest()==entry['sha256'],name
   for ext in ('.olean','.lean','.txt'):
    src=base/(name+ext)
    if src.is_file():shutil.copy2(src,out/src.name)
 else:
  subprocess.run(['python3',str(pkg.parent/'nested-write-cycle-20261115'/'check.py'),'--out',str(out)],check=True)
  receipt=json.loads((out/'receipt.json').read_text())
 def compile(name):
  src=pkg/(name+'.lean');contents=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M);prints=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
  assert len(claims)==len(prints)and all(any(n.endswith('.'+c)for n in prints)for c in claims),(name,len(claims),len(prints))
  shutil.copy2(src,out/src.name)
  proc=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
  log=proc.stdout+proc.stderr;(out/(name+'.txt')).write_text(log)
  if proc.returncode:raise RuntimeError(name+': '+log[:5000])
  assert 'warning:'not in log,log[:2000]
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims),(name,len(audited),len(claims))
  for n,axs in audited:assert set(axs.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axs)
  print('PASS',name,len(audited),flush=True)
  return name,dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
 results=[compile('PointWriteReplay'),compile('PointWriteProperties')]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
  results+=list(pool.map(compile,sorted(p.stem for p in pkg.glob('PointCertificate*.lean'))))
 for name,item in results:receipt['models'][name]=item
 receipt['auditedDeclarations']=sum(v['auditedDeclarations']for v in receipt['models'].values());receipt['newDeclarations']=sum(v['auditedDeclarations']for _,v in results)
 receipt['scope']='Remove only EXACT/FLOW descendant-keep MAY contributions. Generic constructive point semantics, native NORMAL and unsupported cases, fixed-plan work; complete cold initial/publication/caller/handoff/quiescence and natural DATA/Target stop for all 12 prior references plus 6 nested-write references; exact old-state equality. Synthetic core-form scope; no universal whole-analyzer termination claim.'
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=receipt['newDeclarations'],auditedDeclarations=receipt['auditedDeclarations'],modules=len(receipt['models']),receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
