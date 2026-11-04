#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, time
ROOT=Path(__file__).resolve().parent
MODEL=ROOT/'Sparse.lean'
NOTE=ROOT.parent/'sparse-c5-program-finalization-20261104.md'
OUT=ROOT/'verification'
OUT.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
names=re.findall(r'^(?:theorem|def|abbrev|structure|inductive)\s+(\w+)',MODEL.read_text(),re.M)
axioms=OUT/'Audit.lean'
axioms.write_text('import Sparse\n'+'\n'.join('#print axioms SparseC5Finalization.'+name for name in names)+'\n')
env=os.environ.copy();env['ELAN_TOOLCHAIN']='leanprover/lean4:v4.33.1';env['LEAN_PATH']=str(ROOT)
lean=shutil.which('lean')
if not lean:raise SystemExit('Lean unavailable')
started=time.monotonic()
for label,args in [('Compile',[lean,'-j1','-M768','-o',str(ROOT/'Sparse.olean'),str(MODEL)]),('Audit',[lean,'-j1','-M768',str(axioms)])]:
 p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(label+'.log')).write_text(p.stdout)
 if p.returncode:raise SystemExit(label+' failed: '+p.stdout)
text=(OUT/'Audit.log').read_text()
found=set()
for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text):
 found.update(name.strip() for name in group.split(',') if name.strip())
if found-{'propext','Quot.sound'}:raise SystemExit('Rejected axioms: '+repr(found))
if len(re.findall(r"'SparseC5Finalization\.",text))!=len(names):raise SystemExit('Incomplete explicit declaration audit')
receipt={'status':'PASS_CONDITIONAL_MODEL_ONLY','selected':False,'implemented':False,'kotlin_verified':False,
 'toolchain':'leanprover/lean4:v4.33.1','workers':1,'memory_mib':768,'elapsed_seconds':time.monotonic()-started,
 'explicit_declarations':len(names),'theorems':len(re.findall(r'^theorem\s+',MODEL.read_text(),re.M)),
 'declaration_names':names,'axioms':sorted(found),
 'prerequisites':['Exact sparse-key permutation/support/uniqueness','Unchanged ordered bucket streams and headers','Same pure native pack/protection/limit emitter','No result before reference-cap fallback check'],
 'inputs':{p.name:sha(p) for p in [MODEL,NOTE,ROOT/'README.md',Path(__file__).resolve()]},
 'audit_sha256':sha(OUT/'Audit.log'),'compile_sha256':sha(OUT/'Compile.log')}
(ROOT/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({key:receipt[key] for key in ['status','explicit_declarations','theorems','axioms','elapsed_seconds']}))
