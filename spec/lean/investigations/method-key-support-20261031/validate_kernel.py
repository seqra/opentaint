#!/usr/bin/env python3
"""Bounded direct Lean validation. No Gradle, analyzer, or repository build."""
from pathlib import Path
import os, subprocess, json, hashlib, time, resource, re
ROOT=Path(__file__).resolve().parent
LEAN=Path('/home/sobol/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
source=(ROOT/'MethodSupport.lean').read_text()
for forbidden in [r'^axiom\s',r'\bsorry\b',r'\bnoncomputable\b',r'\bclassical\b']:
    assert not re.search(forbidden,source,re.M),forbidden
commands=[
 ['--version'],
 ['-M2048','-o','MethodSupport.olean','MethodSupport.lean'],
 ['-M2048','Audit.lean'],
]
receipt={'scope':'Constructive finite support kernel and executable ZERO seed protocol only; no production/project/Gradle run.','timeoutSecondsPerCommand':60,'memoryCapMiB':2048,'commands':[]}
env=dict(os.environ);env['LEAN_PATH']=str(ROOT)
for i,args in enumerate(commands):
    started=time.time()
    result=subprocess.run([str(LEAN)]+args,cwd=str(ROOT),env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,universal_newlines=True,timeout=60)
    logname=['lean-version.log','kernel-compile.log','kernel-audit.log'][i]
    (ROOT/logname).write_text(result.stdout)
    receipt['commands'].append({'argv':[str(LEAN)]+args,'cwd':str(ROOT),'exitCode':result.returncode,'elapsedSeconds':time.time()-started,'output':result.stdout,'log':logname})
    assert result.returncode==0,result.stdout
assert 'version 4.33.1' in receipt['commands'][0]['output']
audit=receipt['commands'][2]['output']
match=re.search(r'Audited (\d+) MethodSupport declarations, including (\d+) theorem declarations; (\d+) have unexpected axioms',audit)
assert match and int(match[3])==0
assert 'Classical.choice' not in audit and 'sorryAx' not in audit
assert 'Chain 1000: incoming support 1; nonzero initial support 0; seeded outgoing support 1000; unseeded outgoing support 0.' in audit
receipt.update({'auditedDeclarations':int(match[1]),'auditedTheoremDeclarationsIncludingGenerated':int(match[2]),'explicitTheorems':len(re.findall(r'^theorem ',source,re.M)),'unexpectedAxioms':0,'transitiveAxiomUnion':['propext','Quot.sound'],'maxChildPeakRssKiB':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'allCommandsPassed':True})
receipt['files']={name:{'bytes':(ROOT/name).stat().st_size,'sha256':digest(ROOT/name)} for name in ['MethodSupport.lean','Audit.lean','validate_kernel.py','lean-version.log','kernel-compile.log','kernel-audit.log']}
(ROOT/'kernel-validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['commands','files']},indent=2))
