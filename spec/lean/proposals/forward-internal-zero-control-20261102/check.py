#!/usr/bin/env python3
"""Check the UNSELECTED conditional model. This is not a production source gate."""
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if(p/'spec/lean/lean-toolchain').is_file())
TOOLCHAIN='leanprover/lean4:v4.33.1'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
 scanner_path=ROOT/'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
 spec=importlib.util.spec_from_file_location('zero_candidate_scanner',scanner_path)
 scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
 source=HERE/'Control.lean';draft=ROOT/'spec/forward-internal-zero-control.md'
 assert 'DRAFT / UNSELECTED' in draft.read_text(),'A behavior decision needs an explicit proof-scope review'
 pins=json.loads((HERE/'reference-source-pins.json').read_text())
 assert pins['candidateRuntimeImplemented']is False and pins['productionVerified']is False
 for name,expected in pins['sources'].items():
  assert sha(ROOT/name)==expected,'Reference source changed; review and refresh explicitly: '+name
 clean=scanner.uncomment(source.read_text())
 assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b',clean)
 assert re.findall(r'^import\s+(\S+)',clean,re.M)==['Std']
 declarations,count=scanner.declarations(source.read_text())
 inputs=[source,draft,HERE/'README.md',HERE/'check.py',HERE/'reference-source-pins.json',
         ROOT/'spec/proof-guide.md',ROOT/'spec/lean/lean-toolchain',scanner_path]+[ROOT/name for name in pins['sources']]
 before={str(p.relative_to(ROOT)):sha(p)for p in inputs}
 assert (ROOT/'spec/lean/lean-toolchain').read_text().strip()==TOOLCHAIN
 lean=shutil.which('lean');assert lean
 env=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN)
 version=subprocess.check_output([lean,'--version'],text=True,env=env).strip();assert re.search(r'version 4\.33\.1\b',version)
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 work=ROOT/'spec/lean/.lake/verification/forward-internal-zero-control-20261102'/stamp;work.mkdir(parents=True)
 env['LEAN_PATH']=str(work)
 def one_cpu():
  if hasattr(os,'sched_getaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 def run(command,name,cwd):
  result=subprocess.run(command,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                        timeout=90,preexec_fn=one_cpu)
  (work/name).write_text(result.stdout)
  assert result.returncode==0 and not re.search(r'\b(?:warning|error):',result.stdout),result.stdout
  return result.stdout
 run([lean,'-j','1','-M','768','-o',str(work/'Control.olean'),str(source)],'Control.log',HERE)
 audit=work/'Audit.lean';audit.write_text('import Control\n'+''.join('#print axioms '+name+'\n'for name in declarations))
 output=run([lean,'-j','1','-M','768',str(audit)],'Audit.log',work)
 actual=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",output));assert actual==set(declarations)
 axioms=set()
 for group in re.findall(r'depends on axioms: \[([^\]]*)\]',output):axioms.update(p.strip()for p in group.split(',')if p.strip())
 assert axioms<={'propext','Quot.sound'}
 (HERE/'audit.txt').write_text(output)
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in inputs},'Inputs changed during the check'
 receipt=dict(status='CONDITIONAL_MODEL_PASS',selection='DRAFT_UNSELECTED',candidateRuntimeImplemented=False,
  productionVerifiedByKernel=False,fullAPAdapterVerified=False,wholeDriverConvergenceProved=False,projectSpeedupMeasured=False,
  utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),toolchain=TOOLCHAIN,leanVersion=version,
  moduleCount=1,theoremCount=count,auditedPublicDeclarationCount=len(declarations),declarations=declarations,
  axioms=sorted(axioms),allExplicitPublicDefinitionsAndTheoremsAudited=True,noChoiceOrUnprovedAxioms=True,
  inputsStable=True,inputHashes=before,referenceSourceRole=pins['sourceRole'],
  portableAudit=dict(path=str((HERE/'audit.txt').relative_to(ROOT)),sha256=sha(HERE/'audit.txt')),
  logs={str((work/name).relative_to(ROOT)):sha(work/name)for name in ['Control.log','Audit.lean','Audit.log']},
  limits=['Current source pins are reference snapshots, not implementation/native evidence.',
   'Type-valued paths and supplied exact parent interfaces are checked; Kotlin CFG/binding extraction is not.',
   'Ordinary AP lookup is opaque; finite endpoint cells cover only the ZERO/Target probe hazard.',
   'The replay model covers one exact cell/link, not all packed relations or current scheduling code.',
   'Source action evaluation and complete AP ND matching/layer correspondence need native tests.',
   'Control-cache invariants do not imply equality of final AP stores or a bound on all rule work.'])
 (HERE/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({key:receipt[key]for key in ['status','selection','moduleCount','theoremCount','auditedPublicDeclarationCount','axioms','inputsStable']},indent=2))

if __name__=='__main__':main()
