#!/usr/bin/env python3
"""Check identity storage, owner visibility and protected admission models only."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
MODULES = ['IdentityCells', 'ProtectionAdmission', 'OwnerVisibility']
ALLOWED_AXIOMS = {'propext', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def limited_child():
    if hasattr(os, 'sched_getaffinity') and hasattr(os, 'sched_setaffinity'):
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    if hasattr(os, 'nice'):
        os.nice(10)


def uncomment(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; i += 2
            elif source.startswith('-/', i): depth -= 1; i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('/-', i): depth = 1; i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else: out.append(source[i]); i += 1
    if depth: raise RuntimeError('Unclosed Lean comment')
    return ''.join(out)


def declarations(source):
    stack, found, theorem_count = [], [], 0
    for line in uncomment(source).splitlines():
        begin = re.match(r'^\s*(namespace|section)\s*([\w.]*)', line)
        if begin:
            stack.append(begin.group(2) if begin.group(1) == 'namespace' else '')
            continue
        if re.match(r'^\s*end(?:\s|$)', line):
            if not stack: raise RuntimeError('Unexpected namespace end: '+line)
            stack.pop(); continue
        match = re.match(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|def|abbrev)\s+([\w.]+)', line)
        if match and not re.match(r'^\s*private\b', line):
            prefix = '.'.join(x for x in stack if x)
            found.append((prefix+'.' if prefix else '')+match.group(2))
            theorem_count += match.group(1) == 'theorem'
    return found, theorem_count


def run(command, env, out, directory=HERE):
    start = time.monotonic()
    options = dict(cwd=directory, env=env, capture_output=True, text=True, timeout=90)
    if os.name == 'posix': options['preexec_fn'] = limited_child
    result = subprocess.run(command, **options)
    text = result.stdout + result.stderr
    out.write_text(text)
    return {'command':command, 'cwd':str(directory.relative_to(ROOT)), 'exitCode':result.returncode, 'wallSeconds':time.monotonic()-start,
            'log':str(out.relative_to(ROOT)), 'logSha256':sha(out)}, text


def main():
    if (ROOT/'spec/lean/lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise RuntimeError('Pinned toolchain changed')
    lean = shutil.which('lean')
    if lean is None: raise RuntimeError('lean is absent')
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], cwd=HERE, env=env, text=True).strip()
    if not re.search(r'\bversion 4\.33\.1\b', version): raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT/'spec/lean/.lake/verification/identity-owner-protection-20261030'/stamp
    (work/'ApSpec').mkdir(parents=True)
    env['LEAN_PATH'] = str(work)
    sources = [ROOT/'spec/lean/proposals/selected-work-20261030/CachedCfgDelivery.lean']+[HERE/(m+'.lean') for m in MODULES]
    source_hashes_before = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    expected, theorem_count = [], 0
    for source in sources:
        code = uncomment(source.read_text())
        if re.search(r'\b(?:sorry|noncomputable)\b|^\s*axiom\b', code, re.M):
            raise RuntimeError('Unproved or noncomputable declaration: '+str(source))
        names, count = declarations(source.read_text())
        expected.extend(names); theorem_count += count
    audit = '\n'.join(['import CachedCfgDelivery']+['import '+m for m in MODULES]+['']+
                      ['#print axioms '+name for name in expected])+'\n'
    (work/'Audit.lean').write_text(audit)
    runs=[]
    for source in sources:
        relative_module = Path(source.stem)
        command=[lean,'-j','1','-M','768','-o',str(work/relative_module.with_suffix('.olean')),str(source)]
        row, output=run(command,env,work/(source.stem+'.log'), source.parent);runs.append(row)
        if row['exitCode'] != 0: raise RuntimeError(output[-8000:])
    row, output=run([lean,'-j','1','-M','768',str(work/'Audit.lean')],env,work/'Audit.log',work);runs.append(row)
    actual=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",output))
    axioms=set()
    for dep in re.findall(r'depends on axioms: \[([^\]]*)\]',output):
        axioms.update(x.strip() for x in dep.split(',') if x.strip())
    checks={'allCommandsPass':all(r['exitCode']==0 for r in runs),
            'allPublicTheoremsAndDefinitionsAudited':actual==set(expected),
            'onlyAllowedKernelAxioms':axioms<=ALLOWED_AXIOMS,
            'noChoiceOrSorry':not ({'Classical.choice','sorryAx'} & axioms),
            'noUnprovedOrNoncomputableSource':True,
            'sourceBytesStableDuringCheck':source_hashes_before == {str(p.relative_to(ROOT)): sha(p) for p in sources},
            'noLeanSorryWarning':all("uses 'sorry'" not in (ROOT/r['log']).read_text() for r in runs)}
    runtime=ROOT/'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi'
    bindings={str((runtime/p).relative_to(ROOT)):sha(runtime/p) for p in [
        'store/MethodEdges.kt','store/FrozenOwnerVisibility.kt','store/StaticGuidance.kt','store/StaticEntryLookup.kt',
        'store/StaticPairLookup.kt','store/C5StaticDemandView.kt','store/StaticSelectorIndex.kt',
        'ap/LiteralInitialImage.kt','ap/Groups.kt','ap/Conclusions.kt','ap/FlowBackedProtection.kt','ap/TrieOps.kt',
        'ap/Trie.kt','ap/Facts.kt','ap/Premise.kt','ap/ApManager.kt',
        'engine/RunMethodAnalyzer.kt','driver/IterationDriver.kt']}
    proposal=ROOT/'docs/design/bidirectional-identity-owner-protection-implementation-20261030.md'
    receipt={'status':'PASS' if all(checks.values()) else 'FAILED','runtimeVerifiedByThisChecker':False,
             'baseRuntime':'c98d12582a138d5898e94908ee6690dda73998ca',
             'proposalSha256':sha(proposal) if proposal.exists() else None,
             'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'toolchain':TOOLCHAIN,
             'leanVersion':version,'moduleSourceHashes':{str(p.relative_to(ROOT)):sha(p) for p in sources},
             'checkerSha256':sha(Path(__file__)),'theoremCount':theorem_count,
             'auditedDeclarationCount':len(expected),'auditedDeclarations':expected,
             'axiomDependencies':sorted(axioms),'checks':checks,'runs':runs,'runtimeSourceHashes':bindings,
             'scope':'Constructive identity state/delta and promotion kernels, finite graph path and certified quotient/DAG visibility, and exact-coordinate protection admission. Kotlin SCC extraction, AP recognition and runtime tests are separate implementation obligations.'}
    (HERE/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','theoremCount','auditedDeclarationCount','axiomDependencies','checks']},indent=2))
    if not all(checks.values()): raise SystemExit(1)

if __name__=='__main__': main()
