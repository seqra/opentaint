"""Check the portable, constructive local STAR_OR_ANY model. No native jobs."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent.parent
MODULES = [
    ('RestrictedInitialPolicy', '3a42cc1eb3209c82400ba528bdb1e80ba17bc09540e19e59b0d5272f9fd7c5f0'),
    ('MayInitialToStarAuditRootChecked', 'afe6f23f44a937bda291f0444476737e418a1fee574d597b9cb3cf7bbdb6a0c4'),
    ('SelectedFullAdmissionProofFixed', 'c8e7c2bd1c79039991f2918ca4cbccca88b7787a25261d414704373af987785b'),
    ('StarOrAnyDesignProofFixed', '705d2f474e039c517f8f33b4e7ffdec5af6436bd590e437a0df56392b4e4442c'),
    ('StarOrAnyObligationsProofFixed', 'b63650cb76f437b668028a42f93b50b00a30130c857d73c7fbb3f4bd575a1cb2'),
    ('PublicDemandHandoffCounterexample', 'ecb79a5ddda53f35de7c086bd20d679303c387eb26cc98a00d06a2e3f50317e1'),
    ('StaticCarryC5Preimage', '78bb7d9ed219902ef605d900f85845d9045902897c464ed13152061cbee0c800'),
    ('SavedRepeatObserverCountermodelProofFixed', 'f8e2065c4b70f0af788f7fbeb1dead8025a03148c496195d91428bf9d944cb48'),
]

def check_pins():
    for module, expected in MODULES:
        assert hashlib.sha256((HERE / (module + '.lean')).read_bytes()).hexdigest() == expected, module

check_pins()
outputs = []
with tempfile.TemporaryDirectory(prefix='portable-star-or-any-') as directory:
    env = dict(os.environ)
    env['LEAN_PATH'] = directory + os.pathsep + env.get('LEAN_PATH', '')
    for module, _ in MODULES:
        source = HERE / (module + '.lean')
        code = re.sub(r'/\-.*?\-/', '', source.read_text(), flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b|\b(?:sorry|admit|Classical)\b', code, re.M)
        result = subprocess.run(
            ['lake', 'env', 'lean', '--root=' + str(HERE), '-M2048',
             '-o', str(Path(directory) / (module + '.olean')), str(source)],
            cwd=LEAN, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(result.stdout, end='', flush=True)
        assert result.returncode == 0 and 'error:' not in result.stdout and 'sorryAx' not in result.stdout, module
        outputs.append(result.stdout)

check_pins()
audits = []
for name, dependencies in re.findall(
    r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", '\n'.join(outputs), re.S
):
    used = sorted(filter(None, dependencies.replace('\n', '').replace(' ', '').split(',')))
    assert set(used) <= {'propext', 'Quot.sound'}, (name, used)
    audits.append(dict(theorem=name, axioms=used))
for name in re.findall(r"'([^']+)' does not depend on any axioms", '\n'.join(outputs)):
    audits.append(dict(theorem=name, axioms=[]))
groups = [
    ('StarOrAnyDesignProofFixed', 'StarOrAnyDesign', 29, 'STAR_OR_ANY_DESIGN'),
    ('StarOrAnyObligationsProofFixed', 'StarOrAnyObligations', 10, 'STAR_OR_ANY_OBLIGATIONS'),
]
adapter_groups = [
    ('StaticCarryC5Preimage', 'StaticCarryC5Preimage', 13, 'STATIC_CARRY_C5_PREIMAGE'),
]
counterexample_groups = [
    ('PublicDemandHandoffCounterexample', 'StarOrAnyPublicHandoff', 8, 'SOA_PUBLIC_HANDOFF_COUNTEREXAMPLE'),
    ('SavedRepeatObserverCountermodelProofFixed', 'SavedRepeatObserverCountermodel', 9, 'SECOND_DEEP_SAVED_REPEAT_COUNTERMODEL'),
]
selected = []
adapters = []
counterexamples = []
for module, namespace, count, marker in groups + adapter_groups + counterexample_groups:
    source = (HERE / (module + '.lean')).read_text()
    names = re.findall(r'^(?:@\[simp\] )?theorem (\w+)', source, re.M)
    assert len(names) == count and len(set(names)) == count
    assert names == re.findall(r'^#print axioms (\w+)', source, re.M)
    group = [item for item in audits if item['theorem'].startswith(namespace + '.')]
    assert len(group) == count
    assert {item['theorem'] for item in group} == {namespace + '.' + name for name in names}
    output = outputs[[name for name, _ in MODULES].index(module)]
    assert marker + '=true' in output and marker + '=false' not in output
    if namespace in {'StarOrAnyPublicHandoff', 'SavedRepeatObserverCountermodel'}:
        counterexamples.extend(group)
    elif namespace == 'StaticCarryC5Preimage':
        adapters.extend(group)
    else:
        selected.extend(group)
assert len(selected) == 39 and len(adapters) == 13 and len(counterexamples) == 17
print(json.dumps(dict(
    state='PASS_LOCAL_STAR_OR_ANY_ADAPTER_AND_CONDITIONAL_COUNTEREXAMPLES', checkedNewLaws=39,
    checkedDesignLaws=39, checkedAdapterLaws=13, checkedPositiveLocalLaws=52,
    checkedCounterexampleLaws=17, totalAuditedLaws=69,
    checkedLawGroups={namespace: count for _, namespace, count, _ in groups},
    adapterLawGroups={namespace: count for _, namespace, count, _ in adapter_groups},
    counterexampleLawGroups={namespace: count for _, namespace, count, _ in counterexample_groups},
    modelPins=dict(MODULES), newLawAxiomAudit=selected,
    adapterAxiomAudit=adapters,
    counterexampleAxiomAudit=counterexamples,
    scope=['Finite ordinary counted-field template image; STAR geometry/erasure; local marker transport and arbitrary wrapper-count induction.',
           'Normalized ND-member deduplication preserves conjunction of STAR-geometric predicates.',
           'Every bounded earlier Empty-E MAY cut gives the same SOA joint seed/layer and unchanged complete label.',
           'A separate literal pattern/layer/H capability frontier preserves supplied SOA C2 effects in both arrival orders, independent of opaque DATA work.'],
    adapterScope='C5-only same-slot carry query uses an existing MAY pair only after unchanged canStore permission; saturated static-field projection, output-restriction equality and supplied N/D/mark/H frame.',
    counterexampleScopes=[
        'Singleton concrete SOA/DEMAND publication normalizes both P/C to STAR; backward-to-forward handoff then rejects a run-3 child EXACT/NORMAL actual that the old MAY demand admits.',
        'Conditional second-Deep case: three scenario-empty families drop a ZERO-origin f^3 exact/NORMAL offer, while a supplied saved NORMAL repeat row has a finite nongrowing f^2->f->root replay. Native eligibility and routing are not proved.'],
    counterexampleIsPolicyRepair=False, globalSoundnessProved=False,
    notProved=['Native adapter equivalence and full legal-input completeness',
               'Arbitrary static/GROUP/mx/E/noncounted/ZERO adapters',
               'Complete C5 and native ND/Target boundary adapters',
               'Native loop trial/certificate equality and packed/scalar point freshness',
               'Producer arrival, mixed-header adapters and whole-pipeline capability transport',
               'Whole-program recovery, global source/sink soundness, progress or project performance'],
), indent=2))
