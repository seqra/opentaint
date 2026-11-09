#!/usr/bin/env python3
"""Bind the small detail report to a heap's existing owner CSV; does not run MAT."""
import argparse
import csv
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--owners', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
parser.add_argument('--template', type=Path, default=Path(__file__).resolve().with_name('bidi-memory-detail.xml'))
parser.add_argument('--entries-address')
parser.add_argument('--forms-address')
parser.add_argument('--rule-statement-address')
args = parser.parse_args()
with args.owners.open() as stream:
    rows = list(csv.DictReader(stream))

def pick(name, explicit):
    if explicit is not None:
        value = explicit
    else:
        matches = [row for row in rows if row.get('ownerClass') == name]
        if not matches:
            parser.error('No >=1 MiB owner row for ' + name + '; supply its explicit address after the complete form inventory')
        value = max(matches, key=lambda row: int(row['retainedBytes']))['address']
    if not re.fullmatch(r'0x[0-9a-fA-F]+', value):
        parser.error('Invalid heap address ' + value)
    return value

entries = pick('org.opentaint.dataflow.jvm.bidi.interp.JIRMethodEntries', args.entries_address)
forms = pick('org.opentaint.dataflow.jvm.bidi.interp.JIRMethodForms', args.forms_address)
text = args.template.read_text()
text = text.replace('0x6a15fccd8', entries).replace('0x7c7bf8158', forms)
if '__RULE_STATEMENT_ADDRESS__' in text:
    statement = pick('org.opentaint.dataflow.bidi.interp.RuleStatement', args.rule_statement_address)
    text = text.replace('__RULE_STATEMENT_ADDRESS__', statement)
# Select this method-context owner's call-plan cache, not the largest cache of a
# different kind (e.g. JIRMethodEntry.statements). This subquery passed the mock.
cache = '(SELECT OBJECTS f.plans FROM OBJECTS ' + forms + ' f)'
text = text.replace('0x7c7bf8178', cache)
text = text.replace('path2gc ' + cache + ' -numberofpaths 5',
                    'path2gc SELECT OBJECTS f.plans FROM OBJECTS ' + forms + ' f; -numberofpaths 5')
text = text.replace('OWASP cached call-plan detail', 'Heap-bound cached call-plan detail')
text = text.replace('Targeted report for OWASP guard-live.hprof captured on 2026-10-12.',
                    'Targeted report bound to owner CSV: ' + str(args.owners))
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(text)
print(json.dumps({'report': str(args.output), 'owners': str(args.owners),
                  'entries': entries, 'methodForms': forms,
                  'callCache': cache, 'sha256': hashlib.sha256(text.encode()).hexdigest()}, indent=2))
