#!/usr/bin/env python3
"""Copy or check the exact shared TR14 import closure and canonical exports.

Source identity is a reproducibility check, not a substitute for Lean or the
isolated Linux Comparator/kernel verification.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

REPO = Path(__file__).resolve().parents[4]
SOURCE = REPO / 'lean-statements'
PROJECT = REPO / 'tensor-computations/TR-14/lean'
ENTRY = 'NLA.Proofs.TR14.Final'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write', action='store_true', help='Write exact copies and regenerate their hash lock; default only checks')
args = parser.parse_args()

def sha(data):
    return hashlib.sha256(data).hexdigest()

ordered = []
visiting = set()
seen = set()

def visit(module):
    if module in visiting:
        raise RuntimeError('Local import cycle: ' + module)
    if module in seen:
        return
    path = SOURCE / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        raise RuntimeError('Missing local source: ' + module)
    visiting.add(module)
    imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', path.read_text(), re.M)
    for name in imports:
        if name.startswith(('NLA.', 'Reviewed.')):
            visit(name)
    visiting.remove(module)
    seen.add(module)
    ordered.append((module, path, imports))

visit(ENTRY)
copies = []
for module, source, imports in ordered:
    relative = Path(module.replace('.', '/') + '.lean')
    target = PROJECT / relative
    if args.write:
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    if not target.is_file() or source.read_bytes() != target.read_bytes():
        raise RuntimeError('Canonical source differs: ' + str(relative))
    copies.append({'module': module, 'source': str(source.relative_to(REPO)),
                   'destination': str(target.relative_to(REPO)),
                   'source_sha256': sha(source.read_bytes()),
                   'destination_sha256': sha(target.read_bytes()), 'imports': imports})
exports = ['Challenge.lean', 'Solution.lean', 'Identity.lean', 'Reviewed/TR14.lean',
           'comparator.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
lock = {'date': '2026-10-18', 'phase': 'complete-copied-proof-pending-linux',
        'source_root': 'lean-statements', 'package_root': str(PROJECT.relative_to(REPO)),
        'topological_module_count': len(copies),
        'proof_module_count': sum(x['module'].startswith('NLA.Proofs.TR14.') for x in copies),
        'entry': ENTRY, 'export': 'NLA.TR14.target', 'copies': copies,
        'package_exports': {name: sha((PROJECT / name).read_bytes()) for name in exports},
        'note': 'Exact-copy and reviewed export lock only. Generic Linux verification independently snapshots all committed project inputs; authoritative TR14 Linux acceptance is pending.',
        'locked_scope': 'Copied Lean import closure and the explicit package exports above.',
        'unlocked_scope': 'README, metadata, review reports, check scripts and evidence are separate; no entire-package hash claim.'}
path = PROJECT / 'proof-source-lock.json'
if args.write:
    path.write_text(json.dumps(lock, indent=2) + '\n')
else:
    if json.loads(path.read_text()) != lock:
        raise RuntimeError('Canonical proof-source lock differs from current exact sources/exports')
print(json.dumps({'passed': True, 'mode': 'write' if args.write else 'check',
                  'actual_source_copies': len(copies), 'proof_modules': lock['proof_module_count'],
                  'explicit_exports': len(exports)}))
