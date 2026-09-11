#!/usr/bin/env python3
"""Check the packaged manifest before rerunning tests or rebuilding documents."""
from __future__ import annotations
import hashlib,json
from pathlib import Path
from create_manifest import ROOT,files

def main():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    expected=set();errors=[]
    for entry in manifest['files']:
        relative=Path(entry['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise RuntimeError('Unsafe path in manifest')
        expected.add(relative.as_posix());p=ROOT/relative
        if not p.is_file():
            errors.append('Missing: '+str(relative));continue
        data=p.read_bytes()
        if len(data)!=entry['bytes'] or hashlib.sha256(data).hexdigest()!=entry['sha256']:
            errors.append('Changed: '+str(relative))
    actual={p.relative_to(ROOT).as_posix() for p in files()}
    for name in sorted(actual-expected-{'MANIFEST.json'}): errors.append('Unlisted: '+name)
    if errors: raise RuntimeError('\n'.join(errors))
    print(f'Integrity PASS: {len(expected)} files match their recorded SHA-256 hashes.')
    print('This verifies file integrity, not mathematical validity or provenance.')

if __name__=='__main__': main()
