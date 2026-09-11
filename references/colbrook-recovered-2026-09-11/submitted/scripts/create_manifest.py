#!/usr/bin/env python3
"""Regenerate a SHA-256 inventory after intentional edits to the package."""
from __future__ import annotations
import hashlib,json
from datetime import datetime,timezone
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
IGNORED={'.build','__pycache__','.git'}

def files():
    return sorted(p for p in ROOT.rglob('*') if p.is_file()
                  and not any(part in IGNORED for part in p.relative_to(ROOT).parts)
                  and p.suffix not in {'.pyc','.pyo'})

def record(p:Path)->dict:
    data=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(data),
            'sha256':hashlib.sha256(data).hexdigest()}

def main():
    entries=[record(p) for p in files() if p.name not in {'MANIFEST.json','SHA256SUMS.txt'}]
    checksum=ROOT/'SHA256SUMS.txt'
    checksum.write_text(''.join(e['sha256']+'  '+e['path']+'\n' for e in entries),encoding='utf-8')
    entries.append(record(checksum))
    manifest={'created_utc':datetime.now(timezone.utc).isoformat(),
              'package':'OpenProblemsInNLA_recovered','kind':'Reconstructed candidate proof and review package',
              'verification_scope':'Six exact-certificate groups plus a separate finite rook example; row-deletion arguments are analytic drafts.',
              'inventory_excludes':['MANIFEST.json','.build/','__pycache__/','.git/'],
              'files':sorted(entries,key=lambda e:e['path'])}
    (ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(f'Manifest written: {len(entries)} hashed files plus MANIFEST.json.')

if __name__=='__main__': main()
