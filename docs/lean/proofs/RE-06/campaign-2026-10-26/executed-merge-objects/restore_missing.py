#!/usr/bin/env python3
"""Validate archived executed merge records; optionally restore missing Git objects, never refs."""
import argparse,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--restore',action='store_true');a=p.parse_args();base=Path(__file__).resolve().parent
for e in json.loads((base/'MANIFEST.json').read_text())['entries']:
 b=(base/e['path']).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'];assert hashlib.sha1(b'commit '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_commit']
 exists=subprocess.run(['git','cat-file','-e',e['git_commit']],cwd=a.repo,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0
 if not exists and a.restore:
  result=subprocess.check_output(['git','hash-object','-t','commit','-w','--stdin'],cwd=a.repo,input=b).decode().strip();assert result==e['git_commit'];exists=True
 if exists:assert subprocess.check_output(['git','cat-file','commit',e['git_commit']],cwd=a.repo)==b
 assert subprocess.check_output(['git','rev-parse',e['source_head']+'^{tree}'],cwd=a.repo,text=True).strip()==e['tree']
 print(e['git_commit'],'validated', 'present' if exists else 'missing; use --restore to rebuild this exact commit object')
