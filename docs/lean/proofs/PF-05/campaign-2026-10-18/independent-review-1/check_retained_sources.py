#!/usr/bin/env python3
"""Verify the immutable PF05 preproof snapshot; optionally check original Git objects."""
import argparse,hashlib,json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--git-source',type=Path,help='Read-only object store with the retained candidate commit')
args=parser.parse_args()
r=json.loads((root/'input-inventory.json').read_text());records=[]
for item in r['files']:
 data=(root/'sources'/item['path']).read_bytes()
 passed=hashlib.sha256(data).hexdigest()==item['sha256'] and len(data)==item['size']
 if args.git_source:
  original=subprocess.check_output(['git','show',r['candidate_revision']+':'+item['path']],cwd=args.git_source)
  passed=passed and original==data
 records.append({'path':item['path'],'passed':passed})
result={'reviewer':'/root/solved_inventory (AI agent)','candidate_revision':r['candidate_revision'],'git_source':str(args.git_source) if args.git_source else None,'scope':'Immutable reviewed input snapshot identity only','files':records,'passed':all(x['passed'] for x in records)}
(root/'retained-source-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'files':len(records)}))
raise SystemExit(0 if result['passed'] else 1)
