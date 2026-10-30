#!/usr/bin/env python3
"""Read-only byte/source audit of the RE-06 seal; kernel acceptance is separate archived evidence."""
import argparse,collections,hashlib,json,re,subprocess
from pathlib import Path,PurePosixPath
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--expected-seal-sha256');a=p.parse_args();repo=a.repo.resolve();base=Path(__file__).resolve().parent;seal_path=base/'FINAL_EVIDENCE_SEAL.json';raw=seal_path.read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest()
if a.expected_seal_sha256:assert sha(raw)==a.expected_seal_sha256
s=json.loads(raw);git=lambda *args:subprocess.check_output(['git',*args],cwd=repo);read=lambda ref,q:git('show',ref+':'+q)
for group in ['canonical_files','evidence_files']:
 for e in s[group]:
  q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts;f=repo/q;assert not f.is_symlink();b=f.read_bytes();assert sha(b)==e['sha256'] and len(b)==e['bytes'],str(q)
  if group=='canonical_files':assert b==read(s['accepted_input_ref'],str(q))
project=s['canonical_project'];actual={str(q.relative_to(repo)) for q in (repo/project).rglob('*') if q.is_file() and not any(x in ['.lake','.git'] for x in q.relative_to(repo/project).parts)};assert actual=={e['path'] for e in s['canonical_files']}
proof=repo/s['evidence_root'];actual={str(q.relative_to(repo)) for q in proof.rglob('*') if q.is_file()};assert actual=={e['path'] for e in s['evidence_files']}|{str(seal_path.relative_to(repo))}
for e in s['source_files']:
 b=read(s['proof_source_ref'],e['path']);assert sha(b)==e['sha256'] and len(b)==e['bytes'];assert b==read(s['accepted_input_ref'],e['path']);assert b==(repo/project/e['path'].removeprefix('lean-statements/')).read_bytes()
old=json.loads(read(s['accepted_input_ref'],'problem_ids.json'));current=json.loads((repo/'problem_ids.json').read_text());assert len(old)==217 and all(current[k]==v for k,v in old.items());assert sha(read(s['accepted_input_ref'],'problem_ids.json'))==s['registry_sha256']
counts=collections.Counter()
for q in old.values():
 m=re.search(r'(?m)^\*\*Status:\*\*\s*([^\n]+)',read(s['accepted_input_ref'],q).decode());assert m;counts[m.group(1).strip()]+=1
assert dict(counts)==s['catalog_at_accepted_input_ref']
print('PASS:',len(s['canonical_files']),'canonical inputs,',len(s['evidence_files']),'evidence files,',len(s['source_files']),'source bindings; registry217 and historical catalog verified. No Lean/Comparator execution claimed.')
