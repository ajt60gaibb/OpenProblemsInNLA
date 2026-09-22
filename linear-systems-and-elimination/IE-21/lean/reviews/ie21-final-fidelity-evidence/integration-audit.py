#!/usr/bin/env python3
"""Independent exact-parent integration check; no proof or source changes."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parent;P=R.parents[1];ROOT=P.parents[2]
HEAD='baf14a2dd15b7842f27d57198a483def8347f9b9'
IE='c445ad291e9046be5ee43bc5780fceab854c5469'
TR='28efcc2eed621b1b7662f71deac670f96b8ed298'
VERIFIED='1eb284b84ecc0d3c958d022b3e020be7fa111391'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def blob(c,n):return git('show',c+':'+n)
def tree(c,p):
 result={}
 for x in git('ls-tree','-r','-z',c,'--',p).split(b'\0'):
  if x:
   m,n=x.split(b'\t');mode,kind,obj=m.split();assert kind==b'blob' and mode in [b'100644',b'100755'];result[n.decode()]=(mode.decode(),obj.decode())
 return result
assert git('rev-parse',HEAD+'^1').decode().strip()==IE and git('rev-parse',HEAD+'^2').decode().strip()==TR
assert subprocess.run(['git','merge-base','--is-ancestor',VERIFIED,HEAD],cwd=ROOT).returncode==0
print('PASS exact reviewed merge parents and retained verified IE21 ancestor')
for ref,prefix,count in [(IE,'linear-systems-and-elimination/IE-21',669),(TR,'tensor-computations/TR-27',320)]:
 old=tree(ref,prefix);current=tree(HEAD,prefix);assert len(old)==count
 for n,record in old.items():
  assert current[n]==record,n
  assert (ROOT/n).read_bytes()==blob(ref,n),n
 print('PASS all',count,prefix,'files and modes unchanged from reviewed parent and matching current working files')
changed=git('diff','--name-only',TR,HEAD).decode().splitlines()
extras=[n for n in changed if not n.startswith('linear-systems-and-elimination/IE-21/')]
assert set(extras)=={'CATALOG.md','README.md','linear-systems-and-elimination/README.md','tools/render_problems.py'},extras
for n in ['CATALOG.md','README.md','linear-systems-and-elimination/README.md']:
 before=blob(TR,n).decode();expect=before.replace('42 solved (published or independently audited); 64 solved with Lean verification.','41 solved (published or independently audited); 65 solved with Lean verification.')
 expect=''.join(line.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if '[IE-21]' in line else line for line in expect.splitlines(keepends=True))
 assert (ROOT/n).read_text()==expect
renderer=blob(TR,'tools/render_problems.py').decode().replace('"IE-14", "IV-03"','"IE-14", "IE-21", "IV-03"').replace('{"SP-11", "SP-12"}','{"IE-21", "SP-11", "SP-12"}')
assert renderer==(ROOT/'tools/render_problems.py').read_text()
assert blob(IE,'problem_ids.json')==blob(TR,'problem_ids.json')==(ROOT/'problem_ids.json').read_bytes()
print('PASS PR-base diff limited to IE21, cumulative summaries/category row and two IE21 renderer memberships; registry unchanged')
registry=json.loads((ROOT/'problem_ids.json').read_text());counts={}
for n in registry.values():
 text=(ROOT/n).read_text();m=re.search(r'^\*\*Status:\*\* (.+)$',text,re.M);assert m,n
 status=m[1].strip();counts[status]=counts.get(status,0)+1
assert counts=={'Lean verified':65,'Partially resolved':70,'Solved':41,'Open':41},counts
print('PASS independently counted217canonical entries:65Leanverified,41Solved,70Partiallyresolved,41Open')
receipt=json.loads((R/'publication-receipt.json').read_text())
for n,h in receipt['publication_file_sha256'].items():
 if n not in {'README.md','CATALOG.md','tools/render_problems.py'}:assert sha((ROOT/n).read_bytes())==h,n
assert sha((ROOT/'linear-systems-and-elimination/IE-21/problem.pdf').read_bytes())=='79bba1583e7cf9ca8282a671defd5d960b910004e24b4959ce6f888458c3ea90'
for n,h in receipt['prior_evidence_sha256'].items():assert sha((R/n).read_bytes())==h,n
assert sha((R/'publication-review.md').read_bytes())=='657fee3b5b0cce5cca075839f4ae7083387466d85b1317c7262f4562d2a28444'
assert sha((R/'publication-receipt.json').read_bytes())=='e354c2dfa8a2af62789ba0522807be26e2f60dd5e5d7e54e6e038f7725c96b53'
print('PASS unchanged IE21 canonical,metadata,PDF/TeX,prior review receipts and verified evidence')
print('RESULT: PASS independent bounded integration audit; no new mathematical verification or remote merge')
