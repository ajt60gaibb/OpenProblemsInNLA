#!/usr/bin/env python3
"""Independent publication delta audit; no new mathematical verification."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parent;P=R.parents[1];ROOT=P.parents[2];E=P/'verification/linux'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
PUB='1eb284b84ecc0d3c958d022b3e020be7fa111391'
def old(n):return subprocess.check_output(['git','show',PUB+':'+n],cwd=ROOT)
def check(s):print('PASS '+s)
inputs=read(E/'input-receipt.json')['input_sha256'];changes={n:{'verified_sha256':h,'publication_sha256':sha(P/n)} for n,h in inputs.items() if sha(P/n)!=h}
assert len(inputs)==289 and set(changes)=={'README.md','formalization.yaml'}
root=read(P/'reviews/publication/root-correspondence.json');assert root['changed_original_inputs']==changes
assert root['unchanged_original_input_count']==287
for n,h in read(P/'reviews/statement-freeze.json')['mathematical_boundary_sha256'].items():assert sha(P/n)==h
check('only README/metadata differ among289 verified inputs; all mathematical, preproof, build and Comparator bytes unchanged')
name='linear-systems-and-elimination/IE-21/README.md';c=(ROOT/name).read_text();o=old(name).decode();marker='## Problem statement\n'
assert o.split(marker,1)[1]==c.split(marker,1)[1]
old_prefix=o.split(marker,1)[0].replace('**Status:** Solved\n','**Status:** Lean verified  \n').replace('**Last checked:** 2026-09-11','**Last checked:** 2026-09-22')
assert c.startswith(old_prefix)
new_notice=c[len(old_prefix):].split(marker,1)[0];assert new_notice.startswith('## Lean proof and verification evidence - 2026-09-22')
assert sha(ROOT/name)==root['canonical_sha256']
assert (ROOT/'problem_ids.json').read_bytes()==old('problem_ids.json')
assert read(ROOT/'problem_ids.json')['IE-21']==name
check('permanent ID/path/registry, entire original problem statement and following history preserved; preceding resolution notice unchanged')
for p in [ROOT/name,P/'README.md']:
 for label,target in re.findall(r'\[([^]]+)\]\(([^)]+)\)',p.read_text()):
  if '://' not in target and not target.startswith('#'):assert (p.parent/target).is_file(),target
for text in [new_notice,(P/'README.md').read_text(),(P/'formalization.yaml').read_text()]:
 assert 'George Stepaniants' in text and 'Department of Computing and Mathematical Sciences, California Institute of Technology' in text
 assert 'Matthew J. Colbrook' in text
 assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',text)
 assert 'official Tau Ceti endorsement' in text
check('credit/affiliation/original attribution/no email and local links correct; AI-review limitations explicit')
for n in ['README.md','formalization.yaml']:assert sha(E/'source'/n)==inputs[n] and sha(P/n)!=inputs[n]
for n,h in read(E/'EVIDENCE-MANIFEST.json')['files'].items():assert sha(E/n)==h,n
assert sha(E/'EVIDENCE-MANIFEST.json')=='e684400fe12bb40fe5b685bdb9ff64241fe8435e30b1ebaf6e0362dec13528ab'
assert sha(R/'review.md')=='7050cf5d149dcdcb6ec094a1e30c5dd954efff47ed96e9633511e6a043bc2381'
assert sha(R/'review-receipt.json')=='495f82e512208699c3eca8dab8826e5257179e7a82f5cd7b4ac17ed0e8b73543'
assert sha(R/'completion-review.md')=='f28bc847c248229cf27de7a7791d1f55508fe0965f57dc431b33784c8518a59f'
assert sha(R/'completion-receipt.json')=='fb147a1c076883290e8d389df5cc1d4d2e760f9daeb15dff4b0bdc25346219a4'
check('historical pending snapshot,350-fileevidence and prior independent reports retained unchanged')
for n in ['CATALOG.md','README.md','linear-systems-and-elimination/README.md']:
 before=old(n).decode();after=(ROOT/n).read_text()
 expected=before.replace('43 solved (published or independently audited); 63 solved with Lean verification.','42 solved (published or independently audited); 64 solved with Lean verification.')
 lines=expected.splitlines(keepends=True)
 expected=''.join(x.replace('**✅ SOLVED**','**🏆 LEAN VERIFIED**') if '[IE-21]' in x else x for x in lines)
 assert expected==after,n
check('catalog changes exactly IE21 status and43/63to42/64 counts; other retained verifications unchanged')
renderer=old('tools/render_problems.py').decode().replace('"IE-14", "IV-03"','"IE-14", "IE-21", "IV-03"').replace('{"SP-11", "SP-12"}','{"IE-21", "SP-11", "SP-12"}')
assert renderer==(ROOT/'tools/render_problems.py').read_text()
tex=(ROOT/'linear-systems-and-elimination/IE-21/problem.tex').read_text();otex=old('linear-systems-and-elimination/IE-21/problem.tex').decode()
texmarker=r'\subsection{Problem statement}\label{problem-statement}'
assert re.sub(r'\s+','',tex.split(texmarker,1)[1])==re.sub(r'\s+','',otex.split(texmarker,1)[1])
assert '\\newpage\n'+texmarker in tex and 'Verification check: 2026-09-22' in tex
check('renderer changes only two IE21 membership entries; complete original TeX target/history preserved modulo whitespace')
print('RESULT: PASS exact publication correspondence; PDF visual inspection recorded separately')
