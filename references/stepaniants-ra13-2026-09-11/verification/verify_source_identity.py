"""Read-only verification of frozen proof, permitted conversion and retained RA-13 target."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[3];ver=Path(__file__).resolve().parent;page=root/'randomized-and-low-rank-approximation/RA-13'
sha=lambda x:hashlib.sha256(x).hexdigest()
frozen=(ver/'reviewed-proof.md').read_text();record=json.loads((ver/'source-identity.json').read_text())
assert sha(frozen.encode())==record['frozen_source_sha256']
assert sha((ver/'RA-13-independent-review.md').read_bytes())==record['independent_review_sha256']
old=frozen.split('## 1. Normalized theorem\n',1)[1].split('\n## References and current-source check',1)[0]
assert old.count(',quad')==2 and old.count('\nu(t)=1-g(z-t)/g(z)')==1
expected=old.replace(',quad',r',\quad').replace('\nu(t)=1-g(z-t)/g(z)','\n\\nu(t)=1-g(z-t)/g(z)')
md=(page/'solution.md').read_text();actual=md.split('## 1. Normalized theorem\n',1)[1].split('\n## References and source check',1)[0]
assert expected==actual
assert sha(old.encode())==record['frozen_core_sha256'] and sha(actual.encode())==record['corrected_core_sha256']
assert sha(md.encode())==record['canonical_solution_md_sha256']
current=(page/'README.md').read_text();retained=current.split('## Problem statement\n',1)[1].split('\n## Why it matters',1)[0]
assert retained==(ver/'original-target.md').read_text()
assert sha(retained.encode())==record['original_target_sha256']
base=subprocess.check_output(['git','show','aaa88c4:randomized-and-low-rank-approximation/RA-13/README.md'],cwd=root,text=True)
assert retained==base.split('## Problem statement\n',1)[1].split('\n## Why it matters',1)[0]
old_aux=base.split('<!-- colbrook-transfer -->',1)[1].split('<!-- /colbrook-transfer -->',1)[0]
new_aux=current.split('<!-- colbrook-transfer -->',1)[1].split('<!-- /colbrook-transfer -->',1)[0]
strip_status=lambda x:re.sub(r'^\*\*(?:Remaining question|Historical scope):\*\*.*$','',x,flags=re.M)
assert strip_status(old_aux)==strip_status(new_aux)
assert 'George Stepaniants' in md and 'Department of Computing and Mathematical Sciences' in md and 'California Institute of Technology' in md
assert 'George Stepaniants' in (page/'solution.tex').read_text()
email=re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
files=list(ver.parent.rglob('*'))+[page/'solution.md',page/'solution.tex',page/'README.md']
for p in files:
 if p.is_file() and p.suffix in {'.md','.tex','.txt','.json','.py'}:
  assert not email.search(p.read_text()),'Contact-address string in '+str(p.relative_to(root))
print('PASS: frozen source/review hashes; exactly three permitted notation corrections; canonical mathematical body; original target; auxiliary authorship/content except historical-scope sentence; author/affiliation; no contact-address strings in new text evidence.')
print('Canonical mathematical-body SHA256:',record['corrected_core_sha256'])
