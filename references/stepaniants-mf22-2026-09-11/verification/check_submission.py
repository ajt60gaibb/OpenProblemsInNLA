"""Check MF-22 exact proof preservation, immutable target, links and authorship."""
from pathlib import Path
import hashlib,json,re,subprocess
from urllib.parse import unquote
ROOT=Path(__file__).resolve().parents[3]
BASE='aaa88c40fbf58e8cebc335021b3c5cd108c357e4'
REF=ROOT/'references/stepaniants-mf22-2026-09-11'
CANON=ROOT/'matrix-functions-and-stability/MF-22'
sha=lambda b:hashlib.sha256(b).hexdigest()
original=(REF/'verification/reviewed-proof.md').read_bytes()
review=(REF/'verification/MF-22-independent-review.md').read_bytes()
assert sha(original)=='4b2b030d0284014d2eabfc79ce56c4293bc83be7cb80f86deda31d3dddab5f4f'
assert len(review)==9317 and sha(review)=='256c61373b594db549bf5aef4c62a0f996b3d812d4b797cb47a7a8122e5fd1d8'
def remove_layout(s):
    return re.sub(r'\\nopagebreak\[4\]\n\n','',re.sub(r'\\Needspace\{[0-9]+\\baselineskip\}\n\n','',s))
def core(s):
    return remove_layout(s).split('## 1. Statement and exact transfer recurrence',1)[1].split('## Scope and source',1)[0]
canonical=(CANON/'solution.md').read_text()
assert core(original.decode())==core(canonical)
def old(path):return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
def target(s):return s.split('## Statement\n',1)[1].split('\n## Numerical significance',1)[0]
assert target(old('matrix-functions-and-stability/MF-22/README.md').decode())==target((CANON/'README.md').read_text())
assert old('problem_ids.json')==(ROOT/'problem_ids.json').read_bytes()
assert '**Status:** Solved' in (CANON/'README.md').read_text()
author='George Stepaniants';affiliation='Department of Computing and Mathematical Sciences, California Institute of Technology'
for p in [CANON/'README.md',CANON/'solution.md',ROOT/'RESOLVED.md',REF/'README.md']:
    s=p.read_text();assert author in s and affiliation in s,p
new_text=[CANON/'README.md',CANON/'solution.md',CANON/'solution.tex',CANON/'problem.tex',REF/'README.md',REF/'verification/reviewed-proof.md',REF/'verification/MF-22-independent-review.md']
email=re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for p in new_text:assert not email.search(p.read_text()),p
for p in [CANON/'solution.pdf',CANON/'problem.pdf']:
    text=subprocess.check_output(['pdftotext',str(p),'-'],text=True)
    assert author in text and not email.search(text),p
paths=[ROOT/'README.md',ROOT/'CATALOG.md',ROOT/'RESOLVED.md',ROOT/'matrix-functions-and-stability/README.md',CANON/'README.md',CANON/'solution.md',REF/'README.md',REF/'verification/MF-22-independent-review.md',REF/'verification/reviewed-proof.md']
links=0
for p in paths:
    for url in re.findall(r'\]\(([^)]+)\)',p.read_text()):
        if re.match(r'[a-z]+:',url) or url.startswith('#'):continue
        assert (p.parent/unquote(url.split('#',1)[0])).resolve().exists(),(p,url)
        links+=1
print(json.dumps({'result':'PASS','original_proof_sha256':sha(original),'independent_review_sha256':sha(review),'mathematical_core_sha256':sha(core(original.decode()).encode()),'mathematical_body_unchanged_after_layout_directives_removed':True,'canonical_statement_unchanged':True,'all_203_id_mappings_unchanged':True,'author_department_university_present':True,'no_contact_email_in_new_documents_or_pdfs':True,'valid_local_markdown_links':links},indent=2))
