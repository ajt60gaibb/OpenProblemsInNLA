"""Check the MF-18 proof conversion, immutable target, links and authorship."""
from pathlib import Path
import hashlib, json, re, subprocess
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[3]
BASE = 'aaa88c40fbf58e8cebc335021b3c5cd108c357e4'
DIR = ROOT / 'references/stepaniants-mf18-2026-09-11'
CANON = ROOT / 'matrix-functions-and-stability/MF-18'
sha = lambda b: hashlib.sha256(b).hexdigest()
original = (DIR/'verification/reviewed-proof.md').read_bytes()
review = (DIR/'verification/MF-18-independent-review.md').read_bytes()
assert len(original) == 10665 and sha(original) == 'dc6fb4b1b4c8d1fc2d841b35165e708d21d8f228dfdf18402e5845a9f29fcfd7'
assert len(review) == 9200 and sha(review) == '3c4f41e34a1ea41351e49f865ef26ff3c77d38e5213ffcddce4c370502a11011'
def mathematical_body(s):
    return s.split('## Theorem 1',1)[1].split('## Scope, attribution, and status',1)[0]
assert mathematical_body(original.decode()) == mathematical_body((CANON/'solution.md').read_text())
def old_file(p):
    return subprocess.check_output(['git','show',BASE+':'+p],cwd=ROOT)
def target(s):
    return s.split('## Problem statement\n',1)[1].split('\n## Why this matters for NLA',1)[0]
assert target(old_file('matrix-functions-and-stability/MF-18/README.md').decode()) == target((CANON/'README.md').read_text())
assert old_file('problem_ids.json') == (ROOT/'problem_ids.json').read_bytes()
assert '**Status:** Solved' in (CANON/'README.md').read_text()
author='George Stepaniants'
affiliation='Department of Computing and Mathematical Sciences, California Institute of Technology'
for p in [CANON/'README.md',CANON/'solution.md',ROOT/'RESOLVED.md',DIR/'README.md']:
    s=p.read_text()
    assert author in s and affiliation in s, p
# These are newly authored prose/typesetting files, not the archived public-network content.
new_text=[CANON/'README.md',CANON/'solution.md',CANON/'solution.tex',CANON/'problem.tex',DIR/'README.md',DIR/'verification/reviewed-proof.md',DIR/'verification/MF-18-independent-review.md']
for p in new_text:
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',p.read_text()),p
paths=[ROOT/'README.md',ROOT/'CATALOG.md',ROOT/'RESOLVED.md',ROOT/'matrix-functions-and-stability/README.md',CANON/'README.md',CANON/'solution.md',DIR/'README.md',DIR/'verification/MF-18-independent-review.md',DIR/'verification/reviewed-proof.md']
links=0
for p in paths:
    for url in re.findall(r'\]\(([^)]+)\)',p.read_text()):
        if re.match(r'[a-z]+:',url) or url.startswith('#'):
            continue
        path=unquote(url.split('#',1)[0])
        assert (p.parent/path).resolve().exists(),(p,url)
        links+=1
print(json.dumps({'result':'PASS','original_proof_sha256':sha(original),'independent_review_sha256':sha(review),'mathematical_body_unchanged':True,'canonical_statement_unchanged':True,'all_203_id_mappings_unchanged':True,'author_department_university_present':True,'no_contact_email_in_new_documents':True,'valid_local_markdown_links':links},indent=2))
