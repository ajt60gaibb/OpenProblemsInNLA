"""Verify IE-02's frozen proof, publication conversion, original target and links.

Uses only Python's standard library plus pdftotext (PDFTOTEXT may set its path).
This is a source-consistency check, not a formal verification of the proof.
"""
from pathlib import Path
from urllib.parse import unquote
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[3]
REF = ROOT / 'references/stepaniants-ie02-2026-09-11'
CAN = ROOT / 'linear-systems-and-elimination/IE-02'
BASE = '87366c62d3b5c47d170f747b1cb40ab38d501013'
PROOF_HASH = '64bbb398344d56651a1a59c65613817bc932cea6772483893a5fc195ce3d9fb9'
REVIEW_HASH = '5a7f2e3b9f28d16566da3e51046434c889ad7cec686ad083e6250597fc951e6c'
sha = lambda b: hashlib.sha256(b).hexdigest()
original = (REF / 'verification/reviewed-proof.md').read_bytes()
review = (REF / 'verification/IE-02-independent-review.md').read_bytes()
assert sha(original) == PROOF_HASH
assert len(review) == 11101 and sha(review) == REVIEW_HASH


def remove_layout(s):
    s = re.sub(r'\\Needspace\{[0-9]+\\baselineskip\}\n\n', '', s)
    return s.replace('\\nopagebreak[4]\n\n', '')


def core(s):
    s = remove_layout(s).split('## 1. Exact target and notation', 1)[1]
    return s.split('## 6. Status, source check, and scope', 1)[0].split('## Scope and verification', 1)[0]


source = (CAN / 'solution.md').read_text()
assert core(original.decode()) == core(source)
tex = (CAN / 'solution.tex').read_text()
tex_core = re.split(r'\\subsection\{1\. Exact target and\s+notation\}', tex, maxsplit=1)[1]
tex_core = tex_core.split(r'\subsection{Scope and verification}', 1)[0]
md_formulas = re.findall(r'\$\$(.*?)\$\$|(?<!\$)\$(?!\$)(.*?)(?<!\$)\$(?!\$)', core(source), re.S)
tex_formulas = re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', tex_core, re.S)
normal = lambda seq: [re.sub(r'\s+', '', a or b) for a, b in seq]
assert normal(md_formulas) == normal(tex_formulas), 'Math expressions differ in source conversion'


def old(path):
    return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)


def target(s):
    return s.split('## Problem statement\n', 1)[1].split('\n## References', 1)[0]


original_target = old('linear-systems-and-elimination/IE-02/README.md')
assert original_target == (REF / 'verification/original-target.md').read_bytes()
assert target(original_target.decode()) == target((CAN / 'README.md').read_text())
assert old('problem_ids.json') == (ROOT / 'problem_ids.json').read_bytes()
assert len(json.loads((ROOT / 'problem_ids.json').read_text())) == 203
assert '**Status:** Solved' in (CAN / 'README.md').read_text()
author = 'George Stepaniants'
affiliation = 'Department of Computing and Mathematical Sciences, California Institute of Technology'
for p in [CAN / 'README.md', CAN / 'solution.md', REF / 'README.md', ROOT / 'RESOLVED.md']:
    text = p.read_text()
    assert author in text and affiliation in text, p
email = re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
new_text = list(REF.rglob('*.md')) + list(REF.rglob('*.json')) + [CAN / name for name in ['README.md', 'solution.md', 'solution.tex', 'problem.tex']]
for p in new_text:
    assert not email.search(p.read_text()), p
assert 'mailto:' not in tex
pdftotext = os.environ.get('PDFTOTEXT', shutil.which('pdftotext'))
if not pdftotext:
    raise SystemExit('Install pdftotext or set PDFTOTEXT to its path.')
for p in [CAN / 'solution.pdf', CAN / 'problem.pdf']:
    text = subprocess.check_output([pdftotext, str(p), '-'], text=True)
    assert author in text and not email.search(text), p
    assert '\ufffd' not in text, p

paths = [ROOT / name for name in ['README.md', 'CATALOG.md', 'RESOLVED.md', 'linear-systems-and-elimination/README.md']]
paths += [CAN / 'README.md', CAN / 'solution.md', REF / 'README.md', REF / 'verification/IE-02-independent-review.md']
links = 0
for p in paths:
    for url in re.findall(r'\]\(([^)]+)\)', p.read_text()):
        if re.match(r'[a-z]+:', url) or url.startswith('#'):
            continue
        assert (p.parent / unquote(url.split('#', 1)[0])).resolve().exists(), (p, url)
        links += 1

print(json.dumps({
    'result': 'PASS',
    'frozen_proof_sha256': sha(original),
    'independent_review_sha256': sha(review),
    'mathematical_core_sha256': sha(core(source).encode()),
    'mathematical_core_bytes': len(core(source).encode()),
    'mathematical_core_unchanged_except_layout': True,
    'ordered_math_expressions_identical_in_tex': len(md_formulas),
    'original_canonical_target_unchanged': True,
    'all_203_permanent_id_mappings_unchanged': True,
    'author_and_affiliation_present': True,
    'no_contact_email_in_new_documents_or_pdfs': True,
    'valid_local_links': links,
}, indent=2))
