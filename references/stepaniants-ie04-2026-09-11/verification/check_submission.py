"""Check IE-04 source preservation, target, exact evidence and local links.

This is a consistency check, not formal proof verification. It needs only the
standard library and pdftotext (or PDFTOTEXT pointing to that executable).
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
REF = ROOT / 'references/stepaniants-ie04-2026-09-11'
VER = REF / 'verification'
CAN = ROOT / 'linear-systems-and-elimination/IE-04'
BASE = '87366c62d3b5c47d170f747b1cb40ab38d501013'
PROOF = '428c586bf6a0b66ce94d478eed5be6e951032cc09fc646df7204ae2823b14a75'
REVIEW = '757daf1061629d1b1efbebc1a8546fca0a2dfb339d2a8e8d68237a08ccd48564'
CONVERSION = '5730e760dd6b37072170e98fbcbdae862b02a2bf92ef57d3b20050c026ae5fde'
sha = lambda b: hashlib.sha256(b).hexdigest()
original = (VER / 'reviewed-proof.md').read_bytes()
review = (VER / 'IE-04-independent-review.md').read_bytes()
assert len(original) == 8401 and sha(original) == PROOF
assert len(review) == 10522 and sha(review) == REVIEW
conversion = (VER / 'IE-04-packaging-review.md').read_bytes()
assert len(conversion) == 7024 and sha(conversion) == CONVERSION
comparison = (VER / 'IE-04-packaging-comparison.json').read_bytes()
assert len(comparison) == 9833 and sha(comparison) == '6494d9b335400f5772280b0f96898bbe943354253a80802ff02ba1d37b9669a4'
manifest = json.loads((VER / 'original-files.json').read_text())
for name, record in manifest.items():
    data = (REF / 'originals' / name).read_bytes()
    assert len(data) == record['bytes'] and sha(data) == record['sha256'], name
for name in ['verify_bounds.py', 'certificate.json', 'verification.txt']:
    assert (CAN / name).read_bytes() == (REF / 'originals' / name).read_bytes()
assert (VER / 'IE-04-supplied-check-rerun.json').read_bytes() == (CAN / 'certificate.json').read_bytes()


def remove_layout(s):
    s = re.sub(r'\\Needspace\{[0-9]+\\baselineskip\}\n\n', '', s)
    return s.replace('\\nopagebreak[4]\n\n', '')


def core(s):
    s = re.sub(r'(?m)^# ', '## ', remove_layout(s))
    return s.split('## Statement and conclusion\n', 1)[1].split('## Verification, scope, and provenance', 1)[0]


source = (CAN / 'solution.md').read_text()
assert core(original.decode()) == core(source), 'Mathematical core changed'
tex = (CAN / 'solution.tex').read_text()
tex_core = re.split(r'\\subsection\{Statement and\s+conclusion\}', tex, maxsplit=1)[1]
tex_core = re.split(r'\\subsection\{Verification, scope, and\s+provenance\}', tex_core, maxsplit=1)[0]
md_math = re.findall(r'\$\$(.*?)\$\$|(?<!\$)\$(?!\$)(.*?)(?<!\$)\$(?!\$)', core(source), re.S)
tex_math = re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', tex_core, re.S)
normal = lambda pairs: [re.sub(r'\s+', '', a or b) for a,b in pairs]
assert normal(md_math) == normal(tex_math), 'Ordered TeX expressions differ'


def old(path):
    return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)


old_target = old('linear-systems-and-elimination/IE-04/README.md')
assert old_target == (VER / 'original-target.md').read_bytes()
original_body = old_target.decode().split('## Context and notation\n', 1)[1]
assert original_body == (CAN / 'README.md').read_text().split('## Context and notation\n', 1)[1]
original_registry = json.loads(old('problem_ids.json'))
current_registry = json.loads((ROOT / 'problem_ids.json').read_text())
assert len(original_registry) == 203
assert all(current_registry.get(identifier) == path
           for identifier, path in original_registry.items()), 'An original ID mapping changed'
# Later published entries may be appended. The repository validator separately
# checks the full registry against the current published base.
assert '**Status:** Solved' in (CAN / 'README.md').read_text()
author = 'George Stepaniants'
affiliation = 'Department of Computing and Mathematical Sciences, California Institute of Technology'
for p in [CAN/'README.md',CAN/'solution.md',REF/'README.md',ROOT/'RESOLVED.md']:
    assert author in p.read_text() and affiliation in p.read_text(), p
email = re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for p in list(REF.rglob('*.md')) + list(REF.rglob('*.json')) + list(REF.rglob('*.tex')) + [CAN/name for name in ['README.md','solution.md','solution.tex','problem.tex']]:
    assert not email.search(p.read_text()), p
assert 'mailto:' not in tex
extractor = os.environ.get('PDFTOTEXT') or shutil.which('pdftotext')
if not extractor:
    raise SystemExit('Install pdftotext or set PDFTOTEXT to its executable path.')
for p in [CAN/'solution.pdf',CAN/'problem.pdf']:
    text = subprocess.check_output([extractor,str(p),'-'],text=True)
    assert author in text and not email.search(text) and '\ufffd' not in text, p

paths = [ROOT/name for name in ['README.md','CATALOG.md','RESOLVED.md','linear-systems-and-elimination/README.md']]
paths += [CAN/'README.md',CAN/'solution.md',REF/'README.md',VER/'IE-04-independent-review.md',VER/'IE-04-packaging-review.md']
links = 0
for p in paths:
    for url in re.findall(r'\]\(([^)]+)\)',p.read_text()):
        if re.match(r'[a-z]+:',url) or url.startswith('#'):
            continue
        assert (p.parent/unquote(url.split('#',1)[0])).resolve().exists(),(p,url)
        links += 1
print(json.dumps({
    'result':'PASS',
    'frozen_proof_sha256':sha(original),
    'independent_review_sha256':sha(review),
    'separate_conversion_review_sha256':sha(conversion),
    'mathematical_core_sha256':sha(core(source).encode()),
    'mathematical_core_bytes':len(core(source).encode()),
    'mathematical_core_unchanged_except_layout_and_heading_depth':True,
    'ordered_math_expressions_identical_in_tex':len(md_math),
    'all_supplied_files_preserved_byte_identically':len(manifest),
    'supplied_checker_and_certificate_unchanged':True,
    'original_target_context_references_history_unchanged':True,
    'all_203_permanent_id_mappings_unchanged':True,
    'author_and_affiliation_present':True,
    'no_contact_email_in_new_documents_or_pdfs':True,
    'valid_local_links':links,
},indent=2))
