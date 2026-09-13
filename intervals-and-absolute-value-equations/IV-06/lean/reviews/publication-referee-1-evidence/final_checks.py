"""Bind the final preparer freeze, complete upstream preservation and viewed PDF.

Read-only with respect to all candidate, publication and operational inputs.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
ENTRY = PROJECT.parent
REPO = PROJECT.parents[2]
PUB = PROJECT / 'verification/publication-2026-09-12'
LINUX = PROJECT / 'verification/linux-2026-09-12'
sha = lambda b: hashlib.sha256(b).hexdigest()
digest = lambda p: sha(p.read_bytes())
load = lambda p: json.loads(p.read_text())
git = lambda *a: subprocess.check_output(['git', *a], cwd=REPO)
save = lambda n, d: (HERE / n).write_text(json.dumps(d, indent=2) + '\n')
preparer_hashes = {
 'PUBLICATION-HANDOFF.md': '07fb9d3e4bc61f0eccdd137dea6264f1e5e948fb2d920fb67ea58df84db703c3',
 'INTEGRITY-CHECKS.json': '71232a29a9150ef51a28dfba398b361d982e3540af31470b085ef02727676beb',
 'EVIDENCE-MANIFEST.json': 'ab90352bc400a56881643a7f5896a5c6417a6474b6eddfc35cb895abc410b113',
}
for rel, h in preparer_hashes.items():
    assert digest(PUB / rel) == h, rel
outer = PUB / 'EVIDENCE-MANIFEST.json'
inventory = load(outer)['files']
actual = {p.relative_to(PUB).as_posix() for p in PUB.rglob('*') if p.is_file() and p != outer}
assert actual == set(inventory) and len(inventory) == 23
for rel, rec in inventory.items():
    p = PUB / rel
    assert digest(p) == rec['sha256'] and p.stat().st_size == rec['bytes']
integrity = load(PUB / 'INTEGRITY-CHECKS.json')
assert len(integrity['publication_sha256']) == 9
for rel, h in integrity['publication_sha256'].items():
    assert digest(REPO / rel) == h, rel
assert set(git('diff', '--name-only', 'HEAD').decode().splitlines()) == set(integrity['publication_sha256'])
assert git('show', '-s', '--format=%ae%x00%ce', 'HEAD').rstrip(b'\n') == b'\0'
assert git('show', '-s', '--format=%an%x00%cn', 'HEAD').rstrip(b'\n') == b'George Stepaniants\0George Stepaniants'

preserved = load(PUB / 'preserved-upstream-files.json')
upstream = '5830ed4fb06da0659414a3deb2a40ad327aca052'
assert preserved['base'] == upstream
upstream_files = {}
for rec in git('ls-tree', '-rz', upstream).split(b'\0'):
    if not rec:
        continue
    metadata, raw = rec.split(b'\t', 1)
    mode, kind, oid = metadata.split()
    rel = raw.decode()
    assert kind == b'blob' and mode in (b'100644', b'100755')
    upstream_files[rel] = oid.decode()
expected_preserved = {p: oid for p, oid in upstream_files.items() if p not in integrity['publication_sha256']}
assert expected_preserved == preserved['Git_blobs'] and len(expected_preserved) == 6967
for rel, oid in expected_preserved.items():
    path = REPO / rel
    assert path.is_file() and not path.is_symlink()
    b = path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == oid, rel

freeze_path = PROJECT / 'verification/proof-freeze.json'
assert digest(freeze_path) == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
freeze = load(freeze_path)
assert len(freeze['files']) == 126 and len(freeze['source_files']) == 8
for rel, record in freeze['files'].items():
    path = PROJECT / rel if rel != 'README.md' else PROJECT / 'verification/linux-candidate-2026-09-12/README.statement.md'
    assert digest(path) == record['sha256'] and path.stat().st_size == record['bytes'], rel
for rel, h in freeze['source_files'].items():
    assert sha(git('show', freeze['source_commit'] + ':' + rel)) == h, rel
    assert digest(LINUX / 'source' / rel) == h, rel
    if rel != 'intervals-and-absolute-value-equations/IV-06/README.md':
        assert digest(REPO / rel) == h, rel

visual = load(PUB / 'VISUAL-REVIEW.json')
assert digest(ENTRY / 'problem.pdf') == visual['pdf_sha256'] == '56df700684f4c678dacd357638ecf0d2397622a8217bcbe9d9266147dfcd1aab'
assert digest(ENTRY / 'problem.tex') == visual['tex_sha256'] == '16a8c9f5ecaf924a2187bb72963cf393a6c83e117acfed6123577fedea2023b7'
assert len(visual['images']) == 3
for rel, h in visual['images'].items():
    assert digest(Path(rel)) == h
# All three original full-page PNGs were independently displayed using view_image.
# Bbox extraction additionally checks that the apparent chat-image footer crop is
# not a source-PDF defect: every actual PDF word is inside its A4 page boundary.
cmd = ['/opt/homebrew/bin/pdftotext', '-bbox', str(ENTRY / 'problem.pdf'), '-']
r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
assert r.returncode == 0
(HERE / 'pdf-bbox.html').write_bytes(r.stdout)
doc = ET.fromstring(r.stdout)
ns = {'h': 'http://www.w3.org/1999/xhtml'}
pages = doc.findall('.//h:page', ns)
assert len(pages) == 3
page_data = []
for number, page in enumerate(pages, 1):
    words = page.findall('h:word', ns)
    width, height = float(page.attrib['width']), float(page.attrib['height'])
    assert words
    for w in words:
        assert 0 <= float(w.attrib['xMin']) <= float(w.attrib['xMax']) <= width
        assert 0 <= float(w.attrib['yMin']) <= float(w.attrib['yMax']) <= height
    page_data.append({'page': number, 'words': len(words), 'width_pt': width, 'height_pt': height,
                      'all_word_boxes_inside_page': True})
save('PDF-REVIEW.json', {
    'reviewer': '/root/leancert_examples', 'independently_displayed_pages': [1, 2, 3],
    'result': 'PASS: all three complete page images independently inspected; no mathematical/content/layout correction',
    'observations': {
        '1': 'Correct permanent IV-06 title and Lean verified status; Colbrook mathematical credit and George Caltech CMS formalization affiliation, all eight exports readable.',
        '2': 'Actual run, permitted axioms, pins and reproduction commands readable; complete original universal independent-entry/eigenvector/component target, including empty and singleton cases, is intact.',
        '3': 'Both original references and dated historical status/audit sections retained and legible; page numbering and margins intact.'},
    'pdf_sha256': visual['pdf_sha256'], 'tex_sha256': visual['tex_sha256'],
    'viewed_png_sha256': visual['images'], 'new_PDF_export_or_edit': False,
    'bbox_command': cmd, 'bbox_exit_code': r.returncode, 'page_geometry_checks': page_data,
    'skill': '/Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.904.11930/skills/pdf/SKILL.md',
    'skill_sha256': digest(Path('/Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.904.11930/skills/pdf/SKILL.md'))})

raw = LINUX / 'artifacts/lean-IV-06/verify-20260912T233429Z-4164'
log = (raw / 'comparator.log').read_text()
assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
assert log.rstrip().endswith('EXIT_STATUS=0')
assert 'Build completed successfully (1916 jobs).' in log
assert 'Build completed successfully (2918 jobs).' in log
phase = log.split('Building Solution', 1)[1]
assert 'warning:' not in phase
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", log)
assert len(reports) == 17
assert all(set(a.split(', ')) == {'propext', 'Classical.choice', 'Quot.sound'} for _, a in reports)
deps = (raw / 'dependencies.log').read_text()
for package in load(PROJECT / 'lake-manifest.json')['packages']:
    assert f"{package['name']}: checking out revision '{package['rev']}'" in deps
assert deps.count(': cloning ') == 10
cache = (raw / 'mathlib-cache.log').read_text()
assert '8690' in cache

save('final-checks.json', {
    'verdict': 'PASS final preparer freeze and complete proof/source/upstream/PDF preservation',
    'utc': datetime.now(timezone.utc).isoformat(), 'preparer_binding': preparer_hashes,
    'preparer_evidence_files': 23, 'preparer_evidence_total_including_outer': 24,
    'publication_outputs': integrity['publication_sha256'], 'all_other_upstream_files': 6967,
    'preserved_proof_inputs': 125, 'exact_archived_statement_README': True,
    'preserved_original_Git_source_blobs': 8,
    'candidate_source_build_kernel_log_independently_read': True,
    'actual_kernel_reports': {n: a.split(', ') for n, a in reports},
    'proof_Lake_dependency_or_Linux_rerun': False,
    'source_pin_proof_canonical_or_preparer_evidence_changes': False,
    'publication_review_role_not_additional_math_referee': True})
print('PASS: final 23-file preparer seal, nine outputs, 6967 other upstream files, all 126 proof-freeze inputs via exact README archive, eight original sources, and three PDF pages.')
