"""Independent immutable-head delta check. Does not print any removed contact."""
import hashlib, json, re, subprocess
from pathlib import Path
from pypdf import PdfReader
import pdfplumber

ART = Path('/private/tmp/nla-review-wave2-artifacts')
OLD, NEW = ART/'pr-68', ART/'pr-68-current'
REPO = '/private/tmp/nla-review-pr68-delta-20260911'
OLD_HEAD = 'c9ad7691e1b3f2cf6595fd204fef54a6b1349910'
NEW_HEAD = 'a64f93f93124e0f7486d15a06cac8d0eec69a9eb'

def sha(data):
    return hashlib.sha256(data).hexdigest()

changed = subprocess.check_output(['git', 'diff', '--name-only', OLD_HEAD, NEW_HEAD], cwd=REPO, text=True).splitlines()
records_path = 'references/stepaniants-2026-09-11/verification/document-checks.json'
records = json.loads((NEW/records_path).read_text())
redaction = records['author_contact_redaction']
errors, checks = [], {}
for key, root in [('previous_artifact_hashes', OLD), ('current_artifact_hashes', NEW)]:
    for path, expected in redaction[key].items():
        if sha((root/path).read_bytes()) != expected:
            errors.append({'hash': key, 'path': path})
for path, expected in records['artifact_hashes'].items():
    if sha((NEW/path).read_bytes()) != expected:
        errors.append({'hash': 'artifact_hashes', 'path': path})

for path, details in redaction['complete_document_bodies_preserved'].items():
    a, b = (OLD/path).read_bytes(), (NEW/path).read_bytes()
    ab, bb = a[a.index(b'\\begin{document}'):], b[b.index(b'\\begin{document}'):]
    checks[path] = {'old_full_sha256': sha(a), 'new_full_sha256': sha(b),
                    'body_sha256': sha(bb), 'entire_body_equal': ab == bb}
    if ab != bb or sha(bb) != details['document_body_sha256']:
        errors.append({'body': path})

# Recover the removed address only in memory, avoiding a literal in this artifact.
old_source = (OLD/'arithmetic-and-complexity/AA-01/solution.tex').read_text()
needles = set(re.findall(r'mailto:([^}]+)', old_source))
assert needles, 'Expected old source contact for redaction comparison'
inventory = (OLD/'REVIEW-CHANGED-FILES.txt').read_text().splitlines()
scan, pdf_checks = [], {}
for path in inventory:
    raw = (NEW/path).read_bytes()
    hit_count = sum(raw.lower().count(x.lower().encode()) for x in needles)
    if path.endswith('.pdf'):
        reader = PdfReader(NEW/path)
        visible = '\n'.join(page.extract_text() or '' for page in reader.pages)
        hit_count += sum(visible.lower().count(x.lower()) for x in needles)
        # Pypdf includes objects from compressed object streams in xref_objStm.
        ids = {(objid, generation) for generation, objs in reader.xref.items()
               for objid in objs if objid != 0}
        ids |= {(objid, 0) for objid in reader.xref_objStm}
        from pypdf.generic import IndirectObject
        decoded_objects = 0
        for objid, generation in ids:
            obj = reader.get_object(IndirectObject(objid, generation, reader))
            decoded_objects += 1
            values = [str(obj).encode('utf-8', errors='replace')]
            if hasattr(obj, 'get_data'):
                values.append(obj.get_data())
            for value in values:
                hit_count += sum(value.lower().count(x.lower().encode()) for x in needles)
        expected = records['pdfs'].get(path, {})
        if expected.get('sha256') and sha(raw) != expected['sha256']:
            errors.append({'pdf_hash': path})
        if path in changed:
            oldreader = PdfReader(OLD/path)
            oldtext = '\n'.join(page.extract_text() or '' for page in oldreader.pages)
            for needle in needles:
                oldtext = oldtext.replace(needle, '')
            bounds = []
            with pdfplumber.open(NEW/path) as doc:
                for number, page in enumerate(doc.pages, 1):
                    outside = [c for c in page.chars if c['x0'] < 5 or c['x1'] > page.width-5 or c['top'] < 5 or c['bottom'] > page.height-5]
                    bounds.append({'page': number, 'outside_five_point_inset': len(outside)})
            pdf_checks[path] = {'pages_before': len(oldreader.pages), 'pages_after': len(reader.pages),
                                'extracted_text_equal_after_contact_removal_and_whitespace_normalization': oldtext.split() == visible.split(),
                                'sha256': sha(raw), 'character_bounds': bounds}
            if oldtext.split() != visible.split() or any(x['outside_five_point_inset'] for x in bounds):
                errors.append({'pdf_content_or_bounds': path})
    scan.append({'path': path, 'removed_contact_matches': hit_count})
    if hit_count:
        errors.append({'contact': path})

result = {'old_head': OLD_HEAD, 'new_head': NEW_HEAD, 'changed_paths': changed,
          'source_checks': checks, 'pdf_checks': pdf_checks, 'redaction_scan': scan,
          'all_recorded_hashes_match': not any('hash' in x or 'pdf_hash' in x for x in errors),
          'errors': errors}
(ART/'audit-root/PR68-delta-a64f93f-evidence.json').write_text(json.dumps(result, indent=2))
print(json.dumps({'changed_paths': changed, 'source_checks': checks, 'pdf_checks': pdf_checks,
                  'files_scanned': len(scan), 'removed_contact_matches': sum(x['removed_contact_matches'] for x in scan),
                  'errors': errors}, indent=2))
assert not errors
