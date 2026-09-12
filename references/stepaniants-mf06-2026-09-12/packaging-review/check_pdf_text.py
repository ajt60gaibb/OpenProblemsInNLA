#!/usr/bin/env python3
"""Read already-built MF-06 PDF metadata and text using Poppler; no rendering.

Usage: python3 check_pdf_text.py --repo PATH
Reads two PDFs and writes only JSON to stdout. This is not visual inspection.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import unicodedata

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    args = ap.parse_args()
    repo = args.repo.resolve()
    pdfinfo, pdftotext = shutil.which('pdfinfo'), shutil.which('pdftotext')
    assert pdfinfo and pdftotext, 'Poppler pdfinfo and pdftotext must be on PATH'
    results = []
    for name, count, author in [('solution.pdf', 7, 'George Stepaniants'),
                                ('problem.pdf', 2, 'Open Problems in Numerical Linear Algebra')]:
        path = repo / 'matrix-functions-and-stability/MF-06' / name
        raw = path.read_bytes()
        metadata = subprocess.check_output([pdfinfo, str(path)], text=True)
        content = subprocess.check_output([pdftotext, '-layout', str(path), '-'], text=True)
        normalized = ' '.join(unicodedata.normalize('NFKC', content).split())
        parsed = dict(re.findall(r'^([^:\n]+):\s*(.*)$', metadata, flags=re.M))
        assert parsed.get('Author') == author
        assert int(parsed['Pages']) == count
        assert parsed.get('Encrypted') == 'no' and parsed.get('JavaScript') == 'no'
        for phrase in ('George Stepaniants', 'Department of Computing and Mathematical Sciences',
                       'California Institute of Technology', 'Pasadena, California, USA'):
            assert phrase in normalized, (name, phrase)
        email = re.compile(r'(?<![\w.+-])[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+')
        assert not email.search(metadata + content), name + ': email-like contact found'
        assert 'not external human peer review or formal verification' in normalized
        anomalies = [{'character': c, 'count': content.count(c)} for c in ('ğ', '\ufffd') if c in content]
        results.append({'path': path.relative_to(repo).as_posix(), 'bytes': len(raw),
                        'sha256': hashlib.sha256(raw).hexdigest(),
                        'metadata': parsed, 'extracted_text_bytes': len(content.encode()),
                        'extracted_text_sha256': hashlib.sha256(content.encode()).hexdigest(),
                        'full_visible_author_and_affiliation': True,
                        'email_matches': 0, 'text_anomalies_requiring_visual_followup': anomalies})
    print(json.dumps({'scope': 'Read-only PDF metadata and text audit. Existing visual QA is separate and belongs to its named reviewers.',
                      'verdict': 'PASS' if not any(r['text_anomalies_requiring_visual_followup'] for r in results)
                                 else 'Text/metadata checks pass; flagged glyphs need the document reviewer’s visual check',
                      'pdfs': results}, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
