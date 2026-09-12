#!/usr/bin/env python3
"""Read-only FR-12 packaging checks; not a mathematical proof verifier.

Run with --repo PATH. --allow-pending-manifest is permitted only during
assembly; the completed archive should be checked without that flag.
No input files, PDFs, indexes or git state are written.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit

ORIGINAL = 'efbcaeb82adc140be98cdffca39bf9d9a34d3b281951f42c9d7f7232279335ba'
MATH_REVIEW = '306dfae7a7d2ebe87f27ee3851b62baf8b1a4b0193d344de5eb18d226f652963'
OLD_TARGET = '75985085b1cd29b2a9358692adb1573ab5c454f0befd4d991e023f37cc6cd942'
BASE = '1f22006bdaa4659fcaa0bb775a887685cd3cc566'
REL = Path('frames-and-matrix-designs/FR-12')
RECORD = Path('references/stepaniants-fr12-2026-09-12')


def fp(path):
    b = path.read_bytes()
    return {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def normalized_formula(s):
    s = s.replace(r'\HH', r'\mathcal H')
    s = re.sub(r'\\(?:label|tag)\{[^{}]*\}', '', s)
    return re.sub(r'\s+', '', s)


def math_stream(s, kind):
    if kind == 'md':
        pattern = r'\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$'
    else:
        pattern = r'\\\[(.*?)\\\]|\\\((.*?)\\\)|\\begin\{equation\}(.*?)\\end\{equation\}|(?<!\\)\$(.*?)(?<!\\)\$'
    return [normalized_formula(next(g for g in m.groups() if g is not None))
            for m in re.finditer(pattern, s, re.S)]


def md_links(s):
    # Ignore fenced reproduction commands, which are not rendered links.
    s = re.sub(r'```.*?```', '', s, flags=re.S)
    return re.findall(r'(?<!!)\[[^\]\n]*\]\(([^\s)]+)\)', s)


def check_links(path, root, pending):
    s = path.read_text()
    links = md_links(s) if path.suffix == '.md' else re.findall(r'\\href\{([^{}]+)\}', s)
    count = 0
    for target in links:
        u = urlsplit(target)
        if u.scheme or not u.path:
            continue
        resolved = (path.parent / unquote(u.path)).resolve()
        assert resolved.is_relative_to(root), (path, target, 'escapes repository')
        count += 1
        if not resolved.exists():
            if resolved == root / RECORD / 'manifest.json' and pending:
                continue
            raise AssertionError(('missing link', str(path.relative_to(root)), target))
    return count


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--allow-pending-manifest', action='store_true')
    a = p.parse_args()
    root = a.repo.resolve()
    c, r = root / REL, root / RECORD
    files = {name: fp(c / name) for name in ['README.md', 'problem.tex', 'problem.pdf', 'solution.md', 'solution.tex', 'solution.pdf']}
    assert fp(r / 'original-user-source.tex')['sha256'] == ORIGINAL
    assert (r / 'reviewed-proof.tex').read_bytes() == (r / 'original-user-source.tex').read_bytes()
    assert fp(r / 'REVIEW.md')['sha256'] == MATH_REVIEW
    assert fp(r / 'canonical-target.md')['sha256'] == OLD_TARGET
    original = (r / 'original-user-source.tex').read_text()
    tex, md = (c / 'solution.tex').read_text(), (c / 'solution.md').read_text()
    begin, end = r'\section{Exact target}', r'\end{document}'
    old_body = original[original.index(begin):original.index(end)]
    new_body = tex[tex.index(begin):tex.index(end)]
    assert old_body == new_body
    assert original.split(r'\begin{abstract}', 1)[1].split(r'\end{abstract}', 1)[0] == tex.split(r'\begin{abstract}', 1)[1].split(r'\end{abstract}', 1)[0]
    tm = math_stream(tex[tex.index(r'\begin{abstract}'):tex.index(r'\begin{thebibliography}')], 'tex')
    mm = math_stream(md[:md.index('## References')], 'md')
    assert tm == mm and len(tm) == 66
    for row in [(1, 2, 8, 4, 2), (2, 8, 1536, 192, 8)]:
        assert ' & '.join(map(str, row)) in tex
        assert '| ' + ' | '.join(map(str, row)) + ' |' in md
    target_old = (r / 'canonical-target.md').read_text()
    target = (c / 'README.md').read_text()
    assert target_old[target_old.index('## Statement'):] == target[target.index('## Statement'):]
    registry = json.loads((root / 'problem_ids.json').read_text())
    assert registry['FR-12'] == str(REL / 'README.md')
    # Read the accepted base without mutating git or rerunning global tests.
    old_registry = subprocess.check_output(['git', '-C', str(root), 'show', BASE + ':problem_ids.json'])
    assert json.loads(old_registry) == registry and len(registry) == 217
    pt = (c / 'problem.tex').read_text()
    canonical_math = math_stream(target, 'md')
    assert canonical_math == math_stream(pt, 'tex')
    im = json.loads((r / 'independent-manifest.json').read_text())
    for name, expected in im['files'].items():
        assert fp(r / name) == expected, ('independent manifest mismatch', name)
    verification = json.loads((r / 'verification.json').read_text())
    assert verification['independent_mathematical_review']['sha256'] == MATH_REVIEW
    for name in ['solution.pdf', 'problem.pdf']:
        assert verification['pdfs'][name]['sha256'] == files[name]['sha256']
    assert json.loads((r / 'pdf-qa.json').read_text())['pdf'] == files['solution.pdf']
    network = json.loads((r / 'public-audit/network-check.json').read_text())
    counts = Counter(b['statuses']['FR-12'].replace('**Status:**', '').strip()
                     for b in network['branches'])
    assert counts == {'Open': 19, 'Missing page': 30}
    assert len(network['repositories']) == 6 and len(network['branches']) == 49
    assert network['counts']['selected_text_blobs'] == 118
    assert len(network['discussion_matches']) == 1
    assert network['discussion_matches'][0]['url'].endswith('/pull/111')
    assert len(network['document_fingerprints']) == 118
    required = ['README.md', 'REVIEW.md', 'original-user-source.tex', 'reviewed-proof.tex',
                'canonical-target.md', 'independent-manifest.json', 'independent_check.py',
                'independent-check.json', 'verify_fr12.py', 'verification-output.json',
                'check_conversion.py', 'conversion-check-output.json', 'build_solution.py',
                'source-preservation.json', 'source-search.md', 'pdf-qa.json',
                'verification.json', 'public-audit/README.md', 'public-audit/network-check.json',
                'public-audit/audit_public.py', 'public-audit/build_sanitized.py']
    for name in required:
        assert (r / name).is_file(), ('missing required evidence', name)
    if not a.allow_pending_manifest:
        assert (r / 'manifest.json').is_file()
    # Original target navigation is an explicitly archived historical snapshot.
    # All live Markdown/TeX links, including frozen review links, are checked.
    reference_text = sorted(p for p in r.rglob('*') if p.is_file() and p.suffix in {'.md', '.tex', '.json', '.py'})
    live_link_files = [c / 'README.md', c / 'solution.md', c / 'solution.tex'] + [p for p in reference_text if p.suffix in {'.md', '.tex'} and p.name != 'canonical-target.md']
    local_links = sum(check_links(p, root, a.allow_pending_manifest) for p in live_link_files)
    email = re.compile(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
    scan_files = reference_text + [c / x for x in ['README.md', 'problem.tex', 'solution.md', 'solution.tex']]
    for path in scan_files:
        assert not email.search(path.read_text()), ('contact address found', str(path.relative_to(root)))
    for s in [target, tex, md]:
        for value in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology']:
            assert value in s
    resolved = (root / 'RESOLVED.md').read_text()
    section = resolved[resolved.index('### ✅ FR-12'):].split('\n### ', 1)[0]
    for value in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology', 'Ferber, Jain and Zhao', 'informal agent review']:
        assert value in section
    assert not email.search(section)
    allowed = {'.md', '.tex', '.json', '.py', '.diff'}
    assert all(p.suffix in allowed for p in r.rglob('*') if p.is_file()), 'Unexpected binary or third-party asset in references'
    print(json.dumps({
        'verdict': 'PASS: source preservation, conversion, target, attribution, evidence bindings, local links and text privacy',
        'scope': 'Read-only packaging checks only. Full mathematical review and all-page PDF visual QA are separately attributed. No tests, rendering, public network retrieval, git mutations or publication performed.',
        'six_artifacts': files,
        'frozen_source_sha256': ORIGINAL, 'independent_math_review_sha256': MATH_REVIEW,
        'retained_original_target_sha256': OLD_TARGET,
        'retained_tex_body': {'bytes': len(old_body.encode()), 'sha256': hashlib.sha256(old_body.encode()).hexdigest()},
        'proof_math_expressions': len(tm), 'canonical_math_expressions': len(canonical_math),
        'table_rows': 2, 'registry_entries_unchanged': len(registry),
        'live_local_links_checked': local_links, 'privacy_text_files_checked': len(scan_files),
        'bounded_network': {'checked_utc': network['checked_utc'], 'repositories': 6, 'heads': 49, 'status_counts': dict(counts), 'primary_admission_PR_only': 111},
        'independent_archive_bindings_checked': len(im['files']),
        'outer_manifest': 'PENDING: not a completed manifest verification' if a.allow_pending_manifest else 'Present; per-file final manifest verification remains separate',
        'historical_link_exception': 'canonical-target.md retains its original navigation and is identified as a frozen snapshot in the live record',
    }, indent=2))


if __name__ == '__main__':
    main()
