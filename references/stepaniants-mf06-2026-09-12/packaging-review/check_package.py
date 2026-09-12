#!/usr/bin/env python3
"""Read-only, standard-library audit of the MF-06 publication conversion.

Usage: python3 check_package.py --repo PATH [--require-final-records]
The program reads files and prints JSON. It never edits the repository, invokes
its checkers, compiles documents, fetches the network, or runs git or tests.
It establishes transcription and archive consistency, not mathematical truth.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

CANON = Path('matrix-functions-and-stability/MF-06')
ARCHIVE = Path('references/stepaniants-mf06-2026-09-12')
EXPECTED = {
    'reviewed-proof.md': '2471cce689608c9ff0dfe15e4ed0230f00ba6799c4df1129e593f08e50593f2d',
    'reviewed-proof-clarified.md': '11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94',
    'REVIEW.md': '6c15e3d3a20669ede243d7e56d1229f148e39a138e7c0d1628c5768cf6166d36',
    'canonical-target.md': 'fe32efa1f84a750039f65695f3cadbf615ead558826490e53329ca26704df741',
    'source-clarification.diff': 'ab8e6c4cdb2a66edda6d39174d3508a11e09fe3066b12f54849b5c2be3d14623',
    'source-clarification.json': 'be49b73153aa9f686645166781e27e570fd99612c97a089bca586f5a141fb2cd',
    'independent_exterior_check.py': '2f3e50e7d116473f5c9c8c644487a1c51d92c46deb1bdae810e9d25bd32b960f',
    'independent-exterior-check.json': '617a2b7ec429920d6a7977df1861118d970d51c352b07dc3ab37859eba8abecd',
    'independent-manifest.json': 'd832b26821effd9ec3ff3c3e8b6a4733d23459694ed2c05919864b2ac99a5b50',
    'public-audit/REPORT.md': '2eb546bb1d441bbc4dcc0aafb8995cbf31a75b42571b8bb47c03dbc84c873e38',
    'public-audit/network-check-sanitized.json': 'b7fc71ddc53d93bcdfa67804368fc763eeb8000f1e73febfafc110b682b6be1a',
    'public-audit/source-check.json': 'f92eb0ae71c6eadf69a096f6bfd22a33f13d42baae551ce9f1373ef5fc79eecf',
    'public-audit/audit_public.py': 'a322b77b0369b899b1f04f2f220c5787be6da6c17e1e271d1060912f89e78edc',
    'public-audit/sanitize_audit.py': '4ade5f1abec0a240abc02fba18925a6c5d0b0531343adebbdc8945f0a87d665a',
}
CORE_SHA = '95ffa57f417ac6e0bbc5e43da9f890d92384126f2cac41e2f282898ffb18bc4a'
MD_MATH = re.compile(r'\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$', re.S)
TEX_MATH = re.compile(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', re.S)
MD_LINK = re.compile(r'\[([^\]\n]+)\]\(([^\s]+)\)')
EMAIL = re.compile(r'(?<![\w.+-])[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+')
PRIVATE_PATH = re.compile(r'/(?:Users|private/tmp)/[A-Za-z0-9_.-]+')

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def file_info(path: Path, root: Path) -> dict:
    data = path.read_bytes()
    return {'path': path.relative_to(root).as_posix(), 'bytes': len(data), 'sha256': digest(data)}

def core(s: str) -> str:
    return s[s.index('## 1. The exact target'):s.index('## 7. Scope of verification and attribution')]

def replace_math(s: str, pattern: re.Pattern) -> tuple[str, list[str]]:
    formulas = []
    def replace(m):
        expression = next(x for x in m.groups() if x is not None)
        formulas.append(re.sub(r'\s+', '', expression))
        return f' MATHPLACEHOLDER{len(formulas):03d} '
    return pattern.sub(replace, s), formulas

def normalize(s: str) -> str:
    return ' '.join(s.split())

def markdown_prose(s: str) -> str:
    s = MD_LINK.sub(lambda m: m.group(1), s)
    s = re.sub(r'^\d+\.\s+', '', s, flags=re.M)
    s = re.sub(r'^#{1,6}\s+', '', s, flags=re.M)
    s = s.replace('**', '').replace('*', '')
    return normalize(s)

def tex_prose(s: str) -> str:
    """Invert only enumerated presentation commands; reject unknown commands."""
    s = re.sub(r'\\Needspace\{\d+\\baselineskip\}', '', s)
    s = s.replace(r'\def\labelenumi{\arabic{enumi}.}', '')
    s = s.replace(r'\begin{enumerate}', '').replace(r'\end{enumerate}', '')
    for command in ('tightlist', 'item', 'unskip', 'nobreak', 'hfill'):
        s = re.sub(r'\\' + command + r'\b', ' ', s)
    def group(pos):
        if pos >= len(s) or s[pos] != '{':
            raise AssertionError('Expected TeX group')
        depth, start = 1, pos + 1
        pos += 1
        while pos < len(s):
            if s[pos] == '{' and s[pos-1] != '\\': depth += 1
            if s[pos] == '}' and s[pos-1] != '\\': depth -= 1
            if depth == 0: return s[start:pos], pos + 1
            pos += 1
        raise AssertionError('Unclosed TeX group')
    out, pos = [], 0
    while pos < len(s):
        if s[pos] != '\\':
            out.append(s[pos]); pos += 1; continue
        if pos + 1 < len(s) and s[pos+1] in '&%_#$':
            out.append(s[pos+1]); pos += 2; continue
        match = re.match(r'\\([A-Za-z]+)', s[pos:])
        assert match, f'Unknown TeX escape near {s[pos:pos+50]!r}'
        cmd = match.group(1); pos += len(match.group())
        assert cmd in ('section', 'label', 'emph', 'textbf', 'href', 'S'), f'Unexpected TeX command {cmd}'
        first, pos = group(pos)
        if cmd == 'S':
            assert first == '', 'Only the explicit empty-group section-sign encoding is allowed'
            out.append('§')
        elif cmd == 'href':
            second, pos = group(pos); out.append(tex_prose(second))
        elif cmd != 'label':
            out.append(tex_prose(first))
    return normalize(''.join(out).replace('---', '—').replace('--', '–').replace('~', ' '))

def require_equal(a, b, label):
    if a != b:
        import difflib
        diff = list(difflib.unified_diff(str(a).split(), str(b).split(), n=4))[:100]
        raise AssertionError(label + '\n' + '\n'.join(diff))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--require-final-records', action='store_true')
    args = ap.parse_args(); root = args.repo.resolve(); archive = root / ARCHIVE
    md = (root / CANON / 'solution.md').read_text()
    tex = (root / CANON / 'solution.tex').read_text()
    clarified = (archive / 'reviewed-proof-clarified.md').read_text()
    original = (archive / 'reviewed-proof.md').read_text()
    target = (archive / 'canonical-target.md').read_text()
    readme = (root / CANON / 'README.md').read_text()
    registry = json.loads((root / 'problem_ids.json').read_text())
    assert registry['MF-06'] == (CANON / 'README.md').as_posix()
    archive_checks = []
    for rel, sha in EXPECTED.items():
        info = file_info(archive / rel, root)
        assert info['sha256'] == sha, f'Frozen archive altered: {rel}'
        archive_checks.append(info)
    inserted = 'Let $n\\ge1$ and $K,F\\ge0$. '
    assert clarified.count(inserted) == 1
    require_equal(clarified.replace(inserted, ''), original, 'Source clarification exceeds recorded one insertion')
    require_equal(core(md), core(clarified), 'Complete Sections 1–6 differ')
    assert len(core(md).encode()) == 14325 and digest(core(md).encode()) == CORE_SHA
    old_tail = target[target.index('## Context and notation'):]
    new_tail = readme[readme.index('## Context and notation'):]
    require_equal(old_tail, new_tail, 'Original canonical target/history changed')

    md_body = md[md.index('This manuscript proves'):]
    tex_body = tex.split(r'\maketitle', 1)[1].rsplit(r'\end{document}', 1)[0]
    md_nonmath, md_formulas = replace_math(md_body, MD_MATH)
    tex_nonmath, tex_formulas = replace_math(tex_body, TEX_MATH)
    require_equal(md_formulas, tex_formulas, 'Ordered mathematical expressions changed')
    assert len(md_formulas) == 182
    md_plain, tex_plain = markdown_prose(md_nonmath), tex_prose(tex_nonmath)
    require_equal(md_plain, tex_plain, 'Complete publication prose changed in TeX')
    tex_urls = re.findall(r'\\href\{([^{}]+)\}', tex_body)
    md_urls = [m.group(2) for m in MD_LINK.finditer(md_body)]
    require_equal(md_urls, tex_urls, 'Publication link targets changed in TeX')
    problem_tex = (root / CANON / 'problem.tex').read_text()
    _, canonical_md_math = replace_math(readme, MD_MATH)
    _, canonical_tex_math = replace_math(problem_tex, TEX_MATH)
    require_equal(canonical_md_math, canonical_tex_math, 'Canonical README formulas changed in problem TeX')

    def binding(path, record):
        info = file_info(path, root)
        require_equal(info['bytes'], record['bytes'], 'Saved byte count differs: ' + info['path'])
        require_equal(info['sha256'], record['sha256'], 'Saved SHA-256 differs: ' + info['path'])
    current_records = []
    for filename in ('source-preservation.json', 'conversion-check-output.json', 'pdf-qa.json',
                     'canonical-pdf-qa.json', 'verification.json', 'latex-layout-changes.json',
                     'build_solution.py', 'check_conversion.py', 'README.md'):
        if (archive / filename).exists(): current_records.append(file_info(archive / filename, root))
    preservation = json.loads((archive / 'source-preservation.json').read_text())
    for name, info in preservation['current_public_draft_sources'].items(): binding(root / CANON / name, info)
    binding(root / CANON / 'solution.pdf', preservation['final_solution_pdf'])
    conversion = json.loads((archive / 'conversion-check-output.json').read_text())
    for name, info in conversion['inputs'].items():
        binding((archive if name == 'reviewed-proof-clarified.md' else root / CANON) / name, info)
    proof_qa = json.loads((archive / 'pdf-qa.json').read_text())
    for name, info in proof_qa['artifacts'].items(): binding(root / CANON / name, info)
    assert proof_qa['page_count'] == 7 and len(proof_qa['visual_pages']) == 7
    assert all(page['verdict'] == 'PASS' for page in proof_qa['visual_pages'])
    canonical_qa = json.loads((archive / 'canonical-pdf-qa.json').read_text())
    binding(root / CANON / 'problem.pdf', canonical_qa['canonical_pdf'])
    assert canonical_qa['pages'] == 2 and len(canonical_qa['visual_inspection']) == 2
    assert all(page['result'] == 'PASS' for page in canonical_qa['visual_inspection'])
    if (archive / 'verification.json').exists():
        verification = json.loads((archive / 'verification.json').read_text())
        for name, info in verification['pdfs'].items(): binding(root / CANON / name, info)
        binding(archive / 'REVIEW.md', verification['independent_mathematical_review'])

    expected_byline = ('George Stepaniants', 'Department of Computing and Mathematical Sciences',
                       'California Institute of Technology', 'Pasadena, California, USA')
    for content in (md, tex, readme):
        for phrase in expected_byline: assert phrase in content, phrase
    assert r'pdfauthor={George Stepaniants}' in tex
    assert '**Status:** Solved' in readme
    assert 'not external human peer review or formal verification' in md
    assert 'no novelty is claimed for that general mechanism' in md

    finals = [archive / 'verification.json', archive / 'manifest.json', archive / 'packaging-review/REVIEW.md']
    pending = [p.relative_to(root).as_posix() for p in finals if not p.is_file()]
    if args.require_final_records: assert not pending, f'Missing final records: {pending}'
    link_checks, external = [], set()
    live_mds = [root / CANON / 'README.md', root / CANON / 'solution.md', archive / 'README.md']
    for path in live_mds:
        if not path.exists():
            pending.append(path.relative_to(root).as_posix()); continue
        for match in MD_LINK.finditer(path.read_text()):
            url = match.group(2); parts = urlsplit(url)
            if parts.scheme in ('http', 'https'):
                external.add(url); continue
            assert not parts.scheme, f'Unexpected link scheme: {url}'
            if not parts.path: continue
            dest = (path.parent / unquote(parts.path)).resolve()
            try: destrel = dest.relative_to(root).as_posix()
            except ValueError: raise AssertionError(f'Link escapes repository: {url}')
            exists = dest.exists()
            if not exists and destrel not in pending:
                raise AssertionError(f'Broken live local link: {path.relative_to(root)} -> {url}')
            link_checks.append({'from': path.relative_to(root).as_posix(), 'target': destrel, 'exists': exists})
    privacy_paths = [p for p in archive.rglob('*') if p.is_file() and p.suffix in ('.md', '.tex', '.json', '.py', '.diff')]
    privacy_paths += [root / CANON / name for name in ('README.md', 'solution.md', 'solution.tex', 'problem.tex')]
    for path in privacy_paths:
        text = path.read_text()
        assert not EMAIL.search(text), f'Email-like contact text in {path.relative_to(root)}'
        assert not PRIVATE_PATH.search(text), f'Private filesystem path in {path.relative_to(root)}'
    files = [file_info(root / CANON / name, root) for name in
             ('README.md', 'solution.md', 'solution.tex', 'solution.pdf', 'problem.tex', 'problem.pdf')]
    print(json.dumps({
        'verdict': 'PASS' if not pending else 'PASS source conversion; final assembly pending',
        'scope': 'Independent read-only publication transcription, target/archive consistency and local-link/privacy audit; not a formal mathematical verification or a fresh network/PDF visual audit.',
        'core': {'bytes': 14325, 'sha256': CORE_SHA, 'complete_sections': '1–6', 'byte_identical': True},
        'ordered_math_expressions': len(md_formulas),
        'canonical_ordered_math_expressions': len(canonical_md_math),
        'registry': {'registered_ids': len(registry), 'MF-06': registry['MF-06'],
                     'scope': 'Read-only current mapping; published-base safeguards were run separately by the coordinator'},
        'complete_publication_prose': {'equal_after_documented_presentation_normalization': True,
             'normalized_bytes': len(md_plain.encode()), 'sha256': digest(md_plain.encode())},
        'tex_layout_directives': re.findall(r'\\Needspace\{\d+\\baselineskip\}', tex),
        'explicit_section_sign_encodings': tex.count(r'\S{}'),
        'canonical_retained_tail': {'from': '## Context and notation', 'bytes': len(old_tail.encode()), 'sha256': digest(old_tail.encode()), 'byte_identical': True},
        'files': files, 'frozen_archive_checks': archive_checks,
        'current_packaging_record_bindings': current_records,
        'document_review_attribution': {'proof_pages': 7, 'proof_reviewer': proof_qa['reviewer'],
             'canonical_pages': 2, 'canonical_reviewer': canonical_qa['reviewer'],
             'this_checker_does_not_claim_visual_inspection': True},
        'source_clarification': 'Exactly one insertion: Let $n\\ge1$ and $K,F\\ge0$. ',
        'local_link_checks': link_checks,
        'external_urls_inventory_only_no_network': sorted(external),
        'privacy_text_files_checked': len(privacy_paths), 'pending_final_assembly': pending,
        'limits': ['No repository files written', 'No network, git, repository tests or PDF rendering invoked',
                   'External URL availability is not rechecked by this offline program',
                   'Historical signed snapshots may retain original staging labels; final verification must distinguish them']
    }, indent=2, ensure_ascii=False))

if __name__ == '__main__':
    main()
