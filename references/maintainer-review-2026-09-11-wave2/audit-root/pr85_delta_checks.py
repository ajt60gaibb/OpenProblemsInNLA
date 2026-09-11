"""Read-only checks for PR85's contact-redaction delta; never republishes the contact."""
from pathlib import Path
import hashlib, json, re
import pdfplumber
from PIL import Image, ImageDraw

ROOT = Path('/private/tmp/nla-review-wave2-artifacts')
OLD = ROOT / 'pr-85'
NEW = ROOT / 'pr-85-current'
OUT = ROOT / 'audit-root' / 'pr85-delta-qa'
OUT.mkdir(exist_ok=True)
P = 'matrix-inequalities-and-norms/MI-28/'
R = 'references/stepaniants-mi28-2026-09-11/'
checks = {}
findings = []
def ck(name, value):
    checks[name] = bool(value)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def remove_contact_line(text):
    return '\n'.join(line for line in text.split('\n') if 'mailto:' not in line)

old = (OLD / P / 'solution.md').read_text()
new = (NEW / P / 'solution.md').read_text()
matches = re.findall(r'^email:\s*"([^"\n]+@[^"\n]+)"\s*$', old, flags=re.M)
assert len(matches) == 1
contact = matches[0]
ck('canonical_markdown_only_email_line_removed', re.sub(r'^email:.*\n', '', old, flags=re.M) == new)
oldtex = (OLD / P / 'solution.tex').read_text()
newtex = (NEW / P / 'solution.tex').read_text()
ck('canonical_tex_only_contact_line_removed', remove_contact_line(oldtex) == newtex)
ck('canonical_tex_entire_mathematical_body_identical', oldtex.split('\\pagestyle{plain}', 1)[1] == newtex.split('\\pagestyle{plain}', 1)[1])
oldmd = (OLD / R / 'original-agent-manuscript.md').read_text()
newmd = (NEW / R / 'original-agent-manuscript.md').read_text()
ck('original_markdown_only_contact_line_removed', remove_contact_line(oldmd) == newmd)
ot = (OLD / R / 'original-agent-manuscript.tex').read_text()
nt = (NEW / R / 'original-agent-manuscript.tex').read_text()
lines = ot.split('\n')
positions = [i for i, line in enumerate(lines) if 'mailto:' in line]
assert len(positions) == 1
i = positions[0]
assert lines[i-1].endswith('\\\\') and lines[i].endswith('}')
lines[i-1] = lines[i-1][:-2] + '}'
del lines[i]
ck('original_tex_only_contact_removed_and_author_brace_relocated', '\n'.join(lines) == nt)
ck('original_tex_entire_document_body_identical', ot.split('\\begin{document}', 1)[1] == nt.split('\\begin{document}', 1)[1])
template_old = (OLD / 'tools/solution-template.tex').read_text()
template_new = (NEW / 'tools/solution-template.tex').read_text()
ck('template_only_optional_email_guard_added', template_new.replace('$if(email)$\n', '').replace('$endif$\n', '') == template_old)
for relative in [P+'README.md', P+'problem.tex', P+'problem.pdf', 'problem_ids.json', '.github/workflows/problem-ids.yml', 'tools/render_problems.py', 'tools/render_solutions.py']:
    ck('unchanged_'+relative, (OLD / relative).read_bytes() == (NEW / relative).read_bytes())
old_scripts = sorted((OLD / R / 'verification').rglob('*.py'))
ck('verification_script_inventory_unchanged', [p.relative_to(OLD).as_posix() for p in old_scripts] == [p.relative_to(NEW).as_posix() for p in sorted((NEW / R / 'verification').rglob('*.py'))])
for path in old_scripts:
    relative = path.relative_to(OLD)
    ck('unchanged_'+relative.as_posix(), path.read_bytes() == (NEW / relative).read_bytes())

records = json.loads((NEW / R / 'verification/document-checks.json').read_text())
for relative, digest in records['files'].items():
    ck('current_source_hash_'+relative, sha(NEW / relative) == digest)
for relative, entry in records['email_metadata_redaction']['mathematical_cores'].items():
    data = (NEW / relative).read_bytes()
    size = entry['bytes']
    candidates = [data[start:start+size] for start in range(len(data)-size+1)]
    matches = [chunk for chunk in candidates if hashlib.sha256(chunk).hexdigest() == entry['sha256']]
    ck('declared_core_hash_and_old_new_identity_'+relative, len(matches) == 1 and matches[0] in (OLD / relative).read_bytes())
for entry in records['pdfs']:
    path = NEW / entry['path']
    ck('current_pdf_hash_'+entry['path'], sha(path) == entry['sha256'])
    with pdfplumber.open(path) as doc:
        ck('current_pdf_pages_'+entry['path'], len(doc.pages) == entry['pages'])
historical = records['pre_email_redaction_record']
for relative, digest in historical['files'].items():
    ck('historical_source_hash_'+relative, sha(OLD / relative) == digest)
for entry in historical['pdfs']:
    path = OLD / entry['path']
    actual = sha(path)
    ck('historical_pdf_hash_'+entry['path'], actual == entry['sha256'])
    if actual != entry['sha256']:
        findings.append({'file': R+'verification/document-checks.json', 'line': 93, 'field': 'pre_email_redaction_record.pdfs[0].sha256', 'recorded': entry['sha256'], 'expected_old_pdf_hash': actual, 'impact': 'Incorrect historical fingerprint; no mathematical content change.'})
    with pdfplumber.open(path) as doc:
        ck('historical_pdf_pages_'+entry['path'], len(doc.pages) == entry['pages'])

pages = []
texts = {}
bound_errors = []
for label, base in [('old', OLD), ('new', NEW)]:
    with pdfplumber.open(base / P / 'solution.pdf') as doc:
        chunks = []
        for index, page in enumerate(doc.pages, 1):
            # The footer is only the page number; exclude it from content comparison.
            chunks.append(page.crop((0, 0, page.width, page.height - 55)).extract_text() or '')
            if label == 'new':
                im = page.to_image(resolution=115).original.convert('RGB')
                im.save(OUT / f'page-{index:02}.png')
                im.thumbnail((480, 690))
                tile = Image.new('RGB', (500, 725), '#ddd')
                tile.paste(im, ((500-im.width)//2, 25))
                ImageDraw.Draw(tile).text((10, 5), f'PR85 6fb1041 solution.pdf page {index}/5', fill='black')
                pages.append(tile)
                for char in page.chars:
                    if char['x0'] < 0 or char['x1'] > page.width+1 or char['top'] < 0 or char['bottom'] > page.height+1:
                        bound_errors.append({'page': index, 'char': char['text']})
                ck(f'current_pdf_page_{index}_no_contact_annotation', contact not in json.dumps(page.annots, default=str))
        texts[label] = '\n'.join(chunks)
        (OUT / (label+'-solution.txt')).write_text(texts[label].replace(contact, '[contact redacted]'))
        if label == 'new':
            ck('current_pdf_metadata_no_contact', contact not in json.dumps(doc.metadata, default=str))
ck('complete_pdf_text_only_contact_and_whitespace_changed', re.sub(r'\s+', '', texts['old'].replace(contact, '')) == re.sub(r'\s+', '', texts['new']))
ck('current_pdf_text_no_contact', contact not in texts['new'])
ck('current_pdf_no_out_of_page_characters', not bound_errors)
ck('current_pdf_no_replacement_glyphs', '\ufffd' not in texts['new'])
sheet = Image.new('RGB', (1500, 1450), 'white')
for index, tile in enumerate(pages):
    sheet.paste(tile, ((index % 3)*500, (index // 3)*725))
sheet.save(OUT / 'all-five-pages.jpg', quality=95)
result = {'old_head': 'bf70552daecf8c6275ef1eb73f73aac664358228', 'new_head': '6fb1041e83823f726a326b33ef8169cd593df631', 'passed': sum(checks.values()), 'total': len(checks), 'checks': checks, 'findings': findings, 'bounds_errors': bound_errors, 'rendered_pages': len(pages)}
(OUT / 'checks.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'passed': result['passed'], 'total': result['total'], 'findings': findings, 'rendered_pages': len(pages)}, indent=2))
