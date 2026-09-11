"""Read-only validation of PR83's author-contact-only delta a7afa4d."""
from pathlib import Path
import hashlib,json,re,subprocess
import pdfplumber
from PIL import Image,ImageDraw

ROOT=Path('/private/tmp/nla-review-wave2-artifacts')
OLD=ROOT/'pr-83';NEW=ROOT/'pr-83-a7afa4d';OUT=ROOT/'audit-elimination'/'pr83-delta-qa';OUT.mkdir(exist_ok=True)
P='linear-systems-and-elimination/IE-15/'
R='references/stepaniants-ie15-2026-09-11/'
checks={}
def ck(name,b):checks[name]=bool(b);assert b,name

old=(OLD/P/'solution.md').read_text();new=(NEW/P/'solution.md').read_text()
contact_match=re.search(r'^email:\s*"([^"\n]+@[^"\n]+)"\s*$',old,flags=re.M)
assert contact_match, 'Expected exactly the old email metadata value'
contact=contact_match.group(1)
ck('markdown_only_email_line_removed',re.sub(r'^email:.*\n','',old,flags=re.M)==new)
oldtex=(OLD/P/'solution.tex').read_text();newtex=(NEW/P/'solution.tex').read_text()
ck('generated_tex_only_contact_line_removed','\n'.join(line for line in oldtex.split('\n') if 'mailto:' not in line)==newtex)
ck('generated_tex_mathematical_body_identical',oldtex.split('\\pagestyle{plain}',1)[1]==newtex.split('\\pagestyle{plain}',1)[1])
oldorig=(OLD/R/'original-agent-draft.md').read_text();neworig=(NEW/R/'original-agent-draft.md').read_text()
ck('provenance_only_contact_removed',oldorig.replace('; '+contact+'.','.')==neworig)
for relative in [P+'README.md',P+'problem.tex',P+'problem.pdf',R+'verification/verify_witnesses.py',R+'verification/independent_witnesses.py',R+'verification/reviews/scalar-lemma-independent-proof.md','problem_ids.json','.github/workflows/problem-ids.yml']:
    ck('unchanged_'+relative,(OLD/relative).read_bytes()==(NEW/relative).read_bytes())
docchecks=json.loads((NEW/R/'verification/document-checks.json').read_text())
for relative,digest in docchecks['files'].items():ck('source_hash_'+relative,hashlib.sha256((NEW/relative).read_bytes()).hexdigest()==digest)
for entry in docchecks['pdfs']:
    path=NEW/entry['path']
    ck('pdf_hash_'+entry['path'],hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'])
    with pdfplumber.open(path) as doc:ck('pdf_pages_'+entry['path'],len(doc.pages)==entry['pages'])

pages=[];texts={};bound_errors=[]
for name,base in [('old',OLD),('new',NEW)]:
    doc=pdfplumber.open(base/P/'solution.pdf');chunks=[]
    for i,page in enumerate(doc.pages,1):
        # Footer is only a page number; remove it for content comparison.
        body=page.crop((0,0,page.width,page.height-55));chunks.append(body.extract_text() or '')
        if name=='new':
            im=page.to_image(resolution=115).original.convert('RGB');im.save(OUT/f'page-{i:02}.png')
            im.thumbnail((480,690));tile=Image.new('RGB',(500,725),'#ddd');tile.paste(im,((500-im.width)//2,25));ImageDraw.Draw(tile).text((10,5),f'PR83 a7afa4d solution.pdf page {i}/6',fill='black');pages.append(tile)
            for c in page.chars:
                if c['x0']<0 or c['x1']>page.width+1 or c['top']<0 or c['bottom']>page.height+1:bound_errors.append({'page':i,'char':c['text']})
    text='\n'.join(chunks);texts[name]=text
    (OUT/(name+'-solution.txt')).write_text(text.replace(contact,'[contact redacted]'))
# Account only for explicitly removed email and reflowed whitespace.
oldnorm=re.sub(r'\s+','',texts['old'].replace(contact,''))
newnorm=re.sub(r'\s+','',texts['new'])
ck('complete_pdf_text_only_contact_and_whitespace_changed',oldnorm==newnorm)
ck('pdf_no_out_of_page_characters',not bound_errors)
ck('pdf_no_replacement_glyphs','\ufffd' not in texts['new'])
sheet=Image.new('RGB',(1500,1450),'white')
for i,tile in enumerate(pages):sheet.paste(tile,((i%3)*500,(i//3)*725))
sheet.save(OUT/'all-six-pages.jpg',quality=95)

result={'old_head':'b1a5d597a2d0a1b77f77ab8f98424b1328caebc2','new_head':'a7afa4de26d0ff2cd41c15afe2509380a5ed8d68','passed':sum(checks.values()),'total':len(checks),'checks':checks,'bounds_errors':bound_errors}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'total':result['total']},indent=2))
