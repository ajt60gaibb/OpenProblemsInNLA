"""Read-only source-integrity and final-PDF QA for PR97 and PR101."""
from pathlib import Path
import hashlib, json, re, subprocess
import pdfplumber
from PIL import Image, ImageDraw

ROOT=Path('/private/tmp/nla-review-wave3-artifacts')
OUT=ROOT/'audit-tensors';QA=OUT/'pdf-qa';QA.mkdir(exist_ok=True)
REPO='/private/tmp/nla-pr83-delta-review'
BASE='16369809e6e600144bd350ab70b7473b652f46f1'
ENTRIES={97:['TR-06','TR-15','TR-26'],101:['TR-04','TR-13','TR-20']}
REF={97:'colbrook-unclaimed-2026-09-11',101:'colbrook-recovered-tensors-2026-09-11'}
checks={};documents=[]
def ck(label,boolean): checks[label]=bool(boolean)
def original(path):return subprocess.check_output(['git','-C',REPO,'show',BASE+':'+path])
for pr,ids in ENTRIES.items():
    root=ROOT/f'pr-{pr}'
    registry=json.loads((root/'problem_ids.json').read_text())
    ck(f'PR{pr}_203_permanent_ids',len(registry)==203)
    ck(f'PR{pr}_registry_byte_identical', (root/'problem_ids.json').read_bytes()==original('problem_ids.json'))
    ck(f'PR{pr}_all_other_canonical_pages_unchanged',all((root/p).read_bytes()==original(p) for id,p in registry.items() if id not in ids))
    for id in ids:
        relative=registry[id];old=original(relative).decode();new=(root/relative).read_text()
        marker='## Context and notation' if id=='TR-06' else ('## Statement' if id in ['TR-13','TR-15'] else '## Problem statement')
        ck(id+'_original_target_and_references_retained',old.split(marker,1)[1].rstrip()==new.split(marker,1)[1].rstrip())
        ck(id+'_permanent_heading_retained',old.splitlines()[0]==new.splitlines()[0])
        for field in ['Difficulty','Importance','Rating rationale']:
            pattern=r'^\*\*'+field+r':\*\* (.*)$'
            ck(id+'_historical_'+field+'_retained',re.search(pattern,old,re.M).group(1)==re.search(pattern,new,re.M).group(1))
    for relative in ['tools/validate_problem_ids.py','tools/update_catalog.py','tests/test_problem_ids.py','.github/workflows/problem-ids.yml']:
        ck(f'PR{pr}_unchanged_'+relative,(root/relative).read_bytes()==original(relative))
    ref=root/'references'/REF[pr]
    if pr==101:
        for id in ids:
            old=(ref/'submitted/manuscripts'/id/'main.tex').read_text()
            new=(ref/'manuscripts'/f'{id}.tex').read_text()
            ck(id+'_entire_archived_mathematical_body_identical',old.split('\\begin{abstract}',1)[1]==new.split('\\begin{abstract}',1)[1])
    record=json.loads((ref/'verification/document-checks.json').read_text())
    for entry in record['documents']:
        path=root/entry['path'];digest=hashlib.sha256(path.read_bytes()).hexdigest()
        ck(f'PR{pr}_hash_'+entry['path'],digest==entry['sha256'])
        identifier=path.parent.name if path.name=='problem.pdf' else path.stem
        kind='problem' if path.name=='problem.pdf' else 'manuscript'
        name=f'{pr}-{identifier}-{kind}'
        tiles=[];texts=[];outside=[];replacement=[]
        with pdfplumber.open(path) as doc:
            ck(name+'_pages',len(doc.pages)==entry['pages'])
            for index,page in enumerate(doc.pages,1):
                text=page.extract_text() or '';texts.append(text)
                if '\ufffd' in text:replacement.append(index)
                for char in page.chars:
                    if char['x0']<0 or char['x1']>page.width+1 or char['top']<0 or char['bottom']>page.height+1:
                        outside.append({'page':index,'character':char['text']})
                img=page.to_image(resolution=110).original.convert('RGB')
                img.save(QA/f'{name}-{index:02}.png')
                img.thumbnail((470,670))
                tile=Image.new('RGB',(490,705),'#ddd');tile.paste(img,((490-img.width)//2,25))
                ImageDraw.Draw(tile).text((8,6),f'PR{pr} {identifier} {kind} {index}/{len(doc.pages)}',fill='black')
                tiles.append(tile)
        ck(name+'_no_out_of_page_characters',not outside)
        ck(name+'_no_replacement_glyphs',not replacement)
        cols=min(3,len(tiles));rows=(len(tiles)+cols-1)//cols
        sheet=Image.new('RGB',(cols*490,rows*705),'white')
        for index,tile in enumerate(tiles):sheet.paste(tile,((index%cols)*490,(index//cols)*705))
        sheet.save(QA/f'{name}-contact.jpg',quality=95)
        # Do not reproduce author email addresses in new audit text artifacts.
        text='\n\n'.join(texts)
        text=re.sub(r'\b[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}\b','[contact omitted]',text)
        (QA/f'{name}.txt').write_text(text)
        documents.append({'pr':pr,'path':entry['path'],'pages':len(tiles),'sha256':digest,'out_of_page':outside,'replacement_pages':replacement,'contact_sheet':str(QA/f'{name}-contact.jpg')})
result={'base':BASE,'passed':sum(checks.values()),'total':len(checks),'checks':checks,'documents':documents,'pdfs':len(documents),'pages':sum(d['pages'] for d in documents)}
(OUT/'source-pdf-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['passed','total','pdfs','pages']},indent=2))
print('Failures:',[key for key,value in checks.items() if not value])
