from pathlib import Path
import json,re
import fitz
from PIL import Image,ImageOps,ImageDraw
R=Path(__file__).resolve().parents[1];p=R/'writeup/RA17_topological_relaxation.pdf'
D=fitz.open(p);render=Path('/mnt/data/RA17_continuation_renders');render.mkdir(exist_ok=True)
checks={'page_count':len(D),'page_size_points':[],'outside_page_spans':[],'latex_overfull_warnings':[]}
thumbs=[]
for i,page in enumerate(D):
    checks['page_size_points'].append([page.rect.width,page.rect.height])
    for block in page.get_text('dict')['blocks']:
        for line in block.get('lines',[]):
            for sp in line.get('spans',[]):
                box=fitz.Rect(sp['bbox'])
                if box.x0 < -1 or box.y0 < -1 or box.x1>page.rect.width+1 or box.y1>page.rect.height+1:
                    checks['outside_page_spans'].append({'page':i+1,'text':sp['text'],'bbox':sp['bbox']})
    pix=page.get_pixmap(matrix=fitz.Matrix(1.25,1.25),alpha=False);file=render/f'page-{i+1:02}.png';pix.save(file)
    im=Image.open(file).convert('RGB');im.thumbnail((306,420));tile=Image.new('RGB',(330,454),'white');tile.paste(im,((330-im.width)//2,10));ImageDraw.Draw(tile).text((12,436),f'Page {i+1}',fill='black');thumbs.append(tile)
for start in range(0,len(thumbs),9):
    batch=thumbs[start:start+9];rows=(len(batch)+2)//3;canvas=Image.new('RGB',(990,454*rows),(225,225,225))
    for j,im in enumerate(batch):canvas.paste(im,((j%3)*330,(j//3)*454))
    canvas.save(render/f'montage-{start+1}.png')
log=R/'writeup/main.log'
if log.exists():checks['latex_overfull_warnings']=re.findall(r'Overfull \\hbox[^\n]*',log.read_text(errors='replace'))
checks['text_contains_partial']='PARTIAL' in ''.join(page.get_text() for page in D)
checks['note']='Automated page-boundary and compilation checks. These are not mathematical proof verification.'
(R/'data/pdf_qa.json').write_text(json.dumps(checks,indent=2));print(json.dumps(checks,indent=2))
