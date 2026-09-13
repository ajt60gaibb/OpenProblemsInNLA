from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
import requests
from bs4 import BeautifulSoup
R=Path(__file__).resolve().parents[1]
urls=[
 'https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-17/README.md',
 'https://arxiv.org/abs/1505.07204',
 'https://arxiv.org/abs/1611.01175',
 'https://pi.math.cornell.edu/~hatcher/VBKT/VBpage.html']
records=[]
for url in urls:
 rec={'url':url,'checked_at_utc':datetime.now(timezone.utc).isoformat()}
 try:
  response=requests.get(url,timeout=6);rec['http_status']=response.status_code
  rec['sha256']=hashlib.sha256(response.content).hexdigest()
  if response.ok:
   soup=BeautifulSoup(response.text,'html.parser')
   tag=soup.find('meta',attrs={'name':'citation_title'})
   rec['title']=tag.get('content') if tag else (soup.title.get_text(' ',strip=True) if soup.title else response.text.splitlines()[0])
   rec['authors']=[t.get('content') for t in soup.find_all('meta',attrs={'name':'citation_author'})]
 except Exception as e:rec['error']=str(e)
 records.append(rec)
(R/'data/source_audit.json').write_text(json.dumps(records,indent=2))
p=R/'writeup/main.tex';text=p.read_text()
# Do not retain an unverified guessed title.
text=text.replace('\\emph{The rational cohomology of\nhomogeneous spaces: a brief survey}. arXiv:1611.01175.', '\\emph{arXiv:1611.01175}.')
for rec in records:
 if rec['url'].endswith('1611.01175') and rec.get('http_status')==200 and rec.get('title'):
  title=rec['title']
  if 'arxiv' not in title.lower() and not any(x in title.lower() for x in ('error','denied','unavailable')):
   escaped=title.replace('&',r'\&').replace('%',r'\%').replace('_',r'\_')
   text=text.replace(r'\emph{arXiv:1611.01175}.',r'\emph{'+escaped+r'}. arXiv:1611.01175.')
text=text.replace(' \\text{There exists a $17$-dimensional }K\\subset M_6(\\R)\n \\text{ with }\\rank A\\ge3\\text{ for every }A\\ne0;\\\\\n \\text{or every such $17$-dimensional space contains a nonzero matrix of rank\n at most two.}',
 r' \text{Construct a seventeen-dimensional }K\subset M_6(\R)\\'+'\n'+r' \text{whose every nonzero member has rank at least three,}\\'+'\n'+r' \text{or prove that no such linear space exists.}')
p.write_text(text)
print(json.dumps(records,indent=2))
