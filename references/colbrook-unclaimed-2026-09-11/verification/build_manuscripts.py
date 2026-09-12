"""Compile complete independently reviewed Markdown manuscripts via Pandoc/XeLaTeX."""
import hashlib,os,re,shutil,subprocess,tempfile,sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parents[1]
def render(ident):
 source=ROOT/'manuscripts'/f'{ident}.md';review=ROOT/'verification/reviews'/f'{ident}-review.md'
 digest=hashlib.sha256(source.read_text(encoding='utf-8').encode()).hexdigest();report=review.read_text(encoding='utf-8')
 assert digest in report and 'PASS' in report,(ident,'missing complete independent review')
 with tempfile.TemporaryDirectory(prefix='nla-research-') as d:
  p=Path(d);tex=p/'manuscript.tex'
  subprocess.run([os.environ.get('PANDOC','pandoc'),str(source),'-f','markdown+tex_math_single_backslash','-s','-t','latex','-M','author=Matthew J. Colbrook','--top-level-division=section','-V','geometry:margin=25mm','-V','fontsize=11pt','-o',str(tex)],check=True)
  text=tex.read_text(encoding='utf-8');text=text.replace(r'\begin{document}',r'\usepackage{xurl}'+'\n'+r'\setlength{\emergencystretch}{3em}'+'\n'+r'\begin{document}',1);tex.write_text(text,encoding='utf-8')
  for _ in range(2):
   r=subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=p,capture_output=True,text=True,encoding='utf-8',errors='replace')
   if r.returncode:raise RuntimeError(r.stdout[-5000:])
  log=(p/'manuscript.log').read_text(encoding='utf-8',errors='replace');warnings=re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
  source.with_suffix('.tex').write_text(text,encoding='utf-8');shutil.copyfile(p/'manuscript.pdf',source.with_suffix('.pdf'))
 return ident,warnings
if __name__=='__main__':
 ids=sys.argv[1:] or ['TR-06','TR-15','TR-26']
 with ThreadPoolExecutor(max_workers=3) as pool:
  for name,warnings in pool.map(render,ids):print(name+': '+('; '.join(warnings) if warnings else 'OK'),flush=True)
