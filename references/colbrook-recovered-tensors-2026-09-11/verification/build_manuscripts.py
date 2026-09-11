"""Build attributed copies, retaining the reviewed mathematical body exactly."""
import hashlib,os,re,shutil,subprocess,tempfile,sys
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT=Path(__file__).resolve().parents[1]
def render(ident):
 source=ROOT/'submitted/manuscripts'/ident/'main.tex'
 original=source.read_text(encoding='utf-8');digest=hashlib.sha256(original.encode()).hexdigest()
 report=(ROOT/'verification/reviews'/f'{ident}-review.md').read_text(encoding='utf-8')
 assert digest in report and 'PASS' in report,(ident,'missing complete review')
 text=original.replace(r'\author{}',r'\author{Matthew J. Colbrook\thanks{Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: m.colbrook@damtp.cam.ac.uk.}}',1).replace(r'\date{}',r'\date{11 September 2026}',1)
 text=text.replace(r'\begin{document}',r'\hypersetup{pdfauthor={Matthew J. Colbrook}}'+'\n'+r'\usepackage{xurl}'+'\n'+r'\setlength{\emergencystretch}{3em}'+'\n'+r'\begin{document}',1)
 notice=r'\begin{quote}\small Authorship recorded at the submitter\textquotesingle s request. This recovered draft was generated with AI assistance. The complete original source passed independent agent review against the exact repository target. This is not external human peer review or formal certification; no priority claim is made. Original provenance, full-source review hashes and diagnostic results accompany this manuscript in the submission record.\end{quote}'
 text=text.replace(r'\begin{abstract}',notice+'\n'+r'\begin{abstract}',1)
 marker=r'\begin{abstract}';assert original[original.index(marker):]==text[text.index(marker):]
 with tempfile.TemporaryDirectory(prefix='nla-recovered-tensors-') as d:
  p=Path(d);(p/'manuscript.tex').write_text(text,encoding='utf-8')
  for _ in range(2):
   result=subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=p,capture_output=True,text=True,encoding='utf-8',errors='replace')
   if result.returncode:raise RuntimeError(result.stdout[-5000:])
  log=(p/'manuscript.log').read_text(encoding='utf-8',errors='replace');warnings=re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
  out=ROOT/'manuscripts'/ident;out.with_suffix('.tex').write_text(text,encoding='utf-8');shutil.copyfile(p/'manuscript.pdf',out.with_suffix('.pdf'))
 return ident,warnings
if __name__=='__main__':
 with ThreadPoolExecutor(max_workers=3) as pool:
  for name,warnings in pool.map(render,sys.argv[1:] or ['TR-04','TR-13','TR-20']):print(name+': '+('; '.join(warnings) if warnings else 'OK'),flush=True)
